# Events: the reactor, with completion-shaped custody

**Status: brainstorm, building on Ori's `design/reactor.md`.** Networking,
audio and graphics all need a program that outlives one `main!` activation
and waits on several things at once. Faun has no async, no threads and no
effectful callbacks, so the loop lives in the host and calls total Faun
handlers.

## Ori's contract, briefly

```faun
init! : Host -> Outcome
handle! : (Host, State, Event) -> Outcome
finish! : (Host, State) -> []

Outcome : [Continue(State, List(Source)), Stop(State), Fail(Str)]
```

Waiting resources live in the reactor's custody, together with a
program-chosen payload. An event hands the resource and its payload back to
one activation, which does bounded work and returns the resource to custody,
closes it, or keeps it in `State`. Custody is one-shot. When custody is empty,
`finish!` runs. The payload is a defunctionalized continuation: what an async
compiler would hide in a generated state machine, Faun keeps as a named value.

## The proposed change: sources are operations, not interests

Ori's strawman registers _readiness_: `Tcp(stream, Read, conn)` fires when
the stream is readable, and the handler then calls `read!`. That is epoll's
model. Instead, make each source an **operation the host performs**, and each
event its **completion**:

```faun
Source : [
  Accept(TcpListener, c),
  Receive(TcpStream, Nat, c),             # up to n bytes
  Send(TcpStream, List(U8), c),           # some of these bytes
  ReceiveFrom(UdpSocket, Nat, c),
  Read(Reader, Nat, c),                   # stdin, pipes, files
  Wait(Child, c),
  After(Duration, c),
  AudioWanted(AudioOut, c),               # see audio.md
  NextFrame(Window, c),                   # see graphics.md
]

Event : [
  Accepted(TcpListener, Result(TcpStream, AcceptError), c),
  Received(TcpStream, Result([Data(List(U8)), End], ReceiveError), c),
  Sent(TcpStream, Result(Nat, SendError), c),
  ...
  Timer(c),
  Stop,
]
```

Why this is better:

- **Both kinds of OS primitive implement it natively.** A readiness backend
  (epoll, kqueue, `poll`) waits until the stream is ready and then does the
  syscall. A completion backend (io_uring, IOCP) submits the operation and
  waits for it to finish. Readiness can emulate completion for the price of one
  syscall. Completion can only emulate readiness with tricks: the `polling`
  crate's IOCP backend uses undocumented AFD polling. Making the portable
  contract completion-shaped lets every target use its best primitive.
- **WASI 0.3 fits directly.** Each custody entry becomes a pending `future` or
  a `stream` read, and the reactor's wait is waiting on all of them. The
  browser is similar: each source becomes a promise, and the host's event loop
  calls `handle!` from the promise's callback.
- **Faun avoids the problem Rust's io_uring has with buffer ownership.** An
  in-flight completion owns its buffer. In Rust, dropping the future while the
  kernel still writes into the buffer is the well-known cancellation hazard.
  In Faun the buffer and the resource are both in custody, and a program can't
  touch either until the event hands them back. Linearity already says so.
- **Handlers get simpler.** A handler doesn't do a "ready, now read, handle
  `WouldBlock`" dance, because the data arrives in the event.
- **Backpressure is still explicit.** `Send` answers how much went, and the
  handler re-queues the rest from its payload.

The cost is that one resource can't have a read and a write outstanding at
the same time, since custody holds each resource once. A full-duplex
connection needs either a `SendReceive(stream, bytes, n, c)` source that
completes with whichever finishes first, or a way to split a TCP stream into
separately owned read and write halves (`TcpStream.split : TcpStream ->
(TcpReader, TcpWriter)`). **Lean: split halves.** It is simpler, and matches
`shutdown` semantics.

## A linear poller underneath

Custody doesn't have to exist only inside the reactor entry profile. Expose it
as a linear resource that any `!` code can use:

```faun
Poller.open! : Host -> Result(Poller, [Other(Nat)])
Poller.add! : (Poller, Source) -> {}              # takes the source's resource
Poller.wait! : Poller -> [Fired(Event), Empty]    # hands one back
Poller.close! : Poller -> Result({}, [NotEmpty])  # only when custody is empty
```

- **Batch programs can multiplex.** Downloading ten URLs at once is a
  `main!` that adds ten `Receive` sources and calls `wait!` in a loop bounded
  by the number of events it expects. No entry profile is needed, and the loop
  is ordinary total Faun.
- **The reactor becomes the host calling `wait!` forever.** That is the one
  thing a Faun loop can't do. `init!`, `handle!` and `finish!` stay the
  long-running profile, and the shell's loop is the same poller.
- **Linearity is what makes exposing epoll safe.** A source's resource moves
  into the poller on `add!` and comes back in an event, so a program can't
  read a stream while the host has a receive outstanding on it. `close!`
  refuses while custody holds anything, so no resource is dropped with the
  poller.

Ori's reactor note named explicitly owned pollables as the missing piece for a
self-hosted reactor. This is that piece.

## Ergonomics: libraries on top

The cost of the reactor is inverted control flow. "Connect, send, read the
reply, parse it" is a state machine written out by hand, since there are no
async functions and no stored closures. Three layers keep most programs away
from that:

1. **Blocking calls for batch work.** Most tools never multiplex, and the
   blocking API is the default.
2. **Protocol libraries as pure step functions** (the "sans-I/O" style of
   Python's `h11` or Rust's `quinn-proto`). An HTTP library is
   `step : (Conn, Event) -> (Conn, List(Action))`, with no effects at all.
   That is Faun's natural style, and it is testable without a network.
3. **Runners.** A library supplies the event handling and takes the app's
   pure function, which second-class functions allow:

   ```faun
   handle!(host, state, event) -> http.serve!(host, state, event, respond)
   respond : (App, Request) -> (App, Response)
   ```

   A server author writes `respond` and never sees an event.

## Timers and time

`After(duration, c)` uses the monotonic clock, one-shot, as custody always is.
A periodic timer re-arms itself in the handler, which keeps drift visible:
schedule relative to the intended time, not to when the handler ran.

## Blocking calls inside a handler

A handler may still call blocking operations: `write!` to stdout, or a quick
file read. They stall every other source for as long as they take. That is
allowed and documented, as in Node's `fs.readFileSync`. A target could warn
about blocking calls it sees on the handler's call graph (`requirement
report: handle! reaches Reader.read!`).

## Cost model

- One event, one activation. Arena reset and promotion happen per
  activation, and only the entry that fired, together with the state that was
  returned, pays promotion (Ori's "custody is the old generation").
- The host's per-source overhead is one custody record: the resource, the
  operation and the payload. No task struct, no waker, no stack.
- On Linux the reactor is an `epoll` or `io_uring` loop the target emits as
  ordinary machine code. It sits below the checker because it holds resources
  between activations.

## Batch programs don't pay

`main!` doesn't change. A program that never names a reactor entry never
links the loop. Blocking calls remain the default and the simplest way to
write a batch tool. The poller is an opt-in resource, and the reactor an
opt-in entry profile.

## Open

- Whether `Source` and `Event` belong to the host module and grow with each
  contract (`AudioWanted` only exists where audio does), or whether each
  contract contributes its own variants. Structural tag rows suggest the
  latter: a program's `Source` row is the union of what it uses, and the
  target checks each tag against what it supports.
- Cancellation. With one-shot custody, cancelling is just never re-arming,
  except for a long operation already in flight (a `Receive` on an idle
  connection). A `Cancel` source that answers the resource back with a
  `Cancelled` event covers it without adding a new concept.
- Priority and fairness: unspecified but starvation-free, as in Ori.
