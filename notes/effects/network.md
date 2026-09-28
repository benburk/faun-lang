# Networking: resolution, TCP, UDP

**Status: brainstorm.** Nothing exists yet. The shape follows Ori's proposal:
resolution, outbound connections, listeners and UDP are separate
capabilities, and each socket kind is its own linear resource.

## Capabilities

```faun
Host.resolver : Host -> Resolver      # names to addresses
Host.connect : Host -> Connect        # outbound TCP
Host.listen : Host -> Listen          # inbound TCP
Host.udp : Host -> Udp                # datagrams
```

A launcher can reasonably grant any subset. A crawler needs `Resolver` and
`Connect`. A server needs `Listen`, and maybe nothing else. A test double
for any of them is a structural fake.

Later refinement, carried as values and not as types: a `Connect` limited to
certain hosts or ports, or a `Listen` limited to one port. The type states the
category of authority, and the value holds its scope, as with directory roots.

## Addresses

```faun
Ip : [V4(U32), V6(U64, U64)]
Address : {ip: Ip, port: U16}
```

Addresses are plain values. Parsing `"127.0.0.1:8080"` is pure library
code. Only resolution touches the host:

```faun
Resolver.resolve! : (Resolver, Str) -> Result(List(Ip), [NotFound, Other(Nat)])
```

Resolution is its own capability because it is the operation with the most
per-platform policy: `/etc/hosts`, `nsswitch`, split DNS, and search domains.

- **Linux with no libc has no `getaddrinfo`.** The target would need its own
  stub resolver: read `/etc/resolv.conf` and `/etc/hosts`, and send UDP to
  the nameserver. That's a few hundred lines of Faun over the UDP contract,
  written once in the host module. It won't honor `nsswitch` (mDNS, LDAP),
  which is the usual trade that static binaries make (Go's pure resolver does
  the same). Document it.
- Windows and macOS call `GetAddrInfoW` and `getaddrinfo`, which block. WASI
  0.2 and 0.3 have `ip-name-lookup`.
- In the reactor, resolution is a source (`Resolve(Str, c)`), so the host can
  use a thread pool, `getaddrinfo_a`, or its own asynchronous stub resolver.

## TCP

```faun
Connect.connect! : (Connect, Address) -> Result(TcpStream, ConnectError)
Listen.bind! : (Listen, Address) -> Result(TcpListener, BindError)
TcpListener.accept! : TcpListener -> Result((TcpStream, Address), AcceptError)
TcpListener.close! : TcpListener -> Result({}, [Other(Nat)])

TcpStream.receive! : (TcpStream, Nat) -> Result([Data(List(U8)), End], ReceiveError)
TcpStream.send! : (TcpStream, List(U8)) -> Result(Nat, SendError)
TcpStream.shutdown! : TcpStream -> Result(TcpReader, [Other(Nat)])  # half-close: stop sending
TcpStream.close! : TcpStream -> Result({}, [Other(Nat)])
TcpStream.split : TcpStream -> (TcpReader, TcpWriter)                # for the reactor; see events.md

ConnectError : [Refused, Unreachable, TimedOut, Denied, Other(Nat)]
ReceiveError : [Reset, TimedOut, Other(Nat)]
SendError : [Reset, BrokenPipe, Other(Nat)]
```

- **The same stream shape as files and stdio.** `receive!` answers `End` on
  an orderly close, and `send!` is partial. `send_all!` is the same Faun loop
  as `write_all!`. A structural bound `Readable(r)` or `Writable(w)` lets one
  function copy from any source to any sink.
- **Half-close as a type change.** After `shutdown!` the program can only
  read, so what comes back is a `TcpReader`. The type makes "sent after
  shutdown" impossible. This is linearity doing a little typestate for free.
- **No socket options at first**, except `TCP_NODELAY`. Latency-sensitive
  code needs it, and it has the same meaning everywhere: `set_no_delay! :
  (TcpStream, Bool) -> Result({}, ...)`. Everything else (buffer sizes,
  keepalive, linger) is a later contract or target-specific.
- **Timeouts.** A blocking `connect!` or `receive!` can wait forever, and
  batch programs need a bound. Two options: a deadline argument on the
  blocking calls, which a target implements with a socket timeout option or a
  `poll` before the call, or a requirement that anything with a deadline uses the reactor with an
  `After` source. **Lean:** optional deadlines on the blocking calls, since
  "fetch this URL within 10 seconds" shouldn't need a reactor.
- `SIGPIPE`: the Linux target sends with `MSG_NOSIGNAL`, so a reset peer is
  `Err(BrokenPipe)` and never a signal.

## UDP

```faun
Udp.bind! : (Udp, Address) -> Result(UdpSocket, BindError)
UdpSocket.send_to! : (UdpSocket, Address, List(U8)) -> Result({}, SendToError)
UdpSocket.receive_from! : (UdpSocket, Nat) -> Result((List(U8), Address), ReceiveError)
UdpSocket.close! : UdpSocket -> Result({}, [Other(Nat)])
```

- A datagram goes whole or not at all, so `send_to!` answers `{}`, not a
  count. A datagram over the path MTU is the host's to fragment or refuse
  (`TooLarge`).
- `receive_from!` truncates to `n` bytes on every platform, silently on
  some. Answer a `truncated: Bool` where the platform reports it (`MSG_TRUNC`
  on Linux), and document the rest.
- Connected UDP (`connect` plus `send`) is a later refinement. It only saves
  the address argument.
- Multicast, broadcast and interface enumeration are separate contracts.

## What is left out

- **TLS and HTTP.** These are libraries or separate host contracts. Where the
  platform has a trusted TLS stack (Windows SChannel, Apple's Network
  framework, the browser's `fetch`), a `Https` contract can use it. On Linux
  with no libc, TLS is a Faun library, which is a large but pure piece of
  work, apart from `Entropy` and the clock.
- **Unix domain sockets.** A separate Unix-only contract, rooted in a `Dir`
  like files. It matters for Wayland (see [graphics.md](graphics.md)) and for
  talking to local daemons.
- **Raw sockets and ICMP.** Target-specific.

## Browser

A browser has no TCP or UDP, only `fetch`, WebSocket and WebRTC. The browser
target omits `Connect`, `Listen` and `Udp`, and offers `Http` and `WebSocket`
contracts instead. A program written against `Http` runs in the browser and
on native targets that provide the same contract. A program written against
`Connect` runs only natively. Both are honest.

## Mapping check

- **`connect!`:** `socket` + `connect` on Linux, `tcp-socket.connect` (async)
  on WASI 0.3, `WSASocketW` + `connect` on Windows.
- **`accept!`:** `accept4` on Linux, `tcp-socket.listen` stream on WASI 0.3,
  `accept` on Windows.
- **`receive!`:** `recvfrom` (no address) on Linux, `stream<u8>` read on WASI
  0.3, `WSARecv` on Windows.
- **`send!`:** `sendto` + `MSG_NOSIGNAL` on Linux, `stream<u8>` write on WASI
  0.3, `WSASend` on Windows.
- **`send_to!`:** `sendto` on Linux, `udp-socket.send` on WASI 0.3,
  `WSASendTo` on Windows.
