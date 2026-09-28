# Audio

**Status: brainstorm.** Nothing exists yet. Audio is the hardest of these
contracts for Faun, because most platforms want an audio callback, and
Faun has no effectful callbacks and no threads.

## The constraint

Audio hardware consumes samples at a fixed rate. If the program is late, the
listener hears a glitch. Platforms offer two models:

- **Pull.** The platform calls a function on a real-time thread: "give me 256
  frames now". CoreAudio, AAudio, WASAPI in event mode, JACK, PipeWire's
  native API and the browser's `AudioWorklet` all work this way. It gives the
  lowest latency, but the callback must not block or allocate.
- **Push.** The program writes blocks of frames, and the write blocks while
  the device's buffer is full. ALSA's `snd_pcm_writei`, OSS's `write` to
  `/dev/dsp`, SDL's `SDL_QueueAudio` and PulseAudio's simple API work this
  way. It's easier, with more latency.

Faun can't hand the platform an effectful callback, and the host must not
retain even a pure function after the call returns. So neither model maps
directly.

## Proposal: push for batch, a reactor source for interactive

**Batch (a player, a synthesizer that renders a file):** audio output is a
stream of frames, exactly like `Stdout`:

```faun
Audio.open_output! : (Audio, Format) -> Result(AudioOut, [NoDevice, Unsupported, Other(Nat)])
AudioOut.write! : (AudioOut, Samples) -> Result(Nat, [Disconnected, Other(Nat)])  # frames taken
AudioOut.drain! : AudioOut -> Result({}, ...)     # wait until everything queued has played
AudioOut.close! : AudioOut -> Result({}, ...)

Format : {rate: Nat, channels: Nat}
Samples = List(F32)                               # interleaved, in -1.0 to 1.0
```

- `write!` is partial and blocks, and `write_all!` is the usual Faun loop.
  On a pull platform the host keeps a ring buffer: `write!` copies into it and
  blocks when it is full, and the platform's callback, which is host code on
  the platform's thread, drains it. That callback is written once per target,
  in the target, below Faun.
- **The format is negotiated, not demanded.** `open_output!` asks for a rate
  and channel count, and the returned `AudioOut` reports what the device
  actually runs (`AudioOut.format`). Resampling is a Faun library. The sample
  type is fixed to `F32` interleaved, since every modern mixer is float
  internally and a portable contract should pick one.
- **Time is counted in frames.** `AudioOut.played! : AudioOut -> U64` is the
  one clock that stays in sync with what is heard, and A/V sync uses it, never
  the wall clock.
- **Underruns are counted, not raised.** `AudioOut.underruns! -> Nat`. A
  glitch is a quality problem, not an error that should abort a `?` chain.

**Interactive (a game, a live instrument):** the reactor asks for audio:

```faun
Source : [..., AudioWanted(AudioOut, c)]
Event : [..., AudioWanted(AudioOut, Nat, c)]      # this many frames would keep the buffer full
```

The handler renders that many frames from its state and calls `write!`,
which won't block because the host said there's room, then re-arms the
source. Latency is the host's buffer depth, typically 10 to 20 ms, and every
activation has to finish in less than that. For a total, arena-reset
activation that renders a few hundred frames, that's plausible. It is the
same contract a game's audio thread already has, moved to the one thread.

## Turning the platform's callback into an event

Where the platform insists on a callback, the target converts it into
something a poller can wait on. This is trusted code below Faun, and it never
calls into Faun:

1. **The callback copies from a ring buffer.** A single-producer,
   single-consumer ring sits between Faun (the producer) and the platform's
   audio thread (the consumer). The callback copies out what it needs. If the
   ring runs dry it writes silence and counts an underrun. It never blocks,
   allocates or takes a lock.
2. **Below a threshold, the callback wakes the poller.** It writes to an
   `eventfd` on Linux, calls `SetEvent` on Windows, triggers a `kqueue` user
   event on macOS, or calls `Atomics.notify` in the browser. That handle sits
   in the poller like any socket.
3. **Faun sees `AudioWanted`** and refills the ring in an ordinary
   activation.

The ring's depth is the latency: 512 frames at 48 kHz is about 10.7 ms. The
host may dispatch audio events ahead of others, since dispatch order is
unspecified.

A simpler variant skips the wake-up: the callback only sets a flag, and the
program checks it once per video frame. That works if the ring holds more
than one frame's worth of audio (about 17 ms at 60 Hz, plus margin). The
wake-up handle removes that frame of added latency.

Several platforms need no callback at all:

- **ALSA's kernel PCM device** can be waited on with `poll`.
- **WASAPI in event mode** hands out an event handle to wait on.
- **AAudio** has a blocking write mode.

CoreAudio and the browser's `AudioWorklet` are the ones that force a callback.
The ring-and-wake adapter is one of the shared adapters in
[bindings.md](bindings.md): written once, used by every callback-driven audio
backend.

## Why not a pure render callback?

An attractive alternative: `render : (S, Nat) -> (S, Samples)` is pure, so
the host could call it on the real-time thread with no effect-ordering
problem. It fails on three counts:

1. The host would have to retain the function value across returns, which
   Faun forbids (second-class functions), and the state `S` would have to
   live in the audio thread's custody.
2. Faun's runtime allocates and reference-counts, and neither is real-time
   safe unless the target proves the render path allocation-free.
3. Changing the state from the program (a note on, a volume change) needs a
   channel into the audio thread, which is shared-memory concurrency.

It remains a possible later, optimized contract: "a render function Barb
proves allocation-free and bounded, on a state of fixed size, receiving
messages as values". That is a real-time profile, and it's exactly the kind
of thing whole-program analysis could certify. Not first.

## Input

`open_input!` answers an `AudioIn` with `read!` of frames, symmetric with
output, and a reactor source `AudioReady(AudioIn, c)`. Microphone access
is a capability a platform prompts for, so opening can answer `Denied`.

## Linux without libc

This is the awkward target. Options, in order of plausibility:

1. **The ALSA kernel interface directly.** Open `/dev/snd/pcmC0D0p`, set
   hardware parameters with `SNDRV_PCM_IOCTL_HW_PARAMS`, and write with
   `SNDRV_PCM_IOCTL_WRITEI_FRAMES`. That is all syscalls, and it works when
   nothing else holds the device. On a desktop running PipeWire, the device
   is usually held.
2. **The PipeWire or PulseAudio protocol over a Unix socket.** The Pulse
   native protocol is poorly documented but has been reimplemented outside
   PulseAudio, and PipeWire serves it. It's more code, but it's pure bytes
   over a socket, and it's the right answer on desktops.
3. **A dynamically linked Linux variant** that `dlopen`s `libasound` or
   `libpipewire`. It is the least work, but it gives up the static-binary
   property.

## Mapping check

- **Linux (static):** ALSA ioctls, or the Pulse protocol; push.
- **macOS:** CoreAudio `AudioUnit`; pull callback drains a ring.
- **Windows:** WASAPI shared mode, event-driven; host thread fills from a ring.
- **browser:** `AudioWorklet` + `SharedArrayBuffer` ring; reactor only (no
  blocking).
- **WASI:** none, so the contract is omitted.
- **board:** I2S DMA, double buffer; `AudioWanted` on each DMA half.

The board entry matters: I2S with DMA double buffering is exactly the
`AudioWanted` event, one per half-buffer interrupt, so the reactor form works
from a microcontroller up to a browser.
