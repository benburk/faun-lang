# Graphics and input

**Status: brainstorm.** Nothing exists yet. Graphics is where "portable" and
"efficient" pull hardest in opposite directions, so the proposal is layered.
Each layer is its own optional contract, and a program that uses a lower layer
runs in more places.

## Layers

1. **Display:** windows, input events, and frame timing. Every graphical
   target has it.
2. **Surface:** present a pixel buffer the program computed. It's portable
   everywhere a window is, and fast enough for tools, emulators, and
   software-rendered games.
3. **GPU:** a portable GPU contract modeled on WebGPU.
4. **Native:** Metal, Vulkan, Direct3D 12, a console's PPU, an LCD
   controller. These are target-specific contracts, and a program using one
   compiles only for that target.

## 1. Display

The window system owns the loop (it sends resize, close, input and frame
callbacks), so a graphical program is a reactor program:

```faun
Display.open_window! : (Display, WindowSpec) -> Result(Window, [Unsupported, Other(Nat)])
Window.close! : Window -> Result({}, ...)

WindowSpec : {title: Str, size: {width: Nat, height: Nat}, resizable: Bool}

Source : [..., WindowEvents(Window, c), NextFrame(Window, c)]
Event : [
  ...,
  Input(Window, InputEvent, c),
  Resized(Window, {width: Nat, height: Nat, scale: F32}, c),
  CloseRequested(Window, c),       # the program decides; the host closes nothing
  Frame(Window, Instant, c),       # time to draw the next frame
]

InputEvent : [
  Key({key: Key, pressed: Bool, repeat: Bool}),
  Text(Str),                       # composed text, separate from keys
  Pointer({x: F32, y: F32}),
  Button({button: [Left, Right, Middle, Other(Nat)], pressed: Bool}),
  Scroll({dx: F32, dy: F32}),
  Focus(Bool),
]
```

- **`Frame` is the host's pacing signal.** Wayland's `wl_surface.frame`,
  `requestAnimationFrame`, `CVDisplayLink` and DXGI's frame latency waitable
  object all mean "draw now, it will be shown at the next vblank". The program
  never busy-loops or sleeps for pacing, and a hidden window receives no
  `Frame` events, which saves power for free.
- **Keys and text are separate.** Physical keys are for games and shortcuts,
  and composed text (input method, dead keys) is for typing. Conflating them
  is the classic cross-platform input bug.
- **`CloseRequested` is only a request.** The program closes the window with
  `close!`, or ignores the request to show "unsaved changes?". The host never
  destroys a resource on the program's behalf.

## 2. Surface: pixels

```faun
Window.present! : (Window, Pixels) -> Result({}, [SizeMismatch, Other(Nat)])

Pixels : {width: Nat, height: Nat, data: List(U8)}     # BGRA8, premultiplied, rows packed
```

This is the most portable graphics contract there is, and a good first one:

- **Linux (static):** write into a `wl_shm` buffer (`memfd` + `mmap`), attach,
  commit.
- **Linux console:** DRM dumb buffer + page flip, via ioctls.
- **Windows:** `StretchDIBits`, or `UpdateLayeredWindow`.
- **macOS:** `CGImage` as a `CALayer`'s contents.
- **browser:** `putImageData` on a canvas, from linear memory.
- **sim65, a board:** copy to the LCD controller or framebuffer RAM.

- **One copy per frame, into memory the compositor can read.** Faun's list is
  handed where it lies, and the target copies it into shared memory. At
  1920×1080 that's 8 MB, about a millisecond. That's fine for everything
  except a demanding game, which uses the GPU layer. A later optimization: if
  Barb can see that the frame's list is built fresh and never shared, the
  target can build it directly in the shared buffer.
- **A fixed pixel format.** BGRA8 is what Wayland (`ARGB8888` is BGRA in
  memory), Windows DIBs and most framebuffers take natively. Converting to
  anything else is the target's job, and it's rare.
- **Wayland without libc is realistic.** The Wayland protocol is a documented
  binary protocol over a Unix socket, and shared memory is `memfd_create` plus
  `mmap` plus passing the descriptor with `SCM_RIGHTS`. All of it is
  syscalls. A static Faun binary can open a window on a modern Linux desktop
  with no library at all, which few languages can claim. X11 is also just a
  socket protocol, if Xwayland-only systems matter.

The pure part is where Faun shines: `render : State -> Pixels` is a pure
function, testable without a display, deterministic, and cacheable per
region. A software-rendered UI toolkit is entirely library code.

## 3. GPU: WebGPU-shaped

WebGPU is the obvious model, and not only because it's portable:

- It was designed as the **safe, validated intersection** of Vulkan, Metal
  and Direct3D 12. That is exactly this note's method (intersect the
  guarantees, keep O(1) mapping), already carried out by a standards body,
  with two production implementations (Dawn and wgpu).
- **It has no pointers in its API.** Buffers are handles, and data moves by
  `queue.writeBuffer(buffer, offset, bytes)` and asynchronous mapping. That
  matches Faun's rule that bytes cross the boundary as values and the host
  never holds an address into Faun memory.
- Shaders are WGSL text, a string the program passes in. Later, a Faun subset
  could compile to WGSL or SPIR-V, which is a natural project for a
  first-order, total language.

The problem is object count. A frame touches dozens of buffers, textures,
bind groups and pipelines, and making each one a linear resource that must
be destroyed on every path would be miserable. Proposal:

- **The `Device` is the only linear resource.** Objects created from it are
  unrestricted typed indices (`Buffer`, `Texture`, `Pipeline`) that are valid
  until the device is destroyed. `destroy!` on an individual object is
  available for memory pressure, and using a destroyed object is a
  _validation error the device reports_, as WebGPU already does, not
  undefined behavior. This is region-style ownership: the device is the
  region.
- **Command encoding is pure.** A frame's commands are a Faun value (a list
  of passes and draws) built by pure code, and `queue.submit!(device, commands)`
  is the only effect. The host translates the list into encoder calls. This
  keeps rendering logic pure and testable, and it's cheap: the command list
  is small compared with the GPU work it describes.
- **Presentation** is `Window.present_texture!`, alongside `present!` for
  pixels.

Backends: on Linux the target needs Vulkan, which means `dlopen` of the
loader, so graphics on the GPU needs the dynamically linked Linux variant.
Metal on macOS, D3D12 on Windows, and the browser's real `navigator.gpu`,
which makes the browser target the easiest.

## 4. Native, target-specific contracts

Programs that want the platform's full API use a target-specific contract,
and compile only for that target:

```faun
main!(host) -> (
  ppu = host.nes_ppu      # exists only on an NES target
  ...
)
```

- **Vulkan, Metal and D3D12** are wrapped by the target in Faun-native terms:
  opaque handles, records the target lays out, and explicit effects. Raw C
  declarations are never exposed (see [host-effects.md](../host-effects.md)).
  Generating these wrappers from the API registries (Vulkan's `vk.xml`,
  Metal's headers) is the only realistic way, as the archived host-interface
  draft already noted for structs.
- **Retro and embedded video** (NES PPU, a Game Boy LCD, an SPI display) are
  small, exact contracts, and the most satisfying kind: `ppu.write_oam!`,
  `lcd.blit!(rect, pixels)`. The `Frame` event maps to the vblank interrupt.

## Things to keep out

- **Immediate-mode drawing primitives in the host** (lines, text, rects).
  That's a library over `present!` or the GPU layer. Putting it in the host
  means every target reimplements a 2D renderer.
- **Native widgets.** A portable widget contract is a toolkit design problem
  (see SWT, wxWidgets, and every attempt since), and it can't be O(1) per
  call. Leave it to target-specific contracts.
- **Callbacks that re-enter.** Win32's `WndProc` and macOS's run loop call
  into the program while it's inside a host call. The target's reactor shell
  absorbs this: it pumps the platform's loop, queues what arrives, and
  delivers one event per activation.
