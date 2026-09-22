# Target instruction IR research

Status: design research, not a phase contract.

Faun's Barb and machine IR should remain above target instructions. This note compares LLVM, MLIR, and nesfab to identify the target-level representation and phase boundaries to add below them.

## Conclusion

Use LLVM's machine-code architecture for an opt-in register-machine toolkit, MLIR's block-argument, effect, and verifier ideas to tighten that toolkit's contracts, and nesfab's state-search code generation as a separate target-owned design for the 6502.

The only mandatory target boundary should remain the existing one:

```text
prepared faun_core::ir::Program -> target-owned lowering -> Artifact
```

A backend may opt into a register-machine library providing:

- target instruction storage;
- virtual value identity;
- blocks, edges, and block arguments;
- symbolic machine operands;
- register topology and instruction constraints;
- declared effects;
- segmented liveness;
- parallel-copy planning;
- verified phase boundaries.

X86 and a future ARM backend are likely users. The 6502 may instead jointly choose instructions and locations by searching concrete CPU states, with its own intermediate forms and verifier. Wasm can continue lowering directly to its structured stack machine. A useful algorithm may be extracted into a smaller library, but no backend should implement a shared representation merely to satisfy `Target`.

## What LLVM gets right

LLVM keeps a target-independent `MachineFunction` container whose instructions are only a target opcode plus operands. The target description, rather than `MachineInstr`, says what an opcode means. The same representation can hold SSA virtual registers before allocation and physical registers afterward. Its code generator then lowers this richer machine representation into a smaller MC layer containing encoded registers, immediates, labels, and symbolic expressions.

That separation fits Faun:

```text
prepared faun_core::ir::Program
    -> selected target function
    -> allocated target function
    -> laid-out encoding instructions and fixups
    -> artifact
```

The selected target function should retain facts that an encoder cannot recover: virtual values, stack-slot identities, block edges, constant-pool entries, call clobbers, and instruction effects. The encoding layer should contain only facts needed to choose bytes and resolve labels or relocations.

### Narrow facts by phase

GlobalISel uses one machine representation while tightening its facts in stages:

```text
low-level value type
    -> register bank
    -> register class
    -> physical register
```

This is useful even though Faun does not need GlobalISel's full generic legalizer. A Faun value can begin with a target value class, selection can constrain each operand to a register class or bank, and allocation can choose a physical register. None of these choices should replace the value's identity.

GlobalISel also separates default and alternative register-bank mappings and assigns costs to cross-bank copies. That is a useful shape for future ARM vector/scalar banks and for 6502 distinctions among A, X, Y, zero-page pairs, and memory. It should remain optional policy rather than a mandatory pass for today's scalar targets.

### Keep one central instruction description

LLVM's instruction descriptors centralize:

- explicit operand kinds and register classes;
- tied operands and early-clobber definitions;
- implicit physical-register uses and definitions;
- load, store, call, branch, return, barrier, and trap properties;
- unmodeled effects;
- scheduling class;
- pseudo, rematerializable, and commutable properties.

The x86 and ARM definitions show why this information cannot remain in emitter methods. X86 division fixes values to accumulator registers; calls carry register masks; arithmetic often ties an input to an output; EFLAGS is hidden state. ARM adds CPSR dependencies, predication, early-clobber results, register pairs, even/odd or consecutive-register requirements, and instruction bundles that cannot be separated.

Faun should express relational register constraints directly rather than copy LLVM's `hasExtraSrcRegAllocReq` and `hasExtraDefRegAllocReq` escape hatches. Operand timing must be part of the same description:

```rust
pub struct OperandSpec {
    pub role: Role,          // Use or Def
    pub timing: Timing,      // Early or Late
    pub constraint: Constraint,
}

pub enum Constraint {
    Any(RegClassId),
    Fixed(PRegId),
    Tied(OperandIndex),
    Distinct(OperandIndex),
    Consecutive {
        first: OperandIndex,
        count: u8,
        alignment: u8,
    },
}
```

An early definition conflicts with inputs consumed later; a late definition may reuse the location of an input killed early. A tie requires equal locations but does not merge the operands' value identities.

Register classes alone are not enough for ARM pairs or overlapping 6502 byte pairs. Physical registers should map to register-unit bitsets, with classes and banks defined over those units.

Prefer distinct opcodes when an instruction has materially different effects. For example, `add` and `adds` are simpler to verify than an optional flags definition. A compact target enum with an exhaustive `spec()` match is enough initially; Faun does not need TableGen or MLIR's runtime operation registry.

### Preserve symbolic operands

LLVM's `MachineOperand` distinguishes registers, immediates, basic blocks, frame indices, constant-pool indices, jump tables, external symbols, global addresses, block addresses, and register masks. That broad distinction is worth copying.

Do not copy x86's representation of one address as five adjacent untyped operands. Use a typed address pool while exposing its register uses to liveness and constraints:

```rust
pub struct Address {
    pub base: Option<VReg>,
    pub index: Option<(VReg, Scale)>,
    pub displacement: i32,
    pub segment: Option<PRegId>,
    pub symbol: Option<SymbolRef>,
}
```

A frame reference remains `StackSlotId` until frame layout. A branch remains `BlockId` until code layout. A symbol retains its relocation kind and addend until the artifact writer can resolve it.

### Use segmented live ranges, but keep stable value identity

LLVM's `LiveRange` is an ordered set of disjoint `[start, end)` segments and explicitly supports holes. It also distinguishes early and late values at an instruction. LLVM's greedy allocator gains much of its quality by splitting around busy regions and loops, then evicting or spilling the less valuable pieces.

Faun should adopt the segment representation and loop-aware splitting. It should not adopt the incidental practice of representing every split by rewriting the program to unrelated virtual-register identities. A `VReg` remains the semantic value; allocation assigns locations to segments of that value and records transitions between them.

Kill and dead flags should be derived analysis, not mutable authority stored on operands. Recompute them when an encoder or peephole pass needs them.

### Keep instruction selection conservative around sharing

GlobalISel walks use-def chains to fold producers into selected instructions and requires a safety query before sinking or folding. This is the right rule for Faun's SSA DAG: matching an address expression does not imply that every matched producer disappears. A producer with another use still needs selected code unless the chosen recipe explicitly produces both required forms.

Start with one selected recipe and use counts. Later, a target may expose alternative recipes and costs without changing the instruction representation.

## What MLIR contributes

MLIR's x86, ArmNeon, and ArmSVE dialects are not physical machine IRs. They describe typed semantic operations and usually lower to LLVM intrinsics. They do not model physical registers, spills, calling conventions, or final instruction constraints. They are therefore not a direct template for Faun's target IR.

Three MLIR ideas are still useful.

### Block arguments instead of phi instructions

MLIR blocks take arguments, and branch-like terminators supply successor operands. The parallel-copy semantics are visible on the edge rather than hidden in special phi instructions.

The target CFG should use the same shape:

```rust
pub struct Block {
    pub params: Range<VReg>,
    pub inst_order: Range<InstId>,
    pub terminator: Terminator,
}

pub struct Edge {
    pub from: BlockId,
    pub to: BlockId,
    pub args: Range<VReg>,
}
```

An explicit `EdgeId` gives critical-edge splitting and edge-copy placement one owner. Block identity remains separate from block layout order.

### Structural verification before semantic verification

MLIR verifies storage shape and generic operation invariants before custom operation and region invariants. Faun should follow that ordering:

1. IDs and ranges refer to the same function.
2. Instruction arity agrees with its opcode description.
3. Every virtual value has one definition and every use is dominated.
4. Block parameters and edge arguments agree.
5. Operand classes, ties, timing, and relational constraints are satisfiable.
6. Phase-specific invariants hold.

Later checks may then index pools and inspect target semantics without repeating malformed-storage checks.

### Staged effects over named resources

MLIR distinguishes SSA data flow from implicit behavior and allows effects to name resources and stages. That is more useful for scheduling than a few `mayLoad` and `mayStore` booleans.

A compact target form could be:

```rust
pub struct Effect {
    pub resource: Resource,
    pub access: Access,
    pub timing: Timing,
}

pub enum Resource {
    Memory,
    StackSlot(StackSlotId),
    Flags(FlagBankId),
    RuntimeState(RuntimeResourceId),
}
```

Start conservatively: arbitrary memory accesses conflict, calls touch unknown memory and runtime state, and all flags in one bank conflict. Stack slots can be disjoint immediately. Allocatable or ABI-visible registers remain explicit operands, including implicit operands from the opcode description. Non-allocatable state such as condition-code banks belongs in resource effects instead, avoiding duplicate dependency models.

MLIR's open dialect and dynamic interface machinery would add little here. Faun has three concrete backends and can use target-owned enums plus exhaustive Rust matches.

## What nesfab changes for the 6502

Nesfab does not run ordinary instruction selection followed by ordinary register allocation. It schedules each basic block's SSA DAG, then processes the schedule while tracking an approximation of the complete CPU state. Its state includes:

- which values A, X, Y, carry, zero, and negative state represent;
- known constants in those resources;
- conditional state;
- values that still require a memory store.

For each source operation, continuation-based recipes generate valid instruction sequences. States with the same observable result are hash-equivalent, so the selector retains the cheapest sequence and prunes the rest. The inspected cost function heavily weights cycles, then bytes, with small target-specific penalties.

The scheduler is equally target-aware. It starts from SSA dependencies, then adds dependencies for global memory, carry producers and clobberers, phi behavior, and addressing locality. Ready operations are ranked partly by path length to keep dependent work together and shorten live ranges.

Across blocks, nesfab propagates possible output CPU states to successor inputs until no new useful states appear. Each block retains several `(entry state, exit state, code, cost)` choices. A PBQP problem then selects one choice per block, with CFG-edge costs representing the loads or transfers needed to reconcile adjacent states.

This directly addresses the weakness reported by an LLVM-MOS contributor: LLVM's greedy allocator handles zero-page cache locations reasonably, but tight A/X/Y classes produce many spurious copies. A generic allocator sees scarce asymmetric registers as a difficult coloring problem; nesfab makes their contents part of instruction-selection state.

### Implication for Faun

Do not force the 6502 through either the x86 allocator or its instruction container. The backend pipelines may have genuinely different intermediate forms:

```text
x86 / future ARM:
    prepared Program
        -> select into register-machine function
        -> schedule -> allocate -> layout -> encode

6502:
    target-owned SSA block DAG
        -> schedule
        -> generate (instruction, CPU-state) alternatives
        -> propagate block states
        -> choose block alternatives
        -> target-owned instruction sequence
        -> layout -> encode

wasm:
    structured machine IR -> wasm control and operand stack -> module
```

The 6502's candidate, CPU-state, PBQP, and final instruction structures should remain target-owned. If both native backends eventually need a dependency DAG or parallel-copy planner, extract that named algorithm behind a small input contract. Do not make the 6502 convert into and back out of an x86-shaped function merely to reuse it.

A parallel-copy planner is a plausible narrow library. It can return a `MovePlan` and cost without immediately encoding it. The 6502 backend could use that cost in PBQP edge matrices; x86 could emit the same plan for block edges, calls, and allocation splits. Wasm need not use it: its stack-based transfer is already a different implementation strategy.

Nesfab's search should be adopted selectively. Its bounded candidate count, state hashing, and target-weighted costs fit the 6502. Applying the same state space to x86 would grow rapidly and discard the mature split-allocation model that works well on larger register files.

## Proposed opt-in shape

Keep `faun_core::targets::Target` unchanged: a target owns everything below machine IR and only promises checked preparation and artifact emission. Initially, put the register-machine implementation inside the x86 crate. That gives its storage and phase contracts one real caller before an abstraction is chosen.

```text
crates/x86-64-linux/src/
    selected.rs     selected SSA CFG and target constraints
    selected/register_allocate.rs segmented liveness and split allocation
    machine.rs      allocated symbolic instructions
    parallel_copy.rs simultaneous location transfers
    selected/register_allocate/lower.rs allocated lowering
    encode.rs       layout and bytes

crates/mos6502-sim65/src/
    schedule.rs
    state.rs
    candidate.rs
    choose.rs
    inst.rs
    layout.rs
    encode.rs

crates/wasm32-wasi/src/
    lower.rs
    module.rs
```

If ARM or another conventional register target arrives and the x86 shape survives that second caller, extract `machine/`, its verifier, liveness, and allocator into an optional workspace crate. That crate may own a typed function:

```rust
pub struct Function<O, P> {
    storage: FunctionStorage<O>,
    phase: PhantomData<P>,
}

pub enum Selected {}
pub enum Allocated {}
pub enum LaidOut {}
```

Only backends choosing this crate see those types. The wrappers consume and reuse the same arenas; they need not clone instructions. Constructors remain private so only verified transitions can produce the next phase. Target opcodes, register descriptions, selection recipes, costs, ABI policy, and encoding remain with the backend.

### Selected phase

- target opcodes only;
- virtual values remain SSA;
- block parameters and edge arguments are explicit;
- stack slots, symbols, labels, and constants remain symbolic;
- every opcode has a complete constraint, operand-timing, and effect description;
- no physical assignment is implied by instruction selection.

### Allocated phase

- every live segment has a compatible location;
- fixed registers, ties, early clobbers, distinctness, groups, and call masks hold;
- live values survive implicit clobbers;
- edge and split transitions are explicit parallel copies or resolved move plans;
- pseudos remaining after allocation have declared scratch and clobber contracts.

A pseudo that needs fresh virtual values expands before allocation. A pseudo retained afterward may only use physical scratch resources declared in its opcode description.

An x86 or ARM user reaches this phase through a segmented allocator. The 6502 does not need this phase type.

### Laid-out phase

- stack slots have offsets;
- saved-register and scratch areas are fixed;
- constant-pool entries have placement;
- branch forms have been relaxed;
- late pseudos require no undeclared register;
- unresolved external references exist only as typed fixups.

The final encoder should reject virtual values, abstract stack references, unresolved local labels, and parallel copies.

## Decisions for Faun

Adopt:

- the existing rule that each target owns everything below machine IR;
- an opt-in LLVM-like split between machine instructions and encoding instructions for conventional register targets;
- LLVM's opcode-plus-operands storage with target-owned descriptions inside that toolkit;
- LLVM's register classes, banks, units, symbolic frame indices, register masks, and segmented liveness for toolkit users;
- MLIR block arguments, layered verification, and staged resource effects where a backend's chosen representation benefits from them;
- nesfab's target-owned 6502 CPU-state search, bounded alternatives, cross-block state propagation, and transition-aware block choice;
- narrowly extracted algorithms such as parallel-copy planning only after their callers expose the same contract.

Adapt:

- retain stable Faun value identity across live-range splits;
- use typed address records instead of flattened x86 address operands;
- use explicit relational constraints instead of target-specific allocator escape flags;
- use Rust enums and exhaustive `spec()` matches before considering generated descriptions;
- expose scheduler dependency construction but let targets rank ready nodes.

Avoid:

- making one target instruction form part of the `Target` contract;
- assigning physical registers during ordinary x86/ARM instruction selection;
- forcing the 6502 through an x86-shaped container or allocator;
- treating MLIR's target intrinsic dialects as final machine instructions;
- storing kill/dead flags as authoritative mutable state;
- late pseudo expansion with undeclared scratch requirements;
- a universal dynamic operation framework or TableGen clone before repetition warrants one.

## First implementation slices

First, separate the x86 lowerer from byte encoding without changing its allocation policy:

1. Add an x86-local allocated instruction sequence with typed opcodes and physical registers.
2. Keep labels, frame slots, and data references symbolic through that sequence.
3. Verify the allocated sequence, then make the encoder its only byte-producing consumer.
4. Isolate the current rematerialization, use-count, frame-slot, and scratch plan as an x86-local compatibility allocator.
5. Preserve the current all-spilled allocation and generated-code baselines.

These five steps established the phase boundary. The temporary compatibility allocator then provided a byte-authoritative baseline while the selected path was completed and compared.

The selected form in `selected.rs` flattens prepared regions into target-local blocks, retains source values as virtual SSA registers, and carries block arguments explicitly on edges. Opcode descriptions declare operand timing, fixed and tied constraints, effects, implicit clobbers, expansion kind, and scratch registers.

`parallel_copy.rs` plans target-local simultaneous transfers, removes aliases, orders dependencies, breaks cycles through a reserved temporary, retains input-copy identity, and reports instruction and memory-transition costs. Symbolic stack moves declare their expansion and scratch requirements.

The selected pipeline computes CFG liveness to a fixed point and performs split allocation. It keeps live values in registers across instruction points, spills under pressure, splits around early uses and late definitions, honors fixed and tied operands, vacates scratch registers, preserves values across implicit clobbers, records segmented ranges and transitions, and plans operand and edge copies. Verification checks liveness coverage, register interference, constraints, clobbers, spill bounds, and copy plans.

That verified allocation is now byte-authoritative. It lowers every selected opcode, transition, CFG edge, call boundary, frame reference, and late pseudo into the separately verified `machine::Allocated` sequence consumed by `encode`. R11 is reserved as the stack-copy expansion register. Spill slots are dense, frames are function-local, and functions without emitted split or copy traffic omit them. Clobber-preserving stores run before an instruction while reloads run after it. Register hints, fallthrough layout, and local rematerialization keep every generated-size ratchet at or below its compatibility baseline; the compatibility allocator and lowerer have been removed. Next:

1. Prototype one 6502 block with target-owned nesfab-style CPU-state candidates, sharing no representation initially.

After both target paths work, compare their concrete copy, dependency, ID, and layout code. Extract only pieces with matching invariants and ordinary callers. The architectural test is not whether the 6502 fits the x86 representation; it is whether both backends can remain independently coherent while reusing the few algorithms they genuinely share.

## Sources

- [LLVM Code Generator](https://llvm.org/docs/CodeGenerator.html)
- [LLVM Generic Machine IR](https://llvm.org/docs/GlobalISel/GMIR.html)
- [LLVM RegBankSelect](https://llvm.org/docs/GlobalISel/RegBankSelect.html)
- [LLVM InstructionSelect](https://llvm.org/docs/GlobalISel/InstructionSelect.html)
- [LLVM MIR language reference](https://llvm.org/docs/MIRLangRef.html)
- [LLVM `MachineOperand.h`](https://github.com/llvm/llvm-project/blob/fd4bcc57cd7f2aabc409768097a976edc40ff05b/llvm/include/llvm/CodeGen/MachineOperand.h)
- [LLVM `MCInstrDesc.h`](https://github.com/llvm/llvm-project/blob/fd4bcc57cd7f2aabc409768097a976edc40ff05b/llvm/include/llvm/MC/MCInstrDesc.h)
- [LLVM `LiveInterval.h`](https://github.com/llvm/llvm-project/blob/fd4bcc57cd7f2aabc409768097a976edc40ff05b/llvm/include/llvm/CodeGen/LiveInterval.h)
- [LLVM x86 instruction descriptions](https://github.com/llvm/llvm-project/blob/fd4bcc57cd7f2aabc409768097a976edc40ff05b/llvm/lib/Target/X86/X86InstrInfo.td)
- [LLVM ARM instruction descriptions](https://github.com/llvm/llvm-project/blob/fd4bcc57cd7f2aabc409768097a976edc40ff05b/llvm/lib/Target/ARM/ARMInstrInfo.td)
- [Greedy Register Allocation in LLVM 3.0](https://blog.llvm.org/2011/09/greedy-register-allocation-in-llvm-30.html)
- [MLIR language reference](https://mlir.llvm.org/docs/LangRef/)
- [MLIR operation definition specification](https://mlir.llvm.org/docs/DefiningDialects/Operations/)
- [MLIR side effects and speculation](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
- [MLIR X86 dialect definitions](https://github.com/llvm/llvm-project/blob/fd4bcc57cd7f2aabc409768097a976edc40ff05b/mlir/include/mlir/Dialect/X86/X86.td)
- [MLIR ArmNeon dialect definitions](https://github.com/llvm/llvm-project/blob/fd4bcc57cd7f2aabc409768097a976edc40ff05b/mlir/include/mlir/Dialect/ArmNeon/ArmNeon.td)
- [Explaining my fast 6502 code generator](https://pubby.games/codegen.html)
- [nesfab source](https://github.com/pubby/nesfab/tree/140255614767f715c18ede37c30b4eac1cffdc7f)
- [2023 nesfab discussion](https://news.ycombinator.com/item?id=35294111)
