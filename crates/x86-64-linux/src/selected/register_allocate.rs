//! Register allocation for selected x86 code: the shared allocator of
//! [`faun_core::codegen::registers`], over this target's registers, then
//! lowering what it says to symbolic instructions.

mod lower;

use super::{Inst, OperandSpec, Reg, RegSet, Selected, Terminator};
use crate::machine::Allocated;
use faun_core::codegen;
use faun_core::codegen::registers::{self, Code};
use faun_core::index::Range;
use faun_core::ir::FunctionId;
use lower::COPY_SCRATCH;

pub(super) use registers::{BlockPoints, InstPoints, Liveness, Point, place};

type Allocation = registers::Allocation<Reg>;
type Location = registers::Location<Reg>;
type Transition = registers::Transition<Reg>;

/// Every register a value may be held in. Nothing outside the program
/// calls into it, so none needs keeping for a caller: a call clobbers all
/// of them, and `rbx`, `r11` and `rsp` keep their own jobs.
const REGISTERS: [Reg; 29] = [
    Reg::Rax,
    Reg::Rcx,
    Reg::Rdx,
    Reg::Rsi,
    Reg::Rdi,
    Reg::R8,
    Reg::R9,
    Reg::R10,
    Reg::R12,
    Reg::R13,
    Reg::R14,
    Reg::R15,
    Reg::Rbp,
    Reg::Xmm0,
    Reg::Xmm1,
    Reg::Xmm2,
    Reg::Xmm3,
    Reg::Xmm4,
    Reg::Xmm5,
    Reg::Xmm6,
    Reg::Xmm7,
    Reg::Xmm8,
    Reg::Xmm9,
    Reg::Xmm10,
    Reg::Xmm11,
    Reg::Xmm12,
    Reg::Xmm13,
    Reg::Xmm14,
    Reg::Xmm15,
];

pub(super) fn allocate(selected: &Selected, entry: FunctionId) -> Result<Allocated, String> {
    let code = selected.code(entry);
    let (liveness, allocation) = registers::allocate(&code)?;
    lower::lower(selected, &liveness, &allocation, entry)
}

fn set(held: RegSet) -> codegen::RegSet {
    codegen::RegSet(u64::from(held.0))
}

impl Selected {
    /// What the allocator is handed: the same pools, with each instruction's
    /// constraints read off its opcode, and the logical entry exiting with
    /// its status in `rdi` where every other function answers in `rax`.
    fn code(&self, entry: FunctionId) -> Code<Reg> {
        let mut specs = Vec::new();
        let instructions = self
            .instructions
            .iter()
            .map(|inst| allocated(inst, &mut specs))
            .collect();
        let blocks = self
            .blocks
            .iter()
            .map(|block| registers::Block {
                owner: block.owner,
                params: block.params,
                instructions: block.instructions,
                terminator: terminator(block.terminator, block.owner == entry),
            })
            .collect();
        let functions = self
            .functions
            .iter()
            .map(|function| registers::Function {
                source: function.source,
                entry: function.entry,
            })
            .collect();
        Code {
            values: self.widths.len(),
            operands: self.operands.clone(),
            instructions,
            specs,
            order: self.order.clone(),
            block_params: self.block_params.clone(),
            block_param_specs: self.block_param_specs.clone(),
            blocks,
            functions,
            registers: REGISTERS.to_vec(),
            copies: Some(COPY_SCRATCH),
        }
    }
}

/// One instruction as the allocator sees it, its constraints appended to
/// `specs`: its result's first, then each operand's.
fn allocated(inst: &Inst, specs: &mut Vec<OperandSpec>) -> registers::Inst {
    let count = usize::from(inst.result.is_some()) + inst.operands.len();
    let start = specs.len();
    specs.extend((0..count).map(|at| {
        inst.operand_spec(at)
            .expect("a verified selected instruction")
    }));
    let requirements = inst.opcode.requirements();
    registers::Inst {
        operands: inst.operands,
        result: inst.result,
        specs: Range::of(start, count),
        scratch: set(requirements.scratch),
        clobbers: set(requirements.effects.clobbers),
    }
}

/// How a block ends, a return answering in `rdi` where it leaves the
/// program and in `rax` otherwise.
const fn terminator(terminator: Terminator, exits: bool) -> registers::Terminator<Reg> {
    match terminator {
        Terminator::Jump { target, args } => registers::Terminator::Jump { target, args },
        Terminator::Branch {
            condition,
            then_target,
            then_args,
            else_target,
            else_args,
        } => registers::Terminator::Branch {
            condition,
            allowed: super::GPRS,
            then_target,
            then_args,
            else_target,
            else_args,
        },
        Terminator::Return { values } => registers::Terminator::Return {
            values,
            register: if exits { Reg::Rdi } else { Reg::Rax },
        },
        Terminator::Halt => registers::Terminator::Halt,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::selected::select;
    use faun_core::ir::{Binary, Class, Program};

    #[test]
    fn loops_produce_segmented_live_ranges_and_edge_costs() {
        let program = faun_core::programs::carries_a_total_into_an_arm(3);
        let selected = select(&program).unwrap();
        let (_, allocation) = registers::allocate(&selected.code(program.entry())).unwrap();
        assert!(!allocation.segments.is_empty());
        assert!(allocation.edges > 0);
    }

    #[test]
    fn repeated_values_receive_each_fixed_operand_register() {
        let (mut program, main) = Program::new("main");
        program.define(main, |builder, _| {
            let one = builder.constant(Class::Word, 1);
            let two = builder.constant(Class::Word, 2);
            let value = builder.binary(Binary::Add, one, two);
            let quotient = builder.binary(Binary::Div, value, value);
            builder.ret(&[quotient]);
        });
        let selected = select(&program).unwrap();
        let divide = selected
            .instructions
            .iter()
            .position(|inst| inst.opcode == super::super::Opcode::Divide)
            .unwrap();
        let (_, allocation) = registers::allocate(&selected.code(program.entry())).unwrap();
        assert_eq!(
            allocation.operand_locations[divide],
            [Location::Register(Reg::Rax), Location::Register(Reg::Rcx)]
        );
        assert!(!allocation.operand_moves[divide].is_empty());
    }

    #[test]
    fn register_pressure_creates_spilled_segments() {
        let (mut program, main) = Program::new("main");
        program.define(main, |builder, _| {
            // More live at once than there are registers.
            let mut values: Vec<_> = (0..u64::try_from(13 + 4).unwrap())
                .map(|value| builder.constant(Class::Word, value))
                .collect();
            while values.len() > 1 {
                let right = values.pop().unwrap();
                let left = values.pop().unwrap();
                values.push(builder.binary(Binary::Add, left, right));
            }
            builder.ret(&values);
        });
        let selected = select(&program).unwrap();
        let (_, allocation) = registers::allocate(&selected.code(program.entry())).unwrap();
        assert!(
            allocation
                .segments
                .iter()
                .any(|segment| matches!(segment.location, Location::Spill(_)))
        );
    }

    #[test]
    fn calls_split_values_around_their_clobber_mask() {
        let (mut program, main) = Program::new("main");
        let helper = program.declare("helper", &[], &[Class::Word]);
        program.define(helper, |builder, _| {
            let answer = builder.constant(Class::Word, 3);
            builder.ret(&[answer]);
        });
        // More values live across the call than a call leaves registers
        // for, so some wait in memory.
        program.define(main, |builder, _| {
            let one = builder.constant(Class::Word, 1);
            let across: Vec<_> = (0..8)
                .map(|at| {
                    let other = builder.constant(Class::Word, at);
                    builder.binary(Binary::Add, one, other)
                })
                .collect();
            let mut sum = builder.call_one(helper, &[]);
            for value in across {
                sum = builder.binary(Binary::Add, sum, value);
            }
            builder.ret(&[sum]);
        });
        let selected = select(&program).unwrap();
        let (_, allocation) = registers::allocate(&selected.code(program.entry())).unwrap();
        assert!(allocation.transitions.iter().any(|transition| {
            matches!(transition.from, Location::Register(_))
                && matches!(transition.to, Location::Spill(_))
        }));
    }

    /// A call whose answer is the function's answer jumps to what it calls,
    /// which returns to the caller's caller.
    #[test]
    fn a_call_in_tail_position_is_a_jump() {
        let (mut program, main) = Program::new("main");
        let helper = program.declare("helper", &[Class::Word], &[Class::Word]);
        let inner = program.declare("inner", &[Class::Word], &[Class::Word]);
        program.define(inner, |builder, args| {
            let one = builder.constant(Class::Word, 1);
            let sum = builder.binary(Binary::Add, args[0], one);
            builder.ret(&[sum]);
        });
        program.define(helper, |builder, args| {
            let two = builder.constant(Class::Word, 2);
            let doubled = builder.binary(Binary::Mul, args[0], two);
            let answer = builder.call_one(inner, &[doubled]);
            builder.ret(&[answer]);
        });
        program.define(main, |builder, _| {
            let one = builder.constant(Class::Word, 1);
            let answer = builder.call_one(helper, &[one]);
            builder.ret(&[answer]);
        });
        let allocated = crate::selected::select_and_allocate(&program).unwrap();
        let calls = allocated
            .instructions()
            .iter()
            .filter(|inst| matches!(inst, crate::machine::Inst::Call { .. }))
            .count();
        // `main` calls `helper`, and `helper` jumps to `inner`.
        assert_eq!(calls, 1);
    }

    /// One value across a call waits in a register the call leaves alone,
    /// and a function writing one of those puts it back before returning.
    #[test]
    fn a_value_across_a_call_waits_where_the_call_leaves_it() {
        let (mut program, main) = Program::new("main");
        let helper = program.declare("helper", &[Class::Word], &[Class::Word]);
        let inner = program.declare("inner", &[], &[Class::Word]);
        program.define(inner, |builder, _| {
            let answer = builder.constant(Class::Word, 3);
            builder.ret(&[answer]);
        });
        program.define(helper, |builder, args| {
            let answer = builder.call_one(inner, &[]);
            let sum = builder.binary(Binary::Add, args[0], answer);
            builder.ret(&[sum]);
        });
        program.define(main, |builder, _| {
            let one = builder.constant(Class::Word, 1);
            let answer = builder.call_one(helper, &[one]);
            builder.ret(&[answer]);
        });
        let allocated = crate::selected::select_and_allocate(&program).unwrap();
        let instructions = allocated.instructions();
        // In `helper`, its argument outlives the call to `inner` in a kept
        // register, which it saves on entry and restores before `ret`.
        assert!(!instructions.iter().any(|inst| matches!(
            inst,
            crate::machine::Inst::StoreFrame { src, .. } if !lower::CALLEE_SAVED.contains(src)
        )));
        assert!(instructions.iter().any(|inst| matches!(
            inst,
            crate::machine::Inst::StoreFrame { src, .. } if lower::CALLEE_SAVED.contains(src)
        )));
    }
}
