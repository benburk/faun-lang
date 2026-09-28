use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reg {
    G0,
    G1,
    F0,
    F1,
    Copy,
}

impl Register for Reg {
    fn number(self) -> u8 {
        match self {
            Self::G0 => 0,
            Self::G1 => 1,
            Self::F0 => 32,
            Self::F1 => 33,
            Self::Copy => 63,
        }
    }
}

const GP: RegSet = RegSet(3);
const FP: RegSet = RegSet(3 << 32);

fn spec(allowed: RegSet, constraint: Constraint<Reg>) -> OperandSpec<Reg> {
    OperandSpec {
        role: Role::Use,
        timing: Timing::Early,
        constraint,
        allowed,
    }
}

fn code(values: usize) -> Code<Reg> {
    Code {
        values,
        operands: Vec::new(),
        instructions: Pool::default(),
        specs: Vec::new(),
        order: Vec::new(),
        block_params: Vec::new(),
        block_param_specs: Vec::new(),
        blocks: Pool::default(),
        functions: vec![Function {
            source: FunctionId::at(0),
            entry: BlockId::at(0),
        }],
        registers: vec![Reg::G0, Reg::G1, Reg::F0, Reg::F1],
        copies: Some(Reg::Copy),
    }
}

fn inst(
    code: &mut Code<Reg>,
    result: Option<usize>,
    uses: &[usize],
    specs: &[OperandSpec<Reg>],
    clobbers: RegSet,
) -> InstId {
    let operands = Range::of(code.operands.len(), uses.len());
    code.operands.extend(uses.iter().copied().map(VReg::at));
    let spec_range = Range::of(code.specs.len(), specs.len());
    code.specs.extend_from_slice(specs);
    if result.is_some() {
        let def = &mut code.specs[spec_range.range().start];
        def.role = Role::Def;
        def.timing = Timing::Late;
    }
    let id = code.instructions.push(Inst {
        operands,
        result: result.map(VReg::at),
        specs: spec_range,
        scratch: RegSet::EMPTY,
        clobbers,
    });
    code.order.push(id);
    id
}

fn block(
    code: &mut Code<Reg>,
    params: &[(usize, RegSet)],
    start: usize,
    end: usize,
    terminator: Terminator<Reg>,
) {
    let range = Range::of(code.block_params.len(), params.len());
    for &(value, allowed) in params {
        code.block_params.push(VReg::at(value));
        code.block_param_specs.push(OperandSpec {
            role: Role::Def,
            ..spec(allowed, Constraint::Any)
        });
    }
    code.blocks.push(Block {
        owner: FunctionId::at(0),
        params: range,
        instructions: Range::of(start, end - start),
        terminator,
    });
}

fn halt(code: &mut Code<Reg>) {
    block(code, &[], 0, code.order.len(), Terminator::Halt);
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one tied read/write fixture and its locations"
)]
fn uses_move_between_banks_and_a_tied_input_survives_its_overwrite() {
    let mut code = code(3);
    inst(
        &mut code,
        Some(0),
        &[],
        &[spec(GP, Constraint::Any)],
        RegSet::EMPTY,
    );
    inst(
        &mut code,
        Some(1),
        &[],
        &[spec(FP, Constraint::Any)],
        RegSet::EMPTY,
    );
    let float = inst(
        &mut code,
        Some(2),
        &[0, 1],
        &[
            spec(FP, Constraint::Any),
            spec(FP, Constraint::Tied(0)),
            spec(FP, Constraint::Any),
        ],
        RegSet::EMPTY,
    );
    let integer = inst(
        &mut code,
        None,
        &[0, 2],
        &[spec(GP, Constraint::Any); 2],
        RegSet::EMPTY,
    );
    halt(&mut code);
    let (live, allocation) = allocate(&code).unwrap();
    assert!(
        allocation.operand_locations[float.index()]
            .iter()
            .all(|location| matches!(location, Location::Register(reg) if FP.contains(*reg)))
    );
    assert!(
        allocation.operand_locations[integer.index()]
            .iter()
            .all(|location| matches!(location, Location::Register(reg) if GP.contains(*reg)))
    );
    let points = &live.blocks[0].instructions[2];
    assert_eq!(
        allocation.location(points.late, VReg::at(2)),
        Some(allocation.operand_locations[float.index()][0])
    );
    assert_ne!(
        allocation.location(points.late, VReg::at(0)),
        allocation.location(points.late, VReg::at(2))
    );
}

#[test]
fn repeated_operands_in_different_banks_keep_both_physical_copies() {
    let mut code = code(2);
    inst(
        &mut code,
        Some(0),
        &[],
        &[spec(GP, Constraint::Any)],
        RegSet::EMPTY,
    );
    inst(
        &mut code,
        Some(1),
        &[],
        &[spec(FP, Constraint::Any)],
        RegSet::EMPTY,
    );
    let uses = inst(
        &mut code,
        None,
        &[0, 0, 1],
        &[
            spec(GP, Constraint::Any),
            spec(FP, Constraint::Any),
            spec(GP, Constraint::Any),
        ],
        RegSet::EMPTY,
    );
    halt(&mut code);
    let (_, allocation) = allocate(&code).unwrap();
    let places = &allocation.operand_locations[uses.index()];
    assert_ne!(places[0], places[1]);
    assert_ne!(places[0], places[2]);
    assert!(matches!(places[1], Location::Register(reg) if FP.contains(reg)));
}

#[test]
fn fixed_duplicate_copies_cannot_be_reused_by_another_operand() {
    let mut code = code(2);
    inst(
        &mut code,
        Some(0),
        &[],
        &[spec(GP, Constraint::Any)],
        RegSet::EMPTY,
    );
    inst(
        &mut code,
        Some(1),
        &[],
        &[spec(FP, Constraint::Any)],
        RegSet::EMPTY,
    );
    inst(
        &mut code,
        None,
        &[0, 0, 1],
        &[
            spec(GP, Constraint::Fixed(Reg::G0)),
            spec(GP, Constraint::Fixed(Reg::G1)),
            spec(GP, Constraint::Any),
        ],
        RegSet::EMPTY,
    );
    halt(&mut code);
    assert!(allocate(&code).unwrap_err().contains("more registers"));
}

#[test]
fn bank_pressure_and_call_clobbers_spill_and_reload_float_values() {
    let mut code = code(5);
    for at in 0..5 {
        inst(
            &mut code,
            Some(at),
            &[],
            &[spec(FP, Constraint::Any)],
            RegSet::EMPTY,
        );
    }
    inst(&mut code, None, &[], &[], FP);
    for at in 0..5 {
        inst(
            &mut code,
            None,
            &[at],
            &[spec(FP, Constraint::Any)],
            RegSet::EMPTY,
        );
    }
    halt(&mut code);
    let (live, allocation) = allocate(&code).unwrap();
    assert_eq!(allocation.stores.len(), 5);
    assert!(
        allocation
            .stores
            .iter()
            .all(|(_, reg, _)| FP.contains(*reg))
    );
    let after_call = live.blocks[0].instructions[5].late;
    for at in 0..5 {
        assert!(matches!(
            allocation.location(after_call, VReg::at(at)),
            Some(Location::Spill(_))
        ));
    }
    assert!(allocation.transitions.iter().any(|t| matches!((t.from, t.to), (Location::Spill(_), Location::Register(reg)) if FP.contains(reg))));
}

#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one cyclic CFG and its bank-constrained edges"
)]
fn loop_edges_swap_banks_and_branch_conditions_are_constrained() {
    let mut code = code(4);
    inst(
        &mut code,
        Some(0),
        &[],
        &[spec(GP, Constraint::Any)],
        RegSet::EMPTY,
    );
    inst(
        &mut code,
        Some(1),
        &[],
        &[spec(FP, Constraint::Any)],
        RegSet::EMPTY,
    );
    code.operands
        .extend([VReg::at(0), VReg::at(1), VReg::at(3), VReg::at(2)]);
    block(
        &mut code,
        &[],
        0,
        2,
        Terminator::Jump {
            target: BlockId::at(1),
            args: Range::of(0, 2),
        },
    );
    block(
        &mut code,
        &[(2, GP), (3, FP)],
        2,
        2,
        Terminator::Branch {
            condition: VReg::at(3),
            allowed: GP,
            then_target: BlockId::at(1),
            then_args: Range::of(2, 2),
            else_target: BlockId::at(2),
            else_args: Range::EMPTY,
        },
    );
    block(&mut code, &[], 2, 2, Terminator::Halt);
    let (live, allocation) = allocate(&code).unwrap();
    assert!(
        matches!(allocation.location(live.blocks[1].terminator, VReg::at(3)), Some(Location::Register(reg)) if GP.contains(reg))
    );
    assert!(
        allocation
            .edge_moves
            .iter()
            .any(|edge| edge.from == BlockId::at(1)
                && edge.target == BlockId::at(1)
                && !edge.moves.is_empty())
    );
}

#[test]
fn impossible_masks_and_ties_are_refused_before_allocation() {
    for specs in [
        (
            spec(GP, Constraint::Any),
            spec(RegSet::EMPTY, Constraint::Any),
        ),
        (
            spec(GP, Constraint::Any),
            spec(FP, Constraint::Fixed(Reg::G0)),
        ),
        (
            spec(GP, Constraint::Fixed(Reg::G0)),
            spec(FP, Constraint::Tied(0)),
        ),
        (
            spec(GP, Constraint::Any),
            spec(RegSet(1 << 63), Constraint::Any),
        ),
    ] {
        let mut code = code(2);
        inst(
            &mut code,
            Some(0),
            &[],
            &[spec(GP, Constraint::Any)],
            RegSet::EMPTY,
        );
        inst(
            &mut code,
            Some(1),
            &[0],
            &<[OperandSpec<Reg>; 2]>::from(specs),
            RegSet::EMPTY,
        );
        halt(&mut code);
        assert!(allocate(&code).is_err());
    }
}

#[test]
fn single_use_tied_copies_propagate_the_consumers_bank_to_loads() {
    let mut code = code(3);
    let both = RegSet(GP.0 | FP.0);
    inst(
        &mut code,
        Some(0),
        &[],
        &[spec(both, Constraint::Any)],
        RegSet::EMPTY,
    );
    inst(
        &mut code,
        Some(1),
        &[0],
        &[spec(both, Constraint::Any), spec(both, Constraint::Tied(0))],
        RegSet::EMPTY,
    );
    inst(
        &mut code,
        Some(2),
        &[1],
        &[spec(FP, Constraint::Any), spec(FP, Constraint::Any)],
        RegSet::EMPTY,
    );
    halt(&mut code);
    let (live, allocation) = allocate(&code).unwrap();
    for (at, value) in [0, 1, 2].into_iter().enumerate() {
        assert!(
            matches!(allocation.location(live.blocks[0].instructions[at].late, VReg::at(value)), Some(Location::Register(reg)) if FP.contains(reg))
        );
    }
}
