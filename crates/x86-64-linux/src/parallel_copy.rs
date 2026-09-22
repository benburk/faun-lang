//! X86-local planning for simultaneous location transfers.
//!
//! A plan preserves each source as it existed before any destination was
//! written. It removes aliases, orders acyclic moves backwards through their
//! dependencies, and breaks cycles through one caller-provided temporary.
//! Moves remain symbolic: stack-to-stack expansion and its scratch register
//! are declared here but chosen by the later allocated lowering.

use super::machine::{FrameSlot, Reg};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Place {
    Register(Reg),
    Frame(FrameSlot),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CopySource {
    Place(Place),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Copy {
    source: CopySource,
    destination: Place,
}

impl Copy {
    pub(crate) const fn between(source: Place, destination: Place) -> Self {
        Self {
            source: CopySource::Place(source),
            destination,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CopyId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Move {
    source: CopySource,
    destination: Place,
    origin: Option<CopyId>,
}

impl Move {
    pub(crate) const fn source(self) -> CopySource {
        self.source
    }

    pub(crate) const fn destination(self) -> Place {
        self.destination
    }

    pub(crate) const fn requirements(self) -> MoveRequirements {
        let (instructions, memory_reads, memory_writes, scratch_gprs) =
            match (self.source, self.destination) {
                (CopySource::Place(Place::Register(_)), Place::Register(_)) => (1, 0, 0, 0),
                (CopySource::Place(Place::Frame(_)), Place::Register(_)) => (1, 1, 0, 0),
                (CopySource::Place(Place::Register(_)), Place::Frame(_)) => (1, 0, 1, 0),
                (CopySource::Place(Place::Frame(_)), Place::Frame(_)) => (2, 1, 1, 1),
            };
        MoveRequirements {
            instructions,
            memory_reads,
            memory_writes,
            scratch_gprs,
        }
    }
}

/// Expansion resources for one symbolic move. Every scratch GPR is clobbered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MoveRequirements {
    pub instructions: u8,
    pub memory_reads: u8,
    pub memory_writes: u8,
    pub scratch_gprs: u8,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct TransitionCost {
    pub instructions: u32,
    pub memory_accesses: u32,
}

impl TransitionCost {
    fn add(self, requirements: MoveRequirements) -> Option<Self> {
        Some(Self {
            instructions: self
                .instructions
                .checked_add(u32::from(requirements.instructions))?,
            memory_accesses: self.memory_accesses.checked_add(
                u32::from(requirements.memory_reads) + u32::from(requirements.memory_writes),
            )?,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum PlanError {
    TooManyCopies,
    DuplicateDestination(Place),
    TemporaryRequired,
    TemporaryInUse(Place),
    CostOverflow,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct MovePlan {
    moves: Vec<Move>,
    cost: TransitionCost,
}

impl MovePlan {
    pub(crate) fn moves(&self) -> &[Move] {
        &self.moves
    }

    pub(crate) const fn cost(&self) -> TransitionCost {
        self.cost
    }
}

#[derive(Clone, Copy)]
struct Pending {
    source: CopySource,
    destination: Place,
    origin: CopyId,
}

/// Plan simultaneous copies, using `temporary` only when a cycle requires it.
///
/// A supplied temporary must be reserved for this transition. Acyclic callers
/// may pass `None`; a cycle then reports [`PlanError::TemporaryRequired`].
/// Inputs are borrowed and no state changes on failure.
#[expect(
    clippy::too_many_lines,
    reason = "cycle breaking and ready-move ordering are one small planning algorithm"
)]
pub(crate) fn plan(copies: &[Copy], temporary: Option<Place>) -> Result<MovePlan, PlanError> {
    validate(copies)?;
    let mut pending = Vec::with_capacity(copies.len());
    for (at, copy) in copies.iter().copied().enumerate() {
        if copy.source == CopySource::Place(copy.destination) {
            continue;
        }
        pending.push(Pending {
            source: copy.source,
            destination: copy.destination,
            origin: CopyId(u32::try_from(at).map_err(|_| PlanError::TooManyCopies)?),
        });
    }

    let mut moves = Vec::with_capacity(pending.len().saturating_add(1));
    while !pending.is_empty() {
        if let Some(ready) = pending.iter().position(|copy| {
            !pending
                .iter()
                .any(|other| other.source == CopySource::Place(copy.destination))
        }) {
            let copy = pending.remove(ready);
            moves.push(Move {
                source: copy.source,
                destination: copy.destination,
                origin: Some(copy.origin),
            });
            continue;
        }

        // Every remaining destination is still needed as a source. Save one
        // before overwriting it and redirect all readers to the saved value.
        let temporary = temporary.ok_or(PlanError::TemporaryRequired)?;
        if copies.iter().any(|copy| {
            copy.destination == temporary || copy.source == CopySource::Place(temporary)
        }) {
            return Err(PlanError::TemporaryInUse(temporary));
        }
        let saved = pending[0].destination;
        moves.push(Move {
            source: CopySource::Place(saved),
            destination: temporary,
            origin: None,
        });
        for copy in &mut pending {
            if copy.source == CopySource::Place(saved) {
                copy.source = CopySource::Place(temporary);
            }
        }
    }

    let mut cost = TransitionCost::default();
    for movement in &moves {
        cost = cost
            .add(movement.requirements())
            .ok_or(PlanError::CostOverflow)?;
    }
    Ok(MovePlan { moves, cost })
}

fn validate(copies: &[Copy]) -> Result<(), PlanError> {
    if copies.len() > usize::try_from(u32::MAX).expect("u32 fits usize") {
        return Err(PlanError::TooManyCopies);
    }
    for (at, copy) in copies.iter().enumerate() {
        if copies[..at]
            .iter()
            .any(|earlier| earlier.destination == copy.destination)
        {
            return Err(PlanError::DuplicateDestination(copy.destination));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const RAX: Place = Place::Register(Reg::Rax);
    const RCX: Place = Place::Register(Reg::Rcx);
    const RDX: Place = Place::Register(Reg::Rdx);
    const RSI: Place = Place::Register(Reg::Rsi);

    fn frame(at: u32) -> Place {
        Place::Frame(FrameSlot::at(at))
    }

    #[test]
    fn a_chain_is_ordered_before_its_sources_are_overwritten() {
        let plan = plan(&[Copy::between(RAX, RCX), Copy::between(RCX, RDX)], None).unwrap();
        assert_eq!(
            plan.moves(),
            &[
                Move {
                    source: CopySource::Place(RCX),
                    destination: RDX,
                    origin: Some(CopyId(1)),
                },
                Move {
                    source: CopySource::Place(RAX),
                    destination: RCX,
                    origin: Some(CopyId(0)),
                },
            ]
        );
    }

    #[test]
    fn a_cycle_saves_one_location_and_retains_copy_identity() {
        let temporary = frame(0);
        let plan = plan(
            &[Copy::between(RAX, RCX), Copy::between(RCX, RAX)],
            Some(temporary),
        )
        .unwrap();
        assert_eq!(
            plan.moves(),
            &[
                Move {
                    source: CopySource::Place(RCX),
                    destination: temporary,
                    origin: None,
                },
                Move {
                    source: CopySource::Place(RAX),
                    destination: RCX,
                    origin: Some(CopyId(0)),
                },
                Move {
                    source: CopySource::Place(temporary),
                    destination: RAX,
                    origin: Some(CopyId(1)),
                },
            ]
        );
    }

    #[test]
    fn aliases_need_no_move() {
        let plan = plan(&[Copy::between(RAX, RAX)], None).unwrap();
        assert!(plan.moves().is_empty());
        assert_eq!(plan.cost(), TransitionCost::default());
    }

    #[test]
    fn stack_moves_declare_expansion_scratch_and_transition_cost() {
        let plan = plan(&[Copy::between(frame(0), frame(1))], None).unwrap();
        let requirements = plan.moves()[0].requirements();
        assert_eq!(requirements.instructions, 2);
        assert_eq!(requirements.memory_reads, 1);
        assert_eq!(requirements.memory_writes, 1);
        assert_eq!(requirements.scratch_gprs, 1);
        assert_eq!(
            plan.cost(),
            TransitionCost {
                instructions: 2,
                memory_accesses: 2,
            }
        );
    }

    #[test]
    fn fixed_register_destinations_are_ordinary_copies() {
        let plan = plan(
            &[
                Copy::between(frame(0), Place::Register(Reg::Rdi)),
                Copy::between(frame(1), RSI),
            ],
            None,
        )
        .unwrap();
        assert_eq!(plan.moves().len(), 2);
        assert_eq!(plan.cost().instructions, 2);
        assert_eq!(plan.cost().memory_accesses, 2);
    }

    #[test]
    fn malformed_copy_sets_are_rejected_before_planning() {
        assert_eq!(
            plan(&[Copy::between(RAX, RDX), Copy::between(RCX, RDX)], None,),
            Err(PlanError::DuplicateDestination(RDX))
        );
        let cycle = [Copy::between(RAX, RCX), Copy::between(RCX, RAX)];
        assert_eq!(plan(&cycle, None), Err(PlanError::TemporaryRequired));
        assert_eq!(plan(&cycle, Some(RAX)), Err(PlanError::TemporaryInUse(RAX)));
    }
}
