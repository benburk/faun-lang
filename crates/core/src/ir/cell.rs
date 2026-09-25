//! Runtime support for immutable algebraic cells.
//!
//! A cell shares the natural runtime's allocation header and heap:
//! total bytes, reference count, then a representation-specific payload.
//! Cell payloads store the constructor tag, field count, and `(kind, value)`
//! pairs. Kinds let the generic release walk recursively without recovering
//! erased source types. Scalars need no action; naturals, cells and sequence
//! buffers release through their respective helpers.

use super::natural::{Helper, Library as NaturalLibrary};
use super::{Binary, Builder, Class, FunctionId, Offset, Program, Relation, ValueId, Width};

pub(super) const SCALAR: u64 = 0;
pub(super) const NATURAL: u64 = 1;
pub(super) const CELL: u64 = 2;
pub(super) const BUFFER: u64 = 3;

/// The kind a value of `class` is stored as, in a cell field or a buffer.
pub(super) const fn kind(class: Class) -> u64 {
    match class {
        Class::Natural => NATURAL,
        Class::Cell => CELL,
        Class::Buffer => BUFFER,
        _ => SCALAR,
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Library {
    pub retain: FunctionId,
    pub release: FunctionId,
    pub allocate: FunctionId,
}

const A: Class = Class::Address;
const W: Class = Class::Word;

/// Append the cell routines. `buffers` releases a sequence buffer held in a
/// field, and may be declared but not yet defined.
pub(super) fn append(
    program: &mut Program,
    naturals: &NaturalLibrary,
    buffers: Option<FunctionId>,
    word_bits: u16,
) -> Library {
    let release = program.declare("cell.release", &[A], &[]);
    let library = Library {
        retain: naturals.retain,
        release,
        allocate: naturals.require(Helper::Allocate),
    };
    define_release(program, library, (naturals, buffers), word_bits);
    library
}

fn number(b: &mut Builder<'_>, value: u64) -> ValueId {
    b.constant(W, value)
}

fn pair_address(b: &mut Builder<'_>, object: ValueId, index: ValueId, word_bytes: u64) -> ValueId {
    let two = number(b, 2);
    let pair = b.binary(Binary::Mul, index, two);
    let header = number(b, 4);
    let slot = b.binary(Binary::Add, pair, header);
    let bytes = number(b, word_bytes);
    let offset = b.binary(Binary::Mul, slot, bytes);
    let base = b.convert(W, object);
    let address = b.binary(Binary::Add, base, offset);
    b.convert(A, address)
}

#[expect(
    clippy::too_many_lines,
    reason = "the generated release routine keeps its control-flow and object layout together"
)]
fn define_release(
    program: &mut Program,
    library: Library,
    (naturals, buffer_release): (&NaturalLibrary, Option<FunctionId>),
    word_bits: u16,
) {
    let word_bytes = u64::from(word_bits / 8);
    program.define(library.release, |b, args| {
        let object = args[0];
        let refs = b.load(Width::Word, object, Offset::Words(1));
        let one = number(b, 1);
        let last = b.compare(Relation::Equal, refs, one);
        b.if_(
            last,
            &[],
            |b| {
                let arity = b.load(Width::Word, object, Offset::Words(3));
                let zero = number(b, 0);
                b.loop_(&[zero], &[], |b, state| {
                    let index = state[0];
                    let done = b.compare(Relation::Equal, index, arity);
                    b.if_(done, &[], |b| b.break_(&[]), |b| b.yield_(&[]));
                    let pair = pair_address(b, object, index, word_bytes);
                    let kind = b.load(Width::Word, pair, Offset::Words(0));
                    let held = b.load(Width::Word, pair, Offset::Words(1));
                    let value = b.convert(A, held);
                    let natural = number(b, NATURAL);
                    let is_natural = b.compare(Relation::Equal, kind, natural);
                    b.if_(
                        is_natural,
                        &[],
                        |b| {
                            naturals.release_value(b, value);
                            b.yield_(&[]);
                        },
                        |b| {
                            let cell = number(b, CELL);
                            let is_cell = b.compare(Relation::Equal, kind, cell);
                            b.if_(
                                is_cell,
                                &[],
                                |b| {
                                    b.call(library.release, &[value]);
                                    b.yield_(&[]);
                                },
                                |b| {
                                    // Only a program holding sequences
                                    // stores a buffer in a cell.
                                    if let Some(buffer_release) = buffer_release {
                                        let buffer = number(b, BUFFER);
                                        let is_buffer = b.compare(Relation::Equal, kind, buffer);
                                        b.if_(
                                            is_buffer,
                                            &[],
                                            |b| {
                                                b.call(buffer_release, &[value]);
                                                b.yield_(&[]);
                                            },
                                            |b| b.yield_(&[]),
                                        );
                                    }
                                    b.yield_(&[]);
                                },
                            );
                            b.yield_(&[]);
                        },
                    );
                    let next = b.binary(Binary::Add, index, one);
                    b.continue_(&[next]);
                });
                b.yield_(&[]);
            },
            |b| b.yield_(&[]),
        );
        b.call(naturals.release, &[object]);
        b.ret(&[]);
    });
}
