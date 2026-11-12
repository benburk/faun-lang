use super::{TARGET, shared};
use crate::ir::{Binary, Class, FunctionId, Program, ShapeId};
use crate::targets::Target;

const W: Class = Class::Word;
const C: Class = Class::Cell;

#[test]
fn nested_loops_reuse_a_tiny_heap_and_preserve_full_naturals() {
    for early_return in [false, true] {
        crate::lifetime_fixture::check(&crate::X86_64Linux, None, early_return);
    }
}

/// A spine of one-cell nodes, ending in a scalar leaf. Both layouts live
/// in the same chunks. The depth and leaf value vary independently.
fn spine(p: &mut Program) -> (FunctionId, FunctionId, FunctionId) {
    let leaf = p.shape(&[W]);
    let node = p.shape(&[C]);
    let build = p.declare("spine", &[W, W], &[C]);
    let child = p.declare("child", &[C], &[C]);
    p.define(build, |b, args| {
        let tree = b.if_(
            args[0],
            &[C],
            |b| {
                let one = b.constant(W, 1);
                let depth = b.binary(Binary::Sub, args[0], one);
                let next = b.call_one(build, &[depth, args[1]]);
                let root = b.cell(1, node, &[next]);
                b.yield_(&[root]);
            },
            |b| {
                let root = b.cell(0, leaf, &[args[1]]);
                b.yield_(&[root]);
            },
        )[0];
        b.ret(&[tree]);
    });
    let read = sum(p, leaf, node);
    p.define(child, |b, args| {
        let next = b.cell_field((C, node), args[0], 0);
        b.ret(&[next]);
    });
    (build, read, child)
}

fn sum(p: &mut Program, leaf: ShapeId, node: ShapeId) -> FunctionId {
    let read = p.declare("sum", &[C], &[W]);
    p.define(read, |b, args| {
        let tag = b.cell_tag(args[0]);
        b.if_(
            tag,
            &[],
            |b| {
                let next = b.cell_field((C, node), args[0], 0);
                let sum = b.call_one(read, &[next]);
                let one = b.constant(W, 1);
                let sum = b.binary(Binary::Add, sum, one);
                b.ret(&[sum]);
            },
            |b| {
                let value = b.cell_field((W, leaf), args[0], 0);
                b.ret(&[value]);
            },
        );
    });
    read
}

#[test]
fn independent_regions_survive_loop_allocations_and_an_early_return() {
    let (mut p, main) = Program::new("main");
    let (build, read, _) = spine(&mut p);
    p.define(main, |b, _| {
        let depth = b.constant(W, 512);
        let mark = b.constant(W, 7);
        let keep = b.call_one(build, &[depth, mark]);
        let other = b.constant(W, 29);
        let short = b.constant(W, 190);
        let rounds = b.constant(W, 5);
        let zero = b.constant(W, 0);
        b.loop_(&[rounds, zero], &[], |b, state| {
            let root = b.call_one(build, &[short, other]);
            let sum = b.call_one(read, &[root]);
            let total = b.binary(Binary::Add, state[1], sum);
            b.if_(
                state[0],
                &[],
                |b| b.yield_(&[]),
                |b| {
                    let old = b.call_one(read, &[keep]);
                    let answer = b.binary(Binary::Add, total, old);
                    b.ret(&[answer]);
                },
            );
            let one = b.constant(W, 1);
            let left = b.binary(Binary::Sub, state[0], one);
            b.continue_(&[left, total]);
        });
    });
    let prepared = TARGET.prepare(&p).unwrap();
    assert!(
        prepared
            .functions()
            .iter()
            .any(|f| prepared.name(f.name) == "region.bump")
    );
    assert_eq!(shared::status(&prepared), (512 + 7 + 6 * (190 + 29)) % 256);
}

#[test]
fn returning_a_child_preserves_its_claim_across_another_construction() {
    let (mut p, main) = Program::new("main");
    let (build, read, child) = spine(&mut p);
    p.define(main, |b, _| {
        let depth = b.constant(W, 210);
        let old = b.constant(W, 3);
        let root = b.call_one(build, &[depth, old]);
        let child = b.call_one(child, &[root]);
        let fresh = b.constant(W, 31);
        let root = b.call_one(build, &[depth, fresh]);
        let new_sum = b.call_one(read, &[root]);
        let old_sum = b.call_one(read, &[child]);
        let result = b.binary(Binary::Add, new_sum, old_sum);
        b.ret(&[result]);
    });
    let prepared = TARGET.prepare(&p).unwrap();
    assert!(
        !prepared
            .functions()
            .iter()
            .any(|f| prepared.name(f.name) == "region.bump")
    );
    assert_eq!(shared::status(&prepared), (209 + 3 + 210 + 31) % 256);
}
