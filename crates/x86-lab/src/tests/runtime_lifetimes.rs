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

/// A recursive weighted list with one nullary and one nonempty variant.
fn chain(p: &mut Program, empty: u32, link: u32) -> (FunctionId, FunctionId) {
    let nil = p.shape(&[]);
    let pair = p.shape(&[W, C]);
    let build = p.declare("chain", &[W], &[C]);
    p.define(build, |b, args| {
        let root = b.if_(
            args[0],
            &[C],
            |b| {
                let one = b.constant(W, 1);
                let shorter = b.binary(Binary::Sub, args[0], one);
                let child = b.call_one(build, &[shorter]);
                let node = b.cell(link, pair, &[args[0], child]);
                b.yield_(&[node]);
            },
            |b| {
                let leaf = b.cell(empty, nil, &[]);
                b.yield_(&[leaf]);
            },
        )[0];
        b.ret(&[root]);
    });
    (build, weight(p, empty, pair))
}

fn weight(p: &mut Program, empty: u32, pair: ShapeId) -> FunctionId {
    let read = p.declare("weight", &[C], &[W]);
    p.define(read, |b, args| {
        let tag = b.cell_tag(args[0]);
        let nil = b.constant(W, u64::from(empty));
        let end = b.compare(crate::ir::Relation::Equal, tag, nil);
        b.if_(
            end,
            &[],
            |b| b.ret(&[tag]),
            |b| {
                let weight = b.cell_field((W, pair), args[0], 0);
                let child = b.cell_field((C, pair), args[0], 1);
                let rest = b.call_one(read, &[child]);
                let weight = b.binary(Binary::Add, tag, weight);
                let total = b.binary(Binary::Add, weight, rest);
                b.ret(&[total]);
            },
        );
    });
    read
}

#[test]
fn nullable_regions_preserve_tags_and_project_fields_across_chunks() {
    for (empty, link) in [(0, 1), (1, 0), (19, 7)] {
        let (mut p, main) = Program::new("main");
        let (build, read) = chain(&mut p, empty, link);
        p.define(main, |b, _| {
            let length = b.constant(W, 600);
            let deep = b.call_one(build, &[length]);
            let zero = b.constant(W, 0);
            let leaf = b.call_one(build, &[zero]);
            let bare = b.call_one(read, &[leaf]);
            let sum = b.call_one(read, &[deep]);
            let total = b.binary(Binary::Add, sum, bare);
            let expected = b.constant(
                W,
                600 * 601 / 2 + 600 * u64::from(link) + 2 * u64::from(empty),
            );
            let pass = b.compare(crate::ir::Relation::Equal, total, expected);
            b.ret(&[pass]);
        });
        assert!(p.render().contains("# chain encodes empty as null"));
        assert_eq!(shared::status(&TARGET.prepare(&p).unwrap()), 1);
    }
}

#[test]
fn one_reader_of_an_ordinary_cell_keeps_the_shared_tagged_layout() {
    let (mut p, main) = Program::new("main");
    let (build, read) = chain(&mut p, 2, 8);
    let nil = p.shape(&[]);
    p.define(main, |b, _| {
        let length = b.constant(W, 4);
        let chain = b.call_one(build, &[length]);
        let ordinary = b.cell(2, nil, &[]);
        let a = b.call_one(read, &[ordinary]);
        let total = b.call_one(read, &[chain]);
        let answer = b.binary(Binary::Add, a, total);
        b.ret(&[answer]);
    });
    let dump = p.render();
    assert!(dump.contains("# chain builds in a caller-owned region"));
    assert!(!dump.contains("encodes empty as null"));
    assert_eq!(shared::status(&TARGET.prepare(&p).unwrap()), 46);
}

#[test]
fn payload_only_and_tagged_region_trees_can_coexist() {
    let (mut p, main) = Program::new("main");
    let (compact, weight) = chain(&mut p, 3, 9);
    let (tagged, sum, _) = spine(&mut p);
    p.define(main, |b, _| {
        let depth = b.constant(W, 300);
        let compact = b.call_one(compact, &[depth]);
        let mark = b.constant(W, 21);
        let tagged = b.call_one(tagged, &[depth, mark]);
        let a = b.call_one(weight, &[compact]);
        let z = b.call_one(sum, &[tagged]);
        let result = b.binary(Binary::Add, a, z);
        let expected = b.constant(W, 300 * 301 / 2 + 300 * 9 + 3 + 300 + 21);
        let pass = b.compare(crate::ir::Relation::Equal, result, expected);
        b.ret(&[pass]);
    });
    assert_eq!(p.render().matches("encodes empty as null").count(), 1);
    assert_eq!(shared::status(&TARGET.prepare(&p).unwrap()), 1);
}
