//! Natural-number arithmetic built with the Barb builder, for tests that need
//! a small standard library without a frontend.
//!
//! Every definition is the equation a frontend writes for it, clause by
//! clause, so recognition, folding and bounds see the same shapes they see
//! from source. Tests add their own declarations and entry to `program`.

use super::{ConstId, CtorId, FnId, Program, TypeId};

pub(crate) struct Library {
    pub program: Program,
    pub nat: TypeId,
    pub bool_: TypeId,
    pub zero: CtorId,
    pub succ: CtorId,
    pub false_: CtorId,
    pub true_: CtorId,
    pub add: FnId,
    pub sub: FnId,
    pub mul: FnId,
    pub div: FnId,
    pub modulo: FnId,
    pub equals: FnId,
    pub less_than: FnId,
}

impl Library {
    /// `Nat`, `Bool`, and the arithmetic over them.
    #[expect(
        clippy::too_many_lines,
        reason = "one definition per operation, in the order a source file declares them"
    )]
    pub(crate) fn new() -> Self {
        let mut p = Program::default();
        let nat = p.declare_type("Nat");
        p.define_type(nat, &[("Zero", &[]), ("Succ", &[nat])]);
        let bool_ = p.declare_type("Bool");
        p.define_type(bool_, &[("False", &[]), ("True", &[])]);
        let (zero, succ) = (p.ctor_at(nat, 0), p.ctor_at(nat, 1));
        let (false_, true_) = (p.ctor_at(bool_, 0), p.ctor_at(bool_, 1));
        let two = [nat, nat];

        // add(a, Zero) -> a
        // add(a, Succ(b)) -> Succ(add(a, b))
        let add = p.declare("add", &two, nat);
        p.define(add, |b, args| {
            b.match_(args[1], nat, |b, ctor, fields| {
                if ctor == zero {
                    args[0]
                } else {
                    let rest = b.call(add, &[args[0], fields[0]]);
                    b.con(succ, &[rest])
                }
            })
        });

        // sub(Zero, b) -> Zero
        // sub(Succ(a) Zero) -> Succ(a)
        // sub(Succ(a), Succ(b)) -> sub(a, b)
        let sub = p.declare("sub", &two, nat);
        p.define(sub, |b, args| {
            b.match_(args[0], nat, |b, ctor, left| {
                if ctor == zero {
                    return b.con(zero, &[]);
                }
                b.match_(args[1], nat, |b, ctor, right| {
                    if ctor == zero {
                        b.con(succ, &[left[0]])
                    } else {
                        b.call(sub, &[left[0], right[0]])
                    }
                })
            })
        });

        // mul(a, Zero) -> Zero
        // mul(a, Succ(b)) -> add(a, mul(a, b))
        let mul = p.declare("mul", &two, nat);
        p.define(mul, |b, args| {
            b.match_(args[1], nat, |b, ctor, fields| {
                if ctor == zero {
                    b.con(zero, &[])
                } else {
                    let rest = b.call(mul, &[args[0], fields[0]]);
                    b.call(add, &[args[0], rest])
                }
            })
        });

        let equals = p.declare("equals", &two, bool_);
        compare(&mut p, equals, (nat, zero), [true_, false_, false_]);
        let less_than = p.declare("less_than", &two, bool_);
        compare(&mut p, less_than, (nat, zero), [false_, true_, false_]);

        // mod(a, Zero) -> a
        // mod(Zero Succ(b)) -> Zero
        // mod(Succ(a), Succ(b)) -> r = mod(a, Succ(b)) mod_step(equals(r, b), r)
        // mod_step(True, r) -> Zero
        // mod_step(False, r) -> Succ(r)
        let mod_step = p.declare("mod_step", &[bool_, nat], nat);
        p.define(mod_step, |b, args| {
            b.match_(args[0], bool_, |b, ctor, _| {
                if ctor == true_ {
                    b.con(zero, &[])
                } else {
                    b.con(succ, &[args[1]])
                }
            })
        });
        let modulo = p.declare("mod", &two, nat);
        p.define(modulo, |b, args| {
            b.match_(args[1], nat, |b, ctor, divisor| {
                if ctor == zero {
                    return args[0];
                }
                b.match_(args[0], nat, |b, ctor, dividend| {
                    if ctor == zero {
                        return b.con(zero, &[]);
                    }
                    let whole = b.con(succ, &[divisor[0]]);
                    let r = b.call(modulo, &[dividend[0], whole]);
                    let last = b.call(equals, &[r, divisor[0]]);
                    b.call(mod_step, &[last, r])
                })
            })
        });

        // div(a, Zero) -> Zero
        // div(Zero Succ(b)) -> Zero
        // div(Succ(a) Succ(b)) -> q = div(a Succ(b))
        //   div_step(equals(mod(a Succ(b)) b) q)
        // div_step(True, q) -> Succ(q)
        // div_step(False, q) -> q
        let div_step = p.declare("div_step", &[bool_, nat], nat);
        p.define(div_step, |b, args| {
            b.match_(args[0], bool_, |b, ctor, _| {
                if ctor == true_ {
                    b.con(succ, &[args[1]])
                } else {
                    args[1]
                }
            })
        });
        let div = p.declare("div", &two, nat);
        p.define(div, |b, args| {
            b.match_(args[1], nat, |b, ctor, divisor| {
                if ctor == zero {
                    return b.con(zero, &[]);
                }
                b.match_(args[0], nat, |b, ctor, dividend| {
                    if ctor == zero {
                        return b.con(zero, &[]);
                    }
                    let whole = b.con(succ, &[divisor[0]]);
                    let q = b.call(div, &[dividend[0], whole]);
                    let whole = b.con(succ, &[divisor[0]]);
                    let r = b.call(modulo, &[dividend[0], whole]);
                    let last = b.call(equals, &[r, divisor[0]]);
                    b.call(div_step, &[last, q])
                })
            })
        });

        Self {
            program: p,
            nat,
            bool_,
            zero,
            succ,
            false_,
            true_,
            add,
            sub,
            mul,
            div,
            modulo,
            equals,
            less_than,
        }
    }

    /// Hold `n` in the program's pool.
    pub(crate) fn number(&mut self, n: u64) -> ConstId {
        self.program
            .intern_number(self.nat, n)
            .expect("the library's natural shape")
    }
}

/// A comparison written as its four clauses: both nought, nought against
/// more, more against nought, and a step down on both sides. `answers` are
/// the tags for the first three.
fn compare(p: &mut Program, id: FnId, (nat, zero): (TypeId, CtorId), answers: [CtorId; 3]) {
    let [both, below, above] = answers;
    p.define(id, |b, args| {
        b.match_(args[0], nat, |b, ctor, left| {
            let left_zero = ctor == zero;
            b.match_(args[1], nat, |b, ctor, right| {
                match (left_zero, ctor == zero) {
                    (true, true) => b.con(both, &[]),
                    (true, false) => b.con(below, &[]),
                    (false, true) => b.con(above, &[]),
                    (false, false) => b.call(id, &[left[0], right[0]]),
                }
            })
        })
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::barb::Operation;

    #[test]
    fn every_operation_is_recognised_from_its_equations() {
        let mut library = Library::new();
        library.program.analyze();
        let facts = library.program.facts().expect("just analyzed");
        for (id, expected) in [
            (library.add, Operation::Add),
            (library.sub, Operation::Monus),
            (library.mul, Operation::Mul),
            (library.div, Operation::Div),
            (library.modulo, Operation::Mod),
        ] {
            assert_eq!(facts.operation(id), Some(expected));
        }
        assert!(matches!(
            facts.operation(library.equals),
            Some(Operation::Equals { .. })
        ));
        assert!(matches!(
            facts.operation(library.less_than),
            Some(Operation::LessThan { .. })
        ));
    }

    /// A program built on the library folds to what its arithmetic says.
    #[test]
    fn a_program_on_the_library_answers_its_arithmetic() {
        let mut library = Library::new();
        let (two, three) = (library.number(2), library.number(3));
        let (nat, bool_) = (library.nat, library.bool_);
        let (zero, succ) = (library.zero, library.succ);
        let (add, less_than) = (library.add, library.less_than);
        let (yes, no) = (library.true_, library.false_);
        let pick = library.program.declare("pick", &[bool_], nat);
        library.program.define(pick, |b, args| {
            b.match_(args[0], bool_, |b, ctor, _| {
                if ctor == yes {
                    b.known(three)
                } else {
                    assert_eq!(ctor, no);
                    b.con(zero, &[])
                }
            })
        });
        let main = library.program.declare("main", &[], nat);
        library.program.define(main, |b, _| {
            let (two, three) = (b.known(two), b.known(three));
            let below = b.call(less_than, &[two, three]);
            let chosen = b.call(pick, &[below]);
            let sum = b.call(add, &[two, chosen]);
            b.con(succ, &[sum])
        });
        library.program.set_entry(main);
        crate::barb::optimize(&mut library.program);
        // What the entry does not reach is gone, and the entry renumbered.
        let main = library.program.entry().expect("an entry");
        let body = library.program.function(main).body().unwrap();
        let crate::barb::Expr::Static(value) = library.program.expr(body.tail) else {
            panic!("folded\n{}", library.program.render());
        };
        let crate::barb::ConstantView::Natural(value) = library.program.constant(value).view()
        else {
            panic!("a natural");
        };
        assert_eq!(value.try_u64(), Ok(6));
    }
}
