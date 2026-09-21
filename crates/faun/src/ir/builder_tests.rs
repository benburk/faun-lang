use super::evaluate::{self, RejectHost};
use super::*;
use num_bigint::BigUint;

fn program() -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 7);
        b.ret(&[value]);
    });
    p
}

fn answer(p: &Program) -> u64 {
    validate(p).unwrap();
    let evaluation = evaluate::evaluate(
        p,
        p.entry(),
        &[],
        evaluate::Config::default(),
        &mut RejectHost,
    )
    .unwrap();
    u64::try_from(&evaluation.returned().unwrap()[0]).unwrap()
}

#[test]
fn default_program_requires_an_entry_before_validation() {
    let mut p = Program::default();
    assert!(p.functions().is_empty());
    assert_eq!(validate(&p).unwrap_err(), "missing entry function");
    let main = p.declare("main", &[], &[Class::Word]);
    assert_eq!(main, p.entry());
    assert!(matches!(
        p.function(main).definition,
        Definition::Declared(_)
    ));
    assert!(p.signature(p.function(main).params).is_empty());
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 7);
        b.ret(&[value]);
    });
    assert!(matches!(p.function(main).definition, Definition::Body(_)));
    assert_eq!(answer(&p), 7);
}

#[test]
fn fallible_builds_preserve_the_old_body_but_not_a_pool_checkpoint() {
    let mut p = program();
    let root = p.function(p.entry()).body().unwrap();
    let before = p.region(root);
    let regions = p.regions.len();
    let values = p.values_count();
    let error = p
        .try_define(p.entry(), |b, _| {
            let condition = b.constant(Class::Word, 1);
            b.if_(
                condition,
                &[Class::Natural],
                |b| {
                    let n = b.natural(&BigUint::from(3u8));
                    b.yield_(&[n]);
                },
                |b| {
                    let n = b.natural(&BigUint::from(5u8));
                    b.yield_(&[n]);
                },
            );
            Err(vec!["the callback's owned error"])
        })
        .unwrap_err();
    assert_eq!(error, ["the callback's owned error"]);
    assert_eq!(p.region(root), before, "failed body is not installed");
    assert_eq!(p.regions.len(), regions + 2, "nested appends are retained");
    assert!(p.values_count() > values);
    assert!(!p.data().is_empty());
    assert_eq!(answer(&p), 7);
}

#[test]
fn successful_retry_uses_the_same_parameters_and_installs_only_its_body() {
    let mut p = program();
    let helper = p.declare("helper", &[Class::Word], &[Class::Word]);
    let Definition::Declared(root) = p.function(helper).definition else {
        panic!("unbuilt declaration");
    };
    let params = p.region(root).params;
    let error = p.try_define(helper, |b, args| {
        b.convert(Class::Natural, args[0]);
        Err("unfinished")
    });
    assert_eq!(error, Err("unfinished"));
    assert_eq!(p.function(helper).definition, Definition::Declared(root));
    assert!(validate(&p).unwrap_err().contains("has not been defined"));
    p.try_define(helper, |b, args| {
        b.ret(args);
        Ok::<_, &str>(())
    })
    .unwrap();
    assert_eq!(p.region(root).params, params);
    assert_eq!(p.function(helper).definition, Definition::Body(root));
    assert_eq!(p.signature(p.function(helper).params), &[Class::Word]);
    p.try_define(p.entry(), |b, _| {
        let value = b.constant(Class::Word, 19);
        let result = b.call(helper, &[value]);
        b.ret(&result);
        Ok::<_, &str>(())
    })
    .unwrap();
    assert_eq!(answer(&p), 19);
}

#[test]
fn scalar_calls_emit_the_same_ir_as_general_single_result_calls() {
    for class in [
        Class::Word,
        Class::fixed(0),
        Class::fixed(7),
        Class::Address,
        Class::Natural,
    ] {
        let (mut scalar, main) = Program::new("main");
        let identity = scalar.declare("identity", &[class], &[class]);
        scalar.define(identity, |b, args| {
            b.ret(args);
        });
        let mut general = scalar.clone();
        scalar.define(main, |b, _| {
            let value = b.constant(class, 7);
            let value = b.call_one(identity, &[value]);
            assert_eq!(b.class(value), class);
            let word = b.convert(Class::Word, value);
            b.ret(&[word]);
        });
        general.define(main, |b, _| {
            let value = b.constant(class, 7);
            let result = b.call(identity, &[value]);
            let word = b.convert(Class::Word, result[0]);
            b.ret(&[word]);
        });
        assert_eq!(scalar.ops, general.ops);
        assert_eq!(scalar.results, general.results);
        assert_eq!(scalar.operands, general.operands);
        assert_eq!(scalar.classes, general.classes);
        assert_eq!(scalar.regions, general.regions);
        let expected = if class == (Class::fixed(0)) { 0 } else { 7 };
        assert_eq!(answer(&scalar), expected);
        assert_eq!(answer(&general), expected);
    }
}

#[test]
fn scalar_call_arity_is_checked_before_appending_operands_or_values() {
    for returns in [
        Returns::Never,
        Returns::Values(&[][..]),
        Returns::Values(&[Class::Word, Class::Word][..]),
    ] {
        let mut p = program();
        let caller = p.declare("caller", &[Class::Word], &[Class::Word]);
        p.define(caller, |b, args| {
            b.ret(args);
        });
        let outside = p.external("outside", &[Class::Word], returns);
        let before = p.clone();
        let error = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            p.define(caller, |b, args| {
                b.call_one(outside, args);
            });
        }))
        .unwrap_err();
        assert_eq!(
            error.downcast_ref::<&str>(),
            Some(&"call_one requires exactly one result")
        );
        assert_eq!(p.operands, before.operands);
        assert_eq!(p.classes, before.classes);
        assert_eq!(p.ops, before.ops);
        assert_eq!(p.results, before.results);
        assert_eq!(p.regions, before.regions);
        assert_eq!(p.functions, before.functions);
        assert_eq!(answer(&p), 7);
    }
}

struct Step(Vec<BigUint>);
impl evaluate::Host for Step {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        _: &mut evaluate::Memory<'_>,
    ) -> Result<evaluate::HostResult, evaluate::Error> {
        assert_eq!(name, "step");
        self.0.push(args[0].clone());
        Ok(evaluate::HostResult::Return(vec![&args[0] + 1u8]))
    }
}

#[test]
fn scalar_calls_keep_effect_order_even_when_a_result_is_unused() {
    let (mut p, main) = Program::new("main");
    let step = p.external("step", &[Class::Word], Returns::Values(&[Class::Word]));
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        let first = b.call_one(step, &[zero]);
        let second = b.call_one(step, &[first]);
        b.call_one(step, &[second]);
        b.ret(&[second]);
    });
    validate(&p).unwrap();
    for word_bits in [16, 32, 64] {
        let mut host = Step(Vec::new());
        let result = evaluate::evaluate(
            &p,
            main,
            &[],
            evaluate::Config {
                word_bits,
                ..evaluate::Config::default()
            },
            &mut host,
        )
        .unwrap();
        assert_eq!(result.returned().unwrap(), &[BigUint::from(2u8)]);
        assert_eq!(host.0, [0u8, 1, 2].map(BigUint::from));
    }
}

#[test]
#[should_panic(expected = "an external function cannot be defined")]
fn defining_an_external_is_a_builder_contract_error() {
    let mut p = program();
    let external = p.external("outside", &[], Returns::Values(&[]));
    let _: Result<(), ()> = p.try_define(external, |_, _| panic!("must not run callback"));
}
