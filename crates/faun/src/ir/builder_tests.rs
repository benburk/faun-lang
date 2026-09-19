use super::evaluate::{self, RejectHost};
use super::*;
use num_bigint::BigUint;

fn program() -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 7);
        b.ret(&[value])
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
    p.define(main, |b, _| {
        let value = b.constant(Class::Word, 7);
        b.ret(&[value])
    });
    assert_eq!(answer(&p), 7);
}

#[test]
fn fallible_builds_preserve_the_old_body_but_not_a_pool_checkpoint() {
    let mut p = program();
    let root = p.functions()[0].body().unwrap();
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
                    b.yield_(&[n])
                },
                |b| {
                    let n = b.natural(&BigUint::from(5u8));
                    b.yield_(&[n])
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
    let root = p.functions()[helper.index()].body().unwrap();
    let params = p.region(root).params;
    let error = p.try_define(helper, |b, args| {
        b.convert(Class::Natural, args[0]);
        Err("unfinished")
    });
    assert_eq!(error, Err("unfinished"));
    p.try_define(helper, |b, args| Ok::<_, &str>(b.ret(args)))
        .unwrap();
    assert_eq!(p.region(root).params, params);
    p.try_define(p.entry(), |b, _| {
        let value = b.constant(Class::Word, 19);
        let result = b.call(helper, &[value]);
        Ok::<_, &str>(b.ret(&result))
    })
    .unwrap();
    assert_eq!(answer(&p), 19);
}

#[test]
fn infallible_and_fallible_builders_install_the_same_region() {
    let mut infallible = program();
    let mut fallible = infallible.clone();
    infallible.define(infallible.entry(), |b, _| {
        let value = b.constant(Class::Word, 21);
        b.ret(&[value])
    });
    fallible
        .try_define(fallible.entry(), |b, _| {
            let value = b.constant(Class::Word, 21);
            Ok::<_, &str>(b.ret(&[value]))
        })
        .unwrap();
    assert_eq!(fallible.ops, infallible.ops);
    assert_eq!(fallible.results, infallible.results);
    assert_eq!(fallible.regions, infallible.regions);
    assert_eq!(answer(&fallible), 21);
}

#[test]
#[should_panic(expected = "a defined function")]
fn defining_an_external_is_a_builder_contract_error() {
    let mut p = program();
    let external = p.external("outside", &[], Returns::Values(&[]));
    let _: Result<(), ()> = p.try_define(external, |_, _| panic!("must not run callback"));
}
