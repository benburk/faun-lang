use super::evaluate::{self, Error, Host, HostResult, Memory, Outcome};
use super::*;
use crate::targets::{Artifact, Target};
use num_bigint::BigUint;

fn program() -> Program {
    let (mut p, main) = Program::new("main");
    p.define(main, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    p
}

struct Reply {
    calls: Vec<String>,
    answer: fn(&[BigUint]) -> HostResult,
}

impl Host for Reply {
    fn call(
        &mut self,
        name: &str,
        args: &[BigUint],
        _: &mut Memory<'_>,
    ) -> Result<HostResult, Error> {
        self.calls.push(name.to_owned());
        Ok((self.answer)(args))
    }
}

fn reply(answer: fn(&[BigUint]) -> HostResult) -> Reply {
    Reply {
        calls: Vec::new(),
        answer,
    }
}

fn run(
    p: &Program,
    id: FunctionId,
    args: &[BigUint],
    host: &mut Reply,
) -> Result<evaluate::Evaluation, Error> {
    evaluate::evaluate(p, id, args, evaluate::Config::default(), host)
}

fn call_external(p: &mut Program, function: FunctionId) {
    let held = p.function(function);
    let classes = p.signature(held.params).to_vec();
    let returns = held.returns;
    p.define(p.entry(), |b, _| {
        let status = b.constant(Class::Word, 0);
        let args: Vec<_> = classes.iter().map(|&class| b.constant(class, 0)).collect();
        b.call(function, &args);
        if returns == Returns::Never {
        } else {
            b.ret(&[status]);
        }
    });
}

#[derive(Debug)]
struct Provider(u16);

impl Target for Provider {
    fn name(&self) -> &'static str {
        "test provider"
    }
    fn word(&self) -> u16 {
        self.0
    }
    fn provides(&self) -> &'static [&'static str] {
        &["exit!", "argc!", "write"]
    }
    fn emit(&self, _: &Program) -> Vec<Artifact> {
        Vec::new()
    }
}

#[test]
fn external_declarations_need_neither_a_catalog_nor_parameter_values_or_regions() {
    let mut p = program();
    let values = p.values_count();
    let regions = p.regions.len();
    let f = p.external(
        "library_symbol",
        &[Class::Word],
        Returns::Values(&[Class::Word]),
    );
    let held = p.function(f);
    assert_eq!(p.signature(held.params), [Class::Word]);
    assert_eq!(p.signature(held.returns.classes()), [Class::Word]);
    assert_eq!(p.name(held.name), "library_symbol");
    assert_eq!(held.definition, Definition::External);
    assert_eq!(held.external(), Some(held.name));
    assert!(held.body().is_none());
    assert_eq!(p.values_count(), values);
    assert_eq!(p.regions.len(), regions);
    validate(&p).unwrap();
    // Unused declarations do not require symbol availability. A call does.
    Provider(64).compile(&p).unwrap();
    call_external(&mut p, f);
    assert!(
        Provider(64)
            .compile(&p)
            .unwrap_err()
            .contains("library_symbol")
    );
}

#[test]
fn one_call_operation_handles_local_and_external_multivalue_functions() {
    let mut p = program();
    let pair = p.external(
        "pair_provider",
        &[Class::Word, Class::Word],
        Returns::Values(&[Class::Word, Class::Word]),
    );
    let wrapper = p.declare("wrapper", &[Class::Word, Class::Word], &[Class::Word]);
    p.define(wrapper, |b, args| {
        let values = b.call(pair, args);
        let result = b.binary(Binary::Add, values[0], values[1]);
        b.ret(&[result]);
    });
    p.define(p.entry(), |b, _| {
        let a = b.constant(Class::Word, 3);
        let z = b.constant(Class::Word, 8);
        let answer = b.call(wrapper, &[a, z]);
        b.ret(&answer);
    });
    validate(&p).unwrap();
    let mut host = reply(|args| HostResult::Return(args.to_vec()));
    assert_eq!(
        run(&p, p.entry(), &[], &mut host)
            .unwrap()
            .returned()
            .unwrap(),
        [BigUint::from(11u8)]
    );
    assert_eq!(host.calls, ["pair_provider"]);
    let args = [BigUint::from(3u8), BigUint::from(8u8)];
    assert_eq!(
        run(&p, pair, &args, &mut host).unwrap().returned().unwrap(),
        args
    );
}

#[test]
fn returning_unit_and_never_are_not_interchangeable() {
    for returns in [Returns::Never, Returns::Values([].as_slice())] {
        let mut p = program();
        let effect = p.external("host", &[], returns);
        p.define(p.entry(), |b, _| {
            b.call(effect, &[]);
            let zero = b.constant(Class::Word, 0);
            b.ret(&[zero]);
        });
        if returns == Returns::Never {
            assert!(validate(&p).unwrap_err().contains("does not come back"));
        } else {
            validate(&p).unwrap();
        }
        let mut host = reply(|_| HostResult::Return(vec![]));
        let result = run(&p, effect, &[], &mut host);
        if returns == Returns::Never {
            assert_eq!(
                result.unwrap_err(),
                Error::InvalidProgram("non-returning host returned")
            );
        } else {
            assert_eq!(result.unwrap().outcome, Outcome::Returned(vec![]));
        }
    }
}

#[test]
fn host_halts_escape_internal_callers_and_direct_external_evaluation() {
    let mut p = program();
    let stop = p.external("host_halt", &[], Returns::Never);
    let wrapper = p.declare("wrapper", &[], &[]);
    p.define(wrapper, |b, _| {
        b.call(stop, &[]);
    });
    p.define(p.entry(), |b, _| {
        b.call(wrapper, &[]);
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    validate(&p).unwrap();
    let mut host = reply(|_| HostResult::Halt(vec![BigUint::from(23u8)]));
    for function in [p.entry(), stop] {
        assert_eq!(
            run(&p, function, &[], &mut host).unwrap().outcome,
            Outcome::Halted(vec![BigUint::from(23u8)])
        );
    }
}

#[test]
fn host_values_and_direct_arguments_are_checked_against_declarations() {
    let mut p = program();
    let byte = Class::fixed(8);
    let external = p.external("echo", &[byte], Returns::Values(&[byte]));
    let mut echo = reply(|args| HostResult::Return(args.to_vec()));
    assert_eq!(
        run(&p, external, &[], &mut echo).unwrap_err(),
        Error::InvalidProgram("signature arity")
    );
    assert_eq!(
        run(&p, external, &[BigUint::from(256u16)], &mut echo).unwrap_err(),
        Error::DoesNotFit(byte)
    );
    assert!(echo.calls.is_empty(), "bad arguments never reach the host");
    let mut wide = reply(|_| HostResult::Return(vec![BigUint::from(256u16)]));
    assert_eq!(
        run(&p, external, &[BigUint::from(1u8)], &mut wide).unwrap_err(),
        Error::DoesNotFit(byte)
    );
    let mut empty = reply(|_| HostResult::Return(vec![]));
    assert_eq!(
        run(&p, external, &[BigUint::from(1u8)], &mut empty).unwrap_err(),
        Error::InvalidProgram("signature arity")
    );
}

#[test]
fn direct_external_evaluation_consumes_fuel() {
    let mut p = program();
    let unit = p.external("unit", &[], Returns::Values(&[]));
    let mut host = reply(|_| HostResult::Return(vec![]));
    let result = evaluate::evaluate(
        &p,
        unit,
        &[],
        evaluate::Config {
            fuel: 0,
            ..evaluate::Config::default()
        },
        &mut host,
    );
    assert_eq!(result.unwrap_err(), Error::FuelExhausted);
    assert!(host.calls.is_empty());
}

#[test]
fn target_contracts_check_parameters_results_and_returning_behavior() {
    for (params, returns) in [
        (&[][..], Returns::Never),
        (&[Class::Address][..], Returns::Never),
        (&[Class::Word][..], Returns::Values(&[][..])),
        (&[Class::Word][..], Returns::Values(&[Class::Word][..])),
    ] {
        let mut p = program();
        let external = p.external("exit!", params, returns);
        call_external(&mut p, external);
        validate(&p).unwrap();
        assert!(
            Provider(64)
                .compile(&p)
                .unwrap_err()
                .contains("provider contract")
        );
    }
}

#[test]
fn word_results_and_exact_target_widths_share_an_abi_but_narrower_claims_do_not() {
    for bits in [16, 32, 64] {
        for class in [Class::Word, Class::fixed(bits)] {
            let mut p = program();
            let external = p.external("argc!", &[], Returns::Values(&[class]));
            call_external(&mut p, external);
            Provider(bits).compile(&p).unwrap();
        }
        let mut p = program();
        let external = p.external("argc!", &[], Returns::Values(&[Class::fixed(bits - 1)]));
        call_external(&mut p, external);
        assert!(
            Provider(bits)
                .compile(&p)
                .unwrap_err()
                .contains("provider contract")
        );
    }
}

#[test]
fn a_body_named_like_an_external_function_is_still_a_body() {
    let mut p = program();
    let internal = p.declare("argc!", &[], &[Class::Word]);
    p.define(internal, |b, _| {
        let zero = b.constant(Class::Word, 0);
        b.ret(&[zero]);
    });
    p.define(p.entry(), |b, _| {
        let result = b.call(internal, &[]);
        b.ret(&result);
    });
    assert!(!p.reaches("argc!"));
    Provider(64).compile(&p).unwrap();
    let mut host = reply(|_| HostResult::Return(vec![BigUint::from(7u8)]));
    assert_eq!(
        run(&p, p.entry(), &[], &mut host)
            .unwrap()
            .returned()
            .unwrap(),
        [BigUint::from(0u8)]
    );
    assert!(host.calls.is_empty());
    let external = p.external("argc!", &[], Returns::Values(&[Class::Word]));
    p.define(p.entry(), |b, _| {
        let result = b.call(external, &[]);
        b.ret(&result);
    });
    assert!(p.reaches("argc!"));
    Provider(64).compile(&p).unwrap();
    assert_eq!(
        run(&p, p.entry(), &[], &mut host)
            .unwrap()
            .returned()
            .unwrap(),
        [BigUint::from(7u8)]
    );
    assert_eq!(host.calls, ["argc!"]);
}

#[test]
fn source_externals_check_unit_against_nonreturning_provider_contracts() {
    use crate::{barb, platform};
    for returns in [platform::Returns::Unit, platform::Returns::Never] {
        let mut source = barb::Program::default();
        let unit = source.declare_type("Unit");
        source.define_type(unit, &[("Unit", &[])]);
        let never = source.declare_type("Never");
        source.define_type(never, &[]);
        let result = if returns == platform::Returns::Unit {
            never
        } else {
            unit
        };
        let foreign = source.declare("foreign", &[], result);
        let main = source.declare("main", &[], result);
        source.define(main, |b, _| b.call(foreign, &[]));
        source.set_entry(main);
        let mut routines = platform::Routines::default();
        routines.push(platform::Routine {
            name: "foreign".into(),
            offered: false,
            takes: vec![],
            returns,
        });
        let error = lower(&source, &barb::analyze(&source), &routines).unwrap_err();
        assert!(error.contains("about returning"), "{error}");
    }
}

#[test]
fn an_external_declaration_cannot_be_the_entry_body() {
    let mut p = program();
    p.functions[FunctionId(0)].definition = Definition::External;
    assert!(validate(&p).unwrap_err().contains("entry"));
}
