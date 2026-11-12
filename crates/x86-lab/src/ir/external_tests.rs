use super::evaluate::{self, Error, Host, HostResult, Memory, Outcome};
use super::*;
use crate::targets::Target;
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
        &["exit!", "write!", "count!"]
    }
    /// The built-in routines it provides, and one answering a whole word,
    /// which no built-in routine does.
    fn routines(&self) -> crate::platform::Routines {
        let mut routines = crate::platform::Routines::builtin().only(self.provides());
        routines.push(crate::platform::Routine {
            name: "count!".to_owned(),
            offered: true,
            authority: false,
            takes: Vec::new(),
            returns: crate::platform::Returns::Value(Class::Word),
            built: None,
            consumes: false,
        });
        routines.with_word(self.0)
    }
    fn emit(&self, _: &Program) -> Vec<u8> {
        Vec::new()
    }
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
                .compile_machine_ir(&p)
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
            let external = p.external("count!", &[], Returns::Values(&[class]));
            call_external(&mut p, external);
            Provider(bits).compile_machine_ir(&p).unwrap();
        }
        let mut p = program();
        let external = p.external("count!", &[], Returns::Values(&[Class::fixed(bits - 1)]));
        call_external(&mut p, external);
        assert!(
            Provider(bits)
                .compile_machine_ir(&p)
                .unwrap_err()
                .contains("provider contract")
        );
    }
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
            authority: false,
            takes: vec![],
            returns,
            built: None,
            consumes: false,
        });
        let error = lower(&source, &routines).unwrap_err();
        assert!(error.contains("about returning"), "{error}");
    }
}
