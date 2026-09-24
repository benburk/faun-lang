use super::evaluate::{self, Config as EvaluationConfig, Error, RejectHost};
use super::natural::{self, Config, Needs};
use super::{Class, Layout, Program, legalize};
use crate::targets::Target;
use num_bigint::BigUint;

#[derive(Debug)]
struct TargetAt(Layout);

impl Target for TargetAt {
    fn name(&self) -> &'static str {
        "layout-test"
    }
    fn word(&self) -> u16 {
        self.0.word_bits
    }
    fn provides(&self) -> &'static [&'static str] {
        &["exit!"]
    }
    fn emit(&self, _: &Program) -> Vec<u8> {
        Vec::new()
    }
}

fn config(word_bits: u16) -> Config {
    Config {
        word_bits,
        heap_bytes: 128,
    }
}

fn natural_program() -> Program {
    let (mut program, main) = Program::new("seven");
    program.define(main, |b, _| {
        let value = b.constant(Class::Natural, 7);
        let value = b.convert(Class::Word, value);
        b.ret(&[value]);
    });
    program
}

#[test]
fn interpretation_checks_serialized_width_before_execution() {
    let portable = natural_program();
    assert_eq!(portable.layout(), None);
    for word_bits in [16, 32, 64] {
        let scalar = legalize(&portable, config(word_bits)).unwrap();
        let expected = Layout { word_bits };
        assert_eq!(scalar.layout(), Some(expected));
        for actual_bits in [16, 32, 64] {
            let actual = Layout {
                word_bits: actual_bits,
            };
            let result = evaluate::evaluate(
                &scalar,
                scalar.entry(),
                &[],
                EvaluationConfig {
                    word_bits: actual_bits,
                    ..Default::default()
                },
                &mut RejectHost,
            );
            if expected == actual {
                assert_eq!(result.unwrap().returned().unwrap(), [BigUint::from(7u8)]);
            } else {
                assert_eq!(result, Err(Error::LayoutMismatch { expected, actual }));
            }
        }
    }
    assert_eq!(
        portable.layout(),
        None,
        "legalization does not bind its input"
    );
}

#[test]
fn relegalization_and_compilation_cannot_forget_a_bound_layout() {
    let scalar = legalize(&natural_program(), config(32)).unwrap();
    let again = legalize(&scalar, config(32)).unwrap();
    assert_eq!(again.layout(), scalar.layout());
    assert_eq!(again.data(), scalar.data());
    assert_eq!(again.functions().len(), scalar.functions().len());
    assert!(
        legalize(&scalar, config(64))
            .unwrap_err()
            .contains("layout")
    );
    for word_bits in [32, 64] {
        let target = TargetAt(Layout { word_bits });
        let matches = word_bits == 32;
        assert_eq!(target.accepts(&scalar).is_ok(), matches);
        assert_eq!(target.prepare(&scalar).is_ok(), matches);
        assert_eq!(target.compile(&scalar).is_ok(), matches);
    }
}

#[test]
fn prelegalization_cannot_bypass_the_16_bit_runtime_guard() {
    let scalar = legalize(&natural_program(), config(16)).unwrap();
    let target = TargetAt(config(16).layout());
    assert!(
        target
            .accepts(&scalar)
            .unwrap_err()
            .contains("runtime naturals")
    );
    assert!(
        target
            .prepare(&scalar)
            .unwrap_err()
            .contains("runtime naturals")
    );
    assert!(
        target
            .compile(&scalar)
            .unwrap_err()
            .contains("runtime naturals")
    );
}

#[test]
fn runtime_generation_refuses_to_mix_layouts_in_one_pool() {
    let (mut program, _) = Program::new("pool");
    natural::constant(&mut program, config(32), &BigUint::from(7u8)).unwrap();
    let data = program.data().to_vec();
    let functions = program.functions().len();
    assert!(natural::constant(&mut program, config(64), &BigUint::from(8u8)).is_err());
    assert!(natural::append(&mut program, config(64), Needs::default()).is_err());
    assert_eq!(program.data(), data);
    assert_eq!(program.functions().len(), functions);
    assert_eq!(program.layout(), Some(config(32).layout()));
}

#[test]
fn scalar_only_legalization_does_not_bind_a_portable_program() {
    let (mut program, main) = Program::new("scalar");
    program.define(main, |b, _| {
        let seven = b.constant(Class::Word, 7);
        b.ret(&[seven]);
    });
    let scalar = legalize(&program, config(32)).unwrap();
    assert_eq!(scalar.layout(), None);
    for word_bits in [16, 32, 64] {
        assert!(TargetAt(Layout { word_bits }).compile(&scalar).is_ok());
    }
}
