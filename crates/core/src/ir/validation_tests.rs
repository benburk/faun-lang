use super::*;

#[test]
fn existing_target_fixture_programs_validate() {
    for (name, p, _) in crate::programs::printing() {
        validate(&p).unwrap_or_else(|error| panic!("{name}: {error}"));
    }
}
