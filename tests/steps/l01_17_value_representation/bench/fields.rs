//! Atoms with many named fields at the rule of low complexity (DESIGN.md Part G). The input is
//! `fields` of `fields.rs`, whose test `an_atom_with_named_fields_matches_its_pattern` checks
//! it at three fields.

use zed_kernel::{Evaluator, World};
use zed_tests::deep::resolved;
use zed_tests::scaling::{check, inputs};
use zed_tests::step_helpers::l01_16_elaboration::{checked, with_prelude};

use super::super::fields::fields;

#[test]
fn an_atom_and_a_pattern_with_many_named_fields_scale() {
    // Each field of a pattern was looked for among those before it, to report a repeat.
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 3 µs a
    // field, 1x 57 ms. Building the inputs, each source checked and elaborated, takes about
    // 45 µs a field of the 9n built, so that, not 1x, holds n down: the test takes about 9 s.
    let n = 20_000;
    let units = inputs(n, |n| checked(&fields(n)));
    check("elaborating n named fields", n, |n| {
        assert!(units[&n].elab().get("x").is_some());
    });
}

#[test]
fn matching_many_named_fields_scales() {
    // Each field of the pattern was looked for in the atom's payload from its start.
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 1 µs a field,
    // 1x 19 ms. As above, building the inputs holds n down: the test takes about 8 s.
    let n = 20_000;
    let terms = inputs(n, |n| {
        with_prelude(checked(&fields(n)).elab().get("x").unwrap())
    });
    check("matching n named fields", n, |n| {
        let v = Evaluator::new(World::new()).run(&terms[&n]).unwrap();
        assert_eq!(v.to_string(), "1");
    });
}

#[test]
fn checking_many_named_fields_scales() {
    // Each field of the pattern copied the type it is matched on, and so every field of the
    // atom: at 4000 fields the check took 5 s (COMPLEXITY.md F100).
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 12 µs a
    // field, 1x about 0.24 s. At 30,000 fields the test, with its inputs, took 17 s.
    let n = 20_000;
    let units = inputs(n, |n| resolved(&fields(n)));
    check("checking n named fields", n, |n| {
        let (stmts, res) = &units[&n];
        assert!(zedc::check::walk::check(stmts, res).errors.is_empty());
    });
}
