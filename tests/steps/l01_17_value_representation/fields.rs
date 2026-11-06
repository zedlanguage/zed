//! Atoms with many named fields at the rule of low complexity (DESIGN.md Part G): building the
//! atom and its pattern, and matching the one against the other.

use zed_kernel::{Evaluator, World};
use zed_tests::deep::resolved;
use zed_tests::scaling::{check, inputs};

use zed_tests::step_helpers::l01_16_elaboration::{checked, value, with_prelude};

/// An atom with `n` named fields `p0`, `p1`, … (`f64` would name a type), and an `else` that matches it naming them all.
fn fields(n: usize) -> String {
    let names: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let given: Vec<String> = names.iter().map(|f| format!("{f}: 1")).collect();
    let named: Vec<String> = names.iter().map(|f| format!("{f}:")).collect();
    format!(
        "e = #big({});\nx = e else #big({}) -> p0;\n",
        given.join(", "),
        named.join(", ")
    )
}

#[test]
fn an_atom_and_a_pattern_with_many_named_fields_scale() {
    // Each field of a pattern was looked for among those before it, to report a repeat.
    assert_eq!(value(&fields(3), "x"), "1");
    let units = inputs(2_000, |n| checked(&fields(n)));
    check("elaborating n named fields", 2_000, |n| {
        assert!(units[&n].elab().get("x").is_some());
    });
}

#[test]
fn matching_many_named_fields_scales() {
    // Each field of the pattern was looked for in the atom's payload from its start.
    let terms = inputs(2_000, |n| {
        with_prelude(checked(&fields(n)).elab().get("x").unwrap())
    });
    check("matching n named fields", 2_000, |n| {
        let v = Evaluator::new(World::new()).run(&terms[&n]).unwrap();
        assert_eq!(v.to_string(), "1");
    });
}

#[test]
fn checking_many_named_fields_scales() {
    // Each field of the pattern copied the type it is matched on, and so every field of the
    // atom: at 4000 fields the check took 5 s (COMPLEXITY.md F100).
    let units = inputs(2_000, |n| resolved(&fields(n)));
    check("checking n named fields", 2_000, |n| {
        let (stmts, res) = &units[&n];
        assert!(zedc::check::check(stmts, res).errors.is_empty());
    });
}
