//! Atoms with many named fields at the rule of low complexity (DESIGN.md Part G): building the
//! atom and its pattern, and matching the one against the other. The benchmarks are in
//! `bench::fields`.

use zed_tests::deep::resolved;
use zed_tests::step_helpers::l01_16_elaboration::value;

/// An atom with `n` named fields `p0`, `p1`, … (`f64` would name a type), and an `else` that matches it naming them all.
pub(crate) fn fields(n: usize) -> String {
    let names: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let given: Vec<String> = names.iter().map(|f| format!("{f}: 1")).collect();
    let named: Vec<String> = names.iter().map(|f| format!("{f}:")).collect();
    format!(
        "e = #big({});\nx = e else #big({}) -> p0;\n",
        given.join(", "),
        named.join(", ")
    )
}

/// What the benchmarks check at each size, at three fields: the unit checks with no error, and
/// the match elaborates and gives the first field.
#[test]
fn an_atom_with_named_fields_matches_its_pattern() {
    let (stmts, res) = resolved(&fields(3));
    assert!(zedc::check::walk::check(&stmts, &res).errors.is_empty());
    assert_eq!(value(&fields(3), "x"), "1");
}
