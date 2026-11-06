//! A row of a function's table is a call of the function (DESIGN.md sec:lexical, the test
//! table row): it gives what the same call in the program gives. A loose atom the parameter
//! does not take passes by the body (rule 6 of sec:type_resolution) in a row as in a call, so
//! a table that states what the program does passes, and one that states something else fails.

use super::checks;
use zed_tests::step_helpers::l01_16_elaboration::value;

/// The unit `def` with a table of `rows`, each `(key, call, want)`: every row `key -> want`
/// passes, and `call`, the same call written in the program, gives `want`.
fn agree(def: &str, rows: &[(&str, &str, &str)]) {
    let table: Vec<String> = rows.iter().map(|(k, _, w)| format!("{k} -> {w}")).collect();
    let unit = format!("{def}\ntest {{ {} }}\n", table.join(", "));
    let got = checks(&unit);
    assert_eq!(got.len(), rows.len(), "{unit}{got:?}");
    for c in &got {
        assert!(c.ends_with(": ok"), "{unit}{c}");
    }
    let program: String = rows
        .iter()
        .enumerate()
        .map(|(i, (_, call, _))| format!("v{i} = {call};\n"))
        .collect();
    let program = format!("{def};\n{program}");
    for (i, (_, call, want)) in rows.iter().enumerate() {
        assert_eq!(value(&program, &format!("v{i}")), *want, "{call}");
    }
}

#[test]
fn an_atom_a_declared_parameter_does_not_take_passes_by_in_a_row() {
    // The body would give 5; the call never runs it.
    agree(
        "g(positional n: int) = 5",
        &[("#nf", "g(#nf)", "#nf"), ("1", "g(1)", "5")],
    );
    // A row that states the body's value for the atom fails with the call's value.
    assert_eq!(
        checks("g(positional n: int) = 5\ntest { #nf -> 5 }\n"),
        ["2:8: `#nf -> 5` of `g`: the result is #nf"]
    );
}

#[test]
fn the_row_of_issue_1_gives_what_the_program_gives() {
    // The function of issue 1: a missing line reads as the empty string.
    agree(
        "readName(positional line) = trim(line else \"\")",
        &[
            ("#notFound", "readName(#notFound)", "\"\""),
            ("\" Ada \"", "readName(\" Ada \")", "\"Ada\""),
        ],
    );
}

#[test]
fn an_argument_passes_by_only_the_atoms_its_parameter_does_not_take() {
    // `#missing` goes into the body, which defaults it; `#other` selects no arrow and passes.
    agree(
        "stock(positional count: int | #missing) = count else 0",
        &[
            ("#missing", "stock(#missing)", "0"),
            ("#other", "stock(#other)", "#other"),
            ("12", "stock(12)", "12"),
        ],
    );
}

#[test]
fn each_argument_of_a_tuple_key_passes_its_own_atoms() {
    agree(
        "total(positional price: int, positional qty: int) = price * qty",
        &[
            ("(#noPrice, 3)", "total(#noPrice, 3)", "#noPrice"),
            ("(4, #noQty)", "total(4, #noQty)", "#noQty"),
            ("(4, 3)", "total(4, 3)", "12"),
        ],
    );
    // The key's components are in declaration order whatever the parameters' kinds.
    agree(
        "fee(positional amount: int, rate: int) = amount * rate",
        &[
            ("(#nf, 3)", "fee(#nf, rate: 3)", "#nf"),
            ("(2, #nf)", "fee(2, rate: #nf)", "#nf"),
            ("(2, 3)", "fee(2, rate: 3)", "6"),
        ],
    );
}

#[test]
fn atoms_of_two_arguments_merge_in_a_row_as_in_a_call() {
    let def = "total(positional price: int, positional qty: int) = price * qty";
    let call = format!("{def};\nboth = total(#noPrice, #noQty);\n");
    let merged = value(&call, "both");
    assert_eq!(merged, "#errs({#noPrice, #noQty})");
    assert_eq!(
        checks(&format!(
            "{def}\ntest {{ (#noPrice, #noQty) -> #noPrice }}\n"
        )),
        [format!(
            "2:8: `(#noPrice, #noQty) -> #noPrice` of `total`: the result is {merged}"
        )]
    );
}

#[test]
fn a_key_that_is_itself_a_call_passing_an_atom_passes_it_on() {
    agree(
        "next(positional n: int) = n + 1;\nscaled(positional n: int) = n * 10",
        &[
            ("next(#q)", "scaled(next(#q))", "#q"),
            ("next(1)", "scaled(next(1))", "20"),
        ],
    );
}

#[test]
fn a_row_on_an_inferred_parameter_gives_what_a_call_gives() {
    // Whatever the call gives for the atom, the row gives the same (the inferred class's
    // atoms are CLASS-atoms' to settle, so the value is read from the call, not stated).
    let def = "size(positional x) = if x == #nf { 0 } else { len(x) }";
    let called = value(&format!("{def};\nv = size(#nf);\n"), "v");
    agree(
        def,
        &[
            ("#nf", "size(#nf)", &called),
            ("\"ab\"", "size(\"ab\")", "2"),
        ],
    );
}
