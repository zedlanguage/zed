//! The resolution order: block scopes, innermost outward; the unit's top level; the prelude.

use super::{at, errors, run};

#[test]
fn the_innermost_block_that_binds_a_name_wins() {
    let text = "f(x) { y = x + 1; z = { y = 0; y + 1 }; return y + z; }";
    assert_eq!(at(text, "y", 2), ["binding y = 0;"]);
    assert_eq!(at(text, "y", 3), ["binding y = x + 1;"]);
}

#[test]
fn a_name_not_in_a_block_is_found_in_the_units_top_level() {
    let text = "rate = 3; total(n) { k = n * rate; return k; }";
    assert_eq!(at(text, "rate", 1), ["binding rate = 3;"]);
    assert_eq!(at(text, "n", 1), ["param n"]);
}

#[test]
fn a_name_the_unit_does_not_bind_is_found_in_the_prelude() {
    let text = "name = \"Ada\"; size = len(name);";
    assert_eq!(at(text, "len", 0), ["prelude len"]);
}

#[test]
fn a_units_own_name_shadows_a_prelude_word() {
    // DESIGN.md: a program's own name shadows it (`scan = 0` declares a variable at any layer)
    let text = "len(s) = 0; size = len(\"Ada\"); scan = 0; next = scan + 1;";
    assert_eq!(at(text, "len", 1), ["function len(s) = 0;"]);
    assert_eq!(at(text, "scan", 1), ["binding scan = 0;"]);
}

#[test]
fn a_prelude_word_of_a_later_layer_is_an_error_naming_the_layer() {
    let text = "evens(xs) = where(xs, x -> x mod 2 == 0); best = sort(evens);";
    assert_eq!(
        errors(text),
        [
            "`where` is a prelude word of layer L3 [where]",
            "`sort` is a prelude word of layer L5 [sort]",
        ]
    );
}

#[test]
fn statement_order_does_not_matter() {
    let text = "total = price + tax; tax = price div 10; price = 200;";
    assert_eq!(at(text, "price", 0), ["binding price = 200;"]);
    assert_eq!(at(text, "tax", 0), ["binding tax = price div 10;"]);
}

#[test]
fn a_name_bound_nowhere_is_an_error() {
    assert_eq!(
        errors("total = price + 1; shown = total.price;"),
        ["`price` is not defined [price]"]
    );
}

#[test]
fn a_type_name_resolves_to_the_prelude_and_a_unit_declares_none_at_l1() {
    let r = run("half(n: int) = n div 2; ok(p: Point) = p;");
    assert_eq!(r.unwrap_err(), ["the type `Point` is not defined [Point]"]);
    let text = "main(stdin: Lines) -> (stdout: Lines) { stdout <- stdin; }";
    assert!(run(text).is_ok());
}
