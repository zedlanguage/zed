//! A family whose entries hold functions (row FAIL-family-function-entry). DESIGN.md L1.17:
//! "A tuple, an array or a struct may hold a function at any depth"; sec:values_morphisms:
//! "Application is indexing", and `p(1)(2)` is valid for a function that returns a function.
//! So `b["a"]` reads the entry and `(2)` applies it. The reference evaluator keeps such a
//! family as a held value (`HeldFamily` in crates/zed-kernel/src/value.rs): its keys, and its
//! data entries, by the rules of a data family, and each entry that holds a function as a part
//! of its own. Each expected value is worked by hand from the program. The same programs run
//! by `zedc run` and by an executable are in `l03_02_map_run::functions`.

use zed_tests::step_helpers::l01_16_elaboration::value;

/// Two functions at the keys "a" and "b": `b["a"](n)` is `n + 1`, `b["b"](n)` is `2 n`.
const B: &str = "b = { \"a\" -> (y -> y + 1), \"b\" -> (y -> y * 2) };\n";

/// The value of `a` in `B` followed by `body`.
fn a(body: &str) -> String {
    value(&format!("{B}{body}"), "a")
}

#[test]
fn a_function_read_from_a_family_display_is_applied() {
    let src = "b = { \"a\" -> (y -> y + 1) };\na = b[\"a\"](2);\n";
    assert_eq!(value(src, "a"), "3", "{src}");
    assert_eq!(a("a = b[\"a\"](2);\n"), "3");
    assert_eq!(a("a = b[\"b\"](2);\n"), "4");
}

#[test]
fn a_function_made_by_map_is_read_and_applied() {
    let src = "b = { \"a\" -> 1 }.map(r -> (y -> y + 1));\na = b[\"a\"](2);\n";
    assert_eq!(value(src, "a"), "3", "{src}");
    // The function captures the entry it was made from: 2 + 1.
    let src = "b = { \"a\" -> 1 }.map(r -> (y -> y + r));\na = b[\"a\"](2);\n";
    assert_eq!(value(src, "a"), "3", "{src}");
    // One function per entry, each with its own capture: 10 + 1 and 10 + 2.
    let src = "a = { \"a\" -> 1, \"b\" -> 2 }.map(r -> (y -> y + r)).map(f -> f(10));\n";
    assert_eq!(value(src, "a"), "{\"a\" -> 11, \"b\" -> 12}", "{src}");
}

/// The family passed to a function, which reads and applies an entry: `b["b"](10)` is 20.
#[test]
fn a_family_of_functions_passed_on_is_read_and_applied() {
    assert_eq!(
        a("ap(positional f, positional k) = f[k](10);\na = ap(b, \"b\");\n"),
        "20"
    );
    // Made inside a function, from its argument: 1 + 5.
    let src = "f(positional k) = { \"a\" -> (y -> y + k) };\na = f(5)[\"a\"](1);\n";
    assert_eq!(value(src, "a"), "6", "{src}");
}

/// Held by a tuple, an array, and a family of families. A struct holding one waits for
/// structs to compile (row TEST-family-function-struct-field).
#[test]
fn a_family_of_functions_held_by_another_value_is_read_and_applied() {
    assert_eq!(a("p = (b, 1);\na = p[0][\"a\"](2);\n"), "3");
    assert_eq!(a("a = [b, b][1][\"b\"](3);\n"), "6");
    assert_eq!(a("a = { 1 -> b, 2 -> b }[2][\"b\"](3);\n"), "6");
    assert_eq!(
        a("a = { 1 -> b, 2 -> b }.map(c -> c[\"a\"](1));\n"),
        "{1 -> 2, 2 -> 2}"
    );
    let src = "a = { \"a\" -> { \"b\" -> (y -> y + 1) } }[\"a\"][\"b\"](2);\n";
    assert_eq!(value(src, "a"), "3", "{src}");
}

/// A key that is not in the family gives `#notFound` (sec:type_language), and applying it
/// passes the failure on; `else` gives the default, a function or a number.
#[test]
fn a_missed_key_gives_not_found_and_else_its_default() {
    let ks = "ks = [\"a\", \"z\"];\n";
    assert_eq!(a(&format!("{ks}a = b[ks[1]];\n")), "#notFound");
    assert_eq!(a(&format!("{ks}a = b[ks[1]](2);\n")), "#notFound");
    assert_eq!(a(&format!("{ks}a = b[ks[1]](2) else -1;\n")), "-1");
    assert_eq!(a(&format!("{ks}a = b[ks[0]](2) else -1;\n")), "3");
    assert_eq!(a(&format!("{ks}a = (b[ks[1]] else (y -> 0))(5);\n")), "0");
    assert_eq!(a(&format!("{ks}a = (b[ks[0]] else (y -> 0))(5);\n")), "6");
    assert_eq!(a(&format!("{ks}a = ks[1] in b;\n")), "false");
}

/// An array of functions is a family keyed by position: `[…][1](5)` is 10.
#[test]
fn an_array_of_functions_is_read_and_applied() {
    let src = "a = [(x -> x + 1), (x -> x * 2)][1](5);\n";
    assert_eq!(value(src, "a"), "10", "{src}");
}

/// `map` applies each entry, and may make functions from functions: f(1) + 100 at "b" is 102.
#[test]
fn map_over_a_family_of_functions() {
    assert_eq!(a("a = b.map(f -> f(2));\n"), "{\"a\" -> 3, \"b\" -> 4}");
    assert_eq!(
        a("c = b.map(f -> (y -> f(y) + 100));\na = c[\"b\"](1);\n"),
        "102"
    );
    assert_eq!(a("a = b.map(f -> f)[\"a\"](5);\n"), "6");
    assert_eq!(a("a = b.map(f -> (f, 1))[\"a\"][0](5);\n"), "6");
}

/// `count`, `in`, `first` and `last` read the keys and the entries at the ends.
#[test]
fn count_in_first_and_last() {
    assert_eq!(a("a = b.count;\n"), "2");
    assert_eq!(a("a = \"a\" in b;\n"), "true");
    assert_eq!(a("c = b.first;\na = c(4);\n"), "5");
    assert_eq!(a("c = b.last;\na = c(4);\n"), "8");
}

/// Data entries beside function entries keep their values.
#[test]
fn data_entries_beside_function_entries() {
    let c = "c = { \"a\" -> (y -> y + 1), \"b\" -> 7 };\n";
    assert_eq!(value(&format!("{c}a = c[\"b\"];\n"), "a"), "7");
    assert_eq!(value(&format!("{c}a = c.last;\n"), "a"), "7");
    assert_eq!(value(&format!("{c}a = c.count;\n"), "a"), "2");
    assert_eq!(
        value(&format!("{c}a = c.map(v -> 0);\n"), "a"),
        "{\"a\" -> 0, \"b\" -> 0}"
    );
}

/// Two entries at one key collide as in a family of data (sec:corner_cases), and the run
/// stops with that message, not as a bug in zedc.
#[test]
fn two_function_entries_at_one_key_collide() {
    let src = "b = { \"a\" -> (y -> y + 1), \"a\" -> (y -> y) };\na = b[\"a\"](1);\n";
    let got = value(src, "a");
    assert!(
        got.contains("two entries were written at the same key path, [\"a\"]"),
        "{src}\n{got}"
    );
    assert!(!got.contains("a bug in zedc"), "{src}\n{got}");
}

/// `where` and a remap need no entry to be data (L1.17: only showing and `==` do), so they
/// keep the functions (row FAIL-held-family-operators). `b["a"](3)` is 4 and `b["b"](3)` is 6,
/// so `f(3) > 5` keeps "b" alone.
#[test]
fn where_and_a_remap_over_a_family_of_functions() {
    assert_eq!(a("a = b.where(f -> true).count;\n"), "2");
    assert_eq!(a("c = b.where(f -> true);\na = c[\"a\"](2);\n"), "3");
    assert_eq!(a("a = b.where(f -> f(3) > 5).count;\n"), "1");
    assert_eq!(a("c = b.where(f -> f(3) > 5);\na = c[\"b\"](3);\n"), "6");
    assert_eq!(a("c = b as (k -> v) into (k -> v);\na = c[\"a\"](2);\n"), "3");
}
