//! The forms of step L3.2 and the sort keys of L5.1 are reported as compiled from their step,
//! and the names inside them are still resolved: a `for` binds its keypath pattern in its
//! `where` and its body, and a name nothing binds is reported there as anywhere else.

use super::{alone, describe, errors};
use zed_tests::undefined_noted;

#[test]
fn the_operator_of_a_reduction_is_resolved() {
    let text = "f(xs) = xs >< max;\n";
    assert_eq!(errors(text), Vec::<String>::new());
    assert_eq!(describe(text, &alone(text), "max", 0), ["prelude max"]);
    assert_eq!(
        errors("f(xs) = xs >< maks;\n"),
        [undefined_noted("maks", 1, None)]
    );
}

#[test]
fn a_name_inside_a_display_range_or_test_is_resolved() {
    // Each with the visible name one slip away that comes first in name order.
    for (text, name, near) in [
        ("f(a) = [a, b];\n", "b", "a"),
        ("f(a) = {a, b};\n", "b", "a"),
        ("f(a) = {a -> b};\n", "b", "a"),
        ("f(a) = {b -> a};\n", "b", "a"),
        ("f(n) = 0..<m;\n", "m", "f"),
        ("f(n) = m..=n;\n", "m", "f"),
        ("f(x) = x in s;\n", "s", "f"),
        ("f(x) = s not in x;\n", "s", "f"),
        ("f(x) = s::len;\n", "s", "f"),
    ] {
        assert_eq!(
            errors(text),
            [undefined_noted(name, 1, Some(near))],
            "{text}"
        );
    }
    let text = "f(a, n) = [a, n] in {a -> 0..<n};\n";
    let r = alone(text);
    assert_eq!(errors(text), Vec::<String>::new());
    assert_eq!(describe(text, &r, "n", 2), ["param n"]);
}

#[test]
fn a_sort_key_is_resolved() {
    let text = "g(k) = k;\nf(x) = g(desc x);\n";
    assert_eq!(errors(text), Vec::<String>::new());
    assert_eq!(describe(text, &alone(text), "x", 1), ["param x"]);
    assert_eq!(
        errors("g(k) = k;\nf(x) = g(asc y);\n"),
        [undefined_noted("y", 1, Some("f"))]
    );
}

#[test]
fn a_for_binds_its_pattern_in_its_where_and_body_only() {
    let text = "f(m, lim) = for k -> v in m where k < lim { v + k };\n";
    let r = alone(text);
    assert_eq!(errors(text), Vec::<String>::new());
    assert_eq!(describe(text, &r, "k", 1), ["pattern k"]);
    assert_eq!(describe(text, &r, "v", 1), ["pattern v"]);
    assert_eq!(describe(text, &r, "m", 1), ["param m"]);
    // The source is read outside the pattern's scope, and the pattern binds nothing after it.
    assert_eq!(
        errors("f() = for v in v { v };\n"),
        [undefined_noted("v", 1, Some("f"))]
    );
    assert_eq!(
        errors("f(m) = for k -> _ in m { k };\ng() = k;\n"),
        [undefined_noted("k", 1, Some("f"))]
    );
    // Three blocks: the brace of the body, the pattern's scope and the parameters'.
    assert_eq!(
        errors("f(m) = for v in m { w };\n"),
        [undefined_noted("w", 3, Some("f"))]
    );
}
