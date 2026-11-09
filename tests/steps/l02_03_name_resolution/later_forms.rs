//! The forms of step L3.2 and the sort keys of L5.1 are reported as compiled from their step,
//! and the names inside them are still resolved: a `for` binds its keypath pattern in its
//! `where` and its body, and a name nothing binds is reported there as anywhere else.

use super::{alone, describe, errors};

#[test]
fn the_operator_of_a_reduction_is_resolved() {
    let text = "f(xs) = xs >< max;\n";
    assert_eq!(errors(text), Vec::<String>::new());
    assert_eq!(describe(text, &alone(text), "max", 0), ["prelude max"]);
    assert_eq!(
        errors("f(xs) = xs >< maks;\n"),
        [
            "`maks` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `maks`, or correct the name if it is misspelled. [maks]"
        ]
    );
}

#[test]
fn a_name_inside_a_display_range_or_test_is_resolved() {
    for (text, name) in [
        ("f(a) = [a, b];\n", "b"),
        ("f(a) = {a, b};\n", "b"),
        ("f(a) = {a -> b};\n", "b"),
        ("f(a) = {b -> a};\n", "b"),
        ("f(n) = 0..<m;\n", "m"),
        ("f(n) = m..=n;\n", "m"),
        ("f(x) = x in s;\n", "s"),
        ("f(x) = s not in x;\n", "s"),
        ("f(x) = s::len;\n", "s"),
    ] {
        assert_eq!(
            errors(text),
            [format!("{} [{name}]", zed_tests::undefined(name))],
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
        [
            "`y` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `y`, or correct the name if it is misspelled. [y]"
        ]
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
        [
            "`v` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `v`, or correct the name if it is misspelled. [v]"
        ]
    );
    assert_eq!(
        errors("f(m) = for k -> _ in m { k };\ng() = k;\n"),
        [
            "`k` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `k`, or correct the name if it is misspelled. [k]"
        ]
    );
    assert_eq!(
        errors("f(m) = for v in m { w };\n"),
        [
            "`w` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `w`, or correct the name if it is misspelled. [w]"
        ]
    );
}
