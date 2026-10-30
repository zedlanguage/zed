//! The errors elaboration reports, one case each.

use super::errors;

fn one(src: &str) -> String {
    let es = errors(src);
    assert_eq!(es.len(), 1, "{src}: {es:?}");
    es[0].clone()
}

#[test]
fn recursion_is_layer_l6() {
    let e = one("countdown(positional n) = if n == 0 { 0 } else { countdown(n - 1) };\n");
    assert!(
        e.starts_with("`countdown` is defined in terms of itself: recursion arrives at layer L6"),
        "{e}"
    );
    let e = one("a = b + 1;\nb = a + 1;\n");
    assert!(
        e.starts_with("`a`, `b` are defined in terms of each other"),
        "{e}"
    );
    let e = one("total = { x = y; y = x; x };\n");
    assert!(
        e.contains("are defined in terms of each other: recursion arrives at layer L6"),
        "{e}"
    );
}

#[test]
fn call_rules() {
    let greet = "greet(positional name, punct = \"!\") = name ++ punct;\n";
    let cases = [
        (
            "x = greet(name: \"Al\");",
            "`name` of `greet` is positional: pass it by position [\"Al\"]",
        ),
        (
            "x = greet(punct: \"?\");",
            "missing argument `name` of `greet` [greet(punct: \"?\")]",
        ),
        (
            "x = greet(\"Al\", \"?\");",
            "`punct` of `greet` is named: pass it as `punct: …` [\"?\"]",
        ),
        (
            "x = greet(\"Al\", tone: 1);",
            "`greet` has no parameter `tone` [1]",
        ),
        (
            "x = greet(\"Al\", punct: \"?\", ...);",
            "`...` leaves no named parameter out [greet(\"Al\", punct: \"?\", ...)]",
        ),
        (
            "x = greet(punct: \"?\", ...);",
            "`...` curries named parameters only; the positional `name` is left out [greet(punct: \"?\", ...)]",
        ),
        (
            "x = \"Al\".greet(\"?\");",
            "`punct` of `greet` is named: pass it as `punct: …` [\"?\"]",
        ),
    ];
    for (call, want) in cases {
        assert_eq!(one(&format!("{greet}{call}\n")), want, "{call}");
    }
}

#[test]
fn too_many_arguments() {
    let e = one("pair(positional a, positional b) = (a, b);\nx = 1.pair(2, 3);\n");
    assert_eq!(e, "too many arguments: `pair` takes 2 [3]");
}

#[test]
fn defaults_that_read_each_other() {
    let e = one("f(a = b, b = a) = a;\ny = f();\n");
    assert_eq!(e, "the defaults of `a`, `b` read each other [f()]");
}

#[test]
fn named_arguments_through_a_value_need_types() {
    let e = one("inc = x -> x + 1;\ny = inc(x: 1);\n");
    assert!(
        e.starts_with("named arguments and `...` need the declaration"),
        "{e}"
    );
}

#[test]
fn forms_of_later_steps_and_layers() {
    let cases = [
        (
            "p = 1;\nx = p.size;",
            "`size` is not a function in scope, and fields arrive at L2 [p.size]",
        ),
        (
            "p = 1;\nx = p.map(1);",
            "`map` is a prelude word of layer L3 [p.map]",
        ),
        (
            "f = (x = 1) -> x;",
            "a lambda's default arrives with its expected type at step L1.26 [1]",
        ),
        (
            "f(x: int) = 1;\nf(x: String) = 2;\ny = f(x: 1);",
            "`f` names 2 overloads; choosing among them arrives at L2 [f]",
        ),
    ];
    for (src, want) in cases {
        assert_eq!(one(&format!("{src}\n")), want, "{src}");
    }
}

#[test]
fn test_tables() {
    let e = one("area(w, h) = w * h test { 2 -> 6 }\n");
    assert_eq!(
        e,
        "a test key of `area` is the tuple of its 2 arguments [2]"
    );
    let e = one("outer = { sq(positional x) = x * x test { 2 -> 4 } sq(3) };\n");
    assert!(
        e.starts_with("`sq` has a test table, which belongs to a function at the unit's top level"),
        "{e}"
    );
}
