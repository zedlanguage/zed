//! The errors elaboration reports, one case each.

use super::errors;
use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;
use zedc::resolve::resolve;

fn one(src: &str) -> String {
    let es = errors(src);
    assert_eq!(es.len(), 1, "{src}: {es:?}");
    es[0].clone()
}

/// The one error name resolution gives the unit `src`, which then never reaches elaboration:
/// a name used above its definition.
fn above(src: &str) -> String {
    let tokens = lex_fence(src).unwrap();
    let tree = parse(src, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(src, &tokens, &tree).unwrap();
    let es = resolve(&stmts).err().unwrap_or_default();
    assert_eq!(es.len(), 1, "{src}: {es:?}");
    assert_eq!(es[0].row, Some(Row::NameAboveDefinition), "{src}: {es:?}");
    es[0].message.clone()
}

#[test]
fn recursion_is_layer_l6() {
    let e = one("countdown(positional n) = if n == 0 { 0 } else { countdown(n - 1) };\n");
    assert!(
        e.starts_with("`countdown` is defined in terms of itself, which is recursion."),
        "{e}"
    );
    let e = one("a = b + 1;\nb = a + 1;\n");
    assert!(
        e.starts_with("`a`, `b` are defined in terms of each other"),
        "{e}"
    );
    // In a block a name is used only below its definition, so two bindings of a block that
    // read each other are rejected by name resolution, before elaboration (DESIGN.md
    // sec:lexical).
    let e = above("total = { x = y; y = x; x };\n");
    assert!(
        e.starts_with("`y` is used. In a block a name is used only below"),
        "{e}"
    );
}

#[test]
fn call_rules() {
    let greet = "greet(positional name, punct = \"!\") = name ++ punct;\n";
    let cases = [
        (
            "x = greet(name: \"Al\");",
            "this argument is passed by name, as `name: …`, and `name` of `greet` is positional, so a call passes it only by position [\"Al\"]",
        ),
        (
            "x = greet(punct: \"?\");",
            "this call of `greet` gives no value to its parameter `name`, and `name` has no default, so the call cannot be made [greet(punct: \"?\")]",
        ),
        (
            "x = greet(\"Al\", \"?\");",
            "this argument is passed by position, and the parameter it reaches, `punct` of `greet`, is a named parameter, which a call passes only by name, as `punct: …` [\"?\"]",
        ),
        (
            "x = greet(\"Al\", tone: 1);",
            "this argument is passed by the name `tone`, and `greet` has no parameter of that name, so the argument has no parameter to go to [1]",
        ),
        (
            "x = greet(\"Al\", punct: \"?\", ...);",
            "this call of `greet` ends in `...`, which makes a function of the named parameters the call leaves out, and the call gives every named parameter a value, so `...` has no parameter to leave out [greet(\"Al\", punct: \"?\", ...)]",
        ),
        (
            "x = greet(punct: \"?\", ...);",
            "this call of `greet` ends in `...`, which makes a function of the named parameters the call leaves out, and the call also leaves out `name`, a positional parameter, which `...` cannot leave out [greet(punct: \"?\", ...)]",
        ),
        (
            "x = \"Al\".greet(\"?\");",
            "this argument is passed by position, and the parameter it reaches, `punct` of `greet`, is a named parameter, which a call passes only by name, as `punct: …` [\"?\"]",
        ),
    ];
    for (call, want) in cases {
        assert_eq!(one(&format!("{greet}{call}\n")), want, "{call}");
    }
}

#[test]
fn too_many_arguments() {
    let e = one("pair(positional a, positional b) = (a, b);\nx = 1.pair(2, 3);\n");
    assert_eq!(
        e,
        "this argument is one more than `pair` takes: `pair` takes 2 arguments by position, and the arguments before this one already fill them all [3]"
    );
}

#[test]
fn defaults_that_read_each_other() {
    // A default reads only the parameters before it (DESIGN.md sec:lexical), so defaults
    // cannot read each other in a cycle: the first that reads a later one is rejected by name
    // resolution, before elaboration.
    let e = above("f(a = b, b = a) = a;\ny = f();\n");
    assert!(
        e.starts_with("`b` is used. In a parameter list a name is used only below"),
        "{e}"
    );
}

#[test]
fn named_arguments_through_a_value_need_its_parameter_names() {
    // A lambda with no expected type takes its arguments by position.
    let e = one("inc = x -> x + 1;\ny = inc(x: 1);\n");
    assert_eq!(
        e,
        "this argument is passed by name, as `x: …`, and `x` of `(T) -> T for T in int | f64 | rat` is positional, so a call passes it only by position [1]"
    );
    // A prelude word, and a value of unknown type, give no parameter names.
    let want = "named arguments and `...` need the parameter names of the function called, \
                which a prelude word and a value of unknown type do not give";
    let e = one("y = len(s: \"ab\");\n");
    assert_eq!(e, format!("{want} [len(s: \"ab\")]"));
    let e = one("g(f) = f(x: 1);\n");
    assert_eq!(e, format!("{want} [f(x: 1)]"));
}

#[test]
fn forms_of_later_steps_and_layers() {
    let cases = [
        (
            "p = 1;\nx = p.size;",
            "`size` is not a function in scope, and reading a field with `.size` is part of the Zed language that this version of zedc does not compile yet. Call a function in scope, or correct the name if it is misspelled. [p.size]",
        ),
        (
            "p = 1;\nx = p.map(1);",
            concat!(zed_tests::not_yet!("the prelude word `map`"), " [p.map]"),
        ),
        (
            "f = (x = 1) -> x;",
            "a lambda's parameter has a default only where an expected function type leaves \
             it out [1]",
        ),
        (
            "f(x: int) = 1;\nf(x: String) = 2;\ny = f(x: 1);",
            "`f` names 2 definitions, and this version of zedc does not yet choose among definitions that share a name. Give each of them a name of its own. [f]",
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
