//! What opens a scope, what one scope may bind, and what each scope sees.

use super::{at, errors, run};
use zedc::resolve::Ref;

#[test]
fn rebinding_in_one_scope_is_an_error_and_a_nested_scope_may_shadow() {
    // EXAMPLES.md [d4] sec:lexical — single assignment
    let text = "f(x) { y = x + 1; y = y * 2; z = { y = 0; y }; return y + z; }";
    assert_eq!(
        errors(text),
        ["`y` is already bound in this scope, at byte 7 [y = y * 2;]"]
    );
}

#[test]
fn a_parameter_and_the_body_blocks_statements_share_one_scope() {
    assert_eq!(
        errors("clean(s) { s = trim(s); return s; }"),
        ["`s` is already bound in this scope, at byte 6 [s = trim(s);]"]
    );
    let text = "clean(s) { t = { s = trim(s); s }; return t; }";
    assert_eq!(at(text, "s", 3), ["binding s = trim(s);"]);
}

#[test]
fn functions_of_one_name_with_different_parameter_types_form_an_overload_set() {
    let text = "show(n: int) = n; show(s: String) = s; out = show(1);";
    assert_eq!(
        at(text, "show", 2),
        [
            "function show(n: int) = n;",
            "function show(s: String) = s;"
        ]
    );
    assert_eq!(
        errors("show(n: int) = n; show(m: int) = m;"),
        [
            "`show` is already declared in this scope with these parameter types, at byte 0 \
             [show(m: int) = m;]"
        ]
    );
}

#[test]
fn a_lambdas_parameter_shadows_an_outer_name() {
    let text = "x = 10; inc = x -> x + 1; y = x;";
    assert_eq!(at(text, "x", 2), ["param x"]);
    assert_eq!(at(text, "x", 3), ["binding x = 10;"]);
}

#[test]
fn a_parameters_type_and_default_see_the_parameters_but_not_the_body() {
    let text = "clamp(v: int, lo: int = 0, hi: int = lo + 100) { m = 1; return v; }";
    assert_eq!(at(text, "lo", 1), ["param lo: int = 0"]);
    assert_eq!(
        errors("f(a: int = m) { m = 1; return a; }"),
        ["`m` is not defined [m]"]
    );
}

#[test]
fn test_cases_are_read_in_the_scope_around_the_function() {
    let text = "two = 2; double(x) = two * x test { 1 -> two }";
    assert_eq!(at(text, "two", 2), ["binding two = 2;"]);
    assert_eq!(
        errors("double(x) = 2 * x test { x -> 2 }"),
        ["`x` is not defined [x]"]
    );
}

#[test]
fn an_else_pattern_binds_its_fields_in_its_default() {
    let text =
        "pos = 1; n = parse(s) else #syntaxError(pos:) -> pos; m = pos; s = \"1\"; parse(t) = t;";
    assert_eq!(at(text, "pos", 2), ["pattern #syntaxError(pos:)"]);
    assert_eq!(at(text, "pos", 3), ["binding pos = 1;"]);
}

#[test]
fn a_push_names_an_output_port_of_its_function() {
    let text = "main(stdin: Lines) -> (stdout: Lines) { stdout <- stdin; }";
    assert_eq!(at(text, "stdout", 1), ["port stdout: Lines"]);
    assert_eq!(
        errors("main() { stdout <- \"hi\"; }"),
        ["`stdout` is not defined [stdout <- \"hi\";]"]
    );
}

#[test]
fn a_member_whose_name_is_in_scope_is_recorded_for_the_uniform_call() {
    // DESIGN.md: the uniform call `x.f(a)` is `f(x, a)`; a field is told apart at L1.16
    let text = "twice(x) = x * 2; p = 3; a = p.twice; b = p.size;";
    let r = run(text).unwrap();
    let member = |m: &str| {
        let start = text.find(m).unwrap();
        r.uses
            .iter()
            .find(|(s, _)| (s.start, s.end) == (start, start + m.len()))
            .map(|(_, u)| u.clone())
    };
    assert!(
        matches!(member("p.twice"), Some(Ref::Bound(ids)) if r.binders[ids[0]].name == "twice")
    );
    assert_eq!(member("p.size"), None);
}

#[test]
fn a_binding_that_names_itself_resolves_to_itself() {
    // the cycle `x = x + 1` is reported by a later step; resolution ties the name to its binder
    assert_eq!(at("x = x + 1;", "x", 1), ["binding x = x + 1;"]);
}
