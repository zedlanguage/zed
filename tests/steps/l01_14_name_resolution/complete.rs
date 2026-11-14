//! The cases COMPLETENESS.md lists that the other files of this group leave out: each rule of
//! step L1.14 at each place a name can stand, with the scopes it meets.

use super::{at, errors, run};

/// The repairs of a binding that rebinds a name of its own scope, `first` being the first
/// binder's text and `again` the second's. A block may move the second binding into a nested
/// block; the unit's top level has no block around it, so it is offered the new name only.
fn rebound(name: &str, again: &str, first: &str, nested: bool) -> String {
    let mut s = format!(
        "`{name}` is already bound in this scope [{again}]; the first binding of `{name}` \
         [{first}]; repair: give this binding a new name [{again}]"
    );
    if nested {
        s += &format!(
            "; repair: move this binding into a nested block, where it shadows the first [{again}]"
        );
    }
    s
}

/// The error for a use of `name` that no scope binds.
fn undefined(name: &str) -> String {
    format!("`{name}` is not defined. [{name}]")
}

#[test]
fn each_prelude_word_of_l1_resolves_to_the_prelude_and_count_waits_for_l3() {
    // DESIGN.md L1.14: the prelude words of this step are `int`, `rat`, `f64`, `abs`, `len`,
    // `lower`, `upper`, `trim`, `sum`; `count` takes a family and enters at L3.
    let words = [
        "int", "rat", "f64", "abs", "len", "lower", "upper", "trim", "sum",
    ];
    for w in words {
        let text = format!("x = {w}(1);");
        assert_eq!(at(&text, w, 0), [format!("prelude {w}")], "{w}");
    }
    assert_eq!(
        errors("n = count(1);"),
        [concat!(
            zed_tests::not_yet!("the prelude word `count`"),
            " [count]"
        )]
    );
}

#[test]
fn a_prelude_word_is_shadowed_at_each_kind_of_binder() {
    // A binding, a parameter, a lambda's parameter and a block's binding each shadow the
    // prelude word within their scope, and outside it the word is the prelude's again.
    assert_eq!(at("f(len) = len + 1;", "len", 1), ["param len"]);
    assert_eq!(at("g = len -> len;", "len", 1), ["param len"]);
    let text = "x = { trim = 1; trim }; y = trim(\"a\");";
    assert_eq!(at(text, "trim", 1), ["binding trim = 1;"]);
    assert_eq!(at(text, "trim", 2), ["prelude trim"]);
}

#[test]
fn a_binder_may_not_name_a_type_at_any_kind_of_binder() {
    // DESIGN.md sec:diagnostics, row Binder naming a type, at a binding, a parameter and a
    // lambda's parameter.
    let message = |what: &str, ty: &str, binder: &str| {
        format!(
            "the {what} `{ty}` names the type `{ty}`, which the prelude declares: a binder may \
             not name a type in scope [{ty}]; the {what} `{ty}`, which binds `{ty}` in this \
             scope [{binder}]; repair: rename the binder; where a cast was meant, write the \
             type application `{ty}(…)` [{ty}]"
        )
    };
    assert_eq!(
        errors("int = 3;"),
        [message("binding target", "int", "int = 3;")]
    );
    assert_eq!(errors("f(int) = 1;"), [message("parameter", "int", "int")]);
    assert_eq!(
        errors("g = String -> 1;"),
        [message("parameter", "String", "String")]
    );
}

#[test]
fn rebinding_is_rejected_in_every_scope_with_the_repairs_that_scope_allows() {
    // The top level: no nested block to move into.
    assert_eq!(
        errors("x = 1; x = 2;"),
        [rebound("x", "x = 2;", "x = 1;", false)]
    );
    // A lambda's parameter and its body block share one scope (DESIGN.md L1.14).
    assert_eq!(
        errors("f(x) = { g = y -> { y = 1; y }; g(x) };"),
        [rebound("y", "y = 1;", "y", true)]
    );
    // Two parameters of one name.
    assert_eq!(
        errors("f(a: int, a: int) = a;"),
        [rebound("a", "a: int", "a: int", true)]
    );
    // A block binding a name twice, the first a binding.
    assert_eq!(
        errors("f(x) = { a = x; a = 2; a };"),
        [rebound("a", "a = 2;", "a = x;", true)]
    );
    // A destructuring target naming a parameter, and one naming a name twice.
    assert_eq!(
        errors("f(x) { a, x = (x, x); return a; }"),
        [rebound("x", "a, x = (x, x);", "x", true)]
    );
    assert_eq!(
        errors("a, a = (1, 2);"),
        [rebound("a", "a, a = (1, 2);", "a, a = (1, 2);", false)]
    );
    // An `else` pattern binding one field name twice.
    assert_eq!(
        errors("v = 1 else #e(n:, n:) -> n;"),
        [rebound("n", "#e(n:, n:)", "#e(n:, n:)", true)]
    );
    // `_` binds nothing, so it may stand any number of times.
    assert!(run("_ = 1; _ = 2;").is_ok());
}

#[test]
fn a_name_bound_in_an_inner_scope_is_not_seen_outside_it() {
    // A nested block, the branches of an `if`, a lambda's parameter and an `else` pattern
    // each bind for their own scope only.
    let cases = [
        ("f(x) { y = { z = x; z }; return z; }", "z"),
        ("y = if 1 < 2 { a = 1; a } else { a };", "a"),
        ("v = if true { a = 1; a } else { a = 2; a }; w = a;", "a"),
        ("f = x -> x; y = x;", "x"),
        (
            "v = parse(\"1\") else #e(pos:) -> pos; w = pos; parse(t) = t;",
            "pos",
        ),
        ("v = \"${y}\";", "y"),
    ];
    for (text, name) in cases {
        assert_eq!(errors(text), [undefined(name)], "{text}");
    }
    // Each branch of an `if` is its own block, so each binds `a` once.
    let text = "y = if 1 < 2 { a = 1; a } else { a = 2; a };";
    assert_eq!(at(text, "a", 1), ["binding a = 1;"]);
    assert_eq!(at(text, "a", 3), ["binding a = 2;"]);
    // An `else if` branch is a block of its own as well.
    let text = "v = if true { 1 } else if false { b = 2; b } else { 3 };";
    assert_eq!(at(text, "b", 1), ["binding b = 2;"]);
}

#[test]
fn an_inner_scope_sees_every_outer_scope_out_to_the_top_level() {
    // A lambda nested in a lambda reads both parameters and a top-level binding.
    let text = "k = 2; f = x -> y -> x + y + k;";
    assert_eq!(at(text, "x", 1), ["param x"]);
    assert_eq!(at(text, "y", 1), ["param y"]);
    assert_eq!(at(text, "k", 1), ["binding k = 2;"]);
    // A function declared in a block reads the enclosing function's parameter.
    let text = "f(x) = { h(y) = y + x; h };";
    assert_eq!(at(text, "x", 1), ["param x"]);
    assert_eq!(at(text, "h", 1), ["function h(y) = y + x;"]);
    // A parameter shadows a top-level binding of its name; another parameter does not.
    assert_eq!(at("x = 1; f(x) = x;", "x", 2), ["param x"]);
    assert_eq!(at("x = 1; f(y) = x;", "x", 1), ["binding x = 1;"]);
    // A function's body block may bind the function's own name, shadowing it.
    assert_eq!(at("f(x) = { f = 3; f };", "f", 2), ["binding f = 3;"]);
    assert_eq!(
        at("f(x) = { g = f; g };", "f", 1),
        ["function f(x) = { g = f; g };"]
    );
    // An `else` pattern's field shadows a top-level name in its default.
    let text = "n = 1; v = \"a\" else #e(n:) -> n;";
    assert_eq!(at(text, "n", 2), ["pattern #e(n:)"]);
    // A chain of `else`: each pattern binds for its own default.
    let text = "v = 1 else #e(n:) -> n else #f(n:) -> n;";
    assert_eq!(at(text, "n", 1), ["pattern #e(n:)"]);
    assert_eq!(at(text, "n", 3), ["pattern #f(n:)"]);
    // A default that is a block may bind the pattern's name again, in its nested scope.
    let text = "v = parse(\"1\") else #e(pos:) -> { pos = 2; pos }; parse(t) = t;";
    assert_eq!(at(text, "pos", 2), ["binding pos = 2;"]);
}

#[test]
fn names_resolve_in_every_expression_position() {
    // A tuple component, a destructured binding, an interpolation (nested too), a call's
    // callee in parentheses, a function passed as a value, and a parameter called.
    let text = "v = (1, 2); w = (v, v);";
    assert_eq!(at(text, "v", 2), ["binding v = (1, 2);"]);
    let text = "a, b = (1, 2); c = a + b;";
    assert_eq!(at(text, "b", 1), ["binding a, b = (1, 2);"]);
    assert_eq!(
        at("y = 1; v = \"${\"${y}\"}\";", "y", 1),
        ["binding y = 1;"]
    );
    assert_eq!(at("x = 1; s = \"v ${x}\";", "x", 1), ["binding x = 1;"]);
    // A callee in parentheses: the use recorded spans the parenthesized callee.
    let text = "f(x) = x; y = (f)(1);";
    let r = run(text).unwrap();
    let callee = r
        .uses
        .iter()
        .find(|(s, _)| text[s.start..s.end].contains('f') && s.start > 9)
        .expect("the callee `(f)` is a use");
    assert!(
        matches!(&callee.1, zedc::resolve::Ref::Bound(ids) if r.binders[ids[0]].name == "f"),
        "{:?}",
        callee.1
    );
    assert_eq!(at("f(x) = x; g = f;", "f", 1), ["function f(x) = x;"]);
    assert_eq!(at("f(x) = x; g(f) = f(1);", "f", 2), ["param f"]);
    // A lambda's parameter with a default.
    assert_eq!(at("f = (x = 1) -> x;", "x", 1), ["param x = 1"]);
    // The name of a named argument is the parameter's, not a use: no `x` is in scope here.
    assert_eq!(at("f(x) = x; y = f(x: 1);", "f", 1), ["function f(x) = x;"]);
    // Atoms name nothing.
    assert!(run("x = #a; y = #a(1);").unwrap().uses.is_empty());
}

#[test]
fn a_member_is_a_candidate_uniform_call_in_each_form() {
    // `x.f`, `x.f(a)`, `x?.f` and a chain `x.f.f` each record `f` for elaboration (DESIGN.md
    // L1.14); a member named like no function in scope records nothing.
    for text in [
        "f(x) = x; g(x) = x.f;",
        "f(x) = x; g(x) = x.f(1);",
        "f(x) = x; v = 1?.f;",
        "f(x) = x; v = 1.f.f;",
    ] {
        let r = run(text).unwrap();
        let members = r
            .uses
            .iter()
            .filter(|(s, _)| text[s.start..s.end].ends_with(".f"))
            .count();
        assert!(members >= 1, "{text}");
        for (s, u) in &r.uses {
            if text[s.start..s.end].ends_with(".f") {
                assert!(
                    matches!(u, zedc::resolve::Ref::Bound(ids) if r.binders[ids[0]].name == "f"),
                    "{text}"
                );
            }
        }
    }
    let r = run("s = \"x\"; v = s?.upper; w = s.len;").unwrap();
    assert!(
        r.uses
            .iter()
            .all(|(s, _)| !"s = \"x\"; v = s?.upper; w = s.len;"[s.start..s.end].contains('.')),
    );
}

#[test]
fn functions_in_a_block_overload_resolve_and_are_checked_like_bindings() {
    // A block's functions of one name with different parameter types form one set.
    let text = "f(x) { g(y: int) = y; g(y: String) = y; return g(x); }";
    assert_eq!(
        at(text, "g", 2),
        ["function g(y: int) = y;", "function g(y: String) = y;"]
    );
    // The same parameter types twice is rebinding.
    assert_eq!(
        errors("f(x) { g(y) = y; g(y) = y; return g(x); }"),
        [
            "`g` is already declared in this scope with these parameter types [g(y) = y;]; the \
             first `g` with these parameter types [g(y) = y;]; repair: give this binding a new \
             name [g(y) = y;]; repair: move this binding into a nested block, where it shadows \
             the first [g(y) = y;]"
        ]
    );
    // A block's function is used below its definition only.
    assert_eq!(
        errors("f() { return g(1); g(y) = y; }"),
        [
            "`g` is used above its definition [g]; in a block a name is used only below its \
             definition, so that the text reads from the top; the order of the lines changes \
             no result, since evaluation follows the dependencies, so moving the definition \
             above its first use changes nothing else [g]; `g` is used here, above its \
             definition [g]; the definition of `g`, below its first use [g(y) = y;]; repair: \
             move the definition of `g` above the statement that first uses `g` [g(y) = y;]"
        ]
    );
}

#[test]
fn two_block_definitions_that_name_each_other_are_offered_the_top_level_only_when_they_can_move() {
    let above = "`h` is used above its definition [h]; in a block a name is used only below its \
                 definition, so that the text reads from the top; the order of the lines \
                 changes no result, since evaluation follows the dependencies, so moving the \
                 definition above its first use changes nothing else [h]; `h` is used here, \
                 above its definition [h]";
    let top = "; repair: `g` and `h` call each other, so define both at the top level of the \
               unit, where definitions may name each other in any order";
    // Two functions, and two lambdas, that call each other and read nothing of the block.
    assert_eq!(
        errors("f(n) {\n  g(x) = h(x);\n  h(x) = g(x);\n  g(n)\n}"),
        [format!(
            "{above}; the definition of `h`, below its first use [h(x) = g(x);]{top} \
             [h(x) = g(x);]"
        )]
    );
    assert_eq!(
        errors("f(n) {\n  g = x -> h(x);\n  h = x -> g(x);\n  g(n)\n}"),
        [format!(
            "{above}; the definition of `h`, below its first use [h = x -> g(x);]{top} \
             [h = x -> g(x);]"
        )]
    );
    // One of them reads the parameter `n`, which the top level does not see: no move is
    // offered.
    assert_eq!(
        errors("f(n) {\n  g(x) = h(x) + n;\n  h(x) = g(x);\n  g(n)\n}"),
        [format!(
            "{above}; the definition of `h`, below its first use [h(x) = g(x);]"
        )]
    );
}

#[test]
fn test_cases_see_the_scope_around_the_function_and_not_inside_it() {
    // The keys and expected values of a `test` table are read outside the function: neither
    // a parameter nor a function declared in its body is in scope there.
    assert_eq!(
        errors("g(x) = { h(y) = y; h(1) } test { 1 -> h(1) }"),
        [undefined("h")]
    );
    assert_eq!(errors("f(x) = x test { y -> 1 }"), [undefined("y")]);
    // A block-bodied function's table, and a table of a function with a default.
    assert!(run("f(x) { return x; } test { 1 -> 1 }").is_ok());
    assert_eq!(
        at("f(x, y = x) = y test { (1, 2) -> 2 }", "x", 1),
        ["param x"]
    );
}

#[test]
fn a_parameter_default_naming_its_own_parameter_resolves_to_it() {
    // Like a binding that names itself, the default is tied to its own parameter, and step
    // L1.16 reports the cycle.
    assert_eq!(at("f(a: int = a) = a;", "a", 1), ["param a: int = a"]);
}

#[test]
fn a_type_in_each_type_form_resolves_to_the_prelude() {
    // A tuple, a union, an arrow and an atom in a union: each name in them is a prelude
    // type, and an unknown one is an error wherever it stands.
    for (text, ty, n) in [
        ("f(x: (int, int)) = x;", "int", 1),
        ("f(x: int | String) = x;", "String", 0),
        ("f(x: int -> int) = x;", "int", 1),
        ("f(x: #a | int) = x;", "int", 0),
    ] {
        assert_eq!(at(text, ty, n), [format!("prelude {ty}")], "{text}");
    }
    assert_eq!(
        errors("f(x: Foo -> int) = x;"),
        ["The type `Foo` is not defined. [Foo]"]
    );
}

#[test]
fn main_is_in_scope_but_neither_a_value_nor_called() {
    // QUESTIONS A68: `main` is in scope and runs once, when the program starts; no function
    // calls it.
    assert_eq!(errors("z = main;"), [undefined("main")]);
    let main = "main(m: MainArgs) { m.stdout <- \"a\"; } ";
    assert_eq!(
        errors(&format!("{main}x = main;")),
        [
            "`main` used as a value: no function calls `main`, which runs once, when the program \
             starts. [main]; repair: read `main::args` or `main::files` for what `main` reads \
             [main]; repair: in place of `main`, use a function that `main` and this code both \
             call [main]"
        ]
    );
    assert_eq!(
        errors(&format!("{main}x = main(1);")),
        [
            "Call of `main`: no function calls `main`, which runs once, when the program starts. \
             [main(1)]; repair: read `main::args` for the argument `main` takes [main(1)]; \
             repair: move the code the call wants into a function that `main` and the caller \
             both call [main(1)]"
        ]
    );
    assert!(run("main() { }").is_ok());
    assert_eq!(
        errors("main(m: MainArgs) { } main(m: MainArgs) { }"),
        [
            "`main` is already declared in this scope with these parameter types \
             [main(m: MainArgs) { }]; the first `main` with these parameter types \
             [main(m: MainArgs) { }]; repair: give this binding a new name [main(m: MainArgs) { }]"
        ]
    );
}

#[test]
fn each_form_of_a_later_step_is_named_as_not_yet_compiled() {
    let cases: [(&str, String); 11] = [
        (
            "f(x) { while x < 3; }",
            zed_tests::not_yet("a `while` guard") + " [while x < 3;]",
        ),
        (
            "f(x) { until x < 3; }",
            zed_tests::not_yet("an `until` guard") + " [until x < 3;]",
        ),
        (
            "f(x) { x + 1; }",
            zed_tests::not_yet("an expression statement") + " [x + 1;]",
        ),
        (
            "a[i] = i;",
            zed_tests::not_yet("an indexed definition") + " [a[i] = i;]",
        ),
        (
            "struct P { a: int }",
            zed_tests::not_yet("a struct declaration") + " [struct P { a: int }]",
        ),
        (
            "type T = int;",
            zed_tests::not_yet("a type declaration") + " [type T = int;]",
        ),
        (
            "local x = 1;",
            zed_tests::not_yet("a `local` declaration") + " [local x = 1;]",
        ),
        (
            "x = y';",
            zed_tests::not_yet("the primed name `y'`") + " [y']",
        ),
        (
            "f(x) = { x -> x };",
            zed_tests::not_yet("a map display") + " [{ x -> x }]",
        ),
        (
            "x = [1, 2]; y = x[0];",
            zed_tests::not_yet("an array display") + " [[1, 2]]",
        ),
        (
            "x = { 1, 2 };",
            zed_tests::not_yet("a set display") + " [{ 1, 2 }]",
        ),
    ];
    for (text, want) in cases {
        assert_eq!(errors(text), [want], "{text}");
    }
    // `local` in a block is misplaced as well as not yet compiled.
    assert_eq!(
        errors("f(x) { local y = 1; return y; }"),
        [
            "`local` keeps a declaration from other units, and a declaration in a block is seen \
             by no other unit already, so `local` stands only at a unit's top level or in a \
             loop body. Remove the `local`. [local y = 1;]"
                .to_string(),
            zed_tests::not_yet("a `local` declaration") + " [local y = 1;]",
        ]
    );
}
