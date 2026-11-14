//! An undeclared parameter's type holds the atoms its uses handle: every loose atom where the
//! body writes `line else d`, the atom `#a` where it writes `line is #a` or
//! `line else #a -> d`. A call passing one of them then runs the body, which handles it, where
//! before the atom passed the call by (rule 6) and the body's `else` never ran. The atoms are
//! checked by subtyping, not by their printed text.

use zed_kernel::types::Type as KType;
use zedc::check::read::parse_type;
use zedc::check::ty::{Arrow, Carrier, Ty, atoms};

use super::{info, sig, type_errors};
use zed_tests::step_helpers::l01_16_elaboration::value;

/// The one arrow of `r(positional line) = body;`, which checks without error.
fn arrow(body: &str) -> Arrow {
    let text = format!("r(positional line) = {body};\n");
    assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    let (info, names) = info(&text);
    let (_, s) = info.sigs.iter().find(|(id, _)| names[**id] == "r").unwrap();
    let mut arrows = s.expand();
    assert_eq!(arrows.len(), 1, "{text}: {s}");
    arrows.remove(0)
}

fn same(a: &Ty, b: &Ty) -> bool {
    a.subtype(b) && b.subtype(a)
}

fn string() -> Ty {
    Ty::carrier(Carrier::Str)
}

fn loose() -> Ty {
    Ty::set(atoms())
}

fn atom(name: &str) -> Ty {
    Ty::set(KType::atom(name))
}

#[test]
fn trimming_a_line_or_the_empty_string_takes_every_loose_atom() {
    // The issue's repro: `stdin[9]` is `#notFound` on a short input.
    let a = arrow("trim(line else \"\")");
    assert!(
        same(&a.params[0], &string().union(&loose())),
        "{}",
        a.params[0]
    );
    assert!(same(&a.result, &string()), "{}", a.result);
}

#[test]
fn upper_casing_a_line_or_the_empty_string_takes_every_loose_atom() {
    let a = arrow("upper(line else \"\")");
    assert!(
        same(&a.params[0], &string().union(&loose())),
        "{}",
        a.params[0]
    );
    assert!(same(&a.result, &string()), "{}", a.result);
}

#[test]
fn a_count_or_zero_plus_one_takes_every_loose_atom_and_gives_an_int() {
    // The atoms the `else` replaces do not reach the sum.
    let a = arrow("(line else 0) + 1");
    let int = Ty::carrier(Carrier::Int);
    assert!(same(&a.params[0], &int.union(&loose())), "{}", a.params[0]);
    assert!(same(&a.result, &int), "{}", a.result);
}

#[test]
fn a_line_named_in_a_block_before_it_is_trimmed_is_the_same() {
    let a = arrow("{ s = line else \"\"; trim(s) }");
    assert!(
        same(&a.params[0], &string().union(&loose())),
        "{}",
        a.params[0]
    );
    assert!(same(&a.result, &string()), "{}", a.result);
}

#[test]
fn an_else_on_the_branch_after_an_is_test_takes_every_loose_atom() {
    // The `else` handles every loose atom, `#notFound` among them, so the parameter takes
    // them all, and `#absent` is reachable.
    let a = arrow("if line is #notFound { #absent } else { trim(line else \"\") }");
    assert!(
        same(&a.params[0], &string().union(&loose())),
        "{}",
        a.params[0]
    );
    assert!(
        same(&a.result, &string().union(&atom("absent"))),
        "{}",
        a.result
    );
}

#[test]
fn an_is_test_alone_takes_only_its_atom() {
    let a = arrow("if line is #notFound { \"\" } else { trim(line) }");
    assert!(
        same(&a.params[0], &string().union(&atom("notFound"))),
        "{}",
        a.params[0]
    );
    assert!(same(&a.result, &string()), "{}", a.result);
}

#[test]
fn an_else_on_one_atom_takes_that_atom_with_any_payload() {
    let a = arrow("trim(line else #notFound -> \"\")");
    let any = Ty::set(KType::atom_with("notFound", &KType::top()));
    let want = string().union(&atom("notFound")).union(&any);
    assert!(same(&a.params[0], &want), "{}", a.params[0]);
    assert!(!a.params[0].subtype(&string().union(&atom("notFound"))));
}

#[test]
fn a_parameter_of_any_value_stays_a_type_variable() {
    // Its type already holds every atom.
    for body in [
        "if line is #notFound { #absent } else { \"s\" }",
        "if line is #notFound { #absent } else { line else \"\" }",
        "line else \"\"",
    ] {
        let a = arrow(body);
        assert!(a.params[0].as_var().is_some(), "{body}: {}", a.params[0]);
    }
    let text = "r(positional line) = line else \"\";\n";
    assert_eq!(sig(text, "r"), "T -> \"\" | T");
}

#[test]
fn a_line_trimmed_without_else_takes_no_atom() {
    // An atom passed to it passes the call by, as rule 6 says.
    let a = arrow("trim(line)");
    assert!(same(&a.params[0], &string()), "{}", a.params[0]);
    let text = "r(positional line) = trim(line);\ny = r(#notFound);\n";
    assert_eq!(value(text, "y"), "#notFound");
}

#[test]
fn a_declared_parameter_keeps_its_declared_type() {
    let text = "r(positional line: String | #notFound) = trim(line else \"\");\n";
    assert_eq!(sig(text, "r"), "String | #notFound -> String");
}

#[test]
fn a_bounded_variable_takes_the_atoms_beside_it() {
    // `a else b` and `+ b` bound `a` and `b` to one number carrier; `a` also takes the atoms
    // the `else` replaces with `b`.
    let text = "add(positional a, positional b) = (a else b) + b;\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    let (info, _) = info(text);
    let s = info.sigs.values().next().unwrap();
    // One arrow for each of int, f32, f64 and rat.
    let arrows = s.expand();
    assert_eq!(arrows.len(), 4, "{s}");
    for a in &arrows {
        let c = Ty::carrier(a.result.pieces()[0].carrier().expect("a carrier"));
        assert!(same(&a.params[0], &c.union(&loose())), "{}", a.params[0]);
        assert!(same(&a.params[1], &c), "{}", a.params[1]);
    }
    for (call, want) in [("add(#notFound, 2)", "4"), ("add(1.5f64, 2.0f64)", "3.5")] {
        let p = format!("{text}y = {call};\n");
        assert_eq!(value(&p, "y"), want, "{call}");
    }
}

#[test]
fn a_count_or_zero_plus_a_named_step_takes_the_step_s_carrier() {
    // The `else` gives `0 | T`; the sum binds `T` to the step's carrier as `line + bump`
    // would, so a string line is refused where it is passed, not at run time.
    let text = "r(positional line, bump = 1) = (line else 0) + bump;\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "r"), "(int | #_, bump: int) -> int");
    for (call, want) in [("r(2)", "3"), ("r(#notFound)", "1"), ("r(2, bump: 5)", "7")] {
        let p = format!("{text}y = {call};\n");
        assert_eq!(value(&p, "y"), want, "{call}");
    }
    let e = type_errors(&format!("{text}y = r(\" a \");\n"));
    assert_eq!(e.len(), 1, "{e:?}");
    assert!(e[0].contains("does not take"), "{e:?}");
}

#[test]
fn a_count_or_zero_plus_another_parameter_shares_its_carrier() {
    // Both parameters undeclared: the plain literal `0` is an int, which both take.
    let text = "r(positional line, positional step) = (line else 0) + step;\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "r"), "(int | #_, int) -> int");
    for (call, want) in [("r(2, 3)", "5"), ("r(#notFound, 4)", "4")] {
        let p = format!("{text}y = {call};\n");
        assert_eq!(value(&p, "y"), want, "{call}");
    }
    let e = type_errors(&format!("{text}y = r(\" a \", 1);\n"));
    assert_eq!(e.len(), 1, "{e:?}");
}

#[test]
fn a_function_that_calls_itself_waits_for_layer_l6() {
    let text =
        "r(positional line) = if line is #again { r(\"x\") } else { trim(line else \"\") };\n";
    let (info, _) = info(text);
    assert!(info.sigs.is_empty());
    let e = zed_tests::step_helpers::l01_16_elaboration::errors(&format!("{text}y = r(#again);\n"));
    assert!(
        e[0].contains("which is recursion: this version of zedc does not compile it yet"),
        "{e:?}"
    );
}

#[test]
fn a_line_bound_to_another_name_takes_the_atoms_that_name_handles() {
    // `s` is `line` under another name, so `s else ""` handles every loose atom for `line`,
    // and through a chain of names.
    for body in [
        "{ s = line; trim(s else \"\") }",
        "{ s = line; t = s; trim(t else \"\") }",
    ] {
        let a = arrow(body);
        assert!(
            same(&a.params[0], &string().union(&loose())),
            "{body}: {}",
            a.params[0]
        );
        assert!(same(&a.result, &string()), "{body}: {}", a.result);
    }
    let a = arrow("{ s = line; if s is #notFound { \"\" } else { trim(s) } }");
    assert!(
        same(&a.params[0], &string().union(&atom("notFound"))),
        "{}",
        a.params[0]
    );
}

#[test]
fn a_name_bound_to_a_computed_value_takes_what_its_handler_handles() {
    // Inference runs after bubbling (the author's Q5, 2026-11-07): an atom passed as `line`
    // passes out of `trim(line)` into `s` by rule 6, and `s else ""` handles it, so `line`
    // takes every loose atom, as `line: String | #_` would.
    let a = arrow("{ s = trim(line); s else \"\" }");
    assert!(
        same(&a.params[0], &string().union(&loose())),
        "{}",
        a.params[0]
    );
    assert!(same(&a.result, &string()), "{}", a.result);
}

#[test]
fn a_binding_passes_atoms_from_its_name_to_its_value_and_not_back() {
    // `s = a + b` passes what `s`'s uses handle to `a` and `b`; `a else 0` handles atoms of
    // `a` alone, so `b` takes none of them.
    let text = "r(positional a, positional b) = { s = a + b; s else 0 };\n";
    assert_eq!(
        sig(text, "r"),
        "(T | #_, T | #_) -> 0 | T for T in int | f32 | f64 | rat"
    );
    let text = "r(positional a, positional b) = { s = a + b; (a else 0) + s };\n";
    assert_eq!(
        sig(text, "r"),
        "type T1 = int | #_;\n((int, int) -> int) & ((T1, int) -> T1)"
    );
}

#[test]
fn a_handler_on_a_computed_value_prints_its_atoms_on_the_parameter_only() {
    // The atoms that pass by rule 6 out of a call, an operator, a method or a string hole
    // on the parameter reach the handler, which removes them: the parameter takes them and
    // the result has none. A bare `else` takes every loose atom; `else #nf ->`, `is #nf`,
    // `== #nf` and `!= #nf` take `#nf`.
    for (body, want) in [
        ("trim(line) else \"dflt\"", "String | #_ -> String"),
        (
            "trim(line) else #nf -> \"dflt\"",
            "String | #nf | #nf(..) -> String",
        ),
        (
            "(line + 1) else 0",
            "T | #_ -> 0 | T for T in int | f32 | f64 | rat",
        ),
        ("line?.trim() else \"dflt\"", "String | #_ -> String"),
        (
            "\"${line + 1}\" else \"dflt\"",
            "T | #_ -> String for T in int | f32 | f64 | rat",
        ),
        (
            "if trim(line) is #nf { \"dflt\" } else { \"s\" }",
            "String | #nf -> \"dflt\" | \"s\"",
        ),
        (
            "if trim(line) == #nf { \"dflt\" } else { \"s\" }",
            "String | #nf -> \"dflt\" | \"s\"",
        ),
        (
            "if #nf != trim(line) { \"s\" } else { \"dflt\" }",
            "String | #nf -> \"dflt\" | \"s\"",
        ),
        (
            "(trim(line) else #nf -> \"dflt\") else \"other\"",
            "String | #_ -> String",
        ),
    ] {
        let text = format!("r(positional line) = {body};\n");
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        let printed = sig(&text, "r");
        assert_eq!(printed, want, "{body}");
        let t = parse_type(&printed).unwrap_or_else(|e| panic!("{printed}: {e}"));
        assert_eq!(t.fns[0].to_string(), printed, "{body}");
    }
    // Through a helper: `h(x)` passes the atom by just as `trim(x)` does.
    let text = "h(positional y) = trim(y);\nr(positional line) = h(line) else \"dflt\";\n";
    assert_eq!(sig(text, "r"), "String | #_ -> String");
    assert_eq!(sig(text, "h"), "String -> String");
}

#[test]
fn an_inferred_parameter_and_its_declared_twin_give_the_same_value_at_each_call() {
    // Each handler form, with `f` undeclared and `g` declared with the type `f`'s parameter
    // should infer: every call gives the same value from both (the author's Q5:
    // `f(positional x) = trim(x) else "dflt"` gives `f(#nf) == "dflt"`, as `g(x: String |
    // #nf)` does). Before inference ran after bubbling, `f(#nf)` passed `#nf` by. An atom the
    // handler does not take, `#other`, passes the call by from both.
    let helper = "h(positional y) = trim(y);\n";
    let (any, nf) = ("String | #_", "String | #nf");
    for (body, declared, calls) in [
        (
            "trim(x) else \"dflt\"",
            any,
            [
                ("\" a \"", "\"a\""),
                ("#nf", "\"dflt\""),
                ("#other", "\"dflt\""),
            ],
        ),
        (
            "trim(x) else #nf -> \"dflt\"",
            nf,
            [
                ("\" a \"", "\"a\""),
                ("#nf", "\"dflt\""),
                ("#other", "#other"),
            ],
        ),
        (
            "if trim(x) is #nf { \"dflt\" } else { \"s\" }",
            nf,
            [
                ("\" a \"", "\"s\""),
                ("#nf", "\"dflt\""),
                ("#other", "#other"),
            ],
        ),
        (
            "if x == #nf { \"dflt\" } else { trim(x) }",
            nf,
            [
                ("\" a \"", "\"a\""),
                ("#nf", "\"dflt\""),
                ("#other", "#other"),
            ],
        ),
        (
            "if #nf == trim(x) { \"dflt\" } else { \"s\" }",
            nf,
            [
                ("\" a \"", "\"s\""),
                ("#nf", "\"dflt\""),
                ("#other", "#other"),
            ],
        ),
        (
            "if x != #nf { trim(x) } else { \"dflt\" }",
            nf,
            [
                ("\" a \"", "\"a\""),
                ("#nf", "\"dflt\""),
                ("#other", "#other"),
            ],
        ),
        (
            "h(x) else \"dflt\"",
            any,
            [
                ("\" a \"", "\"a\""),
                ("#nf", "\"dflt\""),
                ("#other", "\"dflt\""),
            ],
        ),
        (
            "{ s = trim(x); s else \"dflt\" }",
            any,
            [
                ("\" a \"", "\"a\""),
                ("#nf", "\"dflt\""),
                ("#other", "\"dflt\""),
            ],
        ),
    ] {
        let text =
            format!("{helper}f(positional x) = {body};\ng(positional x: {declared}) = {body};\n");
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        for (arg, want) in calls {
            let p = format!("{text}a = f({arg});\nb = g({arg});\n");
            assert_eq!(value(&p, "b"), want, "declared: {body} at {arg}");
            assert_eq!(value(&p, "a"), want, "inferred: {body} at {arg}");
        }
    }
}

#[test]
fn an_argument_whose_atoms_a_parameter_takes_in_part_passes_the_rest_by() {
    // Findings F17 and F27: rule 6 treats each loose atom apart, so the parameter takes `#a`
    // and `#b` passes the call by.
    let text = "f(positional x: int | #a) = if x is #a { 0 } else { x + 1 };\n\
                src(positional n: int) = if n == 0 { #a } else if n == 1 { #b } else { n };\n\
                g(positional n: int) = f(src(n));\n";
    for (n, want) in [("0", "0"), ("1", "#b"), ("5", "6")] {
        let p = format!("{text}y = g({n});\n");
        assert_eq!(value(&p, "y"), want, "F17 at {n}");
    }
    let text = "g(positional x: int | #a) = x else 0;\n\
                f(positional y: int | #a | #b) = g(y);\n";
    for (y, want) in [("#a", "0"), ("#b", "#b"), ("5", "5")] {
        let p = format!("{text}v = f({y});\n");
        assert_eq!(value(&p, "v"), want, "F27 at {y}");
    }
}

#[test]
fn a_generic_call_whose_arguments_are_atoms_only_passes_them_by() {
    // Finding F18: every value of both arguments of `add` at its variable `T` passes by, so
    // the call never takes place, and the `else` around it handles the atoms.
    let text = "add(positional x, positional y) = x + y;\n\
                w(positional n: int) = if n == 0 { #a } else { #b };\n\
                g(positional n: int) = add(w(n), w(n + 1)) else -1;\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    for n in ["0", "1"] {
        assert_eq!(value(&format!("{text}y = g({n});\n"), "y"), "-1", "at {n}");
    }
}

#[test]
fn each_row_of_the_issue_prints_as_a_type_the_user_can_write() {
    // The rows of the table in zedlanguage/zed issue 1, and the forms beside them. Every atom
    // is `#_`, an atom with any payload `#a(..)`; each printed signature reads back as the
    // same type.
    for (body, want) in [
        (
            "if line is #notFound { #absent } else { \"s\" }",
            "_ -> \"s\" | #absent",
        ),
        (
            "if line is #notFound { #absent } else { line else \"\" }",
            "T -> \"\" | T | #absent",
        ),
        (
            "if line is #notFound { #absent } else { trim(line else \"\") }",
            "String | #_ -> String | #absent",
        ),
        ("trim(line else \"\")", "String | #_ -> String"),
        ("line else \"\"", "T -> \"\" | T"),
        ("upper(line else \"\")", "String | #_ -> String"),
        ("(line else 0) + 1", "int | #_ -> int"),
        ("{ s = line else \"\"; trim(s) }", "String | #_ -> String"),
        ("{ s = line; trim(s else \"\") }", "String | #_ -> String"),
        (
            "if line is #notFound { \"\" } else { trim(line) }",
            "String | #notFound -> String",
        ),
        (
            "if line is #a | #b { \"\" } else { trim(line) }",
            "String | #a | #b -> String",
        ),
        (
            "trim(line else #notFound -> \"\")",
            "String | #notFound | #notFound(..) -> String",
        ),
        ("trim(line)", "String -> String"),
    ] {
        let text = format!("r(positional line) = {body};\n");
        let printed = sig(&text, "r");
        assert_eq!(printed, want, "{body}");
        let t = parse_type(&printed).unwrap_or_else(|e| panic!("{printed}: {e}"));
        assert_eq!(t.fns.len(), 1, "{printed}");
        assert_eq!(t.fns[0].to_string(), printed, "{body}");
    }
    let text = "add(positional a, positional b) = (a else b) + b;\n";
    assert_eq!(
        sig(text, "add"),
        "(T | #_, T) -> T for T in int | f32 | f64 | rat"
    );
    let text = "r(positional line: String | #notFound) = trim(line else \"\");\n";
    assert_eq!(sig(text, "r"), "String | #notFound -> String");
}

#[test]
fn a_function_whose_handled_atoms_also_reach_its_result_has_two_arrows() {
    // The body handles every loose atom of its parameter and passes the same atoms by to its
    // result: the first arrow, for an argument with no atom, gives none; the second takes them.
    // Each printed signature reads back as the same two arrows.
    for (head, body, want) in [
        (
            "r(positional line)",
            "if (line else \"\") == \"\" { \"empty\" } else { trim(line) }",
            "type T1 = String | #_;\n(String -> String) & (T1 -> T1)",
        ),
        (
            "r(positional c)",
            "{ d = c else false; if c { \"yes\" } else { \"no\" } }",
            "(bool -> \"no\" | \"yes\") & (bool | #_ -> \"no\" | \"yes\" | #_)",
        ),
        (
            "r(positional n)",
            "{ d = n else 0; if n > 3 { \"big\" } else { \"small\" } }",
            "(T -> \"big\" | \"small\") & (T | #_ -> \"big\" | \"small\" | #_) \
             for T in int | f32 | f64 | rat",
        ),
    ] {
        let text = format!("{head} = {body};\n");
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        let printed = sig(&text, "r");
        assert_eq!(printed, want, "{body}");
        let t = parse_type(&printed).unwrap_or_else(|e| panic!("{printed}: {e}"));
        assert_eq!(t.fns.len(), 1, "{printed}");
        assert_eq!(t.fns[0].arrows.len(), 2, "{printed} read as {t}");
        assert_eq!(t.fns[0].to_string(), printed, "{body}");
    }
}

#[test]
fn an_atom_from_elsewhere_stays_on_the_first_arrow() {
    // `#absent` is the body's own, not the parameter's, so the first arrow gives it too; the
    // atoms `trim` passes by are the parameter's, and only the second gives them.
    let text =
        "r(positional line) = if (line else \"\") == \"\" { #absent } else { trim(line) };\n";
    assert_eq!(
        sig(text, "r"),
        "type T1 = String | #_;\n(String -> String | #absent) & (T1 -> T1)"
    );
}

#[test]
fn an_equality_with_an_atom_narrows_the_name_in_each_branch() {
    // `x == #nf` leaves `x` without `#nf` where it fails, and `x != #nf` where it holds, as
    // `x is #nf` does (DESIGN.md sec:type_resolution: "`p is #a`, `p == #a` and `p != #a` add
    // `#a`"). Before, neither narrowed, so `trim(x)` in the other branch passed `#nf` by and
    // each result printed `String | #nf` (CLASS-atoms-followups, part c).
    for (head, body, want) in [
        (
            "f(positional x: String | #nf)",
            "if x == #nf { \"dflt\" } else { trim(x) }",
            "String | #nf -> String",
        ),
        (
            "f(positional x: String | #nf)",
            "if #nf == x { \"dflt\" } else { trim(x) }",
            "String | #nf -> String",
        ),
        (
            "f(positional x: String | #nf)",
            "if x != #nf { trim(x) } else { \"dflt\" }",
            "String | #nf -> String",
        ),
        (
            "f(positional x)",
            "if x == #nf { \"dflt\" } else { trim(x) }",
            "String | #nf -> String",
        ),
        (
            "f(positional x)",
            "if x != #nf { trim(x) } else { \"dflt\" }",
            "String | #nf -> String",
        ),
        (
            "f(positional x: String | #nf)",
            "if x == #nf { x } else { \"s\" }",
            "String | #nf -> \"s\" | #nf",
        ),
    ] {
        let text = format!("{head} = {body};\n");
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
        assert_eq!(sig(&text, "f"), want, "{text}");
    }
}

#[test]
fn an_equality_with_a_number_compares_an_atom_as_data() {
    // `x == 3` compares `x` with a literal without a suffix, which takes the carrier of `x`
    // and fixes none (steps L1.26a, L1.26b), so `x` stays `_`. `==` compares an atom as data
    // (DESIGN.md sec:type_resolution, A15: "a comparison with an atom or a failure ... stays
    // legal"), so `f(#nf)` runs the body and gives "other". Before bare literals were
    // generic, `3` narrowed `x` to `int` and `f(#nf)` passed `#nf` by (part d).
    let text = "f(positional x) = if x == 3 { \"three\" } else { \"other\" };\n";
    assert_eq!(sig(text, "f"), "_ -> \"other\" | \"three\"");
    assert_eq!(value(&format!("{text}a = f(#nf);\n"), "a"), "\"other\"");
    assert_eq!(value(&format!("{text}a = f(3);\n"), "a"), "\"three\"");
}

#[test]
fn passing_the_parameter_to_a_function_that_handles_its_atoms_handles_none() {
    // `f(positional x) = g(x)` writes no `else`, `is`, `==` or `!=`, so `x` takes no atom
    // (DESIGN.md sec:type_resolution: the atoms a parameter accepts are those that reach a
    // handler "in the body"), and `f(#nf)` passes `#nf` by although `g` takes it; the
    // declared twin `f(x: String)` does the same (part b).
    let text = "g(positional y: String | #nf) = trim(y else \"dflt\");\n\
                f(positional x) = g(x);\n\
                l(positional x) = ((y: String | #nf) -> trim(y else \"dflt\"))(x);\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    assert_eq!(sig(text, "f"), "String -> String");
    for (call, want) in [("g(#nf)", "\"dflt\""), ("f(#nf)", "#nf"), ("l(#nf)", "#nf")] {
        assert_eq!(value(&format!("{text}a = {call};\n"), "a"), want, "{call}");
    }
}
