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
    assert_eq!(sig(text, "r"), "(_) -> \"\" | _");
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
    assert_eq!(sig(text, "r"), "(String | #notFound) -> String");
}

#[test]
fn a_bounded_variable_takes_the_atoms_beside_it() {
    // `a else b` and `+ b` bound `a` and `b` to one number carrier; `a` also takes the atoms
    // the `else` replaces with `b`.
    let text = "add(positional a, positional b) = (a else b) + b;\n";
    assert_eq!(type_errors(text), Vec::<String>::new());
    let (info, _) = info(text);
    let s = info.sigs.values().next().unwrap();
    // One arrow for each of int, f64 and rat.
    let arrows = s.expand();
    assert_eq!(arrows.len(), 3, "{s}");
    for a in &arrows {
        let c = Ty::carrier(a.result.pieces()[0].carrier().expect("a carrier"));
        assert!(same(&a.params[0], &c.union(&loose())), "{}", a.params[0]);
        assert!(same(&a.params[1], &c), "{}", a.params[1]);
    }
    for (call, want) in [("add(#notFound, 2)", "4"), ("add(1.5, 2.0)", "3.5")] {
        let p = format!("{text}y = {call};\n");
        assert_eq!(value(&p, "y"), want, "{call}");
    }
}

#[test]
fn a_function_that_calls_itself_waits_for_layer_l6() {
    let text =
        "r(positional line) = if line is #again { r(\"x\") } else { trim(line else \"\") };\n";
    let (info, _) = info(text);
    assert!(info.sigs.is_empty());
    let e = zed_tests::step_helpers::l01_16_elaboration::errors(&format!("{text}y = r(#again);\n"));
    assert!(e[0].contains("recursion arrives at layer L6"), "{e:?}");
}

#[test]
fn a_line_bound_to_another_name_takes_the_atoms_that_name_handles() {
    // `s` is `line` under another name, so `s else ""` handles every loose atom for `line`,
    // in whichever order the block writes its bindings, and through a chain of names.
    for body in [
        "{ s = line; trim(s else \"\") }",
        "{ t = s; s = line; trim(t else \"\") }",
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
fn a_name_bound_to_a_computed_value_handles_nothing_for_the_line() {
    // `s` is `trim(line)`, not `line`: the `else` handles the atoms of the trimmed value, and
    // `line` takes no atom, so an atom passed to `r` passes the call by (rule 6).
    let a = arrow("{ s = trim(line); s else \"\" }");
    assert!(same(&a.params[0], &string()), "{}", a.params[0]);
}

#[test]
fn each_row_of_the_issue_prints_as_a_type_the_user_can_write() {
    // The rows of the table in zedlanguage/zed issue 1, and the forms beside them. Every atom
    // is `#_`, an atom with any payload `#a(..)`; each printed signature reads back as the
    // same type.
    for (body, want) in [
        (
            "if line is #notFound { #absent } else { \"s\" }",
            "(_) -> \"s\" | #absent",
        ),
        (
            "if line is #notFound { #absent } else { line else \"\" }",
            "(_) -> \"\" | #absent | _",
        ),
        (
            "if line is #notFound { #absent } else { trim(line else \"\") }",
            "(String | #_) -> String | #absent",
        ),
        ("trim(line else \"\")", "(String | #_) -> String"),
        ("line else \"\"", "(_) -> \"\" | _"),
        ("upper(line else \"\")", "(String | #_) -> String"),
        ("(line else 0) + 1", "(int | #_) -> int"),
        ("{ s = line else \"\"; trim(s) }", "(String | #_) -> String"),
        ("{ s = line; trim(s else \"\") }", "(String | #_) -> String"),
        (
            "if line is #notFound { \"\" } else { trim(line) }",
            "(String | #notFound) -> String",
        ),
        (
            "if line is #a | #b { \"\" } else { trim(line) }",
            "(String | #a | #b) -> String",
        ),
        (
            "trim(line else #notFound -> \"\")",
            "(String | #notFound | #notFound(..)) -> String",
        ),
        ("trim(line)", "(String) -> String"),
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
        "(#_ | T, T) -> T for T in int | f64 | rat"
    );
    let text = "r(positional line: String | #notFound) = trim(line else \"\");\n";
    assert_eq!(sig(text, "r"), "(String | #notFound) -> String");
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
            "((String) -> String) & ((String | #_) -> String | #_)",
        ),
        (
            "r(positional c)",
            "{ d = c else false; if c { \"yes\" } else { \"no\" } }",
            "((bool) -> \"no\" | \"yes\") & ((bool | #_) -> \"no\" | \"yes\" | #_)",
        ),
        (
            "r(positional n)",
            "{ d = n else 0; if n > 3 { \"big\" } else { \"small\" } }",
            "((int) -> \"big\" | \"small\") & ((int | #_) -> \"big\" | \"small\" | #_)",
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
        "((String) -> String | #absent) & ((String | #_) -> String | #_)"
    );
}
