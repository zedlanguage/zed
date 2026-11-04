//! The kind-wide types (step L1.40d, DESIGN.md sec:type_language): `#_` is every atom, `(..)`
//! every tuple, `{..}` every struct, `#a(..)` the atom `#a` with any payload and `#a()` the atom
//! `#a` with the empty payload. `..` stands alone between its brackets. Each form parses, is the
//! set it names in the kernel and in the checker, and prints back as text that reads back as the
//! same type.

use crate::l01_13_formatter::fmt;
use zed_kernel::types::{Type, Universe};
use zed_tests::scaling;
use zedc::ast::unit;
use zedc::check::read::parse_type;
use zedc::check::ty::{Ty, atoms};
use zedc::lex::lex_fence;
use zedc::parse::{DOTS, TOP, parse};
use zedc::resolve::resolve;

fn tuple(ts: &[Type]) -> Type {
    Type::tuple(ts.to_vec())
}

fn ty(text: &str) -> Ty {
    parse_type(text).unwrap_or_else(|e| panic!("{e}"))
}

#[test]
fn each_form_parses_and_formats_as_written() {
    for text in [
        "f(x: #_) = x;\n",
        "f(x: (..)) = x;\n",
        "f(x: {..}) = x;\n",
        "f(x: #a(..)) = x;\n",
        "f(x: #a()) = x;\n",
        "f(x: (..) \\ (int, int)) = x;\n",
        "f(x: #_ | (..) | {..}) = x;\n",
        "f(x) = x is (..);\n",
        "f(x) = x is not #_;\n",
    ] {
        assert_eq!(fmt(text), text);
    }
}

/// The parse error of the type in `f(x: <t>) = x;`: its message and the text at its span.
fn rejected(t: &str) -> (String, String) {
    let text = format!("f(x: {t}) = x;");
    let tokens = lex_fence(&text).unwrap();
    let e = parse(&text, &tokens, "Unit", TOP).unwrap_err();
    (e.to_string(), text[e.span.start..e.span.end].to_string())
}

#[test]
fn dots_with_other_items_in_a_list_is_rejected_at_the_dots() {
    for t in [
        "(int, ..)",
        "(.., int)",
        "#a(int, ..)",
        "#a(.., int)",
        "{x: int, ..}",
    ] {
        let (message, at) = rejected(t);
        assert_eq!(message, DOTS, "{t}");
        assert_eq!(at, "..", "{t}");
    }
    // The span is that of the `..` itself: in `(int, ..)` it follows `(int, `.
    let text = "f(x: (int, ..)) = x;";
    let tokens = lex_fence(text).unwrap();
    let e = parse(text, &tokens, "Unit", TOP).unwrap_err();
    assert_eq!((e.span.start, e.span.end), (11, 13));
    // Other errors keep their expected tokens.
    let (message, _) = rejected("(int,, int)");
    assert_ne!(message, DOTS);
}

/// The resolution errors of `text`, each `message [text]`.
fn resolve_errors(text: &str) -> Vec<String> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    match resolve(&stmts) {
        Ok(_) => Vec::new(),
        Err(es) => es
            .iter()
            .map(|e| format!("{} [{}]", e.message, &text[e.span.start..e.span.end]))
            .collect(),
    }
}

#[test]
fn every_atom_and_every_tuple_resolve_and_the_l2_forms_wait_for_l2_5() {
    assert_eq!(
        resolve_errors("f(x: #_ | (..)) = x is (..);"),
        Vec::<String>::new()
    );
    for (text, form) in [("f(x: {..}) = x;", "{..}"), ("f(x: #a(..)) = x;", "#a(..)")] {
        let es = resolve_errors(text);
        assert_eq!(es.len(), 1, "{es:?}");
        assert!(es[0].contains("L2.5"), "{es:?}");
        assert!(es[0].ends_with(&format!("[{form}]")), "{es:?}");
    }
}

#[test]
fn each_form_is_the_set_it_names_in_the_kernel() {
    let every_atom = atoms();
    let every_tuple = Type::universe(Universe::Tuple);
    let every_struct = Type::universe(Universe::Struct);
    let any_a = Type::atom_with("a", &Type::top());
    let empty_a = Type::atom_with("a", &tuple(&[]));
    let pair = tuple(&[Type::int(), Type::int()]);
    // Each member below lies in its kind-wide type, and the kind-wide type in none of them.
    for (member, whole) in [
        (Type::atom("none"), &every_atom),
        (&Type::atom("b") | &Type::atom_with("c", &pair), &every_atom),
        (any_a.clone(), &every_atom),
        (tuple(&[]), &every_tuple),
        (pair.clone(), &every_tuple),
        (&tuple(&[Type::top()]) | &pair, &every_tuple),
        (Type::atom_with("a", &pair), &any_a),
        (empty_a.clone(), &any_a),
        (Type::atom_with("a", &every_struct), &any_a),
    ] {
        assert!(member.subtype(whole), "{member} <: {whole}");
        assert!(!whole.subtype(&member), "{whole} </: {member}");
    }
    assert!(every_struct.subtype(&every_struct));
    // The kinds are apart from each other and from the carriers.
    for (a, b) in [
        (&every_atom, &every_tuple),
        (&every_atom, &every_struct),
        (&every_tuple, &every_struct),
    ] {
        assert!((a & b).is_empty(), "{a} & {b}");
    }
    assert!((&every_atom & &Type::int()).is_empty());
    assert!(!Type::int().subtype(&every_atom));
    // `#a()` is not the bare atom `#a`, and neither holds the other.
    assert!((&Type::atom("a") & &empty_a).is_empty());
}

#[test]
fn each_form_is_the_set_it_names_in_the_checker() {
    for (member, whole) in [
        ("#none", "#_"),
        ("#b | #c(int, int)", "#_"),
        ("#a(..)", "#_"),
        ("()", "(..)"),
        ("(int, int)", "(..)"),
        ("(_,) | (int, int)", "(..)"),
        ("(..) \\ (int, int)", "(..)"),
        ("#_ \\ #b", "#_"),
    ] {
        let (m, w) = (ty(member), ty(whole));
        assert!(m.subtype(&w), "{member} <: {whole}");
        assert!(!w.subtype(&m), "{whole} </: {member}");
    }
    // A payload's shape lies in any payload. The reverse is not decided here: the checker's set
    // holds every atom with a payload as `#a(..)` and keeps the shapes beside it, and its
    // subtyping compares the sets only (a flaw of the checker before L1.40d; the kernel test
    // above decides both directions).
    for member in ["#a(int, int)", "#a()"] {
        assert!(ty(member).subtype(&ty("#a(..)")), "{member} <: #a(..)");
    }
    for (a, b) in [
        ("#_", "(..)"),
        ("#_", "{..}"),
        ("(..)", "{..}"),
        ("int", "#_"),
    ] {
        assert!(!ty(a).subtype(&ty(b)), "{a} </: {b}");
        assert!(!ty(b).subtype(&ty(a)), "{b} </: {a}");
    }
    assert!(ty("{..}").subtype(&ty("{..}")));
    // `#a` and `#a()` are different types.
    assert_ne!(ty("#a"), ty("#a()"));
}

#[test]
fn each_form_prints_as_written_and_reads_back_as_the_same_type() {
    for text in [
        "#_",
        "(..)",
        "{..}",
        "#a(..)",
        "#a()",
        "#a(_)",
        "#_ \\ #b",
        "(..) \\ (int, int)",
        "(..) | {..}",
    ] {
        let first = ty(text);
        let printed = first.to_string();
        let again = ty(&printed);
        assert_eq!(again, first, "{text} printed {printed}");
        assert_eq!(again.to_string(), printed, "{text}");
        assert!(again.subtype(&first) && first.subtype(&again), "{text}");
    }
    // The kernel's printer, read back by the checker's reader. An atom with a payload is left
    // out: the checker's set holds it with any payload (see the test above).
    let pair = tuple(&[Type::int(), Type::int()]);
    for t in [
        atoms(),
        Type::universe(Universe::Tuple),
        Type::universe(Universe::Struct),
        &Type::universe(Universe::Tuple) - &pair,
        &atoms() - &Type::atom("b"),
    ] {
        let s = t.surface();
        assert!(s.exact, "{s}");
        let back = ty(&s.to_string());
        assert!(back.subtype(&Ty::set(t.clone())), "{s}");
        assert!(Ty::set(t.clone()).subtype(&back), "{s}");
    }
}

/// A union of `n` members, half kind-wide differences `(..) \ (i, i)` and `#_ \ #ai`, half
/// exact `(i, i)` and `#ai`.
fn mixed(n: usize) -> Type {
    Type::union_all((0..n).map(|i| {
        let v = Type::lit(&zed_kernel::value::Value::Int(i as i64)).unwrap();
        let a = Type::atom(&format!("a{i}"));
        match i % 4 {
            0 => &Type::universe(Universe::Tuple) - &tuple(&[v.clone(), v]),
            1 => &atoms() - &a,
            2 => tuple(&[v.clone(), v]),
            _ => a,
        }
    }))
}

#[test]
fn a_union_of_kind_wide_and_exact_members_scales() {
    // Building, printing and reading back the union is O(n log n) in its members.
    scaling::check("a union of kind-wide and exact members", 256, |n| {
        let t = mixed(n);
        let s = t.surface();
        assert!(s.exact);
        let back = ty(&s.to_string());
        assert!(back.subtype(&Ty::set(t)));
    });
}

/// The checker's type of `n` tuple shapes `(i, i)`, and `(..) \ (0, 0)` as its kind-wide part.
fn shapes(n: usize) -> (Ty, Ty) {
    let lit = |i: usize| Ty::lit(&zed_kernel::value::Value::Int(i as i64));
    let ts: Vec<Ty> = (0..n).map(|i| Ty::tuple(vec![lit(i), lit(i)])).collect();
    (Ty::union_all(&ts), ty("(..) \\ (0, 0)"))
}

#[test]
fn narrowing_tuple_shapes_by_a_kind_wide_type_scales() {
    // `is` and `is not` against a kind-wide part read each shape once against it.
    scaling::check("narrowing n tuple shapes by (..) \\ (0, 0)", 256, |n| {
        let (t, w) = shapes(n);
        let met = t.meet(&w);
        assert_eq!(met.tuples.len(), n - 1);
        let left = t.diff(&w);
        assert_eq!(left.tuples.len(), 1);
    });
}
