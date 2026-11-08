//! The kind-wide types (step L1.40d, DESIGN.md sec:type_language): `#_` is every atom, `(..)`
//! every tuple, `{..}` every struct, `#a(..)` the atom `#a` with any payload and `#a()` the atom
//! `#a` with the empty payload. `..` stands alone between its brackets. Each form parses, is the
//! set it names in the kernel and in the checker, and prints back as text that reads back as the
//! same type.

use zed_kernel::types::{Type, Universe};
use zed_tests::scaling;
use zed_tests::step_helpers::l01_13_formatter::fmt;
use zedc::ast::unit;
use zedc::check::read::parse_type;
use zedc::check::ty::{Shape, Ty, atoms};
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
    // A payload's shape lies in any payload, and any payload in no one shape.
    for (member, whole) in [("#a(int, int)", "#a(..)"), ("#a()", "#a(..)")] {
        let (m, w) = (ty(member), ty(whole));
        assert!(m.subtype(&w), "{member} <: {whole}");
        assert!(!w.subtype(&m), "{whole} </: {member}");
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
fn subtyping_reads_the_payloads_of_atoms() {
    // A payload lies in another when its shape does, alone, in a union, or inside a tuple.
    for (member, whole) in [
        ("#a(int, int)", "#a(int, int)"),
        ("#a(int, int)", "#a(int | String, int)"),
        ("#a(int | String)", "#a(int) | #a(String)"),
        ("#a(int) | #b(String)", "#a(int | rat) | #b(..)"),
        ("#a()", "#a() | #a(int)"),
        ("(#a(int, int),)", "(#a(int | String, int),)"),
        ("#a(#b(int))", "#a(#b(int | String))"),
        ("#a(int) | #c", "#a(int) | #c"),
    ] {
        assert!(ty(member).subtype(&ty(whole)), "{member} <: {whole}");
    }
    // A payload of another shape, of another length, or of any shape is not in it.
    for (member, whole) in [
        ("#a(String)", "#a(int, int)"),
        ("#a(..)", "#a(int, int)"),
        ("#a(..)", "#a()"),
        ("#a()", "#a(int)"),
        ("#a(int, String)", "#a(int, int)"),
        ("#a(int | String)", "#a(int)"),
        ("#a(int) | #b(String)", "#a(int) | #b(int)"),
        ("(#a(String),)", "(#a(int, int),)"),
        ("#a(#b(String))", "#a(#b(int))"),
        ("#a(int) | #a(String)", "#a(int)"),
    ] {
        assert!(!ty(member).subtype(&ty(whole)), "{member} </: {whole}");
    }
}

#[test]
fn every_tuple_may_hold_a_function() {
    // `(..)` is every tuple, those that hold a function among them.
    for text in [
        "(..)",
        "(int, (..))",
        "(..) \\ (int, int)",
        "{..}",
        "(..) | int",
    ] {
        assert!(!ty(text).first_order(), "{text} may hold a function");
    }
    for text in [
        "(int, int)",
        "#_",
        "#a(..)",
        "int | (String,)",
        "(int, #a())",
    ] {
        assert!(ty(text).first_order(), "{text} holds no function");
    }
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
    // out: the checker's set holds it with any payload, and its payload apart, so the two
    // types are equal as sets but not as values.
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

#[test]
fn a_use_that_takes_data_refuses_every_tuple() {
    // A block that ends `return h, 1` builds a tuple that holds a function, and `(..)` takes it,
    // so `==`, interpolation and `String` on a value of `(..)` are refused where they are
    // written, at any depth, as they are on a value whose function is known.
    let errors = zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let call = "g() = f(x: { h(y) = y; return h, 1; });\n";
    for (body, what, at) in [
        ("x == x", "`==`", "x == x"),
        ("\"a${x}b\"", "interpolation", "x"),
        ("String(x)", "`String`", "String(x)"),
    ] {
        let text = format!("f(x: (..)) = {body};\n{call}");
        let want =
            format!("{what} takes data, and this value, of `(..)`, may hold a function [{at}]");
        assert_eq!(errors(&text), [want], "{text}");
    }
    assert_eq!(
        errors("f(x: (int, (..))) = x == x;\n"),
        ["`==` takes data, and this value, of `(..)`, may hold a function [x == x]"]
    );
    // A tuple whose shape is written holds what its components hold.
    assert_eq!(errors("f(x: (int, int)) = x == x;\n"), Vec::<String>::new());
}

/// The atom `#name` with the payloads `shapes`, each of components only.
fn with_payloads(name: &str, shapes: Vec<Vec<Ty>>) -> Ty {
    let mut t = Ty::set(Type::atom_with(name, &Type::top()));
    let shapes = shapes
        .into_iter()
        .map(|items| Shape::new(items, Default::default()))
        .collect();
    t.payloads.insert(name.into(), Some(shapes));
    t
}

fn int(i: usize) -> Ty {
    Ty::lit(&zed_kernel::value::Value::Int(i as i64))
}

#[test]
fn payloads_of_many_atoms_are_compared_in_the_size_of_the_union() {
    // `#a0(0) | … | #a(n-1)(n-1)` against `#ai(int)` for each name, and against the same with
    // `#a0(String)`: the listed names are taken out and put back in one union each.
    scaling::check("payloads of n atoms against n atoms", 256, |n| {
        let each = |f: &dyn Fn(usize) -> Ty| -> Ty {
            let ts: Vec<Ty> = (0..n)
                .map(|i| with_payloads(&format!("a{i}"), vec![vec![f(i)]]))
                .collect();
            Ty::union_all(&ts)
        };
        let small = each(&int);
        let wide = each(&|_| ty("int"));
        let other = each(&|i| if i == 0 { ty("String") } else { ty("int") });
        assert!(small.subtype(&wide));
        assert!(!small.subtype(&other));
    });
}

#[test]
fn many_payloads_of_one_atom_are_compared_in_the_size_of_the_union() {
    // `#a(0, 0) | … | #a(n-1, n-1)` against itself and `#a(n, n)`: each payload tried against
    // each would be n² component checks; the kernel reads both unions once.
    scaling::check("n payloads of one atom against n + 1", 256, |n| {
        let pairs = |m: usize| with_payloads("a", (0..m).map(|i| vec![int(i), int(i)]).collect());
        let (small, big) = (pairs(n), pairs(n + 1));
        assert!(small.subtype(&big));
        assert!(!big.subtype(&small));
    });
}

#[test]
fn a_kind_wide_part_deep_in_tuples_is_found_once() {
    // `((…((..), 0)…), 0)`, n deep: each row keeps the kind-wide part its components hold, so
    // finding it reads one row, and building the type reads each row once.
    scaling::check("a kind-wide part n tuples deep", 256, |n| {
        let mut t = ty("(..)");
        for _ in 0..n {
            t = Ty::tuple(vec![t, int(0)]);
        }
        assert!(!t.first_order());
    });
}

#[test]
fn tuples_and_payloads_that_hold_functions_are_decided_by_their_normal_forms() {
    // A function is in another where it fits it, inside a tuple, in a payload, by position or
    // by field; shapes that hold a tuple only together still hold it.
    for (member, whole) in [
        ("((int) -> int, 1)", "((int) -> int, int)"),
        (
            "(#a0 | #a1, (int) -> int)",
            "(#a0, (int) -> int) | (#a1, (int) -> int)",
        ),
        ("#a((int) -> int)", "#a((int) -> int) | #b"),
        ("#a((int | String) -> int)", "#a((int) -> int)"),
        (
            "#a((int) -> int, 1) | #a((int) -> int, 2)",
            "#a((int) -> int, int)",
        ),
        ("#a(x: int)", "#a(x: int | String)"),
        ("#a(x: int, y: (int) -> int)", "#a(x: int, y: (int) -> int)"),
        ("#a(x: int)", "#a(..)"),
        ("(#a((int) -> int),)", "(#a(..),)"),
    ] {
        assert!(ty(member).subtype(&ty(whole)), "{member} <: {whole}");
    }
    for (member, whole) in [
        ("((int) -> int, \"a\")", "((int) -> int, int)"),
        (
            "(#a0 | #a2, (int) -> int)",
            "(#a0, (int) -> int) | (#a1, (int) -> int)",
        ),
        ("#a((int) -> int)", "#a((String) -> int)"),
        ("#a((int) -> int)", "#a((int | String) -> int)"),
        ("#a(x: int)", "#a(y: int)"),
        ("#a(int)", "#a(x: int)"),
        ("#a(x: int)", "#a(int)"),
        (
            "#a(x: int, y: (int) -> int)",
            "#a(x: int, y: (int) -> String)",
        ),
        ("#a(..)", "#a((int) -> int)"),
    ] {
        assert!(!ty(member).subtype(&ty(whole)), "{member} </: {whole}");
    }
}

#[test]
fn marks_are_cut_from_sets_of_all_atoms() {
    // A form puts an atom no program writes where a function or a payload's fields are; `#_`
    // beside it holds every atom written and none of those.
    for (member, whole) in [
        ("((int) -> int, #b)", "((int) -> int, #_)"),
        ("(#_, (int) -> int)", "(#_, (int) -> int)"),
        ("#a(#b, (int) -> int)", "#a(#_, (int) -> int)"),
        ("#a(x: #b)", "#a(x: #_)"),
        ("#c(#a(x: 1))", "#c(#_)"),
    ] {
        assert!(ty(member).subtype(&ty(whole)), "{member} <: {whole}");
    }
    for (member, whole) in [
        ("((int) -> int, 1)", "(#_, int)"),
        ("#a((int) -> int)", "#a(#_)"),
        ("#a(x: 1)", "#a(int, #_)"),
        ("#a(1, (int) -> int)", "#a(int, #_)"),
        ("(_, 1)", "(#_, int)"),
    ] {
        assert!(!ty(member).subtype(&ty(whole)), "{member} </: {whole}");
    }
}

#[test]
fn functions_unlike_on_both_sides_at_one_place_are_refused() {
    // Two functions of `t`, equal to none of the expected type's, meet two of its at one place:
    // which fits which is not compared (COMPLEXITY.md F112), and the clause says so.
    let (t, u) = (
        ty("((int | String) -> int, 1) | ((int | rat) -> int, 2)"),
        ty("((int) -> int, int) | ((String) -> int, int)"),
    );
    assert!(!t.subtype(&u));
    assert!(
        t.refused(&u).contains("not decided: two or more functions"),
        "{}",
        t.refused(&u)
    );
    // One function on either side is compared with each on the other.
    for (member, whole) in [
        (
            "((int | String) -> int, 1)",
            "((int) -> int, int) | ((String) -> int, int)",
        ),
        (
            "((int | String) -> int, 1) | ((int | rat) -> int, 2)",
            "((int) -> int, int)",
        ),
        // Functions equal on both sides are matched by equality, however many.
        (
            "((int) -> int, 1) | ((String) -> int, 2)",
            "((int) -> int, int) | ((String) -> int, int)",
        ),
    ] {
        let (m, w) = (ty(member), ty(whole));
        assert!(m.subtype(&w), "{member} <: {whole}");
        assert_eq!(m.refused(&w), "", "{member} <: {whole}");
    }
}

#[test]
fn payloads_with_a_variable_are_compared_shape_by_shape() {
    // A variable of the expected type is bound by the shape that holds the payload, and a
    // payload not known is in a payload not known only.
    let a_of = |t: Ty| {
        let mut out = Ty::set(Type::atom_with("a", &Type::top()));
        out.payloads.insert(
            "a".into(),
            Some(vec![Shape::new(vec![t, int(1)], Default::default())]),
        );
        out
    };
    let (member, whole) = (
        with_payloads("a", vec![vec![ty("String"), int(1)]]),
        a_of(Ty::var("T".into())),
    );
    let mut binds = Default::default();
    assert!(member.sub(&whole, &mut binds));
    assert_eq!(
        binds.get("T").map(|t: &Ty| t.to_string()),
        Some("String".to_string())
    );
    let mut binds = Default::default();
    assert!(!ty("#a(..)").sub(&whole, &mut binds));
    let mut binds = Default::default();
    assert!(!with_payloads("a", vec![vec![ty("String"), int(2)]]).sub(&whole, &mut binds));
}

#[test]
fn payloads_that_hold_functions_are_compared_in_the_size_of_the_union() {
    // `#a0((int) -> #r0, 0) | … ` against the same with `(int) -> #r_i | #s` and `int`: one
    // function on each side at each place, so each is compared once; trying each payload
    // against each was n² comparisons (A6, 2026-11-08).
    let union = |n: usize, f: &dyn Fn(usize) -> String| {
        let parts: Vec<String> = (0..n).map(|i| format!("#a{i}({})", f(i))).collect();
        ty(&parts.join(" | "))
    };
    let inputs = scaling::inputs(256, |n| {
        (
            union(n, &|i| format!("(int) -> #r{i}, {i}")),
            union(n, &|i| format!("(int) -> #r{i} | #s, int")),
            union(n, &|i| format!("(int) -> #s, {i}")),
        )
    });
    scaling::check("n payloads that hold functions against n", 256, |n| {
        let (small, wide, other) = &inputs[&n];
        assert!(small.subtype(wide));
        assert!(!small.subtype(other));
    });
    // One atom: `#a((int) -> int, 0) | …` against the same payloads in the other order, and
    // against them with `String` results, all of one length, which trying each payload against
    // each of its length compared in `n²`.
    let one = |n: usize, order: &dyn Fn(usize) -> usize, r: &str| {
        let parts: Vec<String> = (0..n)
            .map(|i| format!("#a((int) -> {r}, {})", order(i)))
            .collect();
        ty(&parts.join(" | "))
    };
    let inputs = scaling::inputs(256, |n| {
        (
            one(n, &|i| i, "int"),
            one(n, &|i| n - 1 - i, "int"),
            one(n, &|i| n - 1 - i, "String"),
        )
    });
    scaling::check("n payloads of one atom that hold functions against n", 256, |n| {
        let (small, same, other) = &inputs[&n];
        assert!(small.subtype(same));
        assert!(!small.subtype(other));
    });
}

#[test]
fn payloads_with_fields_and_tuples_that_hold_functions_are_compared_in_the_size_of_the_union() {
    // `#a(x: 0, f: (int) -> int) | … | #a(x: n-1, …)` against `#a(x: int, f: (int) -> int)`,
    // and `(#a0 | … | #a(n-1), (int) -> int)` against the n shapes `(#a_i, (int) -> int)`,
    // which hold it only together (K38).
    let inputs = scaling::inputs(256, |n| {
        let fields: Vec<String> = (0..n)
            .map(|i| format!("#a(x: {i}, f: (int) -> int)"))
            .collect();
        let atoms: Vec<String> = (0..n).map(|i| format!("#a{i}")).collect();
        let shapes: Vec<String> = atoms
            .iter()
            .map(|a| format!("({a}, (int) -> int)"))
            .collect();
        (
            ty(&fields.join(" | ")),
            ty(&format!("({}, (int) -> int)", atoms.join(" | "))),
            ty(&shapes.join(" | ")),
        )
    });
    let whole = ty("#a(x: int, f: (int) -> int)");
    let not = ty("#a(x: int, f: (int) -> String)");
    scaling::check("n payloads with fields that hold functions", 256, |n| {
        let (fields, _, _) = &inputs[&n];
        assert!(fields.subtype(&whole));
        assert!(!fields.subtype(&not));
    });
    scaling::check("a tuple that holds a function, held by n shapes", 256, |n| {
        let (_, tuple, shapes) = &inputs[&n];
        assert!(tuple.subtype(shapes));
    });
}

