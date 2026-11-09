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
        assert!(zed_tests::is_not_yet(&es[0]), "{es:?}");
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

/// Item PRINT-fmt-audit: the kernel set in a compiler type is written as one expression
/// (`Type::surface_by_name`), at the place it stands in the compiler's text. Before, a part used
/// twice got a definition, written in the middle of the compiler's text:
///
/// - `(int | #x, int | #x)` was `type T1 = int | #x; (T1, T1)`
/// - `#y | (int | #x, int | #x)` was `type T1 = int | #x; #y | (T1, T1)`
/// - `(int | #x, int | #x) | (bool, bool)` was `type T1 = int | #x; (T1, T1) | (bool, bool)`
///
/// `int | (int ->? int)` and `(int ->? int) | (bool, bool)` were written so before too. Each text
/// parses; a set reads back as the same type, and a function, which the reader makes the
/// checker's own function type, reads back as that type again from its own text.
#[test]
fn a_kernel_set_in_a_compiler_type_is_written_without_definitions() {
    let int_or_x = &Type::int() | &Type::atom("x");
    let shared = tuple(&[int_or_x.clone(), int_or_x.clone()]);
    let partial = Type::partial(Type::int(), Type::int());
    // Each type, its text, and whether it is a set of values with no function.
    for (t, text, set) in [
        (Ty::set(shared.clone()), "(int | #x, int | #x)", true),
        (
            Ty::set(&shared | &Type::atom("y")),
            "#y | (int | #x, int | #x)",
            true,
        ),
        (
            ty("(bool, bool)").union(&Ty::set(shared.clone())),
            "(int | #x, int | #x) | (bool, bool)",
            true,
        ),
        (
            Ty::set(&Type::int() | &partial),
            "int | (int ->? int)",
            false,
        ),
        (
            ty("(bool, bool)").union(&Ty::set(partial.clone())),
            "(int ->? int) | (bool, bool)",
            false,
        ),
    ] {
        assert_eq!(t.to_string(), text);
        let back = ty(text);
        match set {
            true => assert!(back.subtype(&t) && t.subtype(&back), "{text}"),
            false => assert_eq!(ty(&back.to_string()), back, "{text}"),
        }
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
        let want = format!(
            "{what} takes data, and this value, of `(..)`, may hold a function: data is a value that holds no function at any depth, and `(..)` holds every value of its shape, functions too [{at}]"
        );
        assert_eq!(errors(&text), [want], "{text}");
    }
    assert_eq!(
        errors("f(x: (int, (..))) = x == x;\n"),
        [
            "`==` takes data, and this value, of `(..)`, may hold a function: data is a value that holds no function at any depth, and `(..)` holds every value of its shape, functions too [x == x]"
        ]
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
    // which fits which is not compared (COMPLEXITY.md F124), and the clause says so.
    let (t, u) = (
        ty("((int | String) -> int, 1) | ((int | rat) -> int, 2)"),
        ty("((int) -> int, int) | ((String) -> int, int)"),
    );
    assert!(!t.subtype(&u));
    assert!(
        t.refused(&u).contains("because two or more functions"),
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
    scaling::check(
        "n payloads of one atom that hold functions against n",
        256,
        |n| {
            let (small, same, other) = &inputs[&n];
            assert!(small.subtype(same));
            assert!(!small.subtype(other));
        },
    );
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
    scaling::check(
        "a tuple that holds a function, held by n shapes",
        256,
        |n| {
            let (_, tuple, shapes) = &inputs[&n];
            assert!(tuple.subtype(shapes));
        },
    );
}

fn var(name: &str) -> Ty {
    Ty::var(name.into())
}

/// `l <: r`, with what it binds.
fn bound(l: &Ty, r: &Ty) -> Option<Vec<(String, String)>> {
    let mut b = Default::default();
    let ok = l.sub(r, &mut b);
    ok.then(|| {
        b.iter()
            .map(|(v, t)| (v.to_string(), t.to_string()))
            .collect()
    })
}

#[test]
fn payloads_with_a_variable_are_searched_by_their_keys() {
    // `#a(String, 0) | … | #a(String, n-1)` against `#a(T, n-1) | … | #a(T, 0)`: each payload
    // is found by its second component, not tried against each shape before it (n²).
    let inputs = scaling::inputs(256, |n| {
        let l = with_payloads("a", (0..n).map(|i| vec![ty("String"), int(i)]).collect());
        let r = with_payloads("a", (0..n).rev().map(|i| vec![var("T"), int(i)]).collect());
        let wrong = with_payloads("a", (0..=n).map(|i| vec![ty("String"), int(i)]).collect());
        (l, r, wrong)
    });
    scaling::check("n payloads with a variable against n", 256, |n| {
        let (l, r, wrong) = &inputs[&n];
        assert_eq!(bound(l, r), Some(vec![("T".into(), "String".into())]));
        assert_eq!(bound(wrong, r), None);
        assert_eq!(wrong.refused(r), "");
    });
}

#[test]
fn tuples_with_a_variable_are_searched_by_their_keys() {
    // The same with tuples: `(String, i)` against `(T, i)` in the reverse order.
    let inputs = scaling::inputs(256, |n| {
        let l: Vec<Ty> = (0..n)
            .map(|i| Ty::tuple(vec![ty("String"), int(i)]))
            .collect();
        let r: Vec<Ty> = (0..n)
            .rev()
            .map(|i| Ty::tuple(vec![var("T"), int(i)]))
            .collect();
        (Ty::union_all(&l), Ty::union_all(&r))
    });
    scaling::check("n tuples with a variable against n", 256, |n| {
        let (l, r) = &inputs[&n];
        assert_eq!(bound(l, r), Some(vec![("T".into(), "String".into())]));
    });
}

#[test]
fn shapes_with_no_variable_are_found_by_their_keys() {
    let l = with_payloads(
        "a",
        vec![vec![int(1), ty("String")], vec![int(2), ty("int")]],
    );
    let r = with_payloads(
        "a",
        vec![
            vec![int(2), ty("int")],
            vec![ty("int"), ty("String")],
            vec![int(1), ty("int")],
        ],
    );
    assert_eq!(bound(&l, &r), Some(vec![]));
    // Payloads told apart by carrier: `#a(int, String)` is not in `#a(String, int)`.
    let crossed = with_payloads(
        "a",
        vec![vec![ty("int"), ty("String")], vec![ty("String"), ty("int")]],
    );
    let one = with_payloads("a", vec![vec![ty("String"), ty("int")]]);
    assert_eq!(bound(&crossed, &crossed), Some(vec![]));
    assert_eq!(bound(&crossed, &one), None);
    assert_eq!(bound(&one, &crossed), Some(vec![]));
}

#[test]
fn one_variable_used_twice_binds_both_components() {
    let r = with_payloads(
        "a",
        vec![vec![var("T"), var("T")], vec![ty("String"), ty("int")]],
    );
    let same = with_payloads("a", vec![vec![int(1), int(1)]]);
    let b = bound(&same, &r).expect("held");
    assert_eq!(b.len(), 1);
    assert_eq!(b[0].0, "T");
    let other = with_payloads("a", vec![vec![ty("String"), int(3)]]);
    assert!(bound(&other, &r).is_some());
    let rows = Ty::union_all(&[Ty::tuple(vec![var("T"), var("T")]), ty("(String, int)")]);
    assert!(bound(&ty("(1, 1)"), &rows).is_some());
    assert!(bound(&ty("(String, 3)"), &rows).is_some());
    // `T` holds both components, so it is bound to their union.
    assert_eq!(
        bound(&ty("(int, String)"), &rows),
        Some(vec![("T".into(), "int | String".into())])
    );
}

#[test]
fn variables_in_nested_payloads_and_tuples_are_bound() {
    let inner = |t: Ty| with_payloads("b", vec![vec![t]]);
    let r = with_payloads(
        "a",
        vec![vec![int(0), inner(var("T"))], vec![int(1), inner(var("U"))]],
    );
    let l = with_payloads(
        "a",
        vec![
            vec![int(1), inner(ty("String"))],
            vec![int(0), inner(ty("int"))],
        ],
    );
    assert_eq!(
        bound(&l, &r),
        Some(vec![
            ("T".into(), "int".into()),
            ("U".into(), "String".into())
        ])
    );
    let rows = Ty::union_all(&[
        Ty::tuple(vec![Ty::tuple(vec![int(0), var("T")]), int(0)]),
        Ty::tuple(vec![Ty::tuple(vec![int(1), var("U")]), int(0)]),
    ]);
    assert_eq!(
        bound(&ty("((1, String), 0) | ((0, int), 0)"), &rows),
        Some(vec![
            ("T".into(), "int".into()),
            ("U".into(), "String".into())
        ])
    );
}

#[test]
fn shapes_that_hold_no_member_are_not_matched() {
    let r = with_payloads("a", vec![vec![var("T"), int(0)], vec![var("T"), int(1)]]);
    let l = with_payloads("a", vec![vec![ty("String"), int(2)]]);
    assert_eq!(bound(&l, &r), None);
    assert_eq!(l.refused(&r), "");
    let rows = Ty::union_all(&[Ty::tuple(vec![var("T"), int(0)]), ty("(int, 1)")]);
    assert_eq!(bound(&ty("(String, 2)"), &rows), None);
    assert_eq!(bound(&ty("(String, 1)"), &rows), None);
}

#[test]
fn of_several_shapes_the_first_in_written_order_binds() {
    // `#a(1)` is held by `#a(T)` and `#a(U)`; the first written binds.
    let r = with_payloads("a", vec![vec![var("T")], vec![var("U")]]);
    let l = with_payloads("a", vec![vec![int(1)]]);
    assert_eq!(bound(&l, &r), Some(vec![("T".into(), "1".into())]));
    let r = with_payloads("a", vec![vec![var("U")], vec![var("T")]]);
    assert_eq!(bound(&l, &r), Some(vec![("U".into(), "1".into())]));
    // A shape of a key before one with a variable: `(1, T)` before `(U, T)`.
    let rows = Ty::union_all(&[
        Ty::tuple(vec![var("U"), var("T")]),
        Ty::tuple(vec![int(1), var("V")]),
    ]);
    assert_eq!(
        bound(&ty("(1, 2)"), &rows),
        Some(vec![("T".into(), "2".into()), ("U".into(), "1".into())])
    );
}

#[test]
fn shapes_told_apart_inside_tuple_components_are_found() {
    // Components that are tuples of one value file the shapes by that value, and those of one
    // length by the length, so these are found without a refusal.
    let inner = with_payloads(
        "b",
        vec![vec![ty("(1, 2)")], vec![ty("(3, 4)")], vec![ty("(5, 6)")]],
    );
    let with_t = with_payloads(
        "b",
        vec![
            vec![ty("(1, 2)")],
            vec![ty("(3, 4)")],
            vec![ty("(5, 6)")],
            vec![Ty::tuple(vec![var("T"), var("T")])],
        ],
    );
    let rows = Ty::union_all(&[ty("((1, 2), 0)"), ty("((3, 4), 0)"), ty("((5, 6), 0)")]);
    let rows_t = Ty::union_all(&[rows.clone(), Ty::tuple(vec![var("T"), int(7)])]);
    for (l, r) in [
        (
            Ty::tuple(vec![inner.clone(), int(1)]),
            Ty::tuple(vec![inner.clone(), var("T")]),
        ),
        (inner.clone(), with_t),
        (rows.clone(), rows_t),
    ] {
        assert!(bound(&l, &r).is_some(), "{l} <: {r}");
        assert_eq!(l.refused(&r), "", "{l} <: {r}");
    }
}

#[test]
fn two_payloads_that_need_a_later_shape_of_one_key_are_refused_with_the_reason() {
    // Component 1 files both shapes under `int`, and `1 | 2` holds neither payload: each
    // would search the bucket past its first shape.
    let r = with_payloads(
        "a",
        vec![vec![ty("1 | 2"), var("T")], vec![ty("int"), var("U")]],
    );
    let l = with_payloads("a", vec![vec![int(3), int(5)], vec![int(4), int(6)]]);
    assert_eq!(bound(&l, &r), None);
    assert_eq!(
        l.refused(&r),
        "; this is not proved wrong: the checker could not decide whether it fits, because the \
         payloads #a(3, 5) and #a(4, 6) may each be held by one of the shapes \
         #a(1 | 2, _) | #a(int, _), which are told apart only at component 1, where they agree \
         with both, and neither is held by the first of those shapes; which shape holds each \
         decides what the type variables are bound to, and the checker looks through those \
         shapes for one of the two only; to repair it, give #a(3, 5) a shape of its own, \
         written just before the shape that should hold it and the same as that shape except \
         at component 1, where it is 3: `#a(3, …)`, with that shape's other components in place \
         of each `…`; or test the value with `is` first, so that each test meets one of the two"
    );
    // The repair applied: `#a(3, U)` written just before `#a(int, U)`, which holds #a(3, 5).
    // The comparison is decided and binds `U` as the rule of one shape does.
    let repaired = with_payloads(
        "a",
        vec![
            vec![ty("1 | 2"), var("T")],
            vec![int(3), var("U")],
            vec![ty("int"), var("U")],
        ],
    );
    assert_eq!(l.refused(&repaired), "");
    assert_eq!(
        bound(&l, &repaired),
        Some(vec![("U".into(), "5 | 6".into())])
    );
    // One such payload is decided.
    let one = with_payloads("a", vec![vec![int(3), int(5)]]);
    assert_eq!(bound(&one, &r), Some(vec![("U".into(), "5".into())]));
    // The same with tuples.
    let rows = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    let l = ty("(3, 5) | (4, 6)");
    assert_eq!(bound(&l, &rows), None);
    let why = l.refused(&rows);
    assert!(
        why.contains("could not decide whether it fits, because the tuples (3, 5) and (4, 6) ")
    );
    assert!(why.contains(
        "give (3, 5) a shape of its own, written just before the shape that \
                          should hold it and the same as that shape except at component 1, \
                          where it is 3: `(3, …)`"
    ));
    let repaired = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![int(3), var("U")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    assert_eq!(l.refused(&repaired), "");
    assert_eq!(
        bound(&l, &repaired),
        Some(vec![("U".into(), "5 | 6".into())])
    );
    // The other repair: tested with `is`, each branch meets one of the two, which is decided.
    for one in [ty("(3, 5)"), ty("(4, 6)")] {
        assert_eq!(one.refused(&rows), "");
        assert!(bound(&one, &rows).is_some(), "{one}");
    }
}

#[test]
fn a_repair_by_a_shape_of_its_own_is_offered_only_where_a_component_tells_the_two_apart() {
    let rows = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    // The two agree at component 1 and differ in carrier at component 2: the shape of its own
    // is filed by that carrier, and the repair applied is decided.
    let l = Ty::union_all(&[
        Ty::tuple(vec![int(3), ty("bool")]),
        Ty::tuple(vec![int(3), ty("f64")]),
    ]);
    assert_eq!(bound(&l, &rows), None);
    assert!(l.refused(&rows).contains(
        "to repair it, give (3, bool) a shape of its own, written just before the shape that \
         should hold it and the same as that shape except at component 2, where it is bool: \
         `(…, bool)`, with that shape's other components in place of each `…`; or test the \
         value with `is` first"
    ));
    let repaired = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![ty("int"), ty("bool")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    assert_eq!(l.refused(&repaired), "");
    assert_eq!(bound(&l, &repaired), Some(vec![("U".into(), "f64".into())]));
    // Here they differ only where neither has a class: no shape of its own is filed apart, so
    // only the test with `is` is offered.
    let l = Ty::union_all(&[
        Ty::tuple(vec![int(3), ty("int | bool")]),
        Ty::tuple(vec![int(3), ty("f64 | String")]),
    ]);
    let why = l.refused(&rows);
    assert!(
        why.ends_with(
            "one of the two only; to repair it, test the value with `is` first, so that each test \
         meets one of the two"
        ),
        "{why}"
    );
}

/// `n` tuples on each side, in pairs `(t, u)` with what is left of `t` without `u` and what
/// of `t` is in `u`, as tuple counts: each tuple of `t` may share a value with at most one of
/// `u`, found by key lookup, which meeting or subtracting every pair of tuples compared in
/// `n^2`.
fn tuple_families(n: usize) -> Vec<(&'static str, Ty, Ty, usize, usize)> {
    let rows = |f: &dyn Fn(usize) -> Ty| Ty::union_all(&(0..n).map(f).collect::<Vec<_>>());
    let pair = |a: Ty, b: Ty| Ty::tuple(vec![a, b]);
    let f = ty("(int) -> int");
    vec![
        // Points: `(i, i)` without and meet `(2i, 2i)`, decided by the kernel.
        (
            "points",
            rows(&|i| pair(int(i), int(i))),
            rows(&|i| pair(int(2 * i), int(2 * i))),
            n / 2,
            n / 2,
        ),
        // A function at a place: decided on the normal forms.
        (
            "functions",
            rows(&|i| pair(f.clone(), int(i))),
            rows(&|i| pair(f.clone(), int(2 * i))),
            n / 2,
            n / 2,
        ),
        // A variable on the expected side, which `String` would bind: every tuple is kept,
        // and no tuple meets.
        (
            "variables",
            rows(&|i| pair(ty("String"), int(i))),
            rows(&|i| pair(var("T"), int(2 * i))),
            n,
            0,
        ),
        // `(bool, i)` is held by `(true, i) | (false, i)` only together.
        (
            "together",
            rows(&|i| pair(ty("bool"), int(i))),
            Ty::union_all(
                &(0..n)
                    .flat_map(|i| [pair(ty("true"), int(i)), pair(ty("false"), int(i))])
                    .collect::<Vec<_>>(),
            ),
            0,
            n,
        ),
    ]
}

#[test]
fn subtracting_tuples_scales() {
    // `t \ u` as `is not` narrows: each tuple of `t` is compared with the tuples of `u` that
    // may share a value with it, found by key lookup.
    let inputs = scaling::inputs(256, tuple_families);
    scaling::check("n tuples without n tuples, four ways", 256, |n| {
        for (what, t, u, left, _) in &inputs[&n] {
            assert_eq!(t.diff(u).tuples.len(), *left, "{what}");
        }
    });
}

#[test]
fn meeting_tuples_scales() {
    // `t` meet `u` as `is` narrows: each tuple of `t` is met with the tuples of `u` that may
    // share a value with it, found by key lookup; the tuples met are as many as the pairs.
    let inputs = scaling::inputs(256, tuple_families);
    scaling::check("n tuples met with n tuples, four ways", 256, |n| {
        for (what, t, u, _, met) in &inputs[&n] {
            let m = t.meet(u);
            // A tuple met twice, `(bool, i)` with `(true, i)` and `(false, i)`, gives two.
            let met = if *what == "together" { 2 * met } else { *met };
            assert_eq!(m.tuples.len(), met, "{what}");
        }
    });
}

/// `n` tuples of points `(i, n + i)`, and `n` tuples `(i, int)` and `n` tuples `(int, n + i)`
/// of two arrangements of points and `int`, which each hold one of the points.
fn two_patterns(n: usize) -> (Ty, Ty) {
    let pair = |a: Ty, b: Ty| Ty::tuple(vec![a, b]);
    let points: Vec<Ty> = (0..n).map(|i| pair(int(i), int(n + i))).collect();
    let open = (0..n).flat_map(|i| [pair(int(i), ty("int")), pair(ty("int"), int(n + i))]);
    (
        Ty::union_all(&points),
        Ty::union_all(&open.collect::<Vec<_>>()),
    )
}

/// `n` tuples of `2·log2 n` components on each side, each a different arrangement of `int` and
/// a point, `1` on one side and `0` on the other: two tuples share a value exactly when no
/// place holds a point in both, so finding the pairs is the orthogonal vectors problem.
fn many_patterns(n: usize) -> (Ty, Ty) {
    let width = 2 * n.ilog2() as usize;
    let side = |point: usize| {
        let rows: Vec<Ty> = (0..n)
            .map(|i| {
                // A different arrangement for each `i`, spread over the places.
                let bits = (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> (64 - width);
                Ty::tuple(
                    (0..width)
                        .map(|j| match bits >> j & 1 {
                            1 => int(point),
                            _ => ty("int"),
                        })
                        .collect(),
                )
            })
            .collect();
        Ty::union_all(&rows)
    };
    (side(1), side(0))
}

#[test]
fn meeting_and_subtracting_tuples_of_many_patterns_costs_the_patterns() {
    // Tuples are filed by their arrangement of points, classes and components of no class, and
    // each arrangement of one side is looked up once in each of the other: two arrangements,
    // as `(i, int) | (int, n + i)`, cost O(n log n) for the points `(i, n + i)`, though each
    // place alone has `n` tuples that hold any value there.
    let inputs = scaling::inputs(256, two_patterns);
    scaling::check("n points against n tuples of two arrangements", 256, |n| {
        let (points, open) = &inputs[&n];
        assert!(points.diff(open).tuples.is_empty());
        assert_eq!(points.meet(open).tuples.len(), n);
        assert_eq!(open.meet(points).tuples.len(), n);
    });
    // Complexity tradeoff (COMPLEXITY.md F127): as many arrangements as tuples cost the
    // product of the two sides, which no algorithm avoids unless the strong exponential time
    // hypothesis fails (the comment at `Near` in `zedc_types::ty`).
    let inputs = scaling::inputs(64, many_patterns);
    scaling::check_order("n tuples against n of n arrangements", 64, 2, |n| {
        let (ones, zeros) = &inputs[&n];
        let met = ones.meet(zeros).tuples.len();
        assert!(met <= n * n, "{met}");
        let left = ones.diff(zeros).tuples.len();
        assert!(left <= n, "{left}");
    });
}

/// Whether `a` and `b` share a value, checked to be the same both ways round.
fn meets(a: &str, b: &str) -> bool {
    let (a, b) = (ty(a), ty(b));
    let m = a.meets(&b);
    assert_eq!(m, b.meets(&a), "({a}) meets ({b}) one way only");
    m
}

#[test]
fn meets_compares_tuples_of_one_length_only() {
    assert!(!meets("(1, 2)", "(1, 2, 3)"));
    assert!(!meets(
        "(1, 2) | (1, 2, 3, 4)",
        "(1, 2, 3) | (1, 2, 3, 4, 5)"
    ));
    // A tuple of each length on both sides: only those of one length are compared.
    assert!(meets("(1, 2) | (1, 2, 3)", "(1, 2, 3)"));
    assert!(meets("(1, 2) | (1, 2, 3)", "(int, int, 3) | (5, 6)"));
    assert!(!meets("(1, 2) | (1, 2, 3)", "(int, int, 4) | (5, 6)"));
}

#[test]
fn meets_tells_apart_tuples_that_share_a_prefix() {
    assert!(!meets("(1, 2, 3)", "(1, 2, 4)"));
    assert!(meets("(1, 2, 3)", "(1, 2, int)"));
    assert!(!meets("(1, 2, 3) | (1, 2, 4)", "(1, 2, 5) | (1, 2, 6)"));
    assert!(meets("(1, 2, 3) | (1, 2, 4)", "(1, 2, 5) | (1, 2, 4)"));
    // The same prefix, then a class at the last place on one side and a value on the other.
    assert!(meets("(1, true, 1) | (1, true, 2)", "(1, bool, 2)"));
    assert!(!meets("(1, true, 1) | (1, true, 2)", "(1, bool, String)"));
    // Prefixes that are tuples themselves.
    assert!(!meets("((1, 2), 3) | ((1, 2), 4)", "((1, 2), 5)"));
    assert!(meets("((1, 2), 3) | ((1, 2), 4)", "((1, int), 4)"));
    assert!(!meets("((1, 2), 3) | ((1, 2), 4)", "((1, 3), int)"));
}

#[test]
fn meets_of_a_side_with_no_tuples_is_decided_by_the_rest() {
    assert!(!meets("int", "(1, 2)"));
    assert!(!meets("String | bool", "(1, 2) | (int, int, int)"));
    assert!(meets("int | (1, 2)", "int"));
    // An empty type shares no value with any.
    let empty = Ty::empty();
    assert!(!empty.meets(&ty("(1, 2)")) && !ty("(1, 2)").meets(&empty));
    assert!(!empty.meets(&empty));
}

#[test]
fn meets_of_one_tuple_against_many_finds_the_one_that_shares_a_value() {
    let many = ty("(0, 0) | (1, 1) | (2, 2) | (3, 3) | (4, 4) | (5, 5)");
    for (one, shares) in [
        ("(int, 5)", true),
        ("(5, int)", true),
        ("(4, 5)", false),
        ("(int, 6)", false),
        ("(int, bool)", false),
        ("(1 | String, 1)", true),
        ("(2 | String, 1)", false),
    ] {
        let one = ty(one);
        assert_eq!(one.meets(&many), shares, "({one}) meets ({many})");
        assert_eq!(many.meets(&one), shares, "({many}) meets ({one})");
    }
}

/// Unions of `n` tuples, as pairs `(t, u)` with whether `t` and `u` share a value: no two
/// tuples, or the last two only, so that a walk of every pair of one length compares `n^2`
/// pairs where a lookup of each tuple's own compares at most one.
fn meets_families(n: usize) -> Vec<(&'static str, Ty, Ty, bool)> {
    let rows = |f: &dyn Fn(usize) -> Ty| Ty::union_all(&(0..n).map(f).collect::<Vec<_>>());
    let pair = |a: Ty, b: Ty| Ty::tuple(vec![a, b]);
    vec![
        // `(i, n + i)` against `(i + 1, n + i)`: each pair differs at one place or both.
        (
            "points",
            rows(&|i| pair(int(i), int(n + i))),
            rows(&|i| pair(int(i + 1), int(n + i))),
            false,
        ),
        // The same, with the tuple `(n - 1, 2n - 1)` last on the other side too.
        (
            "the last pair",
            rows(&|i| pair(int(i), int(n + i))),
            Ty::union_all(&[
                rows(&|i| pair(int(i + 1), int(n + i))),
                pair(int(n - 1), int(2 * n - 1)),
            ]),
            true,
        ),
        // Two arrangements of points and `int` against points of other values.
        (
            "two arrangements",
            Ty::union_all(
                &(0..n)
                    .flat_map(|i| [pair(int(i), ty("int")), pair(ty("int"), int(n + i))])
                    .collect::<Vec<_>>(),
            ),
            rows(&|i| pair(int(2 * n + i), int(3 * n + i))),
            false,
        ),
        // Tuples of tuples that differ in the inner tuple.
        (
            "nested",
            rows(&|i| pair(pair(int(i), int(i)), ty("bool"))),
            rows(&|i| pair(pair(int(n + i), int(i)), ty("bool"))),
            false,
        ),
    ]
}

#[test]
fn meets_of_many_tuples_scales() {
    // Each tuple of one side is compared only with the tuples of the other that agree with it
    // at every place where both have a class or a value, found by key lookup.
    let inputs = scaling::inputs(256, meets_families);
    scaling::check("n tuples against n tuples, meets, four ways", 256, |n| {
        for (what, t, u, shares) in &inputs[&n] {
            assert_eq!(t.meets(u), *shares, "{what}");
            assert_eq!(u.meets(t), *shares, "{what}");
        }
    });
}

#[test]
fn meets_of_tuples_of_many_patterns_costs_the_patterns() {
    // Complexity tradeoff (COMPLEXITY.md F132): as many arrangements as tuples cost up to the
    // product of the two sides; whether any pair shares a value is the orthogonal vectors
    // problem, which no algorithm decides faster unless the strong exponential time hypothesis
    // fails (the comment at `Near` in `zedc_types::ty`).
    let inputs = scaling::inputs(64, |n| {
        let (ones, zeros) = many_patterns(n);
        let shares = !ones.meet(&zeros).tuples.is_empty();
        (ones, zeros, shares)
    });
    scaling::check_order("n tuples against n of n arrangements, meets", 64, 2, |n| {
        let (ones, zeros, shares) = &inputs[&n];
        assert_eq!(ones.meets(zeros), *shares);
    });
}

/// The tuple value of `xs`.
fn tv(xs: Vec<zed_kernel::value::Value>) -> zed_kernel::value::Value {
    zed_kernel::value::Value::tuple(xs)
}

/// The integer value `i`.
fn iv(i: usize) -> zed_kernel::value::Value {
    zed_kernel::value::Value::Int(i as i64)
}

/// The tuple of `k` components, each the one-component tuple `(t)` sharing one row. A copy of
/// a type copies its outer level, so `k` copies of `t` itself would be `k` nodes, each read
/// once; through the shared row, `t` is one node, read for each of the `k` components of a
/// value made by [`singles`].
fn shared(t: &Ty, k: usize) -> Ty {
    Ty::tuple(vec![Ty::tuple(vec![t.clone()]); k])
}

/// The tuple value of the one-component tuples `(v)` for each `v` of `vs`, for [`shared`].
fn singles(vs: impl Iterator<Item = zed_kernel::value::Value>) -> zed_kernel::value::Value {
    tv(vs.map(|v| tv(vec![v])).collect())
}

/// Whether `t` holds `v`, with `t`'s tuples read for many values in one walk: the tuple of
/// `k` copies of `(v)` is looked for in [`shared`]`(t, k)`, so the one node `t` is read for
/// `k` values (distinct copies of `v`), and the answer is that for `v` alone.
fn holds_many(t: &Ty, v: &zed_kernel::value::Value, k: usize) -> bool {
    let held = shared(t, k).contains(&singles((0..k).map(|_| v.clone())));
    assert_eq!(held, t.contains(v), "{t} holds {v:?} alone and {k} times");
    held
}

#[test]
fn contains_compares_tuples_of_one_length_only() {
    let t = ty("(1, 2) | (1, 2, 3)");
    for k in [1, 8] {
        assert!(holds_many(&t, &tv(vec![iv(1), iv(2)]), k));
        assert!(holds_many(&t, &tv(vec![iv(1), iv(2), iv(3)]), k));
        assert!(!holds_many(&t, &tv(vec![iv(1)]), k));
        assert!(!holds_many(&t, &tv(vec![iv(1), iv(2), iv(3), iv(4)]), k));
    }
}

#[test]
fn contains_finds_the_one_tuple_of_many_that_holds_a_value() {
    // Points, classes, atoms, strings and nested tuples, and components of no class.
    let many = ty(
        "(0, 0) | (1, 1) | (2, int) | (int, 3) | (#a, String) | (\"s\", bool) \
                   | ((1, 2), 4) | ((int, 2), 5) | (1 | String, 6)",
    );
    use zed_kernel::value::Value;
    for (v, held) in [
        (tv(vec![iv(1), iv(1)]), true),
        (tv(vec![iv(1), iv(0)]), false),
        (tv(vec![iv(2), iv(9)]), true),
        (tv(vec![iv(9), iv(3)]), true),
        (tv(vec![iv(9), iv(4)]), false),
        (tv(vec![Value::atom("a"), Value::str("x")]), true),
        (tv(vec![Value::atom("b"), Value::str("x")]), false),
        (tv(vec![Value::atom("a"), iv(1)]), false),
        (tv(vec![Value::str("s"), Value::Bool(true)]), true),
        (tv(vec![Value::str("t"), Value::Bool(true)]), false),
        (tv(vec![tv(vec![iv(1), iv(2)]), iv(4)]), true),
        (tv(vec![tv(vec![iv(1), iv(3)]), iv(4)]), false),
        (tv(vec![tv(vec![iv(7), iv(2)]), iv(5)]), true),
        (tv(vec![tv(vec![iv(7), iv(2), iv(1)]), iv(5)]), false),
        (tv(vec![Value::str("u"), iv(6)]), true),
        (tv(vec![iv(2), iv(6)]), true),
        (tv(vec![Value::float(1.0), iv(6)]), false),
    ] {
        for k in [1, 2, 8, 40] {
            assert_eq!(
                holds_many(&many, &v, k),
                held,
                "{many} holds {v:?}, {k} times"
            );
        }
    }
}

#[test]
fn contains_of_a_type_open_at_a_place_holds_any_value_there() {
    // A variable or the unknown holds every value, so every value is looked for in its tuples.
    use zed_kernel::value::Value;
    for t in [
        Ty::union_all(&[
            Ty::tuple(vec![Ty::var("T".into()), int(1)]),
            Ty::tuple(vec![int(0), int(2)]),
        ]),
        Ty::union_all(&[
            Ty::tuple(vec![Ty::dynamic(), int(1)]),
            Ty::tuple(vec![int(0), int(2)]),
        ]),
    ] {
        for k in [1, 40] {
            assert!(holds_many(&t, &tv(vec![Value::str("x"), iv(1)]), k));
            assert!(holds_many(&t, &tv(vec![iv(0), iv(2)]), k));
            assert!(!holds_many(&t, &tv(vec![Value::str("x"), iv(2)]), k));
        }
    }
}

/// Unions of `n` tuples, each with a tuple value of `n` components looked for in it, and
/// whether the union holds every component: each held by one tuple, or each but the last,
/// so that a scan of every tuple for each component reads `n^2` tuples where a lookup of each
/// component's own reads one.
fn contains_families(n: usize) -> Vec<(&'static str, Ty, zed_kernel::value::Value, bool)> {
    use zed_kernel::value::Value;
    let rows = |f: &dyn Fn(usize) -> Ty| Ty::union_all(&(0..n).map(f).collect::<Vec<_>>());
    let pair = |a: Ty, b: Ty| Ty::tuple(vec![a, b]);
    // The union read for `n` values in one walk ([`shared`]), and the values.
    let wide = |u: Ty| shared(&u, n);
    let values = |f: &dyn Fn(usize) -> Value| singles((0..n).map(f));
    vec![
        // `(i, n + i)`, each value held by its own tuple, in reverse order.
        (
            "points",
            wide(rows(&|i| pair(int(i), int(n + i)))),
            values(&|i| tv(vec![iv(n - 1 - i), iv(2 * n - 1 - i)])),
            true,
        ),
        // The same, the last value held by none.
        (
            "the last held by none",
            wide(rows(&|i| pair(int(i), int(n + i)))),
            values(&|i| match i + 1 == n {
                true => tv(vec![iv(0), iv(n + 1)]),
                false => tv(vec![iv(n - 1 - i), iv(2 * n - 1 - i)]),
            }),
            false,
        ),
        // Two arrangements of points and `int`, each value held by the second only.
        (
            "two arrangements",
            wide(Ty::union_all(
                &(0..n)
                    .flat_map(|i| [pair(int(i), ty("int")), pair(ty("int"), int(n + i))])
                    .collect::<Vec<_>>(),
            )),
            values(&|i| tv(vec![iv(5 * n + i), iv(2 * n - 1 - i)])),
            true,
        ),
        // Atoms and strings, and tuples of tuples that differ in the inner tuple.
        (
            "atoms and nested",
            wide(rows(&|i| {
                pair(pair(int(i), int(i)), Ty::lit(&Value::str(&format!("s{i}"))))
            })),
            values(&|i| {
                tv(vec![
                    tv(vec![iv(n - 1 - i), iv(n - 1 - i)]),
                    Value::str(&format!("s{}", n - 1 - i)),
                ])
            }),
            true,
        ),
    ]
}

#[test]
fn contains_of_many_tuples_scales() {
    // Each component of the value is looked for only in the tuples of the union that agree
    // with it at every place where they have a class or a value, found by key lookup.
    let inputs = scaling::inputs(256, contains_families);
    scaling::check(
        "n tuple values in n tuples, contains, four ways",
        256,
        |n| {
            for (what, t, v, held) in &inputs[&n] {
                assert_eq!(t.contains(v), *held, "{what}");
            }
        },
    );
}

#[test]
fn contains_of_tuples_of_many_patterns_costs_the_patterns() {
    // Complexity tradeoff (COMPLEXITY.md F133): as many arrangements as tuples cost up to the
    // product of the tuples and the values; whether a tuple holds a value is the orthogonal
    // vectors problem, which no algorithm decides faster unless the strong exponential time
    // hypothesis fails (the comment at `Holders` in `zedc_types::ty`).
    use zed_kernel::value::Value;
    let inputs = scaling::inputs(128, |n| {
        let width = 2 * n.ilog2() as usize;
        // A different arrangement for each `i`, never all `int`, which would hold every value.
        let bits =
            |i: usize| ((i as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> (64 - width)) | 1;
        // The tuple `i`: the point 0 where `bits(i)` has a 1, `int` elsewhere.
        let rows: Vec<Ty> = (0..n)
            .map(|i| {
                Ty::tuple(
                    (0..width)
                        .map(|j| match bits(i) >> j & 1 {
                            1 => int(0),
                            _ => ty("int"),
                        })
                        .collect(),
                )
            })
            .collect();
        // The value `i`: 0 where `bits(i)` has a 1, 1 elsewhere, held by the tuple `i` and by
        // each tuple whose points are among those places, which few are; so the tuples before
        // the `i`th are looked through, group by group, for most values.
        let value = |i: usize| {
            tv((0..width)
                .map(|j| Value::Int(i64::from(bits(i) >> j & 1 == 0)))
                .collect())
        };
        (shared(&Ty::union_all(&rows), n), singles((0..n).map(value)))
    });
    scaling::check_order(
        "n tuple values in n tuples of n arrangements",
        128,
        2,
        |n| {
            let (t, v) = &inputs[&n];
            assert!(t.contains(v));
        },
    );
}
