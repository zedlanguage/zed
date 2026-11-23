//! The kind-wide types (step L1.40d, DESIGN.md sec:type_language): `#_` is every atom, `(..)`
//! every tuple, `{..}` every struct, `#a(..)` the atom `#a` with any payload and `#a()` the atom
//! `#a` with the empty payload. `..` stands alone between its brackets. Each form parses, is the
//! set it names in the kernel and in the checker, and prints back as text that reads back as the
//! same type.

use std::collections::BTreeMap;

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

/// Item PRINT-fmt-audit: the kernel sets in a compiler type are written together by name
/// (`Type::surfaces_by_name`), each at the place it stands in the compiler's text, and a part
/// used twice or more among them gets a definition placed before the whole text. Before, each
/// set was written with its own definitions, which stood in the middle of the compiler's text
/// where a set was not first:
///
/// - `type Part1 = int | #x;`, then `((int) -> int, (Part1, Part1))` on the next line, was
///   `((int) -> int, type Part1 = int | #x; (Part1, Part1))`, which no parser reads
/// - `type Part1 = int | #x;`, then `((int) -> int, Part1, Part1)`, was
///   `((int) -> int, int | #x, int | #x)`: a part used in two sets is now a part used twice
///
/// Item PRINT-group-site-defs put each definition on a line of its own, as a user declares it;
/// before, they shared the line of the type.
///
/// The first version of this item wrote a part used twice at each use, `(int | #x, int | #x)`,
/// which grows as 2^k for a part shared at k levels (COMPLEXITY.md K91). `int | (int ->? int)`
/// and `(int ->? int) | (bool, bool)` are written as before. Each text parses as a type after
/// its definitions, each of which parses; with the definitions written in place, a set reads
/// back as the same type, and a function, which the reader makes the checker's own function
/// type, reads back as that type again from its own text.
#[test]
fn the_kernel_sets_in_a_compiler_type_put_their_definitions_first() {
    let int_or_x = &Type::int() | &Type::atom("x");
    let shared = tuple(&[int_or_x.clone(), int_or_x.clone()]);
    let partial = Type::partial(Type::int(), Type::int());
    let f = ty("(int) -> int");
    // Each type, its text, and whether it is a set of values with no function.
    for (t, text, set) in [
        (
            Ty::set(shared.clone()),
            "type Part1 = int | #x;\n(Part1, Part1)",
            true,
        ),
        (
            Ty::set(&shared | &Type::atom("y")),
            "type Part1 = int | #x;\n(Part1, Part1) | #y",
            true,
        ),
        (
            ty("(bool, bool)").union(&Ty::set(shared.clone())),
            "type Part1 = int | #x;\n(Part1, Part1) | (bool, bool)",
            true,
        ),
        (
            Ty::tuple(vec![f.clone(), Ty::set(shared.clone())]),
            "type Part1 = int | #x;\n(int -> int, (Part1, Part1))",
            false,
        ),
        (
            Ty::tuple(vec![f, Ty::set(int_or_x.clone()), Ty::set(int_or_x)]),
            "type Part1 = int | #x;\n(int -> int, Part1, Part1)",
            false,
        ),
        (
            Ty::set(&Type::int() | &partial),
            "int | (int ->? int)",
            false,
        ),
        (
            ty("(bool, bool)").union(&Ty::set(partial.clone())),
            "(bool, bool) | (int ->? int)",
            false,
        ),
    ] {
        assert_eq!(t.to_string(), text);
        let (defs, root) = split_definitions(text);
        let tokens = lex_fence(root).unwrap();
        parse(root, &tokens, "Type", TOP).unwrap_or_else(|e| panic!("{root}: {e:?}"));
        for (name, body) in &defs {
            let def = format!("type {name} = {body};");
            let tokens = lex_fence(&def).unwrap();
            parse(&def, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{def}: {e:?}"));
        }
        let inlined = inline(&defs, root);
        let back = ty(&inlined);
        match set {
            true => assert!(back.subtype(&t) && t.subtype(&back), "{text}"),
            false => assert_eq!(ty(&inline_text(&back.to_string())), back, "{text}"),
        }
    }
}

/// The definitions `type Tk = body;`, a line each, that open `text`, and the type after them.
fn split_definitions(text: &str) -> (Vec<(&str, &str)>, &str) {
    let mut defs = Vec::new();
    let mut rest = text;
    while let Some(def) = rest.strip_prefix("type ") {
        let (name, def) = def.split_once(" = ").expect("a definition has a body");
        let (body, after) = def
            .split_once(";\n")
            .expect("a definition ends its line with `;`");
        defs.push((name, body));
        rest = after;
    }
    (defs, rest)
}

/// `text` with each name `Tk` of `defs` replaced by its body in parentheses, the bodies
/// themselves first.
fn inline(defs: &[(&str, &str)], text: &str) -> String {
    let mut bodies: BTreeMap<&str, String> = BTreeMap::new();
    for (name, body) in defs {
        let body = replace_names(&bodies, body);
        bodies.insert(name, body);
    }
    replace_names(&bodies, text)
}

/// `text` with no definitions: its own written in place.
fn inline_text(text: &str) -> String {
    let (defs, root) = split_definitions(text);
    inline(&defs, root)
}

/// `text` with each whole word that `bodies` names replaced by `(body)`.
fn replace_names(bodies: &BTreeMap<&str, String>, text: &str) -> String {
    let mut out = String::new();
    let mut word = String::new();
    let flush = |word: &mut String, out: &mut String| {
        match bodies.get(word.as_str()) {
            Some(body) => {
                out.push('(');
                out.push_str(body);
                out.push(')');
            }
            None => out.push_str(word),
        }
        word.clear();
    };
    for c in text.chars() {
        if c.is_alphanumeric() || c == '_' {
            word.push(c);
        } else {
            flush(&mut word, &mut out);
            out.push(c);
        }
    }
    flush(&mut word, &mut out);
    out
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

/// The checker's type of `n` tuple shapes `(i, i)`, and `(..) \ (0, 0)` as its kind-wide part.
fn shapes(n: usize) -> (Ty, Ty) {
    let lit = |i: usize| Ty::lit(&zed_kernel::value::Value::Int(i as i64));
    let ts: Vec<Ty> = (0..n).map(|i| Ty::tuple(vec![lit(i), lit(i)])).collect();
    (Ty::union_all(&ts), ty("(..) \\ (0, 0)"))
}

/// What the last note of a rejection for want of data says.
const DATA: &str = "data is a value that holds no function at any depth";

/// The notes of the one error of `text`, a rejection for want of data.
fn data_notes(text: &str) -> Vec<String> {
    let (i, _) = zed_tests::step_helpers::l01_26_type_resolution::info(text);
    assert_eq!(i.errors.len(), 1, "{text}: {:?}", i.errors);
    i.errors[0]
        .notes
        .iter()
        .map(|n| n.text.to_string())
        .collect()
}

#[test]
fn a_use_that_takes_data_refuses_every_tuple() {
    // A block that ends `return h, 1` builds a tuple that holds a function, and `(..)` takes it,
    // so `==`, interpolation and `String` on a value of `(..)` are refused where they are
    // written, at any depth, as they are on a value whose function is known.
    let errors = zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let call = "g() = f(x: { h(y) = y; return h, 1; });\n";
    for (body, does, at) in [
        ("x == x", "compare", "x == x"),
        ("\"a${x}b\"", "show", "x"),
        ("String(x)", "show", "String(x)"),
    ] {
        let text = format!("f(x: (..)) = {body};\n{call}");
        let want = format!(
            "Cannot {does} a value that may hold a function: `x : (..)` in `{body}`. [{at}]"
        );
        assert_eq!(errors(&text), [want], "{text}");
        assert_eq!(
            data_notes(&text),
            ["`(..)` holds every value of its shape, functions too", DATA],
            "{text}"
        );
    }
    let text = "f(x: (int, (..))) = x == x;\n";
    assert_eq!(
        errors(text),
        [
            "Cannot compare a value that may hold a function: `x : (int, (..))` in `x == x`. [x == x]"
        ]
    );
    assert_eq!(
        data_notes(text),
        [
            "`(int, (..))` holds `(..)`, which holds every value of its shape, functions too",
            DATA
        ]
    );
    // A tuple whose shape is written holds what its components hold.
    assert_eq!(errors("f(x: (int, int)) = x == x;\n"), Vec::<String>::new());
}

#[test]
fn a_kind_wide_part_met_with_a_written_shape_holds_what_the_shape_holds() {
    // `(..)` less a tuple, met with a written pair of scalars, holds only pairs of scalars:
    // data, which `String` and `==` take. The checker keeps the part of the pair the
    // difference holds as a kernel tuple type beside the kind-wide part, and reads every
    // tuple type there as `(..)`. The second type is the smallest found whose meet reaches
    // the boxes of a meet of unions with an unbounded column in the smaller operand
    // (`types::join_of`, TESTS-coverage-projection-paths): it holds `(#a, #b)` and `(#b, #a)`
    // and nothing else, which a search of the pairs of 0, 1, 7, `#a` and `#b` confirms in the
    // kernel test `l01_23_subtyping::meet_join_oracle`.
    let errors = zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let s = "int | #a | #b";
    let side = |a: &str| format!("((..) \\ ({a}, {a})) & ({s}, {s}) & (({s}, {a}) | ({a}, {s}))");
    for text in [
        "f(p: ((..) \\ (#a, #a)) & (int | #a, int | #a)) = String(p);\n".to_string(),
        format!(
            "f(p: ({}) & ({})) = if p == (#a, #b) {{ 1 }} else {{ 0 }};\n",
            side("#a"),
            side("#b")
        ),
        // `==` takes data as `String` does.
        "f(p: ((..) \\ (#a, #a)) & (int | #a, int | #a)) = p == p;\n".to_string(),
        // A shape nested in the shape is kept as written, at each depth.
        "f(p: ((..) \\ (#a, (#a, #a))) & (int | #a, (int | #a, int | #a))) = String(p);\n"
            .to_string(),
        // A component that holds every atom holds data.
        "f(p: ((..) \\ (#b, #b)) & (#_ | int, int | #b)) = String(p);\n".to_string(),
        // Narrowing by `is` meets the shape with the kind-wide part; by `is not` takes it away.
        "f(p: (int | #b, int | #b)) = if p is (..) \\ (#b, #b) { String(p) } else { \"\" };\n"
            .to_string(),
        "f(p: (int | #b, int | #b) | (..)) = if p is not (..) \\ (#b, #b) { String(p) } else { \"\" };\n"
            .to_string(),
        // A component atom with a payload keeps its payload in the part kept beside the
        // kind-wide part: `#a(1)` holds data, where `#a` with any payload may hold a function.
        // By `is` the shape is met with the kind-wide part; by `is not` the rest of the shape
        // is left beside it.
        "g(c: bool) = (if c { #a(1) } else { #b }, #b);\nf(c: bool) = {\n    p = g(c: c);\n    if p is (..) \\ (#b, #b) { String(p) } else { \"\" }\n};\n"
            .to_string(),
        "g(c: bool) = (if c { #a(1) } else { #b }, #b);\nf(c: bool) = {\n    p = g(c: c);\n    if p is not (..) \\ (#b, #b) { String(p) } else { \"\" }\n};\n"
            .to_string(),
        "g(c: bool) = (if c { #a(1) } else { #b }, #b);\nf(c: bool) = {\n    p = g(c: c);\n    if p is not (..) \\ (#_, #b) { String(p) } else { \"\" }\n};\n"
            .to_string(),
        "g(c: bool) = (if c { #a(1) } else { #b }, #b);\nf(c: bool) = {\n    p = g(c: c);\n    if p is not (..) \\ (#_, #b) { \"\" } else { String(p) }\n};\n"
            .to_string(),
    ] {
        assert_eq!(errors(&text), Vec::<String>::new(), "{text}");
    }
}

#[test]
fn a_kind_wide_part_met_with_a_shape_that_holds_one_may_hold_a_function() {
    // The shape's own component `(..)`, at the outer level or nested, holds every tuple,
    // functions among them, and the meet keeps it. The message writes the value's type and
    // the part of it that may hold a function.
    let errors = zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    for (text, value) in [
        (
            "f(p: ((..) \\ (#a, #a)) & ((..) | #a, int | #a)) = String(p);\n",
            "((..) | #a, int | #a) \\ (#a, #a)",
        ),
        (
            "f(p: ((..) \\ (#a, #a)) & ((int, (..)) | #a, int | #a)) = String(p);\n",
            "((int, (..)) | #a, int | #a) \\ (#a, #a)",
        ),
    ] {
        let want = format!(
            "Cannot show a value that may hold a function: `p : {value}` in `String(p)`. [String(p)]"
        );
        assert_eq!(errors(text), [want], "{text}");
        let holds =
            format!("`{value}` holds `(..)`, which holds every value of its shape, functions too");
        assert_eq!(data_notes(text), [holds.as_str(), DATA], "{text}");
    }
}

#[test]
fn a_tuple_type_that_is_only_subtracted_holds_no_function() {
    // A tuple type taken away holds none of the values left, so its `(..)` is not read as a
    // function the value may hold (COMPLEXITY.md K103): each parameter below holds pairs of
    // `int`s and `#a` alone, data, which `String` and `==` take.
    let errors = zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    for text in [
        // The pair with `(..)` is taken from every tuple, and the rest met with a pair of
        // data: what is left is `(int, #a)`.
        "f(p: ((..) \\ (int | (..), int)) & (int, int | #a)) = String(p);\n",
        // The same in a union with another pair of data.
        "f(p: (((..) \\ (int | (..), int)) & (int, int | #a)) | (#a, #a)) = String(p);\n",
        // Two differences met, each taking away a pair with `(..)` on one side.
        "f(p: ((..) \\ ((..), int)) & ((..) \\ (int, (..))) & (int, int | #a)) = p == p;\n",
        // Taken away three times over, which is taken away once.
        "f(p: ((..) \\ ((..) \\ ((..) \\ ((..), int)))) & (int, int | #a)) = String(p);\n",
    ] {
        assert_eq!(errors(text), Vec::<String>::new(), "{text}");
    }
}

#[test]
fn a_tuple_type_subtracted_twice_or_left_beside_a_difference_may_hold_a_function() {
    // A tuple type taken away twice is kept, and a kind-wide part that a difference does not
    // take away stays in the value.
    let errors = zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    for (text, value) in [
        (
            "f(p: (..) \\ ((..) \\ ((..), int))) = String(p);\n",
            "((..), int)",
        ),
        (
            "f(p: (int, (..)) \\ (int, (int, int))) = String(p);\n",
            "(int, (..)) \\ (int, (int, int))",
        ),
        (
            "f(p: (((..) \\ (int | (..), int)) & (int, int | #a)) | (#a, (..))) = String(p);\n",
            "((int, int | #a) \\ (int | (..), int)) | (#a, (..))",
        ),
    ] {
        let want = format!(
            "Cannot show a value that may hold a function: `p : {value}` in `String(p)`. [String(p)]"
        );
        assert_eq!(errors(text), [want], "{text}");
        let holds =
            format!("`{value}` holds `(..)`, which holds every value of its shape, functions too");
        assert_eq!(data_notes(text), [holds.as_str(), DATA], "{text}");
    }
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
        ("#a((int) -> 1)", "#a((int) -> int)"),
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
        // A domain is exact (DESIGN.md sec:type_language, "plain `K -> V` is exact"): a
        // function taking more keys is not one taking fewer (FAIL-types-fn-param-exact-domain).
        ("#a((int | String) -> int)", "#a((int) -> int)"),
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
    // Three functions of `t`, equal to none of the expected type's and of one domain, each
    // meet all three of its at one place, 9 pairs for 6 functions: which fits which is not
    // compared (COMPLEXITY.md F124), and the clause says so.
    let (t, u) = (
        ty("((int) -> 1, 1) | ((int) -> 2, 2) | ((int) -> 3, 3)"),
        ty("((int) -> 1 | 2, int) | ((int) -> 2 | 3, int) | ((int) -> 1 | 3, int)"),
    );
    assert!(!t.subtype(&u));
    assert!(
        t.refused(&u).contains("because two or more functions"),
        "{}",
        t.refused(&u)
    );
    // Of three domains, they are split by domain and each part is compared alone
    // (PERF-types-loose-pairing-dense; refused before). A domain is exact (DESIGN.md
    // sec:type_language), so each function of `t` fits the expected function of its own
    // domain by its narrower result (FAIL-types-fn-param-exact-domain).
    let (t, u) = (
        ty("((int) -> 1, 1) | ((String) -> 1, 2) | ((f64) -> 1, 3)"),
        ty("((int) -> int, int) | ((String) -> int, int) | ((f64) -> int, int)"),
    );
    assert!(t.subtype(&u));
    assert_eq!(t.refused(&u), "");
    // One function on either side is compared with each on the other.
    for (member, whole) in [
        (
            "((int) -> 1, 1)",
            "((int) -> int, int) | ((String) -> int, int)",
        ),
        ("((int) -> 1, 1) | ((int) -> 0, 2)", "((int) -> int, int)"),
        // Functions equal on both sides are matched by equality, however many.
        (
            "((int) -> int, 1) | ((String) -> int, 2)",
            "((int) -> int, int) | ((String) -> int, int)",
        ),
        // Two a side, each meeting both: 4 pairs, no more than the 4 functions, so each is
        // compared (FAIL-types-loose-pairing-non-star; it was refused).
        (
            "((int) -> 1, 1) | ((String) -> 1, 2)",
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
        "; the checker could not decide this, so it is not proved wrong\n  because the \
         payloads #a(3, 5) and #a(4, 6) may each be held by one of the shapes \
         #a(1 | 2, _) | #a(int, _), which are told apart only at component 1, where they agree \
         with both, and neither is held by the first of those shapes; which shape holds each \
         decides what the type variables are bound to, and the checker looks through those \
         shapes for one of the two only; to repair it, give #a(3, 5) a shape of its own, \
         written after the first of those shapes and before the second, the same as the shape \
         that should hold it except at component 1, where it is 3: `#a(3, …)`, with that \
         shape's other components in place of each `…`; or test the value with `is` first, so \
         that each test meets one of the two"
    );
    // The repair applied: `#a(3, U)` written after `#a(1 | 2, T)` and before `#a(int, U)`,
    // which holds #a(3, 5). The comparison is decided and binds `U` as the rule of one shape
    // does.
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
    assert!(why.contains("not proved wrong\n  because the tuples (3, 5) and (4, 6) "));
    assert!(why.contains(
        "give (3, 5) a shape of its own, written after the first of those shapes and before \
         the second, the same as the shape that should hold it except at component 1, where it \
         is 3: `(3, …)`"
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
        "to repair it, give (3, bool) a shape of its own, written after the first of those \
         shapes and before the second, the same as the shape that should hold it except at \
         component 2, where it is bool: `(…, bool)`, with that shape's other components in place of each `…`; or test the \
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

#[test]
fn a_shape_of_its_own_comes_before_the_second_shape_of_the_bucket() {
    // PROOF-types-own-shape-first-of-bucket: `(5 | 6, V)` is a second shape of the bucket
    // `int` at component 1, between the first and the shape that holds (3, 5). The shape of
    // its own written just before `(int, U)` came after it, so (3, 5) still failed `(1 | 2, T)`
    // and searched the bucket past it at `(5 | 6, V)`, as (4, 6) does, and the repaired type
    // was refused for the same reason. Written before the second shape of the bucket, it is
    // met before any shape of the bucket after the first.
    let rows = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![ty("5 | 6"), var("V")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    let l = ty("(3, 5) | (4, 6)");
    assert_eq!(bound(&l, &rows), None);
    let why = l.refused(&rows);
    assert!(
        why.contains(
            "give (3, 5) a shape of its own, written after the first of those shapes and \
             before the second, the same as the shape that should hold it except at component \
             1, where it is 3: `(3, …)`, with that shape's other components in place of each \
             `…`; or test the value with `is` first"
        ),
        "{why}"
    );
    // Placed just before `(int, U)`, the shape that holds (3, 5), it does not repair it.
    let late = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![ty("5 | 6"), var("V")]),
        Ty::tuple(vec![int(3), var("U")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    assert_ne!(l.refused(&late), "");
    // Placed as the message says, it does, and (4, 6) is held by `(int, U)`.
    let repaired = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![int(3), var("U")]),
        Ty::tuple(vec![ty("5 | 6"), var("V")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    assert_eq!(l.refused(&repaired), "");
    assert_eq!(
        bound(&l, &repaired),
        Some(vec![("U".into(), "5 | 6".into())])
    );
    // A shape written before it with a class at the same places and the same key, `(3, bool)`,
    // which (3, 5) fails: (3, 5) searches that bucket past it, but (4, 6), of key 4 there, is
    // not in that bucket, so the repaired type is still decided.
    let earlier = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![int(3), ty("bool | String")]),
        Ty::tuple(vec![int(3), var("U")]),
        Ty::tuple(vec![ty("5 | 6"), var("V")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    assert_eq!(l.refused(&earlier), "");
    assert_eq!(
        bound(&l, &earlier),
        Some(vec![("U".into(), "5 | 6".into())])
    );
}

#[test]
fn a_shape_of_its_own_repairs_with_a_shape_between_the_second_of_the_bucket_and_the_holder() {
    // TEST-own-shape-repair-bindings: `(7 | 8, W)` stands between `(5 | 6, V)`, the second
    // shape of the bucket `int` at component 1, and `(int, U)`, the shape that holds (3, 5).
    // The message is the one of the two-shape case, and the repair it names, `(3, U)` after
    // the first shape, decides the type with the same bindings: (3, 5) is held by `(3, U)`,
    // (4, 6) passes `(5 | 6, V)` and `(7 | 8, W)` at component 0 and is held by `(int, U)`,
    // so `U` is `5 | 6`, and no other shape raises a refusal.
    let rows = |own: bool| {
        let mut shapes = vec![Ty::tuple(vec![ty("1 | 2"), var("T")])];
        if own {
            shapes.push(Ty::tuple(vec![int(3), var("U")]));
        }
        shapes.extend([
            Ty::tuple(vec![ty("5 | 6"), var("V")]),
            Ty::tuple(vec![ty("7 | 8"), var("W")]),
            Ty::tuple(vec![ty("int"), var("U")]),
        ]);
        Ty::union_all(&shapes)
    };
    let l = ty("(3, 5) | (4, 6)");
    assert_eq!(bound(&l, &rows(false)), None);
    let why = l.refused(&rows(false));
    assert!(
        why.contains(
            "give (3, 5) a shape of its own, written after the first of those shapes and \
             before the second"
        ),
        "{why}"
    );
    assert_eq!(l.refused(&rows(true)), "");
    assert_eq!(
        bound(&l, &rows(true)),
        Some(vec![("U".into(), "5 | 6".into())])
    );
    // A value that also meets the shape between, (7, 1): now (4, 6) and (7, 1) both search the
    // bucket past its first shape, and the message names the next repair, `(4, …)`. With it
    // written after `(3, U)`, (7, 1) is held by `(7 | 8, W)` and the type is decided.
    let l = ty("(3, 5) | (4, 6) | (7, 1)");
    let why = l.refused(&rows(true));
    assert!(
        why.contains("give (4, 6) a shape of its own, written after the first of those shapes"),
        "{why}"
    );
    let both = Ty::union_all(&[
        Ty::tuple(vec![ty("1 | 2"), var("T")]),
        Ty::tuple(vec![int(3), var("U")]),
        Ty::tuple(vec![int(4), var("U")]),
        Ty::tuple(vec![ty("5 | 6"), var("V")]),
        Ty::tuple(vec![ty("7 | 8"), var("W")]),
        Ty::tuple(vec![ty("int"), var("U")]),
    ]);
    assert_eq!(l.refused(&both), "");
    assert_eq!(
        bound(&l, &both),
        Some(vec![("U".into(), "5 | 6".into()), ("W".into(), "1".into())])
    );
}

#[test]
fn a_shape_of_its_own_of_one_component_is_written_whole_with_its_comma() {
    // Tuples of one component: the shape of its own is `((3, 5),)`, as `((3, 5))` reads as
    // `(3, 5)`, and it has no other components to fill in.
    let one = |a: Ty, b: Ty| Ty::tuple(vec![Ty::tuple(vec![a, b])]);
    let rows = Ty::union_all(&[one(ty("1 | 2"), var("T")), one(ty("int"), var("U"))]);
    let l = ty("((3, 5),) | ((4, 6),)");
    assert_eq!(bound(&l, &rows), None);
    let why = l.refused(&rows);
    assert!(
        why.contains(
            "to repair it, give ((3, 5),) a shape of its own, written after the first of those \
             shapes and before the second: `((3, 5),)`; or test the value with `is` first"
        ),
        "{why}"
    );
    // The repair applied is decided.
    let repaired = Ty::union_all(&[
        one(ty("1 | 2"), var("T")),
        ty("((3, 5),)"),
        one(ty("int"), var("U")),
    ]);
    assert_eq!(l.refused(&repaired), "");
    assert_eq!(bound(&l, &repaired), Some(vec![("U".into(), "6".into())]));
    // A payload of one component: `#a((3, 5))` is already written so, and is offered whole.
    let r = with_payloads(
        "a",
        vec![
            vec![Ty::tuple(vec![ty("1 | 2"), var("T")])],
            vec![Ty::tuple(vec![ty("int"), var("U")])],
        ],
    );
    let l = with_payloads("a", vec![vec![ty("(3, 5)")], vec![ty("(4, 6)")]]);
    assert_eq!(bound(&l, &r), None);
    let why = l.refused(&r);
    assert!(
        why.contains(
            "to repair it, give #a((3, 5)) a shape of its own, written after the first of those \
             shapes and before the second: `#a((3, 5))`; or test the value with `is` first"
        ),
        "{why}"
    );
}

#[test]
fn a_program_is_offered_a_one_component_shape_as_a_type_it_can_write() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // Accepted: at `U` = `int`, `g`'s domain, `((int, bool) | (int, bool, bool),) | ((int, int)
    // | (int, int, int),)`, is `f`'s, value for value. Before FAIL-print-two-variables-one-name
    // it was refused, as both tuples searched past the first shape, which holds no variable
    // and neither tuple; that shape is now left out uncounted (`Searched::closed_left_out`).
    let held = "p(f: (x: ((int, bool) | (int, bool, bool),) | ((int, int),) | ((int, int, int),)) \
                -> int) = 0;\n\
                q(g: (x: ((int, bool) | (int, bool, bool),) | ((int, U) | (int, U, U),)) -> int \
                for U in int | f64) = p(f: g);\n";
    assert_eq!(type_errors(held), Vec::<String>::new());
    // `g` takes tuples of one pair or triple, which may each be held by a later shape of the
    // bucket of pairs and triples: the repair writes the shape of its own as a tuple of one.
    // The first shape holds a function, so it is not left out, and the bucket is refused. A
    // domain is exact (DESIGN.md sec:type_language), so `f` also takes the tuples of `g`'s
    // first shape (FAIL-types-fn-param-exact-domain).
    let src = "p(f: (x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
               | ((int, int),) | ((int, int, int),)) -> int) = 0;\n\
               q(g: (x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
               | ((int, U) | (int, U, U),)) -> int for U in int | f64) = p(f: g);\n";
    let errs = type_errors(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        errs[0].contains(
            "the tuples ((int, int),) and ((int, int, int),) may each be held by one of the \
             shapes"
        ),
        "{errs:?}"
    );
    assert!(
        errs[0].contains(
            "to repair it, give ((int, int),) a shape of its own, written after the first of \
             those shapes and before the second: `((int, int),)`; or test the value with `is` \
             first"
        ),
        "{errs:?}"
    );
    // The repair written into the program is accepted.
    let repaired = "p(f: (x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
                    | ((int, int),) | ((int, int, int),)) -> int) = 0;\n\
                    q(g: (x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
                    | ((int, int),) | ((int, U) | (int, U, U),)) -> int for U in int | f64) \
                    = p(f: g);\n";
    assert_eq!(type_errors(repaired), Vec::<String>::new());
}

#[test]
fn a_bounded_type_variable_in_a_refused_bucket_prints_by_name_with_where_it_is_bound() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // `U` is bounded by `int` in `g`'s type: the bucket prints it by name, once or twice
    // (DESIGN.md sec:diagnostics, "Types in a message"), and the message says which `for`
    // binds it, since the bucket is printed apart from `g`'s type. A domain is exact (DESIGN.md
    // sec:type_language), so `f` also takes the tuples of `g`'s first shape
    // (FAIL-types-fn-param-exact-domain).
    //
    // With a first shape free of variables, that shape is left out uncounted
    // (`Searched::closed_left_out`, FAIL-print-two-variables-one-name) and the bucket is not
    // refused. `((int, bool) | (int, bool, bool),) | ((int, U) | (int, U, U),)` is then
    // accepted, rightly: at `U` = `int` it is `f`'s domain, value for value.
    // `((int, bool) | (int, bool, bool),) | ((int, U) | (int, bool, bool),)` is then not taken,
    // rightly: it holds `((int, int, int),)` at no `U`, and `f` takes that tuple.
    let plain = "p(f: (x: ((int, bool) | (int, bool, bool),) | ((int, int),) \
                 | ((int, int, int),)) -> int) = 0;\n";
    let held = format!(
        "{plain}q(g: (x: ((int, bool) | (int, bool, bool),) | ((int, U) | (int, U, U),)) -> int \
         for U in int | f64) = p(f: g);\n"
    );
    assert_eq!(type_errors(&held), Vec::<String>::new());
    let lacking = format!(
        "{plain}q(g: (x: ((int, bool) | (int, bool, bool),) | ((int, U) | (int, bool, bool),)) \
         -> int for U in int | f64) = p(f: g);\n"
    );
    let errs = type_errors(&lacking);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].starts_with("`p` does not take"), "{errs:?}");
    // The first shape below holds a function, so it is not left out, and the bucket is refused.
    let p = "p(f: (x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
             | ((int, int),) | ((int, int, int),)) -> int) = 0;\n";
    for (bucket, said) in [
        (
            "((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
             | ((int, U) | (int, U, U),)",
            "((x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
             | ((int, U) | (int, U, U),)) -> int for U in int | f64)",
        ),
        (
            "((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
             | ((int, U) | (int, bool, bool),)",
            "((x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
             | ((int, U) | (int, bool, bool),)) -> int for U in int | f64)",
        ),
    ] {
        let tail = if bucket.contains("U") {
            " for U in int | f64"
        } else {
            ""
        };
        let src = format!("{p}q(g: (x: {bucket}) -> int{tail}) = p(f: g);\n");
        assert_eq!(
            type_errors(&src),
            vec![format!(
                "The checker could not decide whether `p` takes {said}, so it is not proved \
                 wrong.\n  because the tuples ((int, int),) and ((int, int, int),) \
                 may each be held by one of the shapes {bucket}, which have no component that \
                 is one value, of one carrier, of one atom name or of one tuple length, and \
                 neither is held by the first of those shapes; which shape holds each decides \
                 what the type variables are bound to, and the checker looks through those \
                 shapes for one of the two only; here `U` is the type variable of `for U in \
                 int | f64`; to repair it, give ((int, int),) a shape of its own, written after \
                 the first of those shapes and before the second: `((int, int),)`; or test the \
                 value with `is` first, so that each test meets one of the two [p(f: g)]"
            )],
            "{src}"
        );
    }
}

#[test]
fn a_rigid_type_variable_in_a_refused_bucket_prints_by_name_in_the_shape_offered() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // `V` is bounded in `f`'s type, which the heading does not print: the tuples `g` gives,
    // `W` bound to `V`, the bucket and the repair all name it, and the message says which
    // `for` binds it. The repair is written in `f`'s result, where `V` is bound.
    // With `((V, V) | (V, V, V),)` for the second shape, each tuple is a member of its union and
    // is held there as it is (`member_hit`, FAIL-print-two-variables-one-name): accepted, where
    // before it was refused with the message below. With `int | V` in each first component, no
    // tuple is a member of the union, and the search refuses as before.
    let held = "p(f: (x: V) -> ((int, bool) | (int, bool, bool),) | ((V, V) | (V, V, V),) \
                for V in int | f64) = 0;\n\
                q(g: (x: W) -> ((W, W),) | ((W, W, W),) for W in int | f64) = p(f: g);\n";
    assert_eq!(type_errors(held), Vec::<String>::new());
    // With `int | V` in each first component the call is accepted too, where before it was
    // refused: no tuple of `((int, bool) | (int, bool, bool),)` holds a value of `(W, W)`, so
    // that shape is left out, and with `V` bound to `W`'s carrier `((W, W),)` and
    // `((W, W, W),)` are members of `((int | V, V) | (int | V, V, V),)`. Checked by hand.
    let plain = "p(f: (x: V) -> ((int, bool) | (int, bool, bool),) \
                 | ((int | V, V) | (int | V, V, V),) for V in int | f64) = 0;\n\
                 q(g: (x: W) -> ((W, W),) | ((W, W, W),) for W in int | f64) = p(f: g);\n";
    assert_eq!(type_errors(plain), Vec::<String>::new());
    // The first shape below holds a function, so it is not left out, and the bucket is refused.
    let src = "p(f: (x: V) -> ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
               | ((int | V, V) | (int | V, V, V),) for V in int | f64) = 0;\n\
               q(g: (x: W) -> ((W, W),) | ((W, W, W),) for W in int | f64) = p(f: g);\n";
    assert_eq!(
        type_errors(src),
        vec![
            "The checker could not decide whether `p` takes ((x: W) -> ((W, W),) | ((W, W, W),) \
             for W in int | f64), so it is not proved wrong.\n  because the tuples \
             ((V, V),) and ((V, V, V),) may each be held by one of the shapes ((int, bool, \
             (y: int) -> int) | (int, bool, bool, (y: int) -> int),) | ((int | V, V) | \
             (int | V, V, V),), which have no component \
             that is one \
             value, of one carrier, of one atom name or of one tuple length, and neither is held \
             by the first of those shapes; which shape holds each decides what the type \
             variables are bound to, and the checker looks through those shapes for one of the \
             two only; here `V` is the type variable of `for V in int | f64`; to repair it, give \
             ((V, V),) a shape of its own, written after the first of those shapes and before \
             the second: `((V, V),)`; or test the value with `is` first, so that each test meets \
             one of the two [p(f: g)]"
                .to_string()
        ]
    );
    let repaired = "p(f: (x: V) -> ((int, bool, (y: int) -> int) \
                    | (int, bool, bool, (y: int) -> int),) | ((V, V),) \
                    | ((int | V, V) | (int | V, V, V),) for V in int | f64) = 0;\n\
                    q(g: (x: W) -> ((W, W),) | ((W, W, W),) for W in int | f64) = p(f: g);\n";
    assert_eq!(type_errors(repaired), Vec::<String>::new());
}

/// The clause [`Ty::refused`] gives for tuples `(3, 5) | (4, 6)` in the shapes `bucket`, two
/// pairs told apart only at component 1.
fn pairs_refused_in(bucket: &str) -> String {
    format!(
        "; the checker could not decide this, so it is not proved wrong\n  because the \
         tuples (3, 5) and (4, 6) may each be held by one of the shapes {bucket}, which are told \
         apart only at component 1, where they agree with both, and neither is held by the \
         first of those shapes; which shape holds each decides what the type variables are \
         bound to, and the checker looks through those shapes for one of the two only; to \
         repair it, give (3, 5) a shape of its own, written after the first of those shapes and \
         before the second, the same as the shape that should hold it except at component 1, \
         where it is 3: `(3, …)`, with that shape's other components in place of each `…`; or \
         test the value with `is` first, so that each test meets one of the two"
    )
}

#[test]
fn an_unbounded_type_variable_in_a_refused_bucket_prints_by_name_where_it_stands_twice() {
    // In two shapes of the bucket, `T` is one type in both, so it prints by name; `T` and
    // `U` each in one place print `_` (DESIGN.md sec:diagnostics, "Types in a message").
    let pair = |a: Ty, b: Ty| Ty::tuple(vec![a, b]);
    let l = Ty::union_all(&[pair(int(3), int(5)), pair(int(4), int(6))]);
    let twice = Ty::union_all(&[pair(ty("1 | 2"), var("T")), pair(ty("int"), var("T"))]);
    assert_eq!(l.refused(&twice), pairs_refused_in("(1 | 2, T) | (int, T)"));
    let once = Ty::union_all(&[pair(ty("1 | 2"), var("T")), pair(ty("int"), var("U"))]);
    assert_eq!(l.refused(&once), pairs_refused_in("(1 | 2, _) | (int, _)"));
    // The own variable of a function type, in one shape twice and in two shapes. A domain is
    // exact (DESIGN.md sec:type_language), so `p` also takes the tuples of the first shape
    // (FAIL-types-fn-param-exact-domain).
    //
    // With a first shape free of variables, that shape is left out uncounted
    // (`Searched::closed_left_out`, FAIL-print-two-variables-one-name) and the bucket is not
    // refused. `((int, bool) | (int, bool, bool),) | ((int, T) | (int, T, T),)` then fits,
    // rightly: at `T` = `int` it is `p`'s domain, value for value.
    // `((int, bool) | (int, bool, bool),) | ((int, T) | (int, bool, T),)` then does not, rightly:
    // it holds `((int, int, int),)` at no `T`, and `p` takes that tuple.
    let plain =
        ty("(x: ((int, bool) | (int, bool, bool),) | ((int, int),) | ((int, int, int),)) -> int");
    let held = ty("(x: ((int, bool) | (int, bool, bool),) | ((int, T) | (int, T, T),)) -> int");
    assert_eq!(held.refused(&plain), "");
    let lacking =
        ty("(x: ((int, bool) | (int, bool, bool),) | ((int, T) | (int, bool, T),)) -> int");
    assert!(
        !lacking.refused(&plain).contains("could not decide"),
        "{}",
        lacking.refused(&plain)
    );
    // The first shape below holds a function, so it is not left out, and the bucket is refused.
    let p = ty(
        "(x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
                | ((int, int),) | ((int, int, int),)) -> int",
    );
    for bucket in [
        "((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
         | ((int, T) | (int, T, T),)",
        "((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
         | ((int, T) | (int, bool, T),)",
    ] {
        let g = ty(&format!("(x: {bucket}) -> int"));
        assert_eq!(
            g.refused(&p),
            format!(
                "; the checker could not decide this, so it is not proved wrong\n  because the tuples ((int, int),) and ((int, int, int),) may each be held by \
                 one of the shapes {bucket}, which have no component that is one value, of one \
                 carrier, of one atom name or of one tuple length, and neither is held by the \
                 first of those shapes; which shape holds each decides what the type variables \
                 are bound to, and the checker looks through those shapes for one of the two \
                 only; to repair it, give ((int, int),) a shape of its own, written after the \
                 first of those shapes and before the second: `((int, int),)`; or test the value \
                 with `is` first, so that each test meets one of the two"
            )
        );
    }
}

#[test]
fn an_unbounded_type_variable_in_two_payload_shapes_of_a_refused_bucket_prints_by_name() {
    let r = with_payloads(
        "a",
        vec![vec![ty("1 | 2"), var("T")], vec![ty("int"), var("T")]],
    );
    let l = with_payloads("a", vec![vec![int(3), int(5)], vec![int(4), int(6)]]);
    assert_eq!(
        l.refused(&r),
        "; the checker could not decide this, so it is not proved wrong\n  because the \
         payloads #a(3, 5) and #a(4, 6) may each be held by one of the shapes \
         #a(1 | 2, T) | #a(int, T), which are told apart only at component 1, where they agree \
         with both, and neither is held by the first of those shapes; which shape holds each \
         decides what the type variables are bound to, and the checker looks through those \
         shapes for one of the two only; to repair it, give #a(3, 5) a shape of its own, \
         written after the first of those shapes and before the second, the same as the shape \
         that should hold it except at component 1, where it is 3: `#a(3, …)`, with that \
         shape's other components in place of each `…`; or test the value with `is` first, so \
         that each test meets one of the two"
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
        // The even `i` below `n` are met, `n.div_ceil(2)` of them, and the odd ones left
        // (TEST-bench-move-l0123: the meet was `n / 2`, which the benchmark sizes, all even,
        // did not tell apart; the small test at odd `n` does).
        (
            "points",
            rows(&|i| pair(int(i), int(i))),
            rows(&|i| pair(int(2 * i), int(2 * i))),
            n / 2,
            n.div_ceil(2),
        ),
        // A function at a place: decided on the normal forms.
        (
            "functions",
            rows(&|i| pair(f.clone(), int(i))),
            rows(&|i| pair(f.clone(), int(2 * i))),
            n / 2,
            n.div_ceil(2),
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
fn the_meet_of_payloads_of_one_atom_meets_the_payloads() {
    // `&` of two types of one atom meets their payloads, as it meets the components of tuples,
    // and is empty where no payload of one shares a value with one of the other. Before
    // READ-atom-meet the payloads of the left side were kept, so `#a(bool) & #a(int)` read as
    // `#a(bool)`.
    for (text, want) in [
        ("#a(bool) & #a(int)", "Never"),
        ("#a(x: int) & #a(x: bool)", "Never"),
        ("#a(x: int) & #a(y: int)", "Never"),
        ("#a(#a(String)) & #a(#a(bool))", "Never"),
        ("(#a(bool) & #a(int),)", "Never"),
        ("(String, #a(bool) & #a(int))", "Never"),
        ("#a(int, bool) & #a(int, int)", "Never"),
        ("#a(int) & #a(int, int)", "Never"),
        ("#a() & #a(int)", "Never"),
        ("#a(int) & (#a(bool) | #b)", "Never"),
        ("(bool,) & (int,)", "Never"),
        ("(int, bool) & (int, int)", "Never"),
        ("#a(int | bool) & #a(int)", "#a(int)"),
        ("#a(int) & #a(int | bool)", "#a(int)"),
        ("#a(..) & #a(int)", "#a(int)"),
        ("#a(int) & #a(..)", "#a(int)"),
        ("#a(int) & #_", "#a(int)"),
        ("#a(int | String) & #a(String | bool)", "#a(String)"),
        ("(#a(int) | #a(bool)) & #a(int | String)", "#a(int)"),
        ("#a(int) & #a(int, int) & #a(int | bool)", "Never"),
        (
            "(#a(int) | #a(int, int)) & #a(int | bool, int)",
            "#a(int, int)",
        ),
        (
            "#a(x: int | bool, y: int) & #a(x: int, y: int)",
            "#a(x: int, y: int)",
        ),
        ("(#a(int) | #b) & (#a(bool) | #b)", "#b"),
        (
            "(#a(int) | #b(int)) & (#a(bool) | #b(int | bool))",
            "#b(int)",
        ),
        ("#a(#b(int | bool)) & #a(#b(bool | String))", "#a(#b(bool))"),
        ("(#a(bool) | int) & (#a(int) | int)", "int"),
    ] {
        let (t, w) = (ty(text), ty(want));
        assert!(t.subtype(&w) && w.subtype(&t), "{text} is {want}, not {t}");
        assert_eq!(t.is_empty(), want == "Never", "{text}");
    }
}

/// `#a(0, 0) | … | #a(n-1, n-1)` and `#a(0, int) | … | #a(n-1, int)`.
fn payload_pairs(n: usize) -> (Ty, Ty) {
    let each = |f: &dyn Fn(usize) -> Ty| -> Ty {
        let ts: Vec<Ty> = (0..n)
            .map(|i| with_payloads("a", vec![vec![int(i), f(i)]]))
            .collect();
        Ty::union_all(&ts)
    };
    (each(&int), each(&|_| ty("int")))
}

/// The union of `n` shapes `#a(i, int | bool)` and the union of `n` shapes `#a(i, bool)`, for
/// i < n: each shape of the left side is held in part by one of the right side.
fn partial_payload_pairs(n: usize) -> (Ty, Ty) {
    let each = |c: &str| -> Ty {
        let ts: Vec<Ty> = (0..n)
            .map(|i| with_payloads("a", vec![vec![int(i), ty(c)]]))
            .collect();
        Ty::union_all(&ts)
    };
    (each("int | bool"), each("bool"))
}

#[test]
fn the_difference_of_payloads_of_one_atom_takes_the_payloads() {
    // `\` of a type of one atom takes from the left side the payloads the right side holds,
    // shape by shape, as it takes tuples. Before READ-atom-meet the right side's atom was taken
    // with any payload, so `#a(bool) \ #a(int)` read as `Never`, and an `is not #a(int)` test
    // narrowed a `#a(bool)` away.
    for (text, want) in [
        ("#a(bool) \\ #a(int)", "#a(bool)"),
        ("#a(#a(int)) \\ #a((int,))", "#a(#a(int))"),
        ("#a(x: int) \\ #a(y: int)", "#a(x: int)"),
        ("#a(int) \\ #a(int, int)", "#a(int)"),
        ("(#a(int) | #a(bool)) \\ #a(int)", "#a(bool)"),
        ("(#a(int) | #b(int)) \\ #a(int | bool)", "#b(int)"),
        ("(#a(int) | #b) \\ #a(bool)", "#a(int) | #b"),
        ("(String, #a(bool) \\ #a(int))", "(String, #a(bool))"),
        ("#a(..) \\ #a(int)", "#a(..)"),
        ("#a(int) \\ #a(int)", "Never"),
        ("#a(int) \\ #a(..)", "Never"),
        ("#a(x: int) \\ #a(x: int | bool)", "Never"),
        ("#a(int, bool) \\ (#a(int, true) | #a(int, false))", "Never"),
        ("(#a(int) | #a(bool)) \\ (#a(int) | #a(bool))", "Never"),
        ("(#a(int) | #b) \\ (#a(int) | #b)", "Never"),
    ] {
        let (t, w) = (ty(text), ty(want));
        assert!(t.subtype(&w) && w.subtype(&t), "{text} is {want}, not {t}");
        assert_eq!(t.is_empty(), want == "Never", "{text}");
    }
}

#[test]
fn a_payload_shape_taken_away_in_part_leaves_its_rest() {
    // `\` of a payload shape that the right side holds only in part leaves the rest of the
    // shape, as it does for a tuple, and the type is written as it holds its values. Before
    // FAIL-kernel-terms-seed the shape was kept whole: `#a(int | String) \ #a(int)` read as
    // `#a(int | String)`, which holds `#a(1)`.
    for (text, want) in [
        ("#a(int | String) \\ #a(int)", "#a(String)"),
        ("#a(1 | 2) \\ #a(1)", "#a(2)"),
        ("#a(int | bool, int) \\ #a(bool, int)", "#a(int, int)"),
        (
            "#a(int | bool, 1 | 2) \\ #a(bool, 1)",
            "#a(int, 1 | 2) | #a(bool, 2)",
        ),
        (
            "#a(1 | 2 | 3, 1 | 2) \\ (#a(1, 1) | #a(2, 2))",
            "#a(3, 1 | 2) | #a(1, 2) | #a(2, 1)",
        ),
        ("#a(#b(int | bool)) \\ #a(#b(bool))", "#a(#b(int))"),
        ("(#a(int | bool) | #b) \\ #a(bool | String)", "#a(int) | #b"),
        (
            "(#a(int | bool) | #a(String)) \\ #a(bool)",
            "#a(int) | #a(String)",
        ),
        ("(String, #a(int | bool) \\ #a(int))", "(String, #a(bool))"),
    ] {
        let (t, w) = (ty(text), ty(want));
        assert!(t.subtype(&w) && w.subtype(&t), "{text} is {want}, not {t}");
        assert!(!t.is_empty(), "{text}");
        let shown = t.to_string();
        let back = ty(&shown);
        assert!(back.subtype(&w) && w.subtype(&back), "{shown} is {want}");
    }
    // The rest takes part in what follows as any type does.
    let d = ty("#a(int | bool) \\ #a(bool)");
    let u = d.union(&ty("#a(String)"));
    let want = ty("#a(int | String)");
    assert!(u.subtype(&want) && want.subtype(&u), "{u}");
    assert!(d.meet(&ty("#a(bool)")).is_empty());
    assert!(d.diff(&ty("#a(int)")).is_empty());
    assert!(!d.subtype(&ty("#a(bool)")) && d.subtype(&ty("#a(int)")));
}

/// The type errors of `text`, each its message and its steps.
fn errors_with_steps(text: &str) -> Vec<(String, Vec<String>)> {
    let info = zed_tests::step_helpers::l01_26_type_resolution::Resolved::new(text).check();
    (info.errors.iter())
        .map(|e| {
            (
                e.message.clone(),
                e.notes.iter().map(|n| n.text.to_string()).collect(),
            )
        })
        .collect()
}

#[test]
fn a_tuple_type_taken_away_in_part_from_a_wide_tuple_type_leaves_its_values_out() {
    // DESIGN.md sec:type_language: "`t \ t` // difference (t1 \ t2 is sugar for t1 & !t2)",
    // and "types denote sets of values". So `((..), (..)) \ ((..), (int, int))` holds no pair
    // whose second component is a pair of `int`s, and a parameter of that type takes none.
    // Before FIX-ty-diff-wide-row a tuple type of the left side that a tuple type of the
    // right side held only in part was kept whole: the difference read as `((..), (..))`, and
    // `f(p: ((1, 2), (3, 4)))` was accepted. The parameter's type is written as declared, the
    // call takes one argument in the part `\` takes away and one outside it.
    for (param, taken, outside, removed) in [
        (
            "((..), (..)) \\ ((..), (int, int))",
            "((1, 2), (3, 4))",
            "((1, 2), (3, 4, 5))",
            "((..), (int, int))",
        ),
        (
            "((..), (..)) \\ ((int, int), (..))",
            "((1, 2), (3, 4))",
            "((1, 2, 0), (3, 4))",
            "((int, int), (..))",
        ),
        (
            "((..), (..)) \\ ((int, int), (int, int))",
            "((1, 2), (3, 4))",
            "((1, 2), (3, 4, 5))",
            "((int, int), (int, int))",
        ),
        (
            "(int, (..)) \\ (int, (int, int))",
            "(1, (3, 4))",
            "(1, (3, 4, 5))",
            "(int, (int, int))",
        ),
        (
            "(((..), int), int) \\ (((int, int), int), int)",
            "(((1, 2), 3), 4)",
            "(((1, 2, 0), 3), 4)",
            "(((int, int), int), int)",
        ),
    ] {
        let t = ty(param);
        assert!(
            !ty(taken).subtype(&t),
            "{taken} is not in {param}, read as {t}"
        );
        assert!(
            ty(outside).subtype(&t),
            "{outside} is in {param}, read as {t}"
        );
        // MSG-derive-type-size: in the last case `((1, 2), 3)` is the type of a step of its own
        // and a part of the argument, and it holds a part, so the message names it `Part1` and
        // writes the argument `(Part1, 4)`; the shorter `(1, 2)` stays in full.
        let written = if taken == "(((1, 2), 3), 4)" {
            "(Part1, 4)"
        } else {
            taken
        };
        let step =
            format!("`{written} : {removed}` is in the part `\\` takes away from `p : {param}`");
        let text = format!("f(p: {param}) = p;\ng() = f(p: {taken});\nh() = f(p: {outside});\n");
        let errs = errors_with_steps(&text);
        assert_eq!(errs.len(), 1, "{text}{errs:#?}");
        let (message, steps) = &errs[0];
        assert!(
            message.starts_with(&format!("`f` does not take ({written})")),
            "{text}{message}"
        );
        assert!(steps.contains(&step), "{text}{steps:#?}");
        // A positional parameter takes its argument by place.
        let text = format!("f(positional p: {param}) = p;\ng() = f({taken});\n");
        let errs = errors_with_steps(&text);
        assert_eq!(errs.len(), 1, "{text}{errs:#?}");
        assert!(errs[0].1.contains(&step), "{text}{errs:#?}");
    }
}

#[test]
fn a_difference_that_takes_part_of_a_tuple_holding_a_function_is_refused() {
    // DESIGN.md sec:type_language: "t1 \ t2 is sugar for t1 & !t2". The checker cannot split a
    // tuple type that holds a function type (it has no kernel type), so where the right side
    // may hold part of such a tuple of the left side, the difference it reads holds the whole
    // tuple, more than `t1 & !t2`. Before (FAIL-ty-diff-function-rows, found by proofdoc4c)
    // that reading was used: `f((inc, #a))` was accepted below, though `(inc, #a)` is in the
    // part `\` takes away. Now the written difference is refused, once, at the difference.
    let errors = zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    for (param, arg) in [
        ("((int) -> int, #a | #b) \\ ((int) -> int, #a)", "(inc, #a)"),
        (
            "((int) -> int, (..)) \\ ((int) -> int, (int, int))",
            "(inc, (1, 2))",
        ),
    ] {
        let text = format!(
            "inc(positional x: int) = x + 1;\nf(positional p: {param}) = p;\ng() = f({arg});\n"
        );
        let errs = errors(&text);
        let refused = format!(
            "`{param}` takes away part of a tuple or payload that holds a function type, which \
             is part of the Zed language but is not supported by this version of zedc. Write \
             the type without `\\`, as the union of the tuples or payloads that are left. \
             [{param}]"
        );
        assert_eq!(errs, [refused], "{text}");
    }
    // A difference whose right side shares no value with a tuple holding a function is read
    // exactly, and is not refused.
    for (param, arg) in [
        ("((int) -> int, #a) \\ String", "(inc, #a)"),
        ("(((int) -> int, #a) | (int, #b)) \\ (int, #b)", "(inc, #a)"),
    ] {
        let text = format!(
            "inc(positional x: int) = x + 1;\nf(positional p: {param}) = p;\ng() = f({arg});\n"
        );
        assert_eq!(errors(&text), Vec::<String>::new(), "{text}");
    }
    // The same on the types, where a payload, which a program cannot yet write as a type, is
    // read too: a payload shape holding a function that the right side may hold in part is
    // kept whole, so the answer is inexact; one the right side shares no value with is not.
    for (a, b, exact) in [
        ("((int) -> int, #a | #b)", "((int) -> int, #a)", false),
        ("#c((int) -> int, #a | #b)", "#c((int) -> int, #a)", false),
        ("((int) -> int, #a)", "String", true),
        ("#c((int) -> int, #a)", "#c(int, int, int)", true),
        ("((int, int), (..))", "((int, int), (int, int))", true),
    ] {
        let (d, got) = ty(a).diff_exact(&ty(b));
        assert_eq!(got, exact, "{a} \\ {b}, read as {d}");
    }
}

#[test]
fn a_difference_that_takes_away_a_type_variable_is_refused() {
    // FAIL-diff-type-var-right-inexact: `int \ V` was read as `int`, exact, though where a
    // call picks `int` for `V` it is `Never`. So `h`, which takes `(int, f64)`, was refused for
    // `(int \ V, V) -> int for V in int | f64`, which it fits at each carrier: at `int` the
    // first parameter has no value, at `f64` `h` takes both. Without `\ V` the refusal is
    // right, and the same: the difference changed nothing. Now the difference is refused, at
    // itself, and names `V`.
    let errors = zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let h = "h(x: int, y: f64) = x;\n";
    let text =
        format!("p(f: (x: int \\ V, y: V) -> int for V in int | f64) = 0;\n{h}z = p(f: h);\n");
    assert_eq!(
        errors(&text),
        [
            "`int \\ V` takes away `V`, which holds a type variable whose carrier only a call \
             picks; that is part of the Zed language but is not supported by this version of \
             zedc. Write the type without `\\ V`. [int \\ V]"
        ],
        "{text}"
    );
    // A variable inside a union on the right is named with the union.
    let text = "p(f: (x: int \\ (V | String), y: V) -> int for V in int | f64) = 0;\n";
    let errs = errors(text);
    assert_eq!(errs.len(), 1, "{text}\n{errs:#?}");
    assert!(
        errs[0].starts_with("`int \\ (V | String)` takes away `V | String`,"),
        "{errs:#?}"
    );
    // A difference with no variable on the right is read as before, exactly.
    let text =
        format!("p(f: (x: int \\ String, y: V) -> int for V in int | f64) = 0;\n{h}z = p(f: h);\n");
    let errs = errors(&text);
    assert_eq!(errs.len(), 1, "{text}\n{errs:#?}");
    assert!(
        errs[0].starts_with("`h` is `(x: int, y: f64) -> int`, not "),
        "{errs:#?}"
    );
    // On the types: a variable on the right leaves the answer inexact where anything is left,
    // and exact where nothing is.
    assert!(!ty("int").diff_exact(&var("V")).1);
    assert!(
        !ty("int | String")
            .diff_exact(&ty("String").union(&var("V")))
            .1
    );
    assert!(ty("String").diff_exact(&ty("String").union(&var("V"))).1);
}

#[test]
fn a_tuple_type_taken_away_in_whole_leaves_never() {
    // DESIGN.md sec:type_language: "`t1 <: t2` iff `t1 & !t2` is empty", and the empty type is
    // `Never`. A difference whose right side holds every value of its left side has no value,
    // and a parameter of that type takes no argument; the message says both why the type has
    // no value and that the argument is in the part taken away.
    for (param, arg, removed) in [
        (
            "((..), (..)) \\ ((..), (..))",
            "((1, 2), (3, 4))",
            "((..), (..))",
        ),
        ("((..), (..)) \\ (..)", "((1, 2), 3)", "(..)"),
        (
            "(int, (..)) \\ (int | bool, (..))",
            "(1, (3, 4))",
            "(int | bool, (..))",
        ),
    ] {
        assert!(ty(param).is_empty(), "{param} is {}", ty(param));
        let text = format!("f(p: {param}) = p;\ng() = f(p: {arg});\n");
        let errs = errors_with_steps(&text);
        assert_eq!(errs.len(), 1, "{text}{errs:#?}");
        let steps = &errs[0].1;
        assert!(
            steps
                .iter()
                .any(|s| s.starts_with("this difference has no value")),
            "{text}{steps:#?}"
        );
        let step = format!("`{arg} : {removed}` is in the part `\\` takes away from `p : {param}`");
        assert!(steps.contains(&step), "{text}{steps:#?}");
    }
}

#[test]
fn a_difference_nested_in_a_parameter_type_names_the_component_it_takes_away() {
    // MSG-diff-nested-arg-step: the step names the innermost component of a tuple display in
    // the part a nested difference takes away, read as the body reads it, `p[1]`.
    let inner = "`(2, 3) : (int, int)` is in the part `\\` takes away from \
                 `p[1] : (..) \\ (int, int)`";
    let deep = "`(3, 4) : (int, int)` is in the part `\\` takes away from \
                `p[1][1] : (..) \\ (int, int)`";
    for (param, arg, step) in [
        ("(int, (..) \\ (int, int))", "(1, (2, 3))", inner),
        // The outer difference takes the argument away too; only the innermost is named.
        (
            "(int, (..) \\ (int, int)) \\ (int, (int, int))",
            "(1, (2, 3))",
            inner,
        ),
        // The outer difference takes nothing away here.
        (
            "(int, (..) \\ (int, int)) \\ (int, (int, bool))",
            "(1, (2, 3))",
            inner,
        ),
        ("(int, (int, (..) \\ (int, int)))", "(1, (2, (3, 4)))", deep),
        // A difference in the left side of a difference, at the same component.
        (
            "((..) \\ (int, int)) \\ (bool, bool)",
            "(true, false)",
            "`(true, false) : (bool, bool)` is in the part `\\` takes away from \
             `p : (..) \\ (int, int) \\ (bool, bool)`",
        ),
        (
            "((..) \\ (int, int)) \\ (int, int)",
            "(1, 2)",
            "`(1, 2) : (int, int)` is in the part `\\` takes away from `p : (..) \\ (int, int)`",
        ),
    ] {
        let text = format!("f(p: {param}) = p;\ng() = f(p: {arg});\n");
        let errs = errors_with_steps(&text);
        assert_eq!(errs.len(), 1, "{text}{errs:#?}");
        let took: Vec<&String> = (errs[0].1.iter())
            .filter(|s| s.contains("takes away"))
            .collect();
        assert_eq!(took, [step], "{text}{errs:#?}");
    }
    // A component reached through a name is named where the display holds the name.
    let text = "f(p: (int, (..) \\ (int, int))) = p;\ng() = { t = (2, 3); f(p: (1, t)) };\n";
    let errs = errors_with_steps(text);
    assert!(
        (errs.iter().flat_map(|e| &e.1))
            .any(|s| s.ends_with("takes away from `p[1] : (..) \\ (int, int)`")),
        "{text}{errs:#?}"
    );
}

/// `f(p: (int, (int, … (..) \ (int, int) …)))`, the difference `n` tuples deep, called with a
/// display that reaches it, `(1, (1, … (2, 3) …))`.
fn nested_difference(n: usize) -> String {
    format!(
        "f(p: {}(..) \\ (int, int){}) = p;\ng() = f(p: {}(2, 3){});\n",
        "(int, ".repeat(n),
        ")".repeat(n),
        "(1, ".repeat(n),
        ")".repeat(n)
    )
}

#[test]
fn the_steps_of_differences_side_by_side_take_linear_time_in_their_number() {
    // MSG-diff-nested-arg-step: the walk visits each written component once, writes a path
    // only for a step taken, and drops the outer steps in one pass, where comparing each pair
    // of steps took time quadratic in their number. `n` differences side by side in one tuple
    // each take a component away, and each gets its step.
    let step = format!(
        "takes away from `p{} : (..) \\ (int, int)`",
        "[1]".repeat(4)
    );
    let errs = errors_with_steps(&nested_difference(4));
    assert!(
        errs.iter().flat_map(|e| &e.1).any(|s| s.ends_with(&step)),
        "{errs:#?}"
    );
    let side_by_side = |n: usize| {
        format!(
            "f(p: ({}int)) = p;\ng() = f(p: ({}1));\n",
            "(..) \\ (int, int), ".repeat(n),
            "(2, 3), ".repeat(n)
        )
    };
    let count = |n: usize| {
        let errs = errors_with_steps(&side_by_side(n));
        assert_eq!(errs.len(), 1);
        errs[0]
            .1
            .iter()
            .filter(|s| s.contains("takes away"))
            .count()
    };
    assert_eq!(count(3), 3);
    scaling::check(
        "the steps of differences side by side, by number",
        40,
        |n| {
            assert_eq!(count(n), n);
        },
    );
    // A difference at each of `n` depths, `((..) \ (int, int), ((..) \ (int, int), … int))`:
    // each step's path is as long as its depth, and each pair of steps shares that prefix.
    // Side by side, the steps' paths are short, so comparing each pair of the `k` steps, the
    // walk before b22-msgtypes, stayed within the limit up to k = 1000 (9.5 times at 8n,
    // measured at f36f5888e), each step's own check costing far more than a comparison.
    // Nested, the run measured 25.0 times the bytes at 8n at f36f5888e and at 964ae4d8c,
    // from the derivation building the type of each nested display at every level
    // (PERF-deep-tuple-call-refusal), which the depth test below measures alone.
    let comb = |n: usize| {
        format!(
            "f(p: {}int{}) = p;\ng() = f(p: {}1{});\n",
            "((..) \\ (int, int), ".repeat(n),
            ")".repeat(n),
            "((2, 3), ".repeat(n),
            ")".repeat(n)
        )
    };
    let nested = |n: usize| {
        let errs = errors_with_steps(&comb(n));
        assert_eq!(errs.len(), 1);
        errs[0]
            .1
            .iter()
            .filter(|s| s.contains("takes away"))
            .count()
    };
    assert_eq!(nested(3), 3);
    scaling::check("the steps of differences nested, by depth", 40, |n| {
        assert_eq!(nested(n), n);
    });
}

#[test]
fn a_refused_call_on_a_deeply_nested_display_takes_linear_time_in_its_depth() {
    // PERF-deep-tuple-call-refusal: the derivation of a refused call asks for the type of each
    // tuple written out in the argument, and built each one from its parts at any depth, so a
    // display `n` tuples deep cost time and memory quadratic in `n` (3.3e9 instructions in the
    // check stage at n = 400, 3.5 times those at 200); each tuple is now built once.
    let deep = |n: usize| {
        format!(
            "f(p: {}(int, bool){}) = p;\ng() = f(p: {}(2, 3){});\n",
            "(int, ".repeat(n),
            ")".repeat(n),
            "(1, ".repeat(n),
            ")".repeat(n)
        )
    };
    let refused = |n: usize| {
        let errs = errors_with_steps(&deep(n));
        assert_eq!(errs.len(), 1, "{errs:#?}");
        assert!(errs[0].0.contains("does not take"), "{errs:#?}");
    };
    refused(3);
    scaling::check("a refused call on a nested display, by depth", 40, refused);
}

#[test]
fn only_an_argument_in_the_part_taken_away_gets_the_step_about_it() {
    // An argument refused for being outside the left side of the difference, or a call refused
    // for another argument, says nothing of the part `\` takes away.
    let param = "((..), (..)) \\ ((..), (int, int))";
    for (call, why) in [
        ("f(p: 3, q: 1)", "the argument is outside the left side"),
        (
            "f(p: ((1, 2), (3, 4, 5)), q: true)",
            "another argument is refused",
        ),
    ] {
        let text = format!("f(p: {param}, q: int) = p;\ng() = {call};\n");
        let errs = errors_with_steps(&text);
        assert_eq!(errs.len(), 1, "{why}: {text}{errs:#?}");
        assert!(
            !errs[0]
                .1
                .iter()
                .any(|s| s.contains("is in the part `\\` takes away")),
            "{why}: {text}{errs:#?}"
        );
    }
}

/// `n` tuple types `(i, (..))` and `n` tuple types `(i, (int, int))`, `i` from 0.
fn wide_pairs(n: usize) -> (Ty, Ty) {
    let each = |c: &Ty| -> Ty {
        let ts: Vec<Ty> = (0..n).map(|i| Ty::tuple(vec![int(i), c.clone()])).collect();
        Ty::union_all(&ts)
    };
    (each(&ty("(..)")), each(&ty("(int, int)")))
}

/// The note of a refused bucket of two shapes, after the headline "The checker could not
/// decide whether `p` takes (…), so it is not proved wrong.": the tuples
/// `first` and `second` held by `shapes`, the type variables named by `here`, and the repair
/// `own`, a shape of its own for `first`, when one is offered.
fn bucket_refused(first: &str, second: &str, shapes: &str, here: &str, own: bool) -> String {
    let repair = match own {
        true => format!(
            "give {first} a shape of its own, written after the first of those shapes and \
             before the second: `{first}`; or "
        ),
        false => String::new(),
    };
    format!(
        "\n  because the tuples {first} and {second} may each be held by one of the shapes {shapes}, which have \
         no component that is one value, of one carrier, of one atom name or of one tuple \
         length, and neither is held by the first of those shapes; which shape holds each \
         decides what the type variables are bound to, and the checker looks through those \
         shapes for one of the two only; here {here}; to repair it, {repair}test the value with \
         `is` first, so that each test meets one of the two [p(f: g)]"
    )
}

#[test]
fn a_function_in_a_tuple_of_a_refused_bucket_prints_as_its_type() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // The comparison holds each function as a variable of its own; the message prints the
    // function, as it prints it outside a tuple, and not `_`: a function, a tuple that holds
    // one, a function with a bounded variable of its own, and a curried function.
    for h in [
        "(y: int) -> int",
        "((y: int) -> int, int)",
        "(y: W) -> W for W in int",
        "(y: int) -> (z: int) -> int",
    ] {
        let shapes = format!(
            "((int, bool, {h}) | (int, bool, bool, {h}),) | ((int, U, {h}) | (int, U, U, {h}),)"
        );
        // A domain is exact (DESIGN.md sec:type_language), so `f` also takes the tuples of
        // `g`'s first shape (FAIL-types-fn-param-exact-domain).
        let bools = format!("((int, bool, {h}) | (int, bool, bool, {h}),)");
        let src = format!(
            "p(f: (x: {bools} | ((int, int, {h}),) | ((int, int, int, {h}),)) -> int) = 0;\n\
             q(g: (x: {shapes}) -> int for U in int | f64) = p(f: g);\n"
        );
        let first = format!("((int, int, {h}),)");
        let clause = bucket_refused(
            &first,
            &format!("((int, int, int, {h}),)"),
            &shapes,
            "`U` is the type variable of `for U in int | f64`",
            true,
        );
        assert_eq!(
            type_errors(&src),
            vec![format!(
                "The checker could not decide whether `p` takes ((x: {shapes}) -> int for U in int | f64), so it is not proved \
             wrong.{clause}"
            )],
            "{h}"
        );
        let repaired = format!(
            "p(f: (x: {bools} | ((int, int, {h}),) | ((int, int, int, {h}),)) -> int) = 0;\n\
             q(g: (x: ((int, bool, {h}) | (int, bool, bool, {h}),) | {first} \
             | ((int, U, {h}) | (int, U, U, {h}),)) -> int for U in int | f64) = p(f: g);\n"
        );
        assert_eq!(type_errors(&repaired), Vec::<String>::new(), "{h}");
    }
}

#[test]
fn functions_in_several_places_of_a_tuple_of_a_refused_bucket_print_as_their_types() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let (a, b) = ("(y: int) -> int", "(z: bool) -> int");
    let shapes = format!(
        "(({a}, bool, {b}) | ({a}, bool, bool, {b}),) | (({a}, U, {b}) | ({a}, U, U, {b}),)"
    );
    // A domain is exact (DESIGN.md sec:type_language), so `f` also takes the tuples of `g`'s
    // first shape (FAIL-types-fn-param-exact-domain).
    let src = format!(
        "p(f: (x: (({a}, bool, {b}) | ({a}, bool, bool, {b}),) | (({a}, int, {b}),) \
         | (({a}, int, int, {b}),)) -> int) = 0;\n\
         q(g: (x: {shapes}) -> int for U in int | f64) = p(f: g);\n"
    );
    let clause = bucket_refused(
        &format!("(({a}, int, {b}),)"),
        &format!("(({a}, int, int, {b}),)"),
        &shapes,
        "`U` is the type variable of `for U in int | f64`",
        true,
    );
    assert_eq!(
        type_errors(&src),
        vec![format!(
            "The checker could not decide whether `p` takes ((x: {shapes}) -> int for U in int | f64), so it is not proved \
             wrong.{clause}"
        )]
    );
}

#[test]
fn a_function_as_a_tuple_of_one_component_in_a_refused_bucket_prints_as_its_type() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // Accepted: at `U` = `int`, `g`'s domain is `f`'s, value for value. Before
    // FAIL-print-two-variables-one-name it was refused, as both tuples searched past the first
    // shape, which holds no variable and neither tuple; that shape is now left out uncounted
    // (`Searched::closed_left_out`).
    let held = "p(f: (x: ((int, bool) | (int, bool, bool),) | ((int, int),) | ((int, int, int),) \
                | ((y: int) -> int,)) -> int) = 0;\n\
                q(g: (x: ((int, bool) | (int, bool, bool),) | ((int, U) | (int, U, U),) \
                | ((y: int) -> int,)) -> int for U in int | f64) = p(f: g);\n";
    assert_eq!(type_errors(held), Vec::<String>::new());
    // The first shape below holds a function, so it is not left out, and the bucket is refused.
    let shapes = "((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
                  | ((int, U) | (int, U, U),) | ((y: int) -> int,)";
    // A domain is exact (DESIGN.md sec:type_language), so `f` also takes the tuples of `g`'s
    // first and last shapes (FAIL-types-fn-param-exact-domain).
    let src = format!(
        "p(f: (x: ((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),) \
         | ((int, int),) | ((int, int, int),) | ((y: int) -> int,)) -> int) = 0;\n\
         q(g: (x: {shapes}) -> int for U in int | f64) = p(f: g);\n"
    );
    let clause = bucket_refused(
        "((int, int),)",
        "((int, int, int),)",
        shapes,
        "`U` is the type variable of `for U in int | f64`",
        true,
    );
    assert_eq!(
        type_errors(&src),
        vec![format!(
            "The checker could not decide whether `p` takes ((x: {shapes}) -> int for U in int | f64), so it is not proved \
             wrong.{clause}"
        )]
    );
}

#[test]
fn a_function_in_a_refused_bucket_prints_the_rigid_variable_it_holds_by_name() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // `V` of `f`'s type is rigid in the outer comparison; the function in the tuple that holds
    // it is read as the comparison reads `f`'s type, and prints `V`. Before
    // FAIL-types-fn-in-tuple-bound-variable-refused, these programs were answered "`p` does
    // not take ...", which says they are wrong: `g`'s `k` is `f`'s `k` once `W` is bound to
    // `V` (DESIGN.md sec:type_resolution rule 6), and the same program without the function in
    // the tuples is answered "could not decide", as this is now. A domain is exact (DESIGN.md
    // sec:type_language), so `f`'s `k` also takes the tuples of `g`'s first shape
    // (FAIL-types-fn-param-exact-domain).
    let h = "(y: int) -> int";
    for (fv, fw) in [
        ("(y: V) -> int", "(y: W) -> int"),
        ("(y: int) -> V", "(y: int) -> W"),
    ] {
        let shapes = format!(
            "((int, bool, {h}) | (int, bool, bool, {h}),) | ((int, W, {fw}) | (int, W, W, {fw}),)"
        );
        let src = format!(
            "p(f: (k: (x: ((int, bool, {h}) | (int, bool, bool, {h}),) | ((int, V, {fv}),) \
             | ((int, V, V, {fv}),)) -> int) -> int for V in int | f64) = 0;\n\
             q(g: (k: (x: {shapes}) -> int for W in int | f64) -> int) = p(f: g);\n"
        );
        let clause = bucket_refused(
            &format!("((int, V, {fv}),)"),
            &format!("((int, V, V, {fv}),)"),
            &shapes,
            "`V` is the type variable of `for V in int | f64`, and `W` is the type variable of \
             `for W in int | f64`",
            false,
        );
        assert_eq!(
            type_errors(&src),
            vec![format!(
                "The checker could not decide whether `p` takes ((k: (x: {shapes}) -> int for W in int | f64) -> int), so it is not proved \
                 wrong.{clause}"
            )],
            "{src}"
        );
    }
}

#[test]
fn a_rigid_variable_of_an_outer_comparison_and_an_own_variable_of_the_same_name_print_apart() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // `V` of `f`'s type is rigid in the outermost comparison; the comparison of the functions
    // `k` two levels in meets `V` of `g`'s `k`, an own variable of the same name, which prints
    // as `T`.
    // A domain is exact (DESIGN.md sec:type_language), so `f`'s `k` also takes the tuples of
    // the first shape (FAIL-types-fn-param-exact-domain).
    let shapes = "((int, bool) | (int, bool, bool),) | ((V, V) | (V, V, V),)";
    let src = format!(
        "p(f: (h: (k: (x: ((int, bool) | (int, bool, bool),) | ((V, V),) | ((V, V, V),)) \
         -> int) -> int) -> int for V in int | f64) = 0;\n\
         q(g: (h: (k: (x: {shapes}) -> int for V in int | f64) -> int) -> int) = p(f: g);\n"
    );
    //
    // Not taken, rightly: `g`'s `k` is bounded by its own `for`, and "A bounded type variable
    // is one carrier at a call" (DESIGN.md sec:type_resolution rule 6), so the type of `g`'s
    // `k` is the overload of one exact arrow at each carrier, whose domain is the union of the
    // two instances, the pairs and triples of `f64` with those of `int`. `f`'s `k`, at its one
    // `V`, takes the pairs and triples of one carrier only, so no `k` is of both types, the
    // domains of `h` differ, and `p` does not take `g`. Before
    // FAIL-print-two-variables-one-name the first shape, free of variables, was counted as
    // failed by both tuples and the bucket was refused; base 2f21f4ed2 says this same "no"
    // with `f`'s and `g`'s domains equal and no such shape.
    assert_eq!(
        type_errors(&src),
        vec![format!(
            "`p` does not take ((h: (k: (x: {shapes}) -> int for V in int | f64) -> int) -> \
             int): no arrow of `p` takes these types. [p(f: g)]"
        )]
    );
    // The first shape below holds a function, so it is not left out, and the bucket is refused
    // before the domains are found to differ; the two variables print apart.
    let first = "((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),)";
    let shapes = format!("{first} | ((V, V) | (V, V, V),)");
    let src = format!(
        "p(f: (h: (k: (x: {first} | ((V, V),) | ((V, V, V),)) -> int) -> int) -> int \
         for V in int | f64) = 0;\n\
         q(g: (h: (k: (x: {shapes}) -> int for V in int | f64) -> int) -> int) = p(f: g);\n"
    );
    let clause = bucket_refused(
        "((V, V),)",
        "((V, V, V),)",
        &format!("{first} | ((T, T) | (T, T, T),)"),
        "`T` is the type variable `V` of `for V in int | f64`, and `V` is the type variable of \
         `for V in int | f64`",
        false,
    );
    assert_eq!(
        type_errors(&src),
        vec![format!(
            "The checker could not decide whether `p` takes ((h: (k: (x: {shapes}) -> int for V \
             in int | f64) -> int) -> int), so it is not proved wrong.{clause}"
        )]
    );
}

#[test]
fn a_rigid_variable_and_an_own_variable_of_the_same_name_one_level_in_print_apart() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // `V` of `f`'s type is rigid in the outer comparison; the comparison of the functions `h`
    // meets `V` of `g`'s `h`, an own variable of the same name, which is given a new name
    // there, so the two are two variables, and print apart, `V` and `T`. A domain is exact
    // (DESIGN.md sec:type_language), so `f`'s `h` also takes the tuples of the first shape
    // (FAIL-types-fn-param-exact-domain).
    //
    // The bound is `int | f64`: a bound of one carrier is that carrier at every instance, and
    // is read so (FAIL-fn-domain-bindable-variable), so with `int` no variable is left to print
    // and the program is accepted. `f`'s tuples are `((V, V),)` and `((V, V, V),)`: with
    // `((V, int),)`, at `V` = `f64` no shape of `g` holds `(f64, int)`, and the program is
    // refused as wrong, rightly, before the bucket. The own-variable form of this test is
    // FAIL-print-two-variables-one-name.
    let shapes = "((int, bool) | (int, bool, bool),) | ((V, V) | (V, V, V),)";
    let src = format!(
        "p(f: (h: (x: ((int, bool) | (int, bool, bool),) | ((V, V),) | ((V, V, V),)) \
         -> int) -> int for V in int | f64) = 0;\n\
         q(g: (h: (x: {shapes}) -> int for V in int | f64) -> int) = p(f: g);\n"
    );
    //
    // Not taken, rightly: `g`'s `h` is bounded by its own `for`, and "A bounded type variable
    // is one carrier at a call" (DESIGN.md sec:type_resolution rule 6), so the type of `g`'s
    // `h` is the overload of one exact arrow at each carrier, whose domain is the union of the
    // two instances, the pairs and triples of `f64` with those of `int`. `f`'s `h`, at its one
    // `V`, takes the pairs and triples of one carrier only, so no `h` is of both types, the
    // domains differ, and `p` does not take `g`. Before FAIL-print-two-variables-one-name the
    // first shape, free of variables, was counted as failed by both tuples and the bucket was
    // refused; base 2f21f4ed2 says this same "no" with `f`'s and `g`'s domains equal and no
    // such shape.
    assert_eq!(
        type_errors(&src),
        vec![format!(
            "`p` does not take ((h: (x: {shapes}) -> int for V in int | f64) -> int): no arrow \
             of `p` takes these types. [p(f: g)]"
        )]
    );
    // The first shape below holds a function, so it is not left out, and the bucket is refused
    // before the domains are found to differ; the two variables print apart.
    let first = "((int, bool, (y: int) -> int) | (int, bool, bool, (y: int) -> int),)";
    let shapes = format!("{first} | ((V, V) | (V, V, V),)");
    let src = format!(
        "p(f: (h: (x: {first} | ((V, V),) | ((V, V, V),)) -> int) -> int for V in int | f64) \
         = 0;\n\
         q(g: (h: (x: {shapes}) -> int for V in int | f64) -> int) = p(f: g);\n"
    );
    let clause = bucket_refused(
        "((V, V),)",
        "((V, V, V),)",
        &format!("{first} | ((T, T) | (T, T, T),)"),
        "`T` is the type variable `V` of `for V in int | f64`, and `V` is the type variable of \
         `for V in int | f64`",
        false,
    );
    assert_eq!(
        type_errors(&src),
        vec![format!(
            "The checker could not decide whether `p` takes ((h: (x: {shapes}) -> int for V in \
             int | f64) -> int), so it is not proved wrong.{clause}"
        )]
    );
}

/// A function whose parameter type holds a type variable the comparison binds fits an exact or
/// a `->?` domain that its instance fits (FAIL-fn-domain-bindable-variable). DESIGN.md
/// sec:type_language ("Morphism types carry two domain bounds"): `<:` iff L2 <: L1, U1 <: U2,
/// V1 <: V2, and `K ->? V` has L empty and U = K. sec:type_resolution rule 6: a call fixes a
/// bounded variable to one carrier, so with `for V in int`, `V` is `int`, and each program
/// below has the verdict of the same program with `int` written for `V`, which is accepted.
#[test]
fn a_function_whose_parameter_holds_a_bound_variable_fits_a_domain_its_instance_fits() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    for src in [
        // One level, `->?`: U1 = V = int is within U2 = int | String; L2 is empty.
        "p(f: (x: int | String) ->? int) = 0;\nq(g: (x: V) -> int for V in int) = p(f: g);\n",
        // One level, `->?`, the variable in a tuple.
        "p(f: (x: ((int, int),) | ((int, int, int),)) ->? int) = 0;\n\
         q(g: (x: ((V, int),)) -> int for V in int) = p(f: g);\n",
        // Two levels, exact: `(x: V) -> int` is `(x: int) -> int`; one level of the same is
        // accepted.
        "p(f: (h: (x: int) -> int) -> int) = 0;\n\
         q(g: (h: (x: V) -> int) -> int for V in int) = p(f: g);\n",
        // Two levels, exact, the same shapes on both sides, `V` of `f`'s `h` its own.
        "p(f: (h: (x: ((int, bool) | (int, bool, bool),) | ((V, V) | (V, V, V),)) -> int \
         for V in int) -> int) = 0;\n\
         q(g: (h: (x: ((int, bool) | (int, bool, bool),) | ((V, V) | (V, V, V),)) -> int) \
         -> int for V in int) = p(f: g);\n",
        // The form the bucket tests below use with `int | f64`, accepted with `int`.
        "p(f: (x: ((int, bool) | (int, bool, bool),) | ((int, int),) | ((int, int, int),)) \
         -> int) = 0;\n\
         q(g: (x: ((int, bool) | (int, bool, bool),) | ((int, U) | (int, U, U),)) -> int \
         for U in int) = p(f: g);\n",
        // One level, `->?`, an unbounded variable in the parameter only: at every instance
        // the answer is `int`, within the partial arrow's result.
        "p(f: (x: (int, int) | String) ->? int) = 0;\nq(g: (x: (T, T)) -> int) = p(f: g);\n",
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    }
    // The same with a result outside the partial arrow's: refused at every instance.
    let src =
        "p(f: (x: (int, int) | String) ->? int) = 0;\nq(g: (x: (T, T)) -> String) = p(f: g);\n";
    assert_eq!(type_errors(src).len(), 1, "{src}");
    // Two levels, `->?` at the outer arrow, `g` of exact arrows: the types fit, and the one
    // error is that a call through `f` of an `h` outside `g`'s domain must give `#notFound`,
    // which no test at run time can tell, since a function value does not show its domain
    // (FAIL-partial-slot-untestable-domain). Before that row these were accepted, and such a
    // call ran `g` on an `h` it does not take.
    for src in [
        "p(f: (h: (x: ((int, int),) | ((int, int, int),)) ->? int) ->? int) = 0;\n\
         q(g: (h: (x: ((V, int),)) -> int) -> int for V in int) = p(f: g);\n",
        "p(f: (h: (x: ((int, bool) | (int, bool, bool),) | ((V, V) | (V, V, V),)) ->? int \
         for V in int) ->? int) = 0;\n\
         q(g: (h: (x: ((V, int),) | ((V, int, int),)) -> int) -> int for V in int) = p(f: g);\n",
    ] {
        let errors = type_errors(src);
        assert_eq!(errors.len(), 1, "{src}: {errors:?}");
        assert!(
            errors[0].contains("`h` is a function, whose domain its value does not show"),
            "{src}: {errors:?}"
        );
    }
}

/// `V` an own variable of `g`, bound by the outer comparison, and `V` of `f`'s `h` its own, in
/// partial domains: `g`'s `h` answers `int` at every instance, within `f`'s `h`'s result, so `g`
/// fits (FAIL-fn-domain-bindable-variable), as it does with `int` for `V`
/// (`a_function_whose_parameter_holds_a_bound_variable_fits_a_domain_its_instance_fits`).
/// This was the form of
/// `an_own_variable_of_an_outer_comparison_and_one_of_the_same_name_inside_print_apart`, which
/// printed the bucket refused here before; with exact arrows that test now reaches the bucket and
/// prints the two variables both as `V`, which is FAIL-print-two-variables-one-name. The types fit;
/// the one error is that a call through `f` of an `h` outside `g`'s domain must give `#notFound`,
/// which no test at run time can tell (FAIL-partial-slot-untestable-domain).
#[test]
fn an_own_variable_of_an_outer_comparison_bound_in_a_partial_domain_fits() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let shapes = "((int, bool) | (int, bool, bool),) | ((V, V) | (V, V, V),)";
    let src = format!(
        "p(f: (h: (x: {shapes}) ->? int for V in int | f64) ->? int) = 0;\n\
         q(g: (h: (x: ((V, int),) | ((V, int, int),)) -> int) -> int for V in int | f64) \
         = p(f: g);\n"
    );
    let errors = type_errors(&src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("`h` is a function, whose domain its value does not show"),
        "{errors:?}"
    );
}

/// The int literal `i` as a kernel type.
fn klit(i: usize) -> Type {
    Type::lit(&zed_kernel::value::Value::Int(i as i64)).expect("an int")
}

/// `n` tuple types `(int, (i, #a))` less `(i, (i, #a))`, which hold data, and a last
/// `(int, (n, last))`: the input of `held_wide` that walks a union of rows.
fn wide_rows(n: usize, last: Type) -> Ty {
    let row = |i: usize, c: Type| Type::tuple(vec![Type::int(), Type::tuple(vec![klit(i), c])]);
    let mut ts: Vec<Type> = (0..n)
        .map(|i| {
            &row(i, Type::atom("a"))
                - &Type::tuple(vec![klit(i), Type::tuple(vec![klit(i), Type::atom("a")])])
        })
        .collect();
    ts.push(row(n, last));
    Ty::set(Type::union_all(ts))
}

/// A pair nested `n` deep whose two components are one node, on `last`: `2^n` paths and `n`
/// nodes.
fn pair_nested(n: usize, last: Type) -> Ty {
    Ty::set((0..n).fold(last, |t, _| Type::tuple(vec![t.clone(), t])))
}

/// `((..), int)` taken away from `(..)` `n` times.
fn taken_away(n: usize) -> Type {
    let tuples = Type::universe(Universe::Tuple);
    let wide_int = Type::tuple(vec![tuples.clone(), Type::int()]);
    (0..n).fold(wide_int, |t, _| &tuples - &t)
}

/// The exclusive or of `n` tuple types `(i, int)` and a last `(n, last)`: each node reached by
/// a path to `true` both kept and taken away, so `2^n` paths and `n` nodes.
fn parity(n: usize, last: Type) -> Ty {
    let rows = (0..n).map(|i| Type::tuple(vec![klit(i), Type::int()]));
    let rows = rows.chain([Type::tuple(vec![klit(n), last])]);
    Ty::set(rows.fold(Type::empty(), |p, r| &(&p - &r) | &(&r - &p)))
}

/// `n` tuples of `2·log2 n` components (`n` at least 2), the tuple `i` the point 0 where a
/// different arrangement `bits(i)` has a 1 and `int` elsewhere, and the `n` values `i`, 0 where
/// `bits(i)` has a 1 and 1 elsewhere, each held by the tuple `i` and by each tuple whose points
/// are among those places, which few are.
fn arrangements(n: usize) -> (Ty, zed_kernel::value::Value) {
    use zed_kernel::value::Value;
    let width = 2 * n.ilog2() as usize;
    // A different arrangement for each `i`, never all `int`, which would hold every value.
    let bits = |i: usize| ((i as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> (64 - width)) | 1;
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
}

/// A program whose call is refused on a bucket of two tuple shapes, each tuple ending in `n`
/// functions `(y: int) -> int`, and the text of the bucket its error names.
fn bucket_of_functions(n: usize) -> (String, String) {
    let hs = ", (y: int) -> int".repeat(n);
    let shapes =
        format!("((int, bool{hs}) | (int, bool, bool{hs}),) | ((int, U{hs}) | (int, U, U{hs}),)");
    // A domain is exact (DESIGN.md sec:type_language), so `f` also takes the tuples of `g`'s
    // first shape (FAIL-types-fn-param-exact-domain).
    let src = format!(
        "p(f: (x: ((int, bool{hs}) | (int, bool, bool{hs}),) | ((int, int{hs}),) \
         | ((int, int, int{hs}),)) -> int) = 0;\n\
         q(g: (x: {shapes}) -> int for U in int | f64) = p(f: g);\n"
    );
    (src, format!("one of the shapes {shapes}, which"))
}

/// A function type nested `n + 1` levels deep, level `k` from the inside binding the eight
/// variables `A{k + from}_0` to `A{k + from}_7`, each held by a parameter, and holding the level
/// inside it as its first parameter. Each is bounded by `int | f64`: a variable bounded by one
/// carrier is read as that carrier (FAIL-fn-domain-bindable-variable), so with `int` no level
/// reads a variable under its name, and none meets the clash of names.
fn nested_functions(n: usize, from: usize) -> String {
    (0..=n).fold(String::new(), |t, k| {
        let vs: Vec<String> = (0..8).map(|j| format!("A{}_{j}", k + from)).collect();
        let params = vs.iter().enumerate().map(|(j, v)| format!("y{j}: {v}"));
        let bounds = vs.iter().map(|v| format!("{v} in int | f64"));
        let params: Vec<String> = match k {
            0 => params.collect(),
            _ => std::iter::once(format!("h: {t}")).chain(params).collect(),
        };
        format!(
            "({}) -> {} for {}",
            params.join(", "),
            vs[0],
            bounds.collect::<Vec<_>>().join(", ")
        )
    })
}

/// Small instance of `bench::a_union_of_kind_wide_and_exact_members_scales`
/// (TEST-bench-move-l0123, author P169): unions of 1 to 12 members, kind-wide differences and
/// exact members in turn, print exactly and read back as a subtype of the union.
#[test]
fn a_union_of_kind_wide_and_exact_members_prints_and_reads_back() {
    for n in 1..=12 {
        let t = mixed(n);
        let s = t.surface();
        assert!(s.exact, "{n}: {s}");
        let back = ty(&s.to_string());
        assert!(back.subtype(&Ty::set(t)), "{n}: {s}");
    }
}

/// Small instance of `bench::narrowing_tuple_shapes_by_a_kind_wide_type_scales`
/// (TEST-bench-move-l0123, author P169): 1 to 8 shapes `(i, i)` narrowed by `(..) \ (0, 0)`:
/// `is` keeps every shape but `(0, 0)`, and `is not` keeps `(0, 0)` alone.
#[test]
fn narrowing_tuple_shapes_by_a_kind_wide_type_keeps_the_shapes_on_each_side() {
    for n in 1..=8 {
        let (t, w) = shapes(n);
        assert_eq!(t.meet(&w).tuples.len(), n - 1, "{n}");
        assert_eq!(t.diff(&w).tuples.len(), 1, "{n}");
    }
}

/// Small instance of `bench::the_function_part_of_a_kind_wide_part_is_found_in_linear_time`
/// (TEST-bench-move-l0123, author P169): its four families of tuple types at sizes 1 to 5,
/// each with and without a `(..)` that may hold a function.
#[test]
fn the_function_part_of_a_kind_wide_part_is_found() {
    let int = Type::int;
    let tuples = Type::universe(Universe::Tuple);
    let shape = Type::tuple(vec![int(), &int() | &Type::atom("a")]);
    let kept = Type::tuple(vec![&int() | &tuples, int()]);
    for n in 1..=5 {
        assert_eq!(wide_rows(n, Type::atom("a")).held_wide(), None, "{n}");
        assert_eq!(
            wide_rows(n, tuples.clone()).held_wide(),
            Some(tuples.clone()),
            "{n}"
        );
        assert_eq!(pair_nested(n, int()).held_wide(), None, "{n}");
        assert_eq!(
            pair_nested(n, &int() | &tuples).held_wide(),
            Some(tuples.clone()),
            "{n}"
        );
        assert_eq!(Ty::set(&shape & &taken_away(n)).held_wide(), None, "{n}");
        // At even `n` the tuple type is kept and holds a function, as the benchmark checks at
        // its sizes, all even. At odd `n` the meet is `(int, int)`, which holds none, but
        // `function_part` walks `(int | (..), int)`, a tuple type a path to `true` takes, and
        // `held_wide` gives `(..)`, so the checker refuses `String(p)` on it: the case
        // `Type::function_part` gives up on (COMPLEXITY.md K103, coNP-hard in general), not
        // checked here.
        if n % 2 == 0 {
            assert_eq!(
                Ty::set(&kept & &taken_away(n)).held_wide(),
                Some(tuples.clone()),
                "{n}"
            );
        }
        assert_eq!(parity(n, int()).held_wide(), None, "{n}");
        assert_eq!(
            parity(n, tuples.clone()).held_wide(),
            Some(tuples.clone()),
            "{n}"
        );
    }
}

/// Small instance of `bench::payloads_that_hold_functions_are_compared_in_the_size_of_the_union`
/// (TEST-bench-move-l0123, author P169): 1 to 6 payloads that hold functions, of several atoms
/// and of one atom in the other order, in their wider type and not in a type whose functions
/// return another result.
#[test]
fn payloads_that_hold_functions_are_compared_payload_by_payload() {
    let union = |n: usize, f: &dyn Fn(usize) -> String| {
        let parts: Vec<String> = (0..n).map(|i| format!("#a{i}({})", f(i))).collect();
        ty(&parts.join(" | "))
    };
    let one = |n: usize, order: &dyn Fn(usize) -> usize, r: &str| {
        let parts: Vec<String> = (0..n)
            .map(|i| format!("#a((int) -> {r}, {})", order(i)))
            .collect();
        ty(&parts.join(" | "))
    };
    for n in 1..=6 {
        let small = union(n, &|i| format!("(int) -> #r{i}, {i}"));
        let wide = union(n, &|i| format!("(int) -> #r{i} | #s, int"));
        assert!(small.subtype(&wide), "{n}");
        assert!(
            !small.subtype(&union(n, &|i| format!("(int) -> #s, {i}"))),
            "{n}"
        );
        let small = one(n, &|i| i, "int");
        assert!(small.subtype(&one(n, &|i| n - 1 - i, "int")), "{n}");
        assert!(!small.subtype(&one(n, &|i| n - 1 - i, "String")), "{n}");
    }
}

/// Small instance of
/// `bench::payloads_with_fields_and_tuples_that_hold_functions_are_compared_in_the_size_of_the_union`
/// (TEST-bench-move-l0123, author P169): 1 to 6 payloads with fields, one of them a function,
/// in the payload with the wider field and not in the one whose function returns `String`.
#[test]
fn payloads_with_fields_that_hold_functions_are_compared_payload_by_payload() {
    let whole = ty("#a(x: int, f: (int) -> int)");
    let not = ty("#a(x: int, f: (int) -> String)");
    for n in 1..=6 {
        let fields: Vec<String> = (0..n)
            .map(|i| format!("#a(x: {i}, f: (int) -> int)"))
            .collect();
        let fields = ty(&fields.join(" | "));
        assert!(fields.subtype(&whole), "{n}");
        assert!(!fields.subtype(&not), "{n}");
    }
}

/// Small instance of `bench::payloads_with_a_variable_are_searched_by_their_keys`
/// (TEST-bench-move-l0123, author P169): 1 to 6 payloads `#a(String, i)` in the shapes
/// `#a(T, i)` listed in the other order bind `T` to `String`, and one payload more is not held.
#[test]
fn payloads_with_a_variable_are_found_by_their_keys_in_any_order() {
    for n in 1..=6 {
        let l = with_payloads("a", (0..n).map(|i| vec![ty("String"), int(i)]).collect());
        let r = with_payloads("a", (0..n).rev().map(|i| vec![var("T"), int(i)]).collect());
        let wrong = with_payloads("a", (0..=n).map(|i| vec![ty("String"), int(i)]).collect());
        let want = Some(vec![("T".into(), "String".into())]);
        assert_eq!(bound(&l, &r), want, "{n}");
        assert_eq!(bound(&wrong, &r), None, "{n}");
        assert_eq!(wrong.refused(&r), "", "{n}");
    }
}

/// Small instance of `bench::tuples_with_a_variable_are_searched_by_their_keys`
/// (TEST-bench-move-l0123, author P169): 1 to 6 tuples `(String, i)` in the tuples `(T, i)`
/// listed in the other order bind `T` to `String`.
#[test]
fn tuples_with_a_variable_are_found_by_their_keys_in_any_order() {
    for n in 1..=6 {
        let l: Vec<Ty> = (0..n)
            .map(|i| Ty::tuple(vec![ty("String"), int(i)]))
            .collect();
        let r: Vec<Ty> = (0..n)
            .rev()
            .map(|i| Ty::tuple(vec![var("T"), int(i)]))
            .collect();
        assert_eq!(
            bound(&Ty::union_all(&l), &Ty::union_all(&r)),
            Some(vec![("T".into(), "String".into())]),
            "{n}"
        );
    }
}

/// Small instance of
/// `bench::a_refused_bucket_of_long_shapes_that_repeat_a_variable_prints_in_linear_time`
/// (TEST-bench-move-l0123, author P169): shapes of 2 to 5 components, `T` at each place after the
/// first, print `T` at each place in the refusal.
#[test]
fn a_refused_bucket_of_long_shapes_prints_the_variable_at_each_place() {
    let row = |head: Ty, rest: &dyn Fn() -> Ty, n: usize| {
        Ty::tuple(
            std::iter::once(head)
                .chain((1..n).map(|_| rest()))
                .collect(),
        )
    };
    for n in 2..=5 {
        let l = Ty::union_all(&[row(int(3), &|| int(5), n), row(int(4), &|| int(6), n)]);
        let r = Ty::union_all(&[
            row(ty("1 | 2"), &|| var("T"), n),
            row(ty("int"), &|| var("T"), n),
        ]);
        let bucket = format!("(1 | 2{ts}) | (int{ts})", ts = ", T".repeat(n - 1));
        let why = l.refused(&r);
        assert!(
            why.contains(&format!("one of the shapes {bucket}, which")),
            "{n}: {why}"
        );
    }
}

/// Small instance of `bench::subtracting_tuples_scales` and `bench::meeting_tuples_scales`
/// (TEST-bench-move-l0123, author P169): the four families at sizes 1 to 6 keep and meet the
/// counted tuples; odd sizes check that `n / 2` rounds down.
#[test]
fn subtracting_and_meeting_tuples_keeps_the_tuples_that_share_a_value() {
    for n in 1..=6 {
        for (what, t, u, left, met) in tuple_families(n) {
            assert_eq!(t.diff(&u).tuples.len(), left, "{what} at {n}");
            // A tuple met twice, `(bool, i)` with `(true, i)` and `(false, i)`, gives two.
            let met = if what == "together" { 2 * met } else { met };
            assert_eq!(t.meet(&u).tuples.len(), met, "{what} at {n}");
        }
    }
}

/// Small instance of `bench::meeting_and_subtracting_tuples_of_many_patterns_costs_the_patterns`
/// (TEST-bench-move-l0123, author P169): points against two arrangements of points and `int`
/// at sizes 1 to 6, and tuples of many arrangements at 4 and 8 (`many_patterns` needs at least
/// 2).
#[test]
fn meeting_and_subtracting_tuples_of_several_arrangements_keeps_the_right_tuples() {
    for n in 1..=6 {
        let (points, open) = two_patterns(n);
        assert!(points.diff(&open).tuples.is_empty(), "{n}");
        assert_eq!(points.meet(&open).tuples.len(), n, "{n}");
        assert_eq!(open.meet(&points).tuples.len(), n, "{n}");
    }
    for n in [4, 8] {
        let (ones, zeros) = many_patterns(n);
        let met = ones.meet(&zeros).tuples.len();
        assert!(met <= n * n, "{n}: {met}");
        let left = ones.diff(&zeros).tuples.len();
        assert!(left <= n, "{n}: {left}");
    }
}

/// Small instance of `bench::meets_of_many_tuples_scales` (TEST-bench-move-l0123, author P169):
/// the four families at sizes 1 to 6, each the same both ways round.
#[test]
fn meets_of_unions_of_tuples_finds_the_pair_that_shares_a_value() {
    for n in 1..=6 {
        for (what, t, u, shares) in meets_families(n) {
            assert_eq!(t.meets(&u), shares, "{what} at {n}");
            assert_eq!(u.meets(&t), shares, "{what} at {n}");
        }
    }
}

/// Small instance of `bench::meets_of_tuples_of_many_patterns_costs_the_patterns`
/// (TEST-bench-move-l0123, author P169): tuples of many arrangements at 4 and 8 meet exactly
/// when their meet has a tuple, both ways round.
#[test]
fn meets_of_tuples_of_many_arrangements_agrees_with_the_meet() {
    for n in [4, 8] {
        let (ones, zeros) = many_patterns(n);
        let shares = !ones.meet(&zeros).tuples.is_empty();
        assert_eq!(ones.meets(&zeros), shares, "{n}");
        assert_eq!(zeros.meets(&ones), shares, "{n}");
    }
}

/// Small instance of `bench::contains_of_many_tuples_scales` (TEST-bench-move-l0123, author
/// P169): the four families at sizes 1 to 6.
#[test]
fn contains_of_unions_of_tuples_finds_each_value() {
    for n in 1..=6 {
        for (what, t, v, held) in contains_families(n) {
            assert_eq!(t.contains(&v), held, "{what} at {n}");
        }
    }
}

/// Small instance of `bench::contains_of_tuples_of_many_patterns_costs_the_patterns`
/// (TEST-bench-move-l0123, author P169): tuples of many arrangements at 2, 4 and 8 hold each
/// value made to fit one of them.
#[test]
fn contains_of_tuples_of_many_arrangements_holds_each_value() {
    for n in [2, 4, 8] {
        let (t, v) = arrangements(n);
        assert!(t.contains(&v), "{n}");
    }
}

/// Small instance of `bench::the_meet_of_many_payloads_of_one_atom_scales` and
/// `bench::the_difference_of_many_payloads_of_one_atom_scales` (TEST-bench-move-l0123, author
/// P169): 1 to 6 payloads `#a(i, i)` met with `#a(i, int)` are themselves, and less them are
/// empty.
#[test]
fn many_payloads_of_one_atom_met_with_or_less_wider_ones() {
    for n in 1..=6 {
        let (l, r) = payload_pairs(n);
        let met = l.meet(&r);
        assert!(met.subtype(&l) && l.subtype(&met), "{n}: {met}");
        assert!(l.diff(&r).is_empty(), "{n}");
    }
}

/// Small instance of `bench::the_difference_of_many_wide_tuple_types_scales`
/// (TEST-bench-move-l0123, author P169): 1 to 6 tuple types `(i, (..))` less `(i, (int, int))`
/// keep `(i, (1, 2, 3))` and lose `(i, (1, 2))`.
#[test]
fn many_wide_tuple_types_less_pairs_keep_the_other_tuples() {
    for n in 1..=6 {
        let (l, r) = wide_pairs(n);
        let d = l.diff(&r);
        assert!(!d.is_empty(), "{n}");
        for i in [0, n - 1] {
            assert!(ty(&format!("({i}, (1, 2, 3))")).subtype(&d), "{n}: {d}");
            assert!(!ty(&format!("({i}, (1, 2))")).subtype(&d), "{n}: {d}");
        }
    }
}

/// Small instance of `bench::a_refused_bucket_of_tuples_of_many_functions_prints_in_linear_time`
/// (TEST-bench-move-l0123, author P169): tuples of a refused bucket holding 1 to 3 functions
/// print each function in the bucket.
#[test]
fn a_refused_bucket_of_tuples_of_several_functions_prints_each_function() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    for n in 1..=3 {
        let (src, shapes) = bucket_of_functions(n);
        let errors = type_errors(&src);
        assert!(
            errors.len() == 1 && errors[0].contains(shapes.as_str()),
            "{n}: {errors:?}"
        );
    }
}

/// Small instance of
/// `bench::function_types_nested_deep_whose_variables_share_names_across_the_two_fit_in_linear_time`
/// (TEST-bench-move-l0123, author P169): function types 1 to 4 levels deep, whose levels share
/// variable names across the two, fit; 1 level has no clash and is the control.
#[test]
fn function_types_whose_variables_share_names_across_the_two_fit() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    for n in 0..=3 {
        let text = format!(
            "p(f: {}) = 0;\nq(g: {}) = p(f: g);\n",
            nested_functions(n, 1),
            nested_functions(n, 0)
        );
        assert_eq!(type_errors(&text), Vec::<String>::new(), "{text}");
    }
}

/// `(h: … (h: (y: v) -> int, y: v) -> int …, y: v) -> int for v in int | f64`, `n` levels of
/// `h` around `(y: v) -> int`: each level holds the outer function's own bounded variable.
fn nest_holding_outer_variable(n: usize, v: &str) -> String {
    let t = (1..=n).fold(format!("(y: {v}) -> int"), |t, _| {
        format!("(h: {t}, y: {v}) -> int")
    });
    format!("{t} for {v} in int | f64")
}

/// FAIL-types-fn-outer-variable-nest: a function type whose parameter is a function type
/// holding the outer function's own bounded variable, nested n deep, fits the same type with the
/// variable renamed (DESIGN sec:type_resolution rule 6, `U` bound to `T`). n = 0 is the control,
/// accepted before the fix.
#[test]
fn function_types_nested_whose_inner_levels_hold_the_outer_variable_fit() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    for n in 0..=6 {
        let src = format!(
            "p(f: {}) = 0;\nq(g: {}) = p(f: g);\n",
            nest_holding_outer_variable(n, "T"),
            nest_holding_outer_variable(n, "U")
        );
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    }
}

/// The negative control of `function_types_nested_whose_inner_levels_hold_the_outer_variable_fit`:
/// where the function `g` takes is not the one each instance of `f` passes, `g` does not fit,
/// though the variable is read at its binding inside the function. `f`'s caller picks `T`, and
/// at `T = f64` passes an `h` that takes only `f64`: `g` asks for one that takes `int` (the
/// innermost domain written `int`, at every depth), or allows `U = int` only. The parameters in
/// the other order, `y` first, still fit (the order the fix compares them in).
#[test]
fn function_types_nested_whose_inner_levels_differ_from_the_outer_variable_do_not_fit() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let refused = |src: &str| {
        let errors = type_errors(src);
        errors.len() == 1 && errors[0].starts_with("`p` does not take")
    };
    for n in 1..=4 {
        let f = nest_holding_outer_variable(n, "T");
        // The innermost function takes `int` whatever `U` is.
        let inner_int =
            nest_holding_outer_variable(n, "U").replacen("(y: U) -> int", "(y: int) -> int", 1);
        let src = format!("p(f: {f}) = 0;\nq(g: {inner_int}) = p(f: g);\n");
        assert!(refused(&src), "{src}\n{:?}", type_errors(&src));
        let narrow =
            nest_holding_outer_variable(n, "U").replace("for U in int | f64", "for U in int");
        let src = format!("p(f: {f}) = 0;\nq(g: {narrow}) = p(f: g);\n");
        assert!(refused(&src), "{src}\n{:?}", type_errors(&src));
    }
    let src = "p(f: (y: T, h: (y: T) -> int) -> int for T in int | f64) = 0;\n\
               q(g: (y: U, h: (y: U) -> int) -> int for U in int | f64) = p(f: g);\n";
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
}

/// `#a(int, …, int)` with `w` items, and the union of the `k` cuts `#a(c(j), …, c(j))` with
/// `w` items, for j < k.
fn wide_payload_cuts(w: usize, k: usize, c: &dyn Fn(usize) -> String) -> (Ty, Ty) {
    let whole = format!("#a({})", vec!["int"; w].join(", "));
    let cuts: Vec<String> = (0..k)
        .map(|j| format!("#a({})", vec![format!("({})", c(j)); w].join(", ")))
        .collect();
    (ty(&whole), ty(&cuts.join(" | ")))
}

/// The numbers in `range`, as a union of literals.
fn numbers(range: impl Iterator<Item = usize>) -> String {
    range.map(|v| v.to_string()).collect::<Vec<_>>().join(" | ")
}

/// The number of payload shapes of `#a` in `t`.
fn shapes_of_a(t: &Ty) -> usize {
    t.payloads
        .get("a")
        .and_then(|s| s.as_ref())
        .map_or(0, |s| s.len())
}

#[test]
fn a_payload_less_many_cuts_is_the_difference_in_few_shapes() {
    // FAIL-types-shape-rest-many-cuts: the rest of a payload shape held in part by k shapes
    // is built item by item, the values of each item split by which shapes hold them. Before,
    // each shape cut every shape left into up to w, so k nested cuts `#a(0..j, …)` left
    // C(k + w - 1, w - 1) shapes where w hold the rest (969 for w = 4, k = 16). The cuts by
    // bit need w^k shapes in any union of shapes (proof at `shape_rest`), and get that many.
    for w in 1..=4 {
        for k in 1..=5 {
            let nested = wide_payload_cuts(w, k, &|j| numbers(0..=j));
            let bits =
                wide_payload_cuts(w, k, &|j| numbers((0..1 << k).filter(|v| v >> j & 1 == 1)));
            for (what, (whole, cuts), want) in
                [("nested", nested, w), ("by bit", bits, w.pow(k as u32))]
            {
                let rest = whole.diff(&cuts);
                assert!(
                    rest.meet(&cuts).is_empty(),
                    "{what}, w = {w}, k = {k}: {rest}"
                );
                assert!(rest.subtype(&whole), "{what}, w = {w}, k = {k}: {rest}");
                // The rest and the cuts together hold the whole. This asks whether the
                // difference is empty, not `whole.subtype(…)`, which answers no for the cuts
                // by bit at w = k = 3 (FAIL-types-shape-union-sub-incomplete).
                assert!(
                    whole.diff(&rest.union(&cuts)).is_empty(),
                    "{what}, w = {w}, k = {k}: {rest}"
                );
                assert_eq!(shapes_of_a(&rest), want, "{what}, w = {w}, k = {k}: {rest}");
            }
        }
    }
    // Cuts that overlap in a chain, and one that misses `s` at its last item.
    let (whole, cuts) = wide_payload_cuts(3, 6, &|j| numbers(2 * j..2 * j + 3));
    let cuts = cuts.union(&ty("#a(int, int, String)"));
    let rest = whole.diff(&cuts);
    assert!(
        rest.meet(&cuts).is_empty() && rest.subtype(&whole),
        "{rest}"
    );
    assert!(whole.diff(&rest.union(&cuts)).is_empty(), "{rest}");
}

mod bench;

/// A payload shape within a union of shapes that together hold it is a subtype of the union
/// (FAIL-types-shape-union-sub-incomplete): `#a(int, …, int)` within the cuts `#a(B_j, …, B_j)`
/// (B_j the numbers below 2^k with bit j set) and the rest of it less them, which the kernel
/// refuses to decide, as it would split more than one item at once. With the last cut left
/// out, the point `#a(2^(k-1), …)` is in no shape, and the answer is no. Each point of numbers
/// below 2^k, or 99, is in the union, as a check of the union apart from the comparison.
#[test]
fn a_payload_shape_held_by_many_shapes_together_is_a_subtype_of_their_union() {
    for k in 1..=3 {
        for w in 1..=3 {
            let c = |j: usize| numbers((0..1 << k).filter(|v| v >> j & 1 == 1));
            let (whole, cuts) = wide_payload_cuts(w, k, &c);
            let all = whole.diff(&cuts).union(&cuts);
            assert!(whole.diff(&all).is_empty(), "control, w = {w}, k = {k}");
            assert!(whole.subtype(&all), "w = {w}, k = {k}: {all}");
            let fewer = match k {
                1 => Ty::empty(),
                _ => wide_payload_cuts(w, k - 1, &c).1,
            };
            let partial = whole.diff(&cuts).union(&fewer);
            assert!(!whole.subtype(&partial), "w = {w}, k = {k}: {partial}");
            let values: Vec<usize> = (0..1 << k).chain([99]).collect();
            let mut point = vec![0; w];
            loop {
                let text = point.iter().map(|&p| values[p].to_string());
                let p = ty(&format!("#a({})", text.collect::<Vec<_>>().join(", ")));
                assert!(p.subtype(&all), "w = {w}, k = {k}: {p} in {all}");
                let Some(at) = point.iter().position(|&p| p + 1 < values.len()) else {
                    break;
                };
                point[at] += 1;
                point[..at].fill(0);
            }
        }
    }
}

/// The payload shapes of an atom both sides list are decided by the rest of each shape less the
/// other side's shapes near it, and the rest of the type by the kernel
/// (`Comparing::payloads_by_rest`, PERF-types-payload-union-kernel-refusal): a shape not held
/// gives no, a bare atom beside the payloads, a payload of another atom, a scalar and a payload
/// the other side does not list are each still compared, and a shape held by two shapes
/// together gives yes. A bare atom `#b` is the atom with no payload, so it does not hold `#b(1)`.
#[test]
fn payload_shapes_decided_by_their_rest_leave_the_rest_of_the_type_compared() {
    for (a, b, want) in [
        ("#a(1) | #a(2)", "#a(1)", false),
        ("#a(1) | #a(2)", "#a(1 | 2)", true),
        ("#a(1 | 2, 1 | 2)", "#a(1, 1 | 2) | #a(2, 1 | 2)", true),
        ("#a(1 | 2, 1 | 2)", "#a(1, 1 | 2) | #a(2, 1)", false),
        ("#a | #a(1)", "#a(int)", false),
        ("#a | #a(1)", "#a | #a(int)", true),
        ("#a(1) | #b(1)", "#a(int) | #b(2)", false),
        ("#a(1) | #b(1)", "#a(int) | #b(int)", true),
        ("#a(1) | 5", "#a(int)", false),
        ("#a(1) | 5", "#a(int) | int", true),
        ("#a(1) | #b(1)", "#a(int) | #b", false),
        ("#a(1)", "#a", false),
        ("#a(String)", "#a(int)", false),
    ] {
        let (at, bt) = (ty(a), ty(b));
        assert_eq!(at.subtype(&bt), want, "{a} within {b}");
        assert_eq!(at.diff(&bt).is_empty(), want, "control: {a} less {b}");
    }
}

/// A random payload item of data, `d` levels deep: literals, `int`, `bool`, an atom, tuples,
/// payloads, unions and meets.
fn random_item(r: &mut zed_tests::instances::Rng, d: usize) -> String {
    match r.below(if d == 0 { 4 } else { 8 }) {
        0 => r.below(3).to_string(),
        1 => "int".into(),
        2 => "bool".into(),
        3 => "#c".into(),
        4 => format!("({}, {})", random_item(r, d - 1), random_item(r, d - 1)),
        5 => format!("#b({})", random_item(r, d - 1)),
        6 => format!(
            "(({}) | ({}))",
            random_item(r, d - 1),
            random_item(r, d - 1)
        ),
        _ => format!(
            "(({}) & ({}))",
            random_item(r, d - 1),
            random_item(r, d - 1)
        ),
    }
}

/// A payload shape of data is within a union of shapes exactly when it less the union is
/// empty. Where both sides have kernel types, `diff` takes the rest of each shape
/// (`Comparing::shape_rest`) and asks the kernel's verdict on it before it asks `sub_near`
/// whether the union holds the shape (a3cee3606, PROOF-diff-exact-skip); this checks that the
/// order changes no answer, against the comparison, which does not go through `diff`. A new
/// seed each run, printed (`ZED_TEST_SEED=<seed>` repeats it).
#[test]
fn a_payload_shape_is_within_a_union_exactly_when_its_rest_is_empty() {
    let (mut r, seed) = zed_tests::instances::Rng::fresh("a payload shape within a union");
    let shape = |r: &mut zed_tests::instances::Rng| match r.below(2) {
        0 => format!("#a({}, {})", random_item(r, 2), random_item(r, 2)),
        _ => format!(
            "#a({}, {}, {})",
            random_item(r, 2),
            random_item(r, 1),
            random_item(r, 2)
        ),
    };
    for _ in 0..1000 {
        let p = shape(&mut r);
        let k = 1 + r.below(6);
        let u = (0..k)
            .map(|_| shape(&mut r))
            .collect::<Vec<_>>()
            .join(" | ");
        let (pt, ut) = (ty(&p), ty(&u));
        assert_eq!(
            pt.subtype(&ut),
            pt.diff(&ut).is_empty(),
            "{p} within {u}: {} (ZED_TEST_SEED={seed})",
            pt.diff(&ut)
        );
    }
}

/// The pigeonhole rows for `pigeons` pigeons and `holes` holes: the tuple of one `#f | #t`
/// for each pigeon and hole (`#t` where the pigeon sits in the hole), and the rows that
/// forbid a placement: a pigeon in no hole, and two pigeons in one hole. The whole is within
/// the union of the forbidden rows exactly when no placement puts each pigeon in a hole of
/// its own, that is when `pigeons > holes`.
fn pigeon_rows(pigeons: usize, holes: usize) -> (String, Vec<String>) {
    let d = pigeons * holes;
    let row = |hit: &dyn Fn(usize) -> bool, b: &str| {
        let cs: Vec<String> = (0..d)
            .map(|j| {
                if hit(j) {
                    b.to_string()
                } else {
                    "(#f | #t)".into()
                }
            })
            .collect();
        format!("({})", cs.join(", "))
    };
    let whole = row(&|_| false, "");
    let mut forbidden = Vec::new();
    for p in 0..pigeons {
        forbidden.push(row(&|j| j / holes == p, "#f"));
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                forbidden.push(row(&|j| j == p * holes + h || j == q * holes + h, "#t"));
            }
        }
    }
    (whole, forbidden)
}

/// A payload `#a(P)` with `P` the pigeonhole tuple, against the union of `#a(F)` for each
/// forbidden row `F` ([`pigeon_rows`]), alone and with an arm `#b(x: int)` that has no kernel
/// type. For 4 pigeons and 3 holes the whole is within the union, and the kernel cannot show
/// it (`TupleSplit`), so the answer is refused. Before (PROOF-diff-exact-skip) the comparison
/// with the field arm said a plain no with no refusal: the rest of the shape less the near
/// shapes was empty but not proved empty by `is_empty`, and was read as a value outside.
/// With 2 or 3 pigeons in one hole fewer the yes is decided, and with a forbidden row left
/// out the no is decided, with no refusal.
#[test]
fn a_payload_whose_tuple_item_needs_a_split_of_many_components_is_refused() {
    let payloads = |rows: &[String], field: bool| {
        let mut arms: Vec<String> = rows.iter().map(|f| format!("#a({f})")).collect();
        if field {
            arms.push("#b(x: int)".into());
        }
        ty(&arms.join(" | "))
    };
    for (pigeons, holes) in [(2, 1), (3, 2)] {
        let (whole, forbidden) = pigeon_rows(pigeons, holes);
        let pw = ty(&format!("#a({whole})"));
        for field in [false, true] {
            let what = format!("{pigeons} pigeons, {holes} holes, field arm {field}");
            let all = payloads(&forbidden, field);
            assert!(pw.subtype(&all), "{what}");
            assert_eq!(pw.refused(&all), "", "{what}");
            assert!(pw.diff(&all).is_empty(), "{what}: {}", pw.diff(&all));
            // The last row forbids the last two pigeons the last hole; with it left out they
            // may share it, the others each in a hole of its own, and the whole is outside.
            let fewer = payloads(&forbidden[..forbidden.len() - 1], field);
            assert!(!pw.subtype(&fewer), "{what}, a row left out");
            assert_eq!(pw.refused(&fewer), "", "{what}, a row left out");
        }
    }
    let (whole, forbidden) = pigeon_rows(4, 3);
    let pw = ty(&format!("#a({whole})"));
    for field in [false, true] {
        let all = payloads(&forbidden, field);
        assert!(!pw.subtype(&all), "field arm {field}");
        let why = pw.refused(&all);
        assert!(
            why.contains("splitting more than one of its components"),
            "field arm {field}: {why:?}"
        );
        // The difference may hold more than the empty rest, and never a value outside `pw`.
        assert!(pw.diff(&all).subtype(&pw), "field arm {field}");
    }
}

/// A generic function type whose parameter is a function type holding its variable fits itself
/// with the variable renamed (DESIGN.md sec:type_resolution rule 6: the two are one type).
/// FAIL-types-generic-fn-param-renamed-refused: ten of these were refused against themselves
/// renamed, `q(g: X') = p(f: g)` answering that `p` does not take `g`, since a bounded variable
/// held only inside a function parameter was never bound. Nine were fixed by 988743bce
/// (FAIL-types-fn-only-bounded-variable); the function held in a tuple, `((y: int) -> T,)`,
/// was still refused, as the kernel's form compared the two functions with no binding, and is
/// now compared by the rule of one shape (`Comparing::sub_near`). The pairs after them are
/// controls: the same types with a bound, a result or a component that differs, which do not
/// fit, and the bound written in another order, which does.
#[test]
fn a_generic_function_type_holding_a_function_of_its_variable_fits_itself_renamed() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let sigs = [
        "(h: ((y: int) -> T, int)) -> int for T in int | f64",
        "(h: (((y: int) -> T,),)) -> int for T in int | f64",
        "(h: ((y: int) -> T,) | String) -> int for T in int | f64",
        "(h: ((y: int) -> T,), k: (y: int) -> T) -> int for T in int | f64",
        "(h: ((y: T) -> int,)) -> T for T in int | f64",
        "(h: (y: int) -> T) -> int for T in int | f64",
        "(h: (y: T) -> T) -> int for T in int | f64",
        "(h: (y: int) -> T, y: int) -> int for T in int | f64",
        "(h: (y: T) -> int) -> T for T in int | f64",
        "(h: (y: int) -> T) -> T for T in int | f64",
        "(h: ((y: int) -> T,)) -> int for T in int | f64",
        "(h: (y: int) -> T, k: (y: int) -> T) -> int for T in int | f64",
        "(h: (y: int) ->? T) -> int for T in int | f64",
        "(h: (y: int) -> T) -> int for T in int | f64 | bool",
        "(h: (y: int) -> (T,)) -> int for T in int | f64",
    ];
    let mut wrong = Vec::new();
    for s in sigs {
        let src = format!("p(f: {s}) = 0;\nq(g: {}) = p(f: g);\n", s.replace('T', "U"));
        let errs = type_errors(&src);
        if !errs.is_empty() {
            wrong.push((src, errs));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
    let p = "(h: ((y: int) -> T,)) -> int for T in int | f64";
    let p2 = "(h: ((y: int) -> T, int)) -> int for T in int | f64";
    for (p, q, fits) in [
        // At `T = f64`, `p` takes a function giving `f64`, which `q` takes at no `U`.
        (p, "(h: ((y: int) -> U,)) -> int for U in int | bool", false),
        (p, "(h: ((y: int) -> U,)) -> int for U in int", false),
        (p, "(h: ((y: int) -> int,)) -> int", false),
        (
            p2,
            "(h: ((y: int) -> U, bool)) -> int for U in int | f64",
            false,
        ),
        (
            p2,
            "(h: ((y: int) -> U, int)) -> String for U in int | f64",
            false,
        ),
        // A domain is exact (DESIGN.md sec:type_language), so `g` must take at each instance of
        // `p`'s parameter no more than it: a function giving `int | f64` is taken by neither
        // instance, `T = int` nor `T = f64`, with the tuple or without it, and a wider
        // component is not taken either.
        (p, "(h: ((y: int) -> int | f64,)) -> int", false),
        (
            "(h: (y: int) -> T) -> int for T in int | f64",
            "(h: (y: int) -> int | f64) -> int",
            false,
        ),
        (
            p2,
            "(h: ((y: int) -> U, int | bool)) -> int for U in int | f64",
            false,
        ),
        // The same bound written in another order is the same type.
        (p, "(h: ((y: int) -> U,)) -> int for U in f64 | int", true),
        (
            p2,
            "(h: ((y: int) -> U, int)) -> int for U in f64 | int",
            true,
        ),
    ] {
        let src = format!("p(f: {p}) = 0;\nq(g: {q}) = p(f: g);\n");
        let errs = type_errors(&src);
        assert_eq!(errs.is_empty(), fits, "{src}{errs:#?}");
        if !fits {
            assert!(
                errs.iter().any(|e| e.contains("`p` does not take")),
                "{src}{errs:#?}"
            );
        }
    }
}

/// FAIL-print-two-variables-one-name: `g`'s parameter `{first} | ((V, V),) | ((V, V, V),)`
/// holds the same values as `f`'s `{first} | ((V, V) | (V, V, V),)`, so `p(f: g)` is right.
/// It was refused twice over: `((V'4, V'4),)` was not held as it is by
/// `((V'4, V'4) | (V'4, V'4, V'4),)` (fixed by the member lookup of `held_as_is`), and then
/// both members failed the shape `((int, bool) | (int, bool, bool),)`, which holds no variable,
/// in one bucket of the search, and the second was refused; such a shape is now left out
/// uncounted where a value of the member is outside it (`Searched::closed_left_out`).
#[test]
fn an_own_variable_of_an_outer_comparison_and_one_of_the_same_name_inside_print_apart() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    let first = "((int, bool) | (int, bool, bool),)";
    let src = format!(
        "p(f: (h: (x: {first} | ((V, V) | (V, V, V),)) -> int for V in int | f64) -> int) = 0;\n\
         q(g: (h: (x: {first} | ((V, V),) | ((V, V, V),)) -> int) -> int for V in int | f64) \
         = p(f: g);\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
}

/// A function type written as a morphism type (`Sig::morphism`), `K ->? V` or `L .. U -> V`,
/// prints in that form and reads back to the same type; an exact arrow that may answer
/// `#notFound` prints as an arrow, and a key that is a tuple keeps its parentheses.
#[test]
fn morphism_types_print_as_written_and_read_back() {
    for (written, printed) in [
        ("int ->? String", "int ->? String"),
        ("((int, int)) ->? int", "((int, int)) ->? int"),
        ("#a .. (#a | #b) -> int", "#a .. (#a | #b) -> int"),
        ("(int) -> int | #notFound", "int -> int | #notFound"),
    ] {
        let t = ty(written);
        assert_eq!(t.to_string(), printed, "{written}");
        assert_eq!(ty(printed), t, "{written}");
    }
}
