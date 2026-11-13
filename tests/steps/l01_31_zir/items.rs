//! Types, values, patterns and edges, each read back from the text the kernel prints.

use zed_kernel::Value;
use zed_kernel::term::Pattern;
use zed_kernel::types::Type;
use zedc::zir::text::{edge, parse, parse_edge, parse_pattern, parse_type, parse_value, pattern};

#[test]
fn types_read_back() {
    for t in [
        "_",
        "(|)",
        "bool",
        "true",
        "int",
        "rat",
        "f32",
        "f64",
        "String",
        "#_",
        "(| int f32)",
        "tuple",
        "struct",
        "morphism",
        "3",
        "\"GET\"",
        "#none",
        "(#some (tuple int))",
        "(#some _)",
        "(| #none (#some (tuple int)))",
        "(| int String)",
        "(\\ int 0)",
        "(tuple int String)",
        "(-> int bool)",
        "(->? String int)",
        "(| (-> String String) (-> int int))",
    ] {
        let ty = parse_type(t).unwrap_or_else(|e| panic!("{t}: {e}"));
        assert_eq!(ty.to_string(), t);
    }
}

#[test]
fn values_read_back() {
    for v in [
        "true",
        "-42",
        "123456789012345678901234567890",
        "3r",
        "-3r/4r",
        "1.5",
        "-0.0",
        "inf",
        "-inf",
        "nan",
        "1.5e30",
        "0.1f32",
        "-0.0f32",
        "1.0e-45f32",
        "3.4028235e38f32",
        "inff32",
        "-inff32",
        "nanf32",
        "\"tab\\there \\\"quoted\\\" 😀\"",
        "#empty",
        "#pair(1, \"b\")",
        "#err(code: 3, why: \"x\")",
        "()",
        "(1,)",
        "((1,),)",
        "(#e(1),)",
        "(1, (2,))",
        "(1, (2, 3))",
        "[\"eu\" -> 2024 -> 3]",
        "{}",
        "{1 -> \"a\", 2 -> \"b\"}",
        "{\"x\", \"y\"}",
        "{1 -> {2 -> 3}}",
    ] {
        let val = parse_value(v).unwrap_or_else(|e| panic!("{v}: {e}"));
        assert_eq!(val.to_string(), v);
    }
}

#[test]
fn a_one_tuple_is_written_with_a_comma() {
    // A one-tuple is written `(x,)`, as its type `(T,)` is: in a program `(x)` is `x`.
    let one = |v| Value::tuple(vec![v]);
    let nested = one(one(Value::Int(0)));
    assert_eq!(one(Value::Int(0)).to_string(), "(0,)");
    assert_eq!(nested.to_string(), "((0,),)");
    assert_eq!(parse_value(&nested.to_string()), Ok(nested.clone()));
    assert_ne!(parse_value("((0,),)"), Ok(one(Value::Int(0))));
    // The reader takes a tuple's last `,` or not, as it does a pattern's.
    assert_eq!(parse_value("((0),)"), Ok(nested));
    assert_eq!(
        parse_value("(1, 2,)"),
        Ok(Value::tuple(vec![Value::Int(1), Value::Int(2)]))
    );
    assert_eq!(
        parse_value("(1,,)"),
        Err("column 4: expected a value, found `,)`".into())
    );
}

#[test]
fn string_escapes() {
    // The kernel prints a printable character as itself; the reader takes Rust's escapes too.
    assert_eq!(
        parse_value("\"\\u{1f600}\\n\\0\""),
        Ok(Value::str("😀\n\0"))
    );
    assert_eq!(
        parse_value("\"a\\qb\""),
        Err("column 2: `\\q` is not an escape".into())
    );
}

#[test]
fn named_payload_fields_sort() {
    // A struct payload's fields are sorted, whatever order the text gives them in.
    assert_eq!(
        parse_value("#err(why: \"x\", code: 3)"),
        parse_value("#err(code: 3, why: \"x\")")
    );
    assert_eq!(
        parse_value("#err(code: 3, code: 4)"),
        Err("column 23: atom `#err` names a field twice".into())
    );
}

#[test]
fn names_the_lexer_accepts_read_back() {
    // A name is what the lexer takes (lex/name.rs): ASCII name characters and one trailing
    // prime.
    let one = Value::str("1");
    for v in [
        Value::atom("ok'"),
        Value::atom("x_1"),
        Value::atom_with("_x1", vec![one.clone()]),
        Value::atom_named("point", vec![("x'".into(), one.clone()), ("x".into(), one)])
            .expect("distinct fields"),
    ] {
        let text = v.to_string();
        assert_eq!(parse_value(&text), Ok(v), "{text}");
    }
    for p in [
        Pattern::Bind("x'".into()),
        Pattern::Bind("x_1".into()),
        Pattern::Atom("ok'".into(), vec![Pattern::Bind("x'".into())]),
        Pattern::Fields(
            "point".into(),
            vec![("x'".into(), Pattern::Bind("y'".into()))],
        ),
        // `is'` is a binder, not the start of `(is T)`.
        Pattern::Tuple(vec![Pattern::Bind("is'".into()), Pattern::Wild]),
    ] {
        let text = pattern(&p);
        assert_eq!(parse_pattern(&text), Ok(p), "{text}");
    }
    for (name, t) in [
        ("ok'", Type::atom("ok'")),
        ("x_1", Type::atom("x_1")),
        (
            "_x1",
            Type::atom_with("_x1", &Type::tuple(vec![Type::int()])),
        ),
    ] {
        let text = t.to_string();
        assert!(text.contains(name), "{text} names {name}");
        assert_eq!(parse_type(&text), Ok(t), "{text}");
    }
}

#[test]
fn an_atom_type_form_with_a_head_that_is_no_name_is_rejected() {
    // The head of `(#name t)` is read up to a space or a bracket, so it is checked as a name
    // the lexer accepts, like the bare atom type `#name`.
    assert_eq!(
        parse_type("(#foo-bar (tuple))"),
        Err("column 19: `(#foo-bar …)`: `foo-bar` is not a name".into())
    );
    assert_eq!(
        parse_type("(#ok'' (tuple))"),
        Err("column 16: `(#ok'' …)`: `ok''` is not a name".into())
    );
}

/// Each form that reads a name, written with `{}` where the name goes, and the reader that
/// reads it; the error of a graph line names its line, here line 3.
const NAME_FORMS: &[(&str, &str)] = &[
    ("value", "#{}"),
    ("value", "#{}(1)"),
    ("value", "#p({}: 1)"),
    ("value", "#p(_0: 1, {}: 2)"),
    ("pattern", "{}"),
    ("pattern", "#{}"),
    ("pattern", "#{}(a)"),
    ("pattern", "#p({}: a)"),
    ("pattern", "#p(_0: b, {}: c)"),
    ("type", "#{}"),
    ("edge", "state {}"),
    ("edge", "String facet {} \"m\""),
    ("graph", "r.0 port read {} (r^0) -> (String; state out)"),
    ("graph", "r.0 port push {} (r^0, 1) -> (_; state out)"),
    ("graph", "r.0 fold 1 {{}: proved} (r^0, r^1) -> (int)"),
];

/// `form` with `name` in it, read by its reader; the text of what was read, or the error.
fn read_name_form(reader: &str, form: &str, name: &str) -> Result<String, String> {
    let text = form.replacen("{}", name, 1);
    match reader {
        "value" => parse_value(&text).map(|v| v.to_string()),
        "pattern" => parse_pattern(&text).map(|p| pattern(&p)),
        "type" => parse_type(&text).map(|t| t.to_string()),
        "edge" => parse_edge(&text).map(|e| edge(&e)),
        _ => parse(&format!(
            "zir 1\nr region port (state out)\n{text}\nr results ()\n"
        ))
        .map(|_| text),
    }
}

#[test]
fn a_name_starts_as_the_lexer_starts_one() {
    // lex/name.rs: a name starts with an ASCII letter, or with `_` before a name character;
    // a name is ASCII (NAME-ascii-only), so `élan` and `面積` are no names.
    for (reader, form) in NAME_FORMS {
        for name in ["elan", "x1", "_1"] {
            let want = form.replacen("{}", name, 1);
            assert_eq!(
                read_name_form(reader, form, name),
                Ok(want),
                "{form} {name}"
            );
        }
        let column = form.find("{}").expect("a place for the name") + 1;
        for bad in ["1x", "\u{e9}lan", "\u{9762}\u{7a4d}"] {
            let why = format!("`{bad}` is not a name: a name starts with an ASCII letter or `_`");
            let want = match *reader {
                "graph" => format!("line 3: column {column}: {why}"),
                _ => format!("column {column}: {why}"),
            };
            assert_eq!(read_name_form(reader, form, bad), Err(want), "{form} {bad}");
        }
    }
    // The head of a type form is read up to a space or a bracket, and checked when it ends.
    assert_eq!(
        parse_type("(#1x (tuple int))"),
        Err("column 18: `(#1x …)`: `1x` is not a name".into())
    );
    assert_eq!(
        parse_type("(#Area (tuple int))").map(|t| t.to_string()),
        Ok("(#Area (tuple int))".into())
    );
    // The column counts bytes: each of the two Han characters is three.
    assert_eq!(
        parse_type("(#\u{9762}\u{7a4d} (tuple int))"),
        Err("column 22: `(#\u{9762}\u{7a4d} …)`: `\u{9762}\u{7a4d}` is not a name".into())
    );
    // A bare `_` is the wildcard: a binder pattern, never the name of an atom or a field.
    assert_eq!(parse_pattern("_"), Ok(Pattern::Wild));
    let why = "`_` is not a name: a name that starts with `_` has an ASCII letter, a digit or `_` \
               next";
    assert_eq!(parse_value("#_"), Err(format!("column 2: {why}")));
    assert_eq!(parse_pattern("#p(_: a)"), Err(format!("column 4: {why}")));
    assert_eq!(
        parse_pattern("(a, _')"),
        Err("column 5: `_'` is not a name: a name that starts with `_` has an ASCII letter, a digit or `_` next".into())
    );
}

#[test]
fn floats_keep_their_bits() {
    let v = parse_value("-0.0").expect("a float");
    assert_eq!(v, Value::float(-0.0));
    assert_ne!(v, Value::float(0.0));
}

#[test]
fn patterns_read_back() {
    for p in [
        "_",
        "n",
        "#_",
        "#none",
        "#some(n)",
        "#err(code: c, why: _)",
        "(a, b)",
        "(a,)",
        "()",
        "=3",
        "=\"GET\"",
        "=#none",
        "=(1, 2)",
        "(is (| int String))",
        "#some((a, #pair(=1, b)))",
    ] {
        let pat = parse_pattern(p).unwrap_or_else(|e| panic!("{p}: {e}"));
        assert_eq!(pattern(&pat), p);
    }
    // A literal atom is not an atom pattern: `=#none` matches the value, `#none` the shape.
    assert_ne!(parse_pattern("=#none"), parse_pattern("#none"));
    assert!(matches!(parse_pattern("#none"), Ok(Pattern::Atom(..))));
}

#[test]
fn generated_binders_read_back() {
    use zedc::canon::binders::level_name;
    // The elaborator's binders `$1`, `$2` (a wave's values in a port graph) and the canonical
    // binders at levels 0 and 12 print with `$`, which no written name contains, and read back.
    let bind = |x: &str| Pattern::Bind(x.into());
    let level = |k| Pattern::Bind(level_name(k));
    for (p, text) in [
        (bind("$1"), "$1"),
        (
            Pattern::Tuple(vec![bind("$1"), bind("$2"), bind("n")]),
            "($1, $2, n)",
        ),
        (level(0), "$$0"),
        (Pattern::Atom("some".into(), vec![level(12)]), "#some($$12)"),
        (
            Pattern::Fields("err".into(), vec![("code".into(), level(1))]),
            "#err(code: $$1)",
        ),
    ] {
        assert_eq!(pattern(&p), text);
        assert_eq!(parse_pattern(text), Ok(p), "{text}");
    }
    // A graph the canonicalizer renamed prints and reads back whole, its binders at their levels.
    let g = parse(
        "zir 1\nr region function (tuple)\nr.0 match [(lo, hi)] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0.0 prim + (r.0/0^0, r.0/0^1) -> (int)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n",
    )
    .expect("a graph");
    let c = zedc::zir::canon::canonicalize(&g);
    let printed = zedc::zir::text::print(&c);
    assert!(printed.contains("match [($$0, $$1)]"), "{printed}");
    assert_eq!(parse(&printed), Ok(c));
    // Each binder has one spelling, and a `$` that starts no binder is refused at the `$`.
    for (text, why) in [
        (
            "$",
            "`$` is not a binder: a binder written with `$` has a number after the `$`",
        ),
        (
            "($$, a)",
            "`$$` is not a binder: a binder written with `$` has a number after the `$`",
        ),
        (
            "$01",
            "`$01` is not a binder: a binder written with `$` has a number with no leading zero",
        ),
        (
            "$$007",
            "`$$007` is not a binder: a binder written with `$` has a number with no leading zero",
        ),
        (
            "(a, $1x)",
            "`$1x` is not a binder: a binder written with `$` ends with its number",
        ),
        (
            "$$99999999999999999999999",
            "`$$99999999999999999999999` is not a binder: its level is too large",
        ),
    ] {
        let col = text.find('$').expect("a `$`") + 1;
        assert_eq!(
            parse_pattern(text),
            Err(format!("column {col}: {why}")),
            "{text}"
        );
    }
}

#[test]
fn the_text_and_binary_forms_read_the_same_generated_binders() {
    use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src, binary, text};
    // A match on `0` with one arm, whose pattern binds the one name `x`.
    let matching = |x: &str| Region {
        kind: RegionKind::Function,
        args: Vec::new(),
        nodes: vec![Node {
            op: Op::Match(vec![Pattern::Bind(x.into())]),
            inputs: vec![Src::Const(Value::Int(0))],
            outputs: vec![Edge::value(zed_kernel::types::Type::int())],
            regions: vec![
                Region {
                    kind: RegionKind::Match,
                    args: vec![Edge::value(zed_kernel::types::Type::int())],
                    nodes: Vec::new(),
                    results: vec![Src::Arg(0)],
                }
                .into(),
            ],
        }],
        results: vec![Src::Out(0, 0)],
    };
    let huge = "99999999999999999999999";
    for (x, made) in [
        ("$1", true),
        ("$10", true),
        ("\u{0}0", true),
        ("\u{0}12", true),
        ("$", false),
        ("$01", false),
        ("\u{0}", false),
        ("\u{0}01", false),
        ("\u{0}+1", false),
        (&format!("${huge}"), true),
        (&format!("\u{0}{huge}"), false),
    ] {
        let g = matching(x);
        let from_text = text::parse(&text::print(&g));
        let from_binary = binary::decode(&binary::encode(&g).expect("memory for the bytes"));
        assert_eq!(from_text.as_ref().ok(), made.then_some(&g), "text, {x:?}");
        assert_eq!(
            from_binary.as_ref().ok(),
            made.then_some(&g),
            "binary, {x:?}"
        );
    }
}

#[test]
fn edges_read_back() {
    for e in [
        "state out",
        "state m.stdout",
        "int",
        "int in [0..=9]",
        "int in [..=-1, 1..]",
        "int class 1 mod 3",
        "int class 5",
        "int set {1, 5, 9}",
        "int in [0..] class 0 mod 2 set {0, 2}",
        "rat facet units \"m/s\"",
        "String hint name \"title\" facet locale \"en\"",
    ] {
        let ed = parse_edge(e).unwrap_or_else(|err| panic!("{e}: {err}"));
        assert_eq!(edge(&ed), e);
    }
}

#[test]
fn a_port_named_by_a_field_of_main_args_reads_back() {
    // `main(m: MainArgs)` pushes to `m.stdout`: the name of the port is the push target,
    // names joined by `.`, in a state edge and in a port operation alike.
    let text = "zir 1\nr region port (state m.stdout)\n\
                r.0 port read m.stdin (r^0) -> (String; state m.stdin)\n\
                r.1 port push m.stdout (r^0, 1) -> (_; state m.stdout)\nr results ()\n";
    let g = parse(text).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(parse(&zedc::zir::text::print(&g)), Ok(g));
    for (bad, why) in [
        (
            "state m.",
            "column 9: expected a name, found the end of the line",
        ),
        (
            "state m. stdout",
            "column 9: expected a name right after `.`, found a space",
        ),
        (
            "state m.1x",
            "column 9: `1x` is not a name: a name starts with an ASCII letter or `_`",
        ),
    ] {
        assert_eq!(
            parse_edge(bad).map(|e| edge(&e)),
            Err(why.to_string()),
            "{bad}"
        );
    }
}
