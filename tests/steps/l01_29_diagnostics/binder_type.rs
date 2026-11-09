//! A binder that names a type (DESIGN.md sec:diagnostics, row "Binder naming a type", and the
//! `match` row of the operator inventory in sec:syntax_tour): every binder but a type name in a
//! pattern is an error when it names a type in scope, so a cast habit such as `y as (int)` is
//! not read as a binding that shadows the type. A unit declares no type before L2, so at L1 the
//! types in scope are the prelude's. The error names the binder and the type, and offers the
//! repairs: rename the binder, and, for a type that casts, the type application `int(…)`.

use std::collections::BTreeSet;

use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;
use zedc::resolve::resolve;

use super::rejected;

/// The errors of resolving the unit `text`, each as its row's name or `-`, then its message's
/// text span: the binder for the row "Binder naming a type".
fn errors(text: &str) -> Vec<(String, String)> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP)
        .unwrap_or_else(|e| panic!("{text:?} does not parse: {e}"));
    let stmts = unit(text, &tokens, &tree).unwrap_or_else(|e| panic!("{text:?}: {e}"));
    resolve(&stmts).err().map_or_else(Vec::new, |es| {
        es.iter()
            .map(|e| {
                let row = e.row.map_or("-", Row::name);
                (row.into(), text[e.span.start..e.span.end].into())
            })
            .collect()
    })
}

/// Whether resolving `text` gives exactly one error, the row "Binder naming a type", whose
/// text is `binder`.
fn names_type(text: &str, binder: &str) {
    assert_eq!(
        errors(text),
        [("Binder naming a type".to_string(), binder.to_string())],
        "{text}"
    );
}

#[test]
fn a_lambda_parameter_named_for_the_cast_it_was_meant_to_be_is_rejected() {
    // The lambda was meant to turn its argument into a string, and names its parameter for it:
    // `String` would shadow the cast, and `+ 1` would add to the number.
    let out = rejected("label(positional n: int) = (String -> String + 1)(n);\n");
    assert_eq!(
        out,
        "1:29: the parameter `String` names the type `String`, which the prelude declares: a \
binder may not name a type in scope
  [1] 1:29: the parameter `String`, which binds `String` in this scope
      1 | label(positional n: int) = (String -> String + 1)(n);
        |                             ^^^^^^
  [2] 1:29: repair: rename the binder; where a cast was meant, write the type application \
`String(…)`"
    );
}

#[test]
fn a_statement_target_named_for_a_type_is_rejected_and_its_cast_is_not_reported_too() {
    // Before this row, `String = y + 1;` shadowed the cast, and the call `String(String)` was
    // reported as a call of an integer, naming neither the binder nor the row.
    let out =
        rejected("describe(positional y: int) {\n  String = y + 1;\n  return String(String);\n}\n");
    assert_eq!(
        out,
        "2:3: the binding target `String` names the type `String`, which the prelude declares: \
a binder may not name a type in scope
  [1] 2:3: the binding target `String`, which binds `String` in this scope
      2 |   String = y + 1;
        |   ^^^^^^^^^^^^^^^
  [2] 2:3: repair: rename the binder; where a cast was meant, write the type application \
`String(…)`
      2 |   String = y + 1;
        |   ^^^^^^"
    );
}

#[test]
fn a_positional_parameter_named_int_is_rejected() {
    names_type("next(positional int) = int + 1;\n", "int");
}

#[test]
fn a_named_parameter_named_f64_is_rejected_at_its_name() {
    names_type(
        "scale(positional x: f64, f64: f64 = 2.0) = x * f64;\n",
        "f64",
    );
}

#[test]
fn a_parameter_named_string_is_rejected_though_its_type_is_another() {
    names_type(
        "pick(positional String: int, positional s: String) = s;\n",
        "String",
    );
}

#[test]
fn a_parenthesized_lambda_parameter_is_rejected() {
    names_type("first = (positional x, positional rat) -> x;\n", "rat");
}

#[test]
fn a_bare_lambda_parameter_is_rejected() {
    names_type("succ = int -> int + 1;\n", "int");
}

#[test]
fn a_tuple_target_is_rejected_at_its_own_name() {
    names_type(
        "bounds(positional y: int) {\n  lo, int = (y, y + 1);\n  return lo;\n}\n",
        "int",
    );
}

#[test]
fn a_top_level_binding_named_bool_is_rejected() {
    names_type("bool = 1 < 2;\n", "bool");
}

#[test]
fn a_function_named_for_a_cast_is_rejected() {
    // A unit's own function would shadow the cast `int(…)` everywhere in the unit.
    names_type("int(positional s: String) = 0;\n", "int");
}

#[test]
fn an_output_port_named_for_its_type_is_rejected_with_the_one_repair() {
    let out = rejected("main() -> (Lines: Lines) {\n  Lines <- \"done\";\n}\n");
    assert_eq!(
        out,
        "1:12: the output port `Lines` names the type `Lines`, which the prelude declares: a \
binder may not name a type in scope
  [1] 1:12: the output port `Lines`, which binds `Lines` in this scope
      1 | main() -> (Lines: Lines) {
        |            ^^^^^^^^^^^^
  [2] 1:12: repair: rename the binder
      1 | main() -> (Lines: Lines) {
        |            ^^^^^"
    );
}

#[test]
fn a_field_an_else_pattern_binds_is_rejected() {
    names_type(
        "parsed(positional x) = x else #bad(String:) -> 0;\n",
        "#bad(String:)",
    );
}

#[test]
fn a_type_variable_named_for_a_type_is_rejected_once() {
    // The type `int` in `(x: int) -> int` names the prelude type, so the variable binds nothing
    // the type could hold; only the row is reported, not also that the type does not hold it.
    names_type(
        "twice(positional h: (x: int) -> int for int in int | f64) = h(x: h(x: 1));\n",
        "int",
    );
}

#[test]
fn each_binder_that_names_a_type_is_reported() {
    assert_eq!(
        errors("f(positional int) {\n  String = int;\n  g = f64 -> f64;\n  return String;\n}\n"),
        [
            ("Binder naming a type".to_string(), "int".to_string()),
            ("Binder naming a type".to_string(), "String".to_string()),
            ("Binder naming a type".to_string(), "f64".to_string()),
        ]
    );
}

#[test]
fn binders_that_name_no_type_are_accepted() {
    // Prelude words that are not types may be shadowed (DESIGN.md "Defined words by layer"),
    // a name differs from a type in case, and a type in type position or as a cast is a use.
    for text in [
        "f(positional y: int) {\n  abs = y + 1;\n  return abs;\n}\n",
        "len(positional s: String) = 0;\n",
        "f(positional string: String) = string;\n",
        "f(positional Int: int) = Int;\n",
        "f(positional y: int) = (s -> String(s))(y);\n",
        "f(positional x) = x else #bad(msg:) -> 0;\n",
        "main() -> (stdout: Lines) {\n  stdout <- \"done\";\n}\n",
        "twice(positional h: (x: T) -> T for T in int | f64) = h(x: h(x: 1));\n",
    ] {
        assert_eq!(errors(text), [], "{text}");
    }
}

/// What a rule of the grammar's `Name` occurrences are: a binder of layer L1, with a program
/// whose binder of that rule names a type and the binder's text; a binder of a later layer, whose
/// form layer L1 refuses whole, with such a program; or no binder, with the reason.
enum Site {
    L1(&'static str, &'static str),
    Later(&'static str),
    NotBinder(&'static str),
}

/// Every rule of `zed/grammar/syntax.peg` that writes `Name`, and what it binds.
const SITES: &[(&str, Site)] = &[
    ("Name", Site::NotBinder("the identifier itself")),
    ("Import", Site::Later("import geometry.shapes as int;\n")),
    ("Path", Site::NotBinder("a unit's or a type's name, a use")),
    ("Struct", Site::NotBinder("declares a type")),
    (
        "StructField",
        Site::NotBinder("a field, which no scope binds"),
    ),
    ("Field", Site::NotBinder("a field, which no scope binds")),
    ("TypeDecl", Site::NotBinder("declares a type")),
    ("TypeParams", Site::Later("type Pair(int) = (int, int);\n")),
    ("Interface", Site::NotBinder("declares a type")),
    (
        "Member",
        Site::Later("interface Show { law String() = true }\n"),
    ),
    ("Law", Site::Later("law String(x: int) = x == x;\n")),
    (
        "Function",
        Site::L1("int(positional s: String) = 0;\n", "int"),
    ),
    ("Method", Site::Later("Point.int() = 0;\n")),
    (
        "PositionalParam",
        Site::L1("next(positional int) = int + 1;\n", "int"),
    ),
    (
        "Param",
        Site::L1("scale(x: f64, f64: f64 = 2.0) = x * f64;\n", "f64"),
    ),
    (
        "Port",
        Site::L1(
            "main() -> (Lines: Lines) {\n  Lines <- \"done\";\n}\n",
            "Lines",
        ),
    ),
    ("IndexedDef", Site::Later("int[i in s] = i;\n")),
    ("IndexKey", Site::Later("f[int in s] = 1;\n")),
    (
        "AckPush",
        Site::Later("main() -> (out: Lines) {\n  int = out <- \"x\";\n}\n"),
    ),
    ("KeyedPush", Site::NotBinder("a port's name, a use")),
    ("WholePush", Site::NotBinder("a port's name, a use")),
    ("TypedBinding", Site::Later("int: int = 1;\n")),
    (
        "Target",
        Site::L1(
            "f(positional y: int) {\n  lo, int = (y, y + 1);\n  return lo;\n}\n",
            "int",
        ),
    ),
    (
        "BoundaryItem",
        Site::NotBinder("the family a boundary value is given to, a use"),
    ),
    ("Signature", Site::Later("int: int;\n")),
    ("Lambda", Site::L1("succ = int -> int + 1;\n", "int")),
    (
        "MemberSuffix",
        Site::NotBinder("a field or a uniform call, a use"),
    ),
    (
        "SafeSuffix",
        Site::NotBinder("a field or a uniform call, a use"),
    ),
    (
        "SpreadSuffix",
        Site::NotBinder("a field or a uniform call, a use"),
    ),
    ("ReadSuffix", Site::NotBinder("a metadata read, a use")),
    ("Update", Site::NotBinder("a field path, a use")),
    ("KeyPath", Site::NotBinder("a key path, a use")),
    ("FacetCall", Site::NotBinder("a facet word, a use")),
    (
        "NamedArg",
        Site::NotBinder("the parameter an argument is passed to"),
    ),
    (
        "PlainArg",
        Site::NotBinder("the parameter an argument is passed to"),
    ),
    ("Primary", Site::NotBinder("a name read, a use")),
    ("Display", Site::NotBinder("a record's field, a key")),
    ("Loop", Site::Later("g = loop int { x' = x + 1; };\n")),
    (
        "IsPat",
        Site::Later("f(positional v) = match v { int is int -> 1, _ -> 0 };\n"),
    ),
    (
        "CtorPat",
        Site::Later("f(positional v) = match v { Point(x: int) -> 1, _ -> 0 };\n"),
    ),
    (
        "NamePat",
        Site::NotBinder("a type name in a pattern is a type test"),
    ),
    (
        "FieldPat",
        Site::L1(
            "parsed(positional x) = x else #bad(String:) -> 0;\n",
            "#bad(String:)",
        ),
    ),
    (
        "Binder",
        Site::Later("f(positional s) = for int in s { int };\n"),
    ),
    (
        "TypeBounds",
        Site::L1(
            "apply(positional h: (x: int) -> int for int in int) = h(x: 1);\n",
            "int",
        ),
    ),
    (
        "ArrowParams",
        Site::NotBinder("the name a call passes an argument of a function type by"),
    ),
    (
        "TypeParam",
        Site::NotBinder("the name a call passes an argument of a function type by"),
    ),
    (
        "Refinement",
        Site::Later("f(positional x: int[int < 3]) = x;\n"),
    ),
    (
        "FieldType",
        Site::NotBinder("a field, which no scope binds"),
    ),
    (
        "RecordType",
        Site::NotBinder("a field, which no scope binds"),
    ),
    (
        "ShapeDim",
        Site::Later("f(positional x: [f64; int: 3]) = x;\n"),
    ),
    (
        "GItem",
        Site::NotBinder("a grammar field, which no scope binds"),
    ),
    ("GPrimary", Site::NotBinder("a grammar rule's name, a use")),
];

/// The rules of the grammar `peg` whose alternatives write the nonterminal `Name`.
fn rules_writing_name(peg: &str) -> BTreeSet<&str> {
    let mut rule = "";
    let mut out = BTreeSet::new();
    for line in peg.lines() {
        if line.starts_with(|c: char| c.is_ascii_alphabetic()) {
            rule = line.split_whitespace().next().unwrap_or_default();
        }
        // `Name` as a whole word, outside the quoted terminals.
        let unquoted: String = line.split('\'').step_by(2).collect::<Vec<_>>().join(" ");
        let words = unquoted.split(|c: char| !c.is_ascii_alphanumeric() && c != '_');
        if words.into_iter().any(|w| w == "Name") {
            out.insert(rule);
        }
    }
    out
}

#[test]
fn every_rule_of_the_grammar_that_writes_a_name_is_classified_and_its_binders_rejected() {
    let peg = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../zed/grammar/syntax.peg"),
    )
    .unwrap();
    let rules = rules_writing_name(&peg);
    let listed: BTreeSet<&str> = SITES.iter().map(|&(r, _)| r).collect();
    assert_eq!(listed.len(), SITES.len(), "a rule listed twice");
    assert_eq!(
        rules, listed,
        "each rule that writes `Name` is listed once, with what it binds"
    );
    for (rule, site) in SITES {
        match site {
            Site::L1(text, binder) => names_type(text, binder),
            // Layer L1 refuses the form whole, as one this zedc does not compile yet; the row
            // lands with the layer that compiles it (DESIGN.md step L1.29).
            Site::Later(text) => {
                let out = rejected(text);
                assert!(zed_tests::is_not_yet(&out), "{rule}: {out}");
            }
            Site::NotBinder(why) => assert!(!why.is_empty()),
        }
    }
}

/// `n` functions, each with a parameter, a statement target and a lambda parameter that name a
/// type: `3n` binders the row rejects.
fn typed_binders(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "label{i}(positional int) {{\n  String = int + {i};\n  return (f64 -> f64)(String);\n}}\n"
            )
        })
        .collect()
}

#[test]
fn rejecting_many_binders_that_name_types_scales() {
    // The statements of both sizes are built before timing, so only resolution is measured.
    let n = 2000;
    let built: std::collections::HashMap<usize, Vec<zedc::ast::Stmt>> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let text = typed_binders(k);
            let tokens = lex_fence(&text).unwrap();
            let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
            (k, unit(&text, &tokens, &tree).unwrap())
        })
        .collect();
    zed_tests::scaling::check_order("3n binders that name a type", n, 1, |k| {
        let errors = resolve(&built[&k]).err().unwrap();
        assert_eq!(errors.len(), 3 * k);
        assert!(errors.iter().all(|e| e.row == Some(Row::BinderNamingType)));
    });
}
