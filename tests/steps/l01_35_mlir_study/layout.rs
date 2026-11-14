//! Item LAYOUT-measure: the bytes per syntax-tree node, kernel term, ZIR node and native value,
//! measured on the step units and recorded in `zed/compiler/MLIR.md`, section Layout. The
//! record's inline sizes are the compiler's own, so a type that grows shows in it.

use std::mem::size_of;

use zed_kernel::{Term, Value};
use zed_rt::Word;
use zed_rt::heap::CELL_BYTES;
use zed_tests::layout::{Native, Record, ast_stage, record};
use zed_tests::oracle::step_units;
use zedc::ast::{Expr, ExprKind, Pattern, Stmt, Type};
use zedc::zir::{Edge, Node, Op, Region, Src};

use super::record as mlir;

/// The inline size of each type the record names, in the order of its table.
fn sizes() -> Vec<(&'static str, usize)> {
    vec![
        ("ast::Expr", size_of::<Expr>()),
        ("ast::ExprKind", size_of::<ExprKind>()),
        ("ast::Stmt", size_of::<Stmt>()),
        ("ast::Type", size_of::<Type>()),
        ("ast::Pattern", size_of::<Pattern>()),
        ("kernel Term", size_of::<Term>()),
        ("kernel Value", size_of::<Value>()),
        ("zir::Node", size_of::<Node>()),
        ("zir::Op", size_of::<Op>()),
        ("zir::Src", size_of::<Src>()),
        ("zir::Edge", size_of::<Edge>()),
        ("zir::Region", size_of::<Region>()),
        ("native Word", size_of::<Word>()),
        ("native heap cell", CELL_BYTES),
    ]
}

/// The rows `| `name` | bytes |` of the table under `## Layout`.
fn recorded() -> Vec<(String, usize)> {
    let text = mlir();
    let start = text.find("\n## Layout\n").expect("no section `Layout`");
    let body = &text[start + 11..];
    let body = &body[..body.find("\n## ").unwrap_or(body.len())];
    body.lines()
        .filter(|l| l.starts_with("| `"))
        .filter_map(|l| {
            let mut cells = l.split('|').map(str::trim).skip(1);
            let name = cells.next()?.trim_matches('`').to_string();
            let bytes = cells.next()?.parse().ok()?;
            Some((name, bytes))
        })
        .collect()
}

/// The sum of the records of the step units, and how many units the front end refused.
fn step_record() -> (Record, usize) {
    let (mut all, mut refused) = (Record::default(), 0);
    for path in step_units() {
        let text = std::fs::read_to_string(&path).unwrap();
        match record(&text) {
            Ok(r) => all.add(&r),
            Err(e) => {
                println!("refused {}: {e}", path.display());
                refused += 1;
            }
        }
    }
    (all, refused)
}

#[test]
fn the_record_names_each_inline_size_as_the_compiler_has_it() {
    let want: Vec<(String, usize)> = sizes().into_iter().map(|(n, b)| (n.into(), b)).collect();
    assert_eq!(recorded(), want, "zed/compiler/MLIR.md, section Layout");
}

#[test]
fn the_step_units_are_measured_and_each_node_takes_at_least_its_inline_size() {
    let (r, refused) = step_record();
    println!("{r:#?}\nrefused: {refused}");
    for (stage, s) in [("ast", r.ast), ("term", r.term), ("zir", r.zir)] {
        println!(
            "{stage}: {} nodes, {} bytes, {:?} per node",
            s.nodes,
            s.bytes,
            s.per_node()
        );
    }
    // The three units whose lines are marked as refused are refused; every other unit is measured.
    assert_eq!((r.units, refused), (step_units().len() - 3, 3));
    assert!(r.ast.bytes >= (r.ast.nodes * size_of::<Expr>().min(size_of::<Stmt>())) as u64);
    assert!(r.term.bytes >= (r.term.nodes * size_of::<Term>()) as u64);
    assert!(r.zir.bytes >= (r.zir.nodes * size_of::<Node>()) as u64);
    assert!(r.native.runs > 0 && r.native.cells > 0);
}

/// A struct declaration of `fields` typed fields; structs are compiled from step L2.4, so only
/// its syntax tree is built at this step.
fn struct_unit(fields: usize) -> String {
    let decl: Vec<String> = (0..fields).map(|i| format!("f{i}: int")).collect();
    format!("struct S {{ {} }}\n", decl.join(", "))
}

#[test]
fn an_empty_struct_and_a_six_field_struct_are_measured() {
    let empty = ast_stage(&struct_unit(0)).unwrap();
    let six = ast_stage(&struct_unit(6)).unwrap();
    println!("struct of 0 fields: {empty:?}; of 6: {six:?}");
    // One statement each, the fields being part of it; six fields take at least six names
    // and six types more.
    assert_eq!((empty.nodes, six.nodes), (1, 1));
    assert!(six.bytes >= empty.bytes + 6 * size_of::<Type>() as u64);
}

#[test]
fn an_empty_node_and_a_six_field_node_are_measured() {
    let leaf = record("leaf(positional x: int) = #leaf\ntest { 1 -> #leaf }\n").unwrap();
    let node = record(
        "node(positional x: int) = #node(x, x + 1, x + 2, x + 3, x + 4, x + 5)\n\
         test { 1 -> #node(1, 2, 3, 4, 5, 6) }\n",
    )
    .unwrap();
    println!("empty node: {leaf:?}\nsix-field node: {node:?}");
    // Each row allocates one cell for the closure of the function it applies. An atom with no
    // payload is a word and takes no cell; a six-field one takes a cell, for the result and for
    // the expected value.
    assert_eq!(
        leaf.native,
        Native {
            runs: 1,
            cells: 1,
            peak: 1
        }
    );
    assert_eq!(
        node.native,
        Native {
            runs: 1,
            cells: 3,
            peak: 2
        }
    );
    assert!(node.zir.nodes > leaf.zir.nodes && node.term.nodes > leaf.term.nodes);
}

#[test]
fn the_value_a_tables_clause_gives_is_a_node_of_a_function_and_of_a_method() {
    let nodes = |text: &str| ast_stage(text).unwrap().nodes;
    for head in ["f(positional x: int) = x", "T.m(positional x: int) = x"] {
        let plain = nodes(&format!("{head}\ntest {{ 1 -> 1 }}\n"));
        let given = nodes(&format!(
            "{head}\ntest with main::files = \"1\" {{ 1 -> 1 }}\n"
        ));
        // The clause adds one expression, the string it gives the port.
        assert_eq!(given, plain + 1, "{head}");
    }
}

/// A unit of `n` definitions, each with a table of one row.
pub(super) fn many(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "step{i}(positional x: int) = x * 2 + {i}\ntest {{ 1 -> {} }}\n",
                2 + i
            )
        })
        .collect()
}

/// The layout record of a unit of a few definitions is made, one native run per definition; the
/// time and the peak bytes are held linear in the definitions in `bench/layout.rs`.
#[test]
fn the_record_of_a_unit_of_a_few_definitions_is_made() {
    for n in [1, 2, 9] {
        let r = record(&many(n)).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(r.native.runs, n as u64);
    }
}

/// The syntax-tree count of each kind of expression and statement: a statement is one node,
/// each expression in it one more, and an expression inside a pattern or a type is part of that
/// pattern or type. Each count below is worked out by hand from that rule; the unit is only
/// parsed, so forms this step does not compile yet are counted too.
#[test]
fn each_kind_of_expression_and_statement_is_counted_once() {
    let cases: [(&str, &str, usize); 41] = [
        ("a range below", "x = 1..<3;\n", 4),
        ("a range through", "x = 1..=3;\n", 4),
        ("an open range", "x = 1..;\n", 3),
        (
            "a for: source, block, its return",
            "x = for d in xs { d };\n",
            6,
        ),
        (
            "a for with a guard",
            "x = for d in xs where d > 0 { d };\n",
            9,
        ),
        (
            "a match: patterns not counted",
            "x = match y { 1 -> 2, _ -> 3 };\n",
            5,
        ),
        (
            "a match arm with a guard",
            "x = match y { a where a > 0 -> 2, _ -> 3 };\n",
            8,
        ),
        ("a record, `y:` one name", "x = {a: 1, y:};\n", 4),
        ("an update", "x = p with { x = 3 };\n", 4),
        ("a map display", "x = {1 -> 2, 3 -> 4};\n", 6),
        ("the empty map", "x = {};\n", 2),
        ("a set display", "x = {1, 2};\n", 4),
        ("an array, an index, else", "x = [1, 2][0] else 3;\n", 8),
        ("a tuple", "x = (1, 2);\n", 4),
        ("a membership", "x = 1 in xs;\n", 4),
        ("a reduction of a section", "x = xs >< (+);\n", 4),
        ("a metadata read", "x = xs::len;\n", 3),
        ("a member", "x = m.stdin;\n", 3),
        ("a writing call `*.`", "x = c*.m(1);\n", 5),
        ("sort keys", "x = xs.sortBy(asc k, desc j);\n", 8),
        (
            "a call with a lambda argument",
            "x = xs.reduce((a, b) -> a + b);\n",
            8,
        ),
        ("a lambda called", "x = (y -> y)(1);\n", 5),
        ("a unary operator", "x = !y;\n", 3),
        ("`is`: the type not counted", "x = y is int;\n", 3),
        ("a string with a hole", "x = \"a${b}c\";\n", 3),
        ("`this`", "x = this;\n", 2),
        (
            "a loop: block, statements, until",
            "x = loop { n = 1; n' = n + 1; until n' == 1; };\n",
            13,
        ),
        (
            "a loop with while and a local",
            "x = loop { n = 1; while n < 3; local t' = n; };\n",
            11,
        ),
        (
            "a loop with initial",
            "x = loop { initial n = 0; n' = n + 1; until n' == 3; };\n",
            13,
        ),
        (
            "a named loop, break in an if",
            "x = loop t { initial x = 0; x' = x + 1; _ = if x > 2 { break x } else { 0 }; };\n",
            21,
        ),
        (
            "an indexed definition: key set and value",
            "x[i in 0..<3] = i;\n",
            5,
        ),
        (
            "a bare annotation",
            "@inline\nf(positional x: int) = x;\n",
            2,
        ),
        (
            "an annotation with arguments",
            "@pure(1, a: 2)\nf(positional x: int) = x;\n",
            4,
        ),
        ("an annotation of the unit", "@log(#off);\nx = 1;\n", 4),
        ("a local function", "local sq(positional v) = v * v;\n", 4),
        ("a parameter default", "f(positional x: int = 3) = x;\n", 3),
        (
            "a method using `this`",
            "T.m(positional x: int) = this.f + x;\n",
            5,
        ),
        (
            "a struct field default",
            "struct S { a: int = 1, b: int }\n",
            2,
        ),
        (
            "a block body: a push and a return of two",
            "f(positional x: int) {\n  out <- x;\n  return x, 1;\n}\n",
            7,
        ),
        (
            "a table row",
            "f(positional x: int) = x\ntest { 1 -> 1 }\n",
            4,
        ),
        ("two statements", "x = 1;\ny = x;\n", 4),
    ];
    for (case, text, want) in cases {
        let got = ast_stage(text).unwrap_or_else(|e| panic!("{case}: {e}"));
        assert_eq!(got.nodes, want, "{case}: {text:?}");
    }
}
