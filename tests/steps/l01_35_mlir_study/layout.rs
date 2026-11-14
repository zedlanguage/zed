//! Item LAYOUT-measure: the bytes per syntax-tree node, kernel term, ZIR node and native value,
//! measured on the step units and recorded in `zed/compiler/MLIR.md`, section Layout. The
//! record's inline sizes are the compiler's own, so a type that grows shows in it.

use std::mem::size_of;

use zed_kernel::{Term, Value};
use zed_rt::Word;
use zed_rt::heap::CELL_BYTES;
use zed_tests::layout::{Native, Record, ast_stage, record};
use zed_tests::oracle::step_units;
use zed_tests::scaling;
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

#[test]
fn the_peak_bytes_of_n_and_8n_definitions_scale() {
    let peak = |n: usize| {
        let text = many(n);
        let (r, l) = zed_alloc_count::live(|| record(&text).unwrap_or_else(|e| panic!("{e}")));
        assert_eq!(r.native.runs, n as u64);
        l.peak
    };
    scaling::hold(
        "the peak bytes of recording 100 and 800 definitions",
        "bytes",
        peak(100),
        peak(800),
        1,
    );
}

/// The layout record of a unit of a few definitions is made, one native run per definition; the
/// time is held linear in the definitions in `bench/layout.rs`.
#[test]
fn the_record_of_a_unit_of_a_few_definitions_is_made() {
    for n in [1, 2, 9] {
        let r = record(&many(n)).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(r.native.runs, n as u64);
    }
}
