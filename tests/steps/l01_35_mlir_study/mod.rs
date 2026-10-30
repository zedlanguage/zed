//! Step L1.35: the MLIR study, `zed/compiler/MLIR.md`. The record decides how ZIR lowers to
//! MLIR's dialects; this step holds it to the node inventory, so an operation or a region
//! kind added later without a lowering fails here.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::sync::Arc;

use zed_kernel::Prim;
use zed_kernel::term::{GuardPos, Witness};
use zedc::zir::{Derived, Op, RegionKind, kind_name, op_name};

fn record() -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/compiler/MLIR.md");
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
}

/// The first cells of the rows of the table under heading `##` `title`, without backticks.
fn rows(text: &str, title: &str) -> BTreeSet<String> {
    let start = text
        .find(&format!("\n## {title}\n"))
        .unwrap_or_else(|| panic!("no section `{title}`"));
    let body = &text[start + title.len() + 5..];
    let body = &body[..body.find("\n## ").unwrap_or(body.len())];
    body.lines()
        .filter(|l| l.starts_with("| `"))
        .map(|l| l[2..].split(" |").next().unwrap().replace('`', ""))
        .collect()
}

/// The row name of `op`: its text-form name, and `read` or `push` for a port.
fn row(op: &Op) -> String {
    // No wildcard: a new operation stops this test from building until it is named here.
    match op {
        Op::Read(_) => "port read".into(),
        Op::Push(_) => "port push".into(),
        Op::Reindex(_)
        | Op::Discard
        | Op::Fold { .. }
        | Op::Fix { .. }
        | Op::Gen(_)
        | Op::Fam
        | Op::Derived(_)
        | Op::Prim(_)
        | Op::Apply
        | Op::Lambda
        | Op::If
        | Op::Match(_)
        | Op::Rec
        | Op::Wave => op_name(op).into(),
    }
}

fn every_op() -> Vec<Op> {
    let p: Arc<str> = "out".into();
    vec![
        Op::Reindex(Witness::Residue),
        Op::Discard,
        Op::Fold {
            depth: 1,
            identity: false,
            ev: Default::default(),
        },
        Op::Fix {
            lattice: true,
            ev: Default::default(),
        },
        Op::Gen(GuardPos::Before),
        Op::Read(p.clone()),
        Op::Push(p),
        Op::Fam,
        Op::Derived(Derived::Group),
        Op::Derived(Derived::Rank),
        Op::Derived(Derived::Scan),
        Op::Derived(Derived::Join),
        Op::Prim(Prim::Add),
        Op::Apply,
        Op::Lambda,
        Op::If,
        Op::Match(Vec::new()),
        Op::Rec,
        Op::Wave,
    ]
}

#[test]
fn every_operation_has_a_lowering() {
    let want: BTreeSet<String> = every_op().iter().map(row).collect();
    assert_eq!(want.len(), 19);
    assert_eq!(rows(&record(), "Operations"), want);
}

#[test]
fn every_region_kind_has_a_form() {
    let kinds = [
        RegionKind::Function,
        RegionKind::Match,
        RegionKind::Loop,
        RegionKind::Rec,
        RegionKind::Port,
    ];
    let want: BTreeSet<String> = kinds.iter().map(|k| kind_name(*k).to_string()).collect();
    assert_eq!(rows(&record(), "Region kinds"), want);
}

#[test]
fn both_edge_kinds_have_a_form() {
    let want: BTreeSet<String> = ["state", "value"].map(String::from).into();
    assert_eq!(rows(&record(), "Edges"), want);
}

#[test]
fn the_record_answers_the_four_questions() {
    // The decisions the plan names: no ZIR dialect in MLIR, the graph regions, the state edges,
    // the content addresses, the certificates, and Cranelift as the compact back end.
    let text = record();
    for decision in [
        "**ZIR is lowered into MLIR's existing dialects and is not written as an MLIR dialect.**",
        "**Graph regions are not used.**",
        "**State edges become order, not values.**",
        "**Content addresses travel as locations.**",
        "**Certificates stop at the lowering.**",
        "**The compact back end stays Cranelift.**",
    ] {
        assert!(text.contains(decision), "the record lacks {decision}");
    }
}
