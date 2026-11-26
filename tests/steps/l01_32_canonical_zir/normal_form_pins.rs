//! The normal forms of a fixed set of graphs and definitions are pinned, so that a change to
//! what a rule gives or to a serialization is seen (FAIL-zir-canon-version-not-bumped: commit
//! 0a516f19c changed what the ZIR binder rule gives a pattern binder spelled as another level,
//! `($$5, y)`, and no test noticed, since none of the pinned inputs met the changed case).
//!
//! This test hashes the bytes each address is taken over: the binary form of the ZIR normal
//! form, and the serialization of the kernel normal form, for a fixed set of graphs and
//! definitions chosen to reach every rule (binders written, spelled as their own level,
//! spelled as another level, nested; hints; facets out of order and repeated; integer facts
//! spelled several ways; strings). The address had a version number until 2026-11-20, which
//! this test made sure moved with the normal forms; there is none before Zed 1.0 (author
//! order, 2026-11-20: "just keep building and fixing, you don't need to rubber stamp anything
//! as a specific ABI version"), so a change to a normal form is now pinned here again, with
//! the addresses pinned elsewhere. The test parses its graphs from the ZIR text form, so a
//! change to that parser that reads one of them differently fails it too.

use zed_kernel::term::Prim;
use zed_kernel::term::build::{lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zedc::address::{ContentAddress, Framed};
use zedc::canon::{Def, Domain, Facet};
use zedc::store::interval::IntervalSet;
use zedc::zir::{binary, canon};

use super::graph;

/// The hash `normal_forms` gives. Changed by A106 (2026-11-20), which writes a kernel string
/// value as its length and its bytes (`strings` below), where it wrote the rules of a canonical
/// parse.
const PINNED: &str = "2ddb603d15a90342b2d89c6b4179c9122029fa84762e0b7b2bc92c27a7419f86";

/// The match of `p` over a pair of integers whose arm adds its two binders.
fn pair(p: &str) -> String {
    format!(
        "zir 1\nr region function (tuple)\nr.0 match [{p}] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0.0 prim + (r.0/0^0, r.0/0^1) -> (int)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n"
    )
}

/// The identity on one argument of type `e`.
fn arg(e: &str) -> String {
    format!("zir 1\nr region function ({e})\nr results (r^0)\n")
}

/// The ZIR graphs of the fixed set, as text.
fn graphs() -> Vec<String> {
    let mut out: Vec<String> = [
        "(a, y)",
        "($$0, $$1)",
        "($$1, $$0)",
        "($$5, y)",
        "(a, $$0)",
        "($$1, y)",
        "(x, =0)",
    ]
    .into_iter()
    .map(pair)
    .collect();
    // Nested patterns, whose binders are counted in preorder.
    out.push(
        "zir 1\nr region function ((tuple (tuple int int) int))\nr.0 match [((p, $$7), q)] (r^0) -> (int)\nr.0/0 region match (int; int; int)\nr.0/0 results (r.0/0^2)\nr results (r.0^0)\n"
            .into(),
    );
    // A match inside a lambda's body, and an optional with a hint on its argument.
    out.push(
        "zir 1\nr region function ()\nr.0 lambda () -> ((-> tuple int))\nr.0/0 region function (tuple)\nr.0/0.0 match [(key, $$0)] (r.0/0^0) -> (int)\nr.0/0.0/0 region match (int; int)\nr.0/0.0/0 results (r.0/0.0/0^1)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n"
            .into(),
    );
    out.push(
        "zir 1\nr region function ((| #none (#some (tuple int))); int in [0..] hint name \"price\")\nr.0 match [#some(off), #none] (r^0, r^1) -> (int)\nr.0/0 region match (int; int in [0..] hint name \"price\")\nr.0/0.0 prim - (r.0/0^1, r.0/0^0) -> (int)\nr.0/0 results (r.0/0.0^0)\nr.0/1 region match (int in [0..] hint name \"price\")\nr.0/1 results (r.0/1^0)\nr results (r.0^0)\n"
            .into(),
    );
    for e in [
        "int facet units \"cents\" facet currency \"EUR\" facet units \"cents\"",
        "int in [0..=10] class 1 mod 4",
        "int set {1, 5, 9}",
        "int in [..]",
    ] {
        out.push(arg(e));
    }
    // Two string constants.
    out.push("zir 1\nr region function ()\nr results (\"ab\", \"abab\")\n".into());
    out
}

/// A facet, a hint when `hint`.
fn facet(kind: &str, value: impl Into<Value>, hint: bool) -> Facet {
    Facet {
        hint,
        kind: kind.into(),
        value: value.into(),
    }
}

/// The kernel definitions of the fixed set.
fn defs() -> Vec<Def> {
    let def = |name: &str, body| Def {
        name: name.into(),
        domain: None,
        facets: vec![],
        body,
    };
    let mut balance = def(
        "balance",
        lam(&["d", "w"], prim(Prim::Sub, vec![var("d"), var("w")])),
    );
    balance.facets = vec![
        facet("units", "cent", false),
        facet("monotone", Value::atom("none"), false),
        facet("units", "cent", false),
        facet("doc", Value::str("the account balance"), true),
    ];
    let mut index = def("index", var("i"));
    index.domain = Some(Domain::ints(IntervalSet::of(1, 3)));
    vec![
        balance,
        index,
        // Shadowing, a let, and binders already named as levels (`\0k`, a name no source text
        // can spell), at their own level and at another.
        def(
            "shadow",
            lam(&["x"], lam(&["x"], prim(Prim::Add, vec![var("x"), lit(1)]))),
        ),
        def(
            "total",
            let_(
                "t",
                lit(3),
                lam(&["n"], prim(Prim::Mul, vec![var("t"), var("n")])),
            ),
        ),
        // Strings, the second held as a join of two nodes, the third sharing the nodes of the
        // first two (item CANON-term-string-nodes): one string in several trees.
        def(
            "strings",
            lit(Value::Tuple(
                [
                    Value::str("abcab"),
                    Value::Str(
                        zed_kernel::text::Text::join(&"abcab".into(), &"abcab".into())
                            .expect("10 bytes"),
                    ),
                    Value::str("abcababcababcab"),
                ]
                .into_iter()
                .collect(),
            )),
        ),
        def("own_level", lam(&["\u{0}0"], var("\u{0}0"))),
        def("other_level", lam(&["\u{0}5"], var("\u{0}5"))),
        def(
            "swapped",
            lam(
                &["\u{0}1", "\u{0}0"],
                prim(Prim::Sub, vec![var("\u{0}1"), var("\u{0}0")]),
            ),
        ),
    ]
}

/// No definition resolves: every free variable is hashed by name.
fn none(_: &str) -> Option<ContentAddress> {
    None
}

/// The hash of the bytes the addresses of the fixed set are taken over:
/// each item's length and then its bytes, the graphs first.
fn normal_forms() -> String {
    let mut h = Framed::new(b"");
    for src in graphs() {
        h.field(&binary::encode(&canon::canonicalize(&graph(&src))).expect("memory for the bytes"));
    }
    for d in defs() {
        h.field(
            &zedc::canon::serialize(&zedc::canon::canonicalize(&d), &none)
                .expect("memory for the bytes"),
        );
    }
    blake3::Hash::from(h.digest()).to_hex().to_string()
}

#[test]
fn the_normal_forms_of_the_fixed_set_are_pinned() {
    let now = normal_forms();
    assert_eq!(
        now, PINNED,
        "the normal forms of the fixed set changed. A change to a rule's result or to a \
         serialization changes the address of everything it reaches: pin it again here, with \
         the addresses pinned in m0_07, m0_11, l01_32 and l02_08, and say why in PINNED's comment."
    );
}
