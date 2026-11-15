//! The canonicalization VERSION moves with the normal form (FAIL-zir-canon-version-not-bumped).
//! crates/zedc-zir/src/canon/mod.rs: "Any change to a rule or to the serialization increments
//! VERSION, so every address changes with it and no address is shared across rule sets." Commit
//! 0a516f19c changed what the ZIR binder rule gives a pattern binder spelled as another level
//! (`($$5, y)`), and left VERSION at 6; no test noticed, since every pinned address hashes
//! VERSION and none of the pinned inputs met the changed case.
//!
//! This test hashes the bytes each address is taken over, without VERSION: the binary form of
//! the ZIR normal form, and the serialization of the kernel normal form, for a fixed set of
//! graphs and definitions chosen to reach every rule (binders written, spelled as their own
//! level, spelled as another level, nested; hints; facets out of order and repeated; integer
//! facts spelled several ways). `HISTORY` records that hash for each VERSION, oldest first. A
//! change to a rule's result or to a serialization changes the hash, and the test then fails
//! until VERSION is incremented and the new hash appended under it. The test parses its graphs
//! from the ZIR text form, so a change to that parser that reads one of them differently fails
//! it too; such a change does not need a new VERSION, and the hash is then re-recorded under the
//! current one.

use zed_kernel::term::Prim;
use zed_kernel::term::build::{lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zedc::address::ContentAddress;
use zedc::canon::{Def, Domain, Facet, VERSION};
use zedc::store::interval::IntervalSet;
use zedc::zir::{binary, canon};

use super::graph;

/// The hash `normal_forms` gives under each VERSION, oldest first: append, never edit.
/// Version 6 is the hash before 0a516f19c: this file run with that commit's change to
/// crates/zedc-zir/src/zir/canon.rs reverted, the only change to a normal form since version 6.
/// Version 8 renames a kernel binder spelled as another level (`other_level` and `swapped`
/// below), FAIL-kernel-canon-misplaced-level.
/// Version 9 writes a string value by the nodes of its text (BUILD-doubling-60s), and adds a
/// graph with two string constants to the set.
/// Version 10 adds the names of an export's parameters that a call may write to its address
/// (ADDR-param-names, `canon::export_address`) and changes no normal form, so its hash is
/// version 9's.
const HISTORY: &[(u32, &str)] = &[
    (
        6,
        "af396b88ed1e0dcc1bcd9cd07347197d117cd58c5f5f98533aa80356e9301b69",
    ),
    (
        7,
        "41155e123640f443421c6f52ca6546ac8ae655429301fdfbf9dd600141f0ccfe",
    ),
    (
        8,
        "c85680ebe00c9fec4892ad04282208321ad49b3692b6fa1c4e49abdfcd6f8d18",
    ),
    (
        9,
        "188a450908788f16778a4a114a6ce47e4226048131afe23336fd176abf472408",
    ),
    (
        10,
        "188a450908788f16778a4a114a6ce47e4226048131afe23336fd176abf472408",
    ),
];

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

/// The hash of the bytes the addresses of the fixed set are taken over, VERSION left out:
/// each item's length and then its bytes, the graphs first.
fn normal_forms() -> String {
    let mut h = blake3::Hasher::new();
    let mut put = |bytes: &[u8]| {
        h.update(&(bytes.len() as u64).to_le_bytes());
        h.update(bytes);
    };
    for src in graphs() {
        put(&binary::encode(&canon::canonicalize(&graph(&src))).expect("memory for the bytes"));
    }
    for d in defs() {
        put(
            &zedc::canon::serialize(&zedc::canon::canonicalize(&d), &none)
                .expect("memory for the bytes"),
        );
    }
    h.finalize().to_hex().to_string()
}

#[test]
fn a_changed_normal_form_comes_with_a_new_version() {
    assert!(
        HISTORY.windows(2).all(|w| w[0].0 < w[1].0),
        "HISTORY lists each version once, oldest first"
    );
    let now = normal_forms();
    let last = HISTORY.last().expect("a recorded version");
    match HISTORY.iter().find(|(v, _)| *v == VERSION) {
        Some((_, d)) if *d == now => {}
        Some((_, d)) => panic!(
            "the normal forms of the fixed set changed under canonicalization VERSION {VERSION} \
             (recorded {d}, now {now}). A change to a rule's result or to the serialization \
             increments VERSION in crates/zedc-zir/src/canon/mod.rs; then append ({}, \"{now}\") \
             to HISTORY and pin again the addresses that hash VERSION.",
            VERSION + 1
        ),
        None => panic!(
            "canonicalization VERSION {VERSION} has no hash in HISTORY: append ({VERSION}, \
             \"{now}\")"
        ),
    }
    assert_eq!(last.0, VERSION, "VERSION is the newest version in HISTORY");
}
