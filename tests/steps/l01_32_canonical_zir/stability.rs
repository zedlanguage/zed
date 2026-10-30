//! Which changes to a graph keep its address, and which change it.

use super::graph;
use zedc::zir::canon::{address, canonicalize, ranks};
use zedc::zir::{Edge, Op, binary};

/// An optional discount: the arm that has one subtracts it, the other passes the price on.
const DISCOUNT: &str = "\
zir 1
r region function ((| #none (#some (tuple int))); int in [0..] hint name \"price\")
r.0 match [#some(off), #none] (r^0, r^1) -> (int)
r.0/0 region match (int; int in [0..] hint name \"price\")
r.0/0.0 prim - (r.0/0^1, r.0/0^0) -> (int)
r.0/0 results (r.0/0.0^0)
r.0/1 region match (int in [0..] hint name \"price\")
r.0/1 results (r.0/1^0)
r results (r.0^0)
";

/// `DISCOUNT` with `from` replaced by `to`, which must occur in it.
fn with(from: &str, to: &str) -> zedc::zir::Region {
    assert!(DISCOUNT.contains(from), "{from}");
    graph(&DISCOUNT.replace(from, to))
}

#[test]
fn renamed_binders_keep_the_address() {
    let a = address(&graph(DISCOUNT));
    assert_eq!(address(&with("#some(off)", "#some(d)")), a);
    // A pair pattern's binders, renamed together and apart.
    let pair = |p: &str| {
        graph(&format!(
            "zir 1\nr region function (tuple)\nr.0 match [{p}] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0.0 prim + (r.0/0^0, r.0/0^1) -> (int)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n"
        ))
    };
    assert_eq!(address(&pair("(x, y)")), address(&pair("(lo, hi)")));
    assert_eq!(address(&pair("(y, x)")), address(&pair("(x, y)")));
    // Each binder takes its own level: the second is the one argument before it.
    let Op::Match(ps) = &canonicalize(&pair("(lo, hi)")).nodes[0].op else {
        panic!("a match")
    };
    assert_eq!(zedc::zir::text::pattern(&ps[0]), "(\u{0}0, \u{0}1)");
    // A match one region down, inside a function's body.
    let inner = |a: &str, b: &str| {
        graph(&format!(
            "zir 1\nr region function ()\nr.0 lambda () -> ((-> tuple int))\nr.0/0 region function (tuple)\nr.0/0.0 match [({a}, {b})] (r.0/0^0) -> (int)\nr.0/0.0/0 region match (int; int)\nr.0/0.0/0 results (r.0/0.0/0^1)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n"
        ))
    };
    assert_eq!(address(&inner("key", "count")), address(&inner("k", "n")));
    // Binding where a literal was matched is a different graph.
    assert_ne!(address(&pair("(x, =0)")), address(&pair("(x, y)")));
}

#[test]
fn hints_do_not_reach_the_address() {
    let a = address(&graph(DISCOUNT));
    assert_eq!(
        address(&with(
            "hint name \"price\")\nr.0 ",
            "hint name \"cost\")\nr.0 "
        )),
        a
    );
    assert_eq!(
        address(&graph(&DISCOUNT.replace(" hint name \"price\"", ""))),
        a
    );
}

#[test]
fn facet_order_and_repeats_do_not_reach_the_address() {
    let one = "int facet units \"cents\" facet currency \"EUR\"";
    let src = |e: &str| format!("zir 1\nr region function ({e})\nr results (r^0)\n");
    let a = address(&graph(&src(one)));
    assert_eq!(
        address(&graph(&src(
            "int facet currency \"EUR\" facet units \"cents\""
        ))),
        a
    );
    assert_eq!(
        address(&graph(&src(
            "int facet units \"cents\" facet currency \"EUR\" facet units \"cents\""
        ))),
        a
    );
    assert_ne!(
        address(&graph(&src(
            "int facet units \"cents\" facet currency \"USD\""
        ))),
        a
    );
    assert_ne!(address(&graph(&src("int facet units \"cents\""))), a);
}

#[test]
fn one_set_of_integers_has_one_address() {
    // The odd quarter-steps from 1 to 9, spelled three ways.
    let src = |e: &str| format!("zir 1\nr region function ({e})\nr results (r^0)\n");
    let a = address(&graph(&src("int in [0..=10] class 1 mod 4")));
    assert_eq!(address(&graph(&src("int in [1..=9] class 1 mod 4"))), a);
    assert_eq!(address(&graph(&src("int set {1, 5, 9}"))), a);
    assert_ne!(address(&graph(&src("int set {1, 5}"))), a);
    // No facts and the facts every integer meets are one domain.
    assert_eq!(
        address(&graph(&src("int"))),
        address(&graph(&src("int in [..]")))
    );
}

#[test]
fn values_reach_the_address() {
    let a = address(&graph(DISCOUNT));
    for (from, to) in [
        ("prim -", "prim +"),
        ("(r.0/0^1, r.0/0^0)", "(r.0/0^0, r.0/0^1)"),
        ("(int; int in [0..] hint", "(int; int in [1..] hint"),
        ("#some(off), #none", "#some(off), #_"),
        ("r results (r.0^0)", "r results (r.0^0, 0)"),
    ] {
        assert_ne!(address(&with(from, to)), a, "{from} -> {to}");
    }
    let port = |p: &str| {
        graph(&format!(
            "zir 1\nr region port (state {p})\nr.0 port read {p} (r^0) -> (String; state {p})\nr results (r.0^1)\n"
        ))
    };
    assert_ne!(address(&port("in")), address(&port("keys")));
}

#[test]
fn the_normal_form() {
    let g = graph(DISCOUNT);
    let n = canonicalize(&g);
    assert_eq!(canonicalize(&n), n);
    assert_eq!(ranks(&n)[..2], [0, 0]);
    assert_eq!(ranks(&n)[3], 0);
    // The binder is renamed to level 0, and every hint, its written name's among them, is gone.
    let Op::Match(ps) = &n.nodes[0].op else {
        panic!("a match")
    };
    assert_eq!(zedc::zir::text::pattern(&ps[0]), "#some(\u{0}0)");
    let Edge::Value(v) = &n.nodes[0].regions[0].args[0] else {
        panic!("a value edge")
    };
    assert!(v.facets.is_empty());
    // The normal form is what the binary form carries, and it reads back.
    assert_eq!(binary::decode(&binary::encode(&n)), Ok(n));
    assert_eq!(address(&g).to_string().len(), 64, "64 lowercase hex digits");
}

#[test]
fn the_address_is_pinned() {
    // The binary form fixes its own layout (little-endian 64-bit words, floats by their
    // IEEE-754 bits, big numbers in decimal), so this hash is the same on every machine.
    assert_eq!(
        address(&graph(DISCOUNT)).to_string(),
        "800ef82a27b7bce0e3dbb8d28e72373e6e875532698f89294af97adbb2847b41"
    );
}

#[test]
fn every_nan_is_one_word() {
    // A NaN with another payload reads as the one NaN, and is written as the fixed word.
    let mut bytes = zedc::zir::binary::encode(&graph(NAN_CONST));
    let at = bytes
        .windows(8)
        .position(|w| w == zedc::zir::binary::NAN_BITS.to_le_bytes())
        .expect("the NaN word");
    bytes[at] ^= 1;
    let g = zedc::zir::binary::decode(&bytes).expect("a graph");
    assert_eq!(
        zedc::zir::binary::encode(&g)[at],
        zedc::zir::binary::NAN_BITS.to_le_bytes()[0]
    );
    assert_eq!(address(&g), address(&graph(NAN_CONST)));
}

const NAN_CONST: &str = "\
zir 1
r region function ()
r.0 prim tuple (nan, 1.5) -> (_)
r results (r.0^0)
";
