//! Whole graphs of the shapes real programs lower to, each through every round trip.

use super::round;
use zedc::zir::{Edge, Op, RegionKind, Src};

/// The total of a price list: `fam` prices each item, and an associative, commutative `+`
/// with identity 0 folds the family's one level.
const PRICE_TOTAL: &str = "\
zir 1
r region function (struct; int in [0..])
r.0 fam (r^0, r^1) -> (struct)
r.0/0 region function (String; int in [0..])
r.0/0.0 prim * (r.0/0^1, 3) -> (int)
r.0/0 results (r.0/0.0^0)
r.1 lambda () -> ((-> (tuple int int) int))
r.1/0 region function (int; int)
r.1/0.0 prim + (r.1/0^0, r.1/0^1) -> (int)
r.1/0 results (r.1/0.0^0)
r.2 fold 1 identity {associative: axiom, commutative: axiom} (r.0^0, r.1^0, 0) -> (int in [0..] facet units \"cents\")
r results (r.2^0)
";

#[test]
fn price_total() {
    let g = round(PRICE_TOTAL);
    assert_eq!(g.kind, RegionKind::Function);
    assert_eq!(g.nodes.len(), 3);
    let fold = &g.nodes[2];
    assert!(matches!(
        fold.op,
        Op::Fold {
            depth: 1,
            identity: true,
            ..
        }
    ));
    assert_eq!(fold.inputs[0], Src::Out(0, 0));
    // The capture enters the `fam` region as its argument after the key, with its type.
    assert_eq!(g.nodes[0].regions[0].args[1], g.args[1]);
}

/// `main` printing a greeting: a wave threads the `out` port's state through a push.
const GREETING: &str = "\
zir 1
r region port (state out)
r.0 wave (r^0) -> (state out)
r.0/0 region port (state out)
r.0/0.0 port push out (r.0/0^0, \"Hello, world\") -> (_; state out)
r.0/0 results (r.0/0.0^1)
r results (r.0^0)
";

#[test]
fn greeting() {
    let g = round(GREETING);
    assert_eq!(g.nodes[0].outputs, vec![Edge::State("out".into())]);
}

/// A read from `in` and a push of what was read to `out`: two ports, each state used once.
const ECHO: &str = "\
zir 1
r region port (state in; state out)
r.0 port read in (r^0) -> (String; state in)
r.1 port push out (r^1, r.0^0) -> (_; state out)
r results (r.0^1, r.1^1)
";

#[test]
fn echo() {
    round(ECHO);
}

/// An optional quantity with a default: a match on an atom, one arm per case.
const DEFAULTED: &str = "\
zir 1
r region function ((| #none (#some (tuple int))); int)
r.0 match [#some(n), #none] (r^0, r^1) -> (int)
r.0/0 region match (int; int)
r.0/0 results (r.0/0^0)
r.0/1 region match (int)
r.0/1 results (r.0/1^0)
r results (r.0^0)
";

#[test]
fn defaulted() {
    let g = round(DEFAULTED);
    // The first arm binds `n` before the capture; the second binds nothing.
    assert_eq!(g.nodes[0].regions[0].args.len(), 2);
    assert_eq!(g.nodes[0].regions[1].args.len(), 1);
}

/// A countdown: `gen` steps the frame down by 1 while it is positive.
const COUNTDOWN: &str = "\
zir 1
r region function (int in [0..])
r.0 gen before (r^0) -> (struct)
r.0/0 region loop (int)
r.0/0.0 prim - (r.0/0^0, 1) -> (int)
r.0/0 results (r.0/0.0^0)
r.0/1 region loop (int)
r.0/1.0 prim > (r.0/1^0, 0) -> (bool)
r.0/1 results (r.0/1.0^0)
r results (r.0^0)
";

#[test]
fn countdown() {
    round(COUNTDOWN);
}

/// Reachability as a least fixed point: bottom `{}`, join by union, and each step adds the
/// edges' targets.
const REACHABLE: &str = "\
zir 1
r region function (struct)
r.0 lambda () -> ((-> (tuple struct struct) struct))
r.0/0 region function (struct; struct)
r.0/0.0 prim union (r.0/0^0, r.0/0^1) -> (struct)
r.0/0 results (r.0/0.0^0)
r.1 fix lattice {finiteHeight: bounded, monotone: proved} ({}, r.0^0, r^0) -> (struct)
r.1/0 region loop (struct; struct)
r.1/0.0 prim union (r.1/0^0, r.1/0^1) -> (struct)
r.1/0 results (r.1/0.0^0)
r results (r.1^0)
";

#[test]
fn reachable() {
    round(REACHABLE);
}

/// Sales grouped by region: `group` carries its definition, a `reindex` that swaps the two
/// key levels, as its certificate.
const BY_REGION: &str = "\
zir 1
r region function (struct)
r.0 group (r^0) -> (struct)
r.0/0 region function (struct)
r.0/0.0 lambda () -> ((-> _ _))
r.0/0.0/0 region function (_)
r.0/0.0/0.0 prim pathKey (r.0/0.0/0^0, 1) -> (_)
r.0/0.0/0.1 prim pathKey (r.0/0.0/0^0, 0) -> (_)
r.0/0.0/0.2 prim path (r.0/0.0/0.0^0, r.0/0.0/0.1^0) -> (_)
r.0/0.0/0 results (r.0/0.0/0.2^0)
r.0/0.1 lambda () -> ((-> _ _))
r.0/0.1/0 region function (_)
r.0/0.1/0 results (r.0/0.1/0^0)
r.0/0.2 reindex residue (r.0/0^0, r.0/0.0^0, r.0/0.1^0) -> (struct)
r.0/0 results (r.0/0.2^0)
r results (r.0^0)
";

#[test]
fn by_region() {
    round(BY_REGION);
}

/// Tiered shipping: an `if` whose arms read a captured weight, with facts on every edge.
const SHIPPING: &str = "\
zir 1
r region function (int in [0..=50000] class 0 mod 10 hint name \"grams\")
r.0 prim < (r^0, 1000) -> (bool)
r.1 if (r.0^0, r^0) -> (int set {499, 999})
r.1/0 region match (int in [0..=50000] class 0 mod 10 hint name \"grams\")
r.1/0 results (499)
r.1/1 region match (int in [0..=50000] class 0 mod 10 hint name \"grams\")
r.1/1 results (999)
r results (r.1^0)
";

#[test]
fn shipping() {
    let g = round(SHIPPING);
    let Edge::Value(v) = &g.args[0] else {
        panic!("a value edge")
    };
    assert!(v.facets[0].hint);
}

/// Mutual recursion: `even` and `odd`, defined together by one `rec`.
const PARITY: &str = "\
zir 1
r region function ()
r.0 rec () -> ((-> int bool); (-> int bool))
r.0/0 region rec ((-> int bool); (-> int bool))
r.0/0.0 lambda (r.0/0^1) -> ((-> int bool))
r.0/0.0/0 region function (int; (-> int bool))
r.0/0.0/0.0 prim == (r.0/0.0/0^0, 0) -> (bool)
r.0/0.0/0.1 prim - (r.0/0.0/0^0, 1) -> (int)
r.0/0.0/0.2 apply (r.0/0.0/0^1, r.0/0.0/0.1^0) -> (bool)
r.0/0.0/0.3 prim || (r.0/0.0/0.0^0, r.0/0.0/0.2^0) -> (bool)
r.0/0.0/0 results (r.0/0.0/0.3^0)
r.0/0.1 lambda (r.0/0^0) -> ((-> int bool))
r.0/0.1/0 region function (int; (-> int bool))
r.0/0.1/0.0 prim != (r.0/0.1/0^0, 0) -> (bool)
r.0/0.1/0.1 prim - (r.0/0.1/0^0, 1) -> (int)
r.0/0.1/0.2 apply (r.0/0.1/0^1, r.0/0.1/0.1^0) -> (bool)
r.0/0.1/0.3 prim && (r.0/0.1/0.0^0, r.0/0.1/0.2^0) -> (bool)
r.0/0.1/0 results (r.0/0.1/0.3^0)
r.0/0 results (r.0/0.0^0, r.0/0.1^0)
r results (r.0^0, r.0^1)
";

#[test]
fn parity() {
    round(PARITY);
}

/// A report keyed by tuples, with every kind of constant on its edges.
const CONSTANTS: &str = "\
zir 1
r region function ()
r.0 prim tuple (-3r/4r, 1.5e30, nan, -0.0, 123456789012345678901234567890) -> (_)
r.1 prim tuple (#err(code: 3, why: \"disk\\nfull\"), #pair(1, 2), (7), [1 -> \"a\"], {1 -> 2, 3 -> 4}, {\"x\", \"y\"}, {}) -> (_)
r results (r.0^0, r.1^0, true)
";

#[test]
fn constants() {
    round(CONSTANTS);
}
