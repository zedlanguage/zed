//! FAIL-preimage-arity-stop-unreported, found by TEST-complete-preimage (author P189): a
//! primitive given the wrong number of operands, under a comparison, is reported as a stop.
//! `Add(x) < 3` (an `Add` with one operand) gave `x [..]; necessary` with no stop: the backward
//! transfer stops at such a term, but the scan of a comparison's operands read it as a scalar
//! primitive and scanned only its operands. DESIGN.md step L1.25: the stops include "a term
//! outside the catalog ...; each is reported with the term it stopped at, and a stop keeps the
//! whole box, necessary".

use zed_kernel::Prim::{Add, Lt, Neg};
use zed_kernel::term::build::{lit, prim, var};
use zedc::store::preimage::{Demand, StopKind, preimage};

use super::{check, doms, shown};

#[test]
fn a_primitive_with_the_wrong_number_of_operands_is_reported() {
    let ds = doms(&[("x", None, None)]);
    let d = Demand::Bool(true);
    for t in [
        prim(Lt, vec![prim(Add, vec![var("x")]), lit(3)]),
        // Too many operands, and a unary primitive given two.
        prim(
            Lt,
            vec![prim(Add, vec![var("x"), var("x"), lit(1)]), lit(3)],
        ),
        prim(Lt, vec![prim(Neg, vec![var("x"), lit(1)]), lit(3)]),
        // Under arithmetic that the transfer follows.
        prim(
            Lt,
            vec![prim(Add, vec![var("x"), prim(Add, vec![var("x")])]), lit(3)],
        ),
    ] {
        let p = preimage(&t, &ds, &d);
        check(&t, &ds, &d, &p, (-40, 40));
        assert_eq!(p.domains["x"].to_string(), "[..]", "{}", shown(&p));
        assert!(
            p.stops.first().is_some_and(|s| s.kind == StopKind::Outside),
            "{t}: {}",
            shown(&p)
        );
    }
}

/// The control: `Add(x, 1) < 3`, with its two operands, is exact with no stop.
#[test]
fn a_primitive_with_its_operands_is_no_stop() {
    let ds = doms(&[("x", None, None)]);
    let d = Demand::Bool(true);
    let t = prim(Lt, vec![prim(Add, vec![var("x"), lit(1)]), lit(3)]);
    let p = preimage(&t, &ds, &d);
    check(&t, &ds, &d, &p, (-40, 40));
    assert!(p.stops.is_empty(), "{t}: {}", shown(&p));
    assert_eq!(shown(&p), "x [..=1]; exact", "{t}");
}
