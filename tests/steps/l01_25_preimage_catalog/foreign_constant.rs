//! FAIL-preimage-foreign-constant-unreported, found by TEST-complete-preimage (author P189): a
//! foreign call whose arguments read no input is reported as a stop. `hash(1) < x` gave
//! `x [..]; necessary` with no stop, so nothing said why the box was only necessary, while
//! `hash(x) < 10` reports "foreign name `hash` stops the transfer at hash(x)": the scan of the
//! stops skipped every term that reads no input, though a foreign call on constants cannot be
//! run. DESIGN.md step L1.25: "the stops are a string operation ..., a call to a name the term
//! does not bind (a foreign call), ...; each is reported with the term it stopped at, and a
//! stop keeps the whole box, necessary".

use zed_kernel::Prim::{Add, Eq, Lt};
use zed_kernel::Term;
use zed_kernel::term::build::{app, lit, prim, var};
use zedc::store::preimage::{Demand, StopKind, preimage};

use super::{check, doms, shown};

#[test]
fn a_foreign_call_on_constants_is_reported() {
    let hash = |t: Term| app(var("hash"), vec![t]);
    let ds = doms(&[("x", None, None)]);
    let d = Demand::Bool(true);
    for t in [
        prim(Lt, vec![hash(lit(1)), var("x")]),
        prim(Eq, vec![var("x"), hash(lit(1))]),
        // Inside arithmetic on the constants.
        prim(Lt, vec![var("x"), prim(Add, vec![hash(lit(1)), lit(2)])]),
        // The control: a foreign call on the input, reported before.
        prim(Lt, vec![hash(var("x")), lit(10)]),
    ] {
        let p = preimage(&t, &ds, &d);
        check(&t, &ds, &d, &p, (-40, 40));
        assert!(!p.exact, "{t}: {}", shown(&p));
        assert!(
            p.stops
                .first()
                .is_some_and(|s| s.kind == StopKind::Foreign("hash".into())),
            "{t}: {}",
            shown(&p)
        );
    }
}

/// A term that reads no input and runs is no stop: `(1 + 2) < x` is exact with no stop.
#[test]
fn a_constant_that_runs_is_no_stop() {
    let ds = doms(&[("x", None, None)]);
    let d = Demand::Bool(true);
    let t = prim(Lt, vec![prim(Add, vec![lit(1), lit(2)]), var("x")]);
    let p = preimage(&t, &ds, &d);
    check(&t, &ds, &d, &p, (-40, 40));
    assert!(p.stops.is_empty(), "{t}: {}", shown(&p));
    assert_eq!(shown(&p), "x [4..]; exact", "{t}");
}
