//! A term the elaborator builds once and reads in several places, such as an inlined helper
//! that both branches of a test call, is one shared subterm. The preimage numbers each shared
//! subterm once, by its id, so its time is of the distinct parts of the term, not of the
//! paths through it, and the result does not depend on where or in what order the parts were
//! allocated.

use zed_kernel::{Prim, Shared, Term, Value};
use zedc::store::preimage::{Demand, preimage};

use super::{doms, shown};

fn ge(k: i64) -> Term {
    Term::Prim(
        Prim::Ge,
        vec![Term::Var("i".into()), Term::Lit(Value::Int(k))],
    )
}

/// `if i >= k { s } else { s }` for `k` from 1 to `depth`, each level's two branches one
/// shared subterm `s`, the level below, and the bottom `i >= 0`: `depth + 1` distinct tests
/// on `2^depth` paths. `pad` allocates that many unused shared terms before each level, so
/// the levels lie at other addresses and take other ids.
pub(super) fn levels(depth: usize, pad: usize) -> Shared {
    let mut keep = Vec::new();
    let mut s = Shared::new(ge(0));
    for k in 1..=depth as i64 {
        keep.extend((0..pad).map(|_| Shared::new(ge(-1))));
        s = Shared::new(Term::If(Shared::new(ge(k)), s.clone(), s));
    }
    s
}

/// The same term built from the top down: each level's guard is allocated before the level
/// below it.
fn levels_top_down(depth: usize) -> Shared {
    let guards: Vec<Shared> = (1..=depth as i64).map(|k| Shared::new(ge(k))).collect();
    let mut s = Shared::new(ge(0));
    for g in guards {
        s = Shared::new(Term::If(g, s.clone(), s));
    }
    s
}

/// The same term with nothing shared: each branch is its own copy.
fn levels_apart(depth: usize) -> Term {
    let mut t = ge(0);
    for k in 1..=depth as i64 {
        t = Term::If(Shared::new(ge(k)), Shared::new(t.clone()), Shared::new(t));
    }
    t
}

/// Built in three allocation orders, or with every branch a copy, the term has one preimage.
#[test]
fn shared_terms_have_one_preimage_in_any_allocation_order() {
    let ds = doms(&[("i", Some(-20), Some(20))]);
    let demand = Demand::Bool(true);
    for depth in [1, 3, 6, 10] {
        let apart = shown(&preimage(&levels_apart(depth), &ds, &demand));
        for (how, t) in [
            ("bottom up", levels(depth, 0)),
            ("bottom up, spaced", levels(depth, 3)),
            ("top down", levels_top_down(depth)),
        ] {
            let p = preimage(&t, &ds, &demand);
            assert_eq!(shown(&p), apart, "depth {depth}, built {how}");
        }
    }
    assert_eq!(
        shown(&preimage(&levels(6, 0), &ds, &demand)),
        "i [0..=20]; exact"
    );
}
