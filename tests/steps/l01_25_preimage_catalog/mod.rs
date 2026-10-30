//! Step L1.25: the scalar entries of the preimage catalog, and the tonicity of the scalar
//! primitives (DESIGN.md sec:domains, "Backward transfer, and `@ensure`").
//!
//! A preimage is taken of a function's body, elaborated from Zed source, from a demand on its
//! value, over a box of parameter domains. The interpreter is the oracle: `entries` checks
//! the preimages of ordinary preconditions and guards against the points that meet them,
//! `random` checks soundness, and exactness where it is claimed, on random terms and domains,
//! `stops` checks that each term the scalar catalog does not cover is reported, `tonicity`
//! checks each claimed tonicity by running the primitive, and `scaling` checks that the
//! transfer's time grows no faster than the rule of low complexity allows.

mod entries;
mod random;
mod scaling;
mod stops;
mod tonicity;

use std::sync::Arc;

use zed_kernel::{Term, Value, eval};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, Preimage, preimage};

use crate::l01_16_elaboration::{elab, with_prelude};

/// The parameters and the body of the function `ok` that `src` defines, under the
/// interpreter's prelude and the unit's other definitions.
pub(crate) fn function(src: &str) -> (Vec<Arc<str>>, Term) {
    let u = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let mut t = u.get("ok").expect("a definition `ok`");
    let mut lets = Vec::new();
    while let Term::Let(n, e, b) = t {
        lets.push((n, e));
        t = (*b).clone();
    }
    let Term::Var(k) = t else {
        panic!("{src}: not a closed definition: {t}")
    };
    let Some(Term::Lam(ps, body)) = lets.iter().find(|(n, _)| *n == k).map(|(_, e)| &**e) else {
        panic!("{src}: `{k}` is not a function")
    };
    let body = lets.iter().rev().fold((**body).clone(), |b, (n, e)| {
        Term::Let(n.clone(), e.clone(), Arc::new(b))
    });
    (ps.clone(), with_prelude(body))
}

/// The domains `name: [lo..=hi]`, `None` for an unbounded end.
pub(crate) fn doms(ds: &[(&str, Option<i64>, Option<i64>)]) -> Domains {
    ds.iter()
        .map(|&(n, lo, hi)| {
            let e = |v: Option<i64>, inf| v.map_or(inf, End::Fin);
            (
                n.into(),
                IntervalSet::range(e(lo, End::NegInf), e(hi, End::PosInf)),
            )
        })
        .collect()
}

/// The preimage of `demand` under the function `src`, over `ds`.
fn pre(src: &str, ds: &[(&str, Option<i64>, Option<i64>)], demand: &Demand) -> Preimage {
    let (_, body) = function(src);
    preimage(&body, &doms(ds), demand)
}

/// The preimage of `true`, printed: each parameter's set, then `exact` or `necessary`, then
/// `enumerated` when it was.
pub(crate) fn shown(p: &Preimage) -> String {
    let mut out: Vec<String> = p.domains.iter().map(|(k, v)| format!("{k} {v}")).collect();
    out.push(if p.exact { "exact" } else { "necessary" }.into());
    if p.enumerated {
        out.push("enumerated".into());
    }
    for s in &p.stops {
        out.push(format!("stop: {s}"));
    }
    out.join("; ")
}

/// Whether `body` meets `demand` with the inputs `names` at `point`; a failure does not.
fn meets(body: &Term, names: &[Arc<str>], point: &[i64], demand: &Demand) -> bool {
    let t = names
        .iter()
        .zip(point)
        .rev()
        .fold(body.clone(), |t, (n, &v)| {
            Term::Let(n.clone(), Arc::new(Term::Lit(Value::Int(v))), Arc::new(t))
        });
    eval(&t).is_ok_and(|v| demand.holds(&v))
}

/// The points of the box `ds` within `window` on each axis, as values in the order of
/// `names`.
fn points(ds: &Domains, names: &[Arc<str>], window: (i64, i64)) -> Vec<Vec<i64>> {
    let mut out = vec![vec![]];
    for n in names {
        let vs: Vec<i64> = (window.0..=window.1)
            .filter(|&v| ds[n].contains(v))
            .collect();
        out = out
            .into_iter()
            .flat_map(|p| {
                vs.iter().map(move |&v| {
                    let mut p = p.clone();
                    p.push(v);
                    p
                })
            })
            .collect();
    }
    out
}

/// Checks `p` against the interpreter on the points of `ds` within `window`: every point that
/// meets the demand is in the preimage, and when it is exact, every point in it meets the
/// demand. Returns how many points met it.
fn check(body: &Term, ds: &Domains, demand: &Demand, p: &Preimage, window: (i64, i64)) -> usize {
    let names: Vec<Arc<str>> = ds.keys().cloned().collect();
    let mut met = 0;
    for pt in points(ds, &names, window) {
        let inside = names
            .iter()
            .zip(&pt)
            .all(|(n, &v)| p.domains[n].contains(v));
        if meets(body, &names, &pt, demand) {
            met += 1;
            assert!(
                inside,
                "{body} over {ds:?}: {pt:?} meets {demand:?} but is outside {}",
                shown(p)
            );
        } else if p.exact {
            assert!(
                !inside,
                "{body}: {pt:?} fails {demand:?} but is inside exact {}",
                shown(p)
            );
        }
    }
    met
}
