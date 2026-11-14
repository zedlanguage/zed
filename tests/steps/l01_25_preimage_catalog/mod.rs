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

mod bench;
mod completeness;
mod constant_minus;
mod deep;
mod div0_false;
mod entries;
mod exact;
mod exact_oracle;
mod foreign_constant;
mod kept_ends;
mod overflow;
mod powers;
mod random;
mod ref_memo;
mod s22;
mod scaling;
mod scopes;
mod shared;
mod stops;
mod tonicity;
mod wide_constants;
mod wide_ends;

use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::{Term, Value, eval};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, Preimage, preimage, preimage_listed};

pub(crate) use zed_tests::step_helpers::l01_25_preimage_catalog::{doms, function, shown};

/// Each name's set of the listed integers `vs`, as the source would list them.
pub(crate) fn listed(ds: &[(&str, &[i64])]) -> Domains {
    ds.iter()
        .map(|&(n, vs)| {
            let pieces = vs.iter().map(|&v| (End::of(v), End::of(v))).collect();
            (n.into(), IntervalSet::from_pieces(pieces))
        })
        .collect()
}

/// The preimage of `demand` under `body` over `ds`, each name's set one the source lists
/// member by member ([`listed`]).
pub(crate) fn pre_listed(body: &Term, ds: &Domains, demand: &Demand) -> Preimage {
    preimage_listed(body, ds, &ds.keys().cloned().collect(), demand)
}

/// The preimage of `demand` under the function `src`, over `ds`.
fn pre(src: &str, ds: &[(&str, Option<i64>, Option<i64>)], demand: &Demand) -> Preimage {
    let (_, body) = function(src);
    preimage(&body, &doms(ds), demand)
}

/// Whether `body` meets `demand` with the inputs `names` at `point`; a failure does not.
fn meets(body: &Term, names: &[Arc<str>], point: &[i64], demand: &Demand) -> bool {
    let t = names
        .iter()
        .zip(point)
        .rev()
        .fold(body.clone(), |t, (n, &v)| {
            Term::Let(
                n.clone(),
                Shared::new(Term::Lit(Value::Int(v))),
                Shared::new(t),
            )
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

/// The seed of the random test `test` (its path in this group, as `--exact` takes it), from
/// [`zed_tests::seed::seed`]: `ZED_TEST_SEED` when it is set, else a new one each run, printed
/// (TEST-bench-move-l0125, author P169: random tests take fewer cases, a new seed each run,
/// and print it).
pub(crate) fn run_seed(test: &str) -> u64 {
    zed_tests::seed::seed(&format!("l01_25_preimage_catalog::{test}"))
}
