//! Preimage helpers of step L1.25 (tests/steps/l01_25_preimage_catalog).

use std::sync::Arc;

use zed_kernel::{Shared, Term};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Domains, Preimage};

use super::l01_16_elaboration::{elab, with_prelude};

/// The parameters and the body of the function `ok` that `src` defines, under the
/// interpreter's prelude and the unit's other definitions.
pub fn function(src: &str) -> (Vec<Arc<str>>, Term) {
    let u = elab(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let mut t = u.get("ok").expect("a definition `ok`");
    let mut lets = Vec::new();
    while let Term::Let(n, e, b) = &t {
        lets.push((n.clone(), e.clone()));
        t = (**b).clone();
    }
    let Term::Var(k) = &t else {
        panic!("{src}: not a closed definition: {t}")
    };
    let Some(Term::Lam(ps, body)) = lets.iter().find(|(n, _)| n == k).map(|(_, e)| &**e) else {
        panic!("{src}: `{k}` is not a function")
    };
    let body = lets.iter().rev().fold((**body).clone(), |b, (n, e)| {
        Term::Let(n.clone(), e.clone(), Shared::new(b))
    });
    (ps.clone(), with_prelude(body))
}

/// The domains `name: [lo..=hi]`, `None` for an unbounded end.
pub fn doms(ds: &[(&str, Option<i64>, Option<i64>)]) -> Domains {
    ds.iter()
        .map(|&(n, lo, hi)| {
            let e = |v: Option<i64>, inf| v.map_or(inf, End::of);
            (
                n.into(),
                IntervalSet::range(e(lo, End::NegInf), e(hi, End::PosInf)),
            )
        })
        .collect()
}

/// The preimage of `true`, printed: each parameter's set, then `exact` or `necessary`, then
/// `enumerated` when it was.
pub fn shown(p: &Preimage) -> String {
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
