//! Plan item S22-WIDE: the piecewise-affine summary of an `if` chain, and the clip of its
//! demand, on domains whose ends lie far from zero. Until S22-WIDE `Tx::fits` turned both off
//! when an end of the domain, moved by the term's literals, could pass `i64`: the summary held
//! its values in `i64` and read `i64::MIN` and `i64::MAX` as the infinite ends of a domain, so
//! a value near an end of `i64` could not be told from an infinity. The summary now holds its
//! values in `i128`, an infinite end of a piece as the limit of its line there, and reads
//! every domain whose finite ends lie in `i128`; past `i128` the `if` is read arm by arm, as
//! before S22a.
//!
//! Each preimage is checked against the interpreter, whose integers are unbounded, at the
//! points near each end of the domain, of the demand and of each guard, and against the
//! transfer before S22 (`preimage_ref`): the box lies inside the one before and is exact
//! wherever that one is.

use std::sync::Arc;
use zed_kernel::Shared;

use num_bigint::BigInt;
use zed_kernel::{Prim, Term, Value, eval};
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::preimage::{Demand, Domains, Preimage, preimage, summary_preimage};
use zedc::store::preimage_ref as before;

use super::shown;

const MAX: i64 = i64::MAX;
const MIN: i64 = i64::MIN;

fn i() -> Term {
    Term::Var("i".into())
}

fn lit(n: &Num) -> Term {
    Term::Lit(Value::from(n))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn num(n: i128) -> Num {
    Num::from(n)
}

/// `2^e + k`.
fn pow2(e: u32, k: i64) -> Num {
    &Num::from(BigInt::from(1) << e) + &Num::from(k)
}

fn fin(n: &Num) -> End {
    End::Fin(n.clone())
}

fn on(lo: End, hi: End) -> Domains {
    [(Arc::from("i"), IntervalSet::range(lo, hi))].into()
}

/// `t0 = i; tj = if i >= g + j { t(j-1) } else { t(j-1) + c }`.
fn chain(k: i64, g: &Num, c: &Num) -> Term {
    (1..=k).fold(i(), |t, j| {
        let t = Shared::new(t);
        let guard = prim(Prim::Ge, i(), lit(&(g + &Num::from(j))));
        let other = prim(Prim::Add, (*t).clone(), lit(c));
        Term::If(Shared::new(guard), t, Shared::new(other))
    })
}

/// `if i >= g { c - i } else { i }`: a reflection, its pieces' lines falling on one side.
fn reflection(g: &Num, c: &Num) -> Term {
    let guard = prim(Prim::Ge, i(), lit(g));
    let then = prim(Prim::Sub, lit(c), i());
    Term::If(Shared::new(guard), Shared::new(then), Shared::new(i()))
}

/// The demands read: `t >= 0`, and integer sets with ends at `0`, at the ends of `i64`, near
/// `2^62` and `2^70`, and unbounded.
fn demands() -> Vec<(Term, Demand)> {
    let z = |lo: End, hi: End| Demand::Ints(IntervalSet::range(lo, hi));
    vec![
        (Term::Lit(Value::Int(0)), Demand::Bool(true)),
        (i(), z(End::of(-5), End::of(5))),
        (i(), z(End::of(MAX - 3), End::PosInf)),
        (i(), z(End::NegInf, End::of(MIN + 3))),
        (i(), z(fin(&pow2(62, -2)), fin(&pow2(62, 2)))),
        (i(), z(fin(&pow2(70, 0)), End::PosInf)),
        (
            i(),
            Demand::Ints(IntervalSet::from_pieces(vec![
                (End::NegInf, End::of(-10)),
                (End::of(MAX - 1), End::from(i128::from(MAX) + 1)),
            ])),
        ),
    ]
}

/// The term `t` asked: `t >= 0` for a Boolean demand.
fn asked(t: &Term, marker: &Term, d: &Demand) -> Term {
    match d {
        Demand::Bool(_) => prim(Prim::Ge, t.clone(), marker.clone()),
        Demand::Ints(_) => t.clone(),
    }
}

/// Whether `t` at `i = v`, by the interpreter, meets `d`.
fn meets(t: &Term, v: &Num, d: &Demand) -> bool {
    let bound = Term::Let("i".into(), Shared::new(lit(v)), Shared::new(t.clone()));
    eval(&bound).is_ok_and(|x| d.holds(&x))
}

/// The points checked: within 3 of each finite end of the domain, of the demand and of `near`.
fn points(ds: &Domains, d: &Demand, near: &[Num]) -> Vec<Num> {
    let mut at: Vec<Num> = near.to_vec();
    let mut ends = |s: &IntervalSet| {
        for (lo, hi) in s.pieces() {
            for e in [lo, hi] {
                if let End::Fin(n) = e {
                    at.push(n.clone());
                }
            }
        }
    };
    ends(&ds["i"]);
    if let Demand::Ints(z) = d {
        ends(z);
    }
    let mut out: Vec<Num> = at
        .iter()
        .flat_map(|n| (-3..=3).map(move |k| n + &Num::from(k)))
        .filter(|n| ds["i"].contains_end(&End::Fin(n.clone())))
        .collect();
    out.sort();
    out.dedup();
    out
}

/// A point of [`points`] at which the interpreter refutes the box `s`: one that meets `d`
/// outside it, or, when `exact`, one inside it that fails `d`.
fn refuted(
    t: &Term,
    ds: &Domains,
    d: &Demand,
    s: &IntervalSet,
    exact: bool,
    near: &[Num],
) -> Option<String> {
    points(ds, d, near).into_iter().find_map(|v| {
        let inside = s.contains_end(&End::Fin(v.clone()));
        match (meets(t, &v, d), inside) {
            (true, false) => Some(format!("{v} meets {d:?} but is outside")),
            (false, true) if exact => Some(format!("{v} fails {d:?} but is inside")),
            _ => None,
        }
    })
}

/// Panics when the interpreter refutes `p` at a point of [`points`].
fn sound(t: &Term, ds: &Domains, d: &Demand, p: &Preimage, near: &[Num]) {
    if let Some(why) = refuted(t, ds, d, &p.domains["i"], p.exact, near) {
        panic!("{t} over {ds:?}: {why} {}", shown(p));
    }
}

fn old(d: &Demand) -> before::Demand {
    match d {
        Demand::Ints(z) => before::Demand::Ints(z.clone()),
        Demand::Bool(b) => before::Demand::Bool(*b),
    }
}

/// Whether every piece of `s` lies inside a piece of `o`.
fn inside(s: &IntervalSet, o: &IntervalSet) -> bool {
    s.pieces()
        .all(|(lo, hi)| o.pieces().any(|(l, h)| l <= lo && hi <= h))
}

/// How a preimage compares with the one before.
#[derive(PartialEq)]
enum Same {
    Equal,
    /// They differ, and the interpreter refutes the one before.
    RefutedBefore,
    /// The box lies strictly inside the one before.
    Narrower,
    /// The same box, exact now and inexact before.
    NowExact,
    /// The same exact box, found now without running each input and before by running them.
    NotEnumerated,
    Differ,
}

/// The preimage of `d` under `t` over `ds`, checked by [`sound`] and against the transfer
/// before: the box lies inside the one before, and is exact wherever that one is.
fn compared(t: &Term, ds: &Domains, d: &Demand, near: &[Num]) -> Same {
    let (now, then) = (preimage(t, ds, d), before::preimage(t, ds, &old(d)));
    sound(t, ds, d, &now, near);
    assert!(
        inside(&now.domains["i"], &then.domains["i"]),
        "{t} over {ds:?}, {d:?}: {} is not inside {:?}",
        shown(&now),
        then.domains
    );
    assert!(
        now.exact || !then.exact,
        "{t} over {ds:?}, {d:?}: {} is inexact, the one before is exact",
        shown(&now)
    );
    if format!("{now:?}") == format!("{then:?}") {
        Same::Equal
    } else if refuted(t, ds, d, &then.domains["i"], then.exact, near).is_some() {
        Same::RefutedBefore
    } else if now.domains["i"] != then.domains["i"] {
        Same::Narrower
    } else if now.exact && !then.exact {
        Same::NowExact
    } else if now.exact && then.enumerated && !now.enumerated {
        Same::NotEnumerated
    } else {
        Same::Differ
    }
}

/// Chains and reflections, their guards and constants near zero, near the ends of `i64`, near
/// `2^62` and past `i64` at `2^70`, over domains with ends at the same places and unbounded:
/// every preimage is sound, lies inside the one before and is exact wherever it is. The summary
/// and the clip now read these; the one before reads each arm by the catalog. Every preimage
/// equals the one before but for the reflections the one before got wrong, and the chains whose
/// values pass `i128`, which the summary now reads (counts held below).
#[test]
fn chains_over_wide_domains_keep_their_preimages() {
    let wide = pow2(62, 0);
    let past = pow2(70, 0);
    let (lo, hi) = (num(MIN.into()), num(MAX.into()));
    let doms = [
        on(End::of(-100), fin(&wide)),
        on(End::of(-100), End::of(MAX)),
        on(End::of(MIN), End::of(MAX)),
        on(End::of(MIN), End::of(100)),
        on(fin(&wide), fin(&past)),
        on(fin(&-&past), fin(&-&wide)),
        on(End::of(-100), End::PosInf),
        on(End::NegInf, End::PosInf),
        on(fin(&past), fin(&pow2(70, 50))),
    ];
    let guards = [
        num(0),
        &hi - &num(5),
        &lo + &num(2),
        &wide - &num(3),
        past.clone(),
    ];
    let consts = [
        num(1),
        num(-1),
        hi.clone(),
        lo.clone(),
        wide.clone(),
        past.clone(),
    ];
    let (mut cases, mut refuted_before, mut differ) = (0, Vec::new(), Vec::new());
    let (mut narrower, mut now_exact, mut not_enumerated) = (Vec::new(), Vec::new(), Vec::new());
    let mut note = |t: &Term, ds: &Domains, d: &Demand, near: &[Num]| {
        cases += 1;
        let what = format!("{t} over {ds:?}, {d:?}");
        match compared(t, ds, d, near) {
            Same::Equal => {}
            Same::RefutedBefore => refuted_before.push(what),
            Same::Narrower => narrower.push(what),
            Same::NowExact => now_exact.push(what),
            Same::NotEnumerated => not_enumerated.push(what),
            Same::Differ => differ.push(what),
        }
    };
    for ds in &doms {
        for (marker, d) in demands() {
            for g in &guards {
                let near = [g.clone(), num(0)];
                for c in &consts {
                    for k in [1, 2, 5] {
                        note(&asked(&chain(k, g, c), &marker, &d), ds, &d, &near);
                    }
                }
                for c in [num(0), num(7), wide.clone(), hi.clone()] {
                    note(&asked(&reflection(g, &c), &marker, &d), ds, &d, &near);
                }
            }
        }
    }
    drop(note);
    assert!(cases >= 2500, "only {cases} cases");
    // No box of the transfer before is refuted by the interpreter. Until item
    // S22-exact-mislabel, 25 were: `MAX - i` under a demand of two pieces on both sides of
    // zero, where the transfer before took `c - x` as the forward image of `{c} - z`, whose
    // cap merged the two pieces, and marked the merged box exact (S22b). It now marks such a
    // box exact only when `i` takes no value of the image outside the reflection of the
    // demand. The linear stage then reads the 25 inexact boxes: in 18 it finds the exact box
    // the new transfer finds, and the two are equal; in 7 its box is still wider than the new
    // one, and they count as narrower (20 before the item, then 27). Since
    // PERF-ref-memo-quadratic, whose transfer before reads guarded chains by intervals of `i`,
    // more boxes before equal the new ones: 16 count as narrower (27 before it) and 247 as now
    // exact (246 before it), and the interpreter refutes no box before.
    assert!(
        refuted_before.is_empty(),
        "the boxes before that the interpreter refutes:\n{}",
        refuted_before.join("\n")
    );
    // The summary reads values past `i128` (its numbers are unbounded), where the transfer
    // before read the `if` arm by arm: its box is the same or narrower and exact more often. Neither
    // runs each input of a range (LIST-size), so the one box the transfer before found exact by
    // running its inputs is now inexact there and counts as exact now.
    // Each is sound by the interpreter, inside the box before and exact wherever it was.
    assert_eq!(
        (narrower.len(), now_exact.len(), not_enumerated.len()),
        (16, 247, 0),
        "narrower:\n{}\nnow exact:\n{}",
        narrower[..narrower.len().min(3)].join("\n"),
        now_exact[..now_exact.len().min(3)].join("\n")
    );
    assert!(
        differ.is_empty(),
        "{} of {cases} differ from the transfer before:\n{}",
        differ.len(),
        differ[..differ.len().min(5)].join("\n")
    );
}

/// The probe over unbounded and wide domains, with the preimage written out: the infinite end
/// of the domain is the limit of the chain's line, never an input at an end of `i64`.
#[test]
fn the_probe_over_wide_domains_is_exact() {
    let k = 6;
    let probe = |ds: &Domains| {
        let t = prim(
            Prim::Ge,
            chain(k, &num(0), &num(1)),
            Term::Lit(Value::Int(0)),
        );
        preimage(&t, ds, &Demand::Bool(true))
    };
    // Below 1 every else arm is taken, `t_k = i + k`; from 1 up `t_k >= i`. So `t_k >= 0` for
    // `i >= -k`.
    let cases = [
        (
            on(End::NegInf, End::PosInf),
            IntervalSet::range(End::of(-k), End::PosInf),
        ),
        (
            on(End::of(-100), End::PosInf),
            IntervalSet::range(End::of(-k), End::PosInf),
        ),
        (on(End::of(-100), End::of(MAX)), IntervalSet::of(-k, MAX)),
        (
            on(End::of(-100), fin(&pow2(62, 0))),
            IntervalSet::range(End::of(-k), fin(&pow2(62, 0))),
        ),
        (on(End::NegInf, End::of(-k - 1)), IntervalSet::empty()),
        (
            on(fin(&pow2(70, 0)), fin(&pow2(70, 9))),
            IntervalSet::range(fin(&pow2(70, 0)), fin(&pow2(70, 9))),
        ),
    ];
    for (ds, want) in cases {
        let p = probe(&ds);
        assert!(p.exact, "{ds:?}: {}", shown(&p));
        assert!(!p.enumerated, "{ds:?}: {}", shown(&p));
        assert_eq!(p.domains["i"], want, "{ds:?}");
    }
}

/// `if i >= 0 { MAX - i } else { i }` over all integers: the then arm's line falls to minus
/// infinity, so a demand below `MIN` holds on the then arm from `i = MAX - MIN + 1` up and on
/// the else arm below `MIN`, and a demand at `MAX` only at `i = 0`.
#[test]
fn a_reflection_over_all_integers_falls_to_minus_infinity() {
    let hi = num(MAX.into());
    let t = reflection(&num(0), &hi);
    let all = on(End::NegInf, End::PosInf);
    let below = Demand::Ints(IntervalSet::range(
        End::NegInf,
        End::from(i128::from(MIN) - 1),
    ));
    let p = preimage(&t, &all, &below);
    let from = i128::from(MAX) - i128::from(MIN) + 1;
    let want = IntervalSet::from_pieces(vec![
        (End::NegInf, End::from(i128::from(MIN) - 1)),
        (End::from(from), End::PosInf),
    ]);
    assert!(p.exact, "{}", shown(&p));
    assert_eq!(p.domains["i"], want);
    sound(&t, &all, &below, &p, &[num(from), num(0)]);
    let top = Demand::Ints(IntervalSet::of(MAX, MAX));
    let p = preimage(&t, &all, &top);
    assert!(p.exact, "{}", shown(&p));
    assert_eq!(p.domains["i"], IntervalSet::of(0, 0));
}

/// `if i >= 0 { i * f * f } else { i }` with `f * f` past `i128` (`f = 2^64`), and with
/// `f * f = 2^120` over a domain where the then arm's values pass `i128`: the summary's
/// coefficients and values are unbounded integers, so it reads every case, exactly: over a finite
/// domain every input is run, and every preimage is compared with the transfer before S22.
#[test]
fn values_past_i128_are_summarized_exactly() {
    let times = |f: &Num| {
        let guard = prim(Prim::Ge, i(), Term::Lit(Value::Int(0)));
        let then = prim(Prim::Mul, prim(Prim::Mul, i(), lit(f)), lit(f));
        Term::If(Shared::new(guard), Shared::new(then), Shared::new(i()))
    };
    let cases = [
        (times(&pow2(64, 0)), Some((-50, 50))),
        (times(&pow2(60, 0)), Some((-50, 300))),
        (times(&pow2(60, 0)), None),
    ];
    let mut kinds = Vec::new();
    for (t, range) in cases {
        let ds = match range {
            Some((lo, hi)) => on(End::of(lo), End::of(hi)),
            None => on(End::NegInf, End::PosInf),
        };
        for (_, d) in demands().into_iter().skip(1) {
            let Demand::Ints(z) = &d else { unreachable!() };
            assert!(
                summary_preimage(&t, &ds, z).is_some(),
                "{t} over {ds:?}, {d:?}"
            );
            kinds.push(compared(&t, &ds, &d, &[num(0), num(256), num(257)]));
            let now = preimage(&t, &ds, &d);
            assert!(now.exact, "{t} over {ds:?}, {d:?}: {}", shown(&now));
            // Over a finite domain, every input is run.
            for v in range.into_iter().flat_map(|(lo, hi)| lo..=hi) {
                let v = num(v.into());
                assert_eq!(
                    now.domains["i"].contains_end(&End::Fin(v.clone())),
                    meets(&t, &v, &d),
                    "{t} over {ds:?}, {d:?} at {v}: {}",
                    shown(&now)
                );
            }
        }
    }
    let count = |s: Same| kinds.iter().filter(|k| **k == s).count();
    // Of the 18, the transfer before gave the same preimage in 14; in 1 the same box inexact and in
    // 3 a wider box. None differs otherwise. The third wider box is `[-50..=-10, 0..=0]` under the
    // demand `(..=-10) | (2^63-2..=2^63)`: before LIST-size the transfer before ran the input `0`
    // and dropped it, and a range is no longer run input by input (LIST-size). Since
    // PERF-ref-memo-quadratic the transfer before reads the `if` by intervals of `i` and gives
    // the same preimage in those 3 as well (17).
    assert_eq!(
        (
            count(Same::Equal),
            count(Same::NowExact),
            count(Same::Narrower),
            count(Same::NotEnumerated),
            count(Same::Differ),
        ),
        (17, 1, 0, 0, 0)
    );
}

/// The chain over a domain whose ends lie past `i128` (`2^130`): the summary gives up and the
/// `if` is read arm by arm, exactly as before S22.
#[test]
fn ends_past_i128_take_the_transfer_before() {
    let far = pow2(130, 0);
    let cases = [
        (
            chain(4, &pow2(130, 5), &num(100)),
            on(fin(&far), fin(&pow2(130, 20))),
        ),
        (chain(4, &num(0), &num(1)), on(End::of(-100), fin(&far))),
        (chain(4, &num(0), &num(1)), on(fin(&-&far), End::PosInf)),
    ];
    let z = |lo: End, hi: End| Demand::Ints(IntervalSet::range(lo, hi));
    let ds_demands = [
        z(fin(&pow2(130, 100)), fin(&pow2(130, 104))),
        z(End::of(-5), End::of(5)),
        z(fin(&far), End::PosInf),
    ];
    for (t, ds) in &cases {
        for d in &ds_demands {
            let Demand::Ints(z) = d else { unreachable!() };
            assert!(
                summary_preimage(t, ds, z).is_none(),
                "{t} over {ds:?}, {d:?}"
            );
            let (now, then) = (preimage(t, ds, d), before::preimage(t, ds, &old(d)));
            assert_eq!(
                format!("{now:?}"),
                format!("{then:?}"),
                "{t} over {ds:?}, {d:?}"
            );
            sound(t, ds, d, &now, &[num(0), pow2(130, 5)]);
        }
    }
}
