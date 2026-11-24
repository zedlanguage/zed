//! Strided sets in the exact projection (row PERF-exact-strided-unlisted): a hub `w = a + b` of
//! two names in boxes `0..=r`, held to a residue class by a row `w == m*t`, with a disjunction
//! that sends the projection to the cover of module `exact`. The set of `w` is the class within
//! `0..=2r`; its cost must not grow with `r` (the benchmark in `bench::strided`).

use zedc::store::classed::Classed;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::Congruence;
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, Shared, project_each_boxed, project_each_boxed_classed,
    project_each_classed,
};

fn sym(n: &str) -> Lin {
    Lin::atom(Atom::Sym(n.into()))
}

fn ge(l: Lin, c: i64) -> Formula {
    Formula::Con(Con::ge(&l, &Lin::constant(c)))
}

fn le(l: Lin, c: i64) -> Formula {
    ge(l.times(-1), -c)
}

/// `0 <= a, b <= r && (a <= 2 || b >= 8) && a + b == w && w == m*t`, and the names asked,
/// `a`, `b` and `w`. With `r >= 7 + m` every `a` and `b` in `0..=r` has a point (the other
/// name one of the `m` values `8..=7 + m`, which meet every residue modulo `m`), and `w` takes
/// every multiple of `m` in `0..=2r`. Below that the sets have holes: at `r = 9`, `m = 3`,
/// `a = 5` needs `b` in `{8, 9}`, and neither `13` nor `14` is a multiple of 3.
pub(crate) fn hub(r: i64, m: i64) -> (Formula, Vec<Atom>) {
    let w = sym("a").plus(&sym("b")).plus(&sym("w").times(-1));
    let t = sym("w").plus(&sym("t").times(-m));
    let f = Formula::And(Shared::new(vec![
        ge(sym("a"), 0),
        le(sym("a"), r),
        ge(sym("b"), 0),
        le(sym("b"), r),
        Formula::Or(Shared::new(vec![le(sym("a"), 2), ge(sym("b"), 8)])),
        Formula::Con(Con::eq(&w, &Lin::constant(0))),
        Formula::Con(Con::eq(&t, &Lin::constant(0))),
    ]));
    (f, ["a", "b", "w"].map(|n| Atom::Sym(n.into())).into())
}

/// The answer of [`hub`] checked: `a` and `b` are `0..=r`, `w` the multiples of `m` in
/// `0..=2r`, kept as one class, not listed value by value.
pub(crate) fn check_hub(r: i64, m: i64) {
    let (f, syms) = hub(r, m);
    let got = project_each_classed(&f, &syms).expect("answered");
    let range = |lo: i64, hi: i64| IntervalSet::range(End::from(lo), End::from(hi));
    for (i, s) in got.sets.iter().enumerate().take(2) {
        let s = s.as_ref().expect("a and b answered");
        assert_eq!(s.met(), range(0, r), "name {i} at r = {r}, m = {m}");
    }
    let w = got.sets[2].as_ref().expect("w answered");
    let (modulus, residue) = w.strided().expect("w is one class");
    assert_eq!(
        (format!("{modulus}"), format!("{residue}")),
        (format!("{m}"), "0".to_string()),
        "the class of w at r = {r}"
    );
    let top = 2 * r - (2 * r).rem_euclid(m);
    assert_eq!(
        w.ranges,
        range(0, top),
        "the range of w at r = {r}, m = {m}"
    );
    assert!(got.causes.is_empty(), "exact at r = {r}: {:?}", got.causes);
}

/// The hub at moduli 2 and 3, against the answer read off by hand ([`check_hub`]). Red before
/// green at `r = 100_000`: with each value of `w` listed, its cover read 8,377,793 units and
/// was refused (2026-11-23, the branch point of PERF-exact-strided-unlisted).
#[test]
fn a_hub_held_to_a_class_projects_to_the_class() {
    for m in [2, 3] {
        for r in [10, 11, 100, 1000, 100_000] {
            check_hub(r, m);
        }
    }
}

/// The answer of [`hub`] as `project_each_boxed_classed` gives it, checked: `a` and `b` are
/// `0..=r`; `w` is the multiples of `m` in `0..=2r`, kept as the range `0` to the last multiple
/// met with the class `0 mod m`, with no value listed, whatever their count; no cause and
/// nothing refused. The same set as `project_each_boxed` lists value by value.
pub(crate) fn check_boxed_hub(r: i64, m: i64) {
    let (f, syms) = hub(r, m);
    let got = project_each_boxed_classed(&f, &syms);
    let range = |lo: i64, hi: i64| IntervalSet::range(End::from(lo), End::from(hi));
    let top = 2 * r - (2 * r).rem_euclid(m);
    assert_eq!(
        got.each,
        vec![
            (Classed::plain(range(0, r)), None),
            (Classed::plain(range(0, r)), None),
            (Classed::new(range(0, top), Congruence::new(m, 0)), None)
        ],
        "the sets at r = {r}, m = {m}"
    );
    assert_eq!(
        (got.skipped, got.whole),
        (Vec::new(), None),
        "r = {r}, m = {m}"
    );
    if r <= 1000 {
        let listed = project_each_boxed(&f, &syms).each;
        let classed = got.each.iter().map(|(s, c)| (s.met(), c.clone()));
        assert!(classed.eq(listed), "listed at r = {r}, m = {m}");
    }
}

/// The hub at moduli 2 and 3 as one class for `w` (PERF-exact-strided-unlisted,
/// DOMAINS-classed-sets), the box that `preimage::boxed_projections` gives where
/// `project_each_boxed` listed each multiple. Red before green: on the branch point,
/// `project_each_boxed` gives `w` one range per multiple, `0..=0, m..=m, ...`; at option (a)
/// (3480ade74), `w` past the formula's size is the range `0..=top` alone, not exact.
#[test]
fn a_boxed_class_keeps_its_class_unlisted() {
    for m in [2, 3] {
        for r in [10, 11, 100, 1000, 100_000] {
            check_boxed_hub(r, m);
        }
    }
}
