//! Coupled subset-sum, multi-row laminar, forced-implication chain, and `I18` witness
//! alignment scaling and soundness tests (PRES-disj-cost-xr, round 4).
//!
//! Every scaling check runs at `n = 64` and `8n = 512` (or `16` and `128` for the pre-density
//! immune subset-sum gap) under `scaling::check_order(..., 1, ...)`, holding both instruction
//! count and heap allocation within `1.1 * 8 * log(8n) / log(n)`. A negative control is a
//! temporary build with the summaries or the batched searches taken out, run once and not
//! committed.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, Refusal, Shared, decide, project_each, satisfiable,
};

pub(super) fn sym(s: &str) -> Atom {
    Atom::Sym(Arc::from(s))
}

fn lin(terms: &[(&str, i64)], k: i64) -> Lin {
    let mut out = Lin::constant(i128::from(k));
    for (name, c) in terms {
        out = out.plus(&Lin::atom(sym(name)).times(i128::from(*c)));
    }
    out
}

fn ge(terms: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::ge(&lin(terms, k), &Lin::constant(0)))
}

fn eq(terms: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::eq(&lin(terms, k), &Lin::constant(0)))
}

pub(super) fn pt_set(vals: &[i64]) -> IntervalSet {
    let mut out = IntervalSet::empty();
    for &x in vals {
        let p = IntervalSet::range(End::Fin(Num::from(x)), End::Fin(Num::from(x)));
        out = out.join(&p);
    }
    out
}

pub(super) fn weights(k: usize) -> Vec<i64> {
    (0..k)
        .map(|i| 1000 + 37 * (i as i64) * (i as i64) % 991)
        .collect()
}

/// Tie-free weights up to `k = 1026`: prime `2053 > 1022 + 1023`, so `i^2 != j^2 (mod 2053)`
/// for all `0 <= i < j <= 1026`, while keeping `w_i in [3000, 5052]` (`max_w < 2 * min_w`).
pub(super) fn weights_untied(k: usize) -> Vec<i64> {
    (0..k)
        .map(|i| 3000 + 37 * (i as i64) * (i as i64) % 2053)
        .collect()
}

pub(super) fn choice_sum(w: &[i64], t: i64) -> Formula {
    let names: Vec<String> = (0..w.len()).map(|i| format!("y{i}")).collect();
    let mut fs: Vec<Formula> = names
        .iter()
        .zip(w)
        .map(|(n, &wi)| Formula::or(vec![eq(&[(n, 1)], 0), eq(&[(n, 1)], -wi)]))
        .collect();
    let terms: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), 1)).collect();
    fs.push(eq(&terms, -t));
    Formula::and(fs)
}

pub(super) fn subset_sum_dp(w: &[i64]) -> Formula {
    let total: usize = w.iter().map(|&x| x as usize).sum();
    let len = total + 1;
    let words = len.div_ceil(64);
    let mut dp = vec![0u64; words];
    dp[0] = 1;
    let mut max_s = 0usize;
    for &x in w {
        let shift = x as usize;
        let word_shift = shift / 64;
        let bit_shift = shift % 64;
        let top_word = (max_s + shift) / 64;
        if bit_shift == 0 {
            for wi in (word_shift..=top_word).rev() {
                dp[wi] |= dp[wi - word_shift];
            }
        } else {
            for wi in (word_shift..=top_word).rev() {
                let mut v = dp[wi - word_shift] << bit_shift;
                if wi > word_shift {
                    v |= dp[wi - word_shift - 1] >> (64 - bit_shift);
                }
                dp[wi] |= v;
            }
        }
        max_s += shift;
    }
    let half = len / 2;
    let t = (half..len)
        .find(|&s| (dp[s / 64] >> (s % 64)) & 1 == 0)
        .expect("an unreachable target") as i64;
    choice_sum(w, t)
}

pub(super) fn build_two_rows(w: &[i64]) -> Formula {
    let k = w.len();
    let names: Vec<String> = (0..k).map(|i| format!("y{i}")).collect();
    let mut fs: Vec<Formula> = names
        .iter()
        .zip(w)
        .map(|(n, &wi)| Formula::or(vec![eq(&[(n, 1)], 0), eq(&[(n, 1)], -wi)]))
        .collect();
    let t1: i64 = w.iter().step_by(2).sum();
    let t2: i64 = (k / 2..k).filter(|i| i % 2 == 0).map(|i| w[i]).sum();
    let all: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), 1)).collect();
    fs.push(eq(&all, -t1));
    fs.push(eq(&all[k / 2..], -t2));
    Formula::and(fs)
}

pub(super) fn build_paired_chain(k: usize) -> Formula {
    let mut fs = vec![eq(&[("y0", 1)], -1), eq(&[(&format!("y{k}"), 1)], 0)];
    for i in 0..k {
        let (a, b) = (format!("y{i}"), format!("y{}", i + 1));
        fs.push(Formula::or(vec![
            Formula::and(vec![eq(&[(&a, 1)], 0), eq(&[(&b, 1)], 0)]),
            Formula::and(vec![eq(&[(&a, 1)], -1), eq(&[(&b, 1)], -1)]),
        ]));
    }
    Formula::and(fs)
}

pub(super) fn build_alternating(k: usize) -> Formula {
    let w: Vec<i64> = (0..k)
        .map(|i| if i % 2 == 0 { 1 } else { 100_000 })
        .collect();
    let t: i64 = (k as i64 / 2) * 100_000 + (k as i64 / 4).max(1);
    choice_sum(&w, t)
}

pub(super) fn build_dense(k: usize) -> Formula {
    let names: Vec<String> = (0..k).map(|i| format!("y{i}")).collect();
    let mut fs = Vec::new();
    let mut s = 0i64;
    for (i, n) in names.iter().enumerate() {
        let hi = 1000 + i as i64;
        fs.push(ge(&[(n, 1)], 0));
        fs.push(ge(&[(n, -1)], hi));
        s += hi;
    }
    let terms: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), 1)).collect();
    fs.push(eq(&terms, -(s / 2)));
    Formula::and(fs)
}

fn collect_atoms(f: &Formula, out: &mut BTreeSet<Atom>) {
    match f {
        Formula::Con(c) => {
            for a in c.lin.terms.keys() {
                out.insert(a.clone());
            }
        }
        Formula::Not(inner) => collect_atoms(inner, out),
        Formula::And(fs) | Formula::Or(fs) => {
            for sub in fs.iter() {
                collect_atoms(sub, out);
            }
        }
    }
}

fn rename_formula(f: &Formula, map: &BTreeMap<Atom, Atom>) -> Formula {
    match f {
        Formula::Con(c) => {
            let mut l = Lin {
                constant: c.lin.constant.clone(),
                ..Lin::default()
            };
            for (a, coeff) in &c.lin.terms {
                let na = map.get(a).cloned().unwrap_or_else(|| a.clone());
                l.terms.insert(na, coeff.clone());
            }
            Formula::Con(Con { lin: l, rel: c.rel })
        }
        Formula::Not(inner) => Formula::Not(Shared::new(rename_formula(inner, map))),
        Formula::And(fs) => Formula::and(fs.iter().map(|s| rename_formula(s, map)).collect()),
        Formula::Or(fs) => Formula::or(fs.iter().map(|s| rename_formula(s, map)).collect()),
    }
}

pub(super) fn reverse_renamed(f: &Formula, keep: &Atom) -> (Formula, Atom) {
    let mut atoms = BTreeSet::new();
    collect_atoms(f, &mut atoms);
    let sorted: Vec<Atom> = atoms.into_iter().collect();
    let n = sorted.len();
    let map: BTreeMap<Atom, Atom> = sorted
        .into_iter()
        .enumerate()
        .map(|(idx, a)| (a, sym(&format!("r{:04}", n - 1 - idx))))
        .collect();
    let nk = map.get(keep).cloned().unwrap_or_else(|| keep.clone());
    (rename_formula(f, &map), nk)
}

fn same_refusal_kind<T: PartialEq>(a: &Result<T, Refusal>, b: &Result<T, Refusal>) -> bool {
    match (a, b) {
        (Ok(x), Ok(y)) => x == y,
        (Err(Refusal::Disjuncts), Err(Refusal::Disjuncts))
        | (Err(Refusal::Growth), Err(Refusal::Growth))
        | (Err(Refusal::Shadows), Err(Refusal::Shadows))
        | (Err(Refusal::Tie(_)), Err(Refusal::Tie(_)))
        | (Err(Refusal::Unordered(_)), Err(Refusal::Unordered(_))) => true,
        _ => false,
    }
}

#[test]
fn i18_decide_matches_satisfiable() {
    struct Rng(u64);
    impl Rng {
        fn next(&mut self, bound: u64) -> i64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            ((self.0 >> 33) % bound) as i64
        }
    }
    let targets: BTreeSet<u64> = [
        78, 91, 399, 590, 646, 918, 1093, 1312, 1711, 1911, 2156, 2473,
    ]
    .into_iter()
    .collect();
    let max_case = *targets.iter().next_back().expect("non-empty");
    let mut rng = Rng(777);
    let mut checked = 0usize;
    for case in 0..=max_case {
        let k = 3 + rng.next(5) as usize;
        let names: Vec<String> = (0..k).map(|i| format!("y{i}")).collect();
        let mut fs = Vec::new();
        let mut doms: Vec<Vec<i64>> = Vec::new();
        for nm in &names {
            let a = if rng.next(3) == 0 { rng.next(6) } else { 0 };
            let b = a + 1 + rng.next(30);
            let mut dom = BTreeSet::new();
            let second = if rng.next(6) == 0 {
                let c = b + rng.next(3);
                dom.extend(b..=c);
                Formula::and(vec![ge(&[(nm, 1)], -b), ge(&[(nm, -1)], c)])
            } else {
                dom.insert(b);
                eq(&[(nm, 1)], -b)
            };
            dom.insert(a);
            fs.push(Formula::or(vec![eq(&[(nm, 1)], -a), second]));
            doms.push(dom.into_iter().collect());
        }
        let nrows = 1 + (rng.next(4) == 0) as u64;
        for r in 0..nrows {
            let cs: Vec<i64> = (0..k)
                .map(|_| [1, 1, 1, 1, 1, -1, 2][rng.next(7) as usize])
                .collect();
            let is_eq = r == 0 || rng.next(2) == 0;
            let t = if rng.next(2) == 0 {
                (0..k)
                    .map(|i| cs[i] * doms[i][rng.next(doms[i].len() as u64) as usize])
                    .sum()
            } else {
                let hi: i64 = (0..k)
                    .map(|i| cs[i].abs() * doms[i][doms[i].len() - 1])
                    .sum();
                rng.next(hi.max(1) as u64 + 1)
            };
            let terms: Vec<(&str, i64)> = names
                .iter()
                .zip(&cs)
                .map(|(n, c)| (n.as_str(), *c))
                .collect();
            fs.push(if is_eq {
                eq(&terms, -t)
            } else {
                ge(&terms, -t)
            });
        }
        if !targets.contains(&case) {
            continue;
        }
        let f = Formula::and(fs);
        let d = decide(&f);
        let s = satisfiable(&f);
        assert_eq!(d, Ok(true), "I18 case {case}: decide gave {d:?}");
        let m = s
            .unwrap_or_else(|e| panic!("I18 case {case}: satisfiable refused {e:?}"))
            .unwrap_or_else(|| panic!("I18 case {case}: satisfiable returned None"));
        assert!(f.holds(&m), "I18 case {case}: witness {m:?} does not hold");
        checked += 1;
    }
    assert_eq!(checked, 12);

    // Reverse-renaming determinism on tied and untied families; the untied ones at k = 16,
    // since their projections are not near linear in k (`ss_untied` over 60 s at k = 256).
    let y0 = sym("y0");
    for (label, f) in [
        ("ss_512", subset_sum_dp(&weights(512))),
        ("ss_untied_16", subset_sum_dp(&weights_untied(16))),
        ("two_rows_untied_16", build_two_rows(&weights_untied(16))),
        ("paired_chain_512", build_paired_chain(512)),
    ] {
        let (rf, ry0) = reverse_renamed(&f, &y0);
        assert!(
            same_refusal_kind(&decide(&f), &decide(&rf)),
            "{label}: decide changed under reverse renaming"
        );
        let (p1, _) = project_each(&f, std::slice::from_ref(&y0)).expect(label);
        let (p2, _) = project_each(&rf, &[ry0]).expect(label);
        assert_eq!(
            p1[0], p2[0],
            "{label}: project_each changed under reverse renaming"
        );
    }
}

/// `points` case 31 of the random harness: weights 799..=817 by 3, target 2412 = 799 + 805 +
/// 808. The slack probes alone miss this point; halving the probe rounds twice finds it.
#[test]
fn small_subset_sums_are_found_with_the_slack_probes() {
    let w: Vec<i64> = (0..7).map(|i| 799 + 3 * i).collect();
    assert_eq!(decide(&choice_sum(&w, 2412)), Ok(true));
}

/// `k/2` rows `y_{2r} + y_{2r+1} = w_{2r}` over two-point atoms, with one inequality over every
/// atom.
pub(super) fn build_many_linked(k: usize) -> Formula {
    let w = weights(k);
    let names: Vec<String> = (0..k).map(|i| format!("y{i}")).collect();
    let mut fs: Vec<Formula> = names
        .iter()
        .zip(&w)
        .map(|(n, &wi)| Formula::or(vec![eq(&[(n, 1)], 0), eq(&[(n, 1)], -wi)]))
        .collect();
    for r in 0..k / 2 {
        fs.push(eq(&[(&names[2 * r], 1), (&names[2 * r + 1], 1)], -w[2 * r]));
    }
    let all: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), -1)).collect();
    fs.push(ge(&all, w.iter().sum::<i64>() - 1));
    Formula::and(fs)
}
