//! The join of two scopes whose relations hold many groups of constraints on names no other
//! group mentions, as the two arms of a test do when each arm checks its own records: one
//! arm narrows the first `k` groups of four names, the other the next `k`. The join's
//! relation is the disjunction of the two arms' groups, one conjunct over all their names,
//! which takes the place of the `k` groups of one side in a single block. Removing those
//! groups from that block once, and not once per constraint, keeps the join near linear in
//! `k` (COMPLEXITY.md S29).

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::product::Scope;

use super::ints;
use super::linked::{partition, partition_by_definition};

/// `Σ c·n + k >= 0` over `names`.
fn row(names: &[Arc<str>], cs: [i64; 4], k: i64) -> Term {
    let sum = names
        .iter()
        .zip(cs)
        .fold(Term::Lit(Value::Int(k)), |t, (n, c)| {
            let m = Term::Prim(
                Prim::Mul,
                vec![Term::Lit(Value::Int(c)), Term::Var(n.clone())],
            );
            Term::Prim(Prim::Add, vec![t, m])
        });
    Term::Prim(Prim::Ge, vec![sum, Term::Lit(Value::Int(0))])
}

fn all(rows: [Term; 4]) -> Term {
    rows.into_iter()
        .reduce(|a, b| Term::Prim(Prim::And, vec![a, b]))
        .expect("four rows")
}

/// A group of four constraints on four names whose integer points the solver does not
/// decide (the system of `Refusal::Growth` in tests/steps/l01_38_presburger/omega.rs).
fn refused(n: &[Arc<str>]) -> Term {
    all([
        row(n, [4, -10, -12, -12], 11),
        row(n, [10, -10, -11, 4], -28),
        row(n, [4, -1, 12, 11], -28),
        row(n, [-5, 12, -1, -8], 31),
    ])
}

/// A group of four constraints on four names that the solver decides:
/// `a + b + c + d >= 0`, `b + d + 5 >= a + c`, `a + 2 * b >= c` and `d + 3 >= a`.
fn decided(n: &[Arc<str>]) -> Term {
    all([
        row(n, [1, 1, 1, 1], 0),
        row(n, [-1, 1, -1, 1], 5),
        row(n, [1, 2, -1, 0], 0),
        row(n, [-1, 0, 0, 1], 3),
    ])
}

type Group = fn(&[Arc<str>]) -> Term;

/// The scope of `8k` integer names, `v0` to `v(8k - 1)`.
fn names(k: usize) -> Vec<Arc<str>> {
    (0..8 * k).map(|i| format!("v{i}").into()).collect()
}

/// The scope of [`names`] narrowed by `group` on the groups `range` of four names.
fn narrowed(ns: &[Arc<str>], group: Group, range: std::ops::Range<usize>) -> Scope {
    let p = Premises::new();
    ns[4 * range.start..4 * range.end]
        .chunks(4)
        .fold(ints(ns), |s, g| s.assume(&group(g), true, &p))
}

/// The two arms: one narrowed on the first `k` groups, the other on the next `k`.
fn arms(k: usize, group: Group) -> (Scope, Scope) {
    let ns = names(k);
    (narrowed(&ns, group, 0..k), narrowed(&ns, group, k..2 * k))
}

/// The states over `ns` with each name one of `values`.
fn states(ns: &[Arc<str>], values: &[i64]) -> Vec<BTreeMap<Arc<str>, Value>> {
    let width = values.len();
    let count = width.pow(ns.len() as u32);
    (0..count)
        .map(|mut i| {
            ns.iter()
                .map(|n| {
                    let v = values[i % width];
                    i /= width;
                    (n.clone(), Value::Int(v))
                })
                .collect()
        })
        .collect()
}

/// For one group on each arm, the join holds exactly the states either arm holds: neither
/// arm bounds the other's names, so the join loses nothing. Checked at every state of eight
/// names, each 0, 1 or 4 (the refused group holds at `(4, 0, 1, 0)`), by evaluating the
/// relations there, with the arms joined either way round. (Until TEST-bench-move-l0139 each
/// name also took -1: ten times the states, 3.3 s at load 30.)
#[test]
fn the_join_of_two_arms_on_disjoint_names_holds_the_states_of_either() {
    let ns = names(1);
    for group in [decided as Group, refused] {
        let (l, r) = arms(1, group);
        let (j, k) = (l.join(&r), r.join(&l));
        let (mut either, mut neither) = (0, 0);
        for s in states(&ns, &[0, 1, 4]) {
            let want = l.contains(&s) || r.contains(&s);
            assert_eq!(j.contains(&s), want, "{s:?} in {j}");
            assert_eq!(k.contains(&s), want, "{s:?} in {k}");
            either += usize::from(want);
            neither += usize::from(!want);
        }
        assert!(either > 0 && neither > 0, "{either} in, {neither} out");
    }
}

/// The join of [`the_join_of_two_arms_on_disjoint_names_holds_the_states_of_either`], reduced
/// as the benchmark `the_join_of_arms_on_many_disjoint_groups_scales` reduces it, still holds
/// exactly the states either arm holds; at 2 and 3 groups on each arm the reduced join is not
/// empty.
#[test]
fn the_reduced_join_of_two_arms_on_disjoint_names_holds_the_states_of_either() {
    let ns = names(1);
    for group in [decided as Group, refused] {
        let (l, r) = arms(1, group);
        let mut j = l.join(&r);
        j.reduce();
        for s in states(&ns, &[0, 1, 4]) {
            let want = l.contains(&s) || r.contains(&s);
            assert_eq!(j.contains(&s), want, "{s:?} in {j}");
        }
        for k in [2, 3] {
            let (l, r) = arms(k, group);
            let mut j = l.join(&r);
            j.reduce();
            assert!(!j.bottom, "{k} groups: {j}");
        }
    }
}

/// The join's relation is held in the blocks its definition gives, for joins of two arms on
/// disjoint groups and of arms that share some of their groups: the groups one arm alone
/// holds leave their block together, which the disjunction then holds.
#[test]
fn the_blocks_of_a_join_are_those_of_the_definition() {
    for group in [decided as Group, refused] {
        for k in [1, 2, 5] {
            // Room for two groups past the first `2k`.
            let ns = names(k + 1);
            let shared = narrowed(&ns, group, 0..k);
            let p = Premises::new();
            let more = |s: &Scope, i: usize| s.assume(&group(&ns[4 * i..4 * i + 4]), true, &p);
            let cases = [
                (narrowed(&ns, group, 0..k), narrowed(&ns, group, k..2 * k)),
                (more(&shared, k), more(&shared, k + 1)),
                (shared.clone(), more(&shared, k)),
            ];
            for (l, r) in cases {
                for j in [l.join(&r), r.join(&l)] {
                    assert_eq!(
                        partition(&j.relation),
                        partition_by_definition(&j.relation),
                        "k = {k}: {}",
                        j.relation
                    );
                }
            }
        }
    }
}

/// Joins at the edges: a side no state reaches, a side with no relation, one side a
/// narrowing of the other, a side joined with itself, and one group on each side.
#[test]
fn joins_of_empty_equal_and_nested_arms() {
    let ns = names(2);
    let p = Premises::new();
    let none = ints(&ns).assume(&Term::Lit(Value::Bool(false)), true, &p);
    assert!(none.bottom);
    let a = narrowed(&ns, decided, 0..2);
    let wider = narrowed(&ns, decided, 0..1);
    // A side no state reaches leaves the other as it is.
    assert_eq!(none.join(&a), a);
    assert_eq!(a.join(&none), a);
    // A side with no relation: the join has none.
    let free = ints(&ns);
    assert!(a.join(&free).relation.is_top(), "{}", a.join(&free));
    assert!(free.join(&a).relation.is_top(), "{}", free.join(&a));
    // A side joined with itself is itself.
    assert_eq!(a.join(&a), a);
    // A narrowing of the other side: the join is the wider side, for every state.
    let j = a.join(&wider);
    for s in states(&ns[..8], &[-1, 0, 1]) {
        let mut s = s;
        s.extend(ns[8..].iter().map(|n| (n.clone(), Value::Int(0))));
        assert_eq!(j.contains(&s), wider.contains(&s), "{s:?} in {j}");
    }
    // One group on each side: the disjunction of the two groups is one conjunct.
    let (l, r) = arms(1, decided);
    let j = l.join(&r);
    assert_eq!(j.relation.set().len(), 1, "{}", j.relation);
}

mod bench;
