//! Cases of different classes joined (row LIMITS-classed-listing-per-set): a name narrowed by a
//! disjunction of cases `lo <= x <= hi && x mod m == r`, or by each case in an arm of its own
//! and the arms' scopes joined (`Scope::join`), holds exactly the values some case holds, read
//! value by value (`Product::contains`) against a brute force over a box. The join keeps the
//! cases' classes as one set per class (`ProductDomains::classes`, a
//! `zedc_lattice::class_union::ClassUnion`) where the congruence domain alone joins them to a
//! wider class, so no value is listed.
//!
//! A case's set was listed up to about 134,800 values before this row
//! (`presburger::listed_within_limit`, since removed), so at the small sizes here every set was
//! listed and the answers were exact on origin/main at 7351ba062 too: this is an oracle check
//! that the join per class changes no answer. Its red case is the same kind of cases past that
//! limit, `scope_relations::lazy::three_cases_whose_classes_join_wide_past_the_old_listing_limit`.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::instances::Rng;
use zedc::store::cell::Premises;
use zedc::store::product::Scope;

use super::ints;

/// Values asked lie in `-W..=W`; every case drawn lies well inside.
const W: i64 = 40;

fn var() -> Term {
    Term::Var(Arc::from("x"))
}

fn int(v: i64) -> Term {
    Term::Lit(Value::Int(v))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn and(a: Term, b: Term) -> Term {
    prim(Prim::And, a, b)
}

fn or(a: Term, b: Term) -> Term {
    prim(Prim::Or, a, b)
}

/// One case: `lo <= x <= hi`, `x mod m == r`.
#[derive(Clone, Copy, Debug)]
struct Case {
    lo: i64,
    hi: i64,
    m: i64,
    r: i64,
}

impl Case {
    fn draw(rng: &mut Rng) -> Case {
        let m = rng.int(1, 6);
        let lo = rng.int(-30, 30);
        Case {
            lo,
            hi: lo + rng.int(0, 20),
            m,
            r: rng.int(0, m - 1),
        }
    }

    fn holds(&self, v: i64) -> bool {
        (self.lo..=self.hi).contains(&v) && v.rem_euclid(self.m) == self.r
    }

    fn test(&self) -> Term {
        let range = and(
            prim(Prim::Ge, var(), int(self.lo)),
            prim(Prim::Le, var(), int(self.hi)),
        );
        let class = prim(Prim::Eq, prim(Prim::Mod, var(), int(self.m)), int(self.r));
        and(range, class)
    }
}

/// The values of `x` the scope holds in `-W..=W`.
fn held(s: &Scope) -> BTreeSet<i64> {
    let x = s.settled(&Arc::from("x"));
    (-W..=W).filter(|v| x.contains(&Value::Int(*v))).collect()
}

/// 600 random sets of one to four cases, each as one disjunction (eager and lazy) and as the
/// join of one arm a case, against the values some case holds.
#[test]
fn joined_cases_of_different_classes_hold_exactly_their_values() {
    let (mut rng, seed) = Rng::fresh("joined_cases_of_different_classes_hold_exactly_their_values");
    let p = Premises::new();
    let names: [Arc<str>; 1] = [Arc::from("x")];
    for round in 0..600 {
        let cases: Vec<Case> = (0..rng.int(1, 4)).map(|_| Case::draw(&mut rng)).collect();
        let want: BTreeSet<i64> = (-W..=W)
            .filter(|v| cases.iter().any(|c| c.holds(*v)))
            .collect();
        let what = format!("seed {seed}, round {round}: {cases:?}");
        let test = (cases.iter().map(Case::test))
            .reduce(or)
            .expect("one case at least");
        for lazy in [false, true] {
            let s = ints(&names);
            let s = if lazy { s.lazy() } else { s };
            let got = held(&s.assume(&test, true, &p));
            assert_eq!(got, want, "{what}, one disjunction, lazy {lazy}");
        }
        let s = ints(&names);
        let joined = (cases.iter().map(|c| s.assume(&c.test(), true, &p)))
            .reduce(|a, b| a.join(&b))
            .expect("one case at least");
        assert_eq!(held(&joined), want, "{what}, arms joined");
    }
}
