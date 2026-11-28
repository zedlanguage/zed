//! Seeded random small formulas over `x` and `y` in the box -5..=5 (PRES-conjunct-one-pass): two
//! to four rows of two terms, and one time in three a disjunction of two rows. Each such formula
//! that the propagation of `forced` does not settle passes through the three reads of its
//! top-level conjuncts in `decide_written`: `may_start` (in `forced`), `OneRow::of` and
//! `row_sums::read`. The benchmark `bench::random_conjuncts` decides the first n and 8n formulas
//! of [`SEED`] and prints their instructions, the measure the row asks for; the test here checks
//! the answers to the same formulas against every point of the box.

use std::sync::Arc;

use zed_tests::instances::Rng;
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide};

/// The fixed seed of the formulas, so every run measures the same ones.
pub(crate) const SEED: u64 = 0x5EED_0777;

const LO: i64 = -5;
const HI: i64 = 5;

/// The row `a·x + b·y + c >= 0`, or `= 0` when `eq`.
#[derive(Clone, Copy, Debug)]
struct Row {
    a: i64,
    b: i64,
    c: i64,
    eq: bool,
}

impl Row {
    /// Coefficients in -3..=3, not both zero; constant in -4..=4; an equation one time in four.
    fn random(rng: &mut Rng) -> Row {
        loop {
            let (a, b) = (rng.int(-3, 3), rng.int(-3, 3));
            if a != 0 || b != 0 {
                let c = rng.int(-4, 4);
                return Row {
                    a,
                    b,
                    c,
                    eq: rng.below(4) == 0,
                };
            }
        }
    }

    fn holds(&self, x: i64, y: i64) -> bool {
        let v = self.a * x + self.b * y + self.c;
        if self.eq { v == 0 } else { v >= 0 }
    }

    fn formula(&self) -> Formula {
        let lin = var("x")
            .times(self.a)
            .plus(&var("y").times(self.b))
            .plus(&Lin::constant(self.c));
        let zero = Lin::constant(0);
        Formula::Con(if self.eq {
            Con::eq(&lin, &zero)
        } else {
            Con::ge(&lin, &zero)
        })
    }
}

/// A random formula: the box, its rows, and, when given, two rows of which one must hold.
#[derive(Clone, Debug)]
pub(crate) struct Case {
    rows: Vec<Row>,
    or: Option<[Row; 2]>,
}

impl Case {
    fn random(rng: &mut Rng) -> Case {
        let rows = (0..2 + rng.below(3)).map(|_| Row::random(rng)).collect();
        let or = (rng.below(3) == 0).then(|| [Row::random(rng), Row::random(rng)]);
        Case { rows, or }
    }

    fn holds(&self, x: i64, y: i64) -> bool {
        self.rows.iter().all(|r| r.holds(x, y))
            && self.or.is_none_or(|[p, q]| p.holds(x, y) || q.holds(x, y))
    }

    /// Whether a point of the box holds; the formula is bounded by the box, so this is its answer.
    fn has_point(&self) -> bool {
        (LO..=HI).any(|x| (LO..=HI).any(|y| self.holds(x, y)))
    }

    pub(crate) fn formula(&self) -> Formula {
        let mut fs = Vec::new();
        for n in ["x", "y"] {
            fs.push(Formula::Con(Con::ge(&var(n), &Lin::constant(LO))));
            fs.push(Formula::Con(Con::ge(&Lin::constant(HI), &var(n))));
        }
        fs.extend(self.rows.iter().map(Row::formula));
        if let Some([p, q]) = &self.or {
            fs.push(Formula::or(vec![p.formula(), q.formula()]));
        }
        Formula::and(fs)
    }
}

/// The first `n` formulas of [`SEED`]; the first `n` of a longer list are the same.
pub(crate) fn cases(n: usize) -> Vec<Case> {
    let mut rng = Rng::new(SEED);
    (0..n).map(|_| Case::random(&mut rng)).collect()
}

fn var(n: &str) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(n)))
}

/// `decide` on the first 400 formulas of the benchmark's seed gives the answer read off the 121
/// points of the box, and both answers occur.
#[test]
fn the_families_of_the_benchmarks_are_answered_at_small_sizes() {
    let cases = cases(400);
    let mut with_point = 0;
    for (i, c) in cases.iter().enumerate() {
        let want = c.has_point();
        with_point += usize::from(want);
        assert_eq!(decide(&c.formula()), Ok(want), "case {i}: {c:?}");
    }
    eprintln!("random conjuncts: {with_point} of 400 have a point");
    assert!(
        with_point > 0 && with_point < cases.len(),
        "{with_point} of 400 have a point"
    );
}
