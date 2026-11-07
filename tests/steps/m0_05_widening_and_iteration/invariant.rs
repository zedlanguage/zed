//! A loop variable's domain holds at every iteration, not only once the ranges settle (author,
//! 2026-11-07; item RANGE-invariant-audit). The variable can take any value of its domain in
//! any iteration, so the domain must be an inductive invariant `D`: the start domain inside
//! `D`, and one step mapping `D` into `D`. A settled range used alone would let an early
//! iteration of `y' = (3 * y) div 4 + x` started at 1000 index an array of length 401 past its
//! end.
//!
//! The two phases give such a `D`: the head's equation joins the start with the step, phase 1
//! stops only at a post-fixpoint, and every narrowing of phase 2 stays between the meet with
//! the projection and the old element, so a post-fixpoint stays one (`iterate::solve`). The
//! solved landmarks `-M` and `M` of step L6.11a are written here as that step defines them,
//! `M = ceil(R / (1 - s))`, since the checker does not yet build them (loops are rejected
//! before layer L6); they are landmarks and never a domain by themselves. The bound is found
//! by the widening stopping at `M`, with no iteration per step: the number of evaluations is
//! the same at every start magnitude.

use std::sync::atomic::{AtomicU64, Ordering};

use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::iterate::{Equations, solve};
use zedc::store::landmarks::Landmarks;
use zedc::store::wto::VertexKey;

use super::{iv, name_key};

/// The loop cell `y = start ⊔ ((a * y) div b + x)`, `0 < a < b`, `x` in `int[x.0..=x.1]`.
struct Recurrence {
    a: i64,
    b: i64,
    x: (i64, i64),
    start: IntervalSet,
    /// Whether the cell has the solved landmarks `-M` and `M` of step L6.11a.
    solved: bool,
    reads: Vec<Vec<usize>>,
    names: Vec<String>,
    evals: AtomicU64,
}

impl Recurrence {
    fn new(a: i64, b: i64, x: (i64, i64), start: IntervalSet) -> Self {
        Recurrence {
            a,
            b,
            x,
            start,
            solved: true,
            reads: vec![vec![0]],
            names: vec!["y".into()],
            evals: AtomicU64::new(0),
        }
    }

    fn unsolved(self) -> Self {
        Recurrence {
            solved: false,
            ..self
        }
    }

    /// `(a * v) div b`, rounding down.
    fn scale(&self, v: &Num) -> Num {
        (&Num::from(self.a) * v).div_floor(&Num::from(self.b))
    }

    /// One step of the loop from every value of `y`: `(a * y) div b + x`. The step is monotone
    /// in `y` and in `x` and moves by at most 1 when `y` moves by 1, so the image of a piece is
    /// the piece between the images of its ends.
    fn step(&self, y: &IntervalSet) -> IntervalSet {
        y.lift1(|(lo, hi)| {
            let end = |e: &End, dx: i64| match e {
                End::Fin(v) => End::Fin(&self.scale(v) + &Num::from(dx)),
                e => e.clone(),
            };
            vec![(end(lo, self.x.0), end(hi, self.x.1))]
        })
    }

    /// `M = ceil(R / (1 - s))` of step L6.11a, with `s = a / b` and `R` the largest magnitude
    /// in `r = x + (−1, 0]`, the rounding of the `div` entering with coefficient 1.
    fn m(&self) -> i64 {
        let r = (self.x.0 - 1).abs().max(self.x.1.abs());
        (r * self.b + self.b - self.a - 1) / (self.b - self.a)
    }

    fn solve(&self) -> IntervalSet {
        solve(self).expect("one cell has one key").remove(0)
    }
}

impl Equations<IntervalSet> for Recurrence {
    type Form = ();
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn key(&self, v: usize) -> VertexKey<'_, ()> {
        name_key(&self.names, v)
    }
    fn eval(&self, _: usize, cells: &[IntervalSet]) -> IntervalSet {
        self.evals.fetch_add(1, Ordering::Relaxed);
        self.start.join(&self.step(&cells[0]))
    }
    fn landmarks(&self, _: usize) -> Landmarks {
        let mut ints = vec![self.a, self.b, self.x.0, self.x.1];
        if let Some((End::Fin(lo), End::Fin(hi))) = self.start.bounds() {
            ints.extend([lo.to_i64(), hi.to_i64()].into_iter().flatten());
        }
        if self.solved {
            ints.extend([-self.m(), self.m()]);
        }
        Landmarks::of(ints, [])
    }
}

/// Whether `d` is an inductive invariant of the loop: the start inside `d`, and one step
/// mapping `d` into `d`.
fn inductive(eq: &Recurrence, d: &IntervalSet) -> bool {
    eq.start.is_subset(d) && eq.step(d).is_subset(d)
}

/// The same, by every value of `y` in `d` and every `x`, for a finite `d`.
fn inductive_by_values(eq: &Recurrence, d: &IntervalSet) -> bool {
    let (Some(End::Fin(lo)), Some(End::Fin(hi))) = (
        d.bounds().map(|b| b.0.clone()),
        d.bounds().map(|b| b.1.clone()),
    ) else {
        return false;
    };
    let (lo, hi) = (lo.to_i64().unwrap(), hi.to_i64().unwrap());
    let start = eq.start.bounds().map(|(l, h)| (l.to_i64(), h.to_i64()));
    let starts_inside = match start {
        Some((Some(l), Some(h))) => (l..=h).all(|v| !eq.start.contains(v) || d.contains(v)),
        _ => false,
    };
    starts_inside
        && (lo..=hi).filter(|&y| d.contains(y)).all(|y| {
            let base = (eq.a * y).div_euclid(eq.b);
            (eq.x.0..=eq.x.1).all(|x| d.contains(base + x))
        })
}

/// An array of `len` items indexed by `y + offset` is accepted only when every value of the
/// domain gives an index inside it.
fn index_fits(d: &IntervalSet, offset: i64, len: i64) -> bool {
    d.is_subset(&IntervalSet::of(-offset, len - 1 - offset))
}

#[test]
fn a_start_above_the_settled_range_stays_in_the_domain() {
    // y' = (3 * y) div 4 + x, x in int[-100..=100], y starting at 1000: the ranges settle in
    // int[-404..=404], but the first iterations read 1000, then up to 850, 737, …
    let eq = Recurrence::new(3, 4, (-100, 100), IntervalSet::single(1000));
    assert_eq!(eq.m(), 404);
    let d = eq.solve();
    assert!(d.contains(1000), "the start is in the domain: {d}");
    assert!(inductive(&eq, &d), "{d} is closed under the step");
    assert!(inductive_by_values(&eq, &d), "{d}, value by value");
    // Indexing an array of length 401 by y, or of 809 by y + 404, is rejected.
    assert!(!index_fits(&d, 0, 401), "{d}");
    assert!(!index_fits(&d, 404, 809), "{d}");
    // The concrete run reads 1000 in its first iteration.
    let first = 1000;
    assert!(d.contains(first) && !IntervalSet::of(-404, 404).contains(first));
}

#[test]
fn a_start_inside_the_settled_range_gives_the_settled_range() {
    for start in [0, 1, -404, 404, 200] {
        let eq = Recurrence::new(3, 4, (-100, 100), IntervalSet::single(start));
        let d = eq.solve();
        assert!(
            d.is_subset(&IntervalSet::of(-404, 404)),
            "start {start}: {d}"
        );
        assert!(inductive_by_values(&eq, &d), "start {start}: {d}");
        assert!(index_fits(&d, 404, 809), "start {start}: {d}");
    }
}

#[test]
fn an_array_of_401_rejects_a_start_of_1000_and_accepts_a_start_inside() {
    // y' = (3 * y) div 4 + x, x in int[0..=100], settles in int[0..=400], the indices of an
    // array of length 401.
    let outside = Recurrence::new(3, 4, (0, 100), IntervalSet::single(1000));
    assert_eq!(outside.m(), 400);
    let d = outside.solve();
    assert!(d.contains(1000) && inductive_by_values(&outside, &d), "{d}");
    assert!(!index_fits(&d, 0, 401), "start 1000 is rejected: {d}");
    for start in [
        IntervalSet::single(0),
        IntervalSet::single(400),
        IntervalSet::of(0, 400),
    ] {
        let inside = Recurrence::new(3, 4, (0, 100), start.clone());
        let d = inside.solve();
        assert!(inductive_by_values(&inside, &d), "start {start}: {d}");
        assert!(index_fits(&d, 0, 401), "start {start} is accepted: {d}");
    }
    // One value past the settled range is enough to reject.
    let just = Recurrence::new(3, 4, (0, 100), IntervalSet::single(401));
    let d = just.solve();
    assert!(d.contains(401) && !index_fits(&d, 0, 401), "{d}");
}

#[test]
fn a_start_wider_than_the_settled_range_on_both_sides_is_the_domain() {
    for (a, b) in [(3, 4), (1023, 1024)] {
        let s = 1_000_000_000_000;
        let eq = Recurrence::new(a, b, (-100, 100), IntervalSet::of(-s, s));
        assert!(eq.m() < s);
        let d = eq.solve();
        assert_eq!(d, IntervalSet::of(-s, s), "{a}/{b}");
        assert!(inductive(&eq, &d), "{a}/{b}: {d}");
    }
    // Wider on one side only: the domain runs from the start's far end to the solved bound on
    // the other side.
    let eq = Recurrence::new(3, 4, (-100, 100), IntervalSet::of(-5000, 0));
    let d = eq.solve();
    assert!(
        d.contains(-5000) && d.is_subset(&IntervalSet::of(-5000, 404)),
        "{d}"
    );
    assert!(inductive_by_values(&eq, &d), "{d}");
}

#[test]
fn without_the_solved_landmarks_the_domain_is_every_integer() {
    // Until step L6.11a, no literal of the loop bounds the cell, and the widening goes to
    // infinity: sound, and the array index is rejected at every start.
    let eq = Recurrence::new(3, 4, (-100, 100), IntervalSet::single(0)).unsolved();
    let d = eq.solve();
    assert_eq!(d, iv(None, None));
    assert!(inductive(&eq, &d));
}

#[test]
fn a_slowly_settling_coefficient_is_solved_without_a_step_per_iteration() {
    // s = 1023/1024: from 10^9, a run takes about 1024 * ln(10^9 / 103424) ≈ 9400 iterations
    // to come within the settled range. The checker's evaluations are as many at every
    // magnitude (8 measured; with the widening replaced by the join they were 14710, 16839 and
    // 18967).
    let counts: Vec<u64> = [1_000_000_000_i64, 8_000_000_000, 64_000_000_000]
        .into_iter()
        .map(|start| {
            let eq = Recurrence::new(1023, 1024, (-100, 100), IntervalSet::single(start));
            assert_eq!(eq.m(), 103_424);
            let d = eq.solve();
            assert!(
                d.contains(start) && inductive(&eq, &d),
                "start {start}: {d}"
            );
            assert!(
                d.is_subset(&IntervalSet::of(-103_425, start)),
                "start {start}: {d}"
            );
            eq.evals.load(Ordering::Relaxed)
        })
        .collect();
    assert!(
        counts.iter().all(|&c| c == counts[0] && c <= 16),
        "evaluations at each magnitude: {counts:?}"
    );
    let inputs = scaling::inputs(1_000_000_000, |n| {
        Recurrence::new(1023, 1024, (-100, 100), IntervalSet::single(n as i64))
    });
    scaling::check(
        "solving y' = (1023 * y) div 1024 + x from a start of magnitude n",
        1_000_000_000,
        |n| {
            inputs[&n].solve();
        },
    );
}
