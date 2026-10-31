//! Phase 1's work on nested loops (COMPLEXITY.md S3). Each loop of the nest counts up to three
//! times the current upper end of the loop around it, `for j in 0..=3 * i`, and reads the loop
//! inside it, so the order nests every loop in the one around it. When each stabilization
//! restarted its head's counters, every entry of an inner loop gave its head three more joins,
//! and the work grew fourfold per level. Counted over the phase, it still grew as the square
//! of the depth, since every change of an enclosing head entered every inner loop again; a
//! loop none of whose inputs changed is now skipped, and the work is linear.

use std::cell::Cell;

use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::iterate::{Equations, dependency_graph, phase1};
use zedc::store::lattice::Landmarks;
use zedc::store::wto::{Element, weak_topological_order};

/// `depth` nested counters; cell `k` reads itself, the loop around it and the loop inside it.
struct Nest {
    reads: Vec<Vec<usize>>,
    evals: Cell<u64>,
}

impl Nest {
    fn new(depth: usize) -> Self {
        let reads = (0..depth)
            .map(|k| (k.saturating_sub(1)..(k + 2).min(depth)).collect())
            .collect();
        Nest {
            reads,
            evals: Cell::new(0),
        }
    }
}

impl Equations<IntervalSet> for Nest {
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn eval(&self, k: usize, cells: &[IntervalSet]) -> IntervalSet {
        self.evals.set(self.evals.get() + 1);
        // The bound: 3 for the outermost loop, else three times the loop around it.
        let bound = if k == 0 {
            End::Fin(3)
        } else {
            match cells[k - 1].bounds().map(|(_, hi)| hi) {
                None => return IntervalSet::empty(),
                Some(End::Fin(hi)) => End::from_i128(3 * hi as i128),
                Some(e) => e,
            }
        };
        let step = cells[k]
            .meet(&IntervalSet::range(End::NegInf, bound))
            .lift1(|(lo, hi)| vec![(lo.succ(), hi.succ())]);
        IntervalSet::single(0).join(&step)
    }
    fn landmarks(&self, _: usize) -> Landmarks {
        Landmarks::of([0, 3], [])
    }
}

fn depth_of(order: &[Element]) -> usize {
    order
        .iter()
        .map(|e| match e {
            Element::Vertex(_) => 0,
            Element::Component { body, .. } => 1 + depth_of(body),
        })
        .max()
        .unwrap_or(0)
}

fn evals(depth: usize) -> u64 {
    let eq = Nest::new(depth);
    let order = weak_topological_order(&dependency_graph(eq.reads()));
    assert_eq!(depth_of(&order), depth, "the loops nest: {order:?}");
    phase1(&eq, &order);
    eq.evals.get()
}

#[test]
fn nested_loops_cost_linear_work_in_the_depth() {
    // The evaluations per loop stay under a constant at every depth: 15 each past the first
    // (the head stops at each landmark 1 to 4 before it widens to infinity).
    for depth in 1..=48 {
        let n = evals(depth);
        assert!(n <= 16 * depth as u64, "depth {depth}: {n} evaluations");
    }
}

#[test]
fn the_nest_scales() {
    scaling::check("phase 1 on nested loops", 6, |depth| {
        evals(depth);
    });
}

/// The order of the nest: the recursive algorithm traversed each component again at every
/// level, so its cost grew as the square of the depth (COMPLEXITY.md S9).
#[test]
fn the_order_of_nested_loops_takes_time_linear_in_the_depth() {
    // A deep nest is dropped one level per stack frame.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("the weak topological order of nested loops", 1000, |d| {
                weak_topological_order(&dependency_graph(Nest::new(d).reads()));
            });
        })
        .expect("a thread")
        .join()
        .expect("the check passes");
}

/// One counter, `i = 0 ⊔ (i < 10·marks) + 1`, in a program that writes the literals 10, 20, …,
/// 10·marks.
struct Counter {
    reads: Vec<Vec<usize>>,
    marks: i64,
    evals: Cell<u64>,
}

impl Equations<IntervalSet> for Counter {
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn eval(&self, _: usize, cells: &[IntervalSet]) -> IntervalSet {
        self.evals.set(self.evals.get() + 1);
        let step = cells[0]
            .meet(&IntervalSet::range(
                End::NegInf,
                End::Fin(10 * self.marks - 1),
            ))
            .lift1(|(lo, hi)| vec![(lo.succ(), hi.succ())]);
        IntervalSet::single(0).join(&step)
    }
    fn landmarks(&self, _: usize) -> Landmarks {
        Landmarks::of((1..=self.marks).map(|k| 10 * k), [])
    }
}

#[test]
fn a_head_stops_at_most_once_per_landmark() {
    // The head may stop at each landmark below its fixpoint, so its evaluations grow linearly
    // in the landmarks under it, and not in the gaps between them (COMPLEXITY.md S13).
    for marks in [1, 2, 4, 8, 16, 32, 64, 128] {
        let eq = Counter {
            reads: vec![vec![0]],
            marks,
            evals: Cell::new(0),
        };
        let cells = phase1(&eq, &weak_topological_order(&dependency_graph(eq.reads())));
        assert_eq!(cells, vec![IntervalSet::of(0, 10 * marks)]);
        let n = eq.evals.get();
        assert!(
            n <= 3 * marks as u64 + 1,
            "{marks} landmarks: {n} evaluations"
        );
    }
}

/// A counter, `i = 0 ⊔ (i < bound) + 1`, at cell 0, beside cells 1 to `marks`, where cell `k`
/// is the literal `10·k`, below the bound.
struct Beside {
    reads: Vec<Vec<usize>>,
    bound: i64,
    evals: Cell<u64>,
}

impl Equations<IntervalSet> for Beside {
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn eval(&self, v: usize, cells: &[IntervalSet]) -> IntervalSet {
        if v > 0 {
            return IntervalSet::single(10 * v as i64);
        }
        self.evals.set(self.evals.get() + 1);
        let step = cells[0]
            .meet(&IntervalSet::range(End::NegInf, End::Fin(self.bound - 1)))
            .lift1(|(lo, hi)| vec![(lo.succ(), hi.succ())]);
        IntervalSet::single(0).join(&step)
    }
    fn landmarks(&self, v: usize) -> Landmarks {
        if v == 0 {
            Landmarks::of([0, self.bound], [])
        } else {
            Landmarks::of([10 * v as i64], [])
        }
    }
}

#[test]
fn a_head_takes_only_the_landmarks_of_its_loop() {
    // The literals outside the counter's loop are not places for its head to stop, so its
    // evaluations do not grow with them (COMPLEXITY.md S13). With every literal of the program
    // as a landmark, they grew as 3·marks + 1.
    for marks in [1, 2, 4, 8, 16, 32, 64, 128] {
        let bound = 10 * marks as i64 + 5;
        let mut reads = vec![vec![0]];
        reads.extend((0..marks).map(|_| Vec::new()));
        let eq = Beside {
            reads,
            bound,
            evals: Cell::new(0),
        };
        let cells = phase1(&eq, &weak_topological_order(&dependency_graph(eq.reads())));
        assert_eq!(cells[0], IntervalSet::of(0, bound));
        let n = eq.evals.get();
        assert!(n <= 5, "{marks} literals beside the loop: {n} evaluations");
    }
}
