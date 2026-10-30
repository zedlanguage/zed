//! The equations of loops over symbolic bounds, solved with the M0.5 strategy, against the
//! values a run takes at each symbol value.

use std::collections::BTreeSet;

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::store::affine::{Affine, Bounds};
use zedc::store::interval::IntervalSet;
use zedc::store::iterate::{Equations, Strategy, solve};
use zedc::store::lattice::Lattice;

use super::{WINDOW, at, envs, random_bounds};

/// One term of a cell's transfer: `(cell[from] ⊓ guard) + step`.
#[derive(Clone, Debug)]
struct Term {
    from: usize,
    guard: Bounds,
    step: i64,
}

/// `cell[v] = init[v] ⊔ ⋃ terms[v]`: a loop's counter starts at `init` and moves by `step`
/// while `guard` holds.
#[derive(Clone, Debug)]
struct System {
    init: Vec<Bounds>,
    terms: Vec<Vec<Term>>,
    reads: Vec<Vec<usize>>,
}

impl System {
    fn new(init: Vec<Bounds>, terms: Vec<Vec<Term>>) -> Self {
        let reads = terms
            .iter()
            .map(|ts| {
                let r: BTreeSet<usize> = ts.iter().map(|t| t.from).collect();
                r.into_iter().collect()
            })
            .collect();
        System { init, terms, reads }
    }

    /// The values each cell takes in a run at `env` that stays in the window.
    fn run(&self, env: [i64; 2]) -> Vec<BTreeSet<i64>> {
        let at = at(env);
        let n = self.init.len();
        let mut cells = vec![BTreeSet::new(); n];
        loop {
            let mut changed = false;
            for v in 0..n {
                let mut next: BTreeSet<i64> =
                    WINDOW.filter(|&x| self.init[v].contains(x, &at)).collect();
                for t in &self.terms[v] {
                    for &x in &cells[t.from] {
                        let y = x + t.step;
                        if t.guard.contains(x, &at) && WINDOW.contains(&y) {
                            next.insert(y);
                        }
                    }
                }
                if next != cells[v] {
                    cells[v] = next;
                    changed = true;
                }
            }
            if !changed {
                return cells;
            }
        }
    }
}

impl Equations<Bounds> for System {
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn eval(&self, v: usize, cells: &[Bounds]) -> Bounds {
        self.terms[v].iter().fold(self.init[v].clone(), |acc, t| {
            acc.join(&cells[t.from].meet(&t.guard).offset(t.step))
        })
    }
}

fn n() -> Affine {
    Affine::sym("n")
}

fn num(c: i64) -> Bounds {
    Bounds::ints(IntervalSet::single(c))
}

/// `for i in 0..<n`: `i = 0 ⊔ (i ⊓ [..=n - 1]) + 1`, and the index the body sees,
/// `j = i ⊓ [..=n - 1]`.
fn counting_up() -> System {
    let below_n = Bounds::range(None, n().plus(-1));
    System::new(
        vec![num(0), Bounds::bottom()],
        vec![
            vec![Term {
                from: 0,
                guard: below_n.clone(),
                step: 1,
            }],
            vec![Term {
                from: 0,
                guard: below_n,
                step: 0,
            }],
        ],
    )
}

#[test]
fn a_counting_loop_keeps_its_symbolic_bound() {
    let s = counting_up();
    let cells = solve(&s, Strategy::SPEC);
    // After the loop the counter is `n`, or 0 when `n` is not positive.
    assert_eq!(cells[0].to_string(), "[0..=max(0, n)]");
    // In the body it is `int[0..<n]`.
    assert_eq!(cells[1].to_string(), "[0..=n - 1]");
}

#[test]
fn a_loop_counting_down_keeps_its_symbolic_bound() {
    // `i = n - 1; while i >= 1 { i = i - 1 }`, and the index the body sees.
    let s = System::new(
        vec![Bounds::range(n().plus(-1), n().plus(-1)), Bounds::bottom()],
        vec![
            vec![Term {
                from: 0,
                guard: Bounds::range(Some(Affine::constant(1)), None),
                step: -1,
            }],
            vec![Term {
                from: 0,
                guard: Bounds::range(Some(Affine::constant(1)), None),
                step: 0,
            }],
        ],
    );
    let cells = solve(&s, Strategy::SPEC);
    assert_eq!(cells[0].to_string(), "[min(0, n - 1)..=n - 1]");
    assert_eq!(cells[1].to_string(), "[1..=n - 1]");
}

#[test]
fn every_solution_holds_every_value_a_run_takes() {
    let mut rng = Rng::new(0x1243);
    let envs = envs();
    let mut symbolic = 0;
    for _ in 0..RANDOM_INSTANCES / 4 {
        let cells = 1 + rng.below(4);
        let init = (0..cells).map(|_| random_bounds(&mut rng)).collect();
        let terms = (0..cells)
            .map(|_| {
                (0..rng.below(3))
                    .map(|_| Term {
                        from: rng.below(cells),
                        guard: random_bounds(&mut rng),
                        step: rng.int(-2, 2),
                    })
                    .collect()
            })
            .collect();
        let s = System::new(init, terms);
        let solved = solve(&s, Strategy::SPEC);
        symbolic += solved
            .iter()
            .filter(|c| c.to_string().contains('n'))
            .count();
        for &env in &envs {
            let run = s.run(env);
            for (v, values) in run.iter().enumerate() {
                for &x in values {
                    assert!(
                        solved[v].contains(x, &at(env)),
                        "cell {v} takes {x} at {env:?}, outside {}: {s:?}",
                        solved[v]
                    );
                }
            }
        }
    }
    // The solutions keep symbolic bounds, so the check above tests them.
    assert!(symbolic > 0);
}
