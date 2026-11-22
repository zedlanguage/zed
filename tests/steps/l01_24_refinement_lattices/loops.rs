//! The equations of loops over symbolic bounds, solved with the M0.5 strategy, against the
//! values a run takes at each symbol value.

use std::collections::BTreeSet;

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::address::ContentAddress;
use zedc::lex::Span;
use zedc::store::affine::{Affine, Bounds};
use zedc::store::interval::End;
use zedc::store::interval::IntervalSet;
use zedc::store::iterate::{Equations, solve};
use zedc::store::landmarks::Landmarks;
use zedc::store::lattice::Lattice;
use zedc::store::wto::VertexKey;

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
pub(super) struct System {
    init: Vec<Bounds>,
    terms: Vec<Vec<Term>>,
    reads: Vec<Vec<usize>>,
    /// Cell `v` is named `c{v}`; the names alone order the traversal.
    names: Vec<String>,
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
        let names = (0..init.len()).map(|v| format!("c{v}")).collect();
        System {
            init,
            terms,
            reads,
            names,
        }
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
    type Form = ();
    type Keypath = ();
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn key(&self, v: usize) -> VertexKey<'_, (), ()> {
        VertexKey {
            name: &self.names[v],
            address: ContentAddress([0; 32]),
            form: &(),
            keypath: &(),
        }
    }
    /// The systems here are built, not read from source, so no cell has a place in a text.
    fn span(&self, _: usize) -> Span {
        Span { start: 0, end: 0 }
    }
    fn eval(&self, v: usize, cells: &[Bounds]) -> Bounds {
        self.terms[v].iter().fold(self.init[v].clone(), |acc, t| {
            acc.join(&cells[t.from].meet(&t.guard).offset(t.step))
        })
    }
    /// The integer ends of cell `v`'s initial value and guards.
    fn landmarks(&self, v: usize) -> Landmarks {
        let bounds = [&self.init[v]]
            .into_iter()
            .chain(self.terms[v].iter().map(|t| &t.guard));
        let ends = bounds.flat_map(|b| b.concrete().pieces().flat_map(|(lo, hi)| [lo, hi]));
        Landmarks::of(
            ends.filter_map(|e| match e {
                End::Fin(v) => Some(v.clone()),
                _ => None,
            }),
            [],
        )
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
    let below_n = Bounds::range(None, Some(n().plus(-1)));
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
    let cells = solve(&s).unwrap();
    // After the loop the counter is `n`, or 0 when `n` is not positive.
    assert_eq!(cells[0].to_string(), "[0..=max(0, n)]");
    // In the body it is `int[0..<n]`.
    assert_eq!(cells[1].to_string(), "[0..=n - 1]");
}

#[test]
fn a_loop_counting_down_keeps_its_symbolic_bound() {
    // `i = n - 1; while i >= 1 { i = i - 1 }`, and the index the body sees.
    let s = System::new(
        vec![
            Bounds::range(Some(n().plus(-1)), Some(n().plus(-1))),
            Bounds::bottom(),
        ],
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
    let cells = solve(&s).unwrap();
    assert_eq!(cells[0].to_string(), "[min(0, n - 1)..=n - 1]");
    assert_eq!(cells[1].to_string(), "[1..=n - 1]");
}

/// Row L1.39-head-rule: `i = 0; while i <= n - 1 && i <= s0 - 1 && i <= s2 - 1 && … { i = i +
/// 1 }`, with `i <= s_j` for each `j < k` as the loop's entry relation, `k` candidate conjuncts
/// over `k` symbols. The guard keeps `i <= s_j - 1` for each even `j`, so the step `i + 1`
/// preserves the candidate `i <= s_j` exactly for even `j`, and refutes it for odd `j` (from
/// `i <= s_j` alone, `i + 1 <= s_j + 1`, and no other candidate names `s_j`). So the largest
/// inductive subset of the candidates, the greatest fixpoint of Houdini (Flanagan and Leino,
/// FME 2001, doi:10.1007/3-540-45251-6_29), is `{i <= s_j : j even}`.
pub(super) fn houdini_loop(k: usize) -> System {
    let s = |j: usize| Affine::sym(&format!("s{j}"));
    let entry = Bounds::new(IntervalSet::single(0), [], (0..k).map(s));
    let guard = Bounds::new(
        IntervalSet::top(),
        [],
        std::iter::once(n().plus(-1)).chain((0..k).step_by(2).map(|j| s(j).plus(-1))),
    );
    System::new(
        vec![entry],
        vec![vec![Term {
            from: 0,
            guard,
            step: 1,
        }]],
    )
}

/// The symbols of the upper bounds of `b`, one name for each bound.
pub(super) fn upper_symbols(b: &Bounds) -> Vec<String> {
    let names = b.bounds(zedc::store::affine::Side::Upper).iter().map(|u| {
        let names: Vec<&str> = u.affine.terms.keys().map(|s| s.0.as_str()).collect();
        names.join("+")
    });
    names.collect()
}

/// The head of a loop keeps the largest inductive subset of the conjuncts of its entry
/// relation, the rule of step M0.5 (row L1.39-head-rule, DESIGN.md sec:domains, "At a widening
/// point a linear relation forms no disjunction"):
/// after the first phase the head of `houdini_loop(k)` holds `i <= s_j` for each even `j` and
/// no other symbolic bound, and narrowing adds none, since the side already has bounds. A
/// second case with the test symbols `n` and `m` is checked against the values a run takes:
/// `i = 0; while i <= n - 1 { i = i + 1 }` entered with `i <= n` and `i <= m` keeps `i <= n`,
/// which the guard re-establishes, and drops `i <= m`, which the step refutes.
#[test]
fn a_loop_head_keeps_the_largest_inductive_subset_of_its_entry_conjuncts() {
    use zedc::store::iterate::{order, phase1};
    for k in [1, 2, 5, 6] {
        let s = houdini_loop(k);
        let even: Vec<String> = (0..k).step_by(2).map(|j| format!("s{j}")).collect();
        let head = &phase1(&s, &order(&s).unwrap())[0];
        assert_eq!(upper_symbols(head), even, "k = {k}: {head}");
        let solved = &solve(&s).unwrap()[0];
        assert_eq!(upper_symbols(solved), even, "k = {k}: {solved}");
    }
    let m = Affine::sym("m");
    let s = System::new(
        vec![Bounds::new(IntervalSet::single(0), [], [n(), m])],
        vec![vec![Term {
            from: 0,
            guard: Bounds::range(None, Some(n().plus(-1))),
            step: 1,
        }]],
    );
    let solved = &solve(&s).unwrap()[0];
    assert_eq!(upper_symbols(solved), ["n"], "{solved}");
    for env in envs() {
        for x in &s.run(env)[0] {
            assert!(
                solved.contains(*x, &at(env)),
                "{x} at {env:?} outside {solved}"
            );
        }
    }
}

#[test]
fn every_solution_holds_every_value_a_run_takes() {
    let (mut rng, seed) = Rng::fresh("loop systems over symbolic bounds");
    let envs = envs();
    let holds_run = |s: &System| {
        let solved = solve(s).unwrap_or_else(|e| panic!("{s:?}: {e:?}, ZED_TEST_SEED={seed}"));
        for &env in &envs {
            let run = s.run(env);
            for (v, values) in run.iter().enumerate() {
                for &x in values {
                    assert!(
                        solved[v].contains(x, &at(env)),
                        "cell {v} takes {x} at {env:?}, outside {}: {s:?}, ZED_TEST_SEED={seed}",
                        solved[v]
                    );
                }
            }
        }
        solved
    };
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
        holds_run(&System::new(init, terms));
    }
    // A solution with a symbolic bound, so the check above tests one whatever the draws gave:
    // the loop counting from 0 while below `n` ends at `max(0, n)` and sees `0..=n - 1` in its
    // body (`a_counting_loop_keeps_its_symbolic_bound`), and no constant end holds those at
    // every `n`.
    let solved = holds_run(&counting_up());
    assert!(
        solved.iter().all(|c| c.to_string().contains('n')),
        "the counting loop kept no symbol: {solved:?}, ZED_TEST_SEED={seed}"
    );
}
