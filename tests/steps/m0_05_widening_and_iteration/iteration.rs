//! The two-phase iteration against a flattened stack machine, against the concrete least
//! fixpoint, and on the loops whose values the landmarks decide.

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::store::interval::IntervalSet;
use zedc::store::iterate::{Equations, Scopes, dependency_graph, narrow, phase1, solve};
use zedc::store::lattice::{Landmarks, Lattice};
use zedc::store::wto::{Element, weak_topological_order};

use super::{System, Term, is_post_fixpoint, iv};

/// One instruction of the flattened order.
#[derive(Clone, Copy, Debug)]
enum Instr {
    /// Join the cell with its projection.
    Eval(usize),
    /// The head of the component that ends at instruction `end`.
    Head { head: usize, end: usize },
    /// The end of the component whose head is at instruction `start`.
    End { start: usize },
}

fn flatten(order: &[Element], out: &mut Vec<Instr>) {
    for e in order {
        match e {
            Element::Vertex(v) => out.push(Instr::Eval(*v)),
            Element::Component { head, body } => {
                let start = out.len();
                out.push(Instr::Head {
                    head: *head,
                    end: 0,
                });
                flatten(body, out);
                let end = out.len();
                out.push(Instr::End { start });
                out[start] = Instr::Head { head: *head, end };
            }
        }
    }
}

/// Phase 1 as a machine over the flattened order, with one frame per open component
/// holding its iteration count. A head widens at every change.
fn machine(eq: &System) -> Vec<IntervalSet> {
    let mut program = Vec::new();
    let order = weak_topological_order(&dependency_graph(&eq.reads));
    flatten(&order, &mut program);
    let marks = Scopes::new(eq, &order);
    let mut cells = vec![IntervalSet::empty(); eq.init.len()];
    // Frames: (instruction of the head, iteration).
    let mut frames: Vec<(usize, u32)> = Vec::new();
    let mut pc = 0;
    while pc < program.len() {
        match program[pc] {
            Instr::Eval(v) => {
                cells[v] = cells[v].join(&eq.eval(v, &cells));
                pc += 1;
            }
            Instr::Head { head, end } => {
                if frames.last().is_none_or(|f| f.0 != pc) {
                    frames.push((pc, 0));
                }
                let (_, i) = *frames.last().unwrap();
                let next = cells[head].join(&eq.eval(head, &cells));
                if i > 0 && next == cells[head] {
                    frames.pop();
                    pc = end + 1;
                } else {
                    if next != cells[head] {
                        cells[head] = cells[head].widen(&next, marks.of(head));
                    }
                    *frames.last_mut().unwrap() = (pc, i + 1);
                    pc += 1;
                }
            }
            Instr::End { start } => pc = start,
        }
    }
    cells
}

#[test]
fn phase_one_agrees_with_the_stack_machine() {
    let mut rng = Rng::new(0x1e7);
    for _ in 0..RANDOM_INSTANCES {
        for eq in [System::random(&mut rng)]
            .map(|e| [e.clone(), e.bare()])
            .concat()
        {
            let order = weak_topological_order(&dependency_graph(&eq.reads));
            assert_eq!(phase1(&eq, &order), machine(&eq), "{eq:?}");
        }
    }
}

#[test]
fn both_phases_end_at_a_sound_post_fixpoint() {
    // Phase 1 ends at a post-fixpoint; phase 2 keeps it one; and the result contains every
    // value of every execution that stays in a window around the constants.
    let mut rng = Rng::new(0x50d);
    let mut narrowed = 0;
    for _ in 0..RANDOM_INSTANCES {
        let eq = System::random(&mut rng);
        let eq = if rng.below(2) == 0 { eq } else { eq.bare() };
        let order = weak_topological_order(&dependency_graph(&eq.reads));
        let mut cells = phase1(&eq, &order);
        assert!(is_post_fixpoint(&eq, &cells), "phase 1: {eq:?}");
        let before = cells.clone();
        if narrow(&eq, &order, &mut cells) > 0 {
            narrowed += 1;
        }
        assert!(is_post_fixpoint(&eq, &cells), "phase 2: {eq:?}");
        for (v, values) in eq.concrete((-40, 40)).iter().enumerate() {
            assert!(cells[v].is_subset(&before[v]));
            for &x in values {
                assert!(cells[v].contains(x), "cell {v} lost {x}: {eq:?}");
            }
        }
    }
    assert!(
        narrowed > RANDOM_INSTANCES / 10,
        "phase 2 changed only {narrowed} systems"
    );
}

/// `i = 0`, then `i = i + 1` while `i < bound`: the counter of `for i in 0..=bound`.
fn counter(bound: i64) -> System {
    System::new(
        vec![IntervalSet::single(0)],
        vec![vec![Term {
            from: 0,
            filter: iv(None, Some(bound - 1)),
            offset: 1,
        }]],
    )
}

#[test]
fn a_counter_stops_at_its_landmarks_in_phase_one() {
    // The guard `i < bound` gives the landmarks `bound - 2..=bound`, so the widening stops
    // the counter's upper end there, at any bound, with no delay.
    let order = [Element::Component {
        head: 0,
        body: vec![],
    }];
    for bound in [2, 3, 99, 1_000_000] {
        assert_eq!(
            phase1(&counter(bound), &order),
            vec![iv(Some(0), Some(bound))]
        );
    }
    // With no landmarks the end goes to infinity, and phase 2 brings it back: an infinite
    // end may take a finite bound once.
    assert_eq!(phase1(&counter(99).bare(), &order), vec![iv(Some(0), None)]);
    assert_eq!(solve(&counter(99).bare()), vec![iv(Some(0), Some(99))]);
}

/// `a = 0 ⊔ c; b = a + 1; c = b ⊓ (-inf, 4]`, with the cells numbered so that `head` is
/// cell 0.
fn three_cell_loop(head: char) -> (System, [usize; 3]) {
    // The cell index of a, b and c.
    let ix = match head {
        'a' => [0, 1, 2],
        'b' => [2, 0, 1],
        _ => [1, 2, 0],
    };
    let [a, b, c] = ix;
    let mut init = vec![IntervalSet::empty(); 3];
    let mut terms = vec![Vec::new(), Vec::new(), Vec::new()];
    init[a] = IntervalSet::single(0);
    terms[a].push(Term {
        from: c,
        filter: IntervalSet::top(),
        offset: 0,
    });
    terms[b].push(Term {
        from: a,
        filter: IntervalSet::top(),
        offset: 1,
    });
    terms[c].push(Term {
        from: b,
        filter: iv(None, Some(4)),
        offset: 0,
    });
    (System::new(init, terms), ix)
}

#[test]
fn the_widening_point_changes_the_phase_one_values() {
    // Phase 1's result depends on where the loop is cut, which is why the traversal is
    // fixed. Cut at a, the bound on c survives widening; cut at c, it does not.
    let run = |head| {
        let (eq, [a, b, c]) = three_cell_loop(head);
        let order = weak_topological_order(&dependency_graph(&eq.reads));
        let cells = phase1(&eq.clone().bare(), &order);
        let solved = solve(&eq.bare());
        (
            [&cells[a], &cells[b], &cells[c]].map(|x| x.to_string()),
            [&solved[a], &solved[b], &solved[c]].map(|x| x.to_string()),
        )
    };
    let (at_a, solved_a) = run('a');
    let (at_c, solved_c) = run('c');
    assert_eq!(at_a, ["[0..]", "[1..]", "[1..=4]"]);
    assert_eq!(at_c, ["[0..]", "[1..]", "[1..]"]);
    // Phase 2 recovers the same values from both.
    assert_eq!(solved_a, ["[0..=4]", "[1..=5]", "[1..=4]"]);
    assert_eq!(solved_c, solved_a);
}

/// The counter followed by a chain of five copies of it.
fn counter_and_copies() -> System {
    let mut init = vec![IntervalSet::single(0)];
    let mut terms = vec![counter(99).terms[0].clone()];
    for v in 1..=5 {
        init.push(IntervalSet::empty());
        terms.push(vec![Term {
            from: v - 1,
            filter: IntervalSet::top(),
            offset: 0,
        }]);
    }
    System::new(init, terms).bare()
}

#[test]
fn phase_two_runs_until_a_round_changes_nothing() {
    // With no landmarks, phase 1 leaves every cell at [0..]. Narrowing the counter takes one
    // round, and each copy one more: phase 2 runs all six rounds, with no budget to stop it.
    let eq = counter_and_copies();
    let order = weak_topological_order(&dependency_graph(&eq.reads));
    let mut cells = phase1(&eq, &order);
    assert!(cells.iter().all(|c| *c == iv(Some(0), None)));
    assert_eq!(narrow(&eq, &order, &mut cells), 6);
    assert!(cells.iter().all(|c| *c == iv(Some(0), Some(99))));
    assert!(is_post_fixpoint(&eq, &cells));
}

#[test]
fn phase_two_ends_where_meets_alone_would_descend_forever() {
    // `x = x + 1` from [0..]: [0..] is a post-fixpoint, and meeting it with the projection
    // gives [1..], [2..], ... without end. The narrowing moves the new lower end back to the
    // old one, so phase 2 changes nothing and ends.
    let eq = System::new(
        vec![IntervalSet::empty()],
        vec![vec![Term {
            from: 0,
            filter: IntervalSet::top(),
            offset: 1,
        }]],
    );
    let start = vec![iv(Some(0), None)];
    assert!(is_post_fixpoint(&eq, &start));
    assert_eq!(start[0].meet(&eq.eval(0, &start)), iv(Some(1), None));
    let mut cells = start.clone();
    let order = weak_topological_order(&dependency_graph(&eq.reads));
    assert_eq!(narrow(&eq, &order, &mut cells), 0);
    assert_eq!(cells, start);
}

#[test]
fn a_loop_with_no_landmark_ends_without_a_cap() {
    // A counter whose guard is not written anywhere the equations see: the head widens to
    // [0..] at its first change past the old bound, and phase 1 ends after a few
    // evaluations, at any bound.
    for bound in [10, 1_000_000_000] {
        let eq = counter(bound).bare();
        let order = weak_topological_order(&dependency_graph(&eq.reads));
        assert_eq!(phase1(&eq, &order), vec![iv(Some(0), None)]);
        assert_eq!(solve(&eq), vec![iv(Some(0), Some(bound))]);
    }
}

#[test]
fn equations_read_through_the_trait() {
    // The store calls the equations only through `Equations`; a system that reads nothing
    // is its initial values.
    let eq = System::new(vec![IntervalSet::of(3, 4)], vec![vec![]]);
    assert!(eq.reads()[0].is_empty());
    assert_eq!(solve(&eq), vec![IntervalSet::of(3, 4)]);
    assert_eq!(IntervalSet::bottom(), IntervalSet::empty());
}

/// `depth` nested loops, cell `k` reading the loop around it, itself and the loop inside it,
/// and writing the literal `100·k`.
struct Levels(Vec<Vec<usize>>);

impl Equations<IntervalSet> for Levels {
    fn reads(&self) -> &[Vec<usize>] {
        &self.0
    }
    fn eval(&self, _: usize, _: &[IntervalSet]) -> IntervalSet {
        IntervalSet::empty()
    }
    fn landmarks(&self, v: usize) -> Landmarks {
        Landmarks::of([100 * v as i64], [])
    }
}

#[test]
fn a_loop_takes_the_landmarks_of_the_loops_inside_it_only() {
    // A guard of an inner loop bounds what flows out to the heads around it, so each head
    // takes the literals of its loop and of every loop inside it, and none from outside.
    let depth = 5;
    let eq = Levels(
        (0..depth)
            .map(|k: usize| (k.saturating_sub(1)..(k + 2).min(depth)).collect())
            .collect(),
    );
    let scopes = Scopes::new(&eq, &weak_topological_order(&dependency_graph(&eq.0)));
    for k in 0..depth {
        let want: Vec<i64> = (k..depth)
            .flat_map(|j| {
                let m = 100 * j as i64;
                [m - 1, m, m + 1]
            })
            .collect();
        let got: Vec<i64> = scopes.of(k).ints().iter().copied().collect();
        assert_eq!(got, want, "cell {k}");
    }
}
