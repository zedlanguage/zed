//! The two-phase iteration against a flattened stack machine, against the concrete least
//! fixpoint, and on the loops whose values the strategy's constants decide.

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::store::interval::IntervalSet;
use zedc::store::iterate::{Equations, Strategy, dependency_graph, narrow, phase1, solve};
use zedc::store::lattice::Lattice;
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
/// holding its iteration count and its number of head changes.
fn machine(eq: &System, s: Strategy) -> Vec<IntervalSet> {
    let mut program = Vec::new();
    flatten(
        &weak_topological_order(&dependency_graph(&eq.reads)),
        &mut program,
    );
    let mut cells = vec![IntervalSet::empty(); eq.init.len()];
    // Frames: (instruction of the head, iteration, changes).
    let mut frames: Vec<(usize, u32, u32)> = Vec::new();
    let mut pc = 0;
    while pc < program.len() {
        match program[pc] {
            Instr::Eval(v) => {
                cells[v] = cells[v].join(&eq.eval(v, &cells));
                pc += 1;
            }
            Instr::Head { head, end } => {
                if frames.last().is_none_or(|f| f.0 != pc) {
                    frames.push((pc, 0, 0));
                }
                let (_, i, changes) = *frames.last().unwrap();
                let next = cells[head].join(&eq.eval(head, &cells));
                if i > 0 && next == cells[head] {
                    frames.pop();
                    pc = end + 1;
                } else if i == s.head_iterations {
                    for instr in &program[pc..end] {
                        if let Instr::Eval(v) | Instr::Head { head: v, .. } = *instr {
                            cells[v] = IntervalSet::top();
                        }
                    }
                    frames.pop();
                    pc = end + 1;
                } else {
                    let mut changes = changes;
                    if next != cells[head] {
                        changes += 1;
                        cells[head] = if changes > s.delay {
                            cells[head].widen(&next)
                        } else {
                            next
                        };
                    }
                    *frames.last_mut().unwrap() = (pc, i + 1, changes);
                    pc += 1;
                }
            }
            Instr::End { start } => pc = start,
        }
    }
    cells
}

fn strategy(delay: u32, head_iterations: u32) -> Strategy {
    Strategy {
        delay,
        head_iterations,
        ..Strategy::SPEC
    }
}

#[test]
fn phase_one_agrees_with_the_stack_machine() {
    let mut rng = Rng::new(0x1e7);
    for _ in 0..RANDOM_INSTANCES {
        let eq = System::random(&mut rng);
        let order = weak_topological_order(&dependency_graph(&eq.reads));
        for delay in 0..=4 {
            for head_iterations in [2, Strategy::SPEC.head_iterations] {
                let s = strategy(delay, head_iterations);
                assert_eq!(phase1(&eq, &order, s), machine(&eq, s), "{eq:?} {s:?}");
            }
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
        let order = weak_topological_order(&dependency_graph(&eq.reads));
        let mut cells = phase1(&eq, &order, Strategy::SPEC);
        assert!(is_post_fixpoint(&eq, &cells), "phase 1: {eq:?}");
        let before = cells.clone();
        if narrow(&eq, &mut cells, Strategy::SPEC.rounds) > 0 {
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
fn a_short_loop_is_exact_in_phase_one_and_a_long_one_is_widened() {
    // The first three head changes are joins: a counter that takes three values (0, 1, 2)
    // changes its head three times and is never widened; one that takes four is.
    let order = [Element::Component {
        head: 0,
        body: vec![],
    }];
    assert_eq!(
        phase1(&counter(2), &order, Strategy::SPEC),
        vec![iv(Some(0), Some(2))]
    );
    assert_eq!(
        phase1(&counter(3), &order, Strategy::SPEC),
        vec![iv(Some(0), None)]
    );
    // Phase 2 recovers the bound.
    assert_eq!(
        solve(&counter(99), Strategy::SPEC),
        vec![iv(Some(0), Some(99))]
    );
    // Delay 0 widens at the first change after the first value.
    assert_eq!(
        phase1(&counter(2), &order, strategy(0, 64)),
        vec![iv(Some(0), None)]
    );
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
        let cells = phase1(&eq, &order, Strategy::SPEC);
        let solved = solve(&eq, Strategy::SPEC);
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

#[test]
fn a_component_past_its_bound_is_set_to_the_top() {
    // With the bound lowered to 5 head updates and widening delayed past it, the counter's
    // component is cut off: its cells go to the top, and a cell after the loop reads that.
    let mut eq = counter(99);
    eq = System::new(
        vec![eq.init[0].clone(), IntervalSet::empty()],
        vec![
            eq.terms[0].clone(),
            vec![Term {
                from: 0,
                filter: iv(Some(10), None),
                offset: 0,
            }],
        ],
    );
    let order = weak_topological_order(&dependency_graph(&eq.reads));
    let cells = phase1(&eq, &order, strategy(100, 5));
    assert_eq!(cells, vec![IntervalSet::top(), iv(Some(10), None)]);
    // At the specified bound the same loop converges by widening first.
    assert_eq!(phase1(&eq, &order, Strategy::SPEC)[0], iv(Some(0), None));
}

#[test]
fn phase_two_stops_at_its_round_budget_with_sound_values() {
    // Narrowing a counter bounded at 99 from [0..] takes one round; a chain of five cells
    // after it takes one round per cell, so a budget of 2 stops partway, at sound values.
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
    let eq = System::new(init, terms);
    let order = weak_topological_order(&dependency_graph(&eq.reads));
    let start = phase1(&eq, &order, Strategy::SPEC);
    let mut cells = start.clone();
    assert_eq!(narrow(&eq, &mut cells, 2), 2);
    assert_eq!(cells[1], iv(Some(0), Some(99)));
    assert_eq!(cells[3], iv(Some(0), None));
    assert!(is_post_fixpoint(&eq, &cells));
    let mut full = start;
    assert_eq!(narrow(&eq, &mut full, Strategy::SPEC.rounds), 6);
    assert!(full.iter().all(|c| *c == iv(Some(0), Some(99))));
}

#[test]
fn equations_read_through_the_trait() {
    // The store calls the equations only through `Equations`; a system that reads nothing
    // is its initial values.
    let eq = System::new(vec![IntervalSet::of(3, 4)], vec![vec![]]);
    assert!(eq.reads()[0].is_empty());
    assert_eq!(solve(&eq, Strategy::SPEC), vec![IntervalSet::of(3, 4)]);
    assert_eq!(IntervalSet::bottom(), IntervalSet::empty());
}
