//! The scheduler of a build's checks, evaluations and compilations (DESIGN.md
//! sec:checking_in_zed, "Checks and evaluations on one dependency graph"; plan row
//! SCHED-dep-dag). The engine (`zedc::store::schedule`) is checked on the examples of that
//! paragraph, modeled as facts, and against [`reference`], an implementation of "The meaning,
//! independent of order" written here from its definition: rounds of closure and refusal, with
//! no search. The two must agree on every value and every refusal for random programs, under
//! renumberings of the nodes and orders of the roots.

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::schedule::{Facts, Kind, Poll, Refusal, Schedule, Values};

/// A fact's value in the model. `Failed` is a fact that read a failed or refused fact, as a
/// rejected expression's `Frame::Fail` spreads; `Refused` is the value of a refused component's
/// members.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Val {
    Num(u32),
    Failed,
    Refused,
}

use Val::{Failed, Num, Refused};

/// The top number of the iterable facts' lattice, which is `0..=CAP` with `Failed` above it.
const CAP: u32 = 50;

/// A node of a program, as data.
#[derive(Clone, Debug)]
enum Spec {
    /// An iterable fact: `Num(base) ⊔ ⨆ step(read)`, where `step` adds `inc` up to [`CAP`] and
    /// takes a failed or refused read to `Failed`.
    Iterable {
        reads: Vec<usize>,
        base: u32,
        inc: u32,
    },
    /// A once fact that makes one read per step. At step `k` it reads `steps[k][s mod len]`,
    /// `s` the sum of the numbers it has read; a failed or refused answer makes it `Failed`;
    /// after the last step it is `Num(s mod 5 + 1)`. Finishing makes the nodes up to `reveals`
    /// exist, as a schema evaluation makes types.
    Once {
        steps: Vec<Vec<usize>>,
        reveals: usize,
    },
}

fn once(steps: Vec<Vec<usize>>) -> Spec {
    Spec::Once { steps, reveals: 0 }
}

fn iterable(base: u32, inc: u32, reads: Vec<usize>) -> Spec {
    Spec::Iterable { reads, base, inc }
}

/// The next step of a once fact, from the answers it has: a function of the answers only.
fn script(steps: &[Vec<usize>], answers: &[Val]) -> Poll<Val> {
    let mut sum = 0u32;
    for a in answers {
        match a {
            Num(x) => sum += x,
            Failed | Refused => return Poll::Ready(Failed),
        }
    }
    match steps.get(answers.len()) {
        Some(choices) => Poll::Pending(choices[sum as usize % choices.len()]),
        None => Poll::Ready(Num(sum % 5 + 1)),
    }
}

fn transfer(base: u32, inc: u32, reads: &[usize], get: impl Fn(usize) -> Val) -> Val {
    let mut acc = Num(base);
    for &r in reads {
        let step = match get(r) {
            Num(x) => Num((x + inc).min(CAP)),
            Failed | Refused => Failed,
        };
        acc = match (acc, step) {
            (Num(a), Num(b)) => Num(a.max(b)),
            _ => Failed,
        };
    }
    acc
}

/// The least fixpoint of a set of iterable facts by Kleene iteration from `Num(0)`, the reads
/// outside it taken from `outside`; it does not depend on the order of `members`.
fn kleene(specs: &[Spec], members: &[usize], outside: impl Fn(usize) -> Val) -> Vec<Val> {
    let mut cur: Vec<Val> = vec![Num(0); members.len()];
    loop {
        let mut changed = false;
        for (i, &v) in members.iter().enumerate() {
            let Spec::Iterable { reads, base, inc } = &specs[v] else {
                panic!("a component handed to the solver holds only iterable facts");
            };
            let next = transfer(*base, *inc, reads, |r| {
                match members.iter().position(|&m| m == r) {
                    Some(j) => cur[j].clone(),
                    None => outside(r),
                }
            });
            if next != cur[i] {
                cur[i] = next;
                changed = true;
            }
        }
        if !changed {
            return cur;
        }
    }
}

/// A program's facts, with a record of what the scheduler asked of them.
struct Model {
    specs: Vec<Spec>,
    keys: Vec<String>,
    /// How many nodes exist now: a once fact's `reveals` raises it when it finishes.
    visible: usize,
    answers: Vec<Vec<Val>>,
    polls: Vec<u32>,
    finished: Vec<bool>,
    solves: Vec<Vec<usize>>,
    refusals: Vec<Refusal>,
    /// The once facts in the order they finished.
    finish_order: Vec<usize>,
}

impl Model {
    fn new(specs: Vec<Spec>, keys: Vec<String>) -> Self {
        let n = specs.len();
        Model {
            specs,
            keys,
            visible: n,
            answers: vec![Vec::new(); n],
            polls: vec![0; n],
            finished: vec![false; n],
            solves: Vec::new(),
            refusals: Vec::new(),
            finish_order: Vec::new(),
        }
    }

    /// Runs every node, in the order of `roots`, and returns the values.
    fn run(&mut self, roots: &[usize]) -> Vec<Val> {
        let mut s = Schedule::new();
        s.run(self, roots.iter().copied());
        (0..self.visible)
            .map(|v| s.values().get(v).cloned().expect("every node is final"))
            .collect()
    }

    /// Each refusal with its members sorted, the list sorted.
    fn sorted_refusals(&self) -> Vec<Refusal> {
        let mut out: Vec<Refusal> = self.refusals.iter().cloned().map(sorted_members).collect();
        out.sort_by(|a, b| a.members.cmp(&b.members));
        out
    }

    /// Checks what the engine promises the facts: each once fact polled once per answer and
    /// once more, each iterable fact solved once.
    fn assert_protocol(&self) {
        let mut solved = vec![false; self.specs.len()];
        for c in &self.solves {
            for &m in c {
                assert!(!solved[m], "{} solved twice", self.keys[m]);
                solved[m] = true;
            }
        }
        for v in 0..self.visible {
            if matches!(self.specs[v], Spec::Once { .. }) && self.polls[v] > 0 {
                assert_eq!(
                    self.polls[v] as usize,
                    self.answers[v].len() + 1,
                    "{} polled once per answer and once more",
                    self.keys[v]
                );
            }
        }
    }
}

impl Facts for Model {
    type Value = Val;
    type Key = String;
    fn count(&self) -> usize {
        self.visible
    }
    fn kind(&self, v: usize) -> Kind {
        match self.specs[v] {
            Spec::Iterable { .. } => Kind::Iterable,
            Spec::Once { .. } => Kind::Once,
        }
    }
    fn key(&self, v: usize) -> String {
        self.keys[v].clone()
    }
    fn reads(&self, v: usize) -> &[usize] {
        match &self.specs[v] {
            Spec::Iterable { reads, .. } => reads,
            Spec::Once { .. } => panic!("only an iterable fact has static reads"),
        }
    }
    fn poll(&mut self, v: usize, answer: Option<&Val>) -> Poll<Val> {
        assert!(
            !self.finished[v],
            "{} polled after it finished",
            self.keys[v]
        );
        assert_eq!(
            answer.is_some(),
            self.polls[v] > 0,
            "{}: an answer exactly from the second poll on",
            self.keys[v]
        );
        self.polls[v] += 1;
        if let Some(a) = answer {
            self.answers[v].push(a.clone());
        }
        let Spec::Once { steps, reveals } = &self.specs[v] else {
            panic!("only a once fact is polled");
        };
        let p = script(steps, &self.answers[v]);
        if let Poll::Ready(_) = p {
            self.finished[v] = true;
            self.finish_order.push(v);
            self.visible = self.visible.max(*reveals);
        }
        p
    }
    fn solve(&mut self, members: &[usize], done: &Values<Val>) -> Vec<Val> {
        let mut sorted = members.to_vec();
        sorted.sort_unstable();
        self.solves.push(sorted);
        kleene(&self.specs, members, |r| {
            done.get(r)
                .cloned()
                .expect("a component is solved only when its reads outside it are final")
        })
    }
    fn refuse(&mut self, refusal: &Refusal) -> Vec<Val> {
        self.refusals.push(refusal.clone());
        vec![Refused; refusal.members.len()]
    }
}

fn sorted_members(mut r: Refusal) -> Refusal {
    r.members.sort_unstable();
    r
}

/// A program whose nodes are named, in the order of the text: a node's key is its position.
struct Program {
    specs: Vec<Spec>,
    names: Vec<&'static str>,
}

impl Program {
    fn new() -> Self {
        Program {
            specs: Vec::new(),
            names: Vec::new(),
        }
    }

    /// Adds a node, defined later with [`Program::set`].
    fn node(&mut self, name: &'static str) -> usize {
        self.specs.push(once(Vec::new()));
        self.names.push(name);
        self.specs.len() - 1
    }

    fn set(&mut self, v: usize, spec: Spec) {
        self.specs[v] = spec;
    }

    fn model(&self) -> Model {
        let keys = (0..self.specs.len()).map(|i| format!("{i:04}")).collect();
        Model::new(self.specs.clone(), keys)
    }

    fn name(&self, v: usize) -> &'static str {
        self.names[v]
    }
}

/// A once fact that reads `reads` in turn and is accepted, `Num(1)`, when none failed: each
/// read's choice list has one entry.
fn reads_all(reads: &[usize]) -> Spec {
    once(reads.iter().map(|&r| vec![r]).collect())
}

/// The keyed write from a function other than `main` (DESIGN.md sec:ports): `save(positional v)
/// { main::files["x"] <- v; }` called from `main`. The check of `save` reads `main`'s declared
/// signature (the type of `main::files` is `main`'s `MainArgs`) and `save`'s own type; the type
/// of `main` reads the type of `save`. Per fact there is no cycle. One node per definition, the
/// check of each reading the other, makes a cycle, and it is refused. (zedc compiles the keyed
/// write at step L7.2; this is the scheduler's part of it.)
#[test]
fn the_keyed_write_from_a_function_other_than_main_has_no_cycle_per_fact() {
    let mut p = Program::new();
    let sig_main = p.node("sig(main)");
    let type_save = p.node("type(save)");
    let type_main = p.node("type(main)");
    let check_save = p.node("check(save)");
    let check_main = p.node("check(main)");
    p.set(sig_main, iterable(1, 0, vec![]));
    p.set(type_save, iterable(1, 0, vec![sig_main]));
    p.set(type_main, iterable(1, 0, vec![type_save]));
    p.set(check_save, reads_all(&[sig_main, type_save]));
    p.set(check_main, reads_all(&[type_main, type_save]));
    for roots in [vec![check_save, check_main], vec![check_main, check_save]] {
        let mut m = p.model();
        let values = m.run(&roots);
        assert!(m.refusals.is_empty(), "{:?}", m.refusals);
        assert_eq!(values[check_save], Num(3));
        assert_eq!(values[check_main], Num(3));
        m.assert_protocol();
    }

    // One node per definition: the check of `save` needs `main`, and `main`'s needs `save`.
    let mut d = Program::new();
    let save = d.node("save");
    let main = d.node("main");
    d.set(save, reads_all(&[main]));
    d.set(main, reads_all(&[save]));
    for roots in [[main, save], [save, main]] {
        let mut m = d.model();
        let values = m.run(&roots);
        assert_eq!(values, [Refused, Refused]);
        // The cycle starts at `save`, the first in the text.
        assert_eq!(
            m.sorted_refusals(),
            [Refusal {
                members: vec![save, main],
                cycle: vec![save, main],
            }]
        );
    }
}

/// DESIGN.md example 1: `f(positional k: int[0..=100]) = (k mod 7) + 3;`, `n = f(40);`,
/// `square(positional i: int[0..<n]) = i * i;`, `last = square(7);`. The store's bound on `n`
/// (here `Num(9)`, the top of `3..=9`) does not settle `7 < n`, so the check of `last` asks for
/// `eval(n)`, which runs after the check of `f`; `eval(last)` runs after the check of `last`.
/// With a bound that settles the obligation, `eval(n)` is never asked for.
#[test]
fn an_evaluation_a_check_asks_for_unlocks_a_second_evaluation() {
    for settled in [false, true] {
        let mut p = Program::new();
        let check_f = p.node("check(f)");
        let bound_n = p.node("bound(n)");
        let eval_n = p.node("eval(n)");
        let check_square = p.node("check(square)");
        let check_last = p.node("check(last)");
        let eval_last = p.node("eval(last)");
        p.set(check_f, reads_all(&[]));
        // `settled`: the store's bound alone shows `7 < n`. The bound is `Num(9)` or `Num(10)`;
        // `check(last)` reads it and then, when the sum read is odd (not settled), `eval(n)`.
        p.set(bound_n, iterable(if settled { 10 } else { 9 }, 0, vec![]));
        p.set(eval_n, reads_all(&[check_f]));
        p.set(check_square, reads_all(&[]));
        p.set(
            check_last,
            once(vec![vec![bound_n], vec![check_square, eval_n]]),
        );
        p.set(eval_last, reads_all(&[check_last, check_square]));
        let mut m = p.model();
        // The last definition first: what it needs is found by demand, not by the root order.
        let values = m.run(&[
            eval_last,
            check_last,
            check_square,
            eval_n,
            bound_n,
            check_f,
        ]);
        assert!(m.refusals.is_empty());
        m.assert_protocol();
        let order: Vec<&str> = m.finish_order.iter().map(|&v| p.name(v)).collect();
        if settled {
            // The second read is `check(square)`: `check(last)` never asked for `eval(n)`.
            assert_eq!(m.answers[check_last], [Num(10), Num(1)]);
            assert_eq!(order[..3], ["check(square)", "check(last)", "eval(last)"]);
        } else {
            // `eval(n)` read `check(f)`, `Num(1)`, and gave `Num(2)`.
            assert_eq!(m.answers[check_last], [Num(9), Num(2)]);
            assert_eq!(
                order[..5],
                [
                    "check(f)",
                    "eval(n)",
                    "check(last)",
                    "check(square)",
                    "eval(last)"
                ]
            );
        }
        assert_eq!(values[check_last], Num(2));
        assert_eq!(values[eval_last], Num(4));
    }
}

/// A check that asks for an evaluation only when the store does not settle it: demanding the
/// check alone runs the evaluation only in that case (rule 3, demand by need).
#[test]
fn an_evaluation_runs_only_when_a_check_needs_it() {
    for settled in [false, true] {
        let mut p = Program::new();
        let bound = p.node("bound(n)");
        let eval_n = p.node("eval(n)");
        let check = p.node("check(last)");
        p.set(bound, iterable(if settled { 2 } else { 1 }, 0, vec![]));
        p.set(eval_n, reads_all(&[]));
        // Sum 2 picks the first choice (settled, read the bound again); sum 1 picks `eval(n)`.
        p.set(check, once(vec![vec![bound], vec![bound, eval_n]]));
        let mut m = p.model();
        let mut s = Schedule::new();
        s.demand(&mut m, check);
        assert_eq!(m.polls[eval_n] > 0, !settled, "settled: {settled}");
        assert!(s.values().get(check).is_some());
    }
}

/// DESIGN.md example 2: `isEven` and `isOdd`. Their types are one component of iterable facts,
/// solved once, together; their checks read both types and not each other's verdict; one
/// compilation reads both checks. Nothing is refused.
#[test]
fn mutually_recursive_types_are_solved_as_one_component() {
    let mut p = Program::new();
    let type_even = p.node("type(isEven)");
    let type_odd = p.node("type(isOdd)");
    let check_even = p.node("check(isEven)");
    let check_odd = p.node("check(isOdd)");
    let compile = p.node("compile(isEven, isOdd)");
    p.set(type_even, iterable(1, 1, vec![type_odd]));
    p.set(type_odd, iterable(1, 1, vec![type_even]));
    p.set(check_even, reads_all(&[type_even, type_odd]));
    p.set(check_odd, reads_all(&[type_odd, type_even]));
    p.set(compile, reads_all(&[check_even, check_odd]));
    for roots in [[0, 1, 2, 3, 4], [4, 3, 2, 1, 0], [3, 0, 4, 2, 1]] {
        let mut m = p.model();
        let values = m.run(&roots);
        assert!(m.refusals.is_empty());
        assert_eq!(m.solves, [vec![type_even, type_odd]]);
        assert_eq!(values[type_even], Num(CAP));
        // It read two verdicts of `Num(1)`: (1 + 1) mod 5 + 1.
        assert_eq!(values[compile], Num(3));
        m.assert_protocol();
    }
}

/// DESIGN.md example 3: `N = steps(3);` with `steps(positional k: int[0..=N]) -> int = ...`.
/// The check of `N`'s definition reads the store's bound on `N` (widened, not settling `3 <=
/// N`), then asks for `eval(N)`, which asks for the check of `N`'s definition: a cycle through
/// once nodes, refused, with the cycle named from the check, the first once node in the text. A
/// definition that reads `N` fails quietly; it is not refused.
#[test]
fn a_value_needed_to_check_its_own_computation_is_refused() {
    let mut p = Program::new();
    let check_n = p.node("check(N)");
    let bound_n = p.node("bound(N)");
    let eval_n = p.node("eval(N)");
    let check_user = p.node("check(user)");
    let eval_user = p.node("eval(user)");
    p.set(check_n, once(vec![vec![bound_n], vec![eval_n, eval_n]]));
    p.set(bound_n, iterable(0, 1, vec![bound_n]));
    p.set(eval_n, reads_all(&[check_n]));
    p.set(check_user, reads_all(&[]));
    p.set(eval_user, reads_all(&[check_user, eval_n]));
    for roots in [[0, 1, 2, 3, 4], [4, 3, 2, 1, 0], [2, 4, 0, 3, 1]] {
        let mut m = p.model();
        let values = m.run(&roots);
        assert_eq!(
            m.sorted_refusals(),
            [Refusal {
                members: vec![check_n, eval_n],
                cycle: vec![check_n, eval_n],
            }]
        );
        assert_eq!(values[check_n], Refused);
        assert_eq!(values[eval_n], Refused);
        assert_eq!(values[bound_n], Num(CAP));
        assert_eq!(values[eval_user], Failed);
        m.assert_protocol();
    }
}

/// A once fact that reads itself is refused alone, its cycle itself.
#[test]
fn a_once_fact_that_reads_itself_is_refused() {
    let mut p = Program::new();
    let a = p.node("check(a)");
    p.set(a, reads_all(&[a]));
    let mut m = p.model();
    assert_eq!(m.run(&[a]), [Refused]);
    assert_eq!(
        m.refusals,
        [Refusal {
            members: vec![a],
            cycle: vec![a],
        }]
    );
}

/// The cycle a refusal names is the shortest through the once fact of least key, whatever the
/// order of the roots. Once `a` asks for the iterable `x`, which reads `y` and then `b`; `y`
/// reads `b`; once `b` asks for `a`. The cycles through `a` are `a x b` and `a x y b`, and a
/// depth-first walk of `x`'s reads would find the longer one first. Once `c`, which waits on
/// the component without being read by it, is not in it and fails quietly.
#[test]
fn a_refusal_names_the_shortest_cycle_through_its_first_once_fact() {
    let mut p = Program::new();
    let a = p.node("a");
    let x = p.node("x");
    let y = p.node("y");
    let b = p.node("b");
    let c = p.node("c");
    p.set(a, reads_all(&[x]));
    p.set(x, iterable(0, 0, vec![y, b]));
    p.set(y, iterable(0, 0, vec![b]));
    p.set(b, reads_all(&[a]));
    p.set(c, reads_all(&[y]));
    for roots in [[c, y, b, a, x], [a, b, c, x, y], [x, c, a, y, b]] {
        let mut m = p.model();
        let values = m.run(&roots);
        assert_eq!(
            m.sorted_refusals(),
            [Refusal {
                members: vec![a, x, y, b],
                cycle: vec![a, x, b],
            }]
        );
        assert_eq!(values[c], Failed);
    }
}

/// DESIGN.md example 4: the `@nonblocking` check adds an iterable fact per function, whether it
/// may block (`Num(0)` or `Num(1)`), and a verdict per marked function; the scheduler is
/// unchanged. Here `a` calls `b`, `b` calls `a` and `io`, which blocks; `@nonblocking a` is
/// rejected (its verdict reads 1) and `@nonblocking c`, which blocks nowhere, is accepted.
#[test]
fn a_new_check_joins_with_no_change_to_the_scheduler() {
    let mut p = Program::new();
    let blocks_io = p.node("mayBlock(io)");
    let blocks_a = p.node("mayBlock(a)");
    let blocks_b = p.node("mayBlock(b)");
    let blocks_c = p.node("mayBlock(c)");
    let verdict_a = p.node("nonblocking(a)");
    let verdict_c = p.node("nonblocking(c)");
    p.set(blocks_io, iterable(1, 0, vec![]));
    p.set(blocks_a, iterable(0, 0, vec![blocks_b]));
    p.set(blocks_b, iterable(0, 0, vec![blocks_a, blocks_io]));
    p.set(blocks_c, iterable(0, 0, vec![]));
    // The verdict reads the fact; the sum picks: 0 accepts (reads nothing more), 1 rejects by
    // reading the fact again (the path of calls is found from the same facts).
    p.set(verdict_a, once(vec![vec![blocks_a]]));
    p.set(verdict_c, once(vec![vec![blocks_c]]));
    let mut m = p.model();
    let values = m.run(&[verdict_a, verdict_c]);
    assert_eq!(values[blocks_a], Num(1));
    assert_eq!(values[blocks_b], Num(1));
    assert_eq!(values[blocks_c], Num(0));
    assert_eq!(m.answers[verdict_a], [Num(1)]);
    assert_eq!(m.answers[verdict_c], [Num(0)]);
    assert!(m.refusals.is_empty());
    assert_eq!(m.solves.iter().filter(|c| c.len() == 2).count(), 1);
}

/// An evaluation may add nodes as it runs, as a schema evaluation makes types (QUESTIONS A72):
/// a check reads the evaluation, then a type that exists only after it.
#[test]
fn an_evaluation_may_add_the_nodes_a_check_reads_next() {
    let mut p = Program::new();
    let eval_schema = p.node("eval(schema)");
    let check_use = p.node("check(use)");
    let type_order = p.node("type(Order)");
    p.set(
        eval_schema,
        Spec::Once {
            steps: vec![],
            reveals: 3,
        },
    );
    p.set(check_use, reads_all(&[eval_schema, type_order]));
    p.set(type_order, iterable(7, 0, vec![]));
    let mut m = p.model();
    // `type(Order)` exists only once `eval(schema)` has run.
    m.visible = 2;
    let mut s = Schedule::new();
    s.demand(&mut m, check_use);
    assert_eq!(m.count(), 3);
    // It read `Num(1)` and `Num(7)`: (1 + 7) mod 5 + 1.
    assert_eq!(s.values().get(check_use), Some(&Num(4)));
    assert_eq!(s.values().get(type_order), Some(&Num(7)));
}

#[test]
#[should_panic(expected = "node 0 reads node 7, which does not exist")]
fn a_read_of_a_node_that_does_not_exist_stops_the_build() {
    let mut p = Program::new();
    let a = p.node("a");
    p.set(a, reads_all(&[7]));
    p.model().run(&[a]);
}

/// "The meaning, independent of order" (DESIGN.md), computed by its definition: rounds of
/// closure, then refusal of every component of the wait graph that waits on nothing outside
/// itself. Returns the values and the refusals, members sorted. Quadratic and more; for small
/// programs only.
fn reference(specs: &[Spec], keys: &[String]) -> (Vec<Val>, Vec<Refusal>) {
    let n = specs.len();
    let mut value: Vec<Option<Val>> = vec![None; n];
    let mut answers: Vec<Vec<Val>> = vec![Vec::new(); n];
    let mut refusals = Vec::new();
    // The components of the static graph among iterable facts, by reachability.
    let iter_edges: Vec<Vec<usize>> = (0..n)
        .map(|v| match &specs[v] {
            Spec::Iterable { reads, .. } => reads
                .iter()
                .copied()
                .filter(|&r| matches!(specs[r], Spec::Iterable { .. }))
                .collect(),
            Spec::Once { .. } => Vec::new(),
        })
        .collect();
    let iter_reach = closure(n, &iter_edges);
    loop {
        // Closure.
        loop {
            let mut changed = false;
            for v in 0..n {
                if value[v].is_some() {
                    continue;
                }
                match &specs[v] {
                    Spec::Once { steps, .. } => loop {
                        match script(steps, &answers[v]) {
                            Poll::Ready(x) => {
                                value[v] = Some(x);
                                changed = true;
                                break;
                            }
                            Poll::Pending(u) => match &value[u] {
                                Some(a) => {
                                    let a = a.clone();
                                    answers[v].push(a);
                                }
                                None => break,
                            },
                        }
                    },
                    Spec::Iterable { .. } => {
                        let comp: Vec<usize> = (0..n)
                            .filter(|&u| iter_reach[v][u] && iter_reach[u][v])
                            .collect();
                        let ready = comp.iter().all(|&u| match &specs[u] {
                            Spec::Iterable { reads, .. } => reads
                                .iter()
                                .all(|&r| comp.contains(&r) || value[r].is_some()),
                            Spec::Once { .. } => unreachable!(),
                        });
                        if ready {
                            let vals = kleene(specs, &comp, |r| {
                                value[r].clone().expect("checked final above")
                            });
                            for (u, x) in comp.into_iter().zip(vals) {
                                value[u] = Some(x);
                            }
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // Refusal.
        let remaining: Vec<usize> = (0..n).filter(|&v| value[v].is_none()).collect();
        if remaining.is_empty() {
            return (value.into_iter().map(Option::unwrap).collect(), {
                refusals.sort_by(|a: &Refusal, b: &Refusal| a.members.cmp(&b.members));
                refusals
            });
        }
        let waits: Vec<Vec<usize>> = (0..n)
            .map(|v| {
                if value[v].is_some() {
                    return Vec::new();
                }
                match &specs[v] {
                    Spec::Iterable { reads, .. } => reads
                        .iter()
                        .copied()
                        .filter(|&r| value[r].is_none())
                        .collect(),
                    Spec::Once { steps, .. } => match script(steps, &answers[v]) {
                        Poll::Pending(u) => vec![u],
                        Poll::Ready(_) => unreachable!("closure finishes a ready once fact"),
                    },
                }
            })
            .collect();
        let reach = closure(n, &waits);
        let mut refused_now: Vec<usize> = Vec::new();
        for &v in &remaining {
            let comp: Vec<usize> = remaining
                .iter()
                .copied()
                .filter(|&u| reach[v][u] && reach[u][v])
                .collect();
            if comp[0] != v {
                continue; // Each component once, at its least member.
            }
            let sink = comp
                .iter()
                .all(|&u| waits[u].iter().all(|w| comp.contains(w)));
            if !sink {
                continue;
            }
            let start = comp
                .iter()
                .copied()
                .filter(|&u| matches!(specs[u], Spec::Once { .. }))
                .min_by(|&a, &b| keys[a].cmp(&keys[b]))
                .expect("a component waiting on nothing outside itself holds a once fact");
            let cycle = bfs_cycle(start, &comp, |x| match &specs[x] {
                Spec::Iterable { reads, .. } => reads.clone(),
                Spec::Once { .. } => waits[x].clone(),
            });
            refused_now.extend(&comp);
            refusals.push(Refusal {
                members: comp,
                cycle,
            });
        }
        assert!(!refused_now.is_empty(), "a round refuses something");
        for v in refused_now {
            value[v] = Some(Refused);
        }
    }
}

/// Reachability by one or more edges, plus each node to itself.
fn closure(n: usize, edges: &[Vec<usize>]) -> Vec<Vec<bool>> {
    let mut r = vec![vec![false; n]; n];
    for (v, row) in r.iter_mut().enumerate() {
        row[v] = true;
        let mut stack = vec![v];
        while let Some(x) = stack.pop() {
            for &y in &edges[x] {
                if !row[y] {
                    row[y] = true;
                    stack.push(y);
                }
            }
        }
    }
    r
}

fn bfs_cycle(start: usize, comp: &[usize], edges: impl Fn(usize) -> Vec<usize>) -> Vec<usize> {
    let mut parent: Vec<(usize, usize)> = vec![(start, start)];
    let mut queue = vec![start];
    let mut head = 0;
    while head < queue.len() {
        let x = queue[head];
        head += 1;
        for y in edges(x) {
            if y == start {
                let mut path = vec![x];
                let mut z = x;
                while z != start {
                    z = parent.iter().find(|p| p.0 == z).expect("reached").1;
                    path.push(z);
                }
                path.reverse();
                return path;
            }
            if comp.contains(&y) && !parent.iter().any(|p| p.0 == y) {
                parent.push((y, x));
                queue.push(y);
            }
        }
    }
    panic!("a refused component is strongly connected");
}

/// A random program of `n` nodes: reads mostly to earlier nodes, so that it has long acyclic
/// stretches as well as components of every kind.
fn random_program(rng: &mut Rng, n: usize) -> Vec<Spec> {
    let pick = |rng: &mut Rng, v: usize| -> usize {
        if v > 0 && rng.below(10) < 7 {
            rng.below(v)
        } else {
            rng.below(n)
        }
    };
    (0..n)
        .map(|v| {
            if rng.below(10) < 6 {
                let k = rng.below(4);
                let reads = (0..k).map(|_| pick(rng, v)).collect();
                iterable(rng.below(4) as u32, rng.below(3) as u32, reads)
            } else {
                let k = 1 + rng.below(3);
                let steps = (0..k)
                    .map(|_| {
                        let c = 1 + rng.below(3);
                        (0..c).map(|_| pick(rng, v)).collect()
                    })
                    .collect();
                once(steps)
            }
        })
        .collect()
}

fn shuffle(rng: &mut Rng, xs: &mut [usize]) {
    for i in (1..xs.len()).rev() {
        let j = rng.below(i + 1);
        xs.swap(i, j);
    }
}

/// The engine gives every program the meaning its definition gives, whatever the numbering of
/// its nodes and the order of its roots: values and refusals, cycles included.
#[test]
fn the_engine_agrees_with_the_meaning_under_every_order() {
    let mut rng = Rng::new(0x5c4ed);
    let mut refused = 0;
    let mut solved_cycles = 0;
    for trial in 0..1500 {
        let n = 1 + rng.below(24);
        let specs = random_program(&mut rng, n);
        let keys: Vec<String> = (0..n).map(|i| format!("{i:04}")).collect();
        let (want, want_refusals) = reference(&specs, &keys);
        for _ in 0..3 {
            // Physical number of logical node `i` is `perm[i]`.
            let mut perm: Vec<usize> = (0..n).collect();
            shuffle(&mut rng, &mut perm);
            let mut phys = vec![once(Vec::new()); n];
            let mut phys_keys = vec![String::new(); n];
            for i in 0..n {
                phys[perm[i]] = match &specs[i] {
                    Spec::Iterable { reads, base, inc } => {
                        iterable(*base, *inc, reads.iter().map(|&r| perm[r]).collect())
                    }
                    Spec::Once { steps, reveals } => Spec::Once {
                        steps: steps
                            .iter()
                            .map(|c| c.iter().map(|&r| perm[r]).collect())
                            .collect(),
                        reveals: *reveals,
                    },
                };
                phys_keys[perm[i]] = keys[i].clone();
            }
            let mut roots: Vec<usize> = (0..n).collect();
            shuffle(&mut rng, &mut roots);
            // One file checked alone: a demand of one node gives every node it makes final the
            // value the whole build gives it (the batch and single-file rule).
            let root = roots[0];
            let mut alone = Model::new(phys.clone(), phys_keys.clone());
            let mut s = Schedule::new();
            s.demand(&mut alone, root);
            let mut m = Model::new(phys, phys_keys);
            let got = m.run(&roots);
            m.assert_protocol();
            assert!(
                s.values().get(root).is_some(),
                "trial {trial}: the demanded node is final"
            );
            for (v, whole) in got.iter().enumerate() {
                if let Some(value) = s.values().get(v) {
                    assert_eq!(
                        value, whole,
                        "trial {trial}: node {v} alone and in the build"
                    );
                }
            }
            let mut inverse = vec![0; n];
            for i in 0..n {
                inverse[perm[i]] = i;
            }
            let got: Vec<Val> = (0..n).map(|i| got[perm[i]].clone()).collect();
            assert_eq!(got, want, "trial {trial}: values");
            let mut got_refusals: Vec<Refusal> = m
                .refusals
                .iter()
                .map(|r| {
                    sorted_members(Refusal {
                        members: r.members.iter().map(|&x| inverse[x]).collect(),
                        cycle: r.cycle.iter().map(|&x| inverse[x]).collect(),
                    })
                })
                .collect();
            got_refusals.sort_by(|a, b| a.members.cmp(&b.members));
            assert_eq!(got_refusals, want_refusals, "trial {trial}: refusals");
            solved_cycles += m.solves.iter().filter(|c| c.len() > 1).count();
        }
        refused += want_refusals.len();
    }
    // The random programs exercise both kinds of cycle.
    assert!(refused > 300, "{refused} refusals");
    assert!(
        solved_cycles > 300,
        "{solved_cycles} iterable components of two or more"
    );
}

/// A program of `n` groups: a two-fact iterable component reading the previous group's, a check
/// reading it and the previous check, and every seventh group a refused pair of once facts with a
/// definition reading them, plus one refused ring of `n / 4` once facts. Demanded from the last
/// root first, so the search runs a chain of every group, deep.
fn scaling_program(n: usize) -> Vec<Spec> {
    let mut specs = Vec::with_capacity(6 * n);
    let mut prev_a = None;
    let mut prev_check = None;
    for i in 0..n {
        let a = specs.len();
        let b = a + 1;
        let mut reads_a = vec![b];
        reads_a.extend(prev_a);
        specs.push(iterable(1, 1, reads_a));
        specs.push(iterable(0, 1, vec![a]));
        let check = specs.len();
        let mut reads = vec![a];
        reads.extend(prev_check);
        specs.push(reads_all(&reads));
        if i % 7 == 0 {
            let d = specs.len();
            specs.push(reads_all(&[d + 1]));
            specs.push(reads_all(&[d]));
            specs.push(reads_all(&[check, d]));
        }
        prev_a = Some(a);
        prev_check = Some(check);
    }
    let ring = specs.len();
    let k = (n / 4).max(1);
    for j in 0..k {
        specs.push(reads_all(&[ring + (j + 1) % k]));
    }
    specs
}

fn run_scaling(n: usize) {
    let specs = scaling_program(n);
    let count = specs.len();
    let keys = (0..count).map(|i| format!("{i:08}")).collect();
    let mut m = Model::new(specs, keys);
    let roots: Vec<usize> = (0..count).rev().collect();
    let values = m.run(&roots);
    assert_eq!(values.len(), count);
    assert_eq!(m.refusals.len(), n.div_ceil(7) + 1);
}

/// The search is linear in the facts and reads (DESIGN.md, "The algorithm"): 7.96 times the
/// instructions and 8.00 times the bytes at 8n (2026-11-13). Negative control, run once and not
/// committed: resetting the refusal marks over every node instead of over the component's
/// members, O(n) for each of n / 7 refusals, took 29.2 times the instructions and failed.
#[test]
fn scaling() {
    scaling::check("the scheduler of checks and evaluations", 4000, run_scaling);
}
