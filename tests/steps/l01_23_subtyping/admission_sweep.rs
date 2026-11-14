//! A random sweep of the admission check of recursive type groups (plan item GROUP-admit):
//! seeded random groups of one to four definitions are given to `Group::new`, and a group the
//! witness-pool evaluator below calls not monotone must be rejected. A group the evaluator
//! calls monotone and the check refuses is a false rejection, which the check allows (it is
//! sufficient, not necessary); each sweep prints their number and the smallest of them.
//!
//! The evaluator is the one of cross-review xs2 (Gemini, `xs_proto` `eval_ty_mask`), ported to
//! Rust, with one change: the integer and the pair are two witnesses, not one, so that
//! `(int, int) & int` is empty here as it is in the kernel. A type is read as the set of the
//! four witnesses it holds, a mask of four bits: the integer 0, a pair, a function on the empty
//! domain and a function from an inhabited domain returning a value. `L .. U -> V` holds the
//! first function when `L` is empty, and the second when `L` holds no witness `U` lacks, `U` is
//! inhabited and `V` is inhabited.
//!
//! A group's emptiness is read as a function `F` of its members' emptiness as seen inside
//! morphism types: a reference inside a morphism type reads `s`, all four witnesses or none,
//! and any other reference reads `l`, the least fixed point of the bodies from no witnesses.
//! `F(s)` is whether each member's `l` holds a witness. The group is monotone when `F` is:
//! when no member is inhabited at some `s` and empty at a larger one, and the iteration of `l`
//! never loses a witness (the prototype's `step_group_checked`, which calls that not
//! monotone too). On the boolean lattice it is enough to compare each `s` with each `s` one
//! member larger.

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::fmt;

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_tests::instances::Rng;
use zed_tests::scaling;

// ---------------------------------------------------------------------------------------------
// Groups
// ---------------------------------------------------------------------------------------------

/// A type of a group; `Ref(i)` is definition `i`.
#[derive(Clone, Debug, PartialEq, Eq)]
enum T {
    Empty,
    Int,
    Top,
    Ref(usize),
    Or(Box<T>, Box<T>),
    And(Box<T>, Box<T>),
    Diff(Box<T>, Box<T>),
    Not(Box<T>),
    Pair(Box<T>, Box<T>),
    /// `Mor(l, u, v)`: guarantee `l`, permission `u`, value type `v`.
    Mor(Box<T>, Box<T>, Box<T>),
}

impl fmt::Display for T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            T::Empty => f.write_str("!_"),
            T::Int => f.write_str("int"),
            T::Top => f.write_str("_"),
            T::Ref(i) => write!(f, "R{i}"),
            T::Or(a, b) => write!(f, "({a} | {b})"),
            T::And(a, b) => write!(f, "({a} & {b})"),
            T::Diff(a, b) => write!(f, "({a} \\ {b})"),
            T::Not(a) => write!(f, "!{a}"),
            T::Pair(a, b) => write!(f, "({a}, {b})"),
            T::Mor(l, u, v) if l == u => write!(f, "(({l}) -> {v})"),
            T::Mor(l, u, v) => write!(f, "({l} .. {u} -> {v})"),
        }
    }
}

/// The group as text, one definition after another.
fn show(group: &[T]) -> String {
    let defs: Vec<String> = group
        .iter()
        .enumerate()
        .map(|(i, d)| format!("R{i} = {d}"))
        .collect();
    defs.join("; ")
}

/// The number of types in the group's bodies.
fn size(group: &[T]) -> usize {
    group.iter().map(|t| kids_and_self(t).len()).sum()
}

/// `t` and every type in it, each before its parts.
fn kids_and_self(t: &T) -> Vec<&T> {
    let (mut out, mut todo) = (Vec::new(), vec![t]);
    while let Some(t) = todo.pop() {
        out.push(t);
        match t {
            T::Empty | T::Int | T::Top | T::Ref(_) => {}
            T::Not(a) => todo.push(a),
            T::Or(a, b) | T::And(a, b) | T::Diff(a, b) | T::Pair(a, b) => {
                todo.extend([&**b, &**a]);
            }
            T::Mor(l, u, v) => todo.extend([&**v, &**u, &**l]),
        }
    }
    out
}

/// `t` as a kernel expression.
fn expr(t: &T) -> Expr {
    let b = |t: &T| Box::new(expr(t));
    match t {
        T::Empty => Expr::Type(Type::empty()),
        T::Int => Expr::Type(Type::int()),
        T::Top => Expr::Type(Type::top()),
        T::Ref(i) => Expr::Ref(*i, vec![]),
        T::Or(a, c) => Expr::Union(vec![expr(a), expr(c)]),
        T::And(a, c) => Expr::And(vec![expr(a), expr(c)]),
        T::Diff(a, c) => Expr::Diff(b(a), b(c)),
        T::Not(a) => Expr::Not(b(a)),
        T::Pair(a, c) => Expr::Tuple(vec![expr(a), expr(c)]),
        T::Mor(l, u, v) => Expr::Morphism(b(l), b(u), b(v)),
    }
}

/// What the admission check makes of a group.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Admission {
    Accepted,
    /// Refused as outside the form the checker accepts, with the message.
    Refused(String),
    /// Rejected for another reason (not contractive, not regular), with the message.
    Other(String),
}

fn admission(group: &[T]) -> Admission {
    let defs = group
        .iter()
        .enumerate()
        .map(|(i, t)| Def {
            name: format!("R{i}"),
            params: vec![],
            body: expr(t),
        })
        .collect();
    match Group::new(defs) {
        Ok(_) => Admission::Accepted,
        Err(e)
            if e.message
                .contains("is outside the form the checker accepts") =>
        {
            Admission::Refused(e.message)
        }
        Err(e) => Admission::Other(e.message),
    }
}

// ---------------------------------------------------------------------------------------------
// The witness-pool evaluator
// ---------------------------------------------------------------------------------------------

const INT: u8 = 0b0001;
const PAIR: u8 = 0b0010;
const FN_EMPTY: u8 = 0b0100;
const FN_INHABITED: u8 = 0b1000;
const ALL: u8 = 0b1111;

/// One type of a flattened group; the operands are indices of earlier types.
#[derive(Clone, Copy)]
enum Op {
    Const(u8),
    Ref(usize),
    Or(usize, usize),
    And(usize, usize),
    Diff(usize, usize),
    Not(usize),
    Pair(usize, usize),
    Mor(usize, usize, usize),
}

/// A group's bodies as one list of types, each after its operands, and the index of each body.
struct Flat {
    ops: Vec<Op>,
    roots: Vec<usize>,
}

impl Flat {
    /// The bodies of `group`, flattened from an explicit stack.
    fn of(group: &[T]) -> Flat {
        enum Step<'a> {
            Visit(&'a T),
            Build(&'a T),
        }
        let mut ops = Vec::new();
        let mut roots = Vec::with_capacity(group.len());
        // The index of each type built and not yet read as an operand.
        let mut done: Vec<usize> = Vec::new();
        for body in group {
            let mut todo = vec![Step::Visit(body)];
            while let Some(step) = todo.pop() {
                let op = match step {
                    Step::Visit(T::Empty) => Op::Const(0),
                    Step::Visit(T::Int) => Op::Const(INT),
                    Step::Visit(T::Top) => Op::Const(ALL),
                    Step::Visit(T::Ref(i)) => Op::Ref(*i),
                    Step::Visit(t) => {
                        todo.push(Step::Build(t));
                        match t {
                            T::Not(a) => todo.push(Step::Visit(a)),
                            T::Or(a, b) | T::And(a, b) | T::Diff(a, b) | T::Pair(a, b) => {
                                todo.extend([Step::Visit(b), Step::Visit(a)]);
                            }
                            T::Mor(l, u, v) => {
                                todo.extend([Step::Visit(v), Step::Visit(u), Step::Visit(l)]);
                            }
                            T::Empty | T::Int | T::Top | T::Ref(_) => {
                                unreachable!("a leaf is not built")
                            }
                        }
                        continue;
                    }
                    Step::Build(t) => {
                        let mut last = || done.pop().expect("each operand is built");
                        match t {
                            T::Not(_) => Op::Not(last()),
                            T::Or(..) | T::And(..) | T::Diff(..) | T::Pair(..) => {
                                let b = last();
                                let a = last();
                                match t {
                                    T::Or(..) => Op::Or(a, b),
                                    T::And(..) => Op::And(a, b),
                                    T::Diff(..) => Op::Diff(a, b),
                                    _ => Op::Pair(a, b),
                                }
                            }
                            T::Mor(..) => {
                                let v = last();
                                let u = last();
                                Op::Mor(last(), u, v)
                            }
                            T::Empty | T::Int | T::Top | T::Ref(_) => {
                                unreachable!("a leaf is not built")
                            }
                        }
                    }
                };
                done.push(ops.len());
                ops.push(op);
            }
            roots.push(done.pop().expect("the body is built"));
        }
        Flat { ops, roots }
    }

    /// The masks of every member's body, `l` read by references outside morphism types and `s`
    /// inside them. `at` holds, for each type, its mask outside and inside a morphism type.
    fn eval(&self, s: &[u8], l: &[u8], at: &mut Vec<(u8, u8)>, out: &mut [u8]) {
        at.clear();
        for op in &self.ops {
            let pair = |a: u8, b: u8| if a != 0 && b != 0 { PAIR } else { 0 };
            let m = match *op {
                Op::Const(c) => (c, c),
                Op::Ref(i) => (l[i], s[i]),
                Op::Or(a, b) => (at[a].0 | at[b].0, at[a].1 | at[b].1),
                Op::And(a, b) => (at[a].0 & at[b].0, at[a].1 & at[b].1),
                Op::Diff(a, b) => (at[a].0 & !at[b].0, at[a].1 & !at[b].1),
                Op::Not(a) => (ALL & !at[a].0, ALL & !at[a].1),
                Op::Pair(a, b) => (pair(at[a].0, at[b].0), pair(at[a].1, at[b].1)),
                Op::Mor(lo, hi, v) => {
                    let (lo, hi, v) = (at[lo].1, at[hi].1, at[v].1);
                    let mut m = 0;
                    if lo == 0 {
                        m |= FN_EMPTY;
                    }
                    if lo & !hi == 0 && hi != 0 && v != 0 {
                        m |= FN_INHABITED;
                    }
                    (m, m)
                }
            };
            at.push(m);
        }
        for (o, &r) in out.iter_mut().zip(&self.roots) {
            *o = at[r].0;
        }
    }

    /// `F(s)`: the members inhabited, one bit each, when the members inhabited inside morphism
    /// types are those of `s`; `None` when the iteration of `l` loses a witness. Each round
    /// before the last adds a witness to some member and none loses one, so there are at most
    /// four rounds a member.
    fn step(&self, s: u32, at: &mut Vec<(u8, u8)>) -> Option<u32> {
        let k = self.roots.len();
        let s: Vec<u8> = (0..k)
            .map(|i| if s >> i & 1 == 1 { ALL } else { 0 })
            .collect();
        let mut l = vec![0u8; k];
        let mut next = vec![0u8; k];
        loop {
            self.eval(&s, &l, at, &mut next);
            if l.iter().zip(&next).any(|(&a, &b)| a & !b != 0) {
                return None;
            }
            if next == l {
                return Some((0..k).fold(0, |m, i| m | u32::from(l[i] != 0) << i));
            }
            std::mem::swap(&mut l, &mut next);
        }
    }

    /// Whether `F` is monotone, or where it is not.
    // Complexity tradeoff: the evaluator reads `F` at all 2^k values of `s` for a group of k
    // definitions, so the sweep builds groups of at most four (`group`); larger groups are not
    // swept. Deciding whether a boolean function given by a formula with complement is monotone
    // is coNP-complete, so an exact answer for any k costs time exponential in k. The tests
    // `random_groups_admitted_are_monotone_*` exercise it; COMPLEXITY.md row GROUP-admit. A
    // complete test of large groups would need the admission check's own argument, which the
    // sweep exists to check.
    fn monotone(&self) -> Result<(), Flip> {
        let k = self.roots.len();
        let mut at = Vec::with_capacity(self.ops.len());
        let mut f = Vec::with_capacity(1 << k);
        for s in 0u32..1 << k {
            f.push(self.step(s, &mut at).ok_or(Flip::Loses(s))?);
        }
        for s in 0u32..1 << k {
            for i in (0..k).filter(|&i| s >> i & 1 == 0) {
                let larger = s | 1 << i;
                let lost = f[s as usize] & !f[larger as usize];
                if lost != 0 {
                    return Err(Flip::Shrinks {
                        s,
                        larger,
                        member: lost.trailing_zeros() as usize,
                    });
                }
            }
        }
        Ok(())
    }
}

/// Why the evaluator calls a group not monotone.
#[derive(Clone, Copy, Debug)]
enum Flip {
    /// At `s`, the iteration of the members outside morphism types loses a witness.
    Loses(u32),
    /// `member` is inhabited at `s` and empty at `larger`, which is `s` and one member more.
    Shrinks { s: u32, larger: u32, member: usize },
}

impl fmt::Display for Flip {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let set = |s: u32| {
            let names: Vec<String> = (0..32)
                .filter(|i| s >> i & 1 == 1)
                .map(|i| format!("R{i}"))
                .collect();
            format!("{{{}}}", names.join(", "))
        };
        match *self {
            Flip::Loses(s) => write!(
                f,
                "with {} inhabited inside morphism types, a member loses a witness as the \
                 members outside them are built",
                set(s)
            ),
            Flip::Shrinks { s, larger, member } => write!(
                f,
                "R{member} is inhabited with {} inhabited inside morphism types and empty with {}",
                set(s),
                set(larger)
            ),
        }
    }
}

fn monotone(group: &[T]) -> Result<(), Flip> {
    Flat::of(group).monotone()
}

// ---------------------------------------------------------------------------------------------
// Random groups
// ---------------------------------------------------------------------------------------------

/// A random type of a group of `k` definitions, at most `depth` deep. A reference stands only
/// inside a pair or a morphism type (`guarded`), so every group is contractive and the
/// admission check is the only check that can refuse it. Half the morphism types are exact, the
/// form the check accepts a reference in the guarantee of.
fn term(g: &mut Rng, k: usize, depth: u32, guarded: bool) -> T {
    if depth == 0 || g.below(4) == 0 {
        return match g.below(if guarded { 6 } else { 3 }) {
            0 => T::Empty,
            1 => T::Int,
            2 => T::Top,
            _ => T::Ref(g.below(k)),
        };
    }
    let kid = |g: &mut Rng, guarded| Box::new(term(g, k, depth - 1, guarded));
    match g.below(10) {
        0 | 1 => T::Or(kid(g, guarded), kid(g, guarded)),
        2 => T::And(kid(g, guarded), kid(g, guarded)),
        3 => T::Diff(kid(g, guarded), kid(g, guarded)),
        4 => T::Not(kid(g, guarded)),
        5 | 6 => T::Pair(kid(g, true), kid(g, true)),
        _ => {
            let l = kid(g, true);
            let u = match g.below(2) {
                0 => l.clone(),
                _ => kid(g, true),
            };
            T::Mor(l, u, kid(g, true))
        }
    }
}

/// A random group of one to four definitions, each at most four deep.
fn group(g: &mut Rng) -> Vec<T> {
    let k = 1 + g.below(4);
    (0..k).map(|_| term(g, k, 4, false)).collect()
}

// ---------------------------------------------------------------------------------------------
// Shrinking
// ---------------------------------------------------------------------------------------------

/// `t` with the type at preorder place `at` replaced by `by`; `at` counts down to it.
fn replaced(t: &T, at: &mut usize, by: &T) -> T {
    if *at == 0 {
        *at = usize::MAX;
        return by.clone();
    }
    *at -= 1;
    let mut r = |t: &T| Box::new(replaced(t, at, by));
    match t {
        T::Empty | T::Int | T::Top | T::Ref(_) => t.clone(),
        T::Not(a) => T::Not(r(a)),
        T::Or(a, b) => {
            let a = r(a);
            T::Or(a, r(b))
        }
        T::And(a, b) => {
            let a = r(a);
            T::And(a, r(b))
        }
        T::Diff(a, b) => {
            let a = r(a);
            T::Diff(a, r(b))
        }
        T::Pair(a, b) => {
            let a = r(a);
            T::Pair(a, r(b))
        }
        T::Mor(l, u, v) => {
            let l = r(l);
            let u = r(u);
            T::Mor(l, u, r(v))
        }
    }
}

/// A smallest group found from `group` by replacing one type at a time with a constant or one
/// of its parts while `keep` holds: each accepted replacement makes the group smaller, so the
/// search ends.
fn shrink(group: &[T], keep: impl Fn(&[T]) -> bool) -> Vec<T> {
    let mut best = group.to_vec();
    'again: loop {
        for d in 0..best.len() {
            let places = kids_and_self(&best[d]);
            for (at, sub) in places.iter().enumerate() {
                let mut by = vec![T::Empty, T::Int, T::Top];
                match sub {
                    T::Empty | T::Int | T::Top | T::Ref(_) => {}
                    T::Not(a) => by.push((**a).clone()),
                    T::Or(a, b) | T::And(a, b) | T::Diff(a, b) | T::Pair(a, b) => {
                        by.extend([(**a).clone(), (**b).clone()]);
                    }
                    T::Mor(l, u, v) => by.extend([(**l).clone(), (**u).clone(), (**v).clone()]),
                }
                for b in by {
                    let mut candidate = best.clone();
                    candidate[d] = replaced(&best[d], &mut at.clone(), &b);
                    if size(&candidate) < size(&best) && keep(&candidate) {
                        best = candidate;
                        continue 'again;
                    }
                }
            }
        }
        return best;
    }
}

// ---------------------------------------------------------------------------------------------
// The sweep
// ---------------------------------------------------------------------------------------------

#[derive(Default, Debug)]
struct Tally {
    groups: usize,
    accepted: usize,
    /// Groups the evaluator calls not monotone.
    not_monotone: usize,
    /// Groups the evaluator calls not monotone and the check accepts: soundness failures.
    unsound: usize,
    /// Groups the evaluator calls monotone and the check refuses.
    false_rejections: usize,
}

/// How a group fails the sweep, if it does.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Failure {
    /// The check accepts it and the evaluator calls it not monotone.
    Unsound,
    /// Another check rejects it, which no generated group should meet.
    Other,
}

fn failure(group: &[T]) -> Option<Failure> {
    match (admission(group), monotone(group)) {
        (Admission::Accepted, Err(_)) => Some(Failure::Unsound),
        (Admission::Other(_), _) => Some(Failure::Other),
        _ => None,
    }
}

/// What the evaluator and the check say of `group`, for a report.
fn explain(group: &[T]) -> String {
    let evaluator = match monotone(group) {
        Ok(()) => "monotone".to_string(),
        Err(flip) => format!("not monotone: {flip}"),
    };
    format!("{:?}; evaluator: {evaluator}", admission(group))
}

/// The arm of the admission check a refusal message comes from.
fn arm(message: &str) -> &'static str {
    if message.contains("whose value type") {
        if message.contains("mentions the group") {
            "value type mentions the group"
        } else if message.contains("may be empty") {
            "value type shrinks"
        } else {
            "value type is empty"
        }
    } else if message.contains("permission") {
        "guarantee and permission differ"
    } else if message.contains("which stands") {
        "guarantee under `&` or `\\`"
    } else if message.contains("narrowed where it is named") {
        "narrowed where named"
    } else if message.contains("under a complement") {
        "under a complement"
    } else if message.contains("to the right of") {
        "right of `\\`"
    } else {
        "other"
    }
}

/// The arm that refuses `group`, if the check refuses it and the evaluator calls it monotone.
fn false_rejection(group: &[T]) -> Option<&'static str> {
    match admission(group) {
        Admission::Refused(m) if monotone(group).is_ok() => Some(arm(&m)),
        _ => None,
    }
}

/// The false rejections of one arm of the check, and the smallest of them, the first by seed.
struct Refused {
    count: usize,
    size: usize,
    seed: u64,
    group: Vec<T>,
}

/// The sweep of the groups of `seeds`: no group fails, and at most `max_false` false rejections.
/// The false rejections are printed by number for each arm of the check, with the smallest shrunk.
fn sweep(name: &str, seeds: std::ops::Range<u64>, max_false: usize) {
    let mut tally = Tally::default();
    let mut failures = Vec::new();
    // For each arm of the check, its false rejections and the smallest of them.
    let mut refused: BTreeMap<&str, Refused> = BTreeMap::new();
    for seed in seeds {
        let group = group(&mut Rng::new(seed));
        tally.groups += 1;
        let flip = monotone(&group);
        tally.not_monotone += usize::from(flip.is_err());
        match admission(&group) {
            Admission::Accepted => {
                tally.accepted += 1;
                if flip.is_err() {
                    tally.unsound += 1;
                    failures.push((seed, group));
                }
            }
            Admission::Refused(message) => {
                if flip.is_ok() {
                    tally.false_rejections += 1;
                    let n = size(&group);
                    match refused.entry(arm(&message)) {
                        Entry::Vacant(e) => {
                            e.insert(Refused {
                                count: 1,
                                size: n,
                                seed,
                                group,
                            });
                        }
                        Entry::Occupied(mut e) => {
                            let r = e.get_mut();
                            r.count += 1;
                            // Seeds rise, so of two groups of one size the one kept came first.
                            if n < r.size {
                                (r.size, r.seed, r.group) = (n, seed, group);
                            }
                        }
                    }
                }
            }
            Admission::Other(_) => failures.push((seed, group)),
        }
    }
    eprintln!("{name}: {tally:?}");
    for (
        arm,
        Refused {
            count, seed, group, ..
        },
    ) in &refused
    {
        let small = shrink(group, |g| false_rejection(g) == Some(*arm));
        eprintln!(
            "{name}: {count} false rejections by the arm {arm}; smallest, seed {seed}, shrunk: {}",
            show(&small)
        );
    }
    let report: Vec<String> = failures
        .iter()
        .map(|(seed, group)| {
            let kind = failure(group);
            let small = shrink(group, |g| failure(g) == kind);
            format!(
                "seed {seed}: {}\n  shrunk: {}\n  {}",
                show(group),
                show(&small),
                explain(&small)
            )
        })
        .collect();
    assert!(report.is_empty(), "{name}:\n{}", report.join("\n"));
    assert!(
        tally.accepted > 0 && tally.not_monotone > 0,
        "{name}: the sweep reaches both answers: {tally:?}"
    );
    assert!(
        tally.false_rejections <= max_false,
        "{name}: more false rejections than recorded: {tally:?}"
    );
}

// Each sweep is a piece of the seeds, sized to finish well under 60 s.

#[test]
fn random_groups_admitted_are_monotone_0() {
    sweep("sweep0", 0..25_000, 14_200);
}

#[test]
fn random_groups_admitted_are_monotone_1() {
    sweep("sweep1", 25_000..50_000, 14_263);
}

// ---------------------------------------------------------------------------------------------
// Corners and the evaluator
// ---------------------------------------------------------------------------------------------

fn r(i: usize) -> Box<T> {
    Box::new(T::Ref(i))
}

fn b(t: T) -> Box<T> {
    Box::new(t)
}

fn exact(k: Box<T>, v: Box<T>) -> T {
    T::Mor(k.clone(), k, v)
}

/// The prototype's named groups (`xs_proto`, `head_flipped_misses_counterexamples_and_fixed_
/// catches_them` and `separating_examples_and_flipped_complete_verify`): the evaluator calls
/// each not monotone, and the check refuses each.
#[test]
fn the_prototypes_groups_are_not_monotone_and_refused() {
    let f = || b(exact(b(T::Empty), b(T::Int)));
    let m2 = T::And(b(exact(r(0), b(T::Int))), f());
    let groups = vec![
        ("M1", vec![T::Mor(r(0), b(T::Empty), b(T::Int))]),
        ("M2", vec![m2.clone()]),
        (
            "M3",
            vec![T::Diff(
                b(exact(r(0), b(T::Int))),
                b(T::Diff(b(T::Mor(b(T::Empty), b(T::Top), b(T::Int))), f())),
            )],
        ),
        ("M4", vec![T::Pair(b(T::Int), b(m2))]),
        (
            "M5_ref",
            vec![
                exact(r(1), b(T::Int)),
                T::Pair(b(T::Int), b(T::And(r(0), f()))),
            ],
        ),
        (
            "M6_dom",
            vec![T::Mor(f(), b(exact(r(0), b(T::Int))), b(T::Int))],
        ),
    ];
    for (name, group) in groups {
        assert!(monotone(&group).is_err(), "{name}: {}", show(&group));
        assert!(
            matches!(admission(&group), Admission::Refused(_)),
            "{name}: {}",
            show(&group)
        );
    }
}

/// Groups of one definition the check accepts, each monotone: a list, a function from the
/// group to `int`, and a function from `int` to the group.
#[test]
fn one_member_groups_accepted_are_monotone() {
    let groups = vec![
        vec![T::Or(b(T::Int), b(T::Pair(b(T::Int), r(0))))],
        vec![exact(r(0), b(T::Int))],
        vec![exact(b(T::Int), r(0))],
    ];
    for group in groups {
        assert_eq!(admission(&group), Admission::Accepted, "{}", show(&group));
        assert!(monotone(&group).is_ok(), "{}", show(&group));
    }
}

/// A group with no definitions is accepted and has no types; `Group::new` indexed the first
/// definition before and panicked.
#[test]
fn the_empty_group_is_accepted() {
    let g = Group::new(vec![]).expect("a group with no definitions is accepted");
    assert!(g.instance(vec![]).is_empty());
    assert!(monotone(&[]).is_ok());
}

/// The evaluator calls `R0 = _ \ (int, R0)` not monotone: from no witnesses `R0` gains the pair,
/// which removes the pair. `int \ (int, R0)` is `int` whatever `R0` is, since the integer and
/// the pair are two witnesses.
#[test]
fn the_evaluator_sees_a_flip() {
    let loses = vec![T::Diff(b(T::Top), b(T::Pair(b(T::Int), r(0))))];
    assert!(matches!(monotone(&loses), Err(Flip::Loses(0))));
    let int_only = vec![T::Diff(b(T::Int), b(T::Pair(b(T::Int), r(0))))];
    assert!(monotone(&int_only).is_ok());
    // `R0 = (R0 .. _ -> int) \ ((!_) -> int)`: at `s` empty the function on the empty domain
    // is removed and the inhabited one is in; at `s` full the guarantee `R0` is inhabited
    // and the inhabited function is in too. Monotone.
    let fine = vec![T::Diff(
        b(T::Mor(r(0), b(T::Top), b(T::Int))),
        b(exact(b(T::Empty), b(T::Int))),
    )];
    assert!(monotone(&fine).is_ok());
}

// ---------------------------------------------------------------------------------------------
// Scaling
// ---------------------------------------------------------------------------------------------

/// A ring of `n` definitions the check accepts: `R(i) = (int, R(i+1)) | ((R(i+1)) -> int)`.
fn ring(n: usize) -> Vec<Def> {
    (0..n)
        .map(|i| {
            let next = Expr::Ref((i + 1) % n, vec![]);
            Def {
                name: format!("R{i}"),
                params: vec![],
                body: Expr::Union(vec![
                    Expr::Tuple(vec![Expr::Type(Type::int()), next.clone()]),
                    Expr::exact(next, Expr::Type(Type::int())),
                ]),
            }
        })
        .collect()
}

/// A balanced union of `n` types, each a pair or a morphism type of the group's three
/// definitions.
fn wide(n: usize) -> Vec<T> {
    let leaf = |i: usize| match i % 3 {
        0 => T::Pair(b(T::Int), r(i % 3)),
        1 => exact(r(i % 3), b(T::Int)),
        _ => T::And(b(T::Top), b(T::Pair(r(i % 3), b(T::Int)))),
    };
    let mut layer: Vec<T> = (0..n).map(leaf).collect();
    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        let mut it = layer.into_iter();
        while let Some(a) = it.next() {
            next.push(match it.next() {
                Some(c) => T::Or(b(a), b(c)),
                None => a,
            });
        }
        layer = next;
    }
    let body = layer.pop().unwrap_or(T::Empty);
    vec![body.clone(), body.clone(), body]
}

mod bench;
