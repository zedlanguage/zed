//! The walk's one pass against the walk and transfer it replaced (PA-if-shortcut-diff).
//!
//! Since PA-bind-cost the walk finds the value of a bound term in the same pass that finds its
//! arms: an `if` with a literal in each arm, as in
//!
//! ```text
//! z = if x > 2 { 1 } else { 5 };
//! ```
//!
//! takes its value from the arms the walk reached (`1` where `x > 2` can hold, `5` where it
//! can fail), with no second reading of the test; before, the forward transfer read the test
//! again, with no premise. And the reduction of a bound product stops when no meet reports a
//! change, where before it compared the product with a copy taken before each round.
//!
//! `one_pass_and_transfer_agree_on_random_blocks_*` build seeded random blocks of bindings
//! over integers `x` and `y`, with literal-armed `if`s bound directly, nested in the arms of
//! other `if`s (where the walk's scopes carry the outer tests as premises), inside inner
//! blocks and under arithmetic, and check that both walks give the same arms, scopes and
//! value. `the_change_flag_matches_a_comparison` checks the flag against the comparison on
//! random products whose domains disagree.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::provenance::{FactAddress, NodeAddress, Position, Vector};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::affine::Bounds;
use zedc::store::cell::{Premise, Premises};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::{Congruence, FiniteSet};
use zedc::store::product::{Arm, Product, arms_and_value, arms_and_value_by_transfer};

use super::ints;

fn var(n: &str) -> Term {
    Term::Var(n.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

fn if_(c: Term, a: Term, b: Term) -> Term {
    Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
}

fn let_(x: &str, e: Term, b: Term) -> Term {
    Term::Let(x.into(), Shared::new(e), Shared::new(b))
}

/// Random blocks over the integer names in scope.
struct Gen {
    rng: Rng,
    /// The number of names bound so far, for fresh names.
    fresh: u32,
    /// The number of `if`s with a literal in each arm made so far.
    shortcuts: usize,
}

impl Gen {
    /// An integer name in scope or a small literal.
    fn atom(&mut self, names: &[Arc<str>]) -> Term {
        if self.rng.below(3) == 0 {
            int(self.rng.int(-4, 4))
        } else {
            Term::Var(self.rng.pick(names))
        }
    }

    /// An integer term the narrowing reads: a name or literal, a sum, a difference or a
    /// remainder.
    fn operand(&mut self, names: &[Arc<str>]) -> Term {
        match self.rng.below(6) {
            0 => prim(Prim::Add, vec![self.atom(names), self.atom(names)]),
            1 => prim(Prim::Sub, vec![self.atom(names), self.atom(names)]),
            2 => prim(Prim::Mod, vec![self.atom(names), int(self.rng.int(2, 4))]),
            _ => self.atom(names),
        }
    }

    /// A test over the names in scope, its literals small so that nested tests often leave an
    /// arm unreachable.
    fn test(&mut self, names: &[Arc<str>], d: u32) -> Term {
        if d == 0 || self.rng.below(3) != 0 {
            let op = self
                .rng
                .pick(&[Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge, Prim::Eq, Prim::Ne]);
            return prim(op, vec![self.operand(names), self.atom(names)]);
        }
        match self.rng.below(3) {
            0 => prim(Prim::Not, vec![self.test(names, d - 1)]),
            1 => prim(
                Prim::And,
                vec![self.test(names, d - 1), self.test(names, d - 1)],
            ),
            _ => prim(
                Prim::Or,
                vec![self.test(names, d - 1), self.test(names, d - 1)],
            ),
        }
    }

    /// A literal for an arm: an integer, or with `any`, also a string or a boolean.
    fn lit(&mut self, any: bool) -> Value {
        match if any { self.rng.below(4) } else { 0 } {
            1 => Value::str(self.rng.pick(&["a", "b"])),
            2 => Value::Bool(self.rng.below(2) == 0),
            _ => Value::Int(self.rng.int(-3, 6)),
        }
    }

    /// A term bound to a name or in an arm, and whether its value is an integer.
    fn value(&mut self, names: &[Arc<str>], d: u32) -> (Term, bool) {
        let choice = if d == 0 {
            self.rng.below(2)
        } else {
            self.rng.below(9)
        };
        match choice {
            // The shortcut's own case, most often: a literal in each arm.
            0 | 2 | 3 => {
                let any = self.rng.below(4) == 0;
                let (a, b) = (self.lit(any), self.lit(any));
                let is_int = matches!((&a, &b), (Value::Int(_), Value::Int(_)));
                self.shortcuts += 1;
                let t = if_(self.test(names, 1), Term::Lit(a), Term::Lit(b));
                (t, is_int)
            }
            1 => (self.operand(names), true),
            // Arithmetic over values, each of which may hold the shortcut.
            4 => {
                let a = self.int_value(names, d - 1);
                let b = self.int_value(names, d - 1);
                let op = self.rng.pick(&[Prim::Add, Prim::Sub, Prim::Min, Prim::Max]);
                (prim(op, vec![a, b]), true)
            }
            // An `if` whose arms are not literals: its arms are walked under its test's
            // premise, so a literal-armed `if` bound inside them is read under it.
            5 | 6 => {
                let c = self.test(names, 1);
                let (a, ai) = self.value(names, d - 1);
                let (b, bi) = self.value(names, d - 1);
                (if_(c, a, b), ai && bi)
            }
            // An inner block.
            _ => self.block(names, d - 1),
        }
    }

    /// [`Gen::value`] whose value is an integer.
    fn int_value(&mut self, names: &[Arc<str>], d: u32) -> Term {
        loop {
            let (t, is_int) = self.value(names, d);
            if is_int {
                return t;
            }
        }
    }

    /// A block of one to three bindings and a last term, each bound name in scope after it
    /// when its value is an integer.
    fn block(&mut self, names: &[Arc<str>], d: u32) -> (Term, bool) {
        let mut scope = names.to_vec();
        let mut bound = Vec::new();
        for _ in 0..self.rng.int(1, 3) {
            let (e, is_int) = self.value(&scope, d);
            self.fresh += 1;
            let x: Arc<str> = format!("z{}", self.fresh).into();
            if is_int {
                scope.push(x.clone());
            }
            bound.push((x, e));
        }
        // The last term reads the bound names, so a value that differs shows in its arms.
        let (last, is_int) = if self.rng.below(2) == 0 {
            let c = self.test(&scope, 1);
            self.shortcuts += 1;
            (if_(c, int(1), int(2)), true)
        } else {
            self.value(&scope, d)
        };
        let t = bound.into_iter().rev().fold(last, |b, (x, e)| {
            Term::Let(x, Shared::new(e), Shared::new(b))
        });
        (t, is_int)
    }
}

/// What differs between two walks' arms and values, if anything.
fn difference((a, p): &(Vec<Arm>, Product), (b, q): &(Vec<Arm>, Product)) -> Option<String> {
    if a.len() != b.len() {
        return Some(format!("{} arms against {}", a.len(), b.len()));
    }
    for (i, (x, y)) in a.iter().zip(b).enumerate() {
        if x.guard != y.guard || x.outcome != y.outcome {
            return Some(format!(
                "arm {i}: `{}` is {} against `{}` is {}",
                x.guard, x.outcome, y.guard, y.outcome
            ));
        }
        if x.scope.bottom != y.scope.bottom
            || x.scope.names != y.scope.names
            || x.scope.to_string() != y.scope.to_string()
            || x.scope.written.keys().collect::<Vec<_>>()
                != y.scope.written.keys().collect::<Vec<_>>()
        {
            return Some(format!(
                "arm {i} (`{}` is {}): scope\n{}against\n{}{:#?}\nagainst\n{:#?}",
                x.guard, x.outcome, x.scope, y.scope, x.scope.names, y.scope.names
            ));
        }
    }
    if p != q || p.to_string() != q.to_string() {
        return Some(format!("value {p:?} against {q:?}"));
    }
    None
}

/// The one pass and the transfer agree on [`BLOCKS`] random blocks, with a new seed each run
/// (author P169; 8,000 seeds agreed when the test was written, and until TEST-bench-move-l0139
/// it ran the seeds 0 to 799, one block each, in four tests of about 6.5 s at load 30).
#[test]
fn one_pass_and_transfer_agree_on_random_blocks() {
    let names: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let scope = ints(&names);
    let (rng, seed) = Rng::fresh("one_pass_and_transfer_agree_on_random_blocks");
    let mut g = Gen {
        rng,
        fresh: 0,
        shortcuts: 0,
    };
    let mut unreached = 0;
    for block in 0..BLOCKS {
        let (t, _) = g.block(&names, 3);
        let one = arms_and_value(&t, &scope);
        let two = arms_and_value_by_transfer(&t, &scope);
        if let Some(d) = difference(&one, &two) {
            panic!("seed {seed}, block {block}: the one pass and the transfer differ on\n{t}\n{d}");
        }
        unreached += one.0.iter().filter(|a| !a.reachable()).count();
    }
    // The blocks hold literal-armed `if`s and reach arms of both kinds, so both of the
    // shortcut's cases, an arm reached and an arm not, are compared.
    let shortcuts = g.shortcuts;
    eprintln!("seed {seed}: {shortcuts} literal-armed ifs, {unreached} unreachable arms");
    assert!(
        shortcuts > 2 * BLOCKS,
        "seed {seed}: {shortcuts} literal-armed ifs in {BLOCKS} blocks"
    );
    assert!(
        unreached > BLOCKS / 2,
        "seed {seed}: {unreached} unreachable arms in {BLOCKS} blocks"
    );
}

/// The random blocks [`one_pass_and_transfer_agree_on_random_blocks`] compares in a run.
const BLOCKS: usize = 20;

/// A literal-armed `if` under a test that decides it, in each of the places the walk takes
/// the shortcut: bound directly, inside an inner block, under arithmetic and in a nested arm.
#[test]
fn one_pass_and_transfer_agree_where_an_outer_test_decides_the_inner_one() {
    let scope = ints(&["x".into()]);
    let gt = |n| prim(Prim::Gt, vec![var("x"), int(n)]);
    let lit_if = |n| if_(gt(n), int(1), int(5));
    let read = |b: Term| {
        let_(
            "z",
            b,
            if_(prim(Prim::Eq, vec![var("z"), int(5)]), int(0), int(1)),
        )
    };
    let cases = [
        // Bound directly, in an arm in which `x > 2` cannot hold.
        (if_(gt(2), int(0), read(lit_if(2))), true),
        // Inside an inner block, where `x > 1` always holds.
        (
            if_(gt(2), read(let_("w", lit_if(1), var("w"))), int(0)),
            true,
        ),
        // Under arithmetic, the first `if` decided and the second not.
        (
            if_(
                gt(2),
                int(0),
                read(prim(Prim::Add, vec![lit_if(4), lit_if(-10)])),
            ),
            true,
        ),
        // Nested in the arms of an `if` whose arms are not literals, each decided there.
        (
            read(if_(gt(0), lit_if(-1), let_("w", lit_if(0), var("w")))),
            true,
        ),
        // A string and an integer, both reached.
        (
            let_(
                "s",
                if_(gt(0), Term::Lit(Value::str("a")), int(1)),
                var("s"),
            ),
            false,
        ),
    ];
    for (t, decided) in cases {
        let one = arms_and_value(&t, &scope);
        let two = arms_and_value_by_transfer(&t, &scope);
        if let Some(d) = difference(&one, &two) {
            panic!("{t}\n{d}");
        }
        // An `if` decided by the test around it has an arm no state reaches.
        assert_eq!(
            one.0.iter().any(|a| !a.reachable()),
            decided,
            "{t}: {:#?}",
            one.0
        );
    }
}

/// The fact at node `n`.
fn because(n: u32) -> Premises {
    Premises::one(Premise::Constraint(FactAddress {
        node: NodeAddress(Vector::from(vec![
            Position::root(),
            Position::root().child(n),
        ])),
        keypath: Vector::new(),
    }))
}

/// A product whose type, interval, class and finite set are drawn apart, so that the
/// reductions between them have work to do.
fn random_product(rng: &mut Rng) -> Product {
    let mut p = Product::top();
    let lit = |v: Value| Type::lit(&v).expect("a literal type");
    p.ty.element = match rng.below(6) {
        0 => Type::int(),
        1 => Type::top(),
        2 => Type::union_all((0..rng.int(1, 4)).map(|_| lit(Value::Int(rng.int(-4, 6))))),
        3 => Type::int() | lit(Value::str("a")),
        4 => lit(Value::Int(rng.int(-2, 2))) | lit(Value::str("b")),
        _ => Type::bool(),
    };
    p.cell.ints.element = Bounds::ints(match rng.below(4) {
        0 => IntervalSet::top(),
        _ => IntervalSet::from_pieces(
            (0..rng.int(1, 3))
                .map(|_| {
                    let lo = rng.int(-8, 6);
                    let hi = lo + rng.int(0, 5);
                    (End::of(lo), End::of(hi))
                })
                .collect(),
        ),
    });
    p.cell.congruence.element = match rng.below(8) {
        0 => Congruence::Bottom,
        1..=3 => Congruence::new(1, 0),
        4 => Congruence::single(rng.int(-3, 3)),
        _ => Congruence::new(rng.int(2, 4), rng.int(0, 3)),
    };
    p.cell.finite.element = match rng.below(3) {
        0 => FiniteSet::Top,
        _ => FiniteSet::Set(
            (0..rng.int(0, 4))
                .map(|_| match rng.below(4) {
                    0 => Value::str("a"),
                    _ => Value::Int(rng.int(-5, 7)),
                })
                .collect::<BTreeSet<Value>>(),
        ),
    };
    p.cell.ints.premises = because(1);
    p.cell.congruence.premises = because(2);
    p.cell.finite.premises = because(3);
    p.ty.premises = because(4);
    p
}

/// Over [`PRODUCTS`] random products, with a new seed each run (author P169; was 20,000 of the
/// seed 7, 1.3 s at load 30).
#[test]
fn the_change_flag_matches_a_comparison() {
    let (mut rng, seed) = Rng::fresh("the_change_flag_matches_a_comparison");
    let mut changed = 0;
    for i in 0..PRODUCTS {
        let start = random_product(&mut rng);
        // As the reduction does now: until no meet reports a change.
        let mut flagged = start.clone();
        let mut rounds = 0;
        while flagged.reduce_domains_once() {
            rounds += 1;
            assert!(
                rounds < 64,
                "seed {seed}, product {i} did not settle: {start:?}"
            );
        }
        // As it did before: until a round leaves the product equal to a copy taken before
        // it, and each round's flag says whether the round changed it.
        let mut compared = start.clone();
        loop {
            let before = compared.clone();
            let flag = compared.reduce_domains_once();
            let moved = compared != before;
            assert_eq!(
                flag, moved,
                "seed {seed}, product {i}: the flag says {flag} where the round went from\n{before:?}\nto\n{compared:?}"
            );
            if !moved {
                break;
            }
        }
        assert_eq!(
            flagged, compared,
            "seed {seed}, product {i}, from {start:?}"
        );
        changed += usize::from(flagged != start);
    }
    eprintln!("seed {seed}: {changed} of {PRODUCTS} products changed");
    assert!(
        changed > PRODUCTS / 2,
        "seed {seed}: {changed} products changed"
    );
}

/// The random products [`the_change_flag_matches_a_comparison`] reduces in a run.
const PRODUCTS: usize = 4_000;

/// A term `d` deep over the integer `x`, of one of five forms, each level `k` built around
/// the one below, `t`:
///
/// 0. a block bound inside a bound block, `z_k = { t }; z_k + 1`;
/// 1. an `if` whose arms are not literals, bound in the arm of another,
///    `if x > k { z_k = t; z_k } else { x }`;
/// 2. a literal-armed `if` bound in each nested arm,
///    `if x > k { z_k = if x > k + 1 { 1 } else { 2 }; t } else { x }`;
/// 3. a chain of literal-armed `if`s bound one after another,
///    `z_k = if x > k { 1 } else { 2 }; t`;
/// 4. `if`s nested in arms, `if x > k { t } else { x }`.
fn nest(form: u8, d: i64) -> Term {
    let gt = |n| prim(Prim::Gt, vec![var("x"), int(n)]);
    (0..d).fold(var("x"), |t, k| {
        let z = format!("z{k}");
        match form {
            0 => let_(&z, t, prim(Prim::Add, vec![var(&z), int(1)])),
            1 => if_(gt(k), let_(&z, t, var(&z)), var("x")),
            2 => if_(gt(k), let_(&z, if_(gt(k + 1), int(1), int(2)), t), var("x")),
            3 => let_(&z, if_(gt(k), int(1), int(2)), t),
            _ => if_(gt(k), t, var("x")),
        }
    })
}

/// The five forms of [`nest`], deep: the random blocks are at most three deep. (Until
/// TEST-bench-move-l0139 twice these depths, 0.55 to 0.75 s at load 32.)
#[test]
fn one_pass_and_transfer_agree_on_deep_nests() {
    let scope = ints(&["x".into()]);
    for (form, d) in [(0, 32), (1, 16), (2, 64), (3, 128), (4, 128)] {
        let t = nest(form, d);
        let one = arms_and_value(&t, &scope);
        if let Some(diff) = difference(&one, &arms_and_value_by_transfer(&t, &scope)) {
            panic!("form {form}, {d} deep: {diff}");
        }
    }
}

/// A chain of [`CHAIN`] bindings `z_k = z_(k-1) + 1`, read by one test at the end, makes each
/// summary when the test reads it, the bindings before it first, on an explicit stack; read
/// by none, it keeps a chain of scopes, which is dropped by a loop (`Lazy` and `Basis` in
/// `product.rs`). Neither recurses down the chain: on a thread of [`CHAIN_STACK`] bytes (on
/// 64 KiB it overflowed at every depth tried, from the stack it takes whatever the depth), the
/// walk passed at 2,000, 10,000 and 30,000 links, so its stack does not grow with the chain,
/// and a walk that took over 66 bytes of stack a link overflows at 4,000 links. Until
/// TEST-bench-move-l0139 (author P169) the chain was 100,000 links long on the test thread's
/// stack, 9.6 s at load 30.
#[test]
fn a_deep_chain_of_bindings_is_walked_and_dropped() {
    std::thread::Builder::new()
        .stack_size(CHAIN_STACK)
        .spawn(|| {
            let scope = ints(&["x".into()]);
            let d = CHAIN;
            let z = |k: i64| {
                if k < 0 {
                    "x".to_string()
                } else {
                    format!("z{k}")
                }
            };
            for read in [&z(d - 1), "x"] {
                let last = if_(prim(Prim::Gt, vec![var(read), int(3)]), int(1), int(2));
                let t = (0..d).rev().fold(last, |b, k| {
                    let_(&z(k), prim(Prim::Add, vec![var(&z(k - 1)), int(1)]), b)
                });
                let (arms, _) = arms_and_value(&t, &scope);
                assert_eq!(arms.len(), 2);
            }
        })
        .expect("a test thread")
        .join()
        .expect("the chain is walked and dropped on a 256 KiB stack");
}

/// The links of the chain of [`a_deep_chain_of_bindings_is_walked_and_dropped`], and the stack
/// it runs on.
const CHAIN: i64 = 4_000;
const CHAIN_STACK: usize = 256 << 10;

mod bench;
