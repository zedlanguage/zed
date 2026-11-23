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
    let (rng, seed) = Rng::fresh("one_pass_and_transfer_agree_on_random_blocks");
    blocks_agree(rng, seed);
}

/// Seed 13376472606931704830 of [`one_pass_and_transfer_agree_on_random_blocks`]: at block 11
/// the one pass and the transfer differed at arm 5 (`((-2 - z103) < x)` false), the one pass
/// giving `x` the ints `[..=-4]` and the transfer `[..=-3]`, where `z103` is
/// `if (-2 == min(x, x)) { 1 } else { 2 }`: the guard's preimage under `min` of two copies of
/// `x` was not exact, so the transfer had no summary of `z103` (FAIL-if-shortcut-seed-
/// 13376472606931704830).
#[test]
fn one_pass_and_transfer_agree_at_seed_13376472606931704830() {
    blocks_agree(
        Rng::new(13_376_472_606_931_704_830),
        13_376_472_606_931_704_830,
    );
}

/// Seed 108049985492391682 of [`one_pass_and_transfer_agree_on_random_blocks`]
/// (FAIL-if-shortcut-seed-13376472606931704830, its second seed).
#[test]
fn one_pass_and_transfer_agree_at_seed_108049985492391682() {
    blocks_agree(Rng::new(108_049_985_492_391_682), 108_049_985_492_391_682);
}

/// Seed 16483970003272068920 of [`one_pass_and_transfer_agree_on_random_blocks`]: at block 9,
/// arm 10, the one pass gave `x` the ints `[4..]` and the transfer `[5..]`, the block of
/// [`a_peeled_body_with_no_summary_is_read_whole`]
/// (FAIL-if-shortcut-seed-16483970003272068920).
#[test]
fn one_pass_and_transfer_agree_at_seed_16483970003272068920() {
    blocks_agree(
        Rng::new(16_483_970_003_272_068_920),
        16_483_970_003_272_068_920,
    );
}

/// Seed 2973454876123146566 of [`one_pass_and_transfer_agree_on_random_blocks`]: on main
/// 6f8d50039, at block 18, arm 7 (`!(z107 < x)` false), with `z107` in `[1..=2]` and the relation
/// `x >= z107 + 1`, one side gave `x` the ints `[2..]` and the other `[3..]`; it agrees after main
/// 585e5f0ec (FAIL-if-shortcut-seed-2973454876123146566).
#[test]
fn one_pass_and_transfer_agree_at_seed_2973454876123146566() {
    blocks_agree(
        Rng::new(2_973_454_876_123_146_566),
        2_973_454_876_123_146_566,
    );
}

/// The block of seed 16483970003272068920, cut down:
/// `z52 = { z48 = -3; if (z48 mod 2) >= x { 1 } else { 2 } }; if (z52 - -3) <= x && (0 + x) != y
/// { 0 } else { 2 }`. The one pass peels `z52`; its body, which reads `z48` through `z48`'s
/// summary, had none, so the test read `z52` as `[1..=2]` and gave `x` the ints `[4..]` where it
/// holds; the transfer reads the whole block, `1` for `x <= 1` and `2` above, and gives `[5..]`.
#[test]
fn a_peeled_body_with_no_summary_is_read_whole() {
    let p = |op, a, b| prim(op, vec![a, b]);
    let t = let_(
        "z52",
        let_(
            "z48",
            int(-3),
            if_(
                p(Prim::Ge, p(Prim::Mod, var("z48"), int(2)), var("x")),
                int(1),
                int(2),
            ),
        ),
        if_(
            p(
                Prim::And,
                p(Prim::Le, p(Prim::Sub, var("z52"), int(-3)), var("x")),
                p(Prim::Ne, p(Prim::Add, int(0), var("x")), var("y")),
            ),
            int(0),
            int(2),
        ),
    );
    let scope = ints(&["x".into(), "y".into()]);
    let one = arms_and_value(&t, &scope);
    if let Some(d) = difference(&one, &arms_and_value_by_transfer(&t, &scope)) {
        panic!("the one pass and the transfer differ on\n{t}\n{d}");
    }
}

/// The block of seed 13376472606931704830 and its neighbors: `z103` bound to
/// `if (-2 == z102) { 1 } else { 2 }` for `z102` each of `min(x, x)`, `max(x, x)`, `min(x, 3)`,
/// `min(x, y)`, `x + 0` and `x * 1`, then a test of `x` against `-2 - z103`. The one pass and
/// the transfer agree on each; before the fix the two of `min(x, x)` and `max(x, x)` differed
/// (`x` in `[..=-4]` against `[..=-3]` where the test fails).
#[test]
fn one_pass_and_transfer_agree_on_min_and_max_of_one_name_under_a_test() {
    let p = |op, a, b| prim(op, vec![a, b]);
    let outer = |z102: Term, test: Term| {
        let_(
            "z103",
            let_("z102", z102, if_(test, int(1), int(2))),
            if_(
                p(Prim::Lt, p(Prim::Sub, int(-2), var("z103")), var("x")),
                int(1),
                int(2),
            ),
        )
    };
    let eq = || p(Prim::Eq, int(-2), var("z102"));
    let scope = ints(&["x".into(), "y".into()]);
    let cases = [
        ("min xx", outer(p(Prim::Min, var("x"), var("x")), eq())),
        ("max xx", outer(p(Prim::Max, var("x"), var("x")), eq())),
        ("min x3", outer(p(Prim::Min, var("x"), int(3)), eq())),
        ("min xy", outer(p(Prim::Min, var("x"), var("y")), eq())),
        ("x+0", outer(p(Prim::Add, var("x"), int(0)), eq())),
        ("x*1", outer(p(Prim::Mul, var("x"), int(1)), eq())),
    ];
    for (name, t) in cases {
        let one = arms_and_value(&t, &scope);
        let two = arms_and_value_by_transfer(&t, &scope);
        if let Some(d) = difference(&one, &two) {
            panic!("{name}: the one pass and the transfer differ on\n{t}\n{d}");
        }
    }
}

/// The one pass and the transfer agree on [`BLOCKS`] blocks drawn from `rng`; `seed` names the
/// run in the message of a difference.
fn blocks_agree(rng: Rng, seed: u64) {
    let names: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let scope = ints(&names);
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
    // Both of the shortcut's cases, a literal-armed `if` with an arm reached and one with an arm
    // no state reaches, are compared in every run by the blocks built for them in
    // `one_pass_and_transfer_agree_where_an_outer_test_decides_the_inner_one`, whatever the
    // draws gave (PROOF-test-count-thresholds; until 2026-11-15 this test asserted more than 40
    // literal-armed `if`s and 10 unreachable arms over its 20 blocks).
    let shortcuts = g.shortcuts;
    eprintln!("seed {seed}: {shortcuts} literal-armed ifs, {unreached} unreachable arms");
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
        _ => FiniteSet::of((0..rng.int(0, 4)).map(|_| match rng.below(4) {
            0 => Value::str("a"),
            _ => Value::Int(rng.int(-5, 7)),
        })),
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
        changed += usize::from(flag_checked(&start, &format!("seed {seed}, product {i}")));
    }
    eprintln!("seed {seed}: {changed} of {PRODUCTS} products changed");
    // The draws may change no product, so the product built below changes in every run
    // (PROOF-test-count-thresholds; until 2026-11-15 the test asserted that more than half of
    // its 4,000 products changed). Its interval `[0..5]` holds the even 0, 2 and 4, which its
    // class, the odd integers, rules out, so the reduction narrows the interval to `[1..5]`.
    let mut built = Product::top();
    built.ty.element = Type::int();
    built.cell.ints.element =
        Bounds::ints(IntervalSet::from_pieces(vec![(End::of(0), End::of(5))]));
    built.cell.congruence.element = Congruence::new(2, 1);
    built.cell.ints.premises = because(1);
    built.cell.congruence.premises = because(2);
    assert!(
        flag_checked(&built, "the built product"),
        "the built product does not change: {built:?}"
    );
}

/// Reduces `start` until no meet reports a change, and as before, until a round leaves the
/// product equal to a copy taken before it, each round's flag checked to say whether the round
/// changed it, and the two results checked equal (`at` names the product in a failure):
/// whether the reduction changed `start`.
fn flag_checked(start: &Product, at: &str) -> bool {
    // As the reduction does now: until no meet reports a change.
    let mut flagged = start.clone();
    let mut rounds = 0;
    while flagged.reduce_domains_once() {
        rounds += 1;
        assert!(rounds < 64, "{at} did not settle: {start:?}");
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
            "{at}: the flag says {flag} where the round went from\n{before:?}\nto\n{compared:?}"
        );
        if !moved {
            break;
        }
    }
    assert_eq!(flagged, compared, "{at}, from {start:?}");
    flagged != *start
}

/// A product whose reduction changed nothing is known settled and not reduced again
/// (CHECK-literal-union-cost), but a write to it, or to a copy that shares its domains, undoes
/// that: the copy written is reduced again, and the product it was copied from keeps its
/// domains and stays settled.
#[test]
fn a_settled_product_written_again_is_reduced_again() {
    let lit = |n: i64| Type::lit(&Value::Int(n)).unwrap();
    let mut settled = Product::of_type(Type::union_all([lit(1), lit(2), lit(3)]));
    while settled.reduce_domains_once() {}
    assert!(!settled.reduce_domains_once());
    let mut written = settled.clone();
    written.cell.ints.element =
        Bounds::ints(IntervalSet::from_pieces(vec![(End::of(2), End::of(5))]));
    assert!(written.reduce_domains_once(), "{written:?}");
    while written.reduce_domains_once() {}
    assert_eq!(written.ty.element, Type::union_all([lit(2), lit(3)]));
    assert_eq!(
        written.cell.finite.element,
        FiniteSet::of([Value::Int(2), Value::Int(3)])
    );
    assert_eq!(
        settled.ty.element,
        Type::union_all([lit(1), lit(2), lit(3)])
    );
    assert!(!settled.reduce_domains_once());
    // Written in place, with no copy sharing its domains.
    let mut alone = written;
    alone.cell.ints.element =
        Bounds::ints(IntervalSet::from_pieces(vec![(End::of(3), End::of(3))]));
    assert!(alone.reduce_domains_once(), "{alone:?}");
    while alone.reduce_domains_once() {}
    assert_eq!(alone.ty.element, lit(3));
}

/// The random products [`the_change_flag_matches_a_comparison`] reduces in a run.
const PRODUCTS: usize = 4_000;

/// A term `d` deep over the integer `x`, of one of seven forms, each level `k` built around
/// the one below, `t`:
///
/// 0. a block bound inside a bound block, `z_k = { t }; z_k + 1`;
/// 1. an `if` whose arms are not literals, bound in the arm of another,
///    `if x > k { z_k = t; z_k } else { x }`;
/// 2. a literal-armed `if` bound in each nested arm,
///    `if x > k { z_k = if x > k + 1 { 1 } else { 2 }; t } else { x }`;
/// 3. a chain of literal-armed `if`s bound one after another,
///    `z_k = if x > k { 1 } else { 2 }; t`;
/// 4. `if`s nested in arms, `if x > k { t } else { x }`;
/// 5. a block bound inside a bound block whose name a test reads,
///    `z_k = { t }; if z_k > k { z_k + 1 } else { z_k }` (item PA-walk-read-all);
/// 6. form 5 with the test `z_k > 3k`, whose cuts move with the level, so the value of a
///    level has `Θ(k)` pieces (review XR-algos, Codex round 1: "the positive thresholds are
///    now separated by two integers").
fn nest(form: u8, d: i64) -> Term {
    let gt = |n| prim(Prim::Gt, vec![var("x"), int(n)]);
    (0..d).fold(var("x"), |t, k| {
        let z = format!("z{k}");
        match form {
            0 => let_(&z, t, prim(Prim::Add, vec![var(&z), int(1)])),
            1 => if_(gt(k), let_(&z, t, var(&z)), var("x")),
            2 => if_(gt(k), let_(&z, if_(gt(k + 1), int(1), int(2)), t), var("x")),
            3 => let_(&z, if_(gt(k), int(1), int(2)), t),
            5 | 6 => {
                let read = if_(
                    prim(
                        Prim::Gt,
                        vec![var(&z), int(if form == 5 { k } else { 3 * k })],
                    ),
                    prim(Prim::Add, vec![var(&z), int(1)]),
                    var(&z),
                );
                let_(&z, t, read)
            }
            _ => if_(gt(k), t, var("x")),
        }
    })
}

/// The forms of [`nest`], deep: the random blocks are at most three deep. Forms 5 and 6
/// compare the one pass, which reads a block's summary from its body's, with the transfer,
/// which summarizes each whole (`Lazy::get` in `product.rs`, item PA-walk-read-all). (Until
/// TEST-bench-move-l0139 twice these depths, 0.55 to 0.75 s at load 32.)
#[test]
fn one_pass_and_transfer_agree_on_deep_nests() {
    let scope = ints(&["x".into()]);
    for (form, d) in [
        (0, 32),
        (1, 16),
        (2, 64),
        (3, 128),
        (4, 128),
        (5, 32),
        (6, 32),
    ] {
        let t = nest(form, d);
        let one = arms_and_value(&t, &scope);
        if let Some(diff) = difference(&one, &arms_and_value_by_transfer(&t, &scope)) {
            panic!("form {form}, {d} deep: {diff}");
        }
    }
}

/// One bound block, the same shared term, `{ u = x; if u > 0 { 1 } else { 2 } }`, bound in
/// both arms of `if x > 0`: the one pass reads each binding's summary from the block's body in
/// the scope of its own arm (item PA-walk-read-all), so `z > 1` can only fail in the first arm
/// and only hold in the second (review XR-algos, Codex round 1,
/// `a_shared_rhs_is_read_in_its_own_scope`).
#[test]
fn a_shared_bound_block_is_read_in_its_own_arm() {
    let part = Shared::new(let_(
        "u",
        var("x"),
        if_(prim(Prim::Gt, vec![var("u"), int(0)]), int(1), int(2)),
    ));
    let read = |same: Shared| {
        Term::Let(
            "z".into(),
            same,
            Shared::new(if_(
                prim(Prim::Gt, vec![var("z"), int(1)]),
                int(10),
                int(20),
            )),
        )
    };
    let scope = ints(&["x".into()]);
    // Whether `z > 1` can hold and can fail where `x > 0` (the block is 1) and where `x <= 0`
    // (it is 2); the test is also written the other way round, so that a summary kept from
    // the first arm walked would be wrong in the second.
    let (pos, neg) = ([false, true], [true, false]);
    for (test, reach) in [(Prim::Gt, [pos, neg]), (Prim::Le, [neg, pos])] {
        let t = if_(
            prim(test, vec![var("x"), int(0)]),
            read(part.clone()),
            read(part.clone()),
        );
        let one = arms_and_value(&t, &scope);
        if let Some(diff) = difference(&one, &arms_and_value_by_transfer(&t, &scope)) {
            panic!("{t}: {diff}");
        }
        let z_test = prim(Prim::Gt, vec![var("z"), int(1)]).to_string();
        let inner: Vec<_> = (one.0.iter())
            .filter(|a| a.guard == z_test)
            .map(|a| (a.outcome, a.reachable()))
            .collect();
        let expected: Vec<_> = (reach.iter())
            .flat_map(|r| [(true, r[0]), (false, r[1])])
            .collect();
        assert_eq!(inner, expected, "{t}");
    }
}

/// A bound block `z = { y = e'; b }` read by a test, for bodies `b` that the summary of the
/// whole block and the summary of `b` read through `y`'s (item PA-walk-read-all) treat by
/// different code paths: `y` cancelled in a sum, `y` doubled, `y` shadowing the input, a
/// `mod`, an `if` in the body, and a block in an arm that rules out a branch of `e'` (review
/// XR-algos, Gemini round 1, "Five subtle exactness traps"). The one pass and the transfer,
/// which does not peel, give the same arms and value.
#[test]
fn a_peeled_block_agrees_with_the_whole_block_on_awkward_bodies() {
    let p = |op, a, b| prim(op, vec![a, b]);
    let (x, y) = (|| var("x"), || var("y"));
    let read = |block: Term, test: Prim, k: i64| {
        let_("z", block, if_(p(test, var("z"), int(k)), int(1), int(2)))
    };
    let cases = [
        read(
            let_("y", x(), p(Prim::Sub, p(Prim::Add, y(), x()), y())),
            Prim::Gt,
            0,
        ),
        read(let_("y", x(), p(Prim::Add, y(), y())), Prim::Eq, 1),
        read(
            let_("x", p(Prim::Add, x(), int(1)), p(Prim::Add, x(), x())),
            Prim::Gt,
            2,
        ),
        read(
            let_("y", p(Prim::Mod, x(), int(3)), p(Prim::Add, y(), int(1))),
            Prim::Gt,
            1,
        ),
        read(
            let_(
                "y",
                x(),
                if_(p(Prim::Gt, y(), int(0)), y(), p(Prim::Sub, int(0), y())),
            ),
            Prim::Gt,
            3,
        ),
        if_(
            p(Prim::Gt, x(), int(0)),
            read(
                let_(
                    "y",
                    if_(p(Prim::Lt, x(), int(0)), p(Prim::Mul, x(), x()), x()),
                    y(),
                ),
                Prim::Gt,
                1,
            ),
            int(0),
        ),
    ];
    let scope = ints(&["x".into()]);
    for t in cases {
        let one = arms_and_value(&t, &scope);
        if let Some(diff) = difference(&one, &arms_and_value_by_transfer(&t, &scope)) {
            panic!("{t}: {diff}");
        }
    }
}

/// A chain of `d` bindings `z_k = z_(k-1) + 1`, read by one test at the end, then read by none
/// (the test reads `x`): each has two arms. A binding's summary is made when the test reads it,
/// the bindings before it first, on an explicit stack; a chain read by none keeps a chain of
/// scopes, which is dropped by a loop (`Lazy` and `Basis` in `product.rs`).
fn walk_chain(d: i64) {
    let scope = ints(&["x".into()]);
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
        assert_eq!(arms.len(), 2, "d = {d}, the test reads {read}");
    }
}

/// [`walk_chain`] at 1, 2 and 5 links. The chain 4,000 links long on a 256 KiB stack is
/// `bench::a_deep_chain_of_bindings_is_walked_and_dropped` (author P178).
#[test]
fn a_chain_of_bindings_is_walked_and_dropped() {
    for d in [1, 2, 5] {
        walk_chain(d);
    }
}

mod bench;

/// The block of seed 108049985492391682, reduced: `z111` bound to the block
/// `{ z109 = 3; y - if (-2 <= x) { 6 } else { 1 } }`, then a test of `y mod 4 == z111`. The one
/// pass peels the block and summarizes its body over `x` and `y`, a summary the whole block
/// cannot have (one input at most, proof at `Lazy::get` in `product.rs`); reading `z111`
/// through it inverted `y - s` by the hull `[1, 6]` of `s`, which kept `y = 5` (`z111` is `-1`
/// or `4` there, and `5 mod 4` is `1`). Before the fix, on main: `y` in `[1..=9]` in the true
/// arm against the transfer's `[1..=4, 6..=9]`. The neighbors bind `z109` to an `if`, to `y`, or
/// read the block through another block, and one subtracts a literal, which peels over `y`
/// alone and must keep the peel's answer.
#[test]
fn a_peeled_block_summed_over_two_inputs_agrees_with_the_transfer() {
    let p = |op, a, b| prim(op, vec![a, b]);
    let (x, y) = (|| var("x"), || var("y"));
    let sel = || if_(p(Prim::Le, int(-2), x()), int(6), int(1));
    let z109 = |t: Term, b: Term| let_("z109", if_(t, int(3), int(3)), b);
    let yle6 = || p(Prim::Le, y(), int(6));
    let blk = || let_("z110", y(), var("z110"));
    let read = |b: Term| {
        let_(
            "z111",
            b,
            if_(
                p(Prim::Eq, p(Prim::Mod, y(), int(4)), var("z111")),
                int(1),
                int(2),
            ),
        )
    };
    let cases = [
        (
            "the reduced block",
            read(let_("z109", int(3), p(Prim::Sub, y(), sel()))),
        ),
        (
            "the seed's block",
            read(z109(yle6(), p(Prim::Sub, blk(), sel()))),
        ),
        (
            "`z109` an `if` on `y`",
            read(z109(yle6(), p(Prim::Sub, y(), sel()))),
        ),
        (
            "`z109` an `if` on `x`",
            read(z109(p(Prim::Le, x(), int(6)), p(Prim::Sub, y(), sel()))),
        ),
        (
            "`y` read through a block",
            read(let_("z109", int(3), p(Prim::Sub, blk(), sel()))),
        ),
        (
            "`z109` bound to `y`",
            read(let_("z109", y(), p(Prim::Sub, y(), sel()))),
        ),
        (
            "a literal subtracted",
            read(z109(yle6(), p(Prim::Sub, y(), int(6)))),
        ),
    ];
    let scope = ints(&["x".into(), "y".into()]);
    for (what, t) in cases {
        let one = arms_and_value(&t, &scope);
        if let Some(diff) = difference(&one, &arms_and_value_by_transfer(&t, &scope)) {
            panic!("{what}, {t}: {diff}");
        }
    }
}

/// A peeled block `let y = .. in b` whose body reads a name `n` whose summary reads the input
/// `y` that the block shadows agrees with the transfer (row PROOF-pa-peel-summary). Inside the
/// block `y` is another binding, so `n`'s summary does not hold there and the peeled body was a
/// function of `n` alone, while the whole block is one of the input `y`: in the first case the
/// test narrowed `n` to 2 one way and `y` to 1 the other. Red before `Lazy::peel_agrees` asked
/// that each name be read through its summary in both scopes or in neither (the first, third and
/// fourth cases). The other cases read a name through a summary over one input inside a
/// `min`, a `max`, a sum of the name with itself, which the whole block reads as one term, and
/// the guard of an `if`, which the whole block reads through the bound term and the peeled
/// body through the name's summary (the steps of the proof at `Lazy::get` not proved).
#[test]
fn a_peeled_block_reading_a_name_over_the_shadowed_input_agrees_with_the_transfer() {
    let p = |op, a, b| prim(op, vec![a, b]);
    let y = || var("y");
    let read =
        |n: Term, blk: Term, test: Term| let_("n", n, let_("z", blk, if_(test, int(1), int(2))));
    let z = || var("z");
    let cases = [
        (
            "n = y + 1, z = (y = 5; n + y), z == 7",
            read(
                p(Prim::Add, y(), int(1)),
                let_("y", int(5), p(Prim::Add, var("n"), y())),
                p(Prim::Eq, z(), int(7)),
            ),
        ),
        (
            "n = 2 * y, z = (y = 1; n - y), z mod 4 == 1",
            read(
                p(Prim::Mul, int(2), y()),
                let_("y", int(1), p(Prim::Sub, var("n"), y())),
                p(Prim::Eq, p(Prim::Mod, z(), int(4)), int(1)),
            ),
        ),
        (
            "n = if y > 3 { 10 } else { 20 }, z = (y = 5; n + y), z == 15",
            read(
                if_(p(Prim::Gt, y(), int(3)), int(10), int(20)),
                let_("y", int(5), p(Prim::Add, var("n"), y())),
                p(Prim::Eq, z(), int(15)),
            ),
        ),
        (
            "n = y + 1, z = (y = 5; n + y), y == 1 && z == 7",
            read(
                p(Prim::Add, y(), int(1)),
                let_("y", int(5), p(Prim::Add, var("n"), y())),
                p(
                    Prim::And,
                    p(Prim::Eq, y(), int(1)),
                    p(Prim::Eq, z(), int(7)),
                ),
            ),
        ),
    ];
    let x = || var("x");
    let t = || var("t");
    let zero_y = || p(Prim::Add, x(), p(Prim::Mul, int(0), y()));
    let more = [
        (
            "z = (t = x + 0 * y; min(t, 3)), z == 2",
            let_(
                "z",
                let_("t", zero_y(), p(Prim::Min, t(), int(3))),
                if_(p(Prim::Eq, z(), int(2)), int(1), int(2)),
            ),
        ),
        (
            "z = (t = x + 0 * y; max(t, -t)), z == 2",
            let_(
                "z",
                let_("t", zero_y(), p(Prim::Max, t(), prim(Prim::Neg, vec![t()]))),
                if_(p(Prim::Eq, z(), int(2)), int(1), int(2)),
            ),
        ),
        (
            "z = (t = x + 0 * y; t + t), z == 3",
            let_(
                "z",
                let_("t", zero_y(), p(Prim::Add, t(), t())),
                if_(p(Prim::Eq, z(), int(3)), int(1), int(2)),
            ),
        ),
        (
            "z = (t = if x > 0 { 5 } else { 1 }; if t > 3 { 10 } else { 20 }), z == 10",
            let_(
                "z",
                let_(
                    "t",
                    if_(p(Prim::Gt, x(), int(0)), int(5), int(1)),
                    if_(p(Prim::Gt, t(), int(3)), int(10), int(20)),
                ),
                if_(p(Prim::Eq, z(), int(10)), int(1), int(2)),
            ),
        ),
        (
            "z = (t = 2 * x; if t > 3 { 10 } else { t }), z == 2",
            let_(
                "z",
                let_(
                    "t",
                    p(Prim::Mul, int(2), x()),
                    if_(p(Prim::Gt, t(), int(3)), int(10), t()),
                ),
                if_(p(Prim::Eq, z(), int(2)), int(1), int(2)),
            ),
        ),
    ];
    let scope = ints(&["x".into(), "y".into()]);
    let mut bad = Vec::new();
    for (what, t) in cases.into_iter().chain(more) {
        let one = arms_and_value(&t, &scope);
        if let Some(diff) = difference(&one, &arms_and_value_by_transfer(&t, &scope)) {
            bad.push(format!("{what}, {t}: {diff}"));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}
