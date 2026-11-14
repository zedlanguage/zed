//! The programs that reach past the minimum of 20,000 nested calls (DESIGN.md step M0.11), run
//! here at small sizes on the default stack: each gives its value, an error at the bottom
//! reaches the top, and fuel ends a recursion and a loop. The same programs 40,000 deep on a
//! 64 KiB stack are in `bench/nested_calls.rs`, and their times in `bench/deep.rs`.

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::{Evaluator, Family, KernelError, Prim, Schedule, Term, Value, World, eval};
use zed_tests::deep::linked_list;
use zed_tests::kernel::*;

/// `f(f, ...args)`, the self-application a recursive function elaborates to.
pub(super) fn recursive(f: Term, args: Vec<Term>) -> Term {
    let mut all = vec![f.clone()];
    all.extend(args);
    app(f, all)
}

pub(super) fn me(args: Vec<Term>) -> Term {
    let mut all = vec![var("me")];
    all.extend(args);
    app(var("me"), all)
}

/// `total(k) = if k == 0 { 0 } else { k + total(k - 1) }`, which nests `k` calls.
pub(super) fn total(k: i64) -> Term {
    let body = if_(
        eq(var("k"), lit(0)),
        lit(0),
        add(var("k"), me(vec![sub(var("k"), lit(1))])),
    );
    recursive(lam(&["me", "k"], body), vec![lit(k)])
}

/// `count(k, sum) = if k == 0 { sum } else { count(k - 1, sum + k) }`, a loop written as tail
/// recursion.
pub(super) fn count_down(k: i64) -> Term {
    let body = if_(
        eq(var("k"), lit(0)),
        var("sum"),
        me(vec![sub(var("k"), lit(1)), add(var("sum"), var("k"))]),
    );
    recursive(lam(&["me", "k", "sum"], body), vec![lit(k), lit(0)])
}

/// `go(k, then) = if k == 0 { end(then) } else { go(k - 1, x -> then(x + 1)) }`: a chain of
/// `k` continuations, each the only holder of the one before.
pub(super) fn continuations(k: i64, end: impl FnOnce(Term) -> Term) -> Term {
    let then = lam(&["x"], app(var("then"), vec![add(var("x"), lit(1))]));
    let body = if_(
        eq(var("k"), lit(0)),
        end(var("then")),
        me(vec![sub(var("k"), lit(1)), then]),
    );
    recursive(
        lam(&["me", "k", "then"], body),
        vec![lit(k), lam(&["x"], var("x"))],
    )
}

/// `depth(k) = if k == 0 { 0 } else { sum of { 0 -> 1 + depth(k - 1) } }`: a recursion that
/// passes through a `fam` and a `fold` at every level, as a tree walk does.
pub(super) fn through_regions(k: i64) -> Term {
    let once = lit(Value::Family(Family::set([0])));
    let inner = fam_with(once, |_| add(lit(1), me(vec![sub(var("k"), lit(1))])));
    let body = if_(
        eq(var("k"), lit(0)),
        lit(0),
        fold(inner, Term::PrimFn(Prim::Add), None),
    );
    recursive(lam(&["me", "k"], body), vec![lit(k)])
}

#[test]
fn a_failed_run_leaves_the_evaluator_usable() {
    // The first run stops inside a pure region. The second reads a port outside any region,
    // which a pure-region count left above zero would refuse, and has the facts of a first run.
    let inside = fam_with(lit(Value::Family(Family::set([1]))), |_| var("nothing"));
    let reading = add(Term::Read("price".into()), lit(1));
    let world = || World::new().input("price", 2);
    let mut ev = Evaluator::new(world()).with_provenance(vec![]);
    assert!(ev.run(&inside).is_err());
    assert_eq!(ev.run(&reading), Ok(Value::Int(3)));
    let after_failure = format!("{:?}", ev.provenance().unwrap().facts());
    let mut fresh = Evaluator::new(world()).with_provenance(vec![]);
    fresh.run(&reading).unwrap();
    assert_eq!(
        after_failure,
        format!("{:?}", fresh.provenance().unwrap().facts())
    );
}

#[test]
fn a_long_fold_keeps_the_canonical_order_on_the_machine() {
    // String concatenation shows the order: the leaves are read left to right.
    let letters = Family::of((0..1000).map(|i| (Value::Int(i), Value::from(&*i.to_string()))));
    let t = fold(
        lit(Value::Family(letters)),
        Term::PrimFn(Prim::Concat),
        None,
    );
    let expected: String = (0..1000).map(|i| i.to_string()).collect();
    assert_eq!(eval(&t), Ok(Value::from(&*expected)));
}

#[test]
fn prim_and_tuple_results_are_the_arguments_in_order() {
    // The arguments of a primitive are evaluated left to right, each pushed before the next.
    let t = prim(Prim::Tuple, vec![lit(1), add(lit(1), lit(1)), lit(3)]);
    assert_eq!(eval(&t).unwrap().to_string(), "(1, 2, 3)");
}

/// Each program the benchmarks of `bench/deep.rs` time returns at small sizes: a recursion,
/// with provenance and without, a tail-recursive loop, a chain of continuations, a recursion
/// through regions and a list built by recursion.
#[test]
fn each_benchmark_program_returns_at_small_sizes() {
    for n in [1, 2, 9] {
        eval(&total(n)).unwrap();
        eval(&count_down(n)).unwrap();
        eval(&continuations(n, |then| app(then, vec![lit(0)]))).unwrap();
        eval(&through_regions(n)).unwrap();
        eval(&linked_list(n)).unwrap();
        let mut ev = Evaluator::new(World::new()).with_provenance(vec![]);
        ev.run(&total(n)).unwrap();
    }
}

/// Each program of `bench/nested_calls.rs` at a few levels, on the default stack, with the
/// value it gives there: a recursion and a tail-recursive loop give the sum, a chain of
/// continuations is called and one nothing calls is freed, a recursion through regions and a
/// traced one give their depth, an error at the bottom reaches the top, fuel ends a recursion
/// and a loop that leaves no frame, a stream runs at each guard position, a chain of demands is
/// defined, and a list built by recursion is walked.
#[test]
fn each_deep_program_gives_its_value_at_small_sizes() {
    for n in [1, 2, 9] {
        let sum = n * (n + 1) / 2;
        assert_eq!(eval(&total(n)), Ok(Value::Int(sum)));
        assert_eq!(eval(&count_down(n)), Ok(Value::Int(sum)));
        let called = continuations(n, |then| app(then, vec![lit(0)]));
        assert_eq!(eval(&called), Ok(Value::Int(n)));
        assert_eq!(eval(&continuations(n, |_| lit(7))), Ok(Value::Int(7)));
        assert_eq!(eval(&through_regions(n)), Ok(Value::Int(n)));
        let mut ev = Evaluator::new(World::new()).with_provenance(vec![]);
        assert_eq!(ev.run(&through_regions(n)), Ok(Value::Int(n)));
        assert!(ev.provenance().unwrap().facts().len() as i64 > n);

        let body = if_(
            eq(var("k"), lit(0)),
            var("nothing"),
            add(lit(1), me(vec![sub(var("k"), lit(1))])),
        );
        assert_eq!(
            eval(&recursive(lam(&["me", "k"], body), vec![lit(n)])),
            Err(KernelError::Type("unbound variable `nothing`".into()))
        );

        for pos in [zed_kernel::GuardPos::Before, zed_kernel::GuardPos::After] {
            let t = Term::Gen {
                init: rc(lit(0)),
                step: rc(lam(&["x"], add(var("x"), lit(1)))),
                guard: rc(lam(&["x"], lt(var("x"), lit(n)))),
                pos,
            };
            let v = eval(&t).unwrap();
            assert_eq!(v.as_family().unwrap().len(), n as usize + 1, "{pos:?}");
        }

        let keys = lit(Value::Family(Family::set(0..n)));
        let t = fix_defined(keys, |this, k| {
            if_(
                eq(k.clone(), lit(n - 1)),
                lit(0),
                add(get(this, add(k, lit(1))), lit(1)),
            )
        });
        let v = Evaluator::new(World::new())
            .with_schedule(Schedule::Pull)
            .run(&t)
            .unwrap();
        assert_eq!(
            v.as_family().unwrap().get(&Value::Int(0)),
            Some(&Value::Int(n - 1))
        );

        let mut v = eval(&linked_list(n)).unwrap();
        let mut head = n;
        while let Value::Tuple(items) = v {
            let mut items = items.into_vec();
            assert_eq!(items[0], Value::Int(head));
            head -= 1;
            v = items.pop().unwrap();
        }
        assert_eq!((head, v), (0, Value::Int(0)));
    }
    let mut ev = Evaluator::new(World::new()).with_fuel(5);
    assert_eq!(ev.run(&total(9)), Err(KernelError::OutOfFuel));
    let spin = recursive(lam(&["me"], me(vec![])), vec![]);
    let mut ev = Evaluator::new(World::new()).with_fuel(1_000);
    assert_eq!(ev.run(&spin), Err(KernelError::OutOfFuel));
}
