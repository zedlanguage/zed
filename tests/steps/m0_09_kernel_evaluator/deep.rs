//! Programs far deeper than the minimum of 20,000 nested calls (DESIGN.md step M0.11). The
//! evaluator keeps its frames on the heap, so each runs on a thread with a
//! small stack: a test passes only if no part of the evaluator nests on the thread's stack.

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::{Evaluator, Family, KernelError, Prim, Schedule, Term, Value, World, eval};
use zed_tests::deep::{linked_list, on_main_sized_stack};
use zed_tests::kernel::*;
use zed_tests::scaling;

/// Far past [`zed_kernel::eval::MIN_NESTED_CALLS`].
const DEEP: i64 = 1_000_000;

/// Runs `f` on a thread with a 64 KiB stack.
fn on_small_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(1 << 16);
        thread.spawn_scoped(scope, f).unwrap().join().unwrap()
    })
}

/// `f(f, ...args)`, the self-application a recursive function elaborates to.
fn recursive(f: Term, args: Vec<Term>) -> Term {
    let mut all = vec![f.clone()];
    all.extend(args);
    app(f, all)
}

fn me(args: Vec<Term>) -> Term {
    let mut all = vec![var("me")];
    all.extend(args);
    app(var("me"), all)
}

/// `total(k) = if k == 0 { 0 } else { k + total(k - 1) }`, which nests `k` calls.
fn total(k: i64) -> Term {
    let body = if_(
        eq(var("k"), lit(0)),
        lit(0),
        add(var("k"), me(vec![sub(var("k"), lit(1))])),
    );
    recursive(lam(&["me", "k"], body), vec![lit(k)])
}

/// `count(k, sum) = if k == 0 { sum } else { count(k - 1, sum + k) }`, a loop written as tail
/// recursion.
fn count_down(k: i64) -> Term {
    let body = if_(
        eq(var("k"), lit(0)),
        var("sum"),
        me(vec![sub(var("k"), lit(1)), add(var("sum"), var("k"))]),
    );
    recursive(lam(&["me", "k", "sum"], body), vec![lit(k), lit(0)])
}

/// `go(k, then) = if k == 0 { end(then) } else { go(k - 1, x -> then(x + 1)) }`: a chain of
/// `k` continuations, each the only holder of the one before.
fn continuations(k: i64, end: impl FnOnce(Term) -> Term) -> Term {
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
fn through_regions(k: i64) -> Term {
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
fn a_recursion_a_million_calls_deep_returns() {
    let sum = DEEP * (DEEP + 1) / 2;
    assert_eq!(on_small_stack(|| eval(&total(DEEP))), Ok(Value::Int(sum)));
}

#[test]
fn a_tail_recursive_loop_returns() {
    let sum = DEEP * (DEEP + 1) / 2;
    assert_eq!(
        on_small_stack(|| eval(&count_down(DEEP))),
        Ok(Value::Int(sum))
    );
}

#[test]
fn a_chain_of_continuations_is_called_and_freed() {
    let called = continuations(DEEP, |then| app(then, vec![lit(0)]));
    assert_eq!(on_small_stack(|| eval(&called)), Ok(Value::Int(DEEP)));
    // Nothing calls this chain: the end of the run frees it from the last continuation in.
    let dropped = continuations(DEEP, |_| lit(7));
    assert_eq!(on_small_stack(|| eval(&dropped)), Ok(Value::Int(7)));
}

#[test]
fn a_recursion_through_regions_returns() {
    assert_eq!(
        on_small_stack(|| eval(&through_regions(100_000))),
        Ok(Value::Int(100_000))
    );
}

#[test]
fn a_deep_recursion_records_its_provenance() {
    let n = 100_000;
    let run = || {
        let mut ev = Evaluator::new(World::new()).with_provenance(vec![]);
        let v = ev.run(&through_regions(n)).unwrap();
        (v, ev.provenance().unwrap().facts().len())
    };
    let (v, facts) = on_small_stack(run);
    assert_eq!(v, Value::Int(n));
    assert!(facts as i64 > n);
}

#[test]
fn an_error_at_the_bottom_of_a_deep_recursion_reaches_the_top() {
    // `1 / 0`-style failure at depth: an unbound name is an error, not a failure atom.
    let body = if_(
        eq(var("k"), lit(0)),
        var("nothing"),
        add(lit(1), me(vec![sub(var("k"), lit(1))])),
    );
    let t = recursive(lam(&["me", "k"], body), vec![lit(DEEP)]);
    assert_eq!(
        on_small_stack(|| eval(&t)),
        Err(KernelError::Type("unbound variable `nothing`".into()))
    );
}

#[test]
fn deep_recursion_ends_when_the_fuel_does() {
    let mut ev = Evaluator::new(World::new()).with_fuel(1000);
    let out = on_small_stack(|| ev.run(&total(DEEP)));
    assert_eq!(out, Err(KernelError::OutOfFuel));
}

#[test]
fn a_loop_without_end_ends_when_the_fuel_does() {
    // `w(w)` with `w = me -> me(me)` has no base case and leaves no frame.
    let spin = recursive(lam(&["me"], me(vec![])), vec![]);
    let mut ev = Evaluator::new(World::new()).with_fuel(1_000_000);
    let out = on_small_stack(|| ev.run(&spin));
    assert_eq!(out, Err(KernelError::OutOfFuel));
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
fn a_long_stream_runs_at_every_guard_position() {
    for pos in [zed_kernel::GuardPos::Before, zed_kernel::GuardPos::After] {
        let n = 100_000;
        let t = Term::Gen {
            init: rc(lit(0)),
            step: rc(lam(&["x"], add(var("x"), lit(1)))),
            guard: rc(lam(&["x"], lt(var("x"), lit(n)))),
            pos,
        };
        let v = eval(&t).unwrap();
        assert_eq!(v.as_family().unwrap().len(), n as usize + 1, "{pos:?}");
    }
}

#[test]
fn a_chain_of_demands_a_million_entries_long_is_defined() {
    // Each entry reads the one after it, so the first demand nests a million attempts.
    let d = DEEP;
    let keys = lit(Value::Family(Family::set(0..d)));
    let t = fix_defined(keys, |this, k| {
        if_(
            eq(k.clone(), lit(d - 1)),
            lit(0),
            add(get(this, add(k, lit(1))), lit(1)),
        )
    });
    let run = || {
        Evaluator::new(World::new())
            .with_schedule(Schedule::Pull)
            .run(&t)
    };
    let v = on_small_stack(run).unwrap();
    assert_eq!(
        v.as_family().unwrap().get(&Value::Int(0)),
        Some(&Value::Int(d - 1))
    );
}

#[test]
fn nested_calls_scale_with_depth() {
    scaling::check("a recursion, by nested calls", 20_000, |n| {
        eval(&total(n as i64)).unwrap();
    });
    scaling::check("a tail-recursive loop, by iterations", 20_000, |n| {
        eval(&count_down(n as i64)).unwrap();
    });
    scaling::check("a chain of continuations, by length", 20_000, |n| {
        eval(&continuations(n as i64, |then| app(then, vec![lit(0)]))).unwrap();
    });
    scaling::check("a recursion through regions, by depth", 5_000, |n| {
        eval(&through_regions(n as i64)).unwrap();
    });
}

#[test]
fn provenance_of_a_deep_recursion_scales_with_depth() {
    scaling::check("a traced recursion, by nested calls", 2_000, |n| {
        let mut ev = Evaluator::new(World::new()).with_provenance(vec![]);
        ev.run(&total(n as i64)).unwrap();
    });
}

#[test]
fn prim_and_tuple_results_are_the_arguments_in_order() {
    // The arguments of a primitive are evaluated left to right, each pushed before the next.
    let t = prim(Prim::Tuple, vec![lit(1), add(lit(1), lit(1)), lit(3)]);
    assert_eq!(eval(&t).unwrap().to_string(), "(1, 2, 3)");
}

#[test]
fn a_list_as_deep_as_the_minimum_is_built_and_dropped() {
    let n = zed_kernel::eval::MIN_NESTED_CALLS as i64;
    on_main_sized_stack(|| {
        let mut v = eval(&linked_list(n)).unwrap();
        let mut head = n;
        while let Value::Tuple(items) = v {
            let mut items = items.into_vec();
            assert_eq!(items[0], Value::Int(head));
            head -= 1;
            v = items.pop().unwrap();
        }
        assert_eq!((head, v), (0, Value::Int(0)));
        drop(eval(&linked_list(n)).unwrap());
    });
}

#[test]
fn building_a_list_scales_with_its_length() {
    // The tuple primitive copied its values, so each element copied the whole list behind it:
    // 19,990 elements took 16 s. It now keeps the values it is given.
    on_main_sized_stack(|| {
        scaling::check("a list built by recursion, by length", 10_000, |n| {
            eval(&linked_list(n as i64)).unwrap();
        });
    });
}
