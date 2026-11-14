//! Programs deeper than the minimum of 20,000 nested calls (DESIGN.md step M0.11), and long
//! runs, each on a thread of 64 KiB stack (author P178: an unusual size is a benchmark). The
//! evaluator keeps its frames on the heap, so a test passes only if no part of the evaluator
//! nests on the thread's stack. Each program gives the same value at small sizes, on the default
//! stack, in `deep::each_deep_program_gives_its_value_at_small_sizes`.

use zed_kernel::term::build::{app, if_, lam, lit, var};
use zed_kernel::{Evaluator, Family, KernelError, Schedule, Term, Value, World, eval};
use zed_tests::deep::{linked_list, on_main_sized_stack};
use zed_tests::kernel::*;

use crate::deep::{continuations, count_down, me, recursive, through_regions, total};

/// Twice [`zed_kernel::eval::MIN_NESTED_CALLS`]. A plain recursion takes at least 112 bytes a
/// level (a recursive equality of nested tuples, measured at opt-level 2), so the 64 KiB stack
/// below would overflow at 585 levels.
const DEEP: i64 = 40_000;

/// Runs `f` on a thread with a 64 KiB stack.
fn on_small_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(1 << 16);
        thread.spawn_scoped(scope, f).unwrap().join().unwrap()
    })
}

#[test]
fn a_recursion_past_the_minimum_depth_returns() {
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
        on_small_stack(|| eval(&through_regions(DEEP))),
        Ok(Value::Int(DEEP))
    );
}

#[test]
fn a_deep_recursion_records_its_provenance() {
    let n = DEEP;
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
fn a_long_chain_of_demands_is_defined() {
    // Each entry reads the one after it, so the first demand nests `DEEP` attempts.
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
