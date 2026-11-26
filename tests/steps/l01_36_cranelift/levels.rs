//! The native code is compiled at Cranelift's `opt_level` `none` with its single-pass register
//! allocator, so each pass is linear in the size of a function (COMPLEXITY.md Z15). That
//! code is slower than what Cranelift's `speed` settings give, and must give the same values:
//! each program here runs at both levels, and the values, the heap's counts and the table rows
//! agree with each other and with the interpreter.

use std::cell::Cell;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_native::{OptLevel, Outcome, run_at};
use zedc::testing::{test, test_through};
use zedc::zir::lower::lower;
use zedc::zir::memory::plan;

use super::{kernel, planned};

/// `t` run natively at `level`, with no ports.
fn at(level: OptLevel, t: &Term) -> Outcome {
    let (g, p) = planned(t);
    run_at(level, &g, &p, &mut Evaluator::new(World::new())).unwrap_or_else(|e| panic!("{e}"))
}

/// The value and the heap's counts of a run.
fn seen(o: &Outcome) -> (Value, u64, u64, u64, u64) {
    let s = &o.stats;
    (
        o.value.clone(),
        s.allocations,
        s.increments,
        s.decrements,
        o.kernel_calls,
    )
}

/// A unit whose tables the test runs at both levels.
const SHIPPING: &str = "\
// A parcel's shipping charge in cents: 450 for the first kilogram, 120 for each kilogram or
// part of one above it, and free above 20 kg.
shipping(positional grams) = if grams > 20000 { 0 } else { if grams <= 1000 { 450 } else { 450 + (grams - 1) div 1000 * 120 } }
test { 500 -> 450, 1000 -> 450, 1001 -> 570, 2500 -> 690, 20000 -> 2730, 20001 -> 0 }

main(m: MainArgs) {
  grams = int(trim(m.stdin[0] else #ioError -> \"\" else #outOfBounds -> \"\"));
  m.stdout <- \"${shipping(grams)} cents\" else #invalid -> \"not a weight in grams\";
}
test {
  \"2500\\n\" -> \"690 cents\\n\",
  \"25000\\n\" -> \"0 cents\\n\",
  \"heavy\\n\" -> \"not a weight in grams\\n\",
}
";

#[test]
fn opt_level_none_gives_the_values_opt_level_speed_gives() {
    let runs = Cell::new(0);
    let through = |t: &Term, ev: &mut Evaluator| {
        let g = zed_native::legalize(lower(t)?);
        let p = plan(g.graph(), true);
        let mut copy = Evaluator::new(ev.world.clone());
        let none = run_at(OptLevel::None, &g, &p, ev)?;
        let speed = run_at(OptLevel::Speed, &g, &p, &mut copy)?;
        assert_eq!(seen(&none), seen(&speed), "{t:?}");
        runs.set(runs.get() + 1);
        Ok(none.value)
    };
    let want = test(SHIPPING);
    let got = test_through(SHIPPING, &through);
    assert_eq!(got, want);
    assert_eq!(got.len(), 9);
    assert!(got.iter().all(|o| o.failure.is_none()), "{got:?}");
    assert!(runs.get() >= 9, "{} native runs", runs.get());
}

/// No function compiled has a loop, at either level: a recursive call and every term of every
/// step unit are compiled here, and `Gen::function` asserts in every debug build that the
/// function it built has none (Cranelift's loop analysis), since at `speed` Cranelift would
/// hoist code out of a loop above the store of a name the debug information places in that
/// code (zed-native `dwarf::bindings`). The test build has debug assertions on.
#[test]
fn no_function_compiled_has_a_loop_at_either_level() {
    // Not `assert!`, which clippy refuses on a constant, nor `const { assert!(..) }`, which
    // would stop a build without debug assertions from compiling the other tests.
    if !cfg!(debug_assertions) {
        panic!("the check is a debug assertion");
    }
    let runs = Cell::new(0);
    let through = |t: &Term, ev: &mut Evaluator| {
        let g = zed_native::legalize(lower(t)?);
        let p = plan(g.graph(), true);
        for level in [OptLevel::None, OptLevel::Speed] {
            let mut copy = Evaluator::new(ev.world.clone());
            run_at(level, &g, &p, &mut copy)?;
        }
        runs.set(runs.get() + 1);
        Ok(run_at(OptLevel::None, &g, &p, ev)?.value)
    };
    for path in super::corpus::units() {
        let text = std::fs::read_to_string(&path).unwrap();
        assert_eq!(
            test_through(&text, &through),
            test(&text),
            "{}",
            path.display()
        );
    }
    // At least one run for each of the 92 table rows the units check.
    assert!(runs.get() >= 92, "{} native runs", runs.get());
    let t = zed_tests::deep::linked_list(10);
    for level in [OptLevel::None, OptLevel::Speed] {
        assert_eq!(at(level, &t).value, kernel(&t).unwrap());
    }
}

#[test]
fn a_loop_of_integer_arithmetic_agrees_at_both_levels() {
    // The sum of the squares below 40 of the numbers that are not multiples of 3, by a closure
    // applied to each: arithmetic and a branch inline, which an optimizer would rearrange.
    let sq = lam(
        &["x"],
        if_(
            prim(
                Prim::Eq,
                vec![prim(Prim::Mod, vec![var("x"), lit(3i64)]), lit(0i64)],
            ),
            lit(0i64),
            prim(Prim::Mul, vec![var("x"), var("x")]),
        ),
    );
    let mut sum = lit(0i64);
    for i in 0..40i64 {
        sum = prim(Prim::Add, vec![sum, app(var("sq"), vec![lit(i)])]);
    }
    let t = let_("sq", sq, sum);
    let (none, speed) = (at(OptLevel::None, &t), at(OptLevel::Speed, &t));
    assert_eq!(seen(&none), seen(&speed));
    assert_eq!(none.value, kernel(&t).unwrap());
    assert_eq!(none.value.to_string(), "13169");
}
