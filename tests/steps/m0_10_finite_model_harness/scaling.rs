//! The definedness `fix` at the rule of low complexity (DESIGN.md Part G). Each attempt at an
//! entry reads the family defined so far; copying the domain and that family into every
//! attempt made a `fix` over `D` keys cost `O(D²)` even when each entry is tried at most twice.

use zed_kernel::term::build::if_;
use zed_kernel::term::build::lit;
use zed_kernel::{Evaluator, Family, Schedule, Term, Value, World};
use zed_tests::kernel::*;
use zed_tests::scaling;

/// The family `k -> k` over `0..d`, each entry above 0 reading entry 0 (`star`) or the entry
/// before it (`chain`).
fn counts(d: usize, chain: bool) -> Term {
    let keys = lit(Value::Family(Family::set(0..d as i64)));
    fix_defined(keys, |this, k| {
        let from = if chain {
            sub(k.clone(), lit(1))
        } else {
            lit(0)
        };
        let step = if chain { lit(1) } else { k.clone() };
        if_(eq(k, lit(0)), lit(0), add(get(this, from), step))
    })
}

fn run(t: &Term, schedule: Schedule) -> Value {
    Evaluator::new(World::new())
        .with_schedule(schedule)
        .run(t)
        .unwrap()
}

#[test]
fn the_definedness_fix_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            // Two rounds: every entry but 0 is postponed once.
            scaling::check("rounds, entries reading entry 0, by keys", 1000, |d| {
                run(&counts(d, false), Schedule::Rounds);
            });
            scaling::check("chaotic, entries reading entry 0, by keys", 1000, |d| {
                run(&counts(d, false), Schedule::Chaotic(7));
            });
            // Each entry demands the one before it, once.
            scaling::check("pull, a chain, by keys", 1000, |d| {
                run(&counts(d, true), Schedule::Pull);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn every_schedule_defines_the_counts() {
    let want = |d: usize| {
        Value::Family(
            Family::from_leaves((0..d as i64).map(|k| (vec![Value::Int(k)], Value::Int(k))))
                .unwrap(),
        )
    };
    for chain in [false, true] {
        for schedule in [Schedule::Rounds, Schedule::Pull, Schedule::Chaotic(3)] {
            assert_eq!(
                run(&counts(50, chain), schedule),
                want(50),
                "{schedule:?}, chain {chain}"
            );
        }
    }
}

#[test]
fn a_jacobi_round_reads_the_family_as_the_round_began() {
    // Each round is one unit of fuel. A chain of 40 entries defines one entry per round, so
    // it takes 40 rounds and a 41st that finds nothing left; a round that read the entries
    // defined earlier in the same round would define the whole chain in one.
    let chain = counts(40, true);
    let with = |fuel| Evaluator::new(World::new()).with_fuel(fuel).run(&chain);
    assert!(with(40).is_err(), "40 rounds do not finish a chain of 40");
    assert!(with(41).is_ok());
}
