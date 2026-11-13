//! The limit against the time taken (QUESTIONS A99): the work a law is charged, read as
//! milliseconds at `poly::LIMIT` units per 250 ms, against the processor time its decision
//! takes. The two laws of the refusal sightings of 2026-11-12 (wt/refusal-sightings.md), the
//! product law at exponent 1000 and the split law `(x + y) ^ 72 - x`, are proved, each within
//! 2x of its prediction, and so is the split law near the limit; past the limit it is refused.
//! The time is the least of a few runs, since the load of the machine only adds to it.

use std::time::Duration;

use zed_kernel::poly::{Carrier, Decision, LIMIT, LIMIT_MS, Verdict};
use zed_tests::scaling::cpu_time;

use super::{decide_sides, sides_of};

/// The decision on `lhs == rhs` over `params`, and the least processor time of `runs` runs.
fn timed(params: &str, lhs: &str, rhs: &str, runs: usize) -> (Decision, Duration) {
    let s = sides_of(&format!("sides({params}) = ({lhs}, {rhs});\n"), &["sides"]).remove(0);
    let mut least = Duration::MAX;
    let mut d = None;
    for _ in 0..runs {
        let t = cpu_time();
        d = Some(decide_sides(&s, Carrier::Int));
        least = least.min(cpu_time() - t);
    }
    (d.expect("one run"), least)
}

/// Asserts `lhs == rhs` proved, with the predicted time within 2x of the time taken.
fn within_2x(what: &str, params: &str, lhs: &str, rhs: &str, runs: usize) {
    let (d, time) = timed(params, lhs, rhs, runs);
    assert_eq!(d.verdict, Verdict::Proved, "{what}");
    let predicted = d.work / LIMIT * LIMIT_MS;
    let taken = time.as_secs_f64() * 1e3;
    eprintln!(
        "{what}: work {:.0}, predicted {predicted:.3} ms, taken {taken:.3} ms, ratio {:.2}",
        d.work,
        taken / predicted
    );
    assert!(
        (0.5..=2.0).contains(&(taken / predicted)),
        "{what}: predicted {predicted:.3} ms, taken {taken:.3} ms"
    );
}

#[test]
fn the_product_law_at_exponent_1000() {
    within_2x(
        "(1 + x) ^ 1000 * (1 - x) ^ 1000",
        "x: int",
        "(1 + x) ^ 1000 * (1 - x) ^ 1000",
        "(1 - x ^ 2) ^ 1000",
        5,
    );
}

#[test]
fn the_split_law_at_exponent_72() {
    within_2x(
        "(x + y) ^ 72 - x",
        "x: int, y: int",
        "(x + y) ^ 72 - x",
        "(x + y) ^ 36 * (y + x) ^ 36 - x",
        9,
    );
}

#[test]
fn the_split_law_near_the_limit() {
    // Exponent 4096 is proved in about 150 ms; 8192, about four times the work, is refused.
    within_2x(
        "(x + y) ^ 4096 - x",
        "x: int, y: int",
        "(x + y) ^ 4096 - x",
        "(x + y) ^ 2048 * (y + x) ^ 2048 - x",
        2,
    );
    let (d, _) = timed(
        "x: int, y: int",
        "(x + y) ^ 8192 - x",
        "(x + y) ^ 4096 * (y + x) ^ 4096 - x",
        1,
    );
    assert!(matches!(d.verdict, Verdict::Refused(_)), "{:?}", d.verdict);
    assert!(d.work <= LIMIT);
}
