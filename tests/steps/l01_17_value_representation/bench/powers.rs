//! Exact numbers held as powers of primes at the rule of low complexity. The bodies timed are
//! checked at small sizes in `powers.rs`, by `ten_to_n_orders_multiplies_divides_and_projects`,
//! `a_kept_power_beside_its_built_successor_orders` and `a_rat_power_of_a_kept_exponent_is_exact`.

use num_bigint::BigInt;
use zed_kernel::Rat;
use zed_tests::scaling::check_order;

use super::super::powers::{rat_power_facts, ten_to_n_facts};

/// Building, ordering, multiplying, dividing and projecting `10^n` costs a few products of
/// numbers of `log n` bits, not the `3.3 n` bits of the value.
#[test]
fn ten_to_n_costs_its_exponent_and_not_its_digits() {
    // The work grows as the bits of `n`, so a run at any `n` takes well under 1 ms and no size
    // makes it 0.6 s; `2^20` is the size it has run at.
    check_order(
        "10^n built, compared, multiplied and projected",
        1 << 20,
        0,
        ten_to_n_facts,
    );
}

/// A kept power `3^n` and the built sum `3^n + 1` agree in every bit a bound reads, so their
/// order builds `3^n`; that build and the sum's cost O(n log n) in the width (item
/// KERNEL-sum-tower), not the O(n^1.47) of num-bigint's products they took before.
#[test]
fn a_kept_power_beside_its_built_successor_costs_n_log_n() {
    // `3^n` is built by squaring, so a run's work is a sum over squares of halving widths:
    // those num-bigint's Toom-3 does faster (at most `fast::MUL_LEAF` = 459 words, and above
    // it where `toom_cost` is the least of `fast::mul`'s computed costs), and the wider by
    // transforms. The smaller run has three fewer squares by transforms than the larger, so
    // its sum stops short and the ratio counts the change of method as growth. Measured with
    // a leaf of 6144 words (SCALE-fix-crossover, 2026-11-07, load 47): from n = 2^18 (the
    // last square of 3,250 words) 14.6 times against a limit of 10.3, from 2^21 10.12 against
    // 10.06, from 2^22 9.72 against 10.0; with the cost model, 9.67 from 2^22 (2026-11-09).
    // One comparison is timed, half the work of the three in
    // `a_kept_power_beside_its_built_successor_orders`, which builds `3^n` and the sum as they
    // do. The SCALE-ratio limit tells num-bigint's O(n^1.47), 21 times at 8n, from O(n log n),
    // so the comparison at n and 64n that stood in for it is gone.
    // Measured 2026-11-14 at a load of about 35, six benchmarks at once: about 58 ns a
    // unit of n, 1x 0.36 s, 2.3 GB at 8n, ratio 9.0; at 2^23, 1x 0.72 s and the test 19.5 s.
    let n = 3 << 21;
    check_order("3^n + 1 built and compared with the kept 3^n", n, 1, |n| {
        let three = Rat::int(BigInt::from(3));
        let p = three.pow(&(n as u64).into()).unwrap();
        assert!(p < p.add(&Rat::int(BigInt::from(1))).unwrap());
    });
}

/// A `rat` power costs the bits of its exponent, not the exponent: `(2r/3r)^-n` multiplies the
/// kept exponents of 2 and 3 by `n`, and `(-1r)^(2^n)` reads the parity of `2^n` from its kept
/// form (complexity tradeoff at `Rat::pow_int`, COMPLEXITY.md K30). Building `2^n`, or a
/// product per unit of the exponent, grows with `n` and fails this check (negative controls
/// run 2026-11-12, POW-rat).
#[test]
fn a_rat_power_costs_the_bits_of_its_exponent() {
    // As for `10^n`, no size makes a run 0.6 s; `2^20` is the size it has run at.
    check_order("(2r/3r)^-n and (-1r)^(2^n)", 1 << 20, 0, rat_power_facts);
}
