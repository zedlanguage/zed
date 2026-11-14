//! The ZIR and kernel addresses of a constant of n bits, and of a product of n kept powers, take
//! time linear in n: the benchmarks of `wide_constants.rs`, whose tests address each at small
//! sizes.

use num_bigint::Sign;
use zed_kernel::Value;
use zed_tests::scaling::check_order;
use zedc::canon;
use zedc::zir::canon::address;
use zedc::zir::{Region, binary};

use crate::wide_constants::{def, graph, kept_product, primes, two_to, wide};

/// Writing a number kept as the product of the first n primes, each to the power 2^100, takes
/// time and memory linear in n, the size of its form: its value has about 2^100 n bits.
#[test]
fn a_kept_power_is_written_in_time_linear_in_its_parts() {
    const N: usize = 1 << 10;
    let primes = primes(8 * N);
    let (small, large) = (kept_product(&primes[..N]), kept_product(&primes));
    let gs = [graph(small.clone()), graph(large.clone())];
    let pick = |k: usize| &gs[usize::from(k != N)];
    check_order("the ZIR address of a product of n kept powers", N, 1, |k| {
        address(pick(k)).expect("the powers");
    });
    check_order("the binary form of a product of n kept powers", N, 1, |k| {
        binary::encode(pick(k)).expect("the powers");
    });
    let defs = [def(small), def(large)];
    let none = |_: &str| None;
    check_order(
        "the kernel address of a product of n kept powers",
        N,
        1,
        |k| {
            canon::address(&defs[usize::from(k != N)], &none).expect("the powers");
        },
    );
}

/// The decimal digits cost about `n^1.5` here, 22.3 times the work at 8n: over the limit of 13,
/// though under the 24 allowed until SCALE-ratio, when a second test held it at 64 times the
/// bits (removed by TESTS-scaling-limit-13).
#[test]
fn addressing_a_wide_constant_is_linear_in_its_bits() {
    const N: usize = 1 << 17;
    let terms = |sign| {
        [
            graph(Value::int(wide(N, sign))),
            graph(Value::int(wide(8 * N, sign))),
        ]
    };
    let (random, negative) = (terms(Sign::Plus), terms(Sign::Minus));
    let powers = [
        graph(Value::integer(two_to(N))),
        graph(Value::integer(two_to(8 * N))),
    ];
    fn pick(gs: &[Region; 2], k: usize) -> &Region {
        &gs[usize::from(k != N)]
    }
    check_order("the ZIR address of a random number of n bits", N, 1, |k| {
        address(pick(&random, k)).expect("memory for the address");
    });
    check_order(
        "the ZIR address of a negative number of n bits",
        N,
        1,
        |k| {
            address(pick(&negative, k)).expect("memory for the address");
        },
    );
    check_order("the ZIR address of 2^n kept as a power", N, 1, |k| {
        address(pick(&powers, k)).expect("memory for the address");
    });
    let defs = [
        def(Value::int(wide(N, Sign::Plus))),
        def(Value::int(wide(8 * N, Sign::Plus))),
    ];
    let none = |_: &str| None;
    check_order(
        "the kernel address of a random number of n bits",
        N,
        1,
        |k| {
            canon::address(&defs[usize::from(k != N)], &none).expect("memory for the address");
        },
    );
}
