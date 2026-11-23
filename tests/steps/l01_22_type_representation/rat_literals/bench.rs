//! The benchmarks of `rat_literals.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `rat_literals.rs`.

use super::*;

#[test]
fn a_rat_literal_costs_its_exponent_and_not_its_digits() {
    // The exponent `N` at `2^20` and `2^23`: the value has `N` digits, the text `log10 N`.
    let ns = [1usize << 20, 1 << 23];
    let texts = programs(&ns.map(|n| n.to_string()));
    check_order(
        "the types of 1eNr, 10eNr, 1.0eNr and 1e-Nr checked, compared and printed",
        ns[0],
        0,
        |n| {
            let i = usize::from(n != ns[0]);
            check_program(&texts[&i], &ns[i].to_string());
        },
    );
}

#[test]
fn a_rat_literal_costs_the_length_of_its_text() {
    // The exponent written with `n` and `8n` digits: no form of the value could be built.
    // TEST-bench-move-l0123 (author P169): it was left at its old size, 200 digits, for the
    // finding below.
    // Measured 2026-11-14 at load about 30: at 200 digits ns=464421/579104, instructions ratio
    // 1.74, bytes 1.90 (1x is 0.46 ms, far under 0.5 s); at 2,000 digits instructions 6.78,
    // bytes 7.22; at 20,000 digits instructions 15.48, bytes 11.7, and at 200,000 digits
    // (1x 110 ms) instructions 12.72, bytes 12.8, both over the limit of 10.5. The cost of a
    // literal grows faster than the length of its text once it has some thousands of digits.
    // b22-misc3, 2026-11-22, at 20,000 and 160,000 digits: instructions 13.20, bytes about
    // 11.0. perf: num-bigint's `mac3` 18.9%, `Field::forward` 12.2%, `inverse_pair` 5.4%,
    // `Printer::named` 3.4%: the exponent is read into a BigInt (`read_digits`) and printed back
    // in decimal, each O(n log^2 n), the order of RADIX-nlog2-10_5, which passes 10.5 only from
    // about 1.6 million digits. Left at 200 digits until the exponent is kept as its decimal
    // text or the conversion is faster (PERF-rat-literal-text-length).
    // b22-kept1, 2026-11-23, with the exponent kept in decimal digits (`num::dec`, DESIGN step
    // L1.17b; nothing converts, as `check_program` asserts): on main at 20,000 and 160,000
    // digits processor time 10.29 times and bytes 10.9 (over the limit); after, 5.75 and 7.5.
    // Raised to its 1 s size, 4 and 32 million digits: 1x 0.85 s, processor time 8.73 times,
    // bytes 8.4, peak resident memory 0.9 GB (Colab hm2).
    let digits = [4_000_000usize, 32_000_000];
    let ns = digits.map(|d| format!("1{}", "0".repeat(d - 1)));
    let texts = programs(&ns);
    check(
        "the types of 1eNr, 10eNr, 1.0eNr and 1e-Nr, N of n digits",
        digits[0],
        |n| {
            let i = usize::from(n != digits[0]);
            check_program(&texts[&i], &ns[i]);
        },
    );
    // The negative control at the old size of 160,000 digits, where its conversion takes some
    // tens of milliseconds: at 32 million it would take far longer than the benchmark.
    check_control(&format!("1{}", "0".repeat(159_999)));
}
