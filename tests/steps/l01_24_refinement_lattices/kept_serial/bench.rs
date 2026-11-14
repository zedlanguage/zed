//! The benchmarks of `kept_serial.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `kept_serial.rs`.

use super::*;

/// Addressing a definition whose end and class hold a number past `i64` is linear in the
/// number's bits; its decimal text took more than linear time. The decimal text cost about
/// `n^1.5`, 22.6 times the work at 8n: over the limit of 13, though under the 24 allowed until
/// SCALE-ratio, when a second test held it at 64 times the bits (removed by
/// TESTS-scaling-limit-13). Those figures were measured at n = 128 KiB.
/// TEST-bench-move-l0123, author P169: n was 128 KiB, now 40 MiB; 1x 0.32 s at load 60.
#[test]
fn addressing_a_wide_end_and_class_scales() {
    let (n, sizes) = (40usize << 20, [40usize << 20, 320 << 20]);
    let inputs: HashMap<usize, (Def, Def)> = sizes
        .into_iter()
        .map(|b| {
            let v = wide(b);
            (b, (at(v.clone()), class(&v + &v, v)))
        })
        .collect();
    check_order(
        "addressing a wide end and a wide class, by the bytes of the number",
        n,
        1,
        |b| {
            let (end, class) = &inputs[&b];
            addr(end);
            addr(class);
        },
    );
}
