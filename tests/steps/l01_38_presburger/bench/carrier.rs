//! The benchmarks of `carrier.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::sig_of;

#[test]
fn the_int_parameters_of_a_signature_scale() {
    // O(arrows × parameters): each parameter's type on each arrow is tested once.
    let sig = |k: usize| {
        let ps: Vec<String> = (0..k)
            .map(|i| format!("p{i}: {}", if i % 2 == 0 { "int" } else { "f64" }))
            .collect();
        sig_of(&format!("ok({}) = true;", ps.join(", ")), "ok")
    };
    // Built by `check_inputs`, only at the sizes this process runs: built at both before the
    // first run, under DynamoRIO, the first phase passed its limit of 20 s (rc 124 at 20.2 s on
    // l43, b22-tests8 job f2, FAIL-bench-pieces-past-limit-on-main).
    scaling::check_inputs(
        "the int parameters of a signature of n parameters",
        40000,
        |k| (k, sig(k)),
        |(k, sig)| {
            let ints = sig.int_params();
            assert_eq!(ints.iter().filter(|&&i| i).count(), k / 2);
        },
    );
}
