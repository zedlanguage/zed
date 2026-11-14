//! The benchmarks of `payload_scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `payload_scaling.rs`.

use super::*;

/// The k pinwheels of `name` ends made by `wrap`, the last with a cofinite end, at k and 8k:
/// the verdict is `Empty` when `full` and `Inhabited` with a middle.
///
/// The cofinite end of the last pinwheel lists the 3k - 1 integers of the other ends, under
/// an atom payload `#e((i,))` or a one-tuple `(i,)`. Each pinwheel is a class of its own
/// only if the cells of the integers under the payloads and one-tuples join the cofinite
/// one just when they hold an integer it leaves out (T6 repair 7 for plain integers). Inputs
/// are built before timing. Measured from k = 32 to 256 (2026-11-12, load 38 to 48, at the
/// old sizes): 7.9 to 8.2 times the instructions empty, 5.3 to 5.9 with a middle. A naive test
/// of each pair of the first component's cells for a shared value, on the region of the whole
/// union, made it 46.2 times the bytes, and the test failed.
///
/// The four checks were one test, at k = 32 each, until TEST-bench-move-l0123 (author P169)
/// split them and sized each to about 0.5 s at 1x.
fn cofinite_end_scales(k: usize, name: &'static str, wrap: fn(Type) -> Type, full: bool) {
    let (want, how) = if full {
        (Verdict::Empty, "empty")
    } else {
        (Verdict::Inhabited, "with a middle")
    };
    std::thread::Builder::new()
        .spawn(move || {
            let built: HashMap<usize, Type> =
                scaling::inputs(k, |k| cofinite_pinwheels(k as i64, full, wrap));
            scaling::check(
                &format!("k pinwheels of {name} ends, one cofinite, {how}, by k"),
                k,
                |k| {
                    Type::forget_emptiness();
                    assert_eq!(built[&k].verdict(), want);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pinwheels_of_payload_ends_with_a_cofinite_end_scale() {
    // TEST-bench-move-l0123, author P169: k 32 before, now 64; 1x 0.41 s by `ns`, load 35.
    cofinite_end_scales(64, "#e((i,))", payload, true);
}

#[test]
fn pinwheels_of_payload_ends_with_a_cofinite_end_and_a_middle_scale() {
    // TEST-bench-move-l0123, author P169: k 32 before, now 1024; 1x 0.42 s by `ns`, load 34.
    cofinite_end_scales(1024, "#e((i,))", payload, false);
}

#[test]
fn pinwheels_of_one_tuple_ends_with_a_cofinite_end_scale() {
    // TEST-bench-move-l0123, author P169: k 32 before, now 64; 1x 0.49 s by `ns`, load 35.
    cofinite_end_scales(64, "(i,)", one_tuple, true);
}

#[test]
fn pinwheels_of_one_tuple_ends_with_a_cofinite_end_and_a_middle_scale() {
    // TEST-bench-move-l0123, author P169: k 32 before, now 1024; 1x 0.52 s by `ns`, load 34.
    cofinite_end_scales(1024, "(i,)", one_tuple, false);
}
