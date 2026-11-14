//! The benchmarks of `payload_scaling.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `payload_scaling.rs`.

use super::*;

#[test]
fn pinwheels_of_payload_and_one_tuple_ends_with_a_cofinite_end_scale() {
    // The cofinite end of the last pinwheel lists the 3k - 1 integers of the other ends, under
    // an atom payload `#e((i,))` or a one-tuple `(i,)`. Each pinwheel is a class of its own
    // only if the cells of the integers under the payloads and one-tuples join the cofinite
    // one just when they hold an integer it leaves out (T6 repair 7 for plain integers). Inputs
    // are built before timing. Measured from k = 32 to 256 (2026-11-12, load 38 to 48): 7.9 to
    // 8.2 times the instructions empty, 5.3 to 5.9 with a middle. A naive test of each pair of
    // the first component's cells for a shared value, on the region of the whole union, made
    // it 46.2 times the bytes, and the test failed.
    std::thread::Builder::new()
        .spawn(|| {
            for (name, wrap) in [
                ("#e((i,))", payload as fn(Type) -> Type),
                ("(i,)", one_tuple),
            ] {
                for (full, want, how) in [
                    (true, Verdict::Empty, "empty"),
                    (false, Verdict::Inhabited, "with a middle"),
                ] {
                    let built: HashMap<usize, Type> = [32, 256]
                        .into_iter()
                        .map(|k| (k, cofinite_pinwheels(k as i64, full, wrap)))
                        .collect();
                    scaling::check(
                        &format!("k pinwheels of {name} ends, one cofinite, {how}, by k"),
                        32,
                        |k| {
                            Type::forget_emptiness();
                            assert_eq!(built[&k].verdict(), want);
                        },
                    );
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
