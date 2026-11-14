//! The tests of `check::tests` at unusual sizes (author P178), run by `tools/run_tests.sh
//! --bench` and left out of its default run (TEST-bench-move-crates). The correctness test that
//! keeps what this checks at small sizes is
//! `one_shape_per_length_joins_each_length_once_through_shared_parts`.

use super::*;

/// The type of `min` of two tuples nested 20,000 deep, one with an `int` at the bottom and
/// one with an `f64`, is joined at every level on the 8 MiB stack of a main thread: one
/// shape per level, `int | f64` at the bottom. Joined by recursion, once per level, it
/// overflowed that stack.
#[test]
fn one_shape_per_length_joins_a_tuple_nested_deep_on_a_main_sized_stack() {
    const DEPTH: usize = 20_000;
    let (int, f64) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::F64));
    let both = nested(int.clone(), DEPTH).union(&nested(f64.clone(), DEPTH));
    assert_eq!(both.tuples.len(), 2);
    let want = digest(&nested(int.union(&f64), DEPTH));
    let joined = std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            let joined = one_shape_per_length(&both);
            (joined.tuples.len(), digest(&joined))
        })
        .expect("starting the thread")
        .join()
        .expect("joining on an 8 MiB stack");
    assert_eq!(joined, (1, want));
}
