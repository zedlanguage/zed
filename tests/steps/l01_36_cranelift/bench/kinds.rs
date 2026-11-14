//! `is T` on a tuple in cells, when `T` holds every tuple or none, is answered from the kind,
//! so its cost does not grow with the tuple (COMPLEXITY.md R13). The small instances are in
//! `kinds.rs`.

use std::sync::Mutex;

use zed_kernel::types::{Type, Universe};
use zed_rt::{Heap, Word};
use zed_tests::scaling;

use crate::kinds::{is, tuple_of_strings};

/// `TESTS` tests of a tuple of `n` strings, which the kind decides, at `n` and `8n`: the work
/// is the same at both sizes. Each would read all `n` parts if the tuple were made a value.
#[test]
fn testing_the_kind_of_a_large_tuple_scales() {
    const TESTS: usize = 1 << 20;
    let n = 2000;
    let small = Mutex::new(tuple_of_strings(n));
    let large = Mutex::new(tuple_of_strings(scaling::FACTOR * n));
    let types = [Type::universe(Universe::Tuple), Type::int(), Type::string()];
    let run = |hw: &Mutex<(Heap, Word)>| {
        let (h, w) = &mut *hw.lock().unwrap();
        for i in 0..TESTS {
            let t = &types[i % types.len()];
            std::hint::black_box(is(h, *w, t));
        }
    };
    scaling::compare(
        &format!(
            "{TESTS} tests by kind of a tuple of {n} and {} strings",
            scaling::FACTOR * n
        ),
        0,
        || run(&small),
        || run(&large),
    );
}
