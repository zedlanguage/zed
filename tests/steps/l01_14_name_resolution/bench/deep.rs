//! Each deep program shape resolved 20,000 deep on a thread of the default 2 MiB stack (author
//! P178: an unusual size is a benchmark). Resolution recursed once per level of nesting and
//! overflowed this stack near 10,000. The same shapes at small depths are resolved in
//! `scaling.rs`, and the time at 12,500 and 100,000 is held in `bench/scaling.rs`.

use crate::scaling::{DEEP_SHAPES, deep_resolves};

#[test]
fn each_deep_shape_resolves_20000_deep_on_a_2_mib_stack() {
    use zed_tests::deep::{on_small_stack, program, statements};
    let n = 20_000;
    on_small_stack(|| {
        for shape in DEEP_SHAPES {
            let r = zedc::resolve::resolve(&statements(&program(shape, n).text)).unwrap();
            deep_resolves(shape, &r, n);
        }
    });
}
