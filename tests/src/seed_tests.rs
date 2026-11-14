//! The tests of [`crate::seed`], compiled into this crate's unit tests only. The module itself is
//! compiled, by `#[path]`, into the unit tests of zedc-int, zedc-lattice, zedc-preimage,
//! zedc-presburger, zedc-solvers, zedc-types and zed-kernel too, and while this test lay inside
//! it, it ran again in each of those binaries, eight times a run, and each of their test counts
//! was one more than their own tests (TEST-seed-test-once, as TEST-scaling-module-tests-once did
//! for `crate::scaling`). The module gives this file `mix` as `pub(crate)`.

use crate::seed::mix;

#[test]
fn the_mix_is_splitmix64() {
    // The first output of SplitMix64 from the state 0 (Steele, Lea and Flood 2014).
    assert_eq!(mix(0), 0xe220_a839_7b1d_cdaf);
}
