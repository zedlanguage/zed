//! The benchmark of `classed.rs` (row DOMAINS-classed-sets), run by
//! `tools/run_tests.sh --bench`.

use crate::classed::check_class_unlisted;
use zed_tests::scaling;

/// The preimage of `i mod 10 == 3` over `[0, n]` at n = 1,000,000 and 8,000,000: the formula
/// is the same size at both, the class holds 10^5 values at n and 8 * 10^5 at 8n, and the work
/// is of order 1 in `n` (power 0), since the set is kept as one class with no value listed.
/// Measured 2026-11-23 (Colab VM): 6,201,649 and 6,327,124 instructions, ratio 1.020; bytes
/// 1,383,657 at both. The work stays flat from n = 10^3 to 5.12 * 10^8 (5.7M to 6.5M units).
/// Before `exact::block_set` charged one piece a class, it charged each value of a class as
/// listed, so the exact projection was refused past about 134,800 values and the cover's
/// search ran instead (6.2M units up to n = 1.32 * 10^6, 11.2M from 1.4 * 10^6; ratio 1.825).
/// Negative control, not kept: the same preimage with its class listed (`Classed::met`) gave
/// 139,442,647 and 1,072,239,368 instructions, ratio 7.689, and 35.4M and 273.3M bytes, so
/// the test tells a listed class from an unlisted one.
#[test]
fn a_classed_box_is_not_listed_scales() {
    scaling::check_order(
        "the preimage of a remainder test, by the values of its class",
        1_000_000,
        0,
        |n| check_class_unlisted(n as i64, 10, 3),
    );
}
