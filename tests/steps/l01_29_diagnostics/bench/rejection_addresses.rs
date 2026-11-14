//! Addresses of a package's problems and of a deep file, at `n` and `8n`
//! (`rejection_addresses.rs`).

use zed_tests::scaling;
use zedc::suppress::InFile;

use crate::rejection_addresses::{a_deep_file, a_package_of_problems, the_problems_of_a_package_addressed};

/// `Package::report_on_disk` on a package with problems in `n` files, each a unit that imports
/// `per` names its import does not define, with every address suppressed: placing, addressing
/// and matching them is within n log n. The package is loaded before the timing. Each problem
/// costs some 60,000 instructions of its own (placing, hashing, writing), so a cost per pair of
/// problems shows only when there are thousands: a `per` of 40 gives 8,400 and 67,200 problems,
/// and a scan of all problems per problem then grows 50 times, not the 24 allowed.
#[test]
fn addressing_the_problems_of_a_package_scales() {
    let n = 200;
    let made = scaling::inputs(n, |m| a_package_of_problems(m, 40));
    scaling::check("addressing the problems of a package in n files", n, |m| {
        the_problems_of_a_package_addressed(&made[&m]);
    });
}

/// The file's part of an address (`InFile::of`) for a file `n` directories deep, with no
/// manifest above it, so every directory up to the file system's root is probed: within n log n
/// in instructions and bytes at n and 8n. The directories are made before the timing. Work in
/// the kernel, which resolves each probe's path, is not counted (`zed_tests::scaling`). At 40 and
/// 320 directories the bytes grew 12.9 times (169 and 2183 bytes), over the limit of 10.5; at 200
/// and 1600, 7.0 times the instructions and 6.7 times the bytes (2026-11-13). 8n must keep the path under the
/// system's limit of 4096 bytes: at 320 and 2560 the file could not be made ("File name too long").
#[test]
fn the_file_part_of_an_address_scales_with_the_depth_of_the_file() {
    let n = 200;
    let files = scaling::inputs(n, a_deep_file);
    scaling::check("the file part of an address, n directories deep", n, |m| {
        InFile::of(&files[&m]).unwrap();
    });
}
