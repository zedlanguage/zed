//! Reading a unit as source is linear in its bytes: the benchmark of `source.rs`, whose test reads
//! a unit of a few lines.

use zedc::unit::{Dir, Files};

use crate::source::{accented_crlf, package_dir};

#[test]
fn reading_a_unit_as_source_is_linear_in_its_bytes() {
    // The files are written before timing.
    let n = 4000;
    let dirs: Vec<(usize, Dir)> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let d = package_dir(
                &format!("scaling{k}"),
                &[("pricing.zed", &accented_crlf(k))],
            );
            (k, Dir(d))
        })
        .collect();
    let dir = |k: usize| &dirs.iter().find(|(m, _)| *m == k).unwrap().1;
    zed_tests::scaling::check_order("Dir::read of a unit of n lines", n, 1, |k| {
        std::hint::black_box(dir(k).read("pricing.zed"));
    });
}
