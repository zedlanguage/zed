//! Writing and checking the pins of a package is linear, up to a logarithm, in its units, its
//! imports and its pins: the benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and
//! left out of its default run (TEST-bench-move-rest). Each check they make besides the ratio is
//! made at small sizes by a test of `scaling.rs`.

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::pin::{Edit, Pins, apply};
use zedc::query::Db;
use zedc::unit::{Memory, load};

use crate::scaling::{importers_of_one, pin_edits, pin_file, pinned_fan, unpinned_fan};

/// Checks that loading each package of `pkgs` from `main` is linear in its size, up to a
/// logarithm.
fn linear(what: &str, n: usize, make: fn(usize) -> Memory) {
    let pkgs: HashMap<usize, Memory> = [n, 8 * n].into_iter().map(|k| (k, make(k))).collect();
    scaling::check_order(what, n, 1, |k| {
        std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
    });
}

#[test]
fn a_unit_importing_many_units_is_pinned_in_linear_time() {
    linear("pinning a fan of imports", 150, unpinned_fan);
}

#[test]
fn a_unit_importing_many_pinned_units_is_checked_in_linear_time() {
    linear("checking a fan of pinned imports", 150, pinned_fan);
}

#[test]
fn many_units_importing_one_unit_are_pinned_in_linear_time() {
    linear("pinning many importers of one unit", 150, importers_of_one);
}

#[test]
fn a_pin_file_of_many_pins_is_read_and_written_in_n_log_n_time() {
    let n = 2000;
    let texts: HashMap<usize, String> = [n, 8 * n].into_iter().map(|k| (k, pin_file(k))).collect();
    scaling::check_order("reading and writing a pin file", n, 1, |k| {
        let pins = Pins::parse(&texts[&k]).unwrap();
        std::hint::black_box(pins.text());
    });
}

#[test]
fn many_pins_are_written_into_one_file_in_n_log_n_time() {
    let n = 2000;
    let cases: HashMap<usize, (String, Vec<Edit>)> =
        [n, 8 * n].into_iter().map(|k| (k, pin_edits(k))).collect();
    scaling::check_order("writing many pins into one file", n, 1, |k| {
        let (text, edits) = &cases[&k];
        std::hint::black_box(apply(text, edits));
    });
}
