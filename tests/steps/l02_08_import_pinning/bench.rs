//! Writing and checking the pins of a package is linear, up to a logarithm, in its units, its
//! imports and its pins: the benchmarks of `scaling.rs`, run by `tools/run_tests.sh --bench` and
//! left out of its default run (TEST-bench-move-rest). Each check they make besides the ratio is
//! made at small sizes by a test of `scaling.rs`.

use zed_tests::scaling;
use zedc::pin::{Pins, apply};
use zedc::query::Db;
use zedc::unit::{Memory, load};

use crate::scaling::{
    doubled_types, importers_of_one, nested_fn_types, pin_edits, pin_file, pinned_fan,
    unpinned_fan, wide_params,
};

/// Checks that loading each package of `pkgs` from `main` is linear in its size, up to a
/// logarithm.
fn linear(what: &str, n: usize, make: fn(usize) -> Memory) {
    let pkgs = scaling::inputs(n, make);
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

/// The address keeps the name of each parameter a call may write (ADDR-param-names): hashing
/// them is linear in their bytes, so pinning a unit whose one function has many named
/// parameters stays linear in them, its checking and elaboration included.
#[test]
fn a_function_of_many_parameters_is_pinned_in_linear_time() {
    linear(
        "pinning a function of many named parameters",
        300,
        wide_params,
    );
}

/// The address keeps the names of the function types inside an export's type
/// (ADDR-nested-param-names): hashing them is linear in the type's nodes, so pinning a unit
/// whose one function's parameter nests many function types stays linear in them, its checking
/// and elaboration included.
#[test]
fn a_parameter_of_many_nested_function_types_is_pinned_in_linear_time() {
    linear(
        "pinning a parameter of many nested function types",
        40,
        nested_fn_types,
    );
}

/// The type of `d{n}` in `d{i} = (d{i-1}, d{i-1})` holds the signature of `d0` at `2^n`
/// places, shared: each signature and row is hashed once for the whole unit, so pinning n such
/// definitions is linear in n where hashing each path would take O(2^n)
/// (ADDR-nested-param-names).
#[test]
fn a_type_shared_by_many_definitions_is_pinned_in_linear_time() {
    linear(
        "pinning definitions each holding the one before twice",
        40,
        doubled_types,
    );
}

#[test]
fn a_pin_file_of_many_pins_is_read_and_written_in_n_log_n_time() {
    let n = 2000;
    let texts = scaling::inputs(n, pin_file);
    scaling::check_order("reading and writing a pin file", n, 1, |k| {
        let pins = Pins::parse(&texts[&k]).unwrap();
        std::hint::black_box(pins.text());
    });
}

#[test]
fn many_pins_are_written_into_one_file_in_n_log_n_time() {
    let n = 2000;
    let cases = scaling::inputs(n, pin_edits);
    scaling::check_order("writing many pins into one file", n, 1, |k| {
        let (text, edits) = &cases[&k];
        std::hint::black_box(apply(text, edits));
    });
}
