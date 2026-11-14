//! The texts of `print.rs` at `d` and `8d` levels: their lengths grow at most about 8 times
//! (a logarithm included), and the time to the order check. Each term is built before the
//! timing; `print.rs` holds the texts at small sizes.

use std::collections::HashMap;

use zed_kernel::Term;
use zed_tests::scaling::{self, FACTOR};

use crate::print::{arms, lets, shown};
use crate::scaling::deep;

/// The text's length at `d` and at `FACTOR * d` is held to a constant over the factor (a
/// logarithm included), and the time to the order check.
fn scales(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> Term,
    print: impl Fn(&Term) -> String + Sync,
) {
    let terms: HashMap<usize, Term> = scaling::inputs(n, make);
    let lens: HashMap<usize, usize> = terms.iter().map(|(&d, t)| (d, print(t).len())).collect();
    assert!(
        lens[&(FACTOR * n)] <= 3 * FACTOR * lens[&n],
        "{what}: the text is {} long at {n}, {} at {}",
        lens[&n],
        lens[&(FACTOR * n)],
        FACTOR * n
    );
    scaling::check(what, n, |d| {
        assert_eq!(print(&terms[&d]).len(), lens[&d]);
    });
}

#[test]
fn writing_nested_ifs_over_one_part_scales() {
    deep(|| {
        scales(
            "pretty_in on d nested ifs over one part",
            400,
            |d| arms(d, true),
            shown,
        );
        scales(
            "Display on d nested ifs over one part",
            400,
            |d| arms(d, true),
            |t| t.to_string(),
        );
    });
}

#[test]
fn writing_nested_lets_whose_part_reads_a_name_bound_twice_scales() {
    deep(|| {
        scales(
            "pretty_in on d nested ifs binding a name over one part",
            400,
            lets,
            shown,
        );
        scales(
            "Display on d nested ifs binding a name over one part",
            400,
            lets,
            |t| t.to_string(),
        );
    });
}
