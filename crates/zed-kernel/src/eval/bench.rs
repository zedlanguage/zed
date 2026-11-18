//! The benchmarks of `eval`, run by `tools/run_tests.sh --bench` and left out of its default run
//! (TEST-bench-move-crates). What the benchmark checks besides the ratio, that each key of the
//! domain is found at its position in every form, is checked at small sizes by
//! `a_domain_of_families_finds_each_family_in_every_form` in `eval/tests.rs`.

use super::{key_index, position};
use crate::value::Value;
use crate::value::key_forms::families_of_one_size;

/// Plan row PERF-value-key-sites-bench: the index of a definedness fix over a domain of n
/// families of one size and the same end entries ([`key_index`]), and a lookup of each by a
/// copy built apart ([`position`]): one digest and O(1) expected compares a key, so O(n) in all
/// (the families' sizes are fixed). With the hash that read the size alone, each insert and
/// lookup compared the families before it, O(n^2). The inputs are built before timing; the run
/// does nothing but build the map and look up, so the map is all that is timed.
#[test]
fn the_index_of_a_domain_of_families_scales() {
    let inputs = crate::scaling::inputs(20_000, |n| {
        let mut domain = families_of_one_size(n);
        domain.sort();
        (domain.into_boxed_slice(), families_of_one_size(n))
    });
    crate::scaling::check_order(
        "the index of a fix's domain of n families of one size, and n lookups",
        20_000,
        1,
        |n| {
            let (domain, probes) = &inputs[&n];
            let index = key_index(domain);
            let found = probes
                .iter()
                .filter(|p: &&Value| position(&index, p).is_some())
                .count();
            assert_eq!(found, n);
        },
    );
}
