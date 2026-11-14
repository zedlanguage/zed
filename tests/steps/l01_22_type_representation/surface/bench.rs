//! The benchmarks of `surface.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `surface.rs`.

use super::*;

#[test]
fn the_text_of_a_type_shared_n_deep_scales() {
    // A pair of the level below, n deep, has 2^n paths: the text names each level once.
    scaling::check("the text of a pair type shared n deep", 1000, |n| {
        let s = shared(n).surface();
        assert_eq!(s.defs.len(), n - 1);
    });
}

#[test]
fn the_text_of_a_type_written_by_name_scales() {
    // Linear in the text: a tuple nested n deep, and a recursive type whose argument is
    // another, n deep.
    let nested = scaling::inputs(1000, |n| {
        (0..n as i64).fold(lit(-1), |t, i| tuple(&[lit(i), t]))
    });
    scaling::check(
        "the text of a tuple nested n deep, written by name",
        1000,
        |n| {
            let s = nested[&n].surface_by_name(TextPlace::Any);
            assert!(s.defs.is_empty());
        },
    );
    let lists = scaling::inputs(100, |n| (0..n).fold(Type::int(), |t, _| list_of(t)));
    scaling::check(
        "the text of a list type of lists n deep, written by name",
        100,
        |n| {
            let s = lists[&n].surface_by_name(TextPlace::Any);
            assert_eq!(s.root.matches("L(").count(), n);
        },
    );
    // A pair of the level below, n deep, shares a part at each level: each level is defined
    // once, so the text grows as n log n (the names' digits), not as the 2^n leaves the
    // pair has when each part is written out at each use.
    let pairs = scaling::inputs(1000, shared);
    let bytes = |n: usize| pairs[&n].surface_by_name(TextPlace::Any).to_string().len();
    scaling::hold(
        "the text of a pair type shared n deep, written by name: n = 1000 and 8000",
        "bytes of text",
        bytes(1000) as u64,
        bytes(8000) as u64,
        1,
    );
    scaling::check(
        "the text of a pair type shared n deep, written by name",
        1000,
        |n| {
            let s = pairs[&n].surface_by_name(TextPlace::Any);
            assert_eq!(s.defs.len(), n - 1);
        },
    );
}

#[test]
fn the_text_of_a_meet_with_a_long_list_scales() {
    let inputs = scaling::inputs(256, less_a_long_list);
    scaling::check("a meet with a decision list of n points", 256, |n| {
        let s = inputs[&n].surface().to_string();
        assert!(!s.contains('_'), "{s}");
        assert_eq!(s.matches(" \\ ").count() + s.matches(" | ").count(), n + 2);
    });
}

#[test]
fn the_text_of_meets_n_deep_scales() {
    // Each meet asks whether its operands hold values outside every point; each node's answer
    // is kept, so the n meets read each node once and not each node below them again.
    let inputs = scaling::inputs(128, meets_n_deep);
    scaling::check("n meets inside each other", 128, |n| {
        let s = inputs[&n].surface().to_string();
        assert!(!s.contains('_'), "{s}");
        assert_eq!(s.matches(" \\ ").count(), n);
    });
}
