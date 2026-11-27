//! The checks of `dag.rs` at `d` and `8d` levels: staging reads a part shared by two places
//! once, so its time is linear in the levels, not in the `2^d` places. Each unit is built
//! before the timing; `dag.rs` checks what each mix gives at small depths.

use zed_kernel::term::build::{lit, var};
use zed_tests::scaling;
use zedc::stage::{self, Stage, color, free, passed};

use crate::dag::{
    a_join_and_a_tuple, built, calls_at, composed, distinct, doubled, ifs, left_unit, lets,
    mixed_nodes_of, nodes, the_term_left_reported, unit,
};

#[test]
fn mixing_nested_ifs_whose_arms_are_one_part_scales() {
    let n = 1000;
    let units = scaling::inputs(n, |d| unit(d, true));
    scaling::check_order(
        "stage::mix on d nested ifs whose two arms are one part",
        n,
        1,
        |d| {
            let (mixed, _) = stage::mix(&units[&d], &["main"]);
            assert_eq!(distinct(&mixed.defs[1].term), 2 * d + 2);
        },
    );
}

#[test]
fn reading_nested_ifs_whose_arms_are_one_part_scales() {
    let n = 1000;
    let units = scaling::inputs(n, |d| unit(d, true));
    scaling::check_order(
        "stage::free on d nested ifs whose two arms are one part",
        n,
        1,
        |d| assert_eq!(free(&units[&d].defs[1].term).len(), 1, "`f`"),
    );
    // No `lam` or call above or below: the term of names, literals, primitives and `if`s
    // alone, read without `Frees`, each shared node once.
    let bare = scaling::inputs(n, |d| ifs(d, true, &var("m")));
    scaling::check_order(
        "stage::free on d nested ifs of names alone whose two arms are one part",
        n,
        1,
        |d| assert_eq!(free(&bare[&d]).len(), 2, "`m` and `n`"),
    );
    scaling::check_order(
        "stage::color, free names and effects, on d nested ifs whose two arms are one part",
        n,
        1,
        |d| assert_eq!(color(&units[&d])[1].1, Stage::Build),
    );
    scaling::check_order(
        "stage::passed on d nested ifs whose two arms are one part",
        n,
        1,
        |d| assert_eq!(passed(&units[&d], "f", 1).len(), 1),
    );
}

#[test]
fn mixing_nested_lets_of_a_parameter_over_one_body_scales() {
    let n = 1000;
    let units = scaling::inputs(n, |d| lets(d, true));
    scaling::check_order(
        "stage::mix on d nested ifs whose two arms are lets of a parameter over one body",
        n,
        1,
        |d| {
            let (mixed, _) = stage::mix(&units[&d], &["main"]);
            assert_eq!(distinct(&mixed.defs[0].term), 6 * d + 1);
        },
    );
}

// The cases of one built value and of two are two tests: together they took 20 s alone at
// load 42.
#[test]
fn mixing_nested_lets_of_one_built_value_over_one_body_scales() {
    let n = 1000;
    let same = scaling::inputs(n, |d| built(d, 0, 0, true));
    scaling::check_order(
        "stage::mix on d nested ifs whose two arms are lets of one built value over one body",
        n,
        1,
        |d| {
            let (mixed, _) = stage::mix(&same[&d], &["main"]);
            assert_eq!(distinct(&mixed.defs[0].term), nodes(d, true));
        },
    );
}

#[test]
fn mixing_nested_lets_of_two_built_values_over_one_body_scales() {
    // The mixed term has a node for each value of `x` at each level, d(d + 7)/2 in all.
    // That size is forced, so power 2: with a = 1 and b = 2, level k has k + 1 values of
    // `x` (`nodes` in `dag.rs` counts them), and two distinct values give two distinct mixed
    // subterms, as their smallest leaf differs, so a shared term has at least sum(k + 1) =
    // Theta(d^2) nodes. The mix made d(d + 1) evaluations (1260 at 35, 78680 at 280, local
    // job dv115), each of one `let` and no stub; that each costs O(1) is measured, not proved
    // (BENCH-stage-mix-two-values-limit: 62.44 times the evaluations, 62.59 the instructions).
    // At d = 50 and 400 this took 19 s alone at load 45 (TEST-bench-move-l0125).
    let n = 35;
    let apart = scaling::inputs(n, |d| built(d, 1, 2, true));
    scaling::check_order(
        "stage::mix on d nested ifs whose two arms are lets of two built values over one body",
        n,
        2,
        |d| {
            let (mixed, _) = stage::mix(&apart[&d], &["main"]);
            assert_eq!(distinct(&mixed.defs[0].term), nodes(d, false));
        },
    );
}

/// A function bound on each path is numbered by its kind, and a part that calls it is keyed by
/// what it asked of it (COMPLEXITY.md F83): the `2^k` functions on the paths to level `k` take
/// `k + 1` values at 1, so the parts below level `k` are mixed once for each, and the mixed
/// term has `(3d^2 + 17d - 6) / 2` nodes, not `2^d`. The quadratic is the output's own: it
/// holds `d(d + 1) / 2` distinct `if`s (the argument is at `Mixer::eval`), so the test allows
/// power 2. Plan row STAGE-scaling-10_5, back from the deferred tests (TESTS-defer-failing,
/// 2026-11-13: 84.6 times the bytes from 12 to 96 on main cdf07ac4f), under the limit since
/// `Mixer::take` skips the parts that ask nothing (86.5 times before, 66.1 after, locally).
#[test]
fn mixing_lets_of_composed_functions_over_one_body_scales() {
    let n = 12;
    let units = scaling::inputs(n, |d| composed(d, true));
    scaling::check_order(
        "stage::mix on d nested ifs whose two arms are lets of two composed functions over one body",
        n,
        2,
        |d| {
            let (mixed, _) = stage::mix(&units[&d], &["main"]);
            assert_eq!(distinct(&mixed.defs[0].term), (3 * d * d + 17 * d - 6) / 2);
        },
    );
}

/// A call at `("s0" ++ ("s1" ++ … "s(n-1)"), (0, (1, … (n-1, 0))))`, n distinct strings joined and
/// n nested pairs, is keyed by its answer at n and 8n: naming the join and the tuples costs
/// O(n log N) dictionary steps, and the part is still shared by both arms (item
/// STAGE-joined-eq-build).
#[test]
fn keying_a_call_at_a_join_and_a_tuple_of_n_parts_scales() {
    let n = 1000;
    let args = scaling::inputs(n, a_join_and_a_tuple);
    let at_literal = mixed_nodes_of(lit(1i64));
    scaling::check_order(
        "stage::mix of a call at a join and a tuple of n parts",
        n,
        1,
        |d| assert_eq!(mixed_nodes_of(args[&d].clone()), at_literal),
    );
}

/// The values passed at n calls, the i-th at `"s(i/2)"` (i/2 in four digits) doubled 60 times
/// or at `i/2` doubled 40 times as a tuple, each built apart: each pair of equal values is one
/// value, keyed by its canonical form, so the work is O(n log n) and no value is read whole
/// (item STAGE-byte-keys).
/// The strings are doubled 60 times, not 62: from `"s100"` on, a seed of 4 bytes doubled 62
/// times is 2^64 bytes, past the longest string, so its evaluation stops and the call is left
/// to run, not passed (measured: 100 values passed at 800 calls). Doubled 60 times, a seed of
/// up to 16 bytes stays below 2^64. The seeds are all 5 bytes: with `"s{i/2}"`, 2 to 3 bytes at
/// n and 4 at 8n, the strings differed in period and so in the size of their summaries
/// (`text::names`), 12.2 times the bytes at 8n against 8.9 with one width (std VM, 2026-11-22,
/// 10.3 times the processor time; each join is about 27 MB and 50 ms to name).
#[test]
fn the_values_passed_at_long_joins_scale() {
    let n = 100;
    let joins = scaling::inputs(n, |k| {
        calls_at(
            (0..k)
                .map(|i| doubled(lit(format!("s{:04}", i / 2).as_str()), 60, false))
                .collect(),
        )
    });
    scaling::check(
        "stage::passed at n strings, each doubled 60 times, built apart",
        n,
        |k| assert_eq!(passed(&joins[&k], "f", 1).len(), k / 2),
    );
    let tuples = scaling::inputs(n, |k| {
        calls_at(
            (0..k)
                .map(|i| doubled(lit((i / 2) as i64), 40, true))
                .collect(),
        )
    });
    scaling::check(
        "stage::passed at n tuples, each doubled 40 times, built apart",
        n,
        |k| assert_eq!(passed(&tuples[&k], "f", 1).len(), k / 2),
    );
}

/// The report of a term left to run holds the term, its arms still one node; its text,
/// printed as a tree, is 2^d long (STAGE-print). Before repair 5 the report held
/// `t.to_string()`, 2^d time and text (repair 4, release build, load 9: 2.3, 36, 143, 589,
/// 2238 ms and 30.7 KB, 492 KB, 1.97 MB, 7.86 MB, 31.5 MB at d = 10, 14, 16, 18, 20).
#[test]
fn reporting_a_term_left_to_run_whose_arms_are_one_part_scales() {
    let n = 1000;
    let units = scaling::inputs(n, left_unit);
    scaling::check_order(
        "stage::mix and its report of a term left to run, on d nested ifs whose two arms \
         are one node",
        n,
        1,
        |d| the_term_left_reported(&units[&d]),
    );
}
