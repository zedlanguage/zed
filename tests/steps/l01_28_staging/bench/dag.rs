//! The checks of `dag.rs` at `d` and `8d` levels: staging reads a part shared by two places
//! once, so its time is linear in the levels, not in the `2^d` places. Each unit is built
//! before the timing; `dag.rs` checks what each mix gives at small depths.

use zed_kernel::term::build::{lit, var};
use zed_tests::scaling;
use zedc::stage::{self, Stage, color, free, passed};

use crate::dag::{
    a_join_and_a_tuple, built, distinct, ifs, left_unit, lets, mixed_nodes_of, nodes,
    the_term_left_reported, unit,
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
