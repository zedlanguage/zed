//! The report at the rule of low complexity (DESIGN.md Part G), on families of k and 8k fields.
//! Its work is O(fields + the sizes of the laws) plus, in each group, work proportional to the
//! models it lists; the default report lists at most two per group and stops at the first
//! choice that leads to no model, so on every family it is linear. The benchmarks of this step,
//! run by `tools/run_tests.sh --bench`; `scaling.rs` runs each family at small sizes and checks
//! the walk's counts of pairs, runs and steps.

use zed_tests::scaling;

use super::scaling::{
    BRANCHES, PICKS, branches, chain, codecs, cut, free, hard, joint, one_large_atom, one_long_or,
    one_wide_field, picks, run, shared, small_groups, star,
};
use super::trivial::{Mode, Theory, split};

#[test]
fn the_report_scales() {
    let k = 1000;
    for (what, make) in [
        ("free fields", free as fn(usize) -> Theory),
        ("codecs side by side", codecs),
        ("a chain of equations", chain),
        ("small groups", small_groups),
    ] {
        let inputs = scaling::inputs(k, make);
        for mode in [Mode::Default, Mode::Exhaustive] {
            scaling::check(&format!("{what}, {mode:?}, by fields"), k, |n| {
                run(&inputs[&n], mode)
            });
        }
    }
}

#[test]
fn the_default_report_scales_on_one_large_group() {
    let inputs = scaling::inputs(1000, star);
    scaling::check("a star, Default, by fields", 1000, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

/// One atom of k fields: the report builds the atom in O(k log k), not as the k^2 pairs of
/// paths, and its default search, which chooses every field, removes each choice and each path
/// at most once per descent.
#[test]
fn one_large_atom_scales() {
    let inputs = scaling::inputs(1000, one_large_atom);
    scaling::check("one large atom, Default, by fields", 1000, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

/// One clause of k atoms: the report checks it only once at most one of its fields is open,
/// each time in O(k log k), not after every choice.
#[test]
fn one_long_or_scales() {
    let inputs = scaling::inputs(1000, one_long_or);
    scaling::check("one long `||`, Default, by fields", 1000, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

/// One clause whose last open field has k / 2 arguments: the report checks the clause once per
/// choice of that field only on the atoms whose paths reach it, and not again as the field's
/// choices are removed, so the work is linear, not the choices times the clause. Default report
/// only: the constants have exponentially many models, which `@exhaustive` would list.
#[test]
fn one_wide_field_scales() {
    let inputs = scaling::inputs(1000, one_wide_field);
    scaling::check("one wide field in an `||`, Default, by fields", 1000, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

#[test]
fn the_split_scales() {
    let inputs = scaling::inputs(1000, small_groups);
    scaling::check("the split into groups, by fields", 1000, |n| {
        std::hint::black_box(split(&inputs[&n]));
    });
}

/// On random 3-CNF at the density where satisfiable and unsatisfiable formulas are about as
/// common, the default report stops at the first dead end, so it stays linear where the
/// exhaustive search is exponential.
#[test]
fn the_default_report_scales_on_the_hard_family() {
    let k = 1000;
    let inputs = scaling::inputs(k, hard);
    scaling::check("random 3-CNF, Default, by variables", k, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

/// The default report on [`shared`] is of order d^2 log d, the pairs times a log, by d at d and
/// 8d.
#[test]
fn a_shared_field_atom_scales() {
    let d = 50;
    let inputs = scaling::inputs(d, shared);
    scaling::check_order("a shared-field atom, Default, by fields", d, 2, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

/// The default report on [`cut`] is linear in k, not k^2.
#[test]
fn a_shared_field_atom_with_cut_subtrees_scales() {
    let k = 200;
    let inputs = scaling::inputs(k, cut);
    scaling::check(
        "a shared-field atom with cut subtrees, Default, by fields",
        k,
        |n| run(&inputs[&n], Mode::Default),
    );
}

/// The default report on each family of [`branches`] and its mirror is of order m log m, by m at
/// m and 8m: the walk over pairs of nodes, one of each side, follows a field the other side
/// fixed, splits both sides on a field both test and enters only the choices that can hold a
/// pair, and skips the rest of a class of children after one gave no pair, so its steps and runs
/// are linear in m, the same on a family and its mirror (`Theory::pair_form`). The walk before
/// plan row TRIVIAL-walk-branches, of the left side's tree and at each of its leaves the right
/// side's, took steps or runs quadratic in m on brief, wide, same and ne, 26 to 72 times the
/// instructions at m = 128 and 1024 (COMPLEXITY.md C32).
#[test]
fn the_shared_field_families_scale() {
    let m = 128;
    for family in BRANCHES {
        for mirror in [false, true] {
            let inputs = scaling::inputs(m, |m| branches(family, mirror, m));
            let name = format!("{family}{}", if mirror { "-m" } else { "" });
            scaling::check(
                &format!("the shared-field family {name}, Default, by m"),
                m,
                |n| run(&inputs[&n], Mode::Default),
            );
        }
    }
}

/// The default report on [`joint`] is quadratic in m, linear in the input's size.
#[test]
fn the_joint_splits_scale() {
    let m = 16;
    let inputs = scaling::inputs(m, joint);
    scaling::check_order("the joint family, Default, by m", m, 2, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

/// On each family of [`picks`] the default report is quadratic in m, linear in the input's size,
/// by m at m and 8m (`picks_size` in `scaling.rs` gives the walk's counts).
#[test]
fn the_picks_scale() {
    let m = 8;
    for family in PICKS {
        let inputs = scaling::inputs(m, |m| picks(family, m));
        scaling::check_order(
            &format!("the picks family {family}, Default, by m"),
            m,
            2,
            |n| run(&inputs[&n], Mode::Default),
        );
    }
}
