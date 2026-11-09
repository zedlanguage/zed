//! The report at the rule of low complexity (DESIGN.md Part G), on families of k and 8k fields.
//! Its work is O(fields + the sizes of the laws) plus, in each group, work proportional to the
//! models it lists; the default report lists at most two per group and stops at the first
//! choice that leads to no model, so on every family it is linear.

use zed_tests::instances::Rng;
use zed_tests::scaling;

use super::hardness::{random_cnf, sat_theory};
use super::trivial::{Mode, Theory, render, report, split};

/// `k` fields of no arguments that no law names.
fn free(k: usize) -> Theory {
    let mut t = Theory::new("Free");
    for i in 0..k {
        t.field(&format!("f{i}"), 0);
    }
    t
}

/// `k / 2` codecs side by side, each its own group with one model.
fn codecs(k: usize) -> Theory {
    let mut t = Theory::new("Codecs");
    for i in 0..k / 2 {
        t.field(&format!("c{i}"), 1).field(&format!("d{i}"), 1).law(
            &format!("roundTrip{i}"),
            "x",
            &format!("d{i}(c{i}(x)) == x"),
        );
    }
    t
}

/// `k` fields of one argument chained by `f_i(x) == f_{i+1}(x)`: one group of three models,
/// all `#a`, all `#b` and all the identity.
fn chain(k: usize) -> Theory {
    let mut t = Theory::new("Chain");
    for i in 0..k {
        t.field(&format!("f{i}"), 1);
    }
    for i in 0..k - 1 {
        t.law(
            &format!("link{i}"),
            "x",
            &format!("f{i}(x) == f{}(x)", i + 1),
        );
    }
    t
}

/// `k` groups of a binary field with `p(x, y) == p(y, x)` (two models each, the constants) and
/// a field of one argument with `q(q(x)) == q(x)` (all three).
fn small_groups(k: usize) -> Theory {
    let mut t = Theory::new("Groups");
    for i in 0..k / 2 {
        t.field(&format!("p{i}"), 2)
            .field(&format!("q{i}"), 1)
            .law(
                &format!("comm{i}"),
                "x y",
                &format!("p{i}(x, y) == p{i}(y, x)"),
            )
            .law(
                &format!("idem{i}"),
                "x",
                &format!("q{i}(q{i}(x)) == q{i}(x)"),
            );
    }
    t
}

/// A field `z` of no arguments and `k` fields of one argument with `f_i(z) == z`: one group
/// with 2^(k+1) models (`z` either value, each `f_i` the identity or the constant `z`). The
/// default report makes one choice per field to reach its first model, so it measures the
/// propagation of a choice; the exhaustive list is exponential in k, as the output is.
fn star(k: usize) -> Theory {
    let mut t = Theory::new("Star");
    t.field("z", 0);
    for i in 0..k {
        t.field(&format!("f{i}"), 1)
            .law(&format!("fix{i}"), "", &format!("f{i}(z) == z"));
    }
    t
}

fn run(t: &Theory, mode: Mode) {
    let r = report(t, mode);
    std::hint::black_box(render(t, &r));
}

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
    let inputs = scaling::inputs(k, |n| {
        let mut rng = Rng::new(0x3c_4f + n as u64);
        sat_theory(n, &random_cnf(&mut rng, n, n * 426 / 100))
    });
    scaling::check("random 3-CNF, Default, by variables", k, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

#[test]
fn the_families_report_what_they_should() {
    let t = chain(50);
    let r = report(&t, Mode::Exhaustive);
    assert_eq!(r.groups.len(), 1);
    assert_eq!(r.groups[0].models.len(), 3);
    assert_eq!(r.groups[0].dead_ends, 0);
    let r = report(&star(3), Mode::Exhaustive);
    assert_eq!(r.groups[0].models.len(), 16);
    assert_eq!(r.groups[0].dead_ends, 0);
    let r = report(&small_groups(10), Mode::Exhaustive);
    let counts: Vec<usize> = r.groups.iter().map(|g| g.models.len()).collect();
    assert_eq!(counts, [2, 3, 2, 3, 2, 3, 2, 3, 2, 3]);
    let text = render(
        &small_groups(4),
        &report(&small_groups(4), Mode::Exhaustive),
    );
    assert!(
        text.ends_with("  models on two values: 2^2 * 3^2.\n"),
        "{text}"
    );
}
