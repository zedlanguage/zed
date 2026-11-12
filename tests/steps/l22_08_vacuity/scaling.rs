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

/// A balanced tree of the fields `{prefix}0` to `{prefix}{n - 1}`, each of two arguments, with
/// `x` at the leaves: written by a loop over the levels, so its text nests only to depth log n.
fn tree(prefix: &str, n: usize) -> String {
    // Level by level from the leaves: each node takes two terms of the level below.
    let mut level: Vec<String> = vec!["x".to_string(); n + 1];
    let mut next_field = 0;
    while level.len() > 1 {
        let mut up = Vec::with_capacity(level.len() / 2 + 1);
        let mut it = level.into_iter();
        while let Some(a) = it.next() {
            match it.next() {
                Some(b) => {
                    up.push(format!("{prefix}{next_field}({a}, {b})"));
                    next_field += 1;
                }
                None => up.push(a),
            }
        }
        level = up;
    }
    assert_eq!(next_field, n, "a tree of n fields has n + 1 leaves");
    level.pop().expect("one root")
}

/// One law, one atom: two trees of `k / 2` fields each, `f` on the left and `g` on the right,
/// with `f(..) == g(..)`. Each side has about `3k / 2` paths, so the pairs of paths are about
/// `k^2`; the sides name different fields, so the atom is split at its end symbol.
fn one_large_atom(k: usize) -> Theory {
    let mut t = Theory::new("Large");
    for i in 0..k / 2 {
        t.field(&format!("f{i}"), 2);
    }
    for i in 0..k / 2 {
        t.field(&format!("g{i}"), 2);
    }
    let body = format!("{} == {}", tree("f", k / 2), tree("g", k / 2));
    t.law("large", "x", &body);
    t
}

/// k constants, not all equal: one law, an `||` of k - 1 comparisons, so one clause.
fn one_long_or(k: usize) -> Theory {
    let mut t = Theory::new("LongOr");
    for i in 0..k {
        t.field(&format!("c{i}"), 0);
    }
    let body: Vec<String> = (1..k).map(|i| format!("c{} != c{i}", i - 1)).collect();
    t.law("notAllEqual", "", &body.join(" || "));
    t
}

/// k / 2 constants and, declared last, one field `w` of k / 2 arguments, in one clause:
/// `w(c0, ..) != c0 || c0 != c1 || ..`. Once the constants are chosen `w` is the clause's one
/// open field, and k / 2 of its k / 2 + 2 choices fail the clause.
fn one_wide_field(k: usize) -> Theory {
    let mut t = Theory::new("WideField");
    let m = k / 2;
    for i in 0..m {
        t.field(&format!("c{i}"), 0);
    }
    t.field("w", m);
    let args: Vec<String> = (0..m).map(|i| format!("c{i}")).collect();
    let mut body = vec![format!("w({}) != c0", args.join(", "))];
    body.extend((1..m).map(|i| format!("c{} != c{i}", i - 1)));
    t.law("wide", "", &body.join(" || "));
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

/// The family of plan row TRIVIAL-shared-atom: `f1(..fd(x)..) == fd(..f1(x)..)` over fields of
/// one argument. Its sides share every field, so the atom is held as the pairs of paths that
/// agree: d^2 + d + 1 pairs, which hold about 2 d^3 / 3 choices. The pairs are numbered and
/// written as runs, never one by one with their choices, so the default report is of order
/// d^2 log d, the pairs times a log, by d at d and 8d; the walk that numbers the pairs takes
/// 2 d^2 + 6 d + 2 steps and writes 3 d^2 + d runs.
#[test]
fn a_shared_field_atom_scales() {
    let shared = |d: usize| {
        let mut t = Theory::new("Shared");
        for i in 1..=d {
            t.field(&format!("f{i}"), 1);
        }
        let nest = |order: &mut dyn Iterator<Item = usize>| {
            let names: Vec<String> = order.map(|i| format!("f{i}")).collect();
            format!("{}(x{}", names.join("("), ")".repeat(d))
        };
        let body = format!("{} == {}", nest(&mut (1..=d)), nest(&mut (1..=d).rev()));
        t.law("shared", "x", &body);
        t
    };
    let d = 50;
    let inputs = scaling::inputs(d, shared);
    for (&d, t) in &inputs {
        let atom = t.laws[0].clauses()[0][0];
        let (pairs, runs, steps) = t.shared_atom_size(&atom).expect("the sides share fields");
        assert_eq!(pairs, d * d + d + 1);
        assert_eq!(
            (runs, steps),
            (3 * d * d + d, (2 * d * d + 6 * d + 2) as u64)
        );
        eprintln!("a shared-field atom at d = {d}: {pairs} pairs, {runs} runs, {steps} steps");
    }
    scaling::check_order("a shared-field atom, Default, by fields", d, 2, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

/// An atom whose left side fixes a field that cuts off the right side's subtrees:
/// `f(x, .., x) == g1(..gk(g0(f(y, .., y, x), f(y, .., y, x)))..)` with `f` of k arguments. The
/// left side has k leaves at `x`, one for each projection of `f`, and only the last projection
/// reaches an `x` on the right, below k fields the left side does not name. Every path to an
/// `x` on the right needs `f` at its last projection, so the walk refuses the right side at its
/// root for each of the other k - 1 leaves instead of walking the k fields down to each `f`:
/// 2 k + 8 pairs, and work linear in k, not k^2.
#[test]
fn a_shared_field_atom_with_cut_subtrees_scales() {
    let cut = |k: usize| {
        let mut t = Theory::new("Cut");
        t.field("f", k).field("g0", 2);
        for i in 1..=k {
            t.field(&format!("g{i}"), 1);
        }
        let xs = vec!["x"; k].join(", ");
        let last = format!("f({}x)", "y, ".repeat(k - 1));
        let names: Vec<String> = (1..=k).map(|i| format!("g{i}")).collect();
        let body = format!(
            "f({xs}) == {}(g0({last}, {last}){}",
            names.join("("),
            ")".repeat(k)
        );
        t.law("cut", "x y", &body);
        t
    };
    let k = 200;
    let inputs = scaling::inputs(k, cut);
    for (&k, t) in &inputs {
        let atom = t.laws[0].clauses()[0][0];
        let (pairs, runs, steps) = t.shared_atom_size(&atom).expect("the sides share `f`");
        eprintln!("a cut shared-field atom at k = {k}: {pairs} pairs, {runs} runs, {steps} steps");
        assert_eq!(pairs, 2 * k + 8);
        assert_eq!(
            steps,
            6 * k as u64 + 20,
            "the walk takes only steps that reach a pair"
        );
    }
    scaling::check(
        "a shared-field atom with cut subtrees, Default, by fields",
        k,
        |n| run(&inputs[&n], Mode::Default),
    );
}
