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
/// 5 d^2 + 10 d steps and writes 3 d^2 + d runs.
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
        assert_eq!((runs, steps), (3 * d * d + d, (5 * d * d + 10 * d) as u64));
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
/// `x` on the right needs `f` at its last projection. The walk follows the right side's k
/// fields once with the left side's whole tree, which tests none of them, splits at `g0`, and at
/// each pair of `f` nodes enters only the projections whose keys meet, instead of walking the k
/// fields down to each `f` once for each left leaf: 2 k + 8 pairs, 8 k + 17 runs, 18 k + 46
/// steps, and work linear in k, not k^2.
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
        assert_eq!(
            (pairs, runs, steps),
            (2 * k + 8, 8 * k + 17, 18 * k as u64 + 46),
            "the walk takes only steps that reach a pair"
        );
    }
    scaling::check(
        "a shared-field atom with cut subtrees, Default, by fields",
        k,
        |n| run(&inputs[&n], Mode::Default),
    );
}

/// The four families of plan row TRIVIAL-walk-branches, each an atom whose sides share a field,
/// of m fields or arguments; `mirror` swaps the sides. Pairs, tree nodes and the depths of the
/// leaves are linear in m, and so must be the walk's steps and runs:
/// - brief: `f1(f2(w(x, .., x), x), x) == c1(..cm(g(f1(y, x), f2(y, x)))..)`, `w` of m
///   arguments: a right branch point whose children each need a different field the left leaf
///   fixed;
/// - wide: `h(x, .., x) == g1(..gm(h(x, .., x))..)`: a wide node below a long chain;
/// - same: `f1(..fm(x)..) == f1(..fm(x)..)`: a chain the left leaf fixed throughout;
/// - ne: `g(f(x, z), ..) != h(f(z, x), ..)`, `g` and `h` of m arguments: under `!=` the same
///   field on both sides owns no pair.
fn branches(family: &str, mirror: bool, m: usize) -> Theory {
    let mut t = Theory::new("Branches");
    let xs = vec!["x"; m].join(", ");
    let chain = |p: &str, inner: &str| {
        let names: Vec<String> = (1..=m).map(|i| format!("{p}{i}")).collect();
        format!("{}({inner}{}", names.join("("), ")".repeat(m))
    };
    let (binders, lhs, rel, rhs) = match family {
        "brief" => {
            t.field("f1", 2).field("f2", 2).field("w", m).field("g", 2);
            for i in 1..=m {
                t.field(&format!("c{i}"), 1);
            }
            let rhs = chain("c", "g(f1(y, x), f2(y, x))");
            ("x y", format!("f1(f2(w({xs}), x), x)"), "==", rhs)
        }
        "wide" => {
            t.field("h", m);
            for i in 1..=m {
                t.field(&format!("g{i}"), 1);
            }
            (
                "x",
                format!("h({xs})"),
                "==",
                chain("g", &format!("h({xs})")),
            )
        }
        "same" => {
            for i in 1..=m {
                t.field(&format!("f{i}"), 1);
            }
            ("x", chain("f", "x"), "==", chain("f", "x"))
        }
        "ne" => {
            t.field("g", m).field("h", m).field("f", 2);
            let l = vec!["f(x, z)"; m].join(", ");
            let r = vec!["f(z, x)"; m].join(", ");
            ("x z", format!("g({l})"), "!=", format!("h({r})"))
        }
        _ => unreachable!("one of the four families"),
    };
    let body = if mirror {
        format!("{rhs} {rel} {lhs}")
    } else {
        format!("{lhs} {rel} {rhs}")
    };
    t.law("branches", binders, &body);
    t
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
    // The pairs, runs and steps of each family at m, the same for its mirror.
    let size = |family: &str, m: usize| match family {
        "brief" => (6 * m + 15, 20 * m + 40, 38 * m + 95),
        "wide" => (3 * m + 2, 9 * m + 3, 22 * m + 11),
        "same" => (2 * m + 1, 4 * m, 12 * m + 2),
        _ => (4 * m + 2, 14 * m + 7, 30 * m + 21),
    };
    for family in ["brief", "wide", "same", "ne"] {
        for mirror in [false, true] {
            let inputs = scaling::inputs(m, |m| branches(family, mirror, m));
            let name = format!("{family}{}", if mirror { "-m" } else { "" });
            for (&m, t) in &inputs {
                let atom = t.laws[0].clauses()[0][0];
                let (pairs, runs, steps) =
                    t.shared_atom_size(&atom).expect("the sides share fields");
                eprintln!("{name} at m = {m}: {pairs} pairs, {runs} runs, {steps} steps");
                let (p, r, s) = size(family, m);
                assert_eq!((pairs, runs, steps), (p, r, s as u64), "{name} at m = {m}");
            }
            scaling::check(
                &format!("the shared-field family {name}, Default, by m"),
                m,
                |n| run(&inputs[&n], Mode::Default),
            );
        }
    }
}

/// `s(h(x0, .., xm), .., h(x0, .., xm), y0, .., ym) == t(h(y0, .., ym), .., h(y0, .., ym), x0,
/// .., xm)`, m copies of `h` and m distinct binders on each side: `s` and `t` split into m^2
/// pairs of `h` nodes, each with the two constant pairs only, and each `x_i` of the left `h`
/// pairs with the right side's leaf `x_i`. Pairs, runs and steps are quadratic in m, the input's
/// size: a pair of `h` nodes enters both sides together, only at the choices whose children may
/// hold a pair, worked out once for each pair of classes, not all m (m^3 steps before).
#[test]
fn the_joint_splits_scale() {
    let joint = |m: usize| {
        let mut t = Theory::new("Joint");
        t.field("s", 2 * m).field("t", 2 * m).field("h", m);
        let xs: Vec<String> = (0..m).map(|i| format!("x{i}")).collect();
        let ys: Vec<String> = (0..m).map(|i| format!("y{i}")).collect();
        let side = |f: &str, inner: &[String], outer: &[String]| {
            let h = format!("h({})", inner.join(", "));
            format!("{f}({}, {})", vec![h; m].join(", "), outer.join(", "))
        };
        let body = format!("{} == {}", side("s", &xs, &ys), side("t", &ys, &xs));
        t.law(
            "joint",
            &format!("{} {}", xs.join(" "), ys.join(" ")),
            &body,
        );
        t
    };
    let m = 16;
    let inputs = scaling::inputs(m, joint);
    for (&m, t) in &inputs {
        let atom = t.laws[0].clauses()[0][0];
        let (pairs, runs, steps) = t.shared_atom_size(&atom).expect("the sides share `h`");
        eprintln!("the joint family at m = {m}: {pairs} pairs, {runs} runs, {steps} steps");
        assert_eq!(
            (pairs, runs, steps),
            (
                4 * m * m + 4 * m + 2,
                10 * m * m + 16 * m + 7,
                (20 * m * m + 34 * m + 21) as u64
            )
        );
    }
    scaling::check_order("the joint family, Default, by m", m, 2, |n| {
        run(&inputs[&n], Mode::Default)
    });
}

/// The families of plan row TRIVIAL-walk-picks, m copies of `h` of m arguments on each side,
/// each copy of its own class, so that a node of `s` or `t` meets m^2 pairs of `h` nodes of
/// distinct pairs of classes:
///
/// - `alternate`: `s(h(g(x0), x0, g(x0), ..), .., y0, .., ym) == t(h(y0, g(y0), y0, ..), ..,
///   x0, .., xm)`, the i-th `h` at binder `x_i` (or `y_i`), `g` where the left side has a leaf
///   and the reverse, so a leaf meets a subtree at every choice;
/// - `tagged`: `s(h(x0, .., xm, z_i)^m, y.., w..) == t(h(y0, .., ym, w_j)^m, x.., z..)`, leaves
///   of distinct keys at all but the last choice;
/// - `rotations`: `s(h(x_i, .., x_{i-1})^m) == t(h(x_j, .., x_{j-1})^m)`, the m rotations of
///   `h(x0, .., xm)` on each side;
/// - `inner`: `alternate` with `g` at the same choices on both sides, so two subtrees meet;
/// - `keyed`: `alternate` with `x_j` for `y_j` in the right side's `h`, so a leaf meets a
///   subtree that holds its key at the pairs of classes i = j;
/// - `deep`: `tagged` with each right `h` below a unary field of its own, `q_j(h(..))`;
/// - `crossed`: `s(h(g(x_i), x_i, g(x_i), ..)^m, y..) == t(h(x_j, p(x0, .., xm), x_j, ..)^m, y..)`,
///   so a leaf meets a subtree that holds its key at some pairs of classes and not at others, and
///   a subtree of one key or of all; `mirror` is `crossed` with its sides swapped.
fn picks(family: &str, m: usize) -> Theory {
    let mut t = Theory::new("Picks");
    let names = |p: &str| (0..m).map(|i| format!("{p}{i}")).collect::<Vec<String>>();
    let (xs, ys, zs, ws) = (names("x"), names("y"), names("z"), names("w"));
    let side = |f: &str, hs: Vec<String>, rest: &[&[String]]| {
        let mut args = hs;
        for r in rest {
            args.extend(r.iter().cloned());
        }
        format!("{f}({})", args.join(", "))
    };
    // `h` of m arguments at binder `v`: `g(v)` at the choices of this parity, else `v`.
    let alternate = |v: &str, parity: usize| {
        let args: Vec<String> = (0..m)
            .map(|c| {
                if c % 2 == parity {
                    format!("g({v})")
                } else {
                    v.to_string()
                }
            })
            .collect();
        format!("h({})", args.join(", "))
    };
    let tagged = |a: &[String], last: &str| format!("h({}, {last})", a.join(", "));
    let all = |sets: &[&[String]]| {
        sets.iter()
            .map(|s| s.join(" "))
            .collect::<Vec<_>>()
            .join(" ")
    };
    let (binders, l, r) = match family {
        "crossed" | "mirror" => {
            t.field("s", 2 * m)
                .field("t", 2 * m)
                .field("h", m)
                .field("g", 1)
                .field("p", m);
            let l = side("s", xs.iter().map(|x| alternate(x, 0)).collect(), &[&ys]);
            let every = format!("p({})", xs.join(", "));
            let crossed = |x: &String| {
                let args: Vec<&str> = (0..m)
                    .map(|c| {
                        if c % 2 == 0 {
                            x.as_str()
                        } else {
                            every.as_str()
                        }
                    })
                    .collect();
                format!("h({})", args.join(", "))
            };
            let r = side("t", xs.iter().map(crossed).collect(), &[&ys]);
            let (l, r) = if family == "mirror" { (r, l) } else { (l, r) };
            (all(&[&xs, &ys]), l, r)
        }
        "alternate" | "inner" | "keyed" => {
            t.field("s", 2 * m)
                .field("t", 2 * m)
                .field("h", m)
                .field("g", 1);
            let p = usize::from(family != "inner");
            let r = if family == "keyed" { &xs } else { &ys };
            let l = side("s", xs.iter().map(|x| alternate(x, 0)).collect(), &[&ys]);
            let r = side("t", r.iter().map(|y| alternate(y, p)).collect(), &[&xs]);
            (all(&[&xs, &ys]), l, r)
        }
        "tagged" | "deep" => {
            t.field("s", 3 * m).field("t", 3 * m).field("h", m + 1);
            let l = side(
                "s",
                zs.iter().map(|z| tagged(&xs, z)).collect(),
                &[&ys, &ws],
            );
            let hs = ws.iter().enumerate().map(|(j, w)| {
                if family == "deep" {
                    format!("q{j}({})", tagged(&ys, w))
                } else {
                    tagged(&ys, w)
                }
            });
            if family == "deep" {
                for j in 0..m {
                    t.field(&format!("q{j}"), 1);
                }
            }
            let r = side("t", hs.collect(), &[&xs, &zs]);
            (all(&[&xs, &ys, &zs, &ws]), l, r)
        }
        _ => {
            t.field("s", m).field("t", m).field("h", m);
            let rotation = |i: usize| {
                let a: Vec<String> = (0..m).map(|c| xs[(c + i) % m].clone()).collect();
                format!("h({})", a.join(", "))
            };
            let l = side("s", (0..m).map(rotation).collect(), &[]);
            let r = side("t", (0..m).map(rotation).collect(), &[]);
            (all(&[&xs]), l, r)
        }
    };
    t.law("picks", &binders, &format!("{l} == {r}"));
    t
}

/// On each family of [`picks`] the walk's pairs, runs and steps are quadratic in m, linear in
/// the input's size, and the default report is of that order, by m at m and 8m: at a node split
/// against a node of `h`, the lists of the choices of all the pairs of classes it meets are made
/// together from the other node's live children, a lookup each (`Theory::pair_form`). Before
/// plan row TRIVIAL-walk-picks each list was made alone from the smaller side's live children,
/// m^3 steps: at m = 64, 387214, 367246 and 321102 steps and 156, 93 and 81 million
/// instructions, where these take 141970, 105874 and 63442 steps (COMPLEXITY.md C32).
#[test]
fn the_picks_scale() {
    let m = 8;
    let size = |family: &str, m: usize| match family {
        "alternate" => (
            6 * m * m + 4 * m + 2,
            14 * m * m + 20 * m + 7,
            34 * m * m + 42 * m + 18,
        ),
        "tagged" => (
            4 * m * m + 6 * m + 2,
            10 * m * m + 24 * m + 7,
            25 * m * m + 54 * m + 18,
        ),
        _ => (
            3 * m * m + 4 * m + 2,
            5 * m * m + 14 * m + 7,
            15 * m * m + 31 * m + 18,
        ),
    };
    for family in ["alternate", "tagged", "rotations"] {
        let inputs = scaling::inputs(m, |m| picks(family, m));
        for (&m, t) in &inputs {
            let atom = t.laws[0].clauses()[0][0];
            let (pairs, runs, steps) = t.shared_atom_size(&atom).expect("the sides share `h`");
            eprintln!("{family} at m = {m}: {pairs} pairs, {runs} runs, {steps} steps");
            let (p, r, s) = size(family, m);
            assert_eq!(
                (pairs, runs, steps),
                (p, r, s as u64),
                "{family} at m = {m}"
            );
        }
        scaling::check_order(
            &format!("the picks family {family}, Default, by m"),
            m,
            2,
            |n| run(&inputs[&n], Mode::Default),
        );
    }
}

/// The lists made together keep exactly the choices the lists made one by one keep: the report
/// on each family of [`picks`] at m = 2 and 3 agrees with brute force, and on `keyed` at m = 4,
/// which reaches the lookup of each key below a subtree, as m = 2 and 3 do not.
#[test]
fn the_picks_agree_with_brute_force() {
    for family in [
        "alternate",
        "tagged",
        "rotations",
        "inner",
        "keyed",
        "deep",
        "crossed",
        "mirror",
    ] {
        for m in [2, 3] {
            super::brute::check(&picks(family, m));
        }
    }
    super::brute::check(&picks("keyed", 4));
}
