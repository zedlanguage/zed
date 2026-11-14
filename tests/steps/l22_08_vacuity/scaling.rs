//! The families the benchmarks of `bench.rs` report on, k and 8k fields each, and what the
//! report must give on each, checked here at small sizes and, for the walk's counts of pairs,
//! runs and steps, at the timed sizes, which cost no report (TEST-bench-move-rest, P170).

use zed_tests::instances::Rng;

use super::hardness::{random_cnf, sat_theory};
use super::trivial::{Mode, Theory, render, report, split};

/// `k` fields of no arguments that no law names.
pub(super) fn free(k: usize) -> Theory {
    let mut t = Theory::new("Free");
    for i in 0..k {
        t.field(&format!("f{i}"), 0);
    }
    t
}

/// `k / 2` codecs side by side, each its own group with one model.
pub(super) fn codecs(k: usize) -> Theory {
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
pub(super) fn chain(k: usize) -> Theory {
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
pub(super) fn small_groups(k: usize) -> Theory {
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
pub(super) fn star(k: usize) -> Theory {
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
pub(super) fn one_large_atom(k: usize) -> Theory {
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
pub(super) fn one_long_or(k: usize) -> Theory {
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
pub(super) fn one_wide_field(k: usize) -> Theory {
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

pub(super) fn run(t: &Theory, mode: Mode) {
    let r = report(t, mode);
    std::hint::black_box(render(t, &r));
}

/// Random 3-CNF of `n` variables at the density where satisfiable and unsatisfiable formulas
/// are about as common, the seed fixed by `n`.
pub(super) fn hard(n: usize) -> Theory {
    let mut rng = Rng::new(0x3c_4f + n as u64);
    sat_theory(n, &random_cnf(&mut rng, n, n * 426 / 100))
}

/// Every family the benchmarks of `bench.rs` time runs through the default report, and the four
/// of `the_report_scales` through the exhaustive one too, and is split into groups, at small
/// sizes; the timing of each is held in `bench.rs`.
#[test]
fn each_benchmark_family_is_reported_at_small_sizes() {
    let both: [fn(usize) -> Theory; 4] = [free, codecs, chain, small_groups];
    let default: [fn(usize) -> Theory; 5] =
        [star, one_large_atom, one_long_or, one_wide_field, hard];
    for k in [3, 4, 9] {
        for make in both {
            run(&make(k), Mode::Default);
            run(&make(k), Mode::Exhaustive);
        }
        for make in default {
            run(&make(k), Mode::Default);
        }
        assert_eq!(split(&small_groups(k)).groups.len(), 2 * (k / 2));
    }
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
/// d^2 log d, the pairs times a log (held in `bench.rs`); the walk that numbers the pairs takes
/// 5 d^2 + 10 d steps and writes 3 d^2 + d runs.
pub(super) fn shared(d: usize) -> Theory {
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
}

/// The pairs, runs and steps of the walk over the one atom of `t`.
fn atom_size(t: &Theory) -> (usize, usize, u64) {
    let atom = t.laws[0].clauses()[0][0];
    t.shared_atom_size(&atom).expect("the sides share fields")
}

/// An atom whose left side fixes a field that cuts off the right side's subtrees:
/// `f(x, .., x) == g1(..gk(g0(f(y, .., y, x), f(y, .., y, x)))..)` with `f` of k arguments. The
/// left side has k leaves at `x`, one for each projection of `f`, and only the last projection
/// reaches an `x` on the right, below k fields the left side does not name. Every path to an
/// `x` on the right needs `f` at its last projection. The walk follows the right side's k
/// fields once with the left side's whole tree, which tests none of them, splits at `g0`, and at
/// each pair of `f` nodes enters only the projections whose keys meet, instead of walking the k
/// fields down to each `f` once for each left leaf: 2 k + 8 pairs, 8 k + 17 runs, 18 k + 46
/// steps, and work linear in k, not k^2 (held in `bench.rs`).
pub(super) fn cut(k: usize) -> Theory {
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
}

/// The walk over the shared-field atoms of `shared` and `cut` takes the pairs, runs and steps of
/// their formulas at the sizes `bench.rs` times, the sizes the formulas were checked at, and the
/// default report runs on each at small sizes.
#[test]
fn the_shared_field_atoms_take_the_steps_of_their_formulas() {
    for d in [50, 400] {
        let t = shared(d);
        assert_eq!(
            atom_size(&t),
            (d * d + d + 1, 3 * d * d + d, (5 * d * d + 10 * d) as u64),
            "shared at d = {d}"
        );
    }
    for k in [200, 1600] {
        let t = cut(k);
        assert_eq!(
            atom_size(&t),
            (2 * k + 8, 8 * k + 17, 18 * k as u64 + 46),
            "the walk takes only steps that reach a pair, cut at k = {k}"
        );
    }
    for n in [1, 2, 9] {
        run(&shared(n), Mode::Default);
        run(&cut(n), Mode::Default);
    }
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
pub(super) fn branches(family: &str, mirror: bool, m: usize) -> Theory {
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

/// The pairs, runs and steps of the walk on each family of [`branches`] at m, the same for its
/// mirror. The walk before plan row TRIVIAL-walk-branches took steps or runs quadratic in m on
/// brief, wide, same and ne (COMPLEXITY.md C32); its time is held in `bench.rs`.
fn branches_size(family: &str, m: usize) -> (usize, usize, u64) {
    let (p, r, s) = match family {
        "brief" => (6 * m + 15, 20 * m + 40, 38 * m + 95),
        "wide" => (3 * m + 2, 9 * m + 3, 22 * m + 11),
        "same" => (2 * m + 1, 4 * m, 12 * m + 2),
        _ => (4 * m + 2, 14 * m + 7, 30 * m + 21),
    };
    (p, r, s as u64)
}

/// The four families of [`branches`] and their mirrors.
pub(super) const BRANCHES: [&str; 4] = ["brief", "wide", "same", "ne"];

/// The walk on each family of [`branches`] and its mirror takes the pairs, runs and steps of
/// [`branches_size`] at the sizes `bench.rs` times, and the default report runs on each at
/// small sizes.
#[test]
fn the_shared_field_families_take_the_steps_of_their_formulas() {
    for family in BRANCHES {
        for mirror in [false, true] {
            for m in [128, 1024] {
                let got = atom_size(&branches(family, mirror, m));
                assert_eq!(
                    got,
                    branches_size(family, m),
                    "{family} {mirror} at m = {m}"
                );
            }
            for m in [1, 2, 9] {
                run(&branches(family, mirror, m), Mode::Default);
            }
        }
    }
}

/// `s(h(x0, .., xm), .., h(x0, .., xm), y0, .., ym) == t(h(y0, .., ym), .., h(y0, .., ym), x0,
/// .., xm)`, m copies of `h` and m distinct binders on each side: `s` and `t` split into m^2
/// pairs of `h` nodes, each with the two constant pairs only, and each `x_i` of the left `h`
/// pairs with the right side's leaf `x_i`. Pairs, runs and steps are quadratic in m, the input's
/// size: a pair of `h` nodes enters both sides together, only at the choices whose children may
/// hold a pair, worked out once for each pair of classes, not all m (m^3 steps before).
pub(super) fn joint(m: usize) -> Theory {
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
}

/// The walk on [`joint`] takes its quadratic pairs, runs and steps at the sizes `bench.rs`
/// times, and the default report runs on it at small sizes.
#[test]
fn the_joint_family_takes_the_steps_of_its_formula() {
    for m in [16, 128] {
        assert_eq!(
            atom_size(&joint(m)),
            (
                4 * m * m + 4 * m + 2,
                10 * m * m + 16 * m + 7,
                (20 * m * m + 34 * m + 21) as u64
            ),
            "joint at m = {m}"
        );
    }
    for m in [1, 2, 9] {
        run(&joint(m), Mode::Default);
    }
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
/// - `deep`: `tagged` with each right `h` below a unary field of its own, `q_j(h(..))`, and
///   `deeper` with two, `q_j(r_j(h(..)))`, fields the left side never tests;
/// - `crossed`: `s(h(g(x_i), x_i, g(x_i), ..)^m, y..) == t(h(x_j, p(x0, .., xm), x_j, ..)^m, y..)`,
///   so a leaf meets a subtree that holds its key at some pairs of classes and not at others, and
///   a subtree of one key or of all; `mirror` is `crossed` with its sides swapped.
pub(super) fn picks(family: &str, m: usize) -> Theory {
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
        "tagged" | "deep" | "deeper" => {
            t.field("s", 3 * m).field("t", 3 * m).field("h", m + 1);
            let l = side(
                "s",
                zs.iter().map(|z| tagged(&xs, z)).collect(),
                &[&ys, &ws],
            );
            let hs = ws.iter().enumerate().map(|(j, w)| {
                if family == "deep" {
                    format!("q{j}({})", tagged(&ys, w))
                } else if family == "deeper" {
                    format!("q{j}(r{j}({}))", tagged(&ys, w))
                } else {
                    tagged(&ys, w)
                }
            });
            if family != "tagged" {
                for j in 0..m {
                    t.field(&format!("q{j}"), 1);
                    if family == "deeper" {
                        t.field(&format!("r{j}"), 1);
                    }
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

/// The pairs, runs and steps of the walk on each family of [`picks`] at m: quadratic in m,
/// linear in the input's size, since at a node split against a node of `h` the lists of the
/// choices of all the pairs of classes it meets are made together from the other node's live
/// children, a lookup each (`Theory::pair_form`). Before plan row TRIVIAL-walk-picks each list
/// was made alone from the smaller side's live children, m^3 steps: at m = 64, 387214, 367246
/// and 321102 steps and 156, 93 and 81 million instructions, where these take 141970, 105874
/// and 63442 steps (COMPLEXITY.md C32). On `deep` and `deeper` the node of `t` meets each `h` of
/// the left side only after `q_j` (and `r_j`), so the lists are made together for the whole
/// frontier of `h` below the node of `t` (plan row TRIVIAL-walk-frontier); before, each `q_j`
/// made its own, m^3 steps: at m = 64, 446482 and 521234 steps, where these take 180626 and
/// 255378. The time is held in `bench.rs`.
fn picks_size(family: &str, m: usize) -> (usize, usize, u64) {
    let (p, r, s) = match family {
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
        "deep" => (
            6 * m * m + 8 * m + 2,
            20 * m * m + 32 * m + 7,
            43 * m * m + 70 * m + 18,
        ),
        "deeper" => (
            8 * m * m + 10 * m + 2,
            30 * m * m + 40 * m + 7,
            61 * m * m + 86 * m + 18,
        ),
        _ => (
            3 * m * m + 4 * m + 2,
            5 * m * m + 14 * m + 7,
            15 * m * m + 31 * m + 18,
        ),
    };
    (p, r, s as u64)
}

/// The families of [`picks`] whose time `bench.rs` holds.
pub(super) const PICKS: [&str; 5] = ["alternate", "tagged", "rotations", "deep", "deeper"];

/// The walk on each timed family of [`picks`] takes the pairs, runs and steps of [`picks_size`]
/// at the sizes `bench.rs` times; the report on each agrees with brute force at small sizes in
/// `the_picks_agree_with_brute_force`.
#[test]
fn the_picks_take_the_steps_of_their_formulas() {
    for family in PICKS {
        for m in [8, 64] {
            let got = atom_size(&picks(family, m));
            assert_eq!(got, picks_size(family, m), "{family} at m = {m}");
        }
    }
    for family in PICKS {
        for m in [2, 3] {
            run(&picks(family, m), Mode::Default);
        }
    }
}

/// The lists made together keep exactly the choices the lists made one by one keep: the report
/// on each family of [`picks`] at m = 2 and 3 agrees with brute force, on `keyed` at m = 4,
/// which reaches the lookup of each key below a subtree, as m = 2 and 3 do not, and on `deeper`
/// at m = 2 (with `deeper` at m = 3 as well this test ran over a minute).
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
    super::brute::check(&picks("deeper", 2));
}

/// A node of `h` below fields that only one side tests, against `h` on the other side: random
/// atoms `s(A, B) == t(V(C), W(D), E)` over `s`, `h` and `p` of two arguments, `t` of three
/// and `q`, `r` of one, where `A`, `B`, `C` and `D` are nodes of `h` or binders and `V` and `W`
/// wrap their argument in up to three of `q`, `r` and `p` (the other argument of `p` a binder
/// or a node of `h`); the left side sometimes tests `p` too, so the way to the frontier is
/// sometimes cut by a field both sides test; the sides are swapped half the time and the
/// relation is `!=` now and then. The report agrees with brute force on each, so the lists a
/// split node makes together for its whole frontier keep exactly the choices of the lists made
/// one by one (`Theory::pair_form`).
#[test]
fn the_frontier_agrees_with_brute_force() {
    let mut rng = Rng::new(zed_tests::test_seed());
    for _ in 0..100 {
        super::brute::check(&frontier(&mut rng));
    }
}

/// One random atom of [`the_frontier_agrees_with_brute_force`].
fn frontier(rng: &mut Rng) -> Theory {
    fn leaf(rng: &mut Rng) -> String {
        rng.pick(&["a", "b", "c"]).to_string()
    }
    fn h(rng: &mut Rng) -> String {
        if rng.below(4) == 0 {
            leaf(rng)
        } else {
            format!("h({}, {})", leaf(rng), leaf(rng))
        }
    }
    fn wrapped(rng: &mut Rng) -> String {
        let mut c = h(rng);
        for _ in 0..rng.below(4) {
            c = match rng.below(4) {
                0 => format!("q({c})"),
                1 => format!("r({c})"),
                2 => format!("p({c}, {})", h(rng)),
                _ => format!("p({}, {c})", leaf(rng)),
            };
        }
        c
    }
    let mut t = Theory::new("Frontier");
    t.field("s", 2)
        .field("t", 3)
        .field("h", 2)
        .field("q", 1)
        .field("r", 1)
        .field("p", 2);
    let (a, b) = (h(rng), h(rng));
    let b = if rng.below(4) == 0 {
        format!("p({b}, {})", leaf(rng))
    } else {
        b
    };
    let (c, d, e) = (wrapped(rng), wrapped(rng), leaf(rng));
    let (l, r) = (format!("s({a}, {b})"), format!("t({c}, {d}, {e})"));
    let (l, r) = if rng.below(2) == 0 { (l, r) } else { (r, l) };
    let rel = if rng.below(6) == 0 { "!=" } else { "==" };
    t.law("frontier", "a b c", &format!("{l} {rel} {r}"));
    t
}
