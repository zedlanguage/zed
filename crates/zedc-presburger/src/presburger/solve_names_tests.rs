//! Whether [`solve`] answers a system and its renaming alike, refusals included (row
//! PROOF-solve-renaming-invariant): systems drawn from families that reach each of its choices
//! are solved under their names as drawn and under random renamings, with the rows in the same
//! order (as the answers memo of `settle_as_sets` and the kernels of `stage_kernels` need) and
//! in a shuffled order, and the answers compared as point, empty or refused.

use super::*;

mod bench;

use crate::seed::Rng;

/// `0..n` in a random order.
fn shuffled(rng: &mut Rng, n: usize) -> Vec<usize> {
    let mut p: Vec<usize> = (0..n).collect();
    rng.shuffle(&mut p);
    p
}

/// A row `Σ c[i]·x[i] + k`, compared with zero by `>=`, or `==` when `eq`, over variables by
/// place.
#[derive(Clone, Debug)]
struct Row {
    c: Vec<(usize, i128)>,
    k: i128,
    eq: bool,
}

fn row(c: &[(usize, i128)], k: i128, eq: bool) -> Row {
    Row {
        c: c.to_vec(),
        k,
        eq,
    }
}

/// The rows as constraints, variable `i` named `name[i]`.
fn cons(rows: &[Row], name: &[String]) -> Vec<Con> {
    (rows.iter())
        .map(|r| {
            let lin = (r.c.iter()).fold(Lin::constant(r.k), |l, &(i, c)| {
                l.plus(&Lin::atom(Atom::Sym(name[i].as_str().into())).times(c))
            });
            if r.eq {
                Con::eq(&lin, &Lin::default())
            } else {
                Con::ge(&lin, &Lin::default())
            }
        })
        .collect()
}

/// An answer without a model: a point, none, or the kind of refusal. The variables a
/// [`Refusal::Tie`] names are left out, since a renaming renames them.
fn kind(a: Result<Option<Model>, Refusal>) -> &'static str {
    match a {
        Ok(Some(_)) => "point",
        Ok(None) => "empty",
        Err(Refusal::Growth) => "refused: growth",
        Err(Refusal::Shadows) => "refused: shadows",
        Err(Refusal::Tie(_)) => "refused: tie",
        Err(Refusal::Unordered(_)) => "refused: unordered",
        Err(_) => "refused: other",
    }
}

/// The answer of [`solve`] without a model.
fn answer(cs: &[Con]) -> &'static str {
    kind(solve(cs, false))
}

/// `n` distinct names drawn at random, so that their order is random too.
fn names(rng: &mut Rng, n: usize) -> Vec<String> {
    let mut used = BTreeSet::new();
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let s = format!("v{}", rng.below(1_000_000));
        if used.insert(s.clone()) {
            out.push(s);
        }
    }
    out
}

/// Random rows over `n` variables with small coefficients.
fn random_rows(rng: &mut Rng, n: usize) -> Vec<Row> {
    let m = 2 + rng.below(2 * n + 2);
    (0..m)
        .map(|_| {
            let w = 1 + rng.below(n.min(4));
            let vars = shuffled(rng, n);
            let c: Vec<(usize, i128)> = (vars[..w].iter())
                .map(|&i| {
                    let mut k = rng.int_i128(-4, 4);
                    if k == 0 {
                        k = 1;
                    }
                    (i, k)
                })
                .collect();
            row(&c, rng.int_i128(-8, 8), rng.below(4) == 0)
        })
        .collect()
}

/// Division pairs over one variable `x` (variable 0): `x == c·q + r + k`, `0 <= r < c`, with a
/// lower bound on `x` and on the first remainder, as in `FAIL-one-scope-pairs-seed-refusal`.
/// From about 7 pairs the Omega test refuses these (`modular::r7_tests`, 2026-11-16), so
/// [`solve`] answers by the modular solver's point.
fn division_pairs(rng: &mut Rng) -> (usize, Vec<Row>) {
    let pairs = 1 + rng.below(10);
    let mut rows = vec![
        row(&[(0, 1)], -rng.int_i128(0, 90), false),
        row(&[(2, 1)], -rng.int_i128(0, 3), false),
    ];
    let mut n = 1;
    for _ in 0..pairs {
        let c = rng.int_i128(2, 7);
        let (q, r) = (n, n + 1);
        n += 2;
        rows.push(row(&[(0, 1), (q, -c), (r, -1)], -rng.int_i128(-9, 9), true));
        rows.push(row(&[(r, 1)], 0, false));
        rows.push(row(&[(r, -1)], c - 1 - rng.int_i128(0, 1), false));
    }
    (n, rows)
}

/// [`division_pairs`] with each pair written over its own alias `a == s·x + d` of `x`
/// (`s` = ±1), so that the modular solver's union-find, whose root is the least atom by
/// name, joins the aliases where the Omega test refuses.
fn aliased_pairs(rng: &mut Rng) -> (usize, Vec<Row>) {
    let (mut n, pairs) = division_pairs(rng);
    let mut rows = Vec::with_capacity(pairs.len() * 2);
    for mut r in pairs {
        if r.eq && r.c[0].0 == 0 && rng.below(4) != 0 {
            let a = n;
            n += 1;
            let s = if rng.below(2) == 0 { 1 } else { -1 };
            rows.push(row(&[(a, 1), (0, -s)], -rng.int_i128(-5, 5), true));
            r.c[0].0 = a;
        }
        rows.push(r);
    }
    (n, rows)
}

/// A cycle or two of differences `x[i] - x[i+1] + k >= 0` and sums, regular graphs whose
/// variables color refinement does not tell apart (a hexagon against two triangles).
fn tied_cycles(rng: &mut Rng) -> (usize, Vec<Row>) {
    let n = 6;
    let edges: Vec<(usize, usize)> = if rng.below(2) == 0 {
        (0..6).map(|i| (i, (i + 1) % 6)).collect()
    } else {
        vec![(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
    };
    let (a, b, k) = (rng.int_i128(1, 3), rng.int_i128(-3, 3), rng.int_i128(-5, 5));
    let eq = rng.below(3) == 0;
    let mut rows: Vec<Row> = (edges.iter())
        .map(|&(i, j)| row(&[(i, a), (j, b)], k, eq))
        .collect();
    let bound = rng.int_i128(1, 6);
    for i in 0..n {
        rows.push(row(&[(i, 1)], bound, false));
        rows.push(row(&[(i, -1)], bound, false));
    }
    (n, rows)
}

/// Unit equalities joining variables into classes, with rows of other coefficients over them,
/// as the representatives of `Ties` and the roots of the modular solver choose among.
fn unit_classes(rng: &mut Rng) -> (usize, Vec<Row>) {
    let n = 3 + rng.below(4);
    let mut rows = Vec::new();
    for i in 1..n {
        if rng.below(3) != 0 {
            let j = rng.below(i);
            let s = if rng.below(2) == 0 { 1 } else { -1 };
            rows.push(row(&[(i, 1), (j, -s)], rng.int_i128(-3, 3), true));
        }
    }
    for _ in 0..1 + rng.below(3) {
        let i = rng.below(n);
        let j = rng.below(n);
        let (a, b) = (rng.int_i128(2, 5), rng.int_i128(-5, 5));
        let c: Vec<(usize, i128)> = if i == j {
            vec![(i, a)]
        } else {
            vec![(i, a), (j, b)]
        };
        rows.push(row(&c, rng.int_i128(-9, 9), rng.below(2) == 0));
    }
    (n, rows)
}

/// Wide equalities of unit terms, nested or overlapping, with boxes: the slack reductions.
fn wide(rng: &mut Rng) -> (usize, Vec<Row>) {
    let n = 4 + rng.below(4);
    let mut rows = Vec::new();
    for _ in 0..1 + rng.below(3) {
        let w = 2 + rng.below(n - 1);
        let vars = shuffled(rng, n);
        let c: Vec<(usize, i128)> = (vars[..w].iter())
            .map(|&i| (i, if rng.below(4) == 0 { -1 } else { 1 }))
            .collect();
        rows.push(row(&c, -rng.int_i128(0, 2 * w as i128), true));
    }
    for i in 0..n {
        rows.push(row(&[(i, 1)], 0, false));
        rows.push(row(&[(i, -1)], rng.int_i128(1, 3), false));
    }
    (n, rows)
}

/// One drawn system of the family `f`.
fn draw(rng: &mut Rng, f: u64) -> (usize, Vec<Row>) {
    match f {
        0 => {
            let n = 2 + rng.below(5);
            (n, random_rows(rng, n))
        }
        1 => division_pairs(rng),
        2 => tied_cycles(rng),
        3 => unit_classes(rng),
        4 => wide(rng),
        5 => aliased_pairs(rng),
        _ => tied_remainders_drawn(rng),
    }
}

/// The number of families [`draw`] draws from.
const FAMILIES: u64 = 7;

/// The systems drawn, each with every answer it got and how often, where its namings or
/// orders of rows did not give one answer.
fn differing(seed: u64, systems: usize, namings: usize) -> Vec<String> {
    let mut rng = Rng::new(seed);
    let mut found = Vec::new();
    for s in 0..systems {
        let (n, rows) = draw(&mut rng, s as u64 % FAMILIES);
        let mut seen: BTreeMap<&str, Vec<String>> = BTreeMap::new();
        for t in 0..namings {
            let name = names(&mut rng, n);
            let mut cs = cons(&rows, &name);
            let how = if t % 2 == 1 {
                let order = shuffled(&mut rng, cs.len());
                cs = order.iter().map(|&i| cs[i].clone()).collect();
                "shuffled"
            } else {
                "in order"
            };
            let a = answer(&cs);
            seen.entry(a).or_default().push(format!("{how} {cs:?}"));
        }
        if seen.len() > 1 {
            found.push(format!(
                "system {s}: {:?}",
                seen.iter()
                    .map(|(a, v)| format!("{a} x{}: {}", v.len(), v[0]))
                    .collect::<Vec<_>>()
            ));
        }
    }
    found
}

/// Remainder rows whose two unit terms the modular solver cannot tell apart by their bounds:
/// `u + v == m·q1 + k1` and `v + w == m·q2 + k2` (and `u + w == m·q3 + k3` when `triangle`),
/// with `u`, `v`, `w` (variables 0, 1, 2) each bounded to one period `[82, 81 + m]`, and
/// `pairs` division pairs over `v` as in [`division_pairs`], with `r0 >= 3`, which the Omega
/// test refuses from about 7 pairs.
fn tied_remainders(m: i128, ks: [i128; 3], pairs: usize, triangle: bool) -> (usize, Vec<Row>) {
    let mut rows = vec![
        row(&[(0, 1), (1, 1), (3, -m)], ks[0], true),
        row(&[(1, 1), (2, 1), (4, -m)], ks[1], true),
    ];
    let mut n = 5;
    if triangle {
        rows.push(row(&[(0, 1), (2, 1), (n, -m)], ks[2], true));
        n += 1;
    }
    for i in 0..3 {
        rows.push(row(&[(i, 1)], -82, false));
        rows.push(row(&[(i, -1)], 81 + m, false));
    }
    for p in 0..pairs {
        let c = [5, 3, 4, 6][p % 4];
        let (q, r) = (n, n + 1);
        n += 2;
        if p == 0 {
            rows.push(row(&[(r, 1)], -3, false));
        }
        rows.push(row(&[(1, 1), (q, -c), (r, -1)], -((p % 7) as i128), true));
        rows.push(row(&[(r, 1)], 0, false));
        rows.push(row(&[(r, -1)], c - 1, false));
    }
    (n, rows)
}

/// [`tied_remainders`] with its sizes and constants drawn.
fn tied_remainders_drawn(rng: &mut Rng) -> (usize, Vec<Row>) {
    let m = rng.int_i128(2, 1000);
    let k = |rng: &mut Rng| -rng.int_i128(160, 160 + 2 * m);
    let ks = [k(rng), k(rng), k(rng)];
    tied_remainders(m, ks, rng.below(13), rng.below(3) == 0)
}

#[test]
fn two_tied_remainder_rows_are_answered_alike_under_every_naming() {
    // PROOF-solve-renaming-invariant. With two tied rows the two runs of
    // `modular::point_by_structure` read each row the way the names put first and then the
    // other way, two of the four readings; only `u` and `w` as the remainders leave one
    // variable, `v`, so a point was found unless `v` was named between `u` and `w`, and there
    // `solve` kept the Omega test's refusal (Shadows). The rows each holds tell them apart
    // now (`v` is in more), and where they cannot (the triangle with no pairs, where each of
    // `u`, `v`, `w` is in two), no point is given under any naming.
    for (m, pairs, triangle) in [
        (1000, 7, false),
        (1000, 12, false),
        (100_000, 16, false),
        (500, 10, false),
        (1000, 0, true),
        (1000, 8, true),
    ] {
        let (n, rows) = tied_remainders(m, [-(m + 200), -(m + 201), -(m + 202)], pairs, triangle);
        let mut answers = BTreeMap::new();
        for perm in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let mut name: Vec<String> = (0..n).map(|i| format!("z{i:03}")).collect();
            for (i, p) in perm.iter().enumerate() {
                name[i] = format!("a{p}");
            }
            let a = answer(&cons(&rows, &name));
            answers.entry(a).or_insert_with(Vec::new).push(perm);
        }
        assert_eq!(
            answers.len(),
            1,
            "m {m}, {pairs} pairs, triangle {triangle}: {answers:?}"
        );
        if !triangle {
            assert!(
                answers.contains_key("point"),
                "m {m}, {pairs} pairs: {answers:?}"
            );
        }
    }
}

/// PROOF-modular-tied-rows-names: on two and three tied remainder rows, with names drawn at
/// random and those of `u`, `v` and `w` in each of their orders, [`modular::solve_modular`] and [`decide`]
/// never give two verdicts: each run of `solve_modular` is exact, so a point or an empty answer
/// is the formula's own, whichever readings the names choose. Whether `solve_modular` answers
/// at all may turn on the names (PERF-negated-chain-unsolved, U4); this test asserts only what
/// holds under every naming.
#[test]
fn solve_modular_never_gives_two_verdicts_on_tied_remainder_rows() {
    let (mut rng, _) = Rng::fresh("solve_modular_never_gives_two_verdicts_on_tied_remainder_rows");
    let mut answered = 0;
    for (m, pairs, triangle) in [
        (3, 0, false),
        (4, 0, true),
        (5, 2, false),
        (1000, 7, false),
        (1000, 0, true),
        (1000, 8, true),
    ] {
        let (n, rows) = tied_remainders(m, [-(m + 200), -(m + 201), -(m + 202)], pairs, triangle);
        let mut verdicts = BTreeSet::new();
        for perm in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            for _ in 0..4 {
                let mut name = names(&mut rng, n);
                let drawn = name[..3].to_vec();
                for (i, &p) in perm.iter().enumerate() {
                    name[i] = drawn[p].clone();
                }
                let f = Formula::and(cons(&rows, &name).into_iter().map(Formula::Con).collect());
                if let Some(found) = modular::solve_modular(&f, false) {
                    answered += 1;
                    verdicts.insert(found.is_some());
                }
                if let Ok(v) = decide(&f) {
                    verdicts.insert(v);
                }
            }
        }
        assert!(
            verdicts.len() <= 1,
            "m {m}, {pairs} pairs, triangle {triangle}: both verdicts"
        );
    }
    // The modular solver answered some of them, so its verdicts were compared.
    assert!(answered > 0);
}

#[test]
fn solve_answers_every_renaming_and_order_of_rows_alike() {
    let seed = crate::seed::seed("solve_answers_every_renaming_and_order_of_rows_alike");
    let found = differing(seed, 400, 12);
    assert!(found.is_empty(), "{}", found.join("\n"));
}
