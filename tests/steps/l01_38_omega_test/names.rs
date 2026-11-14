//! Answers that do not depend on the names of the variables (plan item NAME-ties, fix B of the
//! cross-review XR3): every step of the solver chooses by the structure of the rows, takes
//! candidates that share no row together, and refuses with `Refusal::Tie` where candidates
//! that only their names tell apart share a row. A formula with disjunctions is renamed by
//! the colors of its atoms before its disjunctions are searched, when each atom has a color
//! of its own. Each system here is decided under every naming of its variables, or under 200
//! random ones, and must give one answer.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::interval::{End, Num};
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, Refusal, decide, project_each, satisfiable,
};

/// A row `Σ c[i]·x[i] + k >= 0`, or `== 0` when `eq`, over the variables by place.
#[derive(Clone, Debug)]
pub(super) struct Row {
    c: Vec<i64>,
    k: i64,
    eq: bool,
}

pub(super) fn ge(c: &[i64], k: i64) -> Row {
    Row {
        c: c.to_vec(),
        k,
        eq: false,
    }
}

pub(super) fn eq(c: &[i64], k: i64) -> Row {
    Row {
        c: c.to_vec(),
        k,
        eq: true,
    }
}

/// The rows with the box `-half <= x[i] <= half` added.
fn with_box(rows: &[Row], n: usize, half: i64) -> Vec<Row> {
    let mut all = rows.to_vec();
    for i in 0..n {
        for s in [1, -1] {
            let mut c = vec![0; n];
            c[i] = s;
            all.push(ge(&c, half));
        }
    }
    all
}

/// The rows as a formula, variable `i` named `v{name[i]}`.
fn formula(rows: &[Row], name: &[usize]) -> Formula {
    let fs = rows
        .iter()
        .map(|r| {
            let lin =
                r.c.iter()
                    .enumerate()
                    .fold(Lin::constant(r.k), |l, (i, c)| {
                        let x = Atom::Sym(Arc::from(format!("v{}", name[i])));
                        l.plus(&Lin::atom(x).times(*c))
                    });
            let zero = Lin::constant(0);
            Formula::Con(if r.eq {
                Con::eq(&lin, &zero)
            } else {
                Con::ge(&lin, &zero)
            })
        })
        .collect();
    Formula::and(fs)
}

/// The answer, a tie written without the names it gives, which a renaming changes.
fn answer(f: &Formula) -> String {
    match decide(f) {
        Err(Refusal::Tie(t)) => format!("Err(Tie, {} variables)", t.vars.len()),
        Err(Refusal::Unordered(t)) => format!(
            "Err(Unordered, {} variables, {} disjunctions)",
            t.vars.len(),
            t.rows.len()
        ),
        a => format!("{a:?}"),
    }
}

/// Visits every permutation of `0..n` (Heap's algorithm); returns how many.
fn each_permutation(n: usize, mut visit: impl FnMut(&[usize])) -> usize {
    let mut perm: Vec<usize> = (0..n).collect();
    visit(&perm);
    let mut count = 1;
    let mut c = vec![0; n];
    let mut i = 1;
    while i < n {
        if c[i] < i {
            perm.swap(if i % 2 == 0 { 0 } else { c[i] }, i);
            visit(&perm);
            count += 1;
            c[i] += 1;
            i = 1;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
    count
}

/// The answers of `rows` under every naming of its `n` variables, with how many namings
/// gave each.
pub(super) fn namings(rows: &[Row], n: usize) -> BTreeMap<String, usize> {
    let mut seen = BTreeMap::new();
    let visited = each_permutation(n, |perm| {
        *seen.entry(answer(&formula(rows, perm))).or_insert(0) += 1;
    });
    assert_eq!(visited, (1..=n).product::<usize>());
    seen
}

/// The answers of `rows` under the naming as written and `count` random namings of its `n`
/// variables from `rng`, with how many namings gave each.
fn sampled_namings(rows: &[Row], n: usize, rng: &mut Rng, count: usize) -> BTreeMap<String, usize> {
    let mut seen = BTreeMap::new();
    let perms = std::iter::once((0..n).collect()).chain((0..count).map(|_| shuffled(rng, n)));
    for perm in perms {
        *seen.entry(answer(&formula(rows, &perm))).or_insert(0) += 1;
    }
    seen
}

/// A random permutation of `0..n`.
fn shuffled(rng: &mut Rng, n: usize) -> Vec<usize> {
    let mut p: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        p.swap(i, rng.below(i + 1));
    }
    p
}

/// `n` rows per layer, each the layer's pattern of 2 to 4 nonzero coefficients placed on
/// distinct variables, so that every variable occurs once with each coefficient of each layer
/// and color refinement gives every variable one color (the family of XR3, R3_CLAUDE.md 2.1).
fn regular_rows(rng: &mut Rng, n: usize, layers: usize) -> Vec<Row> {
    let mut rows = Vec::new();
    for _ in 0..layers {
        let width = 2 + rng.below(3);
        let pick = |rng: &mut Rng| loop {
            let c = rng.int(-5, 5);
            if c != 0 {
                return c;
            }
        };
        let pattern: Vec<i64> = (0..width).map(|_| pick(rng)).collect();
        let k = rng.int(-10, 6);
        let slots: Vec<Vec<usize>> = loop {
            let slots: Vec<Vec<usize>> = (0..width).map(|_| shuffled(rng, n)).collect();
            if (0..n).all(|i| (0..width).all(|j| (0..j).all(|l| slots[j][i] != slots[l][i]))) {
                break slots;
            }
        };
        for i in 0..n {
            let mut cs = vec![0; n];
            for (j, slot) in slots.iter().enumerate() {
                cs[slot[i]] = pattern[j];
            }
            rows.push(ge(&cs, k));
        }
    }
    rows
}

/// The systems of the family drawn from `rng`, `layers` layers each, in its box: of the first
/// `count`, those `decided` keeps are decided under every naming. Returns the systems whose
/// answer changes with the naming, by place, and the counts of systems with a refusal and
/// with an answer.
fn regular(
    rng: &mut Rng,
    n: usize,
    layers: usize,
    count: usize,
    decided: impl Fn(usize) -> bool,
) -> (Vec<usize>, usize, usize) {
    let (mut differ, mut refused, mut answered) = (Vec::new(), 0, 0);
    for s in 0..count {
        let half = 1 + rng.below(3) as i64;
        let rows = with_box(&regular_rows(rng, n, layers), n, half);
        if !decided(s) {
            continue;
        }
        let seen = namings(&rows, n);
        if seen.len() > 1 {
            differ.push(s);
        }
        refused += usize::from(seen.keys().any(|a| a.starts_with("Err")));
        answered += usize::from(seen.keys().any(|a| a.starts_with("Ok")));
    }
    (differ, refused, answered)
}

/// Every naming of `count` systems of the family with `n` variables, drawn with a new seed
/// each run, gives one answer, for each number of layers in `layers` (author P169: random
/// tests run few cases, with a new seed each run). The searches of the cross-review XR3
/// (R3_CLAUDE.md 2.1) ran 300 systems at each of five seeds for five variables and 40 at
/// each of four for six, 20 s a seed; the systems among them that changed answer with the
/// naming before the rule are kept in
/// `the_systems_of_the_regular_family_that_changed_answer_with_the_naming_give_one_answer`.
fn one_answer_on_the_regular_family(n: usize, layers: &[usize], count: usize) {
    let (mut rng, seed) = Rng::fresh(&format!("the regular family of {n}"));
    for &layers in layers {
        let (differ, refused, answered) = regular(&mut rng, n, layers, count, |_| true);
        eprintln!(
            "n {n}, layers {layers}: {count} systems, {refused} refused, {answered} decided, {} name-dependent",
            differ.len()
        );
        assert_eq!(
            differ,
            Vec::<usize>::new(),
            "seed {seed}, n {n}, layers {layers}"
        );
    }
}

#[test]
fn every_naming_gives_one_answer_on_the_regular_family_of_five() {
    one_answer_on_the_regular_family(5, &[1, 2, 3], 3);
}

#[test]
fn every_naming_gives_one_answer_on_the_regular_family_of_six() {
    one_answer_on_the_regular_family(6, &[2], 1);
}

#[test]
fn the_systems_of_the_regular_family_that_changed_answer_with_the_naming_give_one_answer() {
    // Systems 111, 120 and 194 of seed 103 (five variables, two layers, 300 systems) and
    // system 15 of seed 106 (six variables, two layers, 40 systems) changed answer with the
    // naming before the rule.
    for (seed, n, count, systems) in [(103, 5, 300, &[111, 120, 194][..]), (106, 6, 40, &[15])] {
        let mut rng = Rng::new(seed);
        let (differ, refused, answered) = regular(&mut rng, n, 2, count, |s| systems.contains(&s));
        eprintln!("seed {seed}: {refused} refused, {answered} decided");
        assert_eq!(differ, Vec::<usize>::new(), "seed {seed}, n {n}");
    }
}

/// The rows of the orbits of `base` under the cyclic shift of the `n` variables, and under
/// the reversal too when `dihedral`, each distinct row once, in the order first reached: a
/// system the group maps onto itself, so that every variable has one color.
fn orbit(base: &[Row], n: usize, dihedral: bool) -> Vec<Row> {
    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for r in base {
        for s in 0..n {
            for flip in [false, true] {
                if flip && !dihedral {
                    continue;
                }
                let c: Vec<i64> = (0..n)
                    .map(|i| r.c[((if flip { n - i } else { i }) + s) % n])
                    .collect();
                if seen.insert((c.clone(), r.k)) {
                    out.push(ge(&c, r.k));
                }
            }
        }
    }
    out
}

/// `count` systems of the orbit family, drawn with a new seed each run (author P169; the
/// searches of XR3 ran 1500, 240, 24 and 20 systems at fixed seeds): one or two random rows
/// (coefficients in `[-4, 4]`, constant in `[-6, 6]`) with their orbits, in the box
/// `[-half, half]^n` for a random `half` from 1 to 3, each decided under all `n!` namings; the
/// source is `q2_cyclic_*` of the cross-review XR3 (wt/xt4/claude/R3_ZED_IMPL.patch). Asserts
/// one answer per system.
///
/// The tie rule is not what keeps these to one answer: with it disabled (the first tied
/// candidate taken by place; run once 2026-11-05) all four families still gave one answer
/// per system, while `the_five_variable_counterexample_has_one_answer` failed. Variables of
/// one color here are also swapped by a symmetry of the system, so any choice among them
/// leads to the same answer. The family checks the rest of the solver for a dependence on
/// names; the regular family above is the one that checks the tie rule.
fn one_answer_on_orbits(n: usize, count: usize, dihedral: bool) {
    let (mut rng, seed) = Rng::fresh(&format!("orbits of {n}, dihedral {dihedral}"));
    let (mut differ, mut refused, mut decided) = (Vec::new(), 0, 0);
    for s in 0..count {
        let half = 1 + rng.below(3) as i64;
        let bases = 1 + rng.below(2);
        let base: Vec<Row> = (0..bases)
            .map(|_| {
                let c: Vec<i64> = (0..n).map(|_| rng.int(-4, 4)).collect();
                ge(&c, rng.int(-6, 6))
            })
            .collect();
        let rows = with_box(&orbit(&base, n, dihedral), n, half);
        let seen = namings(&rows, n);
        if seen.len() > 1 {
            differ.push((s, seen));
            continue;
        }
        refused += usize::from(seen.keys().any(|a| a.starts_with("Err")));
        decided += usize::from(seen.keys().any(|a| a.starts_with("Ok")));
    }
    eprintln!(
        "n {n}, dihedral {dihedral}, seed {seed}: {count} systems, {refused} refused, {decided} decided, {} name-dependent",
        differ.len()
    );
    assert!(differ.is_empty(), "seed {seed}, n {n}: {differ:?}");
}

#[test]
fn the_orbit_of_a_row_under_a_rotation_or_a_reflection_is_closed() {
    // `x0 - x1 >= 0` turned around four variables is the cycle `x0 >= x1 >= x2 >= x3 >= x0`;
    // a reflection adds the reversed cycle, and a row the group fixes stays one row.
    let cyclic = orbit(&[ge(&[1, -1, 0, 0], 0)], 4, false);
    let cs: Vec<&[i64]> = cyclic.iter().map(|r| r.c.as_slice()).collect();
    assert_eq!(
        cs,
        [[1, -1, 0, 0], [-1, 0, 0, 1], [0, 0, 1, -1], [0, 1, -1, 0]]
    );
    assert_eq!(orbit(&[ge(&[1, -1, 0, 0], 0)], 4, true).len(), 8);
    assert_eq!(orbit(&[ge(&[1, 1, 1, 1], -2)], 4, true).len(), 1);
    // The cycle forces all four equal, so the sum is a multiple of four in `[-4, 4]`.
    let with_sum = |lo: i64, hi: i64| {
        let mut rows = cyclic.clone();
        rows.extend([ge(&[1, 1, 1, 1], -lo), ge(&[-1, -1, -1, -1], hi)]);
        namings(&with_box(&rows, 4, 1), 4)
    };
    let keys = |seen: &BTreeMap<String, usize>| seen.keys().cloned().collect::<Vec<_>>();
    assert_eq!(keys(&with_sum(1, 4)), ["Ok(true)"]);
    assert_eq!(keys(&with_sum(5, 8)), ["Ok(false)"]);
    // Between the multiples there is no integer point but there are rational ones; the
    // equalities the cycle implies are solved before any elimination, so the sum is `4·x0`,
    // which no value of `x0` puts in `[1, 3]` (OMEGA-cycle-growth; refused `Growth` before).
    assert_eq!(keys(&with_sum(1, 3)), ["Ok(false)"]);
}

#[test]
fn every_naming_gives_one_answer_on_cyclic_orbits_of_four() {
    one_answer_on_orbits(4, 60, false);
}

#[test]
fn every_naming_gives_one_answer_on_cyclic_orbits_of_five() {
    one_answer_on_orbits(5, 8, false);
}

#[test]
fn every_naming_gives_one_answer_on_cyclic_orbits_of_six() {
    one_answer_on_orbits(6, 1, false);
}

#[test]
fn every_naming_gives_one_answer_on_dihedral_orbits_of_six() {
    one_answer_on_orbits(6, 1, true);
}

/// System 111 of the regular family at seed 103 with five variables, no box: rows
/// `Σ c·x - 6 >= 0` (R3_CLAUDE.md 2.1). Before the rule 24 namings gave Growth and 96 gave
/// no point.
pub(super) fn claude5() -> Vec<Row> {
    let c: [[i64; 5]; 10] = [
        [1, 0, 0, 2, 0],
        [2, 0, 0, 0, 1],
        [0, 2, 1, 0, 0],
        [0, 1, 2, 0, 0],
        [0, 0, 0, 1, 2],
        [-2, 0, -2, 0, 0],
        [0, 0, -2, -2, 0],
        [0, -2, 0, 0, -2],
        [0, 0, 0, -2, -2],
        [-2, -2, 0, 0, 0],
    ];
    c.iter().map(|r| ge(r, -6)).collect()
}

/// Codex's six-variable system (R3_CODEX.md Q2) in the box `[-3, 3]^6`; `(-2, -3, -3, -3,
/// -3, -3)` is a point. Before the rule 480 namings gave Growth and 240 a point.
pub(super) fn codex6() -> Vec<Row> {
    let rows = [
        ge(&[0, -2, 1, 1, 0, 0], 0),
        ge(&[-2, 1, 0, -2, 0, 0], 0),
        ge(&[0, 0, -2, 0, -2, -2], -1),
        ge(&[1, -2, 0, 0, 1, 0], -1),
        ge(&[-2, 0, 0, -2, 0, 1], -1),
        ge(&[0, 0, -2, 0, -2, -2], 0),
    ];
    with_box(&rows, 6, 3)
}

/// Gemini's coupled four-variable system (R3_GEMINI.md Q2(a)) in the box `[-3, 3]^4`;
/// `(1, 1, 0, 0)` is a point. Before the rule 12 namings gave Growth and 12 a point.
fn coupled4() -> Vec<Row> {
    let rows = [
        ge(&[3, -1, -2, -2], -2),
        ge(&[-1, 3, -2, -2], -2),
        ge(&[3, -3, 2, -2], 0),
        ge(&[-3, 3, -2, 2], 0),
    ];
    with_box(&rows, 4, 3)
}

/// Whether `p` holds every row.
fn holds(rows: &[Row], p: &[i64]) -> bool {
    rows.iter().all(|r| {
        let v = r.c.iter().zip(p).map(|(c, x)| c * x).sum::<i64>() + r.k;
        if r.eq { v == 0 } else { v >= 0 }
    })
}

#[test]
fn the_five_variable_counterexample_has_one_answer() {
    let seen = namings(&claude5(), 5);
    eprintln!("{seen:?}");
    assert_eq!(seen.len(), 1, "{seen:?}");
}

#[test]
fn codexs_six_variable_system_has_one_answer() {
    let rows = codex6();
    // A check of the transcription that can fail.
    assert!(holds(&rows, &[-2, -3, -3, -3, -3, -3]));
    let seen = namings(&rows, 6);
    eprintln!("{seen:?}");
    assert_eq!(seen.len(), 1, "{seen:?}");
}

#[test]
fn geminis_coupled_system_has_one_answer() {
    let rows = coupled4();
    assert!(holds(&rows, &[1, 1, 0, 0]));
    let seen = namings(&rows, 4);
    eprintln!("{seen:?}");
    assert_eq!(seen.len(), 1, "{seen:?}");
}

/// The edges of the Frucht graph, 3-regular on 12 vertices with no symmetry but the identity,
/// from its LCF notation `[-5, -2, -4, 2, 5, -2, 2, 5, -2, -5, 4, 2]`.
fn frucht() -> Vec<(usize, usize)> {
    let lcf = [-5i64, -2, -4, 2, 5, -2, 2, 5, -2, -5, 4, 2];
    let mut e = std::collections::BTreeSet::new();
    for (i, d) in lcf.iter().enumerate() {
        let j = (i + 1) % 12;
        e.insert((i.min(j), i.max(j)));
        let k = (i as i64 + d).rem_euclid(12) as usize;
        e.insert((i.min(k), i.max(k)));
    }
    e.into_iter().collect()
}

#[test]
fn the_frucht_edge_system_has_one_answer() {
    // Rows `x[i] + x[j] >= 1` at each edge, `0 <= x <= 1`, and at most `cover` ones: a cover
    // of the edges by `cover` vertices. Color refinement gives every vertex of the 3-regular
    // graph one color though no two are alike, so every step is among tied variables.
    let e = frucht();
    assert_eq!(e.len(), 18, "the Frucht graph has 18 edges");
    for cover in [6, 7, 8] {
        let mut rows: Vec<Row> = e
            .iter()
            .map(|&(a, b)| {
                let mut c = vec![0; 12];
                c[a] = 1;
                c[b] = 1;
                ge(&c, -1)
            })
            .collect();
        for i in 0..12 {
            let mut c = vec![0; 12];
            c[i] = 1;
            rows.push(ge(&c, 0));
            c[i] = -1;
            rows.push(ge(&c, 1));
        }
        rows.push(ge(&[-1; 12], cover));
        let mut rng = Rng::new(0x38_f0 + cover as u64);
        let mut seen = BTreeMap::new();
        for _ in 0..200 {
            let name = shuffled(&mut rng, 12);
            *seen.entry(answer(&formula(&rows, &name))).or_insert(0) += 1;
        }
        eprintln!("Frucht, cover {cover}: {seen:?}");
        assert_eq!(seen.len(), 1, "cover {cover}: {seen:?}");
    }
}

#[test]
fn every_order_and_naming_of_a_chain_of_equalities_gives_one_answer() {
    // `x0 - x1 == 1`, `x1 - x2 == 1`, `x2 - x3 == 1` join one class; with rows that the box
    // stage alone decides, the answer under every naming and every order of the equalities is
    // the same. All four variables join one class, so this does not show that the member that
    // stands for a class is free of the order in which `Ties::equate` joined it; the unit test
    // `store::presburger::tests::the_representatives_of_joined_equalities_do_not_depend_on_their_order`
    // does, over classes of several sizes and colors.
    let rows = [
        eq(&[1, -1, 0, 0], -1),
        eq(&[0, 1, -1, 0], -1),
        eq(&[0, 0, 1, -1], -1),
        ge(&[2, 3, -5, 7], -4),
        ge(&[-3, 2, 4, -5], 1),
        ge(&[1, 0, 0, 0], 4),
        ge(&[-1, 0, 0, 0], 4),
    ];
    let mut seen = BTreeMap::new();
    each_permutation(4, |name| {
        each_permutation(3, |order| {
            let mut rs: Vec<Row> = order.iter().map(|&i| rows[i].clone()).collect();
            rs.extend(rows[3..].iter().cloned());
            *seen.entry(answer(&formula(&rs, name))).or_insert(0) += 1;
        });
    });
    eprintln!("{seen:?}");
    assert_eq!(seen.len(), 1, "{seen:?}");
}

/// Pugh's example between `x[n / 2]` and `x[n / 2 + 1]` of a chain of `n` steps
/// `3·x[i + 1] - 2·x[i] + 5 >= 0` and `2·x[i] - 3·x[i + 1] + 5 >= 0` over `n + 1` variables, as
/// `scaling::pugh_in_a_chain` builds it: each elimination is dark, and the splinters are
/// searched.
fn pugh_chain(n: usize) -> Vec<Row> {
    let mut rows = Vec::new();
    let at = |pairs: &[(usize, i64)]| {
        let mut c = vec![0; n + 1];
        for (i, a) in pairs {
            c[*i] = *a;
        }
        c
    };
    for i in 0..n {
        let (a, b) = (i, i + 1);
        if i == n / 2 {
            rows.push(ge(&at(&[(a, 11), (b, 13)]), -27));
            rows.push(ge(&at(&[(a, -11), (b, -13)]), 45));
            rows.push(ge(&at(&[(a, 7), (b, -9)]), 10));
            rows.push(ge(&at(&[(a, -7), (b, 9)]), 4));
        } else {
            rows.push(ge(&at(&[(b, 3), (a, -2)]), 5));
            rows.push(ge(&at(&[(a, 2), (b, -3)]), 5));
        }
    }
    rows
}

#[test]
fn the_splinters_are_searched_a_batch_at_a_time() {
    // The search ends after the first batch of dark eliminations with a refusal; the batches,
    // and their order, are the same under every naming. 30 of the 720 namings of six variables
    // and 10 namings of twelve, drawn with a new seed each run (author P169; all 720 and 200 of
    // twelve at one seed took 13.6 s; 60 and 20 took 0.68 s at load 14 and are in
    // `bench::names`).
    let (mut rng, seed) = Rng::fresh("namings of chains of six and twelve");
    splinters_answer_alike(&mut rng, 30, 10, seed);
}

/// [`pugh_chain`]s of 6 and 12 variables give one answer under `six` and `twelve` random
/// namings from `rng`; `seed` is named on failure.
pub(super) fn splinters_answer_alike(rng: &mut Rng, six: usize, twelve: usize, seed: u64) {
    for (links, count) in [(5, six), (11, twelve)] {
        let rows = pugh_chain(links);
        let mut seen = BTreeMap::new();
        for _ in 0..count {
            *seen
                .entry(answer(&formula(&rows, &shuffled(rng, links + 1))))
                .or_insert(0) += 1;
        }
        assert_eq!(
            seen.len(),
            1,
            "seed {seed}, chain of {}: {seen:?}",
            links + 1
        );
    }
}

/// The cycle `-x[i] + 3·x[i + 1] - 10 >= 0` over `n` variables, `x[n]` being `x[0]`: every
/// variable occurs alike, each elimination is exact and shares a row with the next, and
/// `x = (5, 5, ...)` is a point.
fn cycle(n: usize) -> Vec<Row> {
    (0..n)
        .map(|i| {
            let mut c = vec![0; n];
            c[i] = -1;
            c[(i + 1) % n] = 3;
            ge(&c, -10)
        })
        .collect()
}

#[test]
fn a_tie_that_shares_a_row_is_refused() {
    let rows = cycle(4);
    assert!(holds(&rows, &[5, 5, 5, 5]));
    let Err(Refusal::Tie(t)) = decide(&formula(&rows, &[0, 1, 2, 3])) else {
        panic!("the cycle of four is refused with a tie");
    };
    let mut vars = t.vars.clone();
    vars.sort();
    assert_eq!(vars, ["v0", "v1", "v2", "v3"]);
    // Each row written with its terms in the order of the canonical form.
    let mut shared = t.rows.clone();
    shared.sort();
    assert_eq!(
        shared,
        [
            "-v0 + 3 * v1 - 10 >= 0",
            "-v1 + 3 * v2 - 10 >= 0",
            "3 * v0 - v3 - 10 >= 0",
            "3 * v3 - v2 - 10 >= 0",
        ]
    );
    let message = Refusal::Tie(t).to_string();
    assert!(
        message.contains(
            "which occur alike in the conditions (with the same coefficients, in conditions that are alike)"
        ),
        "{message}"
    );
    assert!(message.contains("`-v0 + 3 * v1 - 10 >= 0`"), "{message}");
    // Under every naming, the same refusal.
    assert_eq!(
        namings(&rows, 4).into_keys().collect::<Vec<_>>(),
        ["Err(Tie, 4 variables)"]
    );
}

#[test]
fn tied_equalities_are_kept_as_rows_and_decided() {
    // `x + y == 5` with `x` and `y` alike: either could be defined by the other, so neither
    // is, and the pair of rows `x + y >= 5`, `x + y <= 5` goes to the stage of two variables.
    let rows = vec![eq(&[1, 1], -5), ge(&[1, 0], 0), ge(&[0, 1], 0)];
    assert_eq!(
        namings(&rows, 2).into_keys().collect::<Vec<_>>(),
        ["Ok(true)"]
    );
    let rows = vec![eq(&[1, 1], -5), ge(&[1, 0], -3), ge(&[0, 1], -3)];
    assert_eq!(
        namings(&rows, 2).into_keys().collect::<Vec<_>>(),
        ["Ok(false)"]
    );
    // Three alike in one equality, in a box that leaves no point.
    let rows = with_box(&[eq(&[2, 2, 2], -7)], 3, 3);
    assert_eq!(
        namings(&rows, 3).into_keys().collect::<Vec<_>>(),
        ["Ok(false)"]
    );
}

/// `i mod 7` read three times, as the `mod7` chain of S22 writes it: `i == 7·q + r` with
/// `r` in its range, for each read, over the variables `i, q0, r0, q1, r1, q2, r2`, with `i`
/// in `[lo, hi]`, the first and last remainder in `[0, 6]` and the middle one in `mid`.
fn three_reads_of_a_remainder(lo: i64, hi: i64, mid: (i64, i64)) -> Vec<Row> {
    let mut rows = vec![
        ge(&[1, 0, 0, 0, 0, 0, 0], -lo),
        ge(&[-1, 0, 0, 0, 0, 0, 0], hi),
    ];
    for (j, (l, h)) in [(0, 6), mid, (0, 6)].into_iter().enumerate() {
        let (mut e, mut low, mut high) = (vec![0; 7], vec![0; 7], vec![0; 7]);
        e[0] = 1;
        e[1 + 2 * j] = -7;
        e[2 + 2 * j] = -1;
        low[2 + 2 * j] = 1;
        high[2 + 2 * j] = -1;
        rows.extend([eq(&e, 0), ge(&low, -l), ge(&high, h)]);
    }
    rows
}

/// The first and last equality are alike and share `i`, but each defines its own remainder,
/// which no other equality holds, so they are solved together, in no order; kept as rows
/// instead, the coefficient 7 left a splinter of a splinter (Shadows), and the transfer before
/// of S22 refused `mod7` at k = 3 to 8. The naming as written and 400 random namings of a new
/// seed each run; all 5040 namings (1.19 s at load 25) are in `bench::names`.
#[test]
fn tied_equalities_that_share_only_a_variable_they_do_not_define_are_solved_together() {
    let (mut rng, seed) = Rng::fresh("names tied equalities");
    for (rows, want) in tied_remainder_systems() {
        let seen = sampled_namings(&rows, 7, &mut rng, 400);
        assert_eq!(seen.into_keys().collect::<Vec<_>>(), [want], "seed {seed}");
    }
}

/// The two systems of [`three_reads_of_a_remainder`] that
/// [`tied_equalities_that_share_only_a_variable_they_do_not_define_are_solved_together`] asks,
/// with their answers. In the second, `i` in `[-3, -1]` has remainder 4, 5 or 6, so a middle
/// remainder in `[0, 3]` has none.
pub(super) fn tied_remainder_systems() -> [(Vec<Row>, &'static str); 2] {
    [
        (three_reads_of_a_remainder(-3, 0, (3, 6)), "Ok(true)"),
        (three_reads_of_a_remainder(-3, -1, (0, 3)), "Ok(false)"),
    ]
}

#[test]
fn a_merged_column_of_either_sign_is_left_unmerged() {
    // `x2` and `x4` enter as `5·(x2 - x4)` and `-5·(x2 - x4)`: one column and its negation,
    // which no structure orders, so they are not merged, and the rows `x2 - x4 >= 2` and
    // `x4 - x2 >= 2` show the system empty.
    let rows = vec![
        ge(&[5, -5, 0, 0, 0], -8),
        ge(&[0, 0, 5, 0, -5], -8),
        ge(&[0, 5, 0, -5, 0], -8),
        ge(&[-5, 0, 0, 5, 0], -8),
        ge(&[0, 0, -5, 0, 5], -8),
    ];
    assert_eq!(
        namings(&rows, 5).into_keys().collect::<Vec<_>>(),
        ["Ok(false)"]
    );
}

/// Times `decide` on `k` and `8k` disjoint copies of `base`, a system over `n` variables, each
/// copy first checked to give the answer of one, so that neither size is answered by a quick
/// refusal. Each row is written over all `n k` variables, so building the copies costs O(k²).
pub(super) fn scales_over_copies(what: &str, base: &[Row], n: usize, k: usize) {
    let (small, large) = (copies(base, n, k), copies(base, n, k * scaling::FACTOR));
    assert_answered_as_one_copy(what, base, n, [&small, &large]);
    scaling::check_order(what, k, 1, |m| {
        let f = if m == k { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}

/// `m` disjoint copies of `base`, a system over `n` variables, each row written over all `n m`
/// variables.
pub(super) fn copies(base: &[Row], n: usize, m: usize) -> Formula {
    let rows: Vec<Row> = (0..m)
        .flat_map(|p| {
            base.iter().map(move |r| {
                let mut c = vec![0; n * m];
                c[n * p..n * p + n].copy_from_slice(&r.c);
                Row {
                    c,
                    k: r.k,
                    eq: r.eq,
                }
            })
        })
        .collect();
    formula(&rows, &(0..n * m).collect::<Vec<_>>())
}

/// The check of [`scales_over_copies`]: each of `fs`, copies of `base`, has the answer of one
/// copy.
pub(super) fn assert_answered_as_one_copy<const K: usize>(
    what: &str,
    base: &[Row],
    n: usize,
    fs: [&Formula; K],
) {
    let one = answer(&copies(base, n, 1));
    eprintln!("{what}, one copy: {one}");
    for f in fs {
        assert_eq!(answer(f), one, "{what}");
    }
}

/// `x + y == 5`, `x, y >= 0`: an equality kept as rows, with a point.
pub(super) fn tied_equalities() -> Vec<Row> {
    vec![eq(&[1, 1], -5), ge(&[1, 0], 0), ge(&[0, 1], 0)]
}

/// The check of the benchmark of projections of [`star_with_choices`]: no disjunct is shown to
/// have no point, and the hulls of a leaf and a hub are those of the star alone, a leaf in
/// `[0, 23]` and `h1` in `[0, 5]`.
pub(super) fn assert_star_hulls(f: &Formula, syms: &[Atom]) {
    let (each, skipped) = project_each(f, syms).unwrap();
    let hulls: Vec<String> = (each.iter())
        .map(|s| s.as_ref().unwrap().to_string())
        .collect();
    assert_eq!(hulls, ["[0..=23]", "[0..=5]"]);
    assert_eq!(skipped, Vec::new());
}

/// A leaf and a hub of [`star_with_choices`], the names [`assert_star_hulls`] projects.
pub(super) fn leaf_and_hub() -> [Atom; 2] {
    let v = |i: usize| Atom::Sym(format!("v{i}").into());
    [v(2), v(0)]
}

/// The checks of the benchmarks of `bench/names.rs` at small sizes: copies answered as one copy,
/// each family decided true, and its point found where the benchmark asks for one.
#[test]
fn the_families_of_the_benchmarks_are_answered_at_small_sizes() {
    for (what, base, n) in [
        ("copies of a tie", claude5(), 5),
        ("copies of Codex's system", codex6(), 6),
        ("copies of tied equalities", tied_equalities(), 2),
    ] {
        let fs = [1, 2, 3, 8].map(|m| copies(&base, n, m));
        assert_answered_as_one_copy(what, &base, n, [&fs[0], &fs[1], &fs[2], &fs[3]]);
    }
    let point = |f: &Formula| {
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
    };
    for n in [2, 5, 16, 40] {
        assert_eq!(decide(&one_class_of_equalities(n)), Ok(true), "{n}");
        assert_eq!(decide(&star(n)), Ok(true), "{n}");
        assert_eq!(decide(&chain_with_disjunctions(n, n)), Ok(true), "{n}");
        let f = chain_with_disjunctions(n, 4);
        assert_eq!(decide(&f), Ok(true), "{n}");
        point(&f);
        let f = star_with_choices(n);
        assert_eq!(decide(&f), Ok(true), "{n}");
        point(&f);
        assert_star_hulls(&f, &leaf_and_hub());
        let f = separate_pairs(n);
        assert_eq!(decide(&f), Ok(true), "{n}");
        point(&f);
    }
}

/// `n` variables, each with a value in `[-2, 2]`, joined into one class by the equalities
/// `x[a] - x[b] == value[a] - value[b]` of a random tree, given in a random order with each
/// written either way round, and `0 <= x[0] <= 5`.
pub(super) fn one_class_of_equalities(n: usize) -> Formula {
    let mut rng = Rng::new(0x38_0e1f);
    let v = |i: usize| Lin::atom(Atom::Sym(format!("v{i}").into()));
    let value: Vec<i64> = (0..n).map(|_| rng.below(5) as i64 - 2).collect();
    let mut joins: Vec<(usize, usize)> = (1..n).map(|i| (i, rng.below(i))).collect();
    for i in (1..joins.len()).rev() {
        joins.swap(i, rng.below(i + 1));
    }
    let mut fs = vec![
        Formula::Con(Con::ge(&v(0), &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(5), &v(0))),
    ];
    for (a, b) in joins {
        let (a, b) = if rng.below(2) == 0 { (a, b) } else { (b, a) };
        let d = Lin::constant(value[a] - value[b]);
        fs.push(Formula::Con(Con::eq(&v(a).minus(&v(b)), &d)));
    }
    Formula::and(fs)
}

/// A unit whose `main` calls `ok(a, b, c, d) = -a + 3·b >= 10 && ...`, the cycle of four over
/// the parameters named by `names`, each declared `int` (the checker asks a linear question only
/// of a function whose parameters are all `int`), and prints whether it held.
fn cycle_unit(names: [&str; 4]) -> Vec<u8> {
    let [a, b, c, d] = names;
    format!(
        "ok({a}: int, {b}: int, {c}: int, {d}: int) = 3 * {b} - {a} >= 10 && 3 * {c} - {b} >= 10 && 3 * {d} - {c} >= 10 \
         && 3 * {a} - {d} >= 10;\nmain(m: MainArgs) {{\n  x = int(m.stdin[0] else \
         \"0\") else 0;\n  held = if ok({a}: x, {b}: x, {c}: x, {d}: x) {{ \"in\" }} else {{ \"out\" }};\n  \
         m.stdout <- \"${{held}}\";\n}}\n"
    )
    .into_bytes()
}

#[test]
fn batch_and_single_file_checking_agree_on_a_tie() {
    let first = cycle_unit(["p", "q", "r", "s"]);
    let alone = {
        let src = first.clone();
        std::thread::spawn(move || zedc::run::load(&src).err())
            .join()
            .unwrap()
    };
    let message = alone.clone().expect("the cycle of four is rejected");
    eprintln!("{message}");
    assert!(
        message.contains(
            "which occur alike in the conditions (with the same coefficients, in conditions that are alike)"
        ),
        "{message}"
    );
    // After other units on one thread, among them the same cycle under other names.
    let others = [
        cycle_unit(["s", "r", "q", "p"]),
        cycle_unit(["b", "d", "a", "c"]),
        first.clone(),
    ];
    let batch: Vec<Option<String>> = others.iter().map(|u| zedc::run::load(u).err()).collect();
    assert_eq!(batch[2], alone, "alone, then in a batch");
    for b in &batch {
        assert!(
            b.as_ref()
                .is_some_and(|m| m.contains("so only their names could order them")),
            "{b:?}"
        );
    }
}

/// A formula of a base and disjunctions, each disjunct a conjunction of rows.
type Disjunctive = (Vec<Row>, Vec<Vec<Vec<Row>>>);

/// The formula, variable `i` named `v{name[i]}`.
fn disjunctive_formula(sys: &Disjunctive, name: &[usize]) -> Formula {
    let mut parts = vec![formula(&sys.0, name)];
    for ds in &sys.1 {
        let ds = ds.iter().map(|d| formula(d, name)).collect();
        parts.push(Formula::or(ds));
    }
    Formula::and(parts)
}

/// A random formula over three variables in the box `[0, 2]^3`: the box and 2 to 4
/// disjunctions, each of 2 or 3 disjuncts of 1 or 2 rows, coefficients in `-2..=2`.
fn three_in_a_box(rng: &mut Rng) -> Disjunctive {
    let n = 3;
    let base = (0..n)
        .flat_map(|i| {
            let mut c = vec![0; n];
            c[i] = 1;
            let low = ge(&c, 0);
            c[i] = -1;
            [low, ge(&c, 2)]
        })
        .collect();
    let row = |rng: &mut Rng| {
        let c: Vec<i64> = (0..n).map(|_| rng.int(-2, 2)).collect();
        let k = rng.int(-3, 3);
        ge(&c, k)
    };
    let ors = (0..2 + rng.below(3))
        .map(|_| {
            (0..2 + rng.below(2))
                .map(|_| (0..1 + rng.below(2)).map(|_| row(rng)).collect())
                .collect()
        })
        .collect();
    (base, ors)
}

/// Of the first `count` systems of `make` drawn from `rng`, numbered from 0, those `decided`
/// keeps whose answer changes with the naming of their `n` variables, each with its answers and
/// how many namings gave each.
fn name_dependent(
    rng: &mut Rng,
    n: usize,
    count: usize,
    decided: impl Fn(usize) -> bool,
    make: impl Fn(&mut Rng) -> Disjunctive,
) -> Vec<(usize, BTreeMap<String, usize>)> {
    let mut differ = Vec::new();
    for s in 0..count {
        let sys = make(rng);
        if !decided(s) {
            continue;
        }
        let mut seen = BTreeMap::new();
        each_permutation(n, |perm| {
            *seen
                .entry(answer(&disjunctive_formula(&sys, perm)))
                .or_insert(0) += 1;
        });
        if seen.len() > 1 {
            differ.push((s, seen));
        }
    }
    differ
}

/// `count` systems of `make`, drawn with a new seed each run, none of whose answers changes
/// with the naming of their `n` variables (author P169: random tests run few cases, with a new
/// seed each run).
fn one_answer_on_fresh_systems(
    what: &str,
    n: usize,
    count: usize,
    make: impl Fn(&mut Rng) -> Disjunctive,
) {
    let (mut rng, seed) = Rng::fresh(what);
    let differ = name_dependent(&mut rng, n, count, |_| true, make);
    for (s, seen) in &differ {
        eprintln!("system {s}: {seen:?}");
    }
    assert_eq!(differ, Vec::new(), "seed {seed}");
}

// The search through the disjunctions takes the first disjunct that serves, in the order of
// the sorted formula and at the points of the solver, and the names decided both: before the
// formula was renamed by its colors, 10 of 4,000 systems at seed 0x5eed gave `true` under some
// namings and a refusal under others (system 202: Disjuncts under 2 of 6, system 797: Growth
// under 2). The 4,000 ran in two tests of 6 s each; 100 are drawn now.

#[test]
fn every_naming_of_a_formula_with_disjunctions_gives_one_answer() {
    one_answer_on_fresh_systems("three variables in a box", 3, 100, three_in_a_box);
}

#[test]
fn the_formulas_with_disjunctions_that_changed_answer_with_the_naming_give_one_answer() {
    let mut rng = Rng::new(0x5eed);
    let differ = name_dependent(
        &mut rng,
        3,
        798,
        |s| [202, 797].contains(&s),
        three_in_a_box,
    );
    assert_eq!(differ, Vec::new());
}

/// A formula over `n` variables of the regular family whose disjuncts are themselves the rows
/// of a layer, so that color refinement gives every variable one color.
fn regular_with_disjunctions(rng: &mut Rng, n: usize) -> Disjunctive {
    let half = 1 + rng.below(2) as i64;
    let base = with_box(&regular_rows(rng, n, 1), n, half);
    let ors = (0..1 + rng.below(2))
        .map(|_| {
            let layer = regular_rows(rng, n, 1);
            layer.into_iter().map(|r| vec![r]).collect()
        })
        .collect();
    (base, ors)
}

/// Where two atoms share a color the formula was searched as written, and 5 of 1,000 systems of
/// four variables at seed 0x5eed (153, 163, 664, 681 and 760) gave `true` under some namings
/// and Growth under the others. Such a formula is now settled without a search, then answered
/// when each disjunction left is alone in its group of linked rows or the colors choose its
/// disjunct, and refused with `Refusal::Unordered` otherwise (COMPLEXITY.md NAME-ties-or):
/// under one naming, 682 of the 1,000 are decided (311 `true`, 371 `false`) against 814
/// searched as written (440, 374), and 256 are refused for their order. The 1,000 took 23 s;
/// 15 are drawn now, and the five are kept below.
#[test]
fn disjunctions_whose_atoms_share_a_color() {
    one_answer_on_fresh_systems("four variables sharing colors", 4, 15, |rng| {
        regular_with_disjunctions(rng, 4)
    });
}

#[test]
fn the_formulas_whose_atoms_share_a_color_that_changed_answer_with_the_naming_give_one_answer() {
    let mut rng = Rng::new(0x5eed);
    let systems = [153, 163, 664, 681, 760];
    let differ = name_dependent(
        &mut rng,
        4,
        761,
        |s| systems.contains(&s),
        |rng| regular_with_disjunctions(rng, 4),
    );
    assert_eq!(differ, Vec::new());
}

#[test]
fn pncx_gained_color_systems_match_enumeration() {
    // The 21 systems accounting for all 504 gains of this family in R4's
    // answer log, seed 0x5eed, 24 namings each. Every system is inside [-2,2]^4
    // by regular_with_disjunctions. Evaluate its written rows directly, using
    // native integers whose magnitudes here are bounded by the small generator.
    let gained = [
        165, 175, 178, 239, 242, 254, 269, 281, 284, 301, 304, 439, 444, 455, 567, 614, 621, 887,
        909, 929, 951,
    ];
    let mut rng = Rng::new(0x5eed);
    let mut checked = 0;
    for index in 0..1000 {
        let sys = regular_with_disjunctions(&mut rng, 4);
        if !gained.contains(&index) {
            continue;
        }
        let brute = (0..625).any(|mut code| {
            let mut point = [0i64; 4];
            for x in &mut point {
                *x = code % 5 - 2;
                code /= 5;
            }
            let holds = |row: &Row| {
                let value = row.k + row.c.iter().zip(point).map(|(c, x)| c * x).sum::<i64>();
                if row.eq { value == 0 } else { value >= 0 }
            };
            sys.0.iter().all(&holds)
                && sys
                    .1
                    .iter()
                    .all(|ds| ds.iter().any(|d| d.iter().all(&holds)))
        });
        assert!(brute, "gained system {index}");
        each_permutation(4, |perm| {
            let got = decide(&disjunctive_formula(&sys, perm));
            assert_eq!(got, Ok(brute), "system {index}, naming {perm:?}");
            checked += 1;
        });
    }
    assert_eq!(checked, 504);
    println!("COLOR_GAIN_BRUTE systems=21 namings={checked} mismatches=0");
}

/// `0 <= x, y <= 9` and `x <= lo || y <= lo`, with the bounds `x, y >= at_least` when given:
/// `x` and `y` occur alike, so no renaming tells them apart.
fn either_low(lo: i64, at_least: Option<i64>) -> Formula {
    let (x, y) = (
        Lin::atom(Atom::Sym("x".into())),
        Lin::atom(Atom::Sym("y".into())),
    );
    let k = Lin::constant;
    let mut fs = vec![
        Formula::Con(Con::ge(&x, &k(0))),
        Formula::Con(Con::ge(&k(9), &x)),
        Formula::Con(Con::ge(&y, &k(0))),
        Formula::Con(Con::ge(&k(9), &y)),
        Formula::or(vec![
            Formula::Con(Con::ge(&k(lo), &x)),
            Formula::Con(Con::ge(&k(lo), &y)),
        ]),
    ];
    if let Some(m) = at_least {
        fs.push(Formula::Con(Con::ge(&x, &k(m))));
        fs.push(Formula::Con(Con::ge(&y, &k(m))));
    }
    Formula::and(fs)
}

/// `n` tasks in `slots` slots, each pair in different slots, as rows of `x[i] - x[j]`: the
/// tasks occur alike.
fn pigeons(n: usize, slots: i64) -> Formula {
    let v = |i: usize| -> Lin { Lin::atom(Atom::Sym(format!("t{i}").into())) };
    let k = Lin::constant;
    let mut fs = Vec::new();
    for i in 0..n {
        fs.push(Formula::Con(Con::ge(&v(i), &k(0))));
        fs.push(Formula::Con(Con::ge(&k(slots - 1), &v(i))));
        for j in 0..i {
            fs.push(Formula::or(vec![
                Formula::Con(Con::ge(&v(j), &v(i).plus(&k(1)))),
                Formula::Con(Con::ge(&v(i), &v(j).plus(&k(1)))),
            ]));
        }
    }
    Formula::and(fs)
}

#[test]
fn a_formula_whose_atoms_share_a_color_is_settled_or_refused() {
    // With `x, y >= 5` neither disjunct of `x <= 4 || y <= 4` has a point: no point, under
    // either naming, without a search.
    assert_eq!(decide(&either_low(4, Some(5))), Ok(false));
    assert_eq!(satisfiable(&either_low(4, Some(5))), Ok(None));
    // With `x, y >= 3` both have points, and they occur alike, so no structure says which to
    // try first; but settling showed each a point with the base, and no other disjunction is
    // linked to it, so the formula has a point, under every naming, without a choice.
    assert_eq!(decide(&either_low(4, Some(3))), Ok(true));
    let m = satisfiable(&either_low(4, Some(3)))
        .unwrap()
        .expect("a point");
    assert!(either_low(4, Some(3)).holds(&m), "{m:?}");
    // The projection keeps the disjunction: `x` takes every value of `[3, 9]`.
    let ax = Atom::Sym("x".into());
    let (each, skipped) = project_each(&either_low(4, Some(3)), &[ax]).unwrap();
    assert_eq!(each[0].as_ref().unwrap().to_string(), "[3..=9]");
    assert_eq!(skipped, Vec::new());
    // A disjunction that propagation settles leaves a conjunction, decided as any is.
    assert_eq!(decide(&either_low(-1, None)), Ok(false));
    // Two shifts `x` and `y` in `[0, 9]`, each early (`<= 2`) or late (`>= 7`): the shifts
    // occur alike, but the two disjuncts of each do not, so their colors choose one of each,
    // the same under every naming (`x >= 7`, whose constant is the least). Settling removes no
    // disjunct, since each has a point with the base. With `x + y >= 10` the choice has a
    // point; with `x + y <= 10` it has none (both late is 14), but each shift at its lower
    // bound, `x == 0 && y == 0`, is a point, which propagation from the bounds shows before
    // any choice is made. With `1 <= x + y` as well that point is excluded, and the formula is
    // refused, though `x == 1 && y == 0` is a point: the loss of choosing by color, not by a
    // search.
    let shifts = |total: Formula| {
        let k = Lin::constant;
        let mut fs = vec![total];
        for s in ["x", "y"] {
            let v = Lin::atom(Atom::Sym(s.into()));
            fs.push(Formula::Con(Con::ge(&v, &k(0))));
            fs.push(Formula::Con(Con::ge(&k(9), &v)));
            fs.push(Formula::or(vec![
                Formula::Con(Con::ge(&k(2), &v)),
                Formula::Con(Con::ge(&v, &k(7))),
            ]));
        }
        Formula::and(fs)
    };
    let sum = Lin::atom(Atom::Sym("x".into())).plus(&Lin::atom(Atom::Sym("y".into())));
    let late = shifts(Formula::Con(Con::ge(&sum, &Lin::constant(10))));
    assert_eq!(decide(&late), Ok(true));
    let m = satisfiable(&late).unwrap().expect("a point");
    assert!(late.holds(&m), "{m:?}");
    let early = shifts(Formula::Con(Con::ge(&Lin::constant(10), &sum)));
    assert_eq!(decide(&early), Ok(true));
    let m = satisfiable(&early).unwrap().expect("a point");
    assert_eq!(m.values().collect::<Vec<_>>(), [&0.into(), &0.into()]);
    assert!(early.holds(&m), "{m:?}");
    let not_both_zero = Formula::and(vec![
        early.clone(),
        Formula::Con(Con::ge(&sum, &Lin::constant(1))),
    ]);
    assert!(
        matches!(decide(&not_both_zero), Err(Refusal::Unordered(_))),
        "{:?}",
        decide(&not_both_zero)
    );
    // Tasks in slots, each pair apart: the two disjuncts of `t0 <= t1 - 1 || t0 >= t1 + 1`
    // differ only by which task is first, so they tie, and the disjunctions are linked through
    // the tasks; three tasks in two slots, which have no point, are refused like four in
    // three, and the message names the tied tasks and the disjunctions left
    // (`omega::each_cause_of_a_refusal_has_its_own_message` reads it whole).
    for (n, slots, pairs) in [(3, 2, 3), (4, 3, 6)] {
        let Err(Refusal::Unordered(t)) = decide(&pigeons(n, slots)) else {
            panic!("{n} tied tasks in {slots} slots are refused");
        };
        assert_eq!(t.vars.len(), n, "{t:?}");
        assert_eq!(t.rows.len(), pairs, "{t:?}");
    }
}

/// A star: `h1` in `[0, 5]`, `h2` in `[0, 7]`, and for each of `n` leaves `x[i]`,
/// `h1 + h2 <= x[i] <= h1 + 2·h2 + 4`. The leaves occur alike and share no row, so each step
/// eliminates all of them together.
pub(super) fn star(n: usize) -> Formula {
    let v = |i: usize| -> Lin { Lin::atom(Atom::Sym(format!("v{i}").into())) };
    let k = Lin::constant;
    let (h1, h2) = (v(0), v(1));
    let mut fs = vec![
        Formula::Con(Con::ge(&h1, &k(0))),
        Formula::Con(Con::ge(&k(5), &h1)),
        Formula::Con(Con::ge(&h2, &k(0))),
        Formula::Con(Con::ge(&k(7), &h2)),
    ];
    for i in 0..n {
        let x = v(2 + i);
        fs.push(Formula::Con(Con::ge(&x, &h1.plus(&h2))));
        let top = h1.plus(&h2).plus(&h2).plus(&k(4));
        fs.push(Formula::Con(Con::ge(&top, &x)));
    }
    Formula::and(fs)
}

#[test]
fn a_refusal_of_a_renamed_formula_names_the_variables_as_written() {
    // The cycle of four ties under every naming, and a disjunction tells its variables apart,
    // so the formula is renamed; the refusal of the cycle is written over the names given.
    let sys: Disjunctive = (
        cycle(4),
        vec![vec![
            vec![ge(&[1, -1, 0, 0], 1000)],
            vec![ge(&[0, 0, 1, -2], 1000)],
        ]],
    );
    let Err(Refusal::Tie(t)) = decide(&disjunctive_formula(&sys, &[0, 1, 2, 3])) else {
        panic!("the cycle of four is refused with a tie");
    };
    let mut vars = t.vars.clone();
    vars.sort();
    assert_eq!(vars, ["v0", "v1", "v2", "v3"]);
    let message = Refusal::Tie(t).to_string();
    assert!(!message.contains('#'), "{message}");
    assert!(message.contains("10 >= 0"), "{message}");
    assert_eq!(
        answers_under_every_naming(&sys, 4),
        ["Err(Tie, 4 variables)"]
    );
}

/// The answers of `sys` under every naming of its `n` variables.
fn answers_under_every_naming(sys: &Disjunctive, n: usize) -> Vec<String> {
    let mut seen = std::collections::BTreeSet::new();
    each_permutation(n, |perm| {
        seen.insert(answer(&disjunctive_formula(sys, perm)));
    });
    seen.into_iter().collect()
}

#[test]
fn a_point_and_a_projection_of_a_renamed_formula_are_over_the_names_as_written() {
    // `0 <= x <= 2`, `0 <= y <= 5`, and `x·y >= 3 || x >= 7`: a point has `x·y >= 3`.
    let (x, y) = (Arc::<str>::from("x"), Arc::<str>::from("y"));
    let (ax, ay) = (Atom::Sym(x.clone()), Atom::Sym(y.clone()));
    let xy = Lin::atom(Atom::product(&x, &y));
    let zero = Lin::constant(0);
    let f = Formula::and(vec![
        Formula::Con(Con::ge(&Lin::atom(ax.clone()), &zero)),
        Formula::Con(Con::ge(&Lin::constant(2), &Lin::atom(ax.clone()))),
        Formula::Con(Con::ge(&Lin::atom(ay.clone()), &zero)),
        Formula::Con(Con::ge(&Lin::constant(5), &Lin::atom(ay.clone()))),
        Formula::Con(Con::ge(&xy, &Lin::atom(ax.clone()))),
        Formula::or(vec![
            Formula::Con(Con::ge(&xy, &Lin::constant(3))),
            Formula::Con(Con::ge(&Lin::atom(ax.clone()), &Lin::constant(7))),
        ]),
    ]);
    let m = satisfiable(&f).unwrap().expect("a point");
    assert!(m.keys().all(|a| !a.to_string().contains('#')), "{m:?}");
    assert!(m.contains_key(&ax) || m.contains_key(&ay), "{m:?}");
    // The projections, onto a symbol of the formula and one it does not mention.
    let free = Atom::Sym(Arc::from("z"));
    let (each, _) = project_each(&f, &[ax.clone(), ay.clone(), free]).unwrap();
    let ends: Vec<_> = each.iter().map(|s| s.as_ref().unwrap().bounds()).collect();
    assert_eq!(
        ends[0],
        Some((&End::Fin(Num::from(0)), &End::Fin(Num::from(2))))
    );
    assert_eq!(
        ends[1],
        Some((&End::Fin(Num::from(0)), &End::Fin(Num::from(5))))
    );
    assert_eq!(ends[2], Some((&End::NegInf, &End::PosInf)));
}

/// The chain `x[0] >= 0`, `x[i + 1] - x[i] >= 1`, `x[n - 1] <= 2·n`, whose variables color
/// refinement tells apart by their distance from `x[0]`, with `x[i + 1] - x[i] <= 1 ||
/// x[i + 1] - x[i] >= 3` at each `i` that `every` divides: renamed, then searched.
pub(super) fn chain_with_disjunctions(n: usize, every: usize) -> Formula {
    let at = |i: usize, c: i64, j: usize, d: i64| {
        let mut cs = vec![0; n];
        cs[i] += c;
        cs[j] += d;
        cs
    };
    let mut base = vec![
        ge(&at(0, 1, 0, 0), 0),
        ge(&at(n - 1, -1, n - 1, 0), 2 * n as i64),
    ];
    base.extend((0..n - 1).map(|i| ge(&at(i + 1, 1, i, -1), -1)));
    let ors = ((0..n - 1).step_by(every))
        .map(|i| {
            vec![
                vec![ge(&at(i, 1, i + 1, -1), 1)],
                vec![ge(&at(i + 1, 1, i, -1), -3)],
            ]
        })
        .collect();
    disjunctive_formula(&(base, ors), &(0..n).collect::<Vec<_>>())
}

/// [`star`] with, for each leaf, `x[i] <= h1 + h2 + 1 || x[i] >= h1 + 2·h2 + 3`: one
/// connected formula whose leaves occur alike, each with a disjunction of its own.
pub(super) fn star_with_choices(n: usize) -> Formula {
    let v = |i: usize| -> Lin { Lin::atom(Atom::Sym(format!("v{i}").into())) };
    let k = Lin::constant;
    let (h1, h2) = (v(0), v(1));
    let mut fs = vec![star(n)];
    for i in 0..n {
        let x = v(2 + i);
        fs.push(Formula::or(vec![
            Formula::Con(Con::ge(&h1.plus(&h2).plus(&k(1)), &x)),
            Formula::Con(Con::ge(&x, &h1.plus(&h2).plus(&h2).plus(&k(3)))),
        ]));
    }
    Formula::and(fs)
}

// The leaves of `star_with_choices` occur alike, but the two disjuncts of each do not, so the
// colors choose one disjunct of each, and one solve of the base with them finds a point: one
// settling and one solve, where the probe this replaced, which tested each of the 2n disjuncts
// with the n − 1 other disjunctions, was cubic (8 to 64 leaves: 22 ms to 10.8 s, then refused).
// Settling then stayed quadratic: it tested each disjunct that the base's point missed against
// every row linked to it through the hubs, and the projection settled each disjunct with that
// group. Now each leaf's disjunction is removed before settling (`absorb`): the leaf occurs in
// no other row but its two bounds, and one of its disjuncts (`x[i] <= h1 + h2 + 1`) meets them
// for every value of the hubs, so the disjunction removes no point. What is left is the star
// alone, settled once; the projection keeps only the disjunction of the leaf it is asked for.
// COMPLEXITY.md rows DECIDE-disj-chain and NAME-ties-or.

/// `n` copies of `either_low(4, Some(3))` over atoms of their own: every `x[i]` and `y[i]`
/// occur alike, and each disjunction is alone in its group.
pub(super) fn separate_pairs(n: usize) -> Formula {
    let k = Lin::constant;
    let mut fs = Vec::new();
    for i in 0..n {
        let (x, y) = (
            Lin::atom(Atom::Sym(format!("x{i}").into())),
            Lin::atom(Atom::Sym(format!("y{i}").into())),
        );
        for v in [&x, &y] {
            fs.push(Formula::Con(Con::ge(v, &k(3))));
            fs.push(Formula::Con(Con::ge(&k(9), v)));
        }
        fs.push(Formula::or(vec![
            Formula::Con(Con::ge(&k(4), &x)),
            Formula::Con(Con::ge(&k(4), &y)),
        ]));
    }
    Formula::and(fs)
}

/// The tied cycle of four ([`cycle`]) with every variable at most `top`, variable `i` named
/// `v{name[i]}`. Summing the cycle's rows gives `2·Σ x >= 40`, so with `top <= 4`, where
/// `Σ x <= 16`, it has no point; the solver refuses it for its tie.
fn capped_cycle(top: i64, name: &[usize]) -> Formula {
    let mut rows = cycle(4);
    for i in 0..4 {
        let mut c = vec![0; 4];
        c[i] = -1;
        rows.push(ge(&c, top));
    }
    formula(&rows, name)
}

#[test]
fn a_disjunct_the_solver_refuses_is_not_taken_for_a_point() {
    // `(C4 && x <= 4) || (C4 && x <= 3)`: neither disjunct has a point, and the solver
    // refuses both, so settling removes neither. The answer must not be `true` (verifier of
    // NAME-ties repair 3 found `decide` gave `Ok(true)` while `satisfiable` refused): it is
    // refused, by `decide` and `satisfiable` alike, under every naming.
    let mut seen = BTreeMap::new();
    each_permutation(4, |perm| {
        let f = Formula::or(vec![capped_cycle(4, perm), capped_cycle(3, perm)]);
        let d = decide(&f);
        let s = satisfiable(&f);
        assert!(d.is_err(), "{f}: decide gave {d:?}");
        assert!(s.is_err(), "{f}: satisfiable gave {s:?}");
        *seen.entry(answer(&f)).or_insert(0) += 1;
    });
    assert_eq!(seen.len(), 1, "{seen:?}");
}

#[test]
fn a_refused_disjunct_beside_one_with_a_point_gives_one_answer() {
    // `y` in `[0, 9]` and `(C4 && x <= 3) || (1 <= y <= 2)`: the second disjunct has a point
    // and the first is refused. The disjunction is linked to no other, so the formula has a point,
    // under every naming of the cycle and whether `y` sorts before or after it; `satisfiable`
    // must not take the refused disjunct because its name comes first.
    for y in ["a", "z"] {
        let v = Lin::atom(Atom::Sym(y.into()));
        let k = Lin::constant;
        let mut seen = BTreeMap::new();
        each_permutation(4, |perm| {
            let f = Formula::and(vec![
                Formula::Con(Con::ge(&v, &k(0))),
                Formula::Con(Con::ge(&k(9), &v)),
                Formula::or(vec![
                    capped_cycle(3, perm),
                    Formula::and(vec![
                        Formula::Con(Con::ge(&k(2), &v)),
                        Formula::Con(Con::ge(&v, &k(1))),
                    ]),
                ]),
            ]);
            assert_eq!(decide(&f), Ok(true), "{f}");
            let m = satisfiable(&f).unwrap_or_else(|e| panic!("{f}: {e}"));
            let m = m.expect("a point");
            assert!(f.holds(&m), "{f}: {m:?}");
            *seen.entry(answer(&f)).or_insert(0) += 1;
        });
        assert_eq!(seen.len(), 1, "{seen:?}");
    }
}
