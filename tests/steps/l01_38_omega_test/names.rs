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

/// Pugh's example (Pugh 1992, doi:10.1145/135226.135233, sec. 2.3.3, quoted in zedc-presburger
/// `lib.rs`, "References") between `x[n / 2]` and `x[n / 2 + 1]` of a chain of `n` steps
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

/// [`cycle`] with each row also turned the other way, `-x[i + 1] + 3·x[i] - 10 >= 0`: its
/// symmetries are those of a polygon, turning and reflecting it, so once one variable is
/// fixed its two neighbors are still alike, and no swap of two variables maps its rows onto
/// themselves (for `n >= 4`). `x = (5, 5, ...)` is a point.
fn cycle_both_ways(n: usize) -> Vec<Row> {
    let mut rows = cycle(n);
    rows.extend((0..n).map(|i| {
        let mut c = vec![0; n];
        c[(i + 1) % n] = -1;
        c[i] = 3;
        ge(&c, -10)
    }));
    rows
}

/// The cycle of three turned one way with each variable doubled: the pairs `{0, 1}`,
/// `{2, 3}`, `{4, 5}`, and `-x[a] + 3·x[b] - 10 >= 0` for each `a` of a pair and `b` of the
/// next. Every variable has two rows of each sign, so its elimination adds no terms, and
/// occurs alike. Its symmetries turn the cycle and swap the two variables of any pair, each
/// pair on its own: no swap of two variables of different pairs maps the rows onto
/// themselves, and with one variable fixed, and then one of the next pair, the last pair
/// is still alike, so `System::symmetries`, which fixes two variables at most, finds none,
/// and the tie is refused. Summing the rows gives `4·Σ x >= 120`; `x = (5, 5, ...)` is a
/// point.
fn doubled_cycle() -> Vec<Row> {
    let mut rows = Vec::new();
    for k in 0..3 {
        for a in [2 * k, 2 * k + 1] {
            for b in [(2 * k + 2) % 6, (2 * k + 3) % 6] {
                let mut c = vec![0; 6];
                c[a] = -1;
                c[b] = 3;
                rows.push(ge(&c, -10));
            }
        }
    }
    rows
}

#[test]
fn a_tie_that_shares_a_row_is_refused() {
    let rows = doubled_cycle();
    assert!(holds(&rows, &[5, 5, 5, 5, 5, 5]));
    let got = decide(&formula(&rows, &[0, 1, 2, 3, 4, 5]));
    let Err(Refusal::Tie(t)) = got else {
        panic!("the doubled cycle is refused with a tie: {got:?}");
    };
    let mut vars = t.vars.clone();
    vars.sort();
    assert_eq!(vars, ["v0", "v1", "v2", "v3", "v4", "v5"]);
    // Each row written with its terms in the order of the canonical form.
    let mut shared = t.rows.clone();
    shared.sort();
    assert_eq!(
        shared,
        [
            "-v0 + 3 * v2 - 10 >= 0",
            "-v0 + 3 * v3 - 10 >= 0",
            "-v2 + 3 * v4 - 10 >= 0",
            "-v2 + 3 * v5 - 10 >= 0",
            "-v3 + 3 * v4 - 10 >= 0",
            "-v3 + 3 * v5 - 10 >= 0",
            "-v4 + 3 * v1 - 10 >= 0",
            "-v5 + 3 * v1 - 10 >= 0",
            "3 * v0 - v4 - 10 >= 0",
            "3 * v0 - v5 - 10 >= 0",
            "3 * v2 - v1 - 10 >= 0",
            "3 * v3 - v1 - 10 >= 0",
        ]
    );
    let message = Refusal::Tie(t).to_string();
    assert!(
        message.contains(
            "which occur alike in the conditions (with the same coefficients, in conditions that are alike)"
        ),
        "{message}"
    );
    assert!(message.contains("`-v0 + 3 * v3 - 10 >= 0`"), "{message}");
    // Under every naming, the same refusal.
    assert_eq!(
        namings(&rows, 6).into_keys().collect::<Vec<_>>(),
        ["Err(Tie, 6 variables)"]
    );
}

/// The rows the solver meets for two links of `ladder::product_chain_with_abs`, over `z0`,
/// `z1`, `x0`, `y0`, `x1`, `y1`, `q0`, `q1` by place: `0 <= z0 < z1 <= 4`, `x[i] >= z[i]`,
/// `y[i] >= z[i]`, and `|x[i] - y[i]| <= q[i] <= z[i] + 1`, where `q[i] >= x[i] - y[i]` and
/// `q[i] >= y[i] - x[i]` are the two hull rows of `abs`. `x[i]` and `y[i]` share the hull
/// rows and occur alike, and swapping them maps the rows onto themselves.
fn two_abs_links() -> Vec<Row> {
    vec![
        ge(&[-1, 1, 0, 0, 0, 0, 0, 0], -1),
        ge(&[1, 0, 0, 0, 0, 0, 0, 0], 0),
        ge(&[0, -1, 0, 0, 0, 0, 0, 0], 4),
        ge(&[1, 0, 0, 0, 0, 0, -1, 0], 1),
        ge(&[0, 1, 0, 0, 0, 0, 0, -1], 1),
        ge(&[-1, 0, 1, 0, 0, 0, 0, 0], 0),
        ge(&[-1, 0, 0, 1, 0, 0, 0, 0], 0),
        ge(&[0, -1, 0, 0, 1, 0, 0, 0], 0),
        ge(&[0, -1, 0, 0, 0, 1, 0, 0], 0),
        ge(&[0, 0, -1, 1, 0, 0, 1, 0], 0),
        ge(&[0, 0, 1, -1, 0, 0, 1, 0], 0),
        ge(&[0, 0, 0, 0, -1, 1, 0, 1], 0),
        ge(&[0, 0, 0, 0, 1, -1, 0, 1], 0),
    ]
}

#[test]
fn a_tie_that_a_swap_maps_onto_itself_is_decided() {
    // The rows have a point, which the box stage finds before any tie matters.
    let rows = two_abs_links();
    assert!(holds(&rows, &[0, 1, 0, 0, 1, 1, 0, 0]));
    let named: Vec<usize> = (0..8).collect();
    assert_eq!(decide(&formula(&rows, &named)), Ok(true));
    // With `q0 <= -1`, which the two hull rows of `q0` contradict, no point. Until
    // FAIL-abs-hull-rows-tie this was refused with a tie between `x1` and `y1`, which share
    // their hull rows: which goes first was left to their names. Swapping them maps the rows
    // onto themselves, so either order gives the same answer, and the solver takes one.
    let mut empty = rows.clone();
    empty.push(ge(&[0, 0, 0, 0, 0, 0, -1, 0], -1));
    assert_eq!(decide(&formula(&empty, &named)), Ok(false));
    // Under other namings, the same answers.
    let (mut rng, seed) = Rng::fresh("a tie that a swap maps onto itself");
    for (rows, answer) in [(&rows, "Ok(true)"), (&empty, "Ok(false)")] {
        let seen = sampled_namings(rows, 8, &mut rng, 100);
        assert_eq!(
            seen.into_keys().collect::<Vec<_>>(),
            [answer],
            "seed {seed:#x}"
        );
    }
    // The doubled cycle of `a_tie_that_shares_a_row_is_refused` is the control: no swap of
    // two of its variables maps its rows onto themselves, and fixing two variables still
    // leaves two alike, so its tie is still refused.
}

#[test]
fn a_tie_that_only_a_rotation_maps_onto_itself_is_decided() {
    // The cycle of four one way: the symmetries of its rows turn it, and no swap of two
    // variables maps its rows onto themselves. Until FAIL-alone-point-refused-at-model it was
    // refused with a tie. Fixing `x[0]` tells the other three apart (the row from `x[0]`
    // leads to `x[1]`, the row into `x[0]` comes from `x[3]`), and the turns of the cycle map
    // `x[0]` onto each of the others and the rows onto themselves, so the solver may
    // eliminate any one of the four first: it takes one, and every naming gives one answer.
    let rows = cycle(4);
    assert!(holds(&rows, &[5, 5, 5, 5]));
    assert_eq!(decide(&formula(&rows, &[0, 1, 2, 3])), Ok(true));
    assert_eq!(
        namings(&rows, 4).into_keys().collect::<Vec<_>>(),
        ["Ok(true)"]
    );
    // Capped at 4, it has no point (summing its rows gives `2·Σ x >= 40`); at 5 it has one.
    for (top, want) in [(4, "Ok(false)"), (5, "Ok(true)")] {
        let mut capped = rows.clone();
        for i in 0..4 {
            let mut c = vec![0; 4];
            c[i] = -1;
            capped.push(ge(&c, top));
        }
        assert_eq!(
            namings(&capped, 4).into_keys().collect::<Vec<_>>(),
            [want],
            "capped at {top}"
        );
    }
    // Cycles of five and six, whose second tie has no symmetry, are in
    // `a_cycle_turned_both_ways_and_a_longer_cycle_one_way_are_decided`.
}

#[test]
fn a_cycle_turned_both_ways_and_a_longer_cycle_one_way_are_decided() {
    // FAIL-tie-cycle-reflected-and-second-tie. Each row `-x[a] + 3·x[b] - 10 >= 0` of these
    // cycles, summed, gives `Σ x >= 5·n`, so with every variable capped at 4 there is no
    // point, and at 5 there is one.
    let capped = |mut rows: Vec<Row>, n: usize, top: i64| {
        for i in 0..n {
            let mut c = vec![0; n];
            c[i] = -1;
            rows.push(ge(&c, top));
        }
        rows
    };
    // Turned both ways, the cycle of four is a square: fixing `x[0]` leaves its two
    // neighbors alike, and fixing one of them as well tells every variable apart.
    let rows = cycle_both_ways(4);
    assert!(holds(&rows, &[5, 5, 5, 5]));
    assert_eq!(
        namings(&rows, 4).into_keys().collect::<Vec<_>>(),
        ["Ok(true)"]
    );
    for (top, want) in [(4, "Ok(false)"), (5, "Ok(true)")] {
        let rows = capped(cycle_both_ways(4), 4, top);
        assert_eq!(
            namings(&rows, 4).into_keys().collect::<Vec<_>>(),
            [want],
            "capped at {top}"
        );
    }
    let (mut rng, seed) = Rng::fresh("a longer cycle one way is decided");
    for n in [5, 6] {
        // One way: the first tie is taken by a turn of the cycle; eliminating one variable
        // joins its two rows, and the variables left tie on the solver's key with no
        // symmetry between them. Refining the keys by the rows tells them apart.
        // Both ways: the polygon of `n` sides, as the square.
        for rows in [cycle(n), cycle_both_ways(n)] {
            assert!(holds(&rows, &vec![5; n]));
            let seen = sampled_namings(&rows, n, &mut rng, 60);
            assert_eq!(
                seen.into_keys().collect::<Vec<_>>(),
                ["Ok(true)"],
                "n = {n}, seed {seed:#x}"
            );
            for (top, want) in [(4, "Ok(false)"), (5, "Ok(true)")] {
                let seen = sampled_namings(&capped(rows.clone(), n, top), n, &mut rng, 60);
                assert_eq!(
                    seen.into_keys().collect::<Vec<_>>(),
                    [want],
                    "n = {n}, capped at {top}, seed {seed:#x}"
                );
            }
        }
    }
    // With coefficients 2 and 3, `3·x[b] - 2·x[a] >= 1`, no elimination is exact, so the
    // splinter search reads the ties taken (`broken_swap`). Summed, the rows give `Σ x >= n`
    // (one way) or `2·Σ x >= 2·n` (both ways): capped at 0 there is no point, at 1 the point
    // `(1, 1, ...)`.
    let dark = |n: usize, both: bool| {
        let mut rows = Vec::new();
        for i in 0..n {
            let pairs = if both {
                vec![(i, (i + 1) % n), ((i + 1) % n, i)]
            } else {
                vec![(i, (i + 1) % n)]
            };
            for (a, b) in pairs {
                let mut c = vec![0; n];
                c[a] = -2;
                c[b] = 3;
                rows.push(ge(&c, -1));
            }
        }
        rows
    };
    for n in [4, 5, 6] {
        for both in [false, true] {
            for (top, want) in [(0, "Ok(false)"), (1, "Ok(true)")] {
                let rows = capped(dark(n, both), n, top);
                let seen = if n == 4 {
                    namings(&rows, n)
                } else {
                    sampled_namings(&rows, n, &mut rng, 60)
                };
                // Both ways with no point, the tie is taken and the splinters then outgrow
                // the solver's bound, under every naming alike (FAIL-dark-cycle-both-ways-growth).
                let want = if both && top == 0 {
                    "Err(Growth)"
                } else {
                    want
                };
                assert_eq!(
                    seen.into_keys().collect::<Vec<_>>(),
                    [want],
                    "n = {n}, both ways {both}, capped at {top}, seed {seed:#x}"
                );
            }
        }
    }
}

/// Random rows over `v0`..`v3` that swapping `v0` and `v1` maps onto themselves: each row
/// over `v0`, `v2` and `v3` with its image over `v1`, and one row with `v0` and `v1` at one
/// coefficient, all in the box `-4..=4`. The coefficients reach 13, as in Pugh's example,
/// so that eliminations are dark and splinters are searched after the tie is taken.
fn swap_symmetric(rng: &mut Rng) -> Vec<Row> {
    let mut rows = Vec::new();
    for _ in 0..1 + rng.below(3) {
        let (a, b, c, k) = (
            rng.int(-13, 13),
            rng.int(-13, 13),
            rng.int(-3, 3),
            rng.int(-30, 30),
        );
        rows.push(ge(&[a, 0, b, c], k));
        rows.push(ge(&[0, a, b, c], k));
    }
    let (a, b) = (rng.int(-5, 5), rng.int(-5, 5));
    rows.push(ge(&[a, a, b, 0], rng.int(-20, 20)));
    with_box(&rows, 4, 4)
}

#[test]
fn ties_taken_by_a_swap_agree_with_enumeration() {
    // The answer, whether or not the tie is taken and whatever splinters follow it, is that
    // of enumerating the box, under the naming as written and under the swap. Most cases are
    // answered (358 to 372 of 400 in three runs); some are refused with `Growth`, as they are
    // without the rule. No count of the answered is reached at every seed, so none is
    // asserted; `built_ties_taken_by_a_swap_are_answered` asserts an answer of each kind.
    let (mut rng, seed) = Rng::fresh("ties taken by a swap");
    for case in 0..200 {
        let rows = swap_symmetric(&mut rng);
        swap_answers(&rows, &format!("seed {seed:#x}, case {case}"));
    }
}

/// `rows`, of [`swap_symmetric`]'s shape, and the same rows with `v0 <= w <= 4` over a fifth
/// variable `w`, each answered alike under the naming as written and under the swap of `v0`
/// and `v1`, and as enumeration of the box `-4..=4` answers wherever `decide` answers; the
/// answers of `decide` on the two, `None` where it refuses. `what` is named on failure.
fn swap_answers(rows: &[Row], what: &str) -> [Option<bool>; 2] {
    let span = -4..=4i64;
    let mut has_point = false;
    'search: for a in span.clone() {
        for b in span.clone() {
            for c in span.clone() {
                for d in span.clone() {
                    if holds(rows, &[a, b, c, d]) {
                        has_point = true;
                        break 'search;
                    }
                }
            }
        }
    }
    // The control: the same rows with `v0 <= w <= 4` over a fifth variable `w`, which the
    // swap does not map onto themselves. Its projection `v0 <= 4` the box holds, so `w`
    // changes no answer; but `v0` and `v1` now differ in color, and no tie is taken.
    let mut with_w: Vec<Row> = rows
        .iter()
        .map(|r| Row {
            c: [&r.c[..], &[0]].concat(),
            ..r.clone()
        })
        .collect();
    with_w.push(ge(&[-1, 0, 0, 0, 1], 0));
    with_w.push(ge(&[0, 0, 0, 0, -1], 4));
    [rows, &with_w[..]].map(|rows| {
        let [written, swapped] =
            [[0, 1, 2, 3, 4], [1, 0, 2, 3, 4]].map(|name| formula(rows, &name));
        assert_eq!(answer(&written), answer(&swapped), "{what}: {rows:?}");
        let got = decide(&written).ok();
        if let Some(got) = got {
            assert_eq!(got, has_point, "{what}: {rows:?}");
        }
        got
    })
}

/// Two systems of [`swap_symmetric`]'s shape, each answered, with and without the fifth
/// variable: `v0 >= 0`, its image `v1 >= 0` and `v0 + v1 >= 0` hold at the origin;
/// `v0 >= 3`, `v1 >= 3` and `v0 + v1 <= 5` ask for a sum at least 6 and at most 5, so no
/// point. The coefficients and constants lie in what [`swap_symmetric`] draws.
#[test]
fn built_ties_taken_by_a_swap_are_answered() {
    let point = with_box(
        &[
            ge(&[1, 0, 0, 0], 0),
            ge(&[0, 1, 0, 0], 0),
            ge(&[1, 1, 0, 0], 0),
        ],
        4,
        4,
    );
    assert_eq!(swap_answers(&point, "built, with a point"), [Some(true); 2]);
    let empty = with_box(
        &[
            ge(&[1, 0, 0, 0], -3),
            ge(&[0, 1, 0, 0], -3),
            ge(&[-1, -1, 0, 0], 5),
        ],
        4,
        4,
    );
    assert_eq!(
        swap_answers(&empty, "built, with no point"),
        [Some(false); 2]
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

/// A unit whose `main` calls `ok(a, b, c, d, e, f) = 3 * c - a >= 10 && ...`, the rows of
/// [`doubled_cycle`] over the parameters named by `names`, each declared `int` (the checker
/// asks a linear question only of a function whose parameters are all `int`), and prints
/// whether it held.
fn cycle_unit(names: [&str; 6]) -> Vec<u8> {
    let mut conds = Vec::new();
    for k in 0..3 {
        for a in [2 * k, 2 * k + 1] {
            for b in [(2 * k + 2) % 6, (2 * k + 3) % 6] {
                conds.push(format!("3 * {} - {} >= 10", names[b], names[a]));
            }
        }
    }
    let params: Vec<String> = names.iter().map(|n| format!("{n}: int")).collect();
    let args: Vec<String> = names.iter().map(|n| format!("{n}: x")).collect();
    format!(
        "ok({}) = {};\nmain(m: MainArgs) {{\n  x = int(m.stdin[0] else #ioError -> \"0\" else #outOfBounds -> \"0\") else #invalid -> 0;\n  \
         held = if ok({}) {{ \"in\" }} else {{ \"out\" }};\n  m.stdout <- \"${{held}}\";\n}}\n",
        params.join(", "),
        conds.join(" && "),
        args.join(", "),
    )
    .into_bytes()
}

#[test]
fn batch_and_single_file_checking_agree_on_a_tie() {
    let first = cycle_unit(["p", "q", "r", "s", "t", "u"]);
    let alone = {
        let src = first.clone();
        std::thread::spawn(move || zedc::run::load(&src).err())
            .join()
            .unwrap()
    };
    let message = alone.clone().expect("the doubled cycle is rejected");
    eprintln!("{message}");
    assert!(
        message.contains(
            "which occur alike in the conditions (with the same coefficients, in conditions that are alike)"
        ),
        "{message}"
    );
    // After other units on one thread, among them the same cycle under other names.
    let others = [
        cycle_unit(["u", "t", "s", "r", "q", "p"]),
        cycle_unit(["b", "d", "f", "a", "c", "e"]),
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
/// under one naming, 682 of the 1,000 were decided (311 `true`, 371 `false`) against 814
/// searched as written (440, 374), and 256 refused for their order. Since plan row
/// FAIL-or-if-tie-refusal, a tie that every swap maps onto itself is ranked by name and
/// searched where the tied path leaves it: 716 decided (321 `true`, 395 `false`), 232 refused
/// for their order, 52 with `Growth`, none name-dependent. The 1,000 took 23 s; 15 are drawn
/// now, and the five are kept below.
#[test]
fn disjunctions_whose_atoms_share_a_color() {
    one_answer_on_fresh_systems("four variables sharing colors", 4, 15, |rng| {
        regular_with_disjunctions(rng, 4)
    });
}

/// A row given by its terms (variable, coefficient), its constant, and whether it is an
/// equation.
type Sparse = (Vec<(usize, i64)>, i64, bool);

/// The rows `rows` over `n` variables.
fn dense(n: usize, rows: &[Sparse]) -> Vec<Row> {
    rows.iter()
        .map(|(t, k, e)| {
            let mut c = vec![0; n];
            for (i, x) in t {
                c[*i] += x;
            }
            Row { c, k: *k, eq: *e }
        })
        .collect()
}

/// A system of 16 variables drawn at random (chains of two- and three-term rows, three of the
/// variables boxed) with one disjunction, `v5 - v4 == 3 || v5 - v4 == 1`, each of whose
/// disjuncts the base rules out: the system has no point.
fn a_chain_and_a_choice_with_no_point() -> (usize, Disjunctive) {
    let rows: Vec<Sparse> = vec![
        (vec![(8, 1)], 4, false),
        (vec![(8, -1)], 4, false),
        (vec![(10, 1)], 4, false),
        (vec![(10, -1)], 4, false),
        (vec![(11, 1)], 4, false),
        (vec![(11, -1)], 4, false),
        (vec![(1, -3), (0, 3)], 1, false),
        (vec![(2, 1), (1, 1)], 6, true),
        (vec![(3, -1), (2, -1)], -1, false),
        (vec![(4, -3), (1, 1)], -1, false),
        (vec![(5, -1), (1, 3)], 4, false),
        (vec![(6, -1), (0, -1)], 3, false),
        (vec![(7, 2), (2, -3)], 2, false),
        (vec![(8, -3), (3, 2)], 5, false),
        (vec![(9, 2), (7, -1)], 6, false),
        (vec![(10, 1), (5, -2)], 6, false),
        (vec![(11, -1), (4, -1)], 1, false),
        (vec![(12, 1), (9, 1)], 4, false),
        (vec![(13, 3), (6, 1)], 0, false),
        (vec![(14, -1), (8, 2)], -2, false),
        (vec![(15, -3), (6, -1)], 4, false),
        (vec![(1, 2), (0, -1)], 6, false),
        (vec![(2, -1), (0, -1)], 4, false),
        (vec![(3, -1), (0, 1)], 1, false),
        (vec![(4, 1), (0, -1)], 3, false),
        (vec![(5, -1), (4, -1), (0, 1)], 6, false),
        (vec![(6, 1), (3, 1)], 2, false),
        (vec![(7, 1), (3, -3)], 5, false),
        (vec![(8, 1), (2, 1)], 1, false),
        (vec![(9, 3), (2, 1)], -2, false),
        (vec![(10, -1), (3, -1), (8, -2)], -1, false),
        (vec![(11, 2), (7, -1)], -2, false),
        (vec![(12, 1), (11, -1)], 1, false),
        (vec![(13, -1), (10, -1)], 1, false),
        (vec![(14, -2), (12, 3)], 5, false),
        (vec![(15, 1), (9, -2)], 3, false),
        (vec![(1, -1), (0, -3)], 4, false),
    ];
    let n = 16;
    let ors = vec![vec![
        dense(n, &[(vec![(5, 1), (4, -1)], -3, true)]),
        dense(n, &[(vec![(5, 1), (4, -1)], -1, true)]),
    ]];
    (n, (dense(n, &rows), ors))
}

/// `sys` over `n` variables beside [`triangles_and_a_hexagon`] over the next twelve, whose
/// atoms share a color that no swap maps onto itself, so that the whole is settled as a tied
/// formula ([`settle_tied`] in the library) and not renamed.
fn beside_the_tied_gadget(n: usize, sys: &Disjunctive) -> Disjunctive {
    let widen = |r: &Row, at: usize| {
        let mut c = vec![0; n + 12];
        c[at..at + r.c.len()].copy_from_slice(&r.c);
        Row {
            c,
            k: r.k,
            eq: r.eq,
        }
    };
    let widen_ors = |ors: &[Vec<Vec<Row>>], at: usize| -> Vec<Vec<Vec<Row>>> {
        (ors.iter())
            .map(|ds| {
                (ds.iter())
                    .map(|d| d.iter().map(|r| widen(r, at)).collect())
                    .collect()
            })
            .collect()
    };
    let (gb, go) = triangles_and_a_hexagon();
    let mut base: Vec<Row> = sys.0.iter().map(|r| widen(r, 0)).collect();
    base.extend(gb.iter().map(|r| widen(r, n)));
    let mut ors = widen_ors(&sys.1, 0);
    ors.extend(widen_ors(&go, n));
    (base, ors)
}

/// A tied formula's disjuncts were tested against the base projected onto their atoms, and
/// that projection was made by eliminations in an order the names chose, so the solver refused
/// it under some namings and showed the disjunct empty under others; the base rows linked to
/// the disjunct, tried after a refusal, are refused under all. The chain below beside the tied
/// gadget was decided `false` under 46 of 60 random namings and refused with
/// `Refusal::Unordered` under 14 (seed 2; 41 and 19 at seed 4), before and after 5213e08d6
/// (PROOF-settle-marks-naming-free). The projections are now made over names given by the
/// structure ([`stage_kernels`] in the library). A new seed each run (author P169).
#[test]
fn a_tied_formula_settled_with_projections_gives_one_answer_under_every_naming() {
    let (n, chain) = a_chain_and_a_choice_with_no_point();
    let sys = beside_the_tied_gadget(n, &chain);
    let n = n + 12;
    let (mut rng, seed) = Rng::fresh("namings of a chain beside a tied gadget");
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    for r in 0..24 {
        let perm: Vec<usize> = if r == 0 {
            (0..n).collect()
        } else {
            shuffled(&mut rng, n)
        };
        let f = disjunctive_formula(&sys, &perm);
        let found = match satisfiable(&f) {
            Ok(Some(m)) => panic!("a point of a system with none: {m:?}"),
            Ok(None) => "no point",
            // Its kind alone: the variables it names change with the naming.
            Err(Refusal::Unordered(_)) => "Unordered",
            Err(Refusal::Tie(_)) => "Tie",
            Err(_) => "another refusal",
        };
        *seen.entry(format!("{} / {found}", answer(&f))).or_insert(0) += 1;
    }
    // The chain's component has no two atoms of one color, so its projection is made over the
    // names its structure gives; the solver refuses that projection (Growth), as it refused
    // the projections of 14 namings in 60 before, and the rows linked to the disjuncts, so the
    // formula is refused under every naming. `false` is the true answer: the refusal is the
    // cost of answering alike (PROOF-settle-marks-naming-free).
    assert_eq!(
        seen.keys().collect::<Vec<_>>(),
        ["Err(Unordered, 12 variables, 12 disjunctions) / Unordered"],
        "seed {seed}: {seen:?}"
    );
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

/// System 6 of seed 16475671021983193007, under `disjunctions_whose_atoms_share_a_color`: its
/// layer holds `t >= 0` beside `-t >= 0` for a `t` like `a - b`, which `decide` joins into the
/// equation `t == 0` (FAIL-rewrite-growth-both). Written with the sign of the first name, as
/// project_each writes such an equation, it gave `true` under 12 of the 24 namings and
/// `Refusal::Unordered` under the others; `decide` now holds such an equation with both signs.
#[test]
fn a_joined_equation_whose_sign_only_the_names_choose_gives_one_answer() {
    let mut rng = Rng::new(16475671021983193007);
    let differ = name_dependent(
        &mut rng,
        4,
        7,
        |s| s == 6,
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

/// [`pigeons`] with the tasks joined in a ring by `t[(i + 1) % n] <= t[i] + 2`, which the
/// bounds imply: the tasks still occur alike, but swapping two of them moves the ring's rows.
fn pigeons_in_a_ring(n: usize, slots: i64) -> Formula {
    let v = |i: usize| -> Lin { Lin::atom(Atom::Sym(format!("t{i}").into())) };
    let mut fs = vec![pigeons(n, slots)];
    for i in 0..n {
        fs.push(Formula::Con(Con::ge(
            &v(i).plus(&Lin::constant(2)),
            &v((i + 1) % n),
        )));
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
    // any choice is made. With `1 <= x + y` as well that point is excluded; the choice by
    // color has no point, but swapping `x` and `y` maps the formula onto itself, so they are
    // ranked by name and searched, which finds `x == 1 && y == 0` (before plan row
    // FAIL-or-if-tie-refusal the formula was refused).
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
    assert_eq!(decide(&not_both_zero), Ok(true));
    let m = satisfiable(&not_both_zero).unwrap().expect("a point");
    assert!(not_both_zero.holds(&m), "{m:?}");
    // Tasks in slots, each pair apart: the two disjuncts of `t0 <= t1 - 1 || t0 >= t1 + 1`
    // differ only by which task is first, so they tie, and the disjunctions are linked through
    // the tasks. Every swap of two tasks maps the formula onto itself, so it is searched
    // (`a_tie_that_every_swap_maps_onto_itself_is_renamed`); joined in a ring by
    // `t[i+1] <= t[i] + 2`, which the bounds imply, a swap moves the ring's rows, and three
    // tasks in two slots, which have no point, are refused like four in three, the message
    // naming the tied tasks and the disjunctions left
    // (`omega::each_cause_of_a_refusal_has_its_own_message` reads it whole).
    for (n, slots, pairs) in [(3, 2, 3), (4, 3, 6)] {
        let Err(Refusal::Unordered(t)) = decide(&pigeons_in_a_ring(n, slots)) else {
            panic!("{n} tied tasks in a ring in {slots} slots are refused");
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

/// `n` gadgets in a chain: links `w0..wn` and, for gadget `i`, `x{i}_0..x{i}_{m-1}`, each in
/// `[0, 10]`, with `1 <= w_i - w_{i+1} + Σ x{i}_j <= 3`. The gadgets are alike, so the
/// shrinking stage of the Omega test ties again and again: 15 ties for the 31 variables of 6
/// gadgets (`tie_group_tests::counts_read_at_a_tie_are_those_of_the_rows_held` in
/// zedc-presburger), O(n) ties for n gadgets (PERF-shrink-tie-every-step).
pub(super) fn gadget_chain(n: usize, m: usize) -> Formula {
    let v = |s: String| -> Lin { Lin::atom(Atom::Sym(s.into())) };
    let k = Lin::constant;
    let mut fs = Vec::new();
    let bound = |x: &Lin, fs: &mut Vec<Formula>| {
        fs.push(Formula::Con(Con::ge(x, &k(0))));
        fs.push(Formula::Con(Con::ge(&k(10), x)));
    };
    for i in 0..=n {
        bound(&v(format!("w{i}")), &mut fs);
    }
    for i in 0..n {
        let mut sum = v(format!("w{i}")).plus(&v(format!("w{}", i + 1)).times(-1));
        for j in 0..m {
            let x = v(format!("x{i}_{j}"));
            bound(&x, &mut fs);
            sum = sum.plus(&x);
        }
        fs.push(Formula::Con(Con::ge(&sum, &k(1))));
        fs.push(Formula::Con(Con::ge(&k(3), &sum)));
    }
    Formula::and(fs)
}

/// `x` and `y` each in `[-6, -1]` or in `[1, 6]`, and `x == at || y == at`, the atoms named
/// `names`. With `at` zero it is the question of exactness of `if x == 0 { true } else { x ==
/// x - y }` read as `||` (`zedc_preimage`, seed 3178640468583431682 round 104, plan row
/// FAIL-or-if-tie-refusal). Swapping `x` and `y` maps the formula onto itself.
fn either_at(at: i64, names: [&str; 2]) -> Formula {
    let v = |s: &str| Lin::atom(Atom::Sym(s.into()));
    let k = Lin::constant;
    let mut fs = Vec::new();
    for s in names {
        let within = |lo: i64, hi: i64| {
            Formula::and(vec![
                Formula::Con(Con::ge(&v(s), &k(lo))),
                Formula::Con(Con::ge(&k(hi), &v(s))),
            ])
        };
        fs.push(Formula::or(vec![within(-6, -1), within(1, 6)]));
    }
    let at = names.iter().map(|s| Formula::Con(Con::eq(&v(s), &k(at))));
    fs.push(Formula::or(at.collect()));
    Formula::and(fs)
}

/// Two triangles and a hexagon over `v0..v11`, each variable in `[0, 2]` and at `0` or at
/// `2`, the two ends of each edge summing to at most 3: every variable has two edges, so color
/// refinement gives all twelve one color, but swapping a variable of a triangle with one of
/// the hexagon does not map the formula onto itself.
fn triangles_and_a_hexagon() -> Disjunctive {
    let n = 12;
    let unit = |i: usize, s: i64| {
        let mut c = vec![0; n];
        c[i] = s;
        c
    };
    let mut base = Vec::new();
    let edges = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
        .into_iter()
        .chain((0..6).map(|i| (6 + i, 6 + (i + 1) % 6)));
    for (i, j) in edges {
        let mut c = vec![0; n];
        c[i] = -1;
        c[j] = -1;
        base.push(ge(&c, 3));
    }
    let mut ors = Vec::new();
    for i in 0..n {
        base.push(ge(&unit(i, 1), 0));
        base.push(ge(&unit(i, -1), 2));
        ors.push(vec![vec![ge(&unit(i, -1), 0)], vec![ge(&unit(i, 1), -2)]]);
    }
    (base, ors)
}

#[test]
fn a_tie_that_every_swap_maps_onto_itself_is_renamed() {
    // `x` and `y` share a color, but every permutation of the two maps the formula onto
    // itself, so ranking them by name renames every naming to one formula, which is searched:
    // before, each of these was refused with `Refusal::Unordered`.
    for names in [["x", "y"], ["y", "x"]] {
        assert_eq!(decide(&either_at(0, names)), Ok(false), "{names:?}");
        assert_eq!(decide(&either_at(1, names)), Ok(true), "{names:?}");
        let f = either_at(-6, names);
        let m = satisfiable(&f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
    }
    // Every permutation of the tasks maps `pigeons` onto itself: `n` tasks fit in `slots`
    // slots, each pair apart, exactly when `n <= slots`. Four tasks in three slots are refused
    // by the search, as the tasks joined in a chain are, which no naming orders
    // (`omega::each_cause_of_a_refusal_has_its_own_message`): the search shows no choice
    // empty by propagation, and refusing is the cost of the pigeonhole, not of the names.
    for (n, slots) in [(3, 2), (3, 3), (4, 3), (4, 4)] {
        let want = if (n, slots) == (4, 3) {
            Err(Refusal::Disjuncts)
        } else {
            Ok(n as i64 <= slots)
        };
        assert_eq!(
            decide(&pigeons(n, slots)),
            want,
            "{n} tasks in {slots} slots"
        );
        let want = want == Ok(true);
        if want {
            let f = pigeons(n, slots);
            let m = satisfiable(&f).unwrap().expect("a point");
            assert!(f.holds(&m), "{m:?}");
        }
    }
    // A tie that a swap does not map onto itself is settled as before, with one answer under
    // every naming tried: all twelve at 0 is a point.
    let sys = triangles_and_a_hexagon();
    let mut seen = std::collections::BTreeSet::new();
    for r in 0..12 {
        let rotated: Vec<usize> = (0..12).map(|i| (i + r) % 12).collect();
        let reversed: Vec<usize> = (0..12).map(|i| (12 + r - i) % 12).collect();
        seen.insert(answer(&disjunctive_formula(&sys, &rotated)));
        seen.insert(answer(&disjunctive_formula(&sys, &reversed)));
    }
    assert_eq!(seen.into_iter().collect::<Vec<_>>(), ["Ok(true)"]);
}

#[test]
fn a_refusal_of_a_renamed_formula_names_the_variables_as_written() {
    // The doubled cycle ([`doubled_cycle`]) ties under every naming, and a disjunction tells
    // its variables apart, so the formula is renamed; the refusal of the cycle is written over
    // the names given.
    let sys: Disjunctive = (
        doubled_cycle(),
        vec![vec![
            vec![ge(&[1, -1, 0, 0, 0, 0], 1000)],
            vec![ge(&[0, 0, 1, -2, 0, 0], 1000)],
        ]],
    );
    let got = decide(&disjunctive_formula(&sys, &[0, 1, 2, 3, 4, 5]));
    let Err(Refusal::Tie(t)) = got else {
        panic!("the doubled cycle is refused with a tie: {got:?}");
    };
    let mut vars = t.vars.clone();
    vars.sort();
    assert_eq!(vars, ["v0", "v1", "v2", "v3", "v4", "v5"]);
    let message = Refusal::Tie(t).to_string();
    assert!(!message.contains('#'), "{message}");
    assert!(message.contains("10 >= 0"), "{message}");
    assert_eq!(
        answers_under_every_naming(&sys, 6),
        ["Err(Tie, 6 variables)"]
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

/// The tied doubled cycle ([`doubled_cycle`]) with every variable at most `top`, variable `i`
/// named `v{name[i]}`. Summing its rows gives `4·Σ x >= 120`, so with `top <= 4`, where
/// `Σ x <= 24`, it has no point; the solver refuses it for its tie.
fn capped_cycle(top: i64, name: &[usize]) -> Formula {
    let mut rows = doubled_cycle();
    for i in 0..6 {
        let mut c = vec![0; 6];
        c[i] = -1;
        rows.push(ge(&c, top));
    }
    formula(&rows, name)
}

#[test]
fn a_disjunct_the_solver_refuses_is_not_taken_for_a_point() {
    // `(C && x <= 4) || (C && x <= 3)`, `C` the doubled cycle: neither disjunct has a point,
    // and the solver refuses both, so settling removes neither. The answer must not be `true`
    // (verifier of NAME-ties repair 3 found `decide` gave `Ok(true)` while `satisfiable`
    // refused): it is refused, by `decide` and `satisfiable` alike, under every naming.
    let mut seen = BTreeMap::new();
    each_permutation(6, |perm| {
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
    // `y` in `[0, 9]` and `(C && x <= 3) || (1 <= y <= 2)`, `C` the doubled cycle: the second
    // disjunct has a point and the first is refused. The disjunction is linked to no other, so
    // the formula has a point, under every naming of the cycle and whether `y` sorts before or
    // after it; `satisfiable` must not take the refused disjunct because its name comes first.
    for y in ["a", "z"] {
        let v = Lin::atom(Atom::Sym(y.into()));
        let k = Lin::constant;
        let mut seen = BTreeMap::new();
        each_permutation(6, |perm| {
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

/// A chain of `ifs`, as the preimage asks it: for each `j` from 1, `(b[j] >= 1 && q[j - 1] ==
/// q[j]) || (!(b[j] >= 1) && q[j - 1] == q[j] - c[j])` with `b[j]` in `[0, 1]`, `q[0]` one of
/// `zs` (a disjunction), and the demand `q[n] == 0` when `last_is_0`, else `!(q[n] == 0)`.
pub(super) fn guarded_steps(c: &[i64], zs: &[i64], last_is_0: bool) -> Formula {
    let v = |s: &str, j: usize| Lin::atom(Atom::Sym(format!("{s}{j}").into()));
    let k = Lin::constant;
    let con = Formula::Con;
    let mut fs = Vec::with_capacity(3 * c.len() + 2);
    for (j, &cj) in (1..).zip(c) {
        let (b, before, after) = (v("b", j), v("q", j - 1), v("q", j));
        let then = con(Con::ge(&b, &k(1)));
        fs.push(Formula::or(vec![
            Formula::and(vec![then.clone(), con(Con::eq(&before, &after))]),
            Formula::and(vec![
                Formula::negate(then),
                con(Con::eq(&before, &after.plus(&k(-cj)))),
            ]),
        ]));
        fs.push(con(Con::ge(&b, &k(0))));
        fs.push(con(Con::ge(&k(1), &b)));
    }
    let q0_is = |z: &i64| con(Con::eq(&v("q", 0), &k(*z)));
    fs.push(Formula::or(zs.iter().map(q0_is).collect()));
    let last = con(Con::eq(&v("q", c.len()), &k(0)));
    fs.push(if last_is_0 {
        last
    } else {
        Formula::negate(last)
    });
    Formula::and(fs)
}

/// The relation of `t1 = if b1 >= 1 { z } else { z + 2 }; if b2 >= 1 { t1 } else { t1 + 4 }`
/// with `z` (`q0`) one of -6, -4, -2 and 0, as the preimage asks it ([`guarded_steps`] of
/// 2 and 4), under `!(q2 == 0)` (has the demand a miss?) and under `q2 == 0`. The rows of
/// `b1` and of `b2` are alike, so color refinement over the rows ties the two, and with the
/// four values of `q0` written as a disjunction the tie stayed after settling and merging;
/// it was refused as `Unordered` (PREIMAGE-tie-indep-let). The rows beside the guards differ
/// (constants 2 and 4, and their places in the chain), the nesting tells the two apart, and
/// `decide` and `satisfiable` answer both: a miss (`q0 == -6` with both then arms gives
/// `q2 == -6`) and a point of the demand (`q0 == 0` with both then arms).
#[test]
fn guards_alike_as_rows_are_told_apart_by_their_nesting() {
    for last_is_0 in [false, true] {
        let f = guarded_steps(&[2, 4], &[-6, -4, -2, 0], last_is_0);
        assert_eq!(decide(&f), Ok(true), "{f}");
        let m = satisfiable(&f).expect("not refused").expect("a point");
        assert!(f.holds(&m), "{m:?}");
    }
}

/// `(if g0 > 0 { 2 } else { 0 }) + ... + (if g[n-1] > 0 { 2 } else { 0 }) != k` as the
/// preimage asks it, or `== k` when `!holds`: for each `i`, `(g[i] <= 0 && q[i] == 0) ||
/// (g[i] >= 1 && q[i] == 2)`, beside `!(Σ q[i] == k)`. The atom `g[i]` is named `v{name[i]}`
/// and `q[i]` is named `v{name[n + i]}`. Exchanging `g[i]` with `g[j]` maps the formula onto
/// itself only together with `q[i]` and `q[j]`, so the ties of the `g` and of the `q` are
/// symmetries jointly and not one at a time (FAIL-tie-sum-ne-constant-refused).
pub(super) fn tie_sum(n: usize, k: i64, holds: bool, name: &[usize]) -> Formula {
    let v = |i: usize| Lin::atom(Atom::Sym(format!("v{}", name[i]).into()));
    let c = Lin::constant;
    let con = Formula::Con;
    let mut fs = Vec::with_capacity(n + 1);
    let sum = (0..n).fold(c(0), |s, i| s.plus(&v(n + i)));
    let e = con(Con::eq(&sum, &c(k)));
    fs.push(if holds { Formula::negate(e) } else { e });
    for i in 0..n {
        let (g, q) = (v(i), v(n + i));
        fs.push(Formula::or(vec![
            Formula::and(vec![con(Con::ge(&c(0), &g)), con(Con::eq(&q, &c(0)))]),
            Formula::and(vec![con(Con::ge(&g, &c(1))), con(Con::eq(&q, &c(2)))]),
        ]));
    }
    Formula::and(fs)
}

/// A sum of two or three conditionals of 0 or 2 compared with each `k` (FAIL-tie-sum-ne-
/// constant-refused, FAIL-ladder-rung2-front-disagree): before, only the questions that the
/// disjuncts of least color answered were decided (`!= 1`, `!= 2`, `!= 3` of two), and the
/// rest were refused as `Unordered`. Each is now decided under every naming of its atoms (all
/// 24 of two conditionals, 200 random ones of three), with the true answer: the sum takes
/// the even values `0..=2n`, so `== k` has a point exactly for those, and `!= k` always has
/// one; each point `satisfiable` gives is one.
#[test]
fn a_sum_of_conditionals_tied_jointly_is_decided_for_every_constant() {
    let mut rng = Rng::new(0x7e5u64);
    for n in [2, 3] {
        for k in -1..=2 * n as i64 + 2 {
            for holds in [true, false] {
                let want = holds || (k >= 0 && k <= 2 * n as i64 && k % 2 == 0);
                let check = |name: &[usize]| {
                    let f = tie_sum(n, k, holds, name);
                    assert_eq!(decide(&f), Ok(want), "{f}");
                    let m = satisfiable(&f).unwrap_or_else(|e| panic!("{f}: {e}"));
                    assert_eq!(m.is_some(), want, "{f}");
                    if let Some(m) = m {
                        assert!(f.holds(&m), "{f}: {m:?}");
                    }
                };
                if n == 2 {
                    each_permutation(2 * n, |p| check(p));
                } else {
                    check(&(0..2 * n).collect::<Vec<_>>());
                    for _ in 0..200 {
                        check(&shuffled(&mut rng, 2 * n));
                    }
                }
            }
        }
    }
}

/// The cycle `v_i + 20 >= v_(i+1)` over `v0` to `v3` with `v0 + v1 + v2 + v3 >= 20` as the base,
/// and one disjunction of `k` disjuncts, the `j`-th the cycle's rows and `u_j >= 0`. Each
/// disjunct holds at the base's point, where `settle_as_sets` once marked it proven with no
/// solve; it is now tested like any other (FAIL-omega-alone-retry-scaling,
/// FAIL-alone-point-refused-at-model, FAIL-settle-proven-marks-names).
pub(super) fn disjuncts_a_solve_refuses(k: usize) -> Formula {
    let c = Lin::constant;
    let v: Vec<Lin> = (0..4)
        .map(|i| Lin::atom(Atom::Sym(format!("v{i}").into())))
        .collect();
    let sum = v.iter().fold(c(0), |s, x| s.plus(x));
    let cyc: Vec<Formula> = (0..4)
        .map(|i| Formula::Con(Con::ge(&v[i].plus(&c(20)), &v[(i + 1) % 4])))
        .collect();
    let ds = (0..k)
        .map(|j| {
            let u = Lin::atom(Atom::Sym(format!("u{j}").into()));
            let mut d = cyc.clone();
            d.push(Formula::Con(Con::ge(&u, &c(0))));
            Formula::and(d)
        })
        .collect();
    Formula::and(vec![Formula::Con(Con::ge(&sum, &c(20))), Formula::or(ds)])
}

/// FAIL-alone-point-refused-at-model: (5, 5, 5, 5) with every `u_j = 0` is a point of
/// [`disjuncts_a_solve_refuses`], and `decide` and `satisfiable` agree at every `k`. Before,
/// `satisfiable` refused with a tie on `v0` to `v3` at every `k`, and `decide` at `k = 1`.
#[test]
fn a_disjunction_decide_proves_has_a_point() {
    for k in [1, 2, 3] {
        let f = disjuncts_a_solve_refuses(k);
        assert_eq!(decide(&f), Ok(true), "k = {k}");
        let m = satisfiable(&f).unwrap().expect("a point");
        assert!(f.holds(&m), "k = {k}: {m:?}");
    }
}

/// FAIL-settle-proven-marks-names: `settle_as_sets` marked a disjunct proven with no solve
/// when it held at the point `solve` found for the base, and that point depends on the names,
/// so a disjunct `solve` refuses could be marked under one naming and not under another, and
/// `decide` answer under one and refuse under the other. Every disjunct is now tested. Each
/// disjunct of [`disjuncts_a_solve_refuses`] holds at the base's point; under all 24 namings of
/// `v0` to `v3`, with the `u_j` named in either order, `decide` and `satisfiable` give one
/// answer. No formula was found on which the marks differed before the change (seeds 4,000 to
/// 11,999 of `one_variable_boundary_modes_do_not_depend_on_names` and the probes of the plan
/// row), and this test passed before it too.
#[test]
fn a_disjunct_proven_at_the_base_point_gives_one_answer_in_every_naming() {
    for k in [1, 2, 3] {
        let f = disjuncts_a_solve_refuses(k);
        each_permutation(4, |p| {
            for reversed in [false, true] {
                let g = f.map_cons(&|c: &Con| {
                    let mut lin = Lin::constant(c.lin.constant.clone());
                    for (a, n) in &c.lin.terms {
                        let s = a.to_string();
                        let i: usize = s[1..].parse().unwrap();
                        let name = match (&s[..1], reversed) {
                            ("v", _) => format!("v{}", p[i]),
                            (_, false) => format!("u{i}"),
                            (_, true) => format!("u{}", k - 1 - i),
                        };
                        lin = lin.plus(&Lin::atom(Atom::Sym(name.into())).times(n.clone()));
                    }
                    Formula::Con(Con { lin, rel: c.rel })
                });
                assert_eq!(decide(&g), Ok(true), "{g}");
                let m = satisfiable(&g)
                    .unwrap_or_else(|e| panic!("{g}: {e}"))
                    .expect("a point");
                assert!(g.holds(&m), "{g}: {m:?}");
            }
        });
    }
}

/// The base and one disjunct of [`disjuncts_a_solve_refuses`] with no disjunction: the sum and
/// the 4-cycle, each variable tied to the others by a rotation of the rows, under every
/// naming of its four variables (FAIL-alone-point-refused-at-model).
#[test]
fn a_sum_over_a_cycle_of_differences_has_a_point_in_every_naming() {
    // Rows over v0..v3: the sum >= 20 and v_i - v_(i+1) + 20 >= 0.
    let mut rows = vec![ge(&[1, 1, 1, 1], -20)];
    for i in 0..4 {
        let mut c = vec![0; 4];
        c[i] = 1;
        c[(i + 1) % 4] = -1;
        rows.push(ge(&c, 20));
    }
    each_permutation(4, |p| {
        let f = formula(&rows, p);
        assert_eq!(decide(&f), Ok(true), "{f}");
        let m = satisfiable(&f)
            .unwrap_or_else(|e| panic!("{f}: {e}"))
            .expect("a point");
        assert!(f.holds(&m), "{f}: {m:?}");
    });
}

/// Two copies of [`a_chain_and_a_choice_with_no_point`], the second over variables `n..2n`,
/// each with its disjunction, joined by the disjunction
/// `v[a] - v[n+a] >= k || v[n+a] - v[a] >= k`, which a swap of the copies maps onto itself, so
/// that each atom shares its color with its copy. At `k <= 0` the joining disjunction always
/// holds and settling drops it, which leaves two components, each untied, that a coloring
/// renames alike; at `k > 0` it stays, and the whole is one tied component. Either way the
/// formula has no point (each copy has none, checked by z3 on the integers and on the reals).
fn two_chains_or(a: usize, k: i64) -> (usize, Disjunctive) {
    let (n, (rows, ors)) = a_chain_and_a_choice_with_no_point();
    let widen = |r: &Row, at: usize| {
        let mut c = vec![0; 2 * n];
        c[at..at + n].copy_from_slice(&r.c);
        Row {
            c,
            k: r.k,
            eq: r.eq,
        }
    };
    let mut base: Vec<Row> = Vec::new();
    let mut all_ors = Vec::new();
    for at in [0, n] {
        base.extend(rows.iter().map(|r| widen(r, at)));
        all_ors.extend((ors.iter()).map(|ds| {
            (ds.iter())
                .map(|d| d.iter().map(|r| widen(r, at)).collect())
                .collect::<Vec<Vec<Row>>>()
        }));
    }
    let side = |p: usize, q: usize| {
        let mut c = vec![0; 2 * n];
        c[p] = 1;
        c[q] = -1;
        vec![ge(&c, -k)]
    };
    all_ors.push(vec![side(a, n + a), side(n + a, a)]);
    (2 * n, (base, all_ors))
}

/// [`two_chains_or`], which has no point, is never decided `true` nor given a point, under
/// random namings. Before FAIL-stage-kernels-shared-back, at `k == 0` the two copies, each
/// untied and colored alike, got the same new names in `stage_kernels`, whose one map back to
/// the old names put atoms of one copy into the other's projection: the projection then had
/// points the base has not, each disjunct was marked proven, and `decide` answered `true`
/// under about half the namings (17 to 23 of 40). The answers may still differ by a refusal
/// at `k > 0`, where the copies form one tied component projected over its names as given
/// (PROOF-tied-projection-refusal-names), so only a wrong answer is asserted against.
#[test]
fn two_copies_of_a_chain_with_no_point_are_never_decided_true() {
    let (mut rng, seed) = Rng::fresh("two copies of a chain with no point");
    for a in [0, 4, 5, 8] {
        for k in [0, 1, 3] {
            let (n, sys) = two_chains_or(a, k);
            for _ in 0..10 {
                let perm = shuffled(&mut rng, n);
                let f = disjunctive_formula(&sys, &perm);
                let decided = decide(&f);
                assert!(
                    !matches!(decided, Ok(true)),
                    "seed {seed}, a {a}, k {k}: {f}"
                );
                let found = satisfiable(&f);
                assert!(
                    !matches!(found, Ok(Some(_))),
                    "seed {seed}, a {a}, k {k}: {found:?} for {f}"
                );
            }
        }
    }
}

/// A refusal written without the names it gives, which a renaming changes.
fn refusal_kind(e: &Refusal) -> String {
    match e {
        Refusal::Tie(_) => "Tie".into(),
        Refusal::Unordered(_) => "Unordered".into(),
        e => format!("{e:?}"),
    }
}

/// The projections of `rows` onto each variable, by place, with variable `i` named
/// `v{name[i]}`, and the causes of the disjunctions left out; refusals without their names.
fn projections(rows: &[Row], name: &[usize]) -> String {
    let f = formula(rows, name);
    let syms: Vec<Atom> = (name.iter())
        .map(|k| Atom::Sym(Arc::from(format!("v{k}"))))
        .collect();
    match project_each(&f, &syms) {
        Ok((sets, causes)) => {
            let sets: Vec<String> = (sets.iter())
                .map(|s| match s {
                    Ok(s) => format!("{s:?}"),
                    Err(e) => refusal_kind(e),
                })
                .collect();
            let causes: Vec<String> = causes.iter().map(refusal_kind).collect();
            format!("{sets:?} {causes:?}")
        }
        Err(e) => refusal_kind(&e),
    }
}

/// `n` variables in the box `-half..=half` and two to five rows, each over two to four of
/// them with coefficients in `-9..=9` and a constant in `-30..=30`, an equation one time in
/// four.
fn random_conjunction(rng: &mut Rng, n: usize) -> Vec<Row> {
    let m = 2 + rng.below(4);
    let rows: Vec<Row> = (0..m)
        .map(|_| {
            let mut c = vec![0; n];
            for _ in 0..2 + rng.below(3) {
                c[rng.below(n)] = rng.int(-9, 9);
            }
            let k = rng.int(-30, 30);
            if rng.below(4) == 0 {
                eq(&c, k)
            } else {
                ge(&c, k)
            }
        })
        .collect();
    let half = rng.int(5, 40);
    with_box(&rows, n, half)
}

/// The answers of `rows` (over `n` variables) under the naming as written and `count` random
/// namings from `rng`.
fn projected_namings(
    rows: &[Row],
    n: usize,
    rng: &mut Rng,
    count: usize,
) -> std::collections::BTreeSet<String> {
    let perms = std::iter::once((0..n).collect()).chain((0..count).map(|_| shuffled(rng, n)));
    perms.map(|p: Vec<usize>| projections(rows, &p)).collect()
}

/// System 909 of seed 1 of [`random_conjunction`] (PRES-project-each-naming): five variables
/// in `-7..=7`, no disjunction. Asked under its own names, as `project_each` asked every
/// formula with no disjunction before, its namings got two answers: `v3` came out
/// `-2..=0, 3..=5, 7` under the names as written and was refused (`Questions`) under others,
/// since the solver orders rows and symbols by name where nothing else orders them and the
/// Omega test refuses some orders of elimination where it decides others. Each question is
/// now renamed by its structure first, so every naming gets one answer, and each set answered
/// is the one brute force finds over the box. The control (`NAMES_AS_WRITTEN`) asks under the
/// names given and still gets two answers, so the test can fail.
#[test]
fn every_naming_of_a_conjunction_gets_one_projection() {
    use zedc::store::presburger::NAMES_AS_WRITTEN;
    let rows = with_box(
        &[
            ge(&[0, 8, 0, 0, -7], 30),
            ge(&[0, -4, -3, 0, 1], -13),
            ge(&[-8, 0, 0, 0, 9], -16),
            eq(&[-9, 0, 4, -8, 0], 30),
        ],
        5,
        7,
    );
    let namings: [[usize; 5]; 5] = [
        [0, 1, 2, 3, 4],
        [1, 3, 4, 0, 2],
        [2, 0, 4, 3, 1],
        [4, 0, 3, 1, 2],
        [4, 1, 0, 3, 2],
    ];
    let answers = |as_written: bool| {
        NAMES_AS_WRITTEN.with(|c| c.set(as_written));
        let seen: std::collections::BTreeSet<String> =
            namings.iter().map(|p| projections(&rows, p)).collect();
        NAMES_AS_WRITTEN.with(|c| c.set(false));
        seen
    };
    assert_eq!(answers(true).len(), 2, "the control: {:?}", answers(true));
    assert_eq!(answers(false).len(), 1, "{:?}", answers(false));
    // Each set answered is the set of values over the points of the box.
    let f = formula(&rows, &[0, 1, 2, 3, 4]);
    let syms: Vec<Atom> = (0..5)
        .map(|i| Atom::Sym(Arc::from(format!("v{i}"))))
        .collect();
    let (sets, _) = project_each(&f, &syms).expect("answered");
    let mut want = vec![std::collections::BTreeSet::new(); 5];
    let mut p = [-7i64; 5];
    loop {
        if holds(&rows, &p) {
            for (w, x) in want.iter_mut().zip(p) {
                w.insert(x);
            }
        }
        let Some(i) = (0..5).find(|&i| p[i] < 7) else {
            break;
        };
        p[i] += 1;
        p[..i].fill(-7);
    }
    for (i, (s, w)) in sets.iter().zip(&want).enumerate() {
        if let Ok(s) = s {
            let got: std::collections::BTreeSet<i64> = (-8..=8)
                .filter(|&x| s.contains_end(&End::Fin(Num::from(x))))
                .collect();
            assert_eq!(&got, w, "v{i}: {s:?}");
        }
    }
}

/// [`random_conjunction`]s at a fresh seed, each under the naming as written and four random
/// ones: one answer each (PRES-project-each-naming). Asked under their own names, 6 of the
/// first 1,151 systems of seed 1 got two answers; renamed, none of 4,000 did (2026-11-20).
#[test]
fn every_naming_of_a_random_conjunction_gets_one_projection() {
    let (mut rng, seed) = Rng::fresh("every naming of a random conjunction");
    for s in 0..100 {
        let n = 3 + rng.below(3);
        let rows = random_conjunction(&mut rng, n);
        let seen = projected_namings(&rows, n, &mut rng, 4);
        assert_eq!(seen.len(), 1, "seed {seed}, system {s}: {rows:?}\n{seen:?}");
    }
}
