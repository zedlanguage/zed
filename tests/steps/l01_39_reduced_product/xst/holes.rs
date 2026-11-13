//! `Scope` on names with holes linked by difference tests, against enumeration (META4 result
//! 1, META3 tests of Claude, Codex and Gemini). A name's values are its range less its holes;
//! an edge `(u, v, w)` is the test `x_v - x_u <= w`. The exact answer is each name's values
//! over every point that meets all the tests.
//!
//! Main's ends (least and greatest kept value) are exact on every named system in every
//! order; its interior sets are not exact on CE-B (it keeps `a = 4`) and the collective
//! example (it keeps `z = 4`), and it takes superlinear time on laps and the mixed family.
//! Those tests wait for ST-holes-moves.

use zed_kernel::Value;
use zed_tests::scaling;

use super::{Inst, Lcg, ends, nm, permutations, rotations};

/// CE-A: `a` in `4..=6`, `b` in `{4, 6}`, `c` in `{2, 4}`, `c - b <= -2`, `a - c <= 2`,
/// `b - a <= 0`. The solutions are `(4, 4, 2)` and `(6, 6, 4)`.
fn ce_a() -> Inst {
    Inst {
        range: vec![(4, 6), (4, 6), (2, 4)],
        out: vec![vec![], vec![5], vec![3]],
        edges: vec![(1, 2, -2), (2, 0, 2), (0, 1, 0)],
    }
}

/// CE-B: `a` in `3..=5`, `b` in `{5, 7}`, `c` in `{6, 8}`, `b - c <= 0`, `c - a <= 3`,
/// `a - b <= -2`. The solutions are `(3, 5, 6)` and `(5, 7, 8)`, so `a = 4` is out, though
/// neither hole alone leaves it out.
fn ce_b() -> Inst {
    Inst {
        range: vec![(3, 5), (5, 7), (6, 8)],
        out: vec![vec![], vec![6], vec![7]],
        edges: vec![(2, 1, 0), (0, 2, 3), (1, 0, -2)],
    }
}

/// The collective example: `x`, `y`, `z` in `0..=6`, `z <= y <= x <= z + 1`, `x != 5`,
/// `y != 4`. Every `z` but 4 has a solution.
fn collective() -> Inst {
    Inst {
        range: vec![(0, 6), (0, 6), (0, 6)],
        out: vec![vec![5], vec![4], vec![]],
        edges: vec![(1, 2, 0), (0, 1, 0), (2, 0, 1)],
    }
}

/// Codex's HeapInvariant system (round 4, `work/r4/src/main.rs`): a cycle of four names, three
/// with holes, whose greatest solution is `(4, 7, 6, 3)`.
fn heap() -> Inst {
    Inst {
        range: vec![(0, 7), (1, 7), (3, 6), (0, 7)],
        out: vec![vec![1, 5], vec![4], vec![], vec![4, 5]],
        edges: vec![(0, 1, 3), (1, 2, -1), (2, 3, -1), (3, 0, 1)],
    }
}

/// The orders tried for `inst`: every order when it has at most six tests, else every
/// rotation of its tests and of their reverse.
fn orders(inst: &Inst) -> Vec<Vec<usize>> {
    let k = inst.tests().1.len();
    if k <= 6 {
        permutations(k)
    } else {
        rotations(k)
    }
}

/// Asserts that `inst`'s scope has exact ends in each of [`orders`] and as one conjunction,
/// and, with `sets`, that each name's whole set is exact. CONTROL: the hull of the ranges
/// differs from the exact answer, so the check can fail.
fn check_named(what: &str, inst: &Inst, sets: bool) {
    let want = inst.exact();
    if sets {
        assert_ne!(inst.hull(), want, "{what}: CONTROL, the hull is exact");
    }
    let mut runs: Vec<(String, Vec<Vec<i64>>)> = orders(inst)
        .into_iter()
        .map(|o| (format!("{o:?}"), inst.values(&inst.in_order(&o))))
        .collect();
    runs.push(("one conjunction".into(), inst.values(&inst.at_once())));
    for (order, got) in runs {
        assert_eq!(ends(&got), ends(&want), "{what}, order {order}: ends");
        if sets {
            assert_eq!(got, want, "{what}, order {order}: sets");
        }
    }
}

/// Claude round 4 (`probe_r4_holes.rs`), Codex round 3 (`holes.mjs`) and round 4 (named
/// systems), Gemini rounds 3 and 4 (`q1_holes_probe.rs`, `q1_holes_r4.rs`): main's ends are
/// exact on the named systems in every order.
#[test]
fn named_systems_have_exact_ends_in_every_order() {
    for (what, inst) in [
        ("CE-A", ce_a()),
        ("CE-B", ce_b()),
        ("collective", collective()),
        ("HeapInvariant", heap()),
    ] {
        check_named(what, &inst, false);
    }
    assert_eq!(
        ends(&heap().exact())
            .iter()
            .map(|e| e.map(|e| e.1))
            .collect::<Vec<_>>(),
        [Some(4), Some(7), Some(6), Some(3)],
        "Codex's greatest solution of HeapInvariant"
    );
}

/// CE-A's sets are exact in all 120 orders (`a` in `{4, 6}`, `b` in `{4, 6}`, `c` in
/// `{2, 4}`).
#[test]
fn ce_a_sets_are_exact_in_every_order() {
    check_named("CE-A", &ce_a(), true);
}

/// HeapInvariant's sets are exact in every rotation of its tests.
#[test]
fn heap_invariant_sets_are_exact_in_every_rotation() {
    check_named("HeapInvariant", &heap(), true);
}

/// CE-B: `a` in `{3, 5}` in all 120 orders. Main keeps `a = 4` (COMPLEXITY.md S25).
#[test]
fn ce_b_sets_are_exact_in_every_order() {
    assert_eq!(ce_b().exact()[0], [3, 5]);
    check_named("CE-B", &ce_b(), true);
}

/// The collective example: `z` in `{0, 1, 2, 3, 5, 6}` in all 120 orders. Main keeps `z = 4`
/// (COMPLEXITY.md S25).
#[test]
#[ignore = "HOLES-exact-between: needs exact values between the ends (cross-review xst O4); ST-holes-moves gives exact ends only"]
fn collective_sets_are_exact_in_every_order() {
    assert_eq!(collective().exact()[2], [0, 1, 2, 3, 5, 6]);
    check_named("collective", &collective(), true);
}

/// Codex round 3 (`holes.mjs`, `equalityFamily`): `n` names held equal by tests both ways,
/// name `i` in `0..=2n` without `2i + 1`. Equality makes every name share every hole, so each
/// is the even numbers of `0..=2n`: the names take one shared value, which no hole may hold.
/// Enumeration confirms this up to `n = 5` (`11^5` points; `n = 8` would be `17^8`).
/// CONTROL: with the last equality removed, the exact answer is not the even numbers, so the
/// check can fail.
#[test]
fn names_held_equal_share_their_holes() {
    let family = |n: usize, drop_last: bool| {
        let mut edges: Vec<(usize, usize, i64)> = (0..n - 1)
            .flat_map(|i| [(i, i + 1, 0), (i + 1, i, 0)])
            .collect();
        if drop_last {
            edges.truncate(edges.len() - 2);
        }
        Inst {
            range: vec![(0, 2 * n as i64); n],
            out: (0..n as i64).map(|i| vec![2 * i + 1]).collect(),
            edges,
        }
    };
    for n in 2..=8 {
        let inst = family(n, false);
        let evens: Vec<i64> = (0..=n as i64).map(|i| 2 * i).collect();
        let want = vec![evens; n];
        if n <= 5 {
            assert_eq!(inst.exact(), want, "n = {n}: enumeration");
            assert_ne!(
                family(n, true).exact(),
                want,
                "n = {n}: CONTROL, the answer without the last equality"
            );
        }
        let k = inst.tests().1.len();
        for order in [(0..k).collect::<Vec<_>>(), (0..k).rev().collect()] {
            assert_eq!(inst.values(&inst.in_order(&order)), want, "n = {n}");
        }
        assert_eq!(
            inst.values(&inst.at_once()),
            want,
            "n = {n}, one conjunction"
        );
    }
}

/// A random system: `names` names in `0..=6`, each without some values, and `edges` edges
/// with weights in `-w..=w`.
fn random_inst(rnd: &mut Lcg, names: usize, edges: usize, holes: u64, w: i64) -> Inst {
    let mut out = vec![vec![]; names];
    for o in out.iter_mut() {
        for _ in 0..rnd.next(holes + 1) {
            let v = rnd.next(7) as i64;
            if !o.contains(&v) {
                o.push(v);
            }
        }
    }
    let mut es = vec![];
    for _ in 0..edges {
        let u = rnd.next(names as u64) as usize;
        let v = rnd.next(names as u64) as usize;
        if u != v {
            es.push((u, v, rnd.next(2 * w as u64 + 1) as i64 - w));
        }
    }
    Inst {
        range: vec![(0, 6); names],
        out,
        edges: es,
    }
}

/// The three corpora of the sources, each reduced to a seeded size that runs in a few
/// seconds: Claude round 4 (`probe_r4_holes_random_exact`, seed `0x5eed_0004`, 3 or 4 names,
/// up to two holes, 2 to 5 edges in `-2..=2`, 3,000 cases, here 300), Codex round 3
/// (`holes.mjs`, 2 to 4 names, up to four holes, up to `2n` edges in `-3..=3`, 6,000 cases,
/// here 300) and Gemini rounds 3 and 4 (`q1_holes_probe.rs`, `q1_holes_r4.rs`; like its
/// `random_in_class`, a cycle through 3 to 5 names and one chord; 50,000 and 4,507 cases,
/// here 300).
fn corpus() -> Vec<Inst> {
    let mut all = vec![];
    let mut rnd = Lcg(0x5eed_0004);
    for _ in 0..300 {
        let n = 3 + rnd.next(2) as usize;
        let e = 2 + rnd.next(4) as usize;
        all.push(random_inst(&mut rnd, n, e, 2, 2));
    }
    let mut rnd = Lcg(235_711);
    for _ in 0..300 {
        let n = 2 + rnd.next(3) as usize;
        let e = rnd.next(2 * n as u64 + 1) as usize;
        all.push(random_inst(&mut rnd, n, e, 4, 3));
    }
    let mut rnd = Lcg(101);
    for _ in 0..300 {
        let n = 3 + rnd.next(3) as usize;
        let mut inst = random_inst(&mut rnd, n, 0, 3, 3);
        // A cycle through every name, and one chord.
        inst.edges = (0..n)
            .map(|i| (i, (i + 1) % n, rnd.next(7) as i64 - 3))
            .collect();
        let (u, v) = (rnd.next(n as u64) as usize, rnd.next(n as u64) as usize);
        if u != v {
            inst.edges.push((u, v, rnd.next(7) as i64 - 3));
        }
        all.push(inst);
    }
    all
}

/// Every system of [`corpus`], its tests in order and as one conjunction: the scope keeps
/// every value some solution has (sound), and finds no solution exactly when there is none.
#[test]
fn random_systems_are_sound() {
    let (mut cases, mut empty) = (0, 0);
    for inst in corpus() {
        let want = inst.exact();
        let order: Vec<usize> = (0..inst.tests().1.len()).collect();
        for (how, s) in [
            ("in order", inst.in_order(&order)),
            ("at once", inst.at_once()),
        ] {
            let got = inst.values(&s);
            for (i, (w, g)) in want.iter().zip(&got).enumerate() {
                assert!(
                    w.iter().all(|v| g.contains(v)),
                    "{how}: {} loses a value of {w:?}, keeps {g:?}: {inst:?}",
                    nm(i)
                );
            }
        }
        cases += 1;
        empty += usize::from(want.iter().any(|w| w.is_empty()));
    }
    assert!(
        empty > 100 && empty < cases - 100,
        "{empty} of {cases} empty"
    );
}

/// Every system of [`corpus`]: the ends of every name are exact, its tests in order and as
/// one conjunction. An empty answer is a name with no values.
#[test]
fn random_systems_have_exact_ends() {
    for inst in corpus() {
        let want = ends(&inst.exact());
        let order: Vec<usize> = (0..inst.tests().1.len()).collect();
        let got = ends(&inst.values(&inst.in_order(&order)));
        if want.iter().any(Option::is_none) {
            assert!(
                got.iter().any(Option::is_none) || inst.in_order(&order).bottom,
                "no solution, but the scope keeps {got:?}: {inst:?}"
            );
            continue;
        }
        assert_eq!(got, want, "in order: {inst:?}");
        assert_eq!(
            ends(&inst.values(&inst.at_once())),
            want,
            "at once: {inst:?}"
        );
    }
}

/// Every system of [`corpus`]: every name's whole set is exact, its tests in order and as
/// one conjunction (META4 result 1).
#[test]
#[ignore = "HOLES-exact-between: needs exact values between the ends (cross-review xst O4); ST-holes-moves gives exact ends only"]
fn random_systems_have_exact_sets() {
    for inst in corpus() {
        let want = inst.exact();
        let order: Vec<usize> = (0..inst.tests().1.len()).collect();
        assert_eq!(
            inst.values(&inst.in_order(&order)),
            want,
            "in order: {inst:?}"
        );
        assert_eq!(inst.values(&inst.at_once()), want, "at once: {inst:?}");
    }
}

/// A name's values as a union of intervals with open ends, `None` for no bound.
type Runs = Vec<(Option<i64>, Option<i64>)>;

/// Codex round 3 (`unbounded.mjs`): the exact projection of names whose values are a union of
/// intervals, some without a bound, by trying each choice of one interval per name and
/// closing the difference tests with Floyd-Warshall (an extra name fixed at 0 carries the
/// bounds). The projection of one choice is an interval; the answer is their union.
fn unbounded_exact(dom: &[Runs], edges: &[(usize, usize, i64)]) -> Vec<Runs> {
    const INF: i64 = i64::MAX / 4;
    let n = dom.len();
    let mut out: Vec<Runs> = vec![vec![]; n];
    let mut choice = vec![0usize; n];
    if dom.iter().any(Vec::is_empty) {
        return out;
    }
    loop {
        let mut d = vec![vec![INF; n + 1]; n + 1];
        for (i, row) in d.iter_mut().enumerate() {
            row[i] = 0;
        }
        let add = |a: usize, b: usize, c: i64, d: &mut Vec<Vec<i64>>| d[a][b] = d[a][b].min(c);
        for &(u, v, w) in edges {
            add(u, v, w, &mut d);
        }
        for i in 0..n {
            let (l, h) = dom[i][choice[i]];
            if let Some(h) = h {
                add(n, i, h, &mut d);
            }
            if let Some(l) = l {
                add(i, n, -l, &mut d);
            }
        }
        for k in 0..=n {
            for i in 0..=n {
                for j in 0..=n {
                    if d[i][k] < INF && d[k][j] < INF {
                        d[i][j] = d[i][j].min(d[i][k] + d[k][j]);
                    }
                }
            }
        }
        if (0..=n).all(|i| d[i][i] >= 0) {
            for i in 0..n {
                let lo = (d[i][n] < INF).then(|| -d[i][n]);
                let hi = (d[n][i] < INF).then_some(d[n][i]);
                out[i].push((lo, hi));
            }
        }
        let mut k = 0;
        while k < n && choice[k] + 1 == dom[k].len() {
            choice[k] = 0;
            k += 1;
        }
        if k == n {
            break;
        }
        choice[k] += 1;
    }
    out.into_iter()
        .map(|mut rs| {
            rs.sort_by_key(|r| r.0.unwrap_or(i64::MIN));
            let mut merged: Runs = vec![];
            for (l, h) in rs {
                if let Some(last) = merged.last_mut()
                    && last
                        .1
                        .is_none_or(|lh| l.is_some_and(|l| l <= lh + 1) || l.is_none())
                {
                    last.1 = match (last.1, h) {
                        (Some(a), Some(b)) => Some(a.max(b)),
                        _ => None,
                    };
                    continue;
                }
                merged.push((l, h));
            }
            merged
        })
        .collect()
}

/// Whether `v` is in `runs`.
fn in_runs(runs: &Runs, v: i64) -> bool {
    runs.iter()
        .any(|&(l, h)| l.is_none_or(|l| l <= v) && h.is_none_or(|h| v <= h))
}

/// The tests that make a name `x` one of `runs`: its least and greatest bound when they
/// exist, and `x != v` for each value of each gap.
fn runs_tests(x: &str, runs: &Runs) -> Vec<zed_kernel::Term> {
    use crate::nests::{int, prim, var};
    use zed_kernel::Prim;
    if runs.is_empty() {
        return vec![
            prim(Prim::Ge, var(x), int(1)),
            prim(Prim::Le, var(x), int(0)),
        ];
    }
    let mut ts = vec![];
    if let Some(l) = runs[0].0 {
        ts.push(prim(Prim::Ge, var(x), int(l)));
    }
    if let Some(h) = runs[runs.len() - 1].1 {
        ts.push(prim(Prim::Le, var(x), int(h)));
    }
    for w in runs.windows(2) {
        let (a, b) = (w[0].1.expect("an inner run"), w[1].0.expect("an inner run"));
        ts.extend((a + 1..b).map(|v| prim(Prim::Ne, var(x), int(v))));
    }
    ts
}

/// Far points, beyond every bound of the systems below: a name keeps one exactly when its
/// answer is unbounded that way.
const PROBES: [i64; 2] = [-1_000_000, 1_000_000];

/// Codex round 3 (`unbounded.mjs`): 1,600 systems (here 400, seed 7331) of 1 to 4 names,
/// each one of eight unions of intervals, some unbounded and one empty, with up to `2n`
/// difference tests in `-3..=3`. The scope keeps each name's exact values on `-12..=12` and
/// keeps a far value exactly when the answer is unbounded that way. CONTROL (Codex's
/// "missing rays"): the same tests within `-10..=10` give an answer that is not the
/// unbounded one, so the check can tell bounded from unbounded.
#[test]
fn unbounded_names_keep_their_exact_values_and_rays() {
    use crate::nests::and;
    use zedc::store::cell::Premises;
    let choices: Vec<Runs> = vec![
        vec![(None, Some(-1)), (Some(1), None)],
        vec![(None, Some(0))],
        vec![(Some(0), None)],
        vec![(Some(-2), Some(2))],
        vec![(Some(-2), Some(-2)), (Some(0), Some(1)), (Some(3), None)],
        vec![(None, Some(-3)), (Some(0), Some(0)), (Some(2), Some(3))],
        vec![(None, None)],
        vec![],
    ];
    let p = Premises::new();
    let check = |dom: &[Runs], edges: &[(usize, usize, i64)], what: &str| {
        let want = unbounded_exact(dom, edges);
        let inst = Inst {
            range: vec![(0, 0); dom.len()],
            out: vec![vec![]; dom.len()],
            edges: edges.to_vec(),
        };
        let mut ts: Vec<zed_kernel::Term> = (0..dom.len())
            .flat_map(|i| runs_tests(&nm(i), &dom[i]))
            .collect();
        ts.extend(inst.tests().1);
        let s = ts.iter().fold(inst.scope(), |s, t| s.assume(t, true, &p));
        let at_once = match ts.iter().cloned().reduce(and) {
            Some(all) => inst.scope().assume(&all, true, &p),
            None => inst.scope(),
        };
        for (how, s) in [("in order", &s), ("at once", &at_once)] {
            for (i, w) in want.iter().enumerate() {
                let g = s.get(&nm(i));
                for v in (-12..=12).chain(PROBES) {
                    assert_eq!(
                        g.contains(&Value::Int(v)),
                        in_runs(w, v),
                        "{what} {how}: {} at {v}, exact {w:?}, dom {dom:?}, edges {edges:?}",
                        nm(i)
                    );
                }
            }
        }
        want
    };
    let mut rnd = Lcg(7331);
    let mut nonempty = 0;
    for t in 0..400 {
        let n = 1 + rnd.next(4) as usize;
        let dom: Vec<Runs> = (0..n)
            .map(|_| choices[rnd.next(choices.len() as u64) as usize].clone())
            .collect();
        let edges: Vec<(usize, usize, i64)> = (0..rnd.next(2 * n as u64 + 1))
            .map(|_| {
                (
                    rnd.next(n as u64) as usize,
                    rnd.next(n as u64) as usize,
                    rnd.next(7) as i64 - 3,
                )
            })
            .collect();
        let want = check(&dom, &edges, &format!("case {t}"));
        nonempty += usize::from(want.iter().any(|r| !r.is_empty()));
    }
    assert!(nonempty > 100, "{nonempty} of 400 have a solution");
    // Two unbounded names with `x0 - x1 <= -3`: both stay unbounded both ways.
    let all = vec![(None, None)];
    let want = check(&[all.clone(), all.clone()], &[(1, 0, -3)], "two rays");
    assert_eq!(want, [all.clone(), all.clone()]);
    let boxed = vec![(Some(-10), Some(10))];
    assert_ne!(
        unbounded_exact(&[boxed.clone(), boxed], &[(1, 0, -3)]),
        [all.clone(), all],
        "CONTROL: a bounded cube gives a bounded answer"
    );
}

/// The greatest (`up`) or least solution of `inst`, by relaxing each edge and snapping to the
/// nearest allowed value until nothing moves: a monotone operator, whose fixpoint from the
/// top (or bottom) of the ranges is the extreme solution (META3 C1). `None` when there is
/// none.
fn extreme(inst: &Inst, up: bool) -> Option<Vec<i64>> {
    let n = inst.len();
    let snap = |i: usize, mut b: i64| {
        while inst.out[i].contains(&b) {
            b += if up { -1 } else { 1 };
        }
        b
    };
    let mut x: Vec<i64> = (0..n)
        .map(|i| snap(i, if up { inst.range[i].1 } else { inst.range[i].0 }))
        .collect();
    loop {
        let mut moved = false;
        for &(u, v, w) in &inst.edges {
            let (from, to, w) = if up { (u, v, w) } else { (v, u, -w) };
            let lim = x[from] + w;
            if (up && x[to] > lim) || (!up && x[to] < lim) {
                x[to] = snap(to, lim);
                moved = true;
            }
        }
        if x.iter()
            .enumerate()
            .any(|(i, v)| *v < inst.range[i].0 || *v > inst.range[i].1)
        {
            return None;
        }
        if !moved {
            return Some(x);
        }
    }
}

/// Laps (Claude round 3 and 4): a cycle of `n` names in `0..=r`, `x(i+1) <= x(i)`,
/// `x0 <= x(n-1) + 1`; name 0 only the multiples of 3, name `n/2` only 0 and the values 1
/// mod 3. Each lap of the cycle lowers the greatest solution by at most 1, until it reaches 0.
fn laps(n: usize, r: i64) -> Inst {
    let mut out = vec![vec![]; n];
    out[0] = (0..=r).filter(|v| v % 3 != 0).collect();
    out[n / 2] = (0..=r).filter(|v| *v != 0 && v % 3 != 1).collect();
    let mut edges: Vec<(usize, usize, i64)> = (0..n - 1).map(|i| (i, i + 1, 0)).collect();
    edges.push((n - 1, 0, 1));
    Inst {
        range: vec![(0, r); n],
        out,
        edges,
    }
}

/// Staircase: the cycle `x(i+1) <= x(i)`, `x0 <= x(n-1)`, names in `0..=2n`, name `i`
/// without the value `2n - i`.
fn staircase(n: usize) -> Inst {
    let r = 2 * n as i64;
    let out = (0..n as i64).map(|i| vec![r - i]).collect();
    let mut edges: Vec<(usize, usize, i64)> = (0..n - 1).map(|i| (i, i + 1, 0)).collect();
    edges.push((n - 1, 0, 0));
    Inst {
        range: vec![(0, r); n],
        out,
        edges,
    }
}

/// Laps whose other names also lack the value `r - i`.
fn mixed(n: usize, r: i64) -> Inst {
    let mut inst = laps(n, r);
    for i in 1..n {
        if i != n / 2 {
            inst.out[i] = vec![r - i as i64];
        }
    }
    inst
}

/// `k` copies of the collective example, copy `c + 1`'s `x` at most copy `c`'s `z`: one
/// chain of cycles with holes (Claude round 4, `collective_chain`).
fn collective_chain(k: usize) -> Inst {
    let mut inst = Inst {
        range: vec![],
        out: vec![],
        edges: vec![],
    };
    for c in 0..k {
        let b = 3 * c;
        inst.range.extend([(0, 6), (0, 6), (0, 6)]);
        inst.out.extend([vec![5], vec![4], vec![]]);
        inst.edges
            .extend([(b + 1, b + 2, 0), (b, b + 1, 0), (b + 2, b, 1)]);
        if c > 0 {
            inst.edges.push((b + 2, b - 1, 0));
        }
    }
    inst
}

/// Asserts that the scope of `make(n)`, its tests in order, has the exact greatest and least
/// value of every name at `n` and `8n`, and that its work grows near linearly
/// ([`scaling::check_order`]).
fn family(what: &str, n: usize, make: impl Fn(usize) -> Inst + Sync) {
    for m in [n, 8 * n] {
        let inst = make(m);
        let order: Vec<usize> = (0..inst.tests().1.len()).collect();
        let s = inst.in_order(&order);
        let want: Vec<Option<(i64, i64)>> = match (extreme(&inst, false), extreme(&inst, true)) {
            (Some(l), Some(h)) => l.into_iter().zip(h).map(Some).collect(),
            _ => vec![None; inst.len()],
        };
        let got: Vec<Option<(i64, i64)>> = (0..inst.len())
            .map(|i| {
                let p = s.get(&nm(i));
                let vs: Vec<i64> = (inst.range[i].0..=inst.range[i].1)
                    .filter(|v| p.contains(&Value::Int(*v)))
                    .collect();
                Some((*vs.first()?, *vs.last()?))
            })
            .collect();
        assert_eq!(got, want, "{what}, n = {m}: ends");
    }
    let inputs = scaling::inputs(n, |m| {
        let inst = make(m);
        let t = inst.tests();
        (inst, t)
    });
    scaling::check_order(what, n, 1, |m| {
        let (inst, (bx, ts)) = &inputs[&m];
        let p = zedc::store::cell::Premises::new();
        let s = ts.iter().fold(inst.scope().assume(bx, true, &p), |s, t| {
            s.assume(t, true, &p)
        });
        drop(s);
    });
}

/// Claude round 3 and 4 (`family4`, `probe_r4_holes_laps`), Codex round 3 and 4, Gemini
/// round 4: laps with `r = 6n` at 64 and 512 names. Every name's ends are 0, found by
/// composing the cycle once. Main takes about 8.8 times the work for 8 times the size; with
/// the `Vec` interval sets before INTERVAL-persistent it took 17.4 times.
#[test]
fn laps_have_exact_ends_in_near_linear_time() {
    family("laps, r = 6n", 64, |n| laps(n, 6 * n as i64));
}

/// The staircase at 16 and 128 names: every name in `0..=n`. Main takes about 8.9 times the
/// work for 8 times the size.
#[test]
fn the_staircase_has_exact_ends_in_near_linear_time() {
    family("staircase", 16, staircase);
}

/// The mixed family, `r = 3n`, at 16 and 128 names. Main takes about 8.7 times the work for
/// 8 times the size.
#[test]
fn the_mixed_family_has_exact_ends_in_near_linear_time() {
    family("mixed, r = 3n", 16, |n| mixed(n, 3 * n as i64));
}

/// CONTROL (Claude round 4): laps without the closing edge, the same tests otherwise. With
/// no cycle the holes cost one pass, so what is left is the cost of the tests themselves:
/// each `x != v` makes a preimage over the domain of `x`, whose holes grow with the number of
/// tests. When the preimage built its landmarks from the ends of every input domain at each
/// test (before LAPS-preimage-cost), that cost was `O(p log p)` per test for `p` holes, and
/// this control took 17.8 times the work for 8 times the size, as the laps with the cycle
/// did (16.3): the cycle was never the cause. It now takes about 8.8 times.
#[test]
fn laps_without_the_closing_edge_take_near_linear_time() {
    family("laps without the closing edge", 16, |n| {
        let mut inst = laps(n, 6 * n as i64);
        inst.edges.pop();
        inst
    });
}

/// Claude round 4 (`probe_r4_holes_collective_chain`): 4 and 32 copies of the collective
/// example in one chain.
#[ignore = "RP-scaling-10_5: 11.3 times the work at 4 and 32 and 17.9 times the bytes at 32 and 256, over the limit of 10.5; open"]
#[test]
fn a_chain_of_collective_examples_has_exact_ends_in_near_linear_time() {
    family("collective chain (copies)", 4, collective_chain);
}

/// Claude round 4 (`probe_r4_holes_collective_chain_sets_are_exact`): two copies of the
/// collective example in a chain; every name's set is exact in order, reversed and as one
/// conjunction.
#[test]
#[ignore = "HOLES-exact-between: needs exact values between the ends (cross-review xst O4); ST-holes-moves gives exact ends only"]
fn a_chain_of_two_collective_examples_has_exact_sets() {
    let inst = collective_chain(2);
    let want = inst.exact();
    assert_ne!(inst.hull(), want, "CONTROL: the hull is exact");
    let k = inst.tests().1.len();
    let forward: Vec<usize> = (0..k).collect();
    let backward: Vec<usize> = (0..k).rev().collect();
    assert_eq!(inst.values(&inst.in_order(&forward)), want, "in order");
    assert_eq!(inst.values(&inst.in_order(&backward)), want, "reversed");
    assert_eq!(inst.values(&inst.at_once()), want, "one conjunction");
}

/// Codex round 4 (`R4_REGRESSIONS.patch`, `check_exact_holes`): CE-B (as `a`, `b`, `c`) and
/// the collective example (as `x`, `y`, `z`) with each bound its own test, so bounds may
/// arrive after the holes and the edges; every rotation of the tests and of their reverse,
/// from a scope with no bounds. `a` must be `{3, 5}` and `z` `{0, 1, 2, 3, 5, 6}`.
fn check_exact_holes(collective: bool) {
    use crate::ints;
    use crate::nests::{diff_ge, int, names, prim, var};
    use zed_kernel::Prim;
    use zedc::store::cell::Premises;

    let p = Premises::new();
    let ns = if collective {
        names(&["x", "y", "z"])
    } else {
        names(&["a", "b", "c"])
    };
    let (lo, hi) = if collective { (0, 6) } else { (3, 8) };
    let mut tests = Vec::new();
    for n in &ns {
        tests.push(prim(Prim::Ge, var(n), int(lo)));
        tests.push(prim(Prim::Le, var(n), int(hi)));
    }
    if collective {
        tests.extend([
            diff_ge("x", "y", 0),
            diff_ge("y", "z", 0),
            diff_ge("z", "x", -1),
            prim(Prim::Ne, var("x"), int(5)),
            prim(Prim::Ne, var("y"), int(4)),
        ]);
    } else {
        tests.extend([
            prim(Prim::Le, var("a"), int(5)),
            prim(Prim::Ge, var("b"), int(5)),
            prim(Prim::Ne, var("b"), int(6)),
            prim(Prim::Le, var("b"), int(7)),
            prim(Prim::Ge, var("c"), int(6)),
            prim(Prim::Ne, var("c"), int(7)),
            diff_ge("c", "b", 0),
            diff_ge("a", "c", -3),
            diff_ge("b", "a", 2),
        ]);
    }
    let (query, want) = if collective {
        ("z", vec![0, 1, 2, 3, 5, 6])
    } else {
        ("a", vec![3, 5])
    };
    for order in rotations(tests.len()) {
        let s = order
            .iter()
            .fold(ints(&ns), |s, &i| s.assume(&tests[i], true, &p));
        let got: Vec<i64> = (-1..=9)
            .filter(|v| s.get(query).contains(&Value::Int(*v)))
            .collect();
        assert_eq!(got, want, "collective = {collective}, order {order:?}");
    }
}

#[test]
fn ce_b_with_each_bound_a_test_is_exact_in_every_rotation() {
    check_exact_holes(false);
}

#[test]
fn the_collective_example_with_each_bound_a_test_is_exact_in_every_rotation() {
    check_exact_holes(true);
}

/// Gemini round 4 (`q1_holes_r4.rs`, a second CE-A): `a` in `4..=5`, `b` in `{4, 6}`, `c` in
/// `{2, 4}`, the edges of CE-A. `b <= a` gives `b = 4`, so `c = 2` and `a = 4`.
#[test]
fn a_second_ce_a_has_exact_sets_in_every_order() {
    let inst = Inst {
        range: vec![(4, 5), (4, 6), (2, 4)],
        out: vec![vec![], vec![5], vec![3]],
        edges: ce_a().edges,
    };
    assert_eq!(inst.exact(), [vec![4], vec![4], vec![2]], "the enumeration");
    check_named("second CE-A", &inst, true);
}

/// Gemini round 4: three names with holes on one cycle, `x <= y <= z <= x + 1`, `x` in
/// `{0, 3}`, `y` in `{1, 4}`, `z` in `{0, 2}`. No point meets them, in any order.
#[test]
fn three_names_with_holes_on_a_cycle_leave_no_value() {
    let inst = Inst {
        range: vec![(0, 4); 3],
        out: vec![vec![1, 2, 4], vec![0, 2, 3], vec![1, 3, 4]],
        edges: vec![(1, 0, 0), (2, 1, 0), (0, 2, 1)],
    };
    assert_eq!(inst.exact(), vec![Vec::<i64>::new(); 3], "the enumeration");
    check_named("three holed names", &inst, true);
}

/// Gemini round 4: the staircase of four names (`x0 >= x1 >= x2 >= x3 >= x0`, `0..=8`, name
/// `i` without `8 - i`) has every name exactly `0..=4`, in every rotation and as one
/// conjunction (all 40,320 orders of its 8 tests would take too long).
#[test]
fn the_staircase_of_four_has_exact_sets() {
    let inst = staircase(4);
    assert_eq!(inst.exact(), vec![(0..=4).collect::<Vec<i64>>(); 4]);
    check_named("staircase of 4", &inst, true);
}

/// Gemini round 4: two cycles through three names with holes (`z <= y <= x <= z + 1`,
/// `z <= x <= y + 1`, `x != 5`, `y != 4`, `z != 3`, all in `0..=6`). The component is not one
/// simple cycle and has three names with holes, so META4 result 1 refuses it: a warning, and
/// every exact value kept, in every rotation and as one conjunction.
#[test]
#[ignore = "HOLES-exact-between: needs hole tests written in one `&&` kept out of the relation's other conjuncts; ST-holes-moves refuses in every order of separate tests"]
fn two_cycles_through_three_names_with_holes_are_refused() {
    let inst = Inst {
        range: vec![(0, 6); 3],
        out: vec![vec![5], vec![4], vec![3]],
        edges: vec![(1, 2, 0), (0, 1, 0), (2, 0, 1), (0, 2, 0), (1, 0, 1)],
    };
    let want = inst.exact();
    let k = inst.tests().1.len();
    let mut runs: Vec<(String, zedc::store::product::Scope)> = rotations(k)
        .into_iter()
        .map(|o| (format!("{o:?}"), inst.in_order(&o)))
        .collect();
    runs.push(("one conjunction".into(), inst.at_once()));
    for (order, s) in runs {
        assert!(!s.warnings().is_empty(), "order {order}: not refused");
        let got = inst.values(&s);
        for (g, w) in got.iter().zip(&want) {
            assert!(w.iter().all(|v| g.contains(v)), "order {order}: unsound");
        }
    }
}
