//! Tests of the factored products solver (design sec. 8), ported from the prototype of
//! b22-factored1 (/home/luke/Work/wt/proto-b22-factored1/, tests2.rs and tests3.rs). The
//! reference throughout is the crate's own integer solver ([`satisfiable`]) on the base rows,
//! every factor row and the products of the pairs: by Theorem D the verdict with the pairs
//! left equals the verdict with every pair. Each test has a negative control: a mutant of the
//! solver, or a weaker rule, that the same test must catch.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use zedc_int::int::Int;

use super::super::formula::{Atom, Con, Factor, Formula, Lin, Rel, Shared};
use super::super::{pairs, satisfiable};
use super::{Opts, Out, Prob, Row, expand_pairs, free_atoms, solve};
use crate::seed::Rng;

mod bench;

/// A problem from small rows (terms merged by variable, zeros dropped), one product per entry
/// of `bic`, and the mentioned atoms `u * v`.
fn prob(
    rows: &[Vec<(usize, i64)>],
    consts: &[i64],
    bic: &[(Vec<usize>, Vec<usize>)],
    mentioned: &[(usize, usize)],
    nv: usize,
) -> Prob {
    let rows: Vec<Row> = (rows.iter())
        .map(|r| {
            let mut m: BTreeMap<usize, Int> = BTreeMap::new();
            for &(v, c) in r {
                let e = m.entry(v).or_insert(Int::ZERO);
                *e = &*e + &Int::from(c);
            }
            m.into_iter().filter(|(_, c)| !c.is_zero()).collect()
        })
        .collect();
    let mut lists = Vec::new();
    let mut b = Vec::new();
    for (x, y) in bic {
        let mut ids = [0; 2];
        for (i, l) in [x, y].into_iter().enumerate() {
            let mut l = l.clone();
            zed_collections::sorted::sort_dedup(&mut l);
            lists.push(l);
            ids[i] = lists.len() - 1;
        }
        b.push((ids[0], ids[1]));
    }
    let mut partners = vec![Vec::new(); nv];
    for &(u, v) in mentioned {
        partners[u].push(v);
        partners[v].push(u);
    }
    for p in &mut partners {
        zed_collections::sorted::sort_dedup(p);
    }
    Prob {
        rows,
        consts: consts.iter().map(|&c| Int::from(c)).collect(),
        lists,
        bic: b,
        partners,
    }
}

/// Every pair of every product, each once.
fn all_pairs(p: &Prob) -> Vec<(usize, usize)> {
    expand_pairs((p.bic.iter()).map(|&(a, b)| (&p.lists[a][..], &p.lists[b][..])))
}

fn sym(v: usize) -> Factor {
    Factor::Sym(Arc::from(format!("v{v}")))
}

/// Row r of `p` as a [`Lin`] over the symbols `v0`, `v1`, ...
fn lin(p: &Prob, r: usize) -> Lin {
    let mut l = Lin::constant(p.consts[r].clone());
    for (v, c) in &p.rows[r] {
        l.plus_assign(&Lin::atom(sym(*v).atom()).times(c.clone()));
    }
    l
}

fn ge(l: Lin) -> Formula {
    Formula::Con(Con {
        lin: l,
        rel: Rel::Ge,
    })
}

/// The integer verdict on `base`, every factor row and the products of `pairs`, each product
/// atom read as an atom of its own; None when the solver refuses.
fn feasible(p: &Prob, base: &[Lin], pairs: &[(usize, usize)], extra: Option<Lin>) -> Option<bool> {
    let prod = |&(a, b): &(usize, usize)| lin(p, a).product(&lin(p, b)).expect("linear rows");
    let fs: Vec<Formula> = (base.iter().cloned())
        .chain((0..p.rows.len()).map(|r| lin(p, r)))
        .chain(pairs.iter().map(prod))
        .chain(extra)
        .map(ge)
        .collect();
    satisfiable(&Formula::And(Shared::new(fs)))
        .ok()
        .map(|m| m.is_some())
}

/// Row r named by content after step 0's division by the gcd of its coefficients: the
/// normalized linear part and the constant as a reduced fraction.
fn name(p: &Prob, r: usize) -> (Vec<(usize, Int)>, Int, Int) {
    let g = p.rows[r].iter().fold(Int::ZERO, |a, (_, c)| a.gcd(c));
    let g = if g.is_zero() { Int::ONE } else { g };
    let q = p.consts[r].gcd(&g);
    (
        p.rows[r]
            .iter()
            .map(|(v, c)| (*v, c.div_floor(&g)))
            .collect(),
        p.consts[r].div_floor(&q),
        g.div_floor(&q),
    )
}

type Named = (Vec<(usize, Int)>, Int, Int);

/// The pairs named by `f`, each with its two names in order, sorted, each once.
fn named_pairs(left: &[(usize, usize)], f: &dyn Fn(usize) -> Named) -> Vec<(Named, Named)> {
    let mut v: Vec<(Named, Named)> = (left.iter())
        .map(|&(a, b)| {
            let (x, y) = (f(a), f(b));
            if x <= y { (x, y) } else { (y, x) }
        })
        .collect();
    v.sort();
    v.dedup();
    v
}

/// Every pair left has a pair of equal content among those the single-holder rule alone keeps
/// on every pair ([`pairs::kept`], the rule `products` used before): the factored solver drops
/// a superset of what it drops (module doc of `factored`: its last phase is that rule's
/// fixpoint, on a subset of the pairs).
fn within_single_holder(p: &Prob, left: &[(usize, usize)]) -> bool {
    let all = all_pairs(p);
    let rows: Vec<Lin> = (0..p.rows.len()).map(|r| lin(p, r)).collect();
    let rows: Vec<&Lin> = rows.iter().collect();
    let mut partners: HashMap<Factor, Vec<Factor>> = HashMap::new();
    for (u, vs) in p.partners.iter().enumerate() {
        for &v in vs {
            partners.entry(sym(u)).or_default().push(sym(v));
        }
    }
    for ps in partners.values_mut() {
        zed_collections::sorted::sort_dedup(ps);
    }
    let kept = pairs::kept(&rows, &all, &partners);
    let sh: Vec<(usize, usize)> = (all.iter().zip(kept))
        .filter(|(_, k)| *k)
        .map(|(e, _)| *e)
        .collect();
    let n = |r: usize| name(p, r);
    let sh: BTreeSet<(Named, Named)> = named_pairs(&sh, &n).into_iter().collect();
    named_pairs(left, &n).iter().all(|e| sh.contains(e))
}

/// Every drop of `out.log` checked again (the prototype's `replay_ok`): a drop under a sign
/// predicate by Theorem D with u_{wz} = σ_w σ_z (negated for frame−), every pair not yet
/// dropped then having `c_r(u) >= 0` and the dropped one `> 0`; a single-holder drop by a free
/// atom of the pair that no other pair not yet dropped holds. Pairs step 0 drops are implied
/// (tested apart) and left out.
fn replay_ok(p: &Prob, out: &Out) -> bool {
    let dom: BTreeSet<(usize, usize)> = out.dominated.iter().copied().collect();
    let all: Vec<(usize, usize)> = (all_pairs(p).into_iter())
        .filter(|e| !dom.contains(e))
        .collect();
    let val = |s: &[i8], kind: u8, a: usize, b: usize| -> Int {
        let mut t = Int::ZERO;
        for ((w, z), c) in free_atoms(p, a, b) {
            t = &t + &(&c * &Int::from(i64::from(s[w]) * i64::from(s[z])));
        }
        if kind == 2 { -&t } else { t }
    };
    let mut live: BTreeSet<(usize, usize)> = all.iter().copied().collect();
    for ((a, b), kind, _) in &out.log {
        if *kind >= 10 {
            let k = kind - 10;
            let s = &out.sig_pass1[usize::from(k)];
            if (all.iter()).any(|&(x, y)| val(s, k, x, y).is_negative())
                || !val(s, k, *a, *b).is_positive()
            {
                return false;
            }
        }
    }
    for ((a, b), kind, _) in &out.log {
        if *kind >= 10 {
            live.remove(&(*a, *b));
        }
    }
    for ((a, b), kind, s) in &out.log {
        let (a, b) = (*a, *b);
        match kind {
            0..=2 => {
                if (live.iter()).any(|&(x, y)| val(s, *kind, x, y).is_negative())
                    || !val(s, *kind, a, b).is_positive()
                {
                    return false;
                }
            }
            9 => {
                let others: Vec<BTreeMap<(usize, usize), Int>> = (live.iter())
                    .filter(|&&e| e != (a, b))
                    .map(|&(x, y)| free_atoms(p, x, y))
                    .collect();
                let mine = free_atoms(p, a, b);
                if !mine
                    .keys()
                    .any(|k| others.iter().all(|o| !o.contains_key(k)))
                {
                    return false;
                }
            }
            _ => continue,
        }
        live.remove(&(a, b));
    }
    true
}

/// `p` with its variables and rows permuted, its products in the reverse order with their
/// sides swapped, and the map from new rows to old.
fn renamed(p: &Prob, rng: &mut Rng) -> (Prob, Vec<usize>) {
    let mut pv: Vec<usize> = (0..p.nv()).collect();
    let mut pr: Vec<usize> = (0..p.rows.len()).collect();
    rng.shuffle(&mut pv);
    rng.shuffle(&mut pr);
    let mut rows = vec![Vec::new(); p.rows.len()];
    let mut consts = vec![Int::ZERO; p.rows.len()];
    for (r, row) in p.rows.iter().enumerate() {
        let mut v: Row = row.iter().map(|(x, c)| (pv[*x], c.clone())).collect();
        v.sort_unstable_by_key(|t| t.0);
        rows[pr[r]] = v;
        consts[pr[r]] = p.consts[r].clone();
    }
    let mut partners = vec![Vec::new(); p.nv()];
    for (u, vs) in p.partners.iter().enumerate() {
        partners[pv[u]] = vs.iter().map(|&v| pv[v]).collect();
        zed_collections::sorted::sort_dedup(&mut partners[pv[u]]);
    }
    let lists = (p.lists.iter())
        .map(|l| {
            let mut l: Vec<usize> = l.iter().map(|&r| pr[r]).collect();
            l.sort_unstable();
            l
        })
        .collect();
    let bic = p.bic.iter().rev().map(|&(a, b)| (b, a)).collect();
    let mut back = vec![0; pr.len()];
    for (r, &s) in pr.iter().enumerate() {
        back[s] = r;
    }
    (
        Prob {
            rows,
            consts,
            lists,
            bic,
            partners,
        },
        back,
    )
}

/// The pairs left do not depend on the names of the variables, the order of the rows or of
/// the products, or the side a list is on (compared by the content of the original rows).
fn rename_same(p: &Prob, rng: &mut Rng) -> bool {
    let out = solve(p, Opts::default());
    let (q, back) = renamed(p, rng);
    let out2 = solve(&q, Opts::default());
    // By content after step 0's normalization: a class of equal rows may keep another
    // representative once the rows are reordered.
    let n1 = |r: usize| name(p, r);
    let n2 = |r: usize| name(p, back[r]);
    named_pairs(&out.left, &n1) == named_pairs(&out2.left, &n2)
}

/// A random tiny instance: rows with constants, listed pairs, the mentioned atoms, and base
/// rows over the variables and the mentioned atoms (the prototype's `random_tiny`).
struct Tiny {
    rows: Vec<Vec<(usize, i64)>>,
    consts: Vec<i64>,
    pairs: Vec<(usize, usize)>,
    ment: Vec<(usize, usize)>,
    nv: usize,
    base: Vec<Lin>,
}

fn random_row(rng: &mut Rng, nv: usize) -> Vec<(usize, i64)> {
    let mut r = Vec::new();
    for v in 0..nv {
        if rng.below(3) > 0 {
            let c = rng.int(-2, 2);
            if c != 0 {
                r.push((v, c));
            }
        }
    }
    if r.is_empty() {
        r.push((rng.below(nv), 1));
    }
    r
}

fn random_pairs(rng: &mut Rng, nr: usize, pairs: &mut Vec<(usize, usize)>) {
    for _ in 0..1 + rng.below(4) {
        let (a, b) = (rng.below(nr), rng.below(nr));
        let key = (a.min(b), a.max(b));
        if !pairs.contains(&key) {
            pairs.push(key);
        }
    }
}

/// Mentioned atoms (each u <= v with probability 1/3) and 1 to 3 base rows over the variables
/// and the mentioned atoms.
fn random_world(rng: &mut Rng, nv: usize) -> (Vec<(usize, usize)>, Vec<Lin>) {
    let mut ment = Vec::new();
    for u in 0..nv {
        for v in u..nv {
            if rng.below(3) == 0 {
                ment.push((u, v));
            }
        }
    }
    let mut base = Vec::new();
    for _ in 0..1 + rng.below(3) {
        let mut l = Lin::constant(0);
        for v in 0..nv {
            if rng.below(2) == 0 {
                l.plus_assign(&Lin::atom(sym(v).atom()).times(rng.int(-2, 2)));
            }
        }
        for &(u, v) in &ment {
            if rng.below(2) == 0 {
                l.plus_assign(&Lin::atom(Atom::product_of(sym(u), sym(v))).times(rng.int(-2, 2)));
            }
        }
        l.plus_assign(&Lin::constant(rng.int(-3, 3)));
        base.push(l);
    }
    (ment, base)
}

fn random_tiny(rng: &mut Rng) -> Tiny {
    let nv = 2 + rng.below(2);
    let nr = 2 + rng.below(3);
    let mut rows = Vec::new();
    let mut consts = Vec::new();
    for _ in 0..nr {
        rows.push(random_row(rng, nv));
        consts.push(rng.int(-2, 2));
    }
    let mut pairs = Vec::new();
    random_pairs(rng, nr, &mut pairs);
    let (ment, base) = random_world(rng, nv);
    Tiny {
        rows,
        consts,
        pairs,
        ment,
        nv,
        base,
    }
}

fn set_coef(row: &mut Vec<(usize, i64)>, v: usize, c: i64) {
    row.retain(|&(x, _)| x != v);
    row.push((v, c));
    row.sort_unstable_by_key(|&(x, _)| x);
}

/// Rows 0 and 1 give variable 0 opposite signs, and maybe share another variable with one
/// sign, and are paired (the prototype's `random_conflict2`).
fn random_conflict(rng: &mut Rng) -> Tiny {
    let mut t = random_tiny(rng);
    let (c0, c1) = (1 + rng.int(0, 1), 1 + rng.int(0, 1));
    set_coef(&mut t.rows[0], 0, c0);
    set_coef(&mut t.rows[1], 0, -c1);
    if rng.below(2) == 0 {
        let v = 1 + rng.below(t.nv - 1);
        let c = if rng.coin() { 1 } else { -1 };
        set_coef(&mut t.rows[0], v, c);
        set_coef(&mut t.rows[1], v, c);
    }
    if !t.pairs.contains(&(0, 1)) {
        t.pairs.push((0, 1));
    }
    if rng.coin() && !t.pairs.contains(&(0, 0)) {
        t.pairs.push((0, 0));
    }
    t
}

/// Three variables; rows 0 and 1 of opposite signs on variable 0, often proportional, paired
/// (the prototype's `random_shared_conflict`, from Gemini's review).
fn random_shared_conflict(rng: &mut Rng) -> Tiny {
    let nv = 3;
    let nr = 3 + rng.below(2);
    let mut r0 = vec![(0, 1 + rng.int(0, 1))];
    let mut r1 = vec![(0, -(1 + rng.int(0, 1)))];
    if rng.coin() {
        let (c0, b0) = (r0[0].1, r1[0].1);
        r0.push((1, c0));
        r1.push((1, -b0));
    } else if rng.coin() {
        r0.push((1, rng.int(-2, 2)));
        r1.push((1, rng.int(-2, 2)));
    }
    if rng.coin() {
        r0.push((2, rng.int(-2, 2)));
    }
    if rng.coin() {
        r1.push((2, rng.int(-2, 2)));
    }
    let mut rows = vec![r0, r1];
    let mut consts = vec![rng.int(-2, 2), rng.int(-2, 2)];
    for _ in 2..nr {
        rows.push(random_row(rng, nv));
        consts.push(rng.int(-2, 2));
    }
    let mut pairs = vec![(0, 1)];
    random_pairs(rng, nr, &mut pairs);
    let (ment, base) = random_world(rng, nv);
    Tiny {
        rows,
        consts,
        pairs,
        ment,
        nv,
        base,
    }
}

/// The two lists of one product (side A, side B).
type Lists = (Vec<usize>, Vec<usize>);

/// The tiny instance with each listed pair a product of its own.
fn tiny_by_pairs(t: &Tiny) -> Prob {
    let bic: Vec<(Vec<usize>, Vec<usize>)> =
        t.pairs.iter().map(|&(a, b)| (vec![a], vec![b])).collect();
    prob(&t.rows, &t.consts, &bic, &t.ment, t.nv)
}

/// The tiny instance with one product of two random sides.
fn tiny_bic(t: &Tiny, rng: &mut Rng) -> Prob {
    let nr = t.rows.len();
    let mut a: Vec<usize> = (0..nr).filter(|_| rng.coin()).collect();
    let mut b: Vec<usize> = (0..nr).filter(|_| rng.coin()).collect();
    if a.is_empty() {
        a.push(0);
    }
    if b.is_empty() {
        b.push(nr - 1);
    }
    prob(&t.rows, &t.consts, &[(a, b)], &t.ment, t.nv)
}

/// The oracle on one family: the verdict with the pairs left equals the verdict with every
/// pair, every drop replays, the pairs left are within the single-holder rule's, and renaming
/// changes nothing. Controls: the mutant `frame_bad` must fail a replay or change a verdict,
/// and dropping every pair with a free atom (no Theorem D) must change a verdict, which shows
/// the oracle can see a wrong drop.
fn tiny_family(what: &str, generate: fn(&mut Rng) -> Tiny, n: usize, seed: u64) {
    let mut rng = Rng::new(seed);
    let (mut differ, mut skip, mut replay_bad, mut drops, mut sh_bad, mut ren_bad) =
        (0, 0, 0, 0, 0, 0);
    let (mut m_replay, mut m_differ, mut c_differ) = (0, 0, 0);
    for i in 0..n {
        let t = generate(&mut rng);
        let p = if i % 2 == 0 {
            tiny_by_pairs(&t)
        } else {
            tiny_bic(&t, &mut rng)
        };
        let all = all_pairs(&p);
        let log = Opts {
            log: true,
            ..Opts::default()
        };
        let out = solve(&p, log);
        replay_bad += usize::from(!replay_ok(&p, &out));
        drops += usize::from(out.left.len() < all.len());
        sh_bad += usize::from(!within_single_holder(&p, &out.left));
        if i % 4 == 0 {
            ren_bad += usize::from(!rename_same(&p, &mut rng));
        }
        let mo = solve(
            &p,
            Opts {
                frame_bad: true,
                ..log
            },
        );
        m_replay += usize::from(!replay_ok(&p, &mo));
        let ctrl: Vec<(usize, usize)> = (all.iter().copied())
            .filter(|&(a, b)| free_atoms(&p, a, b).is_empty())
            .collect();
        match (
            feasible(&p, &t.base, &all, None),
            feasible(&p, &t.base, &out.left, None),
            feasible(&p, &t.base, &mo.left, None),
            feasible(&p, &t.base, &ctrl, None),
        ) {
            (Some(x), Some(y), Some(m), Some(c)) => {
                differ += usize::from(x != y);
                m_differ += usize::from(x != m);
                c_differ += usize::from(x != c);
            }
            _ => skip += 1,
        }
    }
    println!(
        "tiny {what}: n={n} verdict_differs={differ} skipped={skip} replay_failures={replay_bad} \
         with_a_drop={drops} not_within_single_holder={sh_bad} renaming_differs={ren_bad} | \
         controls: frame_bad replay_failures={m_replay} verdict_differs={m_differ}; \
         drop_any_free verdict_differs={c_differ}"
    );
    assert_eq!(
        (differ, replay_bad, sh_bad, ren_bad),
        (0, 0, 0, 0),
        "{what}: the solver changed a verdict, a drop did not replay, a pair was kept that the \
         single-holder rule drops, or renaming changed the pairs left"
    );
    assert!(
        skip * 20 <= n,
        "{what}: the oracle refused {skip} of {n} cases"
    );
    assert!(drops > 0, "{what}: no case dropped a pair");
    assert!(
        c_differ > 0,
        "{what}: the control drop_any_free changed no verdict"
    );
    assert!(
        m_replay + m_differ > 0,
        "{what}: the mutant frame_bad was not caught"
    );
}

#[test]
fn the_pairs_left_keep_the_verdict_on_random_tiny_instances() {
    tiny_family("random_tiny", random_tiny, 4000, 0x9e37_79b9_7f4a_7c15);
}

#[test]
fn the_pairs_left_keep_the_verdict_when_two_rows_conflict_on_a_variable() {
    tiny_family("conflict", random_conflict, 4000, 0xc1a0_de00_0000_0001);
}

#[test]
fn the_pairs_left_keep_the_verdict_when_conflicting_rows_share_variables() {
    tiny_family(
        "shared_conflict",
        random_shared_conflict,
        5000,
        0x5eed_0000_0000_0003,
    );
}

/// The prototype's `tiny_cone2`: a tiny instance as one product, with three rows in one plane
/// added to its side A: either `c1 v >= -c2` (one variable and the constant) or
/// `c1 v + c2 w >= 0`.
fn tiny_cone(rng: &mut Rng) -> (Tiny, Vec<Lists>) {
    let mut t = random_tiny(rng);
    let nr = t.rows.len();
    let mut a: Vec<usize> = (0..nr).filter(|_| rng.coin()).collect();
    let mut b: Vec<usize> = (0..nr).filter(|_| rng.coin()).collect();
    if a.is_empty() {
        a.push(0);
    }
    if b.is_empty() {
        b.push(nr - 1);
    }
    let v = rng.below(t.nv - 1);
    let w = v + 1 + rng.below(t.nv - 1 - v);
    let with_const = rng.coin();
    let nz = |rng: &mut Rng| loop {
        let c = rng.int(-3, 3);
        if c != 0 {
            break c;
        }
    };
    for _ in 0..3 {
        let (c1, c2) = (nz(rng), nz(rng));
        if with_const {
            t.rows.push(vec![(v, c1)]);
            t.consts.push(c2);
        } else {
            t.rows.push(vec![(v, c1), (w, c2)]);
            t.consts.push(0);
        }
        a.push(t.rows.len() - 1);
    }
    (t, vec![(a, b)])
}

/// The cone rule on lists shared by products (design sec. 8 item 11, A225 item 3). The three
/// plane rows of [`tiny_cone`] are on side A of product 0; a second product has, by `shape`,
/// (0) the same list on side A, (1) that list less one plane row (a different list, so the rule
/// fires for product 0 only), (2) that list on side B. Checks: the verdict is kept, every drop
/// replays, and each pair step 0 drops is implied by the pairs step 0 keeps and the factor rows
/// (the product `< 0` with them is unsatisfiable). Control: the mutant `cone_bad`, which keeps
/// one extreme row and the row after it and drops the other extreme; its dropped pairs must be
/// found not implied. (The prototype's control compared verdicts only and saw 1 or 2
/// differences in 4000 cases; the implication check caught 214 of the 530 cases where the
/// mutant fired on shape 0, 146 of 478 on shape 1 and 225 of 525 on shape 2, VM run of
/// 2026-11-24.)
#[test]
fn the_cone_rule_keeps_the_verdict_on_lists_shared_by_products() {
    // Whether each pair step 0 drops is implied by the factor rows and the products of the
    // pairs step 0 keeps (`step0`: the pairs of the reduced lists, whose class representative
    // may lie outside the product's list; the later steps drop some of them, so `left` alone
    // is too few: a pair (3, 3) whose representative (0, 0) step 5 drops was reported as not
    // implied, VM run of 2026-11-24). None when the solver refused on some pair.
    let mut shown = false;
    let mut implied_all = |p: &Prob, out: &Out, show: bool| -> Option<bool> {
        for &(a, b) in &out.dominated {
            let neg = (lin(p, a).product(&lin(p, b)).expect("linear rows"))
                .times(-1)
                .minus(&Lin::constant(1));
            if feasible(p, &[], &out.step0, Some(neg))? {
                if show && !shown {
                    shown = true;
                    println!(
                        "not implied: pair ({a}, {b}); rows {:?}; consts {:?}; lists {:?}; \
                         bic {:?}; dominated {:?}; step0 {:?}",
                        p.rows, p.consts, p.lists, p.bic, out.dominated, out.step0
                    );
                }
                return Some(false);
            }
        }
        Some(true)
    };
    for shape in 0..3usize {
        let mut rng = Rng::new(0x0c0e_1000_0000_0000 + shape as u64);
        let (mut fired, mut differ, mut replay_bad, mut not_implied, mut skip) = (0, 0, 0, 0, 0);
        let mut skip_implied = 0;
        let (mut ctrl_fired, mut ctrl_caught) = (0, 0);
        let n = 2000;
        for _ in 0..n {
            let (t, mut bic) = tiny_cone(&mut rng);
            let nr = t.rows.len();
            let cone: Vec<usize> = (nr - 3..nr).collect();
            let other: Vec<usize> = (0..nr - 3).filter(|_| rng.coin()).collect();
            let b2 = if other.is_empty() { vec![0] } else { other };
            let second = match shape {
                0 => (bic[0].0.clone(), b2),
                1 => {
                    let gone = cone[rng.below(3)];
                    (
                        bic[0].0.iter().copied().filter(|&r| r != gone).collect(),
                        b2,
                    )
                }
                _ => (b2, bic[0].0.clone()),
            };
            bic.push(second);
            let p = prob(&t.rows, &t.consts, &bic, &t.ment, t.nv);
            let log = Opts {
                log: true,
                ..Opts::default()
            };
            let on = solve(&p, log);
            let off = solve(
                &p,
                Opts {
                    no_cone: true,
                    ..log
                },
            );
            let bad = solve(
                &p,
                Opts {
                    cone_bad: true,
                    ..log
                },
            );
            let f = on.dominated.len() != off.dominated.len();
            fired += usize::from(f);
            replay_bad += usize::from(!replay_ok(&p, &on));
            let cf = bad.dominated != on.dominated;
            ctrl_fired += usize::from(cf);
            match implied_all(&p, &on, true) {
                Some(i) => not_implied += usize::from(!i),
                None => skip_implied += 1,
            }
            if cf {
                ctrl_caught += usize::from(implied_all(&p, &bad, false) == Some(false));
            }
            match (
                feasible(&p, &t.base, &all_pairs(&p), None),
                feasible(&p, &t.base, &on.left, None),
            ) {
                (Some(x), Some(y)) => differ += usize::from(x != y),
                _ => skip += 1,
            }
        }
        println!(
            "cone1 shape={shape}: n={n} rule_fired={fired} verdict_differs={differ} \
             replay_failures={replay_bad} not_implied={not_implied} skipped_verdict={skip} \
             skipped_implied={skip_implied} | control cone_bad: fired={ctrl_fired} \
             caught_not_implied={ctrl_caught}"
        );
        assert_eq!(
            (differ, replay_bad, not_implied),
            (0, 0, 0),
            "shape {shape}"
        );
        // At most a fifth of the cases refused by the oracle (measured 2026-11-24: 271 of 2000
        // on shape 0, before the implication check was counted apart).
        assert!(
            skip * 5 <= n && skip_implied * 5 <= n,
            "shape {shape}: the oracle refused {skip} verdicts and {skip_implied} implications of {n}"
        );
        assert!(fired > 0, "shape {shape}: the cone rule never fired");
        // The prototype's verdict control saw 1 or 2 differences in 4000 cases; the implication
        // check must catch at least a tenth of the cases where the mutant drops other pairs.
        assert!(
            ctrl_fired > 0 && ctrl_caught * 10 >= ctrl_fired,
            "shape {shape}: the control cone_bad was caught in {ctrl_caught} of {ctrl_fired} cases"
        );
    }
}

/// Boolean matrix multiplication as one run of the solver (design sec. 5.3, the prototype's
/// `build_bmm`). A (with a unit diagonal) and F are n x n Boolean matrices; rows s_u = Σ_{A[u][x]}
/// w_x (0..n), t_v = z_v (+ (−1)^v g with `g`) (n..2n), blockers b_x = −w_x + y_x (2n..3n);
/// with `g` also t_+ = r_1 + g and t_− = r_2 − g (3n, 3n + 1). Variables w_x = x, z_v = n + v,
/// y_x = 2n + x, g = 4n, r_i = 4n + i. One product: side A the s_u and b_x, side B the t rows.
/// `w_x * z_v` is mentioned iff F[x][v] = 0, and `w_x * r_i` with `g`. Returns AF.
fn build_bmm(n: usize, free: usize, seed: u64, g: bool) -> (Prob, Vec<Vec<bool>>) {
    let mut rng = Rng::new(seed);
    let a: Vec<Vec<bool>> = (0..n)
        .map(|u| (0..n).map(|x| x == u || rng.coin()).collect())
        .collect();
    let mut f = vec![vec![false; n]; n];
    for _ in 0..free {
        f[rng.below(n)][rng.below(n)] = true;
    }
    let mut rows: Vec<Vec<(usize, i64)>> = Vec::new();
    for au in &a {
        rows.push((0..n).filter(|&x| au[x]).map(|x| (x, 1)).collect());
    }
    for v in 0..n {
        let mut t = vec![(n + v, 1)];
        if g {
            t.push((4 * n, if v % 2 == 0 { 1 } else { -1 }));
        }
        rows.push(t);
    }
    for x in 0..n {
        rows.push(vec![(x, -1), (2 * n + x, 1)]);
    }
    let mut side_b: Vec<usize> = (n..2 * n).collect();
    if g {
        rows.push(vec![(4 * n + 1, 1), (4 * n, 1)]);
        rows.push(vec![(4 * n + 2, 1), (4 * n, -1)]);
        side_b.extend([3 * n, 3 * n + 1]);
    }
    let mut ment = Vec::new();
    for (x, fx) in f.iter().enumerate() {
        for (v, &free) in fx.iter().enumerate() {
            if !free {
                ment.push((x, n + v));
            }
        }
        if g {
            ment.extend([(x, 4 * n + 1), (x, 4 * n + 2)]);
        }
    }
    let side_a: Vec<usize> = (0..n).chain(2 * n..3 * n).collect();
    let consts = vec![0; rows.len()];
    let p = prob(&rows, &consts, &[(side_a, side_b)], &ment, 4 * n + 3);
    let c = (0..n)
        .map(|u| (0..n).map(|v| (0..n).any(|x| a[u][x] && f[x][v])).collect())
        .collect();
    (p, c)
}

/// Design sec. 5.3: the pairs left are exactly the zeros of A F (with `g`, also every (s_u,
/// t_±)), and pass 1 lists no pair (b_x, t), so the Def sets fill in step 5 alone, which is
/// what the reduction needs. Control: without the sign predicates (`no_def`) the pairs left
/// are not the zeros of A F wherever F has a one.
#[test]
fn the_residual_of_the_bmm_reduction_is_the_zeros_of_a_f() {
    let mut ctrl_caught = 0;
    let mut ctrl_cases = 0;
    for g in [false, true] {
        for (n, seed) in [(24usize, 1u64), (68, 2)] {
            for free in [0, 3, n, 4 * n] {
                let (p, c) = build_bmm(n, free, seed + free as u64, g);
                let out = solve(
                    &p,
                    Opts {
                        log: true,
                        ..Opts::default()
                    },
                );
                let mut want: Vec<(usize, usize)> = (0..n)
                    .flat_map(|u| (0..n).map(move |v| (u, v)))
                    .filter(|&(u, v)| !c[u][v])
                    .map(|(u, v)| (u, n + v))
                    .collect();
                if g {
                    want.extend((0..n).flat_map(|u| [(u, 3 * n), (u, 3 * n + 1)]));
                }
                want.sort_unstable();
                let blocker = |r: usize| (2 * n..3 * n).contains(&r);
                let t_row = |r: usize| (n..2 * n).contains(&r) || r >= 3 * n;
                let listed_blockers = (out.listed.iter())
                    .filter(|&&(a, b)| blocker(a) && t_row(b) || blocker(b) && t_row(a))
                    .count();
                println!(
                    "bmm n={n} free={free} g={g}: zeros of AF={} left={} listed={} \
                     listed (b_x, t) pairs={listed_blockers} worklist={}",
                    want.len(),
                    out.left.len(),
                    out.listed.len(),
                    out.worklist
                );
                assert_eq!(listed_blockers, 0, "pass 1 listed a pair (b_x, t)");
                assert_eq!(out.left, want, "n={n} free={free} g={g}");
                if free > 0 {
                    ctrl_cases += 1;
                    let ctrl = solve(
                        &p,
                        Opts {
                            no_def: true,
                            ..Opts::default()
                        },
                    );
                    ctrl_caught += usize::from(ctrl.left != want);
                }
            }
        }
    }
    assert_eq!(
        ctrl_caught, ctrl_cases,
        "the control no_def must miss the zeros of A F"
    );
}

/// The prototype's `build_wlgrow(l, r)`: r rows Σ x + (±1) pv + e_i and r rows Σ y + d_j in
/// one product, and l products of one row each, `−x_t + c_t − c_{t+1}` with `m_t`, which give
/// the x their signs one at a time in step 5; with `g`, a variable g on the Y rows with
/// alternating signs (`build_wlgrow_g`), so the Y rows never sign it.
fn build_wlgrow(l: usize, r: usize, g: bool) -> Prob {
    let x = |i: usize| i;
    let pv = l;
    let e = |i: usize| l + 1 + i;
    let y = |i: usize| l + 1 + r + i;
    let d = |j: usize| 2 * l + 1 + r + j;
    let c = |i: usize| 2 * l + 1 + 2 * r + i;
    let m = |i: usize| 3 * l + 2 + 2 * r + i;
    let q = 4 * l + 2 + 2 * r;
    let gv = q + 1;
    let mut rows: Vec<Vec<(usize, i64)>> = Vec::new();
    for i in 0..r {
        let mut v: Vec<(usize, i64)> = (0..l).map(|t| (x(t), 1)).collect();
        v.push((pv, if i % 2 == 0 { 1 } else { -1 }));
        v.push((e(i), 1));
        rows.push(v);
    }
    for j in 0..r {
        let mut v: Vec<(usize, i64)> = (0..l).map(|t| (y(t), 1)).collect();
        v.push((d(j), 1));
        if g {
            v.push((gv, if j % 2 == 0 { 1 } else { -1 }));
        }
        rows.push(v);
    }
    let mut bic = vec![((0..r).collect::<Vec<_>>(), (r..2 * r).collect::<Vec<_>>())];
    for t in 0..l {
        let ki = rows.len();
        rows.push(vec![(x(t), -1), (c(t), 1), (c(t + 1), -1)]);
        rows.push(vec![(m(t), 1)]);
        bic.push((vec![ki], vec![ki + 1]));
    }
    let mut ment = Vec::new();
    for s in 0..l {
        ment.extend((0..l).map(|t| (x(s), y(t))));
        ment.extend((0..r).map(|j| (x(s), d(j))));
    }
    for i in 0..r {
        ment.extend((0..l).map(|t| (e(i), y(t))));
        ment.extend((0..r).map(|j| (e(i), d(j))));
    }
    for t in 0..l {
        ment.extend([(m(t), x(t)), (m(t), c(t)), (q, x(t)), (q, y(t))]);
        ment.extend((0..l).map(|s| (m(t), y(s))));
    }
    let consts = vec![0; rows.len()];
    prob(&rows, &consts, &bic, &ment, gv + 1)
}

/// The input size of the prototype's `kp`: row lengths plus one, products, mentioned atoms
/// (each counted from both ends), and the rows of the distinct nonempty side lists.
fn size(p: &Prob) -> u64 {
    let sides: BTreeSet<&Vec<usize>> = (p.bic.iter())
        .flat_map(|&(a, b)| [&p.lists[a], &p.lists[b]])
        .filter(|s| !s.is_empty())
        .collect();
    p.rows.iter().map(|r| r.len() as u64 + 1).sum::<u64>()
        + p.bic.len() as u64
        + p.partners.iter().map(|v| v.len() as u64).sum::<u64>()
        + sides.iter().map(|s| s.len() as u64).sum::<u64>()
}

/// The work of steps 0 to 4, of the Def-set rechecks and of the count rules and peel, at l
/// and at the l giving about 8 times the input, and their ratios.
fn ratios(build: &dyn Fn(usize) -> Prob, ls: [usize; 2]) -> ([u64; 2], [f64; 4]) {
    let mut at = [[0u64; 4]; 2];
    let mut k = [0u64; 2];
    for (i, l) in ls.into_iter().enumerate() {
        let p = build(l);
        let out = solve(&p, Opts::default());
        k[i] = size(&p);
        at[i] = [k[i], out.pass1, out.worklist, out.single];
        println!(
            "l={l} size={} pass1={} worklist={} single={} left={}",
            k[i],
            out.pass1,
            out.worklist,
            out.single,
            out.left.len()
        );
    }
    let r = std::array::from_fn(|j| at[1][j] as f64 / at[0][j].max(1) as f64);
    println!(
        "ratios: size {:.2} pass1 {:.2} worklist {:.2} single {:.2}",
        r[0], r[1], r[2], r[3]
    );
    (k, r)
}

/// Exception 4 of A225 (COMPLEXITY.md, the A225 entry): on `wlgrow_g` the worklist grows 34
/// times at 8 times the input, since each of the l signings of an x rechecks the r² pairs of
/// the X and Y rows (design sec. 5.3: Boolean matrix multiplication reduces to this worklist,
/// so no combinatorial method is known to bring it under 10.5). This test asserts the limit
/// and fails until that is solved; it is not ignored (the standing rule).
#[test]
fn the_worklist_of_wlgrow_g_scales() {
    let (k, r) = ratios(&|l| build_wlgrow(l, l, true), [10, 28]);
    // The size grows as l²: 28/10 gives 6.97, the nearest to 8 the prototype's sizes reach.
    assert!(
        (6.5..9.0).contains(&(k[1] as f64 / k[0] as f64)),
        "the sizes are about 8x apart"
    );
    assert!(
        r[2] < crate::scaling::LIMIT,
        "the worklist grew {:.2} times at 8x the input on wlgrow_g (exception 4 of A225)",
        r[2]
    );
}

/// Without g the Y rows sign their variables in pass 1, so pass 1 and the worklist stay
/// within the limit. Control: the exact peel after them (`single`), measured on the same two
/// inputs, grows past the limit (47.20 times, VM run of 2026-11-24): it is O(W_listed),
/// exception 3 of the design (docs/studies/products-factored.md sec. 4, item 3, and
/// COMPLEXITY.md, the A225 entry). So the measurement can see superlinear growth here. (The
/// listing of every pair is no control on this family: it grew 7.38 times, as the input.)
#[test]
fn the_pass1_and_worklist_of_wlgrow_scale() {
    let build = |l| build_wlgrow(l, l, false);
    let (k, r) = ratios(&build, [10, 28]);
    assert!(
        (6.5..9.0).contains(&(k[1] as f64 / k[0] as f64)),
        "the sizes are about 8x apart"
    );
    assert!(
        r[1] < crate::scaling::LIMIT,
        "pass 1 grew {:.2} times",
        r[1]
    );
    assert!(
        r[2] < crate::scaling::LIMIT,
        "the worklist grew {:.2} times",
        r[2]
    );
    assert!(
        r[3] > crate::scaling::LIMIT,
        "the control (the exact peel) grew only {:.2} times",
        r[3]
    );
}

/// The arguments of [`kept_pairs`]: the rows, the rows on each factor, the products wanted and
/// the partners of each factor.
pub(super) type Star = (
    Vec<Lin>,
    BTreeMap<Factor, Vec<usize>>,
    BTreeSet<(Factor, Factor)>,
    HashMap<Factor, Vec<Factor>>,
);

/// The family of the bench: factor x has the k rows `x + u_i >= 0`, factor y the k rows
/// `y + w_j >= 0`, and only `x * y` is mentioned. Every product `(x + u_i)(y + w_j)` holds the
/// free atom `u_i * w_j` alone, so none is kept; the old `products` listed all k² pairs first.
pub(super) fn star(k: usize) -> Star {
    let s = |n: String| Factor::Sym(Arc::from(n));
    let (x, y) = (s("x".into()), s("y".into()));
    let mut rows = Vec::with_capacity(2 * k);
    for (f, other) in [(&x, "u"), (&y, "w")] {
        for i in 0..k {
            let mut l = Lin::atom(f.atom());
            l.plus_assign(&Lin::atom(s(format!("{other}{i}")).atom()));
            rows.push(l);
        }
    }
    let on = BTreeMap::from([
        (x.clone(), (0..k).collect()),
        (y.clone(), (k..2 * k).collect()),
    ]);
    let wanted = BTreeSet::from([(x.clone(), y.clone())]);
    let partners = HashMap::from([(x.clone(), vec![y.clone()]), (y, vec![x])]);
    (rows, on, wanted, partners)
}

/// On [`star`], stage A' keeps no pair, and its work grows within the limit at 8 times k, from
/// k = 1000 (n log n meets 10.5 only from n = 777); the control, the k² pairs the old
/// `products` listed, grows 64 times.
#[test]
fn no_pair_of_the_star_is_listed_and_the_work_scales() {
    let mut work = [0u64; 2];
    let mut listed = [0usize; 2];
    for (i, k) in [1000, 8000].into_iter().enumerate() {
        let (rows, on, wanted, partners) = star(k);
        let rows: Vec<&Lin> = rows.iter().collect();
        let p = Prob::of(&rows, &on, &wanted, &partners);
        let out = solve(
            &p,
            Opts {
                log: true,
                ..Opts::default()
            },
        );
        assert_eq!(out.left, [], "k={k}: every pair holds a free atom alone");
        assert_eq!(out.listed, [], "k={k}: pass 1 lists no pair");
        work[i] = out.pass1 + out.worklist + out.single;
        listed[i] = all_pairs(&p).len();
    }
    let r = work[1] as f64 / work[0] as f64;
    let c = listed[1] as f64 / listed[0] as f64;
    println!(
        "star: work {work:?} ratio {r:.2}; control (every pair listed) {listed:?} ratio {c:.2}"
    );
    assert!(r < crate::scaling::PREFERRED, "the work grew {r:.2} times");
    assert!(
        c > crate::scaling::LIMIT,
        "the control grew only {c:.2} times"
    );
}

/// Wide coefficients: the cone rule and step 0's comparisons are exact (the prototype's i128
/// could overflow). Three rows `c1 v + c2 w >= 0` with coefficients near 2^100, the middle one
/// the sum of the outer two, on one side: the middle row's pair goes, the outer two stay.
/// Control: with the cone rule off all three stay.
#[test]
fn the_cone_rule_is_exact_on_wide_coefficients() {
    let big = Int::from(1i128 << 100);
    let row = |a: &Int, b: &Int| -> Row { vec![(0, a.clone()), (1, b.clone())] };
    let one = Int::ONE;
    let b1 = &big + &one;
    let rows = vec![
        row(&big, &one),
        row(&one, &big),
        row(&b1, &b1),
        vec![(2, Int::ONE)],
    ];
    let p = Prob {
        consts: vec![Int::ZERO; rows.len()],
        rows,
        lists: vec![vec![0, 1, 2], vec![3]],
        bic: vec![(0, 1)],
        partners: vec![vec![2], vec![2], vec![0, 1]],
    };
    let log = Opts {
        log: true,
        ..Opts::default()
    };
    let on = solve(&p, log);
    assert_eq!(on.dominated, [(2, 3)], "the middle row's pair goes");
    let off = solve(
        &p,
        Opts {
            no_cone: true,
            ..log
        },
    );
    assert_eq!(off.dominated, [], "control: without the rule all stay");
    assert_eq!(on.left, [(0, 3), (1, 3)]);
}
