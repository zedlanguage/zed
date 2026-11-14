//! Reference models of the S4 base and fixpoint (META4 results 2 and 3), against enumeration.
//!
//! - Claude round 4 (`s4model4`): two names `x`, `y` in `0..=6`, each test a disjunction of two
//!   atoms `a x + b y <= c` (or `>= c`), a box a pair of 7-bit sets. The base is box-only
//!   subsumption: a live case `a` of a part goes into the base when every live case `o` of the
//!   part has no point in the box with `o` and not `a`; a part with no live case gives the
//!   empty box. Under exact, arc and bounds projection it is order independent, monotone and
//!   sound on the 5,000 triples. CONTROLS: skipping a part with no live case, promoting on
//!   arrival, and subsumption relative to the base each break a property.
//! - Codex round 4 (`q2-box-base.mjs`): the same base on `{0, 1, 2}^2` with masks of points,
//!   checked on every pair of nested boxes.
//! - Codex round 3 (`base.mjs`, `class.mjs`, `meter`): the monotonicity mutation, the integer
//!   octagon projection on 6,561 bound choices, the two-hub octagonal component with a
//!   dominating disjunction, and the Boolean-hub implication walk.
//!
//! Not ported: base definitions other than box-only subsumption (round 2 and 3 alternatives
//! that META4 replaced; Claude's corpus logs still list them), and Gemini's C_comb, rejected.

use std::collections::BTreeSet;

use super::Lcg;
use zed_tests::instances::Rng;

// ---------------------------------------------------------------------------------------------
// Claude's two-name model.

/// The values of each name: `0..W`.
const W: i64 = 7;

/// `a x + b y <= c`, or `>= c` when `ge`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Atom {
    a: i64,
    b: i64,
    c: i64,
    ge: bool,
}

impl Atom {
    fn holds(&self, x: i64, y: i64) -> bool {
        let s = self.a * x + self.b * y;
        if self.ge { s >= self.c } else { s <= self.c }
    }
}

/// One test: a disjunction of two atoms.
type Disj = [Atom; 2];

/// `x <= c` and the like, for named cases.
const fn at(a: i64, b: i64, c: i64, ge: bool) -> Atom {
    Atom { a, b, c, ge }
}

fn rnd(g: &mut Lcg, n: u64) -> i64 {
    g.next(n) as i64
}

fn atom(g: &mut Lcg) -> Atom {
    let a = rnd(g, 3) - 1;
    let b = rnd(g, 3) - 1;
    let c = rnd(g, 9) - 4;
    let ge = rnd(g, 2) == 1;
    Atom { a, b, c, ge }
}

fn disj(g: &mut Lcg) -> Disj {
    [atom(g), atom(g)]
}

/// The corpus of rounds 1 to 4: seed `0x139`, 20,000 pairs skipped, then 5,000 triples.
fn triples() -> Vec<[Disj; 3]> {
    let mut g = Lcg(0x139);
    for _ in 0..20_000 {
        disj(&mut g);
        disj(&mut g);
    }
    (0..5000)
        .map(|_| [disj(&mut g), disj(&mut g), disj(&mut g)])
        .collect()
}

/// The sets of `x` and `y` as bit masks; `[0, 0]` is the empty box.
type Bx = [u8; 2];
const FULL: Bx = [0x7f, 0x7f];
const BOT: Bx = [0, 0];

fn norm(b: Bx) -> Bx {
    if b[0] == 0 || b[1] == 0 { BOT } else { b }
}

fn meet(p: Bx, q: Bx) -> Bx {
    norm([p[0] & q[0], p[1] & q[1]])
}

fn join(p: Bx, q: Bx) -> Bx {
    [p[0] | q[0], p[1] | q[1]]
}

fn sub(p: Bx, q: Bx) -> bool {
    p[0] & !q[0] == 0 && p[1] & !q[1] == 0
}

fn bx(xs: &[i64], ys: &[i64]) -> Bx {
    let m = |vs: &[i64]| vs.iter().fold(0u8, |m, v| m | 1 << v);
    [m(xs), m(ys)]
}

/// How the base projection is computed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Pi {
    /// The projection of the points (enumeration).
    Exact,
    /// Each atom alone removes the values without a support, to a fixpoint.
    Arc,
    /// As `Arc`, but only the least and greatest values are removed.
    Bounds,
}

const PIS: [Pi; 3] = [Pi::Exact, Pi::Arc, Pi::Bounds];

fn proj(pi: Pi, b: Bx, atoms: &[Atom]) -> Bx {
    match pi {
        Pi::Exact => proj_exact(b, atoms),
        Pi::Arc => propagate(b, atoms, false),
        Pi::Bounds => propagate(b, atoms, true),
    }
}

/// Whether value `v` of name `k` has a support for `a` in `b`.
fn supported(b: Bx, a: &Atom, k: usize, v: i64) -> bool {
    (0..W).any(|w| b[1 - k] >> w & 1 == 1 && if k == 0 { a.holds(v, w) } else { a.holds(w, v) })
}

fn propagate(b: Bx, atoms: &[Atom], ends: bool) -> Bx {
    let mut b = norm(b);
    loop {
        let before = b;
        for a in atoms {
            for k in 0..2 {
                if ends {
                    while b[k] != 0 && !supported(b, a, k, b[k].trailing_zeros() as i64) {
                        b[k] &= b[k] - 1;
                    }
                    while b[k] != 0 && !supported(b, a, k, 7 - b[k].leading_zeros() as i64) {
                        b[k] &= !(1u8 << (7 - b[k].leading_zeros()));
                    }
                } else {
                    for v in 0..W {
                        if b[k] >> v & 1 == 1 && !supported(b, a, k, v) {
                            b[k] &= !(1u8 << v);
                        }
                    }
                }
                b = norm(b);
                if b == BOT {
                    return BOT;
                }
            }
        }
        if b == before {
            return b;
        }
    }
}

fn proj_exact(b: Bx, atoms: &[Atom]) -> Bx {
    let mut out = [0u8; 2];
    for x in (0..W).filter(|x| b[0] >> x & 1 == 1) {
        for y in (0..W).filter(|y| b[1] >> y & 1 == 1) {
            if atoms.iter().all(|a| a.holds(x, y)) {
                out[0] |= 1 << x;
                out[1] |= 1 << y;
            }
        }
    }
    norm(out)
}

/// The exact answer: the projection of the points that meet every test.
fn exact(ds: &[Disj]) -> Bx {
    let mut out = [0u8; 2];
    for x in 0..W {
        for y in 0..W {
            if ds.iter().all(|d| d.iter().any(|a| a.holds(x, y))) {
                out[0] |= 1 << x;
                out[1] |= 1 << y;
            }
        }
    }
    norm(out)
}

fn negate(a: Atom) -> Atom {
    Atom {
        c: if a.ge { a.c - 1 } else { a.c + 1 },
        ge: !a.ge,
        ..a
    }
}

/// How a part puts a case into the base.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Base {
    /// META4 result 2: box-only subsumption, and a part with no live case gives the empty box.
    SubsumptionBox,
    /// CONTROL: promotion of the only live case, with "exactly one" read literally, so a part
    /// with no live case is skipped.
    PromotionSkipDead,
}

/// The live cases of `d` in `b` with base atoms `bs`, each with its projection.
fn live(pi: Pi, b: Bx, bs: &[Atom], d: &Disj) -> Vec<(Atom, Bx)> {
    d.iter()
        .filter_map(|a| {
            let mut all = bs.to_vec();
            all.push(*a);
            let p = proj(pi, b, &all);
            (p != BOT).then_some((*a, p))
        })
        .collect()
}

/// The case to promote: the only live case, or (box-only subsumption) a live case `a` with no
/// point of the box meeting a live case and not `a`.
fn promoted(pi: Pi, b: Bx, l: &[(Atom, Bx)], base: Base) -> Option<Atom> {
    if l.len() == 1 {
        return Some(l[0].0);
    }
    if base != Base::SubsumptionBox {
        return None;
    }
    l.iter()
        .map(|(a, _)| *a)
        .find(|a| l.iter().all(|(o, _)| proj(pi, b, &[*o, negate(*a)]) == BOT))
}

/// One step of part `d`: the new box; promoted cases go into `bs`.
fn part_step(pi: Pi, b: Bx, bs: &mut Vec<Atom>, d: &Disj, base: Base) -> Bx {
    let l = live(pi, b, bs, d);
    if l.is_empty() {
        return if base == Base::PromotionSkipDead {
            b
        } else {
            BOT
        };
    }
    if let Some(a) = promoted(pi, b, &l, base)
        && !bs.contains(&a)
    {
        bs.push(a);
    }
    meet(b, l.iter().fold([0u8; 2], |acc, (_, p)| join(acc, *p)))
}

/// The greatest fixpoint from the full box, the parts in `order` each round, then the base;
/// stops after a round that changes nothing.
fn gfp_sched(pi: Pi, ds: &[Disj], base: Base, order: &[usize]) -> Bx {
    let mut bs = vec![];
    let mut b = FULL;
    loop {
        let before = (b, bs.len());
        for &i in order {
            b = part_step(pi, b, &mut bs, &ds[i], base);
        }
        b = meet(b, proj(pi, b, &bs));
        if (b, bs.len()) == before || b == BOT {
            return b;
        }
    }
}

/// The same fixpoint under a random schedule: each round every part and the base once in a
/// random order, plus up to three random repeats.
fn gfp_random(pi: Pi, ds: &[Disj], base: Base, g: &mut Lcg) -> Bx {
    let k = ds.len();
    let mut bs = vec![];
    let mut b = FULL;
    loop {
        let before = (b, bs.len());
        let mut order: Vec<usize> = (0..=k).collect();
        for i in (1..order.len()).rev() {
            order.swap(i, g.next(i as u64 + 1) as usize);
        }
        for _ in 0..g.next(4) {
            order.push(g.next(k as u64 + 1) as usize);
        }
        for i in order {
            b = if i == k {
                meet(b, proj(pi, b, &bs))
            } else {
                part_step(pi, b, &mut bs, &ds[i], base)
            };
        }
        if (b, bs.len()) == before || b == BOT {
            return b;
        }
    }
}

/// The operator as a function of the box alone: the least promoted set closed under promotion
/// in `b`, then every part and the base applied once to `b`.
fn operator(pi: Pi, b: Bx, ds: &[Disj], base: Base) -> Bx {
    let mut bs = vec![];
    loop {
        let n = bs.len();
        for d in ds {
            let l = live(pi, b, &bs, d);
            if l.is_empty() {
                if base == Base::PromotionSkipDead {
                    continue;
                }
                return BOT;
            }
            if let Some(a) = promoted(pi, b, &l, base)
                && !bs.contains(&a)
            {
                bs.push(a);
            }
        }
        if bs.len() == n {
            break;
        }
    }
    let mut out = meet(b, proj(pi, b, &bs));
    for d in ds {
        let l = live(pi, b, &bs, d);
        if l.is_empty() {
            continue;
        }
        out = meet(out, l.iter().fold([0u8; 2], |acc, (_, p)| join(acc, *p)));
    }
    out
}

/// CONTROL: promotion decided once per test on arrival, against the fixpoint of the tests
/// before it, and never revisited.
fn promote_on_arrival(pi: Pi, ds: &[Disj], order: &[usize]) -> Bx {
    let mut bs: Vec<Atom> = vec![];
    let mut parts: Vec<Disj> = vec![];
    let mut b = FULL;
    for &i in order {
        let l = live(pi, b, &bs, &ds[i]);
        match l.len() {
            0 => return BOT,
            1 => bs.push(l[0].0),
            _ => parts.push(ds[i]),
        }
        loop {
            let before = b;
            for d in &parts {
                let u = live(pi, b, &bs, d)
                    .iter()
                    .fold([0u8; 2], |acc, (_, p)| join(acc, *p));
                b = meet(b, u);
            }
            b = meet(b, proj(pi, b, &bs));
            if b == before {
                break;
            }
        }
    }
    b
}

const PERMS: [[usize; 3]; 6] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
];

/// A random sub-box of `b`, each value dropped with probability 1/3.
fn sub_box(b: Bx, g: &mut Lcg) -> Bx {
    let mut out = [0u8; 2];
    for k in 0..2 {
        for v in 0..W {
            if b[k] >> v & 1 == 1 && g.next(3) != 0 {
                out[k] |= 1 << v;
            }
        }
    }
    norm(out)
}

#[derive(Debug, Default, PartialEq)]
struct Tally {
    inexact: usize,
    order_dependent: usize,
    unsound: usize,
    not_a_fixpoint: usize,
    monotonicity_failures: usize,
}

/// Claude's `corpus`: each triple in the six part orders and `schedules` random schedules,
/// and `pairs` random nested box pairs for monotonicity of the operator, both drawn from `seed`
/// (`0x5eed` in Claude's run).
fn corpus(pi: Pi, base: Base, schedules: usize, pairs: usize, seed: u64) -> Tally {
    let mut g = Lcg(seed);
    let mut t = Tally::default();
    for ds in &triples() {
        let e = exact(ds);
        let mut outs: Vec<Bx> = PERMS.iter().map(|p| gfp_sched(pi, ds, base, p)).collect();
        for _ in 0..schedules {
            outs.push(gfp_random(pi, ds, base, &mut g));
        }
        let f = outs[0];
        t.order_dependent += outs.iter().any(|o| *o != f) as usize;
        t.inexact += (f != e) as usize;
        t.unsound += outs.iter().any(|o| !sub(e, *o)) as usize;
        t.not_a_fixpoint += (operator(pi, f, ds, base) != f) as usize;
        for _ in 0..pairs {
            let b1 = sub_box(FULL, &mut g);
            let b2 = sub_box(b1, &mut g);
            t.monotonicity_failures +=
                !sub(operator(pi, b2, ds, base), operator(pi, b1, ds, base)) as usize;
        }
    }
    t
}

/// Claude round 4, `s4model4 corpus 20 20`, under projection `pi`: the box-only subsumption
/// base is order independent, sound, a fixpoint of its operator and monotone on every triple,
/// and inexact on `inexact` of the 5,000 triples (the inexact count depends only on the first
/// order, so fewer schedules leave it unchanged). The triples are Claude's; the schedules and
/// nested pairs take a new seed each run, one of each per triple (20 under exact projection and
/// 4 under the others, in one test, before: 4.1 s at load 27).
fn box_only_base_is_order_independent_and_monotone(pi: Pi, inexact: usize) {
    let (_, seed) = Rng::fresh(&format!(
        "schedules and nested boxes of the box-only base, {pi:?}"
    ));
    let t = corpus(pi, Base::SubsumptionBox, 1, 1, seed);
    assert_eq!(
        t,
        Tally {
            inexact,
            ..Tally::default()
        },
        "seed {seed}, {pi:?}"
    );
}

#[test]
fn the_box_only_subsumption_base_is_order_independent_and_monotone_under_exact_projection() {
    box_only_base_is_order_independent_and_monotone(Pi::Exact, 74);
}

#[test]
fn the_box_only_subsumption_base_is_order_independent_and_monotone_under_arc_projection() {
    box_only_base_is_order_independent_and_monotone(Pi::Arc, 196);
}

#[test]
fn the_box_only_subsumption_base_is_order_independent_and_monotone_under_bounds_projection() {
    box_only_base_is_order_independent_and_monotone(Pi::Bounds, 196);
}

/// CONTROL (Claude round 4): with a part that has no live case skipped, the operator is not
/// monotone on Claude's named case (the sub-box `B'` maps outside the image of `B`), and the
/// fixpoint depends on the order (144 triples in Claude's run).
#[test]
fn control_skipping_a_dead_part_breaks_monotonicity_and_order_independence() {
    let ds: [Disj; 3] = [
        [at(-1, 1, 4, true), at(0, 1, -2, false)],
        [at(0, -1, -3, true), at(1, 0, -2, false)],
        [at(-1, 1, 2, false), at(0, 0, 1, false)],
    ];
    let b = bx(&[0, 1, 3, 4, 5, 6], &[0, 1, 2, 3, 4, 6]);
    let b2 = bx(&[4, 5, 6], &[0, 3, 4, 6]);
    assert!(sub(b2, b));
    let f = |base, b| operator(Pi::Exact, b, &ds, base);
    assert_eq!(f(Base::PromotionSkipDead, b), bx(&[0, 1], &[4, 6]));
    assert_eq!(f(Base::PromotionSkipDead, b2), bx(&[4, 5, 6], &[0, 3]));
    assert!(!sub(
        f(Base::PromotionSkipDead, b2),
        f(Base::PromotionSkipDead, b)
    ));
    assert!(sub(f(Base::SubsumptionBox, b2), f(Base::SubsumptionBox, b)));
    let (_, seed) = Rng::fresh("schedules and nested boxes, a dead part skipped");
    let t = corpus(Pi::Exact, Base::PromotionSkipDead, 1, 1, seed);
    assert!(t.order_dependent > 0, "seed {seed}: {t:?}");
    assert!(t.monotonicity_failures > 0, "seed {seed}: {t:?}");
}

/// CONTROL (Claude round 4): promotion decided on arrival and never revisited depends on the
/// order of the tests: 4 triples under exact projection (inexact on 109 in the first order), 3
/// under arc and bounds (inexact on 217).
#[test]
fn control_promotion_on_arrival_depends_on_the_order() {
    for (pi, dep, inexact) in [(Pi::Exact, 4, 109), (Pi::Arc, 3, 217), (Pi::Bounds, 3, 217)] {
        let (mut d, mut i) = (0, 0);
        for ds in &triples() {
            let outs: Vec<Bx> = PERMS
                .iter()
                .map(|p| promote_on_arrival(pi, ds, p))
                .collect();
            d += outs.iter().any(|o| *o != outs[0]) as usize;
            i += (outs[0] != exact(ds)) as usize;
        }
        assert_eq!((d, i), (dep, inexact), "{pi:?}");
    }
}

/// Property P (Claude round 4, `pcheck`): if `o` implies `a` in box `b` (no point of `b` meets
/// `o` and not `a`) and `o` is live with `phi`, then `a` is live with `phi`. Counts, over
/// `count` random draws, the draws where the premises hold and where P fails, for the
/// implication tested in the box alone with `o` one atom, relative to `phi`, and in the box
/// alone with `o` two atoms. Claude drew from seed `0x9c4ec`.
fn pcheck(pi: Pi, count: usize, seed: u64) -> [[usize; 2]; 3] {
    let mut g = Lcg(seed);
    let mut tally = [[0usize; 2]; 3];
    for _ in 0..count {
        let b = sub_box(FULL, &mut g);
        let phi: Vec<Atom> = (0..1 + g.next(3)).map(|_| atom(&mut g)).collect();
        let a = atom(&mut g);
        let o = [atom(&mut g), atom(&mut g)];
        for (k, t) in tally.iter_mut().enumerate() {
            let o: &[Atom] = if k == 2 { &o } else { &o[..1] };
            let mut imp = o.to_vec();
            imp.push(negate(a));
            if k == 1 {
                imp.extend(&phi);
            }
            if proj(pi, b, &imp) != BOT {
                continue;
            }
            let mut with_o = phi.clone();
            with_o.extend(o);
            if proj(pi, b, &with_o) == BOT {
                continue;
            }
            let mut with_a = phi.clone();
            with_a.push(a);
            t[0] += 1;
            t[1] += (proj(pi, b, &with_a) == BOT) as usize;
        }
    }
    tally
}

/// Property P holds for the box-only implication test under each projection, on 50,000 draws
/// from a new seed each run (200,000 of Claude's draws before: 1.4 s at load 27). Claude, all
/// 2,000,000 draws: with `o` one atom the premises held on 266,497 draws under exact projection
/// and 266,499 under arc and bounds, with `o` two atoms on 198,946 and 198,949, and P failed on
/// none.
#[test]
fn property_p_holds_for_the_box_only_implication_test() {
    const DRAWS: usize = 50_000;
    let (_, seed) = Rng::fresh("draws of property P");
    for pi in PIS {
        let t = pcheck(pi, DRAWS, seed);
        assert!(
            t[0][0] > 5_000,
            "seed {seed}, {pi:?}: premises held on {}",
            t[0][0]
        );
        assert_eq!(t[0][1], 0, "seed {seed}, {pi:?}: box-only, one atom");
        assert_eq!(t[2][1], 0, "seed {seed}, {pi:?}: box-only, two atoms");
    }
}

/// CONTROL (Claude round 4): the implication tested relative to the base (`phi`) fails P under
/// arc projection, on 2 of Claude's 2,000,000 draws (seed `0x9c4ec`); this is the first, draw
/// 637,360. In `x` in `{0, 3, 4, 6}`, `y` in `0..=4` with `phi` = `x - y >= 0`, `y - x >= 0`,
/// `x + y >= 4`, the case `o` = `x + y <= 4` implies `a` = `y <= 2` with `phi`, `o` is live
/// with `phi`, and `a` is not. The box-only test does not promote `a` here.
#[test]
fn control_the_base_relative_implication_test_fails_property_p() {
    let b = bx(&[0, 3, 4, 6], &[0, 1, 2, 3, 4]);
    let phi = [
        at(1, -1, 0, true),
        at(-1, 1, 0, true),
        at(-1, -1, -4, false),
    ];
    let o = at(-1, -1, -4, true);
    let a = at(0, -1, -2, true);
    let mut imp = vec![o, negate(a)];
    imp.extend(phi);
    assert_eq!(proj(Pi::Arc, b, &imp), BOT, "o implies a with phi");
    let mut with_o = phi.to_vec();
    with_o.push(o);
    assert_ne!(proj(Pi::Arc, b, &with_o), BOT, "o is live");
    let mut with_a = phi.to_vec();
    with_a.push(a);
    assert_eq!(proj(Pi::Arc, b, &with_a), BOT, "a is not live: P fails");
    assert_ne!(
        proj(Pi::Arc, b, &[o, negate(a)]),
        BOT,
        "the box-only test does not promote a"
    );
}

/// Claude round 4 (`canonicity`): two sets of tests with the same points, and the box each
/// gives under box-only subsumption in the order written. `x <= 3 || y <= 3` and
/// `x <= 3 || y >= 4` together mean `x <= 3`; promotion sees two live cases in each and
/// promotes neither, so S4 keeps the full box under each projection, while `x <= 3 || x <= 3`
/// gives `x` in `0..=3`.
#[test]
fn equivalent_tests_can_give_different_boxes() {
    let x_le_3 = at(1, 0, 3, false);
    let pair = [[x_le_3, at(0, 1, 3, false)], [x_le_3, at(0, 1, 4, true)]];
    let one = [[x_le_3, x_le_3]];
    assert_eq!(exact(&pair), exact(&one));
    assert_eq!(exact(&one), bx(&[0, 1, 2, 3], &[0, 1, 2, 3, 4, 5, 6]));
    for pi in PIS {
        let s = |ds: &[Disj]| gfp_sched(pi, ds, Base::SubsumptionBox, &[0, 1][..ds.len()]);
        assert_eq!(s(&one), exact(&one), "{pi:?}");
        assert_eq!(s(&pair), FULL, "{pi:?}");
    }
}

// ---------------------------------------------------------------------------------------------
// Codex round 4 (`q2-box-base.mjs`): the box-only base on the nine points `{0, 1, 2}^2`.

/// The nine points; a set of points is a 9-bit mask.
fn point(i: usize) -> (i64, i64) {
    ((i / 3) as i64, (i % 3) as i64)
}

fn mask(ok: impl Fn(i64, i64) -> bool) -> u16 {
    (0..9).fold(0, |m, i| {
        let (x, y) = point(i);
        if ok(x, y) { m | 1 << i } else { m }
    })
}

/// A box: the sets of `x` and `y` (3-bit masks) and the mask of its points.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Box3 {
    x: u8,
    y: u8,
    m: u16,
}

fn boxes3() -> Vec<Box3> {
    (0..8u8)
        .flat_map(|x| {
            (0..8u8).map(move |y| Box3 {
                x,
                y,
                m: mask(|a, b| x >> a & 1 == 1 && y >> b & 1 == 1),
            })
        })
        .collect()
}

fn proj3(bs: &[Box3], m: u16) -> Box3 {
    let (mut x, mut y) = (0usize, 0usize);
    for i in (0..9).filter(|i| m >> i & 1 == 1) {
        let (a, b) = point(i);
        x |= 1 << a;
        y |= 1 << b;
    }
    bs[8 * x + y]
}

/// Codex's operator: live cases relative to the base mask; a live case that every live case
/// lies in within the box goes into the base (box-only subsumption); a part with no live case
/// gives the empty box, unless `skip_dead` (CONTROL).
fn op3(
    bs: &[Box3],
    b: Box3,
    base: u16,
    parts: &[[u16; 2]],
    reverse: bool,
    skip_dead: bool,
) -> Box3 {
    let mut bm = base;
    let order: Vec<&[u16; 2]> = if reverse {
        parts.iter().rev().collect()
    } else {
        parts.iter().collect()
    };
    loop {
        let mut next = bm;
        for d in &order {
            let mut live: Vec<u16> = d.iter().copied().filter(|a| b.m & bm & a != 0).collect();
            if live.is_empty() {
                if skip_dead {
                    continue;
                }
                return bs[0];
            }
            if reverse {
                live.reverse();
            }
            for a in &live {
                if live.iter().all(|o| b.m & o & !a == 0) {
                    next &= a;
                }
            }
        }
        if next == bm {
            break;
        }
        bm = next;
    }
    let mut out = proj3(bs, b.m & bm);
    for d in parts {
        let union = d[0] | d[1];
        if skip_dead && b.m & bm & union == 0 {
            continue;
        }
        let p = proj3(bs, b.m & bm & union);
        out = bs[8 * (out.x & p.x) as usize + (out.y & p.y) as usize];
    }
    out
}

fn gfp3(bs: &[Box3], mut b: Box3, base: u16, parts: &[[u16; 2]], reverse: bool) -> Box3 {
    loop {
        let next = op3(bs, b, base, parts, reverse, false);
        if next.m == b.m {
            return b;
        }
        b = next;
    }
}

/// Codex round 4: on 3,000 seeded systems (a base atom and two to four parts of atoms
/// `a x + b y <= c`), the operator is monotone on every pair of nested boxes, the fixpoint is
/// the same with the parts reversed, and no point that meets the tests is lost. CONTROLS:
/// skipping a dead part breaks monotonicity on `x <= 0 || x >= 2`; promoting the first live
/// case loses points.
#[test]
fn the_box_only_base_on_nine_points_is_monotone_on_every_nested_pair() {
    let bs = boxes3();
    let mut atoms: Vec<u16> = vec![];
    for a in -1..=1 {
        for b in -1..=1 {
            for c in -3..=3 {
                let m = mask(|x, y| a * x + b * y <= c);
                if !atoms.contains(&m) {
                    atoms.push(m);
                }
            }
        }
    }
    let mut g = Lcg(0x139);
    let (mut monotone, mut schedules, mut sound, mut comparisons) = (0, 0, 0, 0);
    for _ in 0..3000 {
        let n = atoms.len() as u64;
        let base = atoms[g.next(n) as usize];
        let k = 2 + g.next(3);
        let parts: Vec<[u16; 2]> = (0..k)
            .map(|_| [atoms[g.next(n) as usize], atoms[g.next(n) as usize]])
            .collect();
        let answers: Vec<Box3> = bs
            .iter()
            .map(|b| op3(&bs, *b, base, &parts, false, false))
            .collect();
        for j in 0..bs.len() {
            for i in 0..bs.len() {
                if bs[i].x & !bs[j].x != 0 || bs[i].y & !bs[j].y != 0 {
                    continue;
                }
                comparisons += 1;
                monotone += (answers[i].m & !answers[j].m != 0) as usize;
            }
        }
        for (i, b) in bs.iter().enumerate() {
            schedules += (gfp3(&bs, *b, base, &parts, false).m
                != gfp3(&bs, *b, base, &parts, true).m) as usize;
            let concrete = b.m & base & parts.iter().fold(511, |m, d| m & (d[0] | d[1]));
            sound += (concrete & !answers[i].m != 0) as usize;
        }
    }
    assert!(comparisons > 1_000_000);
    assert_eq!((monotone, schedules, sound), (0, 0, 0));
    let d = [[mask(|x, _| x <= 0), mask(|x, _| x >= 2)]];
    let (full, small) = (bs[63], bs[8 * 2 + 7]);
    let large = op3(&bs, full, 511, &d, false, true);
    let wrong_small = op3(&bs, small, 511, &d, false, true);
    assert_ne!(wrong_small.m & !large.m, 0, "CONTROL: skipping a dead part");
    assert_eq!(
        op3(&bs, small, 511, &d, false, false).m & !op3(&bs, full, 511, &d, false, false).m,
        0
    );
    let first_live = proj3(&bs, full.m & d[0][0]);
    assert_ne!(
        full.m & (d[0][0] | d[0][1]) & !first_live.m,
        0,
        "CONTROL: first live case"
    );
}

/// Codex round 3 (`base.mjs`): the mutation that promotes the first live case when two are
/// live is not monotone on `x <= 0 || x >= 2` with `X = {0, 1, 2}` and `X' = {2}` (`y = 0`);
/// box-only subsumption is. And singleton parts that meet only through the base (`x - y >= 5
/// || y - x >= 5`, `x - y >= -2`, `x - y <= 2`) leave no value.
#[test]
fn promoting_the_first_live_case_is_not_monotone() {
    let d: Disj = [at(1, 0, 0, false), at(1, 0, 2, true)];
    let large = bx(&[0, 1, 2], &[0]);
    let small = bx(&[2], &[0]);
    let wrong = |b: Bx| {
        let l = live(Pi::Exact, b, &[], &d);
        proj_exact(b, &[l[0].0])
    };
    assert!(!sub(wrong(small), wrong(large)), "CONTROL");
    let right = |b| operator(Pi::Exact, b, &[d], Base::SubsumptionBox);
    assert!(sub(right(small), right(large)));
    let only = |a: Atom| [a, a];
    let ds = [
        [at(1, -1, 5, true), at(-1, 1, 5, true)],
        only(at(1, -1, -2, true)),
        only(at(1, -1, 2, false)),
    ];
    for p in PERMS {
        assert_eq!(gfp_sched(Pi::Exact, &ds, Base::SubsumptionBox, &p), BOT);
    }
}

// ---------------------------------------------------------------------------------------------
// Codex round 3 (`class.mjs`, `meter`): the integer octagon projection and the two-hub
// octagonal component with a dominating disjunction.

/// A closed interval; infinite ends mean no bound. `f64` holds every integer here exactly.
type Bounds = [f64; 2];
/// Bounds on `x`, `y`, `x + y` and `x - y`.
type Core = [Bounds; 4];
const OPEN: Bounds = [f64::NEG_INFINITY, f64::INFINITY];

/// The integer values of `x` over the integer points of `c`, by eliminating `y`.
fn xrange(c: Core) -> Option<Bounds> {
    if c.iter().any(|[l, h]| l > h) {
        return None;
    }
    let [mut lo, mut hi] = c[0];
    let lower = [(0.0, c[1][0]), (-1.0, c[2][0]), (1.0, -c[3][1])];
    let upper = [(0.0, c[1][1]), (-1.0, c[2][1]), (1.0, -c[3][0])];
    for (a, b) in lower.into_iter().filter(|(_, b)| b.is_finite()) {
        for (q, r) in upper.into_iter().filter(|(_, b)| b.is_finite()) {
            let (slope, rhs) = (a - q, r - b);
            if slope == 0.0 {
                if rhs < 0.0 {
                    return None;
                }
            } else if slope > 0.0 {
                hi = hi.min((rhs / slope).floor());
            } else {
                lo = lo.max((rhs / slope).ceil());
            }
        }
    }
    (lo <= hi).then_some([lo, hi])
}

/// The least and greatest of `x`, `y`, `x + y`, `x - y` over the integer points of `c`.
fn extrema(c: Core) -> Option<Core> {
    let x = xrange(c)?;
    let y = xrange([c[1], c[0], c[2], [-c[3][1], -c[3][0]]])?;
    let [l, h] = x;
    let [ly, hy] = c[1];
    let [ls, hs] = c[2];
    let [ld, hd] = c[3];
    Some([
        x,
        y,
        [
            ls.max(l + ly).max(2.0 * l - hd),
            hs.min(h + hy).min(2.0 * h - ld),
        ],
        [
            ld.max(l - hy).max(2.0 * l - hs),
            hd.min(h - ly).min(2.0 * h - ls),
        ],
    ])
}

/// Codex's meter `verify`: `extrema` agrees with enumeration on each of the 6,561 choices of
/// bounds on `x + y` and `x - y` in `-4..=4`, with `x`, `y` in `-2..=2`. CONTROL: `x + y = 1`
/// and `x - y = 0` have a real solution and no integer one, and `extrema` finds none.
#[test]
fn the_octagon_projection_is_exact_on_every_bound_choice() {
    let mut cores = 0;
    for ls in -4..=4 {
        for hs in -4..=4 {
            for ld in -4..=4 {
                for hd in -4..=4 {
                    let c: Core = [
                        [-2.0, 2.0],
                        [-2.0, 2.0],
                        [f64::from(ls), f64::from(hs)],
                        [f64::from(ld), f64::from(hd)],
                    ];
                    let mut want = [[f64::INFINITY, f64::NEG_INFINITY]; 4];
                    for x in -2..=2 {
                        for y in -2..=2 {
                            let vs = [x, y, x + y, x - y].map(f64::from);
                            if vs.iter().zip(c).all(|(v, [lo, hi])| lo <= *v && *v <= hi) {
                                for (w, v) in want.iter_mut().zip(vs) {
                                    *w = [w[0].min(v), w[1].max(v)];
                                }
                            }
                        }
                    }
                    let got = extrema(c);
                    if want[0][0].is_infinite() {
                        assert_eq!(got, None, "{c:?}");
                    } else {
                        assert_eq!(got, Some(want), "{c:?}");
                    }
                    cores += 1;
                }
            }
        }
    }
    assert_eq!(cores, 6561);
    assert_eq!(
        extrema([OPEN, OPEN, [1.0, 1.0], [0.0, 0.0]]),
        None,
        "CONTROL: parity"
    );
}

/// Runs of consecutive integers, merged where they touch.
fn merge(mut rs: Vec<Bounds>) -> Vec<Bounds> {
    rs.sort_by(|a, b| a[0].total_cmp(&b[0]));
    let mut out: Vec<Bounds> = vec![];
    for [lo, hi] in rs {
        match out.last_mut() {
            Some(last) if lo <= last[1] + 1.0 => last[1] = last[1].max(hi),
            _ => out.push([lo, hi]),
        }
    }
    out
}

/// One of the four forms with a sign: `sign * form >= t` for a case.
type Form = (usize, f64);

/// A two-hub octagonal component: the core, the two forms of every disjunction, and each
/// disjunction's thresholds `(a, b)`, meaning `form0 >= a || form1 >= b`.
struct Hub {
    core: Core,
    forms: [Form; 2],
    parts: Vec<[f64; 2]>,
}

fn tighten(c: &mut Core, (f, sign): Form, t: f64) {
    if sign > 0.0 {
        c[f][0] = c[f][0].max(t);
    } else {
        c[f][1] = c[f][1].min(-t);
    }
}

/// Why a component is refused.
#[derive(Debug, PartialEq)]
struct NoDominatingDisjunction;

impl Hub {
    /// The values of `x` and `y`: the disjunction with both greatest thresholds implies every
    /// other, so the answer is the union of its two cases. With `check` false (CONTROL) the
    /// greatest thresholds are used even when no disjunction has both.
    fn project(&self, check: bool) -> Result<[Vec<Bounds>; 2], NoDominatingDisjunction> {
        let mut es = vec![];
        if self.parts.is_empty() {
            es.extend(extrema(self.core));
        } else {
            let max = [0, 1].map(|i| {
                self.parts
                    .iter()
                    .map(|p| p[i])
                    .fold(f64::NEG_INFINITY, f64::max)
            });
            if check && !self.parts.contains(&max) {
                return Err(NoDominatingDisjunction);
            }
            for (form, t) in self.forms.into_iter().zip(max) {
                let mut c = self.core;
                tighten(&mut c, form, t);
                es.extend(extrema(c));
            }
        }
        Ok([0, 1].map(|i| merge(es.iter().map(|e| e[i]).collect())))
    }

    fn holds(&self, x: i64, y: i64, part: Option<usize>) -> bool {
        let fs = [x, y, x + y, x - y].map(|v| v as f64);
        let case = |(f, s): Form, t: f64| s * fs[f] >= t;
        self.core
            .iter()
            .zip(fs)
            .all(|([l, h], v)| *l <= v && v <= *h)
            && self.parts.iter().enumerate().all(|(i, p)| {
                part.is_some_and(|q| q != i)
                    || case(self.forms[0], p[0])
                    || case(self.forms[1], p[1])
            })
    }

    /// The exact runs of `x` and `y` (enumeration), and the S4 fixpoint by enumeration, the
    /// parts one at a time (`x`, `y` finite in the core).
    fn oracle(&self) -> ([Vec<Bounds>; 2], [Vec<Bounds>; 2]) {
        let range = |i: usize| (self.core[i][0] as i64..=self.core[i][1] as i64).collect();
        let narrow = |b: &[BTreeSet<i64>; 2], part: Option<usize>| {
            let mut out = [BTreeSet::new(), BTreeSet::new()];
            for x in &b[0] {
                for y in &b[1] {
                    if self.holds(*x, *y, part) {
                        out[0].insert(*x);
                        out[1].insert(*y);
                    }
                }
            }
            out
        };
        let full: [BTreeSet<i64>; 2] = [range(0), range(1)];
        let exact = narrow(&full, None);
        let mut b = full;
        loop {
            let before = b.clone();
            b = narrow(&b, Some(usize::MAX));
            for i in 0..self.parts.len() {
                b = narrow(&b, Some(i));
            }
            if b == before {
                break;
            }
        }
        (exact.map(|s| runs(&s)), b.map(|s| runs(&s)))
    }
}

fn runs(s: &BTreeSet<i64>) -> Vec<Bounds> {
    merge(s.iter().map(|v| [*v as f64, *v as f64]).collect())
}

fn random_form(g: &mut Lcg) -> Form {
    (g.next(4) as usize, if g.next(2) == 1 { 1.0 } else { -1.0 })
}

/// Codex round 3 (`class.mjs`): on seeded components with a dominating disjunction, the
/// projection equals the exact answer and the S4 fixpoint, with the parts in either order.
/// Named: the B4 band (`x - y >= 5 || y - x >= 5`, `-2 <= x - y <= 2`) leaves no value.
/// CONTROLS: crossed thresholds (`x >= 3 || y >= 0`, `x >= 0 || y >= 3`, `x + y <= 2`) have no
/// dominating disjunction and are refused; their greatest thresholds taken anyway give a
/// wrong answer.
#[test]
fn a_two_hub_component_with_a_dominating_disjunction_is_exact() {
    let mut g = Lcg(37);
    let mut nonempty = 0;
    for t in 0..600 {
        let mut r = |n| g.next(n) as f64;
        let core: Core = [
            [-3.0, 3.0],
            [-3.0, 3.0],
            [-6.0 + r(5), 2.0 + r(5)],
            [-6.0 + r(5), 2.0 + r(5)],
        ];
        let forms = [random_form(&mut g), random_form(&mut g)];
        let k = 1 + g.next(6);
        let mut parts: Vec<[f64; 2]> = (0..k)
            .map(|_| [g.next(11) as f64 - 5.0, g.next(11) as f64 - 5.0])
            .collect();
        let max = [0, 1].map(|i| parts.iter().map(|p| p[i]).fold(f64::NEG_INFINITY, f64::max));
        parts.push(max);
        let mut h = Hub { core, forms, parts };
        let got = h.project(true).expect("a dominating disjunction");
        let (exact, s4) = h.oracle();
        assert_eq!(got, exact, "component {t}: exact");
        assert_eq!(got, s4, "component {t}: S4");
        h.parts.reverse();
        nonempty += !got[0].is_empty() as usize;
        assert_eq!(h.project(true), Ok(got), "component {t}: reversed");
    }
    assert!(nonempty > 300, "nonempty components: {nonempty}");
    let band = Hub {
        core: [[-20.0, 20.0], [-20.0, 20.0], OPEN, [-2.0, 2.0]],
        forms: [(3, 1.0), (3, -1.0)],
        parts: vec![[5.0, 5.0]],
    };
    assert_eq!(band.project(true), Ok([vec![], vec![]]));
    let crossed = Hub {
        core: [[-3.0, 3.0], [-3.0, 3.0], [f64::NEG_INFINITY, 2.0], OPEN],
        forms: [(0, 1.0), (1, 1.0)],
        parts: vec![[3.0, 0.0], [0.0, 3.0]],
    };
    assert_eq!(crossed.project(true), Err(NoDominatingDisjunction));
    let wrong = crossed.project(false).expect("no check");
    assert_ne!(
        wrong,
        crossed.oracle().0,
        "CONTROL: greatest thresholds without the check"
    );
}

/// Codex round 3 (`class.mjs`, `walk`): a Boolean-hub implication component. `v_i` in
/// `0..=3`, `w` in `0..=1`; a start `i` is `v_i - w >= 1`; an edge `(i, j)` is
/// `v_i + w <= 0 || v_j - w >= 1`. The names reachable from a start are `1..=3`, the rest
/// `0..=3`, `w` `0..=1`: equal to enumeration and to the S4 fixpoint on seeded components, in
/// either edge order. CONTROL: with an edge missing, the name past it is not forced.
#[test]
fn an_implication_walk_is_exact() {
    fn reach(n: usize, edges: &[(usize, usize)], starts: &[usize]) -> Vec<bool> {
        let mut forced = vec![false; n];
        let mut stack: Vec<usize> = starts.to_vec();
        while let Some(i) = stack.pop() {
            if forced[i] {
                continue;
            }
            forced[i] = true;
            stack.extend(edges.iter().filter(|e| e.0 == i).map(|e| e.1));
        }
        forced
    }
    let mut g = Lcg(37);
    for t in 0..300 {
        let n = 2 + g.next(4) as usize;
        let mut edges = vec![];
        for i in 0..n {
            for j in 0..n {
                if i != j && g.next(3) == 0 {
                    edges.push((i, j));
                }
            }
        }
        let starts: Vec<usize> = (0..n).filter(|_| g.next(3) == 0).collect();
        let base = |v: &[i64]| starts.iter().all(|&i| v[i] - v[n] >= 1);
        let clause = |v: &[i64], (i, j): (usize, usize)| v[i] + v[n] <= 0 || v[j] - v[n] >= 1;
        let narrow = |b: &[BTreeSet<i64>], ok: &dyn Fn(&[i64]) -> bool| {
            let mut out = vec![BTreeSet::new(); n + 1];
            let mut v = vec![0; n + 1];
            fn go(
                k: usize,
                b: &[BTreeSet<i64>],
                v: &mut Vec<i64>,
                ok: &dyn Fn(&[i64]) -> bool,
                out: &mut [BTreeSet<i64>],
            ) {
                if k == b.len() {
                    if ok(v) {
                        for (o, x) in out.iter_mut().zip(v.iter()) {
                            o.insert(*x);
                        }
                    }
                    return;
                }
                for x in &b[k] {
                    v[k] = *x;
                    go(k + 1, b, v, ok, out);
                }
            }
            go(0, b, &mut v, ok, &mut out);
            out
        };
        let mut full: Vec<BTreeSet<i64>> = vec![(0..=3).collect(); n];
        full.push((0..=1).collect());
        let exact = narrow(&full, &|v| base(v) && edges.iter().all(|e| clause(v, *e)));
        let mut b = full;
        loop {
            let before = b.clone();
            b = narrow(&b, &base);
            for e in &edges {
                b = narrow(&b, &|v| base(v) && clause(v, *e));
            }
            if b == before {
                break;
            }
        }
        let forced = reach(n, &edges, &starts);
        let mut rev = edges.clone();
        rev.reverse();
        assert_eq!(forced, reach(n, &rev, &starts), "walk {t}: reversed");
        let mut want: Vec<BTreeSet<i64>> = forced
            .iter()
            .map(|f| (if *f { 1 } else { 0 }..=3).collect())
            .collect();
        want.push((0..=1).collect());
        if exact.iter().any(BTreeSet::is_empty) {
            continue;
        }
        assert_eq!(exact, want, "walk {t}: exact");
        assert_eq!(b, want, "walk {t}: S4");
    }
    assert!(!reach(3, &[(0, 1)], &[0])[2], "CONTROL: a missing edge");
}
