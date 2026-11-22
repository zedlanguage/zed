//! The S4 base on two and three names with cases of several atoms (the S4 base study of round 4,
//! `/home/luke/Work/wt/xst/archive/r4/spec-s4-base/`, `src/pn.rs`, commands `pn` and
//! `pnorders`, with their logs in `logs/`), in the study's sizes and from its seeds.
//!
//! A part is a disjunction of cases and a case a conjunction of atoms `sum k x <= c` (or
//! `>= c`). A live case `a` of a part goes into the base when every live case `o` of the part
//! implies it in the box. Two tests of the implication are compared:
//!
//! - whole case: for each atom `a_j` of `a`, the projection of `o` and `not a_j` together is
//!   empty;
//! - atom-wise (DESIGN L1.39): for each atom `a_j` of `a`, some single atom `o_i` of `o` has an
//!   empty projection with `not a_j`.
//!
//! `pn` counts property P (if `o` implies `a` in box `b` and `o` is live with `phi`, then `a` is
//! live with `phi`) over random draws: the whole-case test breaks it under arc and bounds
//! projection, 3 times in 10,000,000 draws from seed 0x101 and 5 times from 0x202, and never
//! under exact projection; the atom-wise test never breaks it. `pnorders` runs the S4 fixpoint
//! on random systems of three names in six part orders: the whole-case test depends on the order
//! on 2 and 1 systems of 200,000, the atom-wise test on none, and the CONTROL that skips a part
//! with no live case (no zero-live rule) on about 11,500.
//!
//! The two-name model of [`super::s4_model`] keeps a box as one bit mask per name; this one
//! does the same for three names with values `0..5`, so a box is `[u8; 3]` and the boxes of the
//! study's sorted lists map one to one onto these masks.
//!
//! Pieces. The draws of a battery come from one generator in sequence, and a draw takes a
//! number of values that depends on what it draws, so no piece can jump to its first draw. A
//! piece therefore draws and drops the draws before its own (no projection is computed for
//! them: a few dozen generator steps a draw, small beside the projections) and evaluates its
//! own range. The pieces of a battery thus cover exactly the study's sequence, and the counts
//! pinned per piece add up to the study's totals
//! ([`the_pinned_pieces_add_up_to_the_study_counts`]). To change a piece size, change
//! `per_piece` and the list of piece tests; the pieces print their counts, which are pinned
//! again.

use std::array;

use super::Lcg;
use super::s4_model::Pi;
use zed_tests::instances::Rng;

/// Each name takes values in `0..V`.
const V: i64 = 5;

/// The values of names 0, 1 and 2 as bit masks. A draw on two names keeps name 2 at `{0}`,
/// which no atom reads.
type Bx = [u8; 3];

/// `sum k x <= c`, or `>= c` when `ge`, over at most three distinct names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Lin {
    terms: [(usize, i64); 3],
    len: usize,
    c: i64,
    ge: bool,
}

fn lin(terms: &[(usize, i64)], c: i64, ge: bool) -> Lin {
    let mut t = [(0, 0); 3];
    t[..terms.len()].copy_from_slice(terms);
    Lin {
        terms: t,
        len: terms.len(),
        c,
        ge,
    }
}

impl Lin {
    fn terms(&self) -> &[(usize, i64)] {
        &self.terms[..self.len]
    }

    fn holds(&self, p: [i64; 3]) -> bool {
        let s: i64 = self.terms().iter().map(|&(x, k)| k * p[x]).sum();
        if self.ge { s >= self.c } else { s <= self.c }
    }

    fn negate(self) -> Lin {
        Lin {
            c: if self.ge { self.c - 1 } else { self.c + 1 },
            ge: !self.ge,
            ..self
        }
    }
}

fn least(m: u8) -> i64 {
    m.trailing_zeros() as i64
}

fn greatest(m: u8) -> i64 {
    7 - m.leading_zeros() as i64
}

fn values(m: u8) -> impl Iterator<Item = i64> {
    (0..V).filter(move |v| m >> v & 1 == 1)
}

/// The box with the listed values of each name.
fn bx(sets: [&[i64]; 3]) -> Bx {
    sets.map(|vs| vs.iter().fold(0u8, |m, v| m | 1u8 << v))
}

/// Whether value `v` of name `x` has a support for `a` in `d`: `a` holds with `x = v` and each
/// other name at its best value in `d` (the greatest of `k y` for `>=`, the least for `<=`).
fn supported(a: &Lin, d: &Bx, x: usize, v: i64) -> bool {
    let s: i64 = a
        .terms()
        .iter()
        .map(|&(y, k)| {
            if y == x {
                k * v
            } else if a.ge == (k > 0) {
                k * greatest(d[y])
            } else {
                k * least(d[y])
            }
        })
        .sum();
    if a.ge { s >= a.c } else { s <= a.c }
}

/// The projection of `atoms` within `b`, or `None` when it is empty: by enumeration under
/// exact projection; under arc and bounds projection, each atom in turn removes the values of
/// its names with no support (bounds: only the least and greatest), to a fixpoint. Removing a
/// value with no support never removes a point, so `None` from arc or bounds projection means
/// that no point of `b` meets `atoms`.
fn proj(pi: Pi, b: Bx, atoms: &[Lin]) -> Option<Bx> {
    if pi == Pi::Exact {
        return proj_exact(b, atoms);
    }
    let mut d = b;
    loop {
        let mut changed = false;
        for a in atoms {
            for &(x, _) in a.terms() {
                let before = d[x];
                if pi == Pi::Bounds {
                    while d[x] != 0 && !supported(a, &d, x, least(d[x])) {
                        d[x] &= d[x] - 1;
                    }
                    while d[x] != 0 && !supported(a, &d, x, greatest(d[x])) {
                        d[x] &= !(1u8 << greatest(d[x]));
                    }
                } else {
                    // The support of a value of `x` reads the other names only, so removing
                    // values of `x` in this loop leaves the later supports unchanged.
                    for v in values(d[x]) {
                        if !supported(a, &d, x, v) {
                            d[x] &= !(1u8 << v);
                        }
                    }
                }
                changed |= d[x] != before;
                if d[x] == 0 {
                    return None;
                }
            }
        }
        if !changed {
            return Some(d);
        }
    }
}

fn proj_exact(b: Bx, atoms: &[Lin]) -> Option<Bx> {
    let mut out = [0u8; 3];
    for x in values(b[0]) {
        for y in values(b[1]) {
            for z in values(b[2]) {
                if atoms.iter().all(|a| a.holds([x, y, z])) {
                    out[0] |= 1u8 << x;
                    out[1] |= 1u8 << y;
                    out[2] |= 1u8 << z;
                }
            }
        }
    }
    (out[0] != 0).then_some(out)
}

fn with(xs: &[Lin], ys: &[Lin]) -> Vec<Lin> {
    [xs, ys].concat()
}

/// The values of one name: each of `0..V` kept unless `g.next(drop_one_in)` is 0, and one value
/// drawn when none is kept.
fn domain(g: &mut Lcg, drop_one_in: u64) -> u8 {
    let mut m = 0u8;
    for v in 0..V {
        if g.next(drop_one_in) != 0 {
            m |= 1u8 << v;
        }
    }
    if m == 0 { 1u8 << g.next(V as u64) } else { m }
}

/// The study's random atom on names `0..n`: one to three distinct names (a shuffle of the
/// names, its first `k`), coefficients 1 or -1, or 2 and -2 with one chance in three, `c` in
/// `-4..=4`.
fn atom(g: &mut Lcg, n: usize) -> Lin {
    let k = 1 + g.next(n.min(3) as u64) as usize;
    let mut names = [0, 1, 2];
    for i in (1..n).rev() {
        names.swap(i, g.next(i as u64 + 1) as usize);
    }
    let mut terms = [(0, 0); 3];
    for (t, &x) in terms.iter_mut().zip(&names[..k]) {
        let w = if g.next(3) == 0 { 4 } else { 2 };
        *t = (x, [1, -1, 2, -2][g.next(w) as usize]);
    }
    let c = g.next(9) as i64 - 4;
    let ge = g.next(2) == 0;
    Lin {
        terms,
        len: k,
        c,
        ge,
    }
}

fn atoms(g: &mut Lcg, count: u64, n: usize) -> Vec<Lin> {
    (0..count).map(|_| atom(g, n)).collect()
}

// ---------------------------------------------------------------------------------------------
// `pn`: property P over random draws.

/// One draw of `pn`: a box on two or three names, `phi` of one to three atoms, `o` of two or
/// three atoms and `a` of one or two.
struct Draw {
    b: Bx,
    phi: Vec<Lin>,
    o: Vec<Lin>,
    a: Vec<Lin>,
}

fn draw(g: &mut Lcg) -> Draw {
    let n = 2 + g.next(2) as usize;
    let mut b = [1u8; 3];
    for d in &mut b[..n] {
        *d = domain(g, 3);
    }
    let k = 1 + g.next(3);
    let phi = atoms(g, k, n);
    let k = 2 + g.next(2);
    let o = atoms(g, k, n);
    let k = 1 + g.next(2);
    let a = atoms(g, k, n);
    Draw { b, phi, o, a }
}

/// Over `draws` draws from `g`: the draws where the whole-case test finds that `o` implies `a`
/// and `o` is live with `phi`, those of them where `a` is not live with `phi` (P fails), and the
/// same two counts for the atom-wise test.
fn pn(pi: Pi, g: &mut Lcg, draws: usize) -> [usize; 4] {
    let mut t = [0; 4];
    for _ in 0..draws {
        let d = draw(g);
        let negs: Vec<Lin> = d.a.iter().map(|a| a.negate()).collect();
        let whole = negs
            .iter()
            .all(|&na| proj(pi, d.b, &with(&d.o, &[na])).is_none());
        let atom_wise = negs
            .iter()
            .all(|&na| d.o.iter().any(|&oi| proj(pi, d.b, &[oi, na]).is_none()));
        if proj(pi, d.b, &with(&d.phi, &d.o)).is_none() {
            continue;
        }
        let fails = proj(pi, d.b, &with(&d.phi, &d.a)).is_none() as usize;
        if whole {
            t[0] += 1;
            t[1] += fails;
        }
        if atom_wise {
            t[2] += 1;
            t[3] += fails;
        }
    }
    t
}

// ---------------------------------------------------------------------------------------------
// `pnorders`: the S4 fixpoint in six part orders.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Promotion {
    WholeCase,
    AtomWise,
    /// CONTROL: the atom-wise test, and a part with no live case skipped instead of giving the
    /// empty box.
    AtomWiseDeadSkipped,
}

const PROMOTIONS: [Promotion; 3] = [
    Promotion::WholeCase,
    Promotion::AtomWise,
    Promotion::AtomWiseDeadSkipped,
];

/// A system on three names: the range, the base atoms, the parts (each a list of cases, each a
/// list of atoms), and the six part orders the study compares: as written, reversed, and four
/// shuffles.
struct System {
    range: Bx,
    base: Vec<Lin>,
    parts: Vec<Vec<Vec<Lin>>>,
    orders: Vec<Vec<usize>>,
}

fn system(g: &mut Lcg) -> System {
    let mut range = [0u8; 3];
    for d in &mut range {
        *d = domain(g, 4);
    }
    let k = g.next(3);
    let base = atoms(g, k, 3);
    let mut parts = Vec::new();
    for _ in 0..2 + g.next(3) {
        let mut cases = Vec::new();
        for _ in 0..2 + g.next(2) {
            let k = 1 + g.next(3);
            cases.push(atoms(g, k, 3));
        }
        parts.push(cases);
    }
    let k = parts.len();
    let mut orders: Vec<Vec<usize>> = vec![(0..k).collect(), (0..k).rev().collect()];
    for _ in 0..4 {
        let mut o: Vec<usize> = (0..k).collect();
        for i in (1..k).rev() {
            o.swap(i, g.next(i as u64 + 1) as usize);
        }
        orders.push(o);
    }
    System {
        range,
        base,
        parts,
        orders,
    }
}

/// The S4 fixpoint with the parts visited in `order`: each part keeps its live cases (those
/// with a nonempty projection with the base and the promoted cases), promotes once the first
/// live case every live case implies, and narrows the box to the union of the live cases'
/// projections; then the base and promoted cases narrow the box; until nothing changes. A part
/// with no live case gives the empty box (`None`), except under the CONTROL.
fn s4(pi: Pi, s: &System, order: &[usize], promotion: Promotion) -> Option<Bx> {
    let parts = &s.parts;
    let base_with = |promoted: &[Option<usize>]| {
        let mut phi = s.base.clone();
        for (p, c) in promoted.iter().enumerate() {
            if let Some(c) = c {
                phi.extend(&parts[p][*c]);
            }
        }
        phi
    };
    let mut b = s.range;
    let mut promoted: Vec<Option<usize>> = vec![None; parts.len()];
    loop {
        let mut changed = false;
        for &p in order {
            let phi = base_with(&promoted);
            let live: Vec<(usize, Bx)> = parts[p]
                .iter()
                .enumerate()
                .filter_map(|(k, c)| proj(pi, b, &with(&phi, c)).map(|d| (k, d)))
                .collect();
            if live.is_empty() {
                if promotion == Promotion::AtomWiseDeadSkipped {
                    continue;
                }
                return None;
            }
            if promoted[p].is_none() {
                // Whether case `o` implies case `a` in `b`.
                let implies = |o: usize, a: usize| {
                    parts[p][a].iter().all(|aj| {
                        let na = aj.negate();
                        if promotion == Promotion::WholeCase {
                            proj(pi, b, &with(&parts[p][o], &[na])).is_none()
                        } else {
                            parts[p][o]
                                .iter()
                                .any(|&oi| proj(pi, b, &[oi, na]).is_none())
                        }
                    })
                };
                if let Some(a) = live
                    .iter()
                    .map(|l| l.0)
                    .find(|&a| live.iter().all(|l| implies(l.0, a)))
                {
                    promoted[p] = Some(a);
                    changed = true;
                }
            }
            let u = live
                .iter()
                .fold([0u8; 3], |u, (_, d)| array::from_fn(|x| u[x] | d[x]));
            let nb: Bx = array::from_fn(|x| b[x] & u[x]);
            if nb.contains(&0) {
                return None;
            }
            if nb != b {
                b = nb;
                changed = true;
            }
        }
        let nb = proj(pi, b, &base_with(&promoted))?;
        if nb != b {
            b = nb;
            changed = true;
        }
        if !changed {
            return Some(b);
        }
    }
}

/// Over `systems` systems from `g`: the systems with a case of several atoms, and for each
/// promotion of [`PROMOTIONS`] the systems whose fixpoint differs between two of the six orders.
fn pnorders(pi: Pi, g: &mut Lcg, systems: usize) -> [usize; 4] {
    let mut t = [0; 4];
    for _ in 0..systems {
        let s = system(g);
        t[0] += s.parts.iter().flatten().any(|c| c.len() > 1) as usize;
        for (i, promotion) in PROMOTIONS.into_iter().enumerate() {
            let first = s4(pi, &s, &s.orders[0], promotion);
            t[i + 1] += s.orders[1..]
                .iter()
                .any(|o| s4(pi, &s, o, promotion) != first) as usize;
        }
    }
    t
}

// ---------------------------------------------------------------------------------------------
// The batteries, in pieces.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Command {
    /// Counts `[whole-case premises, whole-case P fails, atom-wise premises, atom-wise P
    /// fails]`.
    Pn,
    /// Counts `[systems with a case of several atoms, order-dependent systems under the
    /// whole-case test, under the atom-wise test, under the CONTROL]`.
    PnOrders,
}

struct Battery {
    command: Command,
    pi: Pi,
    seed: u64,
    /// Draws (`Pn`) or systems (`PnOrders`).
    size: usize,
    per_piece: usize,
    /// The study's counts, from its log.
    study: [usize; 4],
    /// The counts of each piece, pinned from the pieces' runs.
    pinned: &'static [[usize; 4]],
}

impl Battery {
    /// Runs piece `j`: the draws or systems `j * per_piece` up to the next piece's first, after
    /// drawing and dropping those before it. Asserts that the atom-wise test never breaks
    /// property P (`Pn`) or depends on the order (`PnOrders`), and the counts pinned for the
    /// piece.
    fn piece(&self, j: usize) {
        let from = j * self.per_piece;
        let to = self.size.min(from + self.per_piece);
        assert!(from < to, "piece {j} starts after the last draw");
        let mut g = Lcg(self.seed);
        let (counts, atom_wise_failures) = match self.command {
            Command::Pn => {
                for _ in 0..from {
                    draw(&mut g);
                }
                let t = pn(self.pi, &mut g, to - from);
                (t, t[3])
            }
            Command::PnOrders => {
                for _ in 0..from {
                    system(&mut g);
                }
                let t = pnorders(self.pi, &mut g, to - from);
                (t, t[2])
            }
        };
        let what = format!(
            "{:?} {:?} seed {:#x}, {from}..{to}",
            self.command, self.pi, self.seed
        );
        eprintln!("{what}: {counts:?}");
        assert_eq!(atom_wise_failures, 0, "{what}: the atom-wise test");
        if let Some(want) = self.pinned.get(j) {
            assert_eq!(counts, *want, "{what}: the pinned counts");
        }
    }
}

// The study's sizes and seeds. The sizes of the pieces are first guesses at under 20 s each in
// a dev build (a draw of `pn` costs about ten small projections, a system of `pnorders` 18 runs
// of the fixpoint); the runs on the VM set them.
//
// Study counts, from the logs (`pn_*.log`, `pnorders_*.log`): arc and bounds projection give
// the same counts on each seed.

const PN_ARC_101: Battery = Battery {
    command: Command::Pn,
    pi: Pi::Arc,
    seed: 0x101,
    size: 10_000_000,
    per_piece: 2_000_000,
    study: [629_846, 3, 614_364, 0],
    pinned: &[],
};

const PN_BOUNDS_101: Battery = Battery {
    pi: Pi::Bounds,
    ..PN_ARC_101
};

const PN_ARC_202: Battery = Battery {
    command: Command::Pn,
    pi: Pi::Arc,
    seed: 0x202,
    size: 10_000_000,
    per_piece: 2_000_000,
    study: [629_323, 5, 613_784, 0],
    pinned: &[],
};

const PN_BOUNDS_202: Battery = Battery {
    pi: Pi::Bounds,
    ..PN_ARC_202
};

const PN_EXACT_303: Battery = Battery {
    command: Command::Pn,
    pi: Pi::Exact,
    seed: 0x303,
    size: 3_000_000,
    per_piece: 500_000,
    study: [188_564, 0, 183_979, 0],
    pinned: &[],
};

const ORDERS_ARC_A1: Battery = Battery {
    command: Command::PnOrders,
    pi: Pi::Arc,
    seed: 0xa1,
    size: 200_000,
    per_piece: 25_000,
    study: [199_616, 2, 0, 11_488],
    pinned: &[],
};

const ORDERS_BOUNDS_A1: Battery = Battery {
    pi: Pi::Bounds,
    ..ORDERS_ARC_A1
};

const ORDERS_ARC_B2: Battery = Battery {
    command: Command::PnOrders,
    pi: Pi::Arc,
    seed: 0xb2,
    size: 200_000,
    per_piece: 25_000,
    study: [199_593, 1, 0, 11_524],
    pinned: &[],
};

const ORDERS_BOUNDS_B2: Battery = Battery {
    pi: Pi::Bounds,
    ..ORDERS_ARC_B2
};

const ORDERS_EXACT_C3: Battery = Battery {
    command: Command::PnOrders,
    pi: Pi::Exact,
    seed: 0xc3,
    size: 30_000,
    per_piece: 5_000,
    study: [29_927, 0, 0, 1_948],
    pinned: &[],
};

const BATTERIES: [&Battery; 10] = [
    &PN_ARC_101,
    &PN_BOUNDS_101,
    &PN_ARC_202,
    &PN_BOUNDS_202,
    &PN_EXACT_303,
    &ORDERS_ARC_A1,
    &ORDERS_BOUNDS_A1,
    &ORDERS_ARC_B2,
    &ORDERS_BOUNDS_B2,
    &ORDERS_EXACT_C3,
];

/// Every battery has one pinned row per piece, and the rows add up to the study's counts: with
/// the pieces' own assertions, the battery reproduces the study. Each piece of a battery must
/// also have its test in the lists below.
#[test]
fn the_pinned_pieces_add_up_to_the_study_counts() {
    for b in BATTERIES {
        let what = format!("{:?} {:?} seed {:#x}", b.command, b.pi, b.seed);
        assert_eq!(
            b.pinned.len(),
            b.size.div_ceil(b.per_piece),
            "{what}: pinned pieces"
        );
        let sum = b
            .pinned
            .iter()
            .fold([0; 4], |s, p| array::from_fn(|i| s[i] + p[i]));
        assert_eq!(sum, b.study, "{what}: the pieces' counts added");
    }
}

macro_rules! pieces {
    ($($test:ident: $battery:ident $j:literal;)*) => {
        $(
            #[test]
            fn $test() {
                $battery.piece($j);
            }
        )*
    };
}

pieces! {
    pn_arc_0x101_piece_0: PN_ARC_101 0;
    pn_arc_0x101_piece_1: PN_ARC_101 1;
    pn_arc_0x101_piece_2: PN_ARC_101 2;
    pn_arc_0x101_piece_3: PN_ARC_101 3;
    pn_arc_0x101_piece_4: PN_ARC_101 4;
    pn_bounds_0x101_piece_0: PN_BOUNDS_101 0;
    pn_bounds_0x101_piece_1: PN_BOUNDS_101 1;
    pn_bounds_0x101_piece_2: PN_BOUNDS_101 2;
    pn_bounds_0x101_piece_3: PN_BOUNDS_101 3;
    pn_bounds_0x101_piece_4: PN_BOUNDS_101 4;
    pn_arc_0x202_piece_0: PN_ARC_202 0;
    pn_arc_0x202_piece_1: PN_ARC_202 1;
    pn_arc_0x202_piece_2: PN_ARC_202 2;
    pn_arc_0x202_piece_3: PN_ARC_202 3;
    pn_arc_0x202_piece_4: PN_ARC_202 4;
    pn_bounds_0x202_piece_0: PN_BOUNDS_202 0;
    pn_bounds_0x202_piece_1: PN_BOUNDS_202 1;
    pn_bounds_0x202_piece_2: PN_BOUNDS_202 2;
    pn_bounds_0x202_piece_3: PN_BOUNDS_202 3;
    pn_bounds_0x202_piece_4: PN_BOUNDS_202 4;
    pn_exact_0x303_piece_0: PN_EXACT_303 0;
    pn_exact_0x303_piece_1: PN_EXACT_303 1;
    pn_exact_0x303_piece_2: PN_EXACT_303 2;
    pn_exact_0x303_piece_3: PN_EXACT_303 3;
    pn_exact_0x303_piece_4: PN_EXACT_303 4;
    pn_exact_0x303_piece_5: PN_EXACT_303 5;
    orders_arc_0xa1_piece_0: ORDERS_ARC_A1 0;
    orders_arc_0xa1_piece_1: ORDERS_ARC_A1 1;
    orders_arc_0xa1_piece_2: ORDERS_ARC_A1 2;
    orders_arc_0xa1_piece_3: ORDERS_ARC_A1 3;
    orders_arc_0xa1_piece_4: ORDERS_ARC_A1 4;
    orders_arc_0xa1_piece_5: ORDERS_ARC_A1 5;
    orders_arc_0xa1_piece_6: ORDERS_ARC_A1 6;
    orders_arc_0xa1_piece_7: ORDERS_ARC_A1 7;
    orders_bounds_0xa1_piece_0: ORDERS_BOUNDS_A1 0;
    orders_bounds_0xa1_piece_1: ORDERS_BOUNDS_A1 1;
    orders_bounds_0xa1_piece_2: ORDERS_BOUNDS_A1 2;
    orders_bounds_0xa1_piece_3: ORDERS_BOUNDS_A1 3;
    orders_bounds_0xa1_piece_4: ORDERS_BOUNDS_A1 4;
    orders_bounds_0xa1_piece_5: ORDERS_BOUNDS_A1 5;
    orders_bounds_0xa1_piece_6: ORDERS_BOUNDS_A1 6;
    orders_bounds_0xa1_piece_7: ORDERS_BOUNDS_A1 7;
    orders_arc_0xb2_piece_0: ORDERS_ARC_B2 0;
    orders_arc_0xb2_piece_1: ORDERS_ARC_B2 1;
    orders_arc_0xb2_piece_2: ORDERS_ARC_B2 2;
    orders_arc_0xb2_piece_3: ORDERS_ARC_B2 3;
    orders_arc_0xb2_piece_4: ORDERS_ARC_B2 4;
    orders_arc_0xb2_piece_5: ORDERS_ARC_B2 5;
    orders_arc_0xb2_piece_6: ORDERS_ARC_B2 6;
    orders_arc_0xb2_piece_7: ORDERS_ARC_B2 7;
    orders_bounds_0xb2_piece_0: ORDERS_BOUNDS_B2 0;
    orders_bounds_0xb2_piece_1: ORDERS_BOUNDS_B2 1;
    orders_bounds_0xb2_piece_2: ORDERS_BOUNDS_B2 2;
    orders_bounds_0xb2_piece_3: ORDERS_BOUNDS_B2 3;
    orders_bounds_0xb2_piece_4: ORDERS_BOUNDS_B2 4;
    orders_bounds_0xb2_piece_5: ORDERS_BOUNDS_B2 5;
    orders_bounds_0xb2_piece_6: ORDERS_BOUNDS_B2 6;
    orders_bounds_0xb2_piece_7: ORDERS_BOUNDS_B2 7;
    orders_exact_0xc3_piece_0: ORDERS_EXACT_C3 0;
    orders_exact_0xc3_piece_1: ORDERS_EXACT_C3 1;
    orders_exact_0xc3_piece_2: ORDERS_EXACT_C3 2;
    orders_exact_0xc3_piece_3: ORDERS_EXACT_C3 3;
    orders_exact_0xc3_piece_4: ORDERS_EXACT_C3 4;
    orders_exact_0xc3_piece_5: ORDERS_EXACT_C3 5;
}

/// The study's claims on a new seed each run: the atom-wise test never breaks property P nor
/// depends on the part order, and under exact projection the whole-case test does neither.
#[test]
fn the_atom_wise_claims_hold_on_a_fresh_seed() {
    let (_, seed) = Rng::fresh("draws of property P and systems of part orders, three names");
    for (pi, draws, systems) in [
        (Pi::Exact, 20_000, 500),
        (Pi::Arc, 100_000, 2_000),
        (Pi::Bounds, 100_000, 2_000),
    ] {
        let p = pn(pi, &mut Lcg(seed), draws);
        let o = pnorders(pi, &mut Lcg(seed), systems);
        eprintln!("seed {seed}, {pi:?}: pn {p:?}, pnorders {o:?}");
        assert_eq!(p[3], 0, "seed {seed}, {pi:?}: atom-wise, property P");
        assert_eq!(o[2], 0, "seed {seed}, {pi:?}: atom-wise, part order");
        if pi == Pi::Exact {
            assert_eq!((p[1], o[1]), (0, 0), "seed {seed}: whole case, exact");
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Named cases from the study's logs.

/// CONTROL (study log `pn_arc_101.log`, the first failure it prints, under arc and bounds
/// projection): the whole-case test breaks property P. Box `x0` in `{0, 3, 4}`, `x1` in
/// `{0, 1, 2, 4}`, `x2` in `{0, 2, 4}`. The projection of `o` and `not a` is empty, `phi` and
/// `o` have a nonempty projection, and `phi` and `a` an empty one. No single atom of `o`
/// implies `a`, so the atom-wise test does not promote `a` (else the study's atom-wise count of
/// failures would not be 0). No point is lost: an empty arc or bounds projection of `o` and
/// `not a` means no point meets them, so a common point of `phi` and `o` would meet `a`, and
/// `phi` and `a` would have a nonempty projection; so `phi` and `o` have no common point.
#[test]
fn control_the_whole_case_test_breaks_property_p_on_a_draw_of_seed_0x101() {
    let b = bx([&[0, 3, 4], &[0, 1, 2, 4], &[0, 2, 4]]);
    let phi = [
        lin(&[(1, -1), (2, -1), (0, 1)], 0, false),
        lin(&[(2, 1), (1, 2)], 2, false),
    ];
    let o = [
        lin(&[(0, 1), (1, 2)], 2, true),
        lin(&[(0, 1), (1, 1)], 0, true),
        lin(&[(2, 1), (1, 2), (0, -1)], 0, false),
    ];
    let a = lin(&[(1, 2), (0, -2)], -1, false);
    let na = a.negate();
    for pi in [Pi::Arc, Pi::Bounds] {
        assert_eq!(proj(pi, b, &with(&o, &[na])), None, "{pi:?}: o implies a");
        assert_ne!(proj(pi, b, &with(&phi, &o)), None, "{pi:?}: o is live");
        assert_eq!(
            proj(pi, b, &with(&phi, &[a])),
            None,
            "{pi:?}: a is not live: P fails"
        );
        for oi in o {
            assert_ne!(proj(pi, b, &[oi, na]), None, "{pi:?}: {oi:?} alone");
        }
    }
    assert_eq!(
        proj_exact(b, &with(&phi, &o)),
        None,
        "phi and o have no common point"
    );
}

/// CONTROL (study log `pnorders_arc_a1.log`, the system it prints): under arc projection the
/// whole-case test gives a fixpoint that depends on the order of the three parts, and the
/// atom-wise test gives one fixpoint in all six orders. The study compared six orders drawn as
/// written, reversed and four shuffles, all among the six permutations here.
#[test]
fn control_the_whole_case_test_depends_on_the_part_order_on_a_system_of_seed_0xa1() {
    let s = System {
        range: bx([&[0, 1, 2, 4], &[0, 3, 4], &[0, 1, 2, 3]]),
        base: vec![lin(&[(0, 1)], 0, true)],
        parts: vec![
            vec![
                vec![
                    lin(&[(1, 1), (2, 1), (0, 2)], 4, true),
                    lin(&[(2, -1), (0, 1), (1, -1)], -3, false),
                    lin(&[(1, 2)], 0, true),
                ],
                vec![lin(&[(0, 2), (1, 2), (2, -1)], 3, true)],
            ],
            vec![
                vec![
                    lin(&[(2, 1), (1, -2), (0, 1)], -3, false),
                    lin(&[(1, -1)], 4, true),
                ],
                vec![lin(&[(2, 1)], 2, true)],
            ],
            vec![
                vec![lin(&[(0, 1), (2, 1)], 3, false)],
                vec![
                    lin(&[(2, 1), (1, 1)], 0, true),
                    lin(&[(2, 1), (0, 1)], 3, true),
                    lin(&[(0, -1), (1, -2)], -2, true),
                ],
                vec![lin(&[(0, -1), (2, 1)], 4, true), lin(&[(0, -1)], 0, true)],
            ],
        ],
        orders: Vec::new(),
    };
    let perms = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let fixpoints = |promotion| {
        let mut outs: Vec<Option<Bx>> = perms
            .iter()
            .map(|o| s4(Pi::Arc, &s, o, promotion))
            .collect();
        outs.sort();
        outs.dedup();
        outs
    };
    let whole = fixpoints(Promotion::WholeCase);
    assert!(whole.len() > 1, "whole case: {whole:?}");
    let atom_wise = fixpoints(Promotion::AtomWise);
    assert_eq!(atom_wise.len(), 1, "atom-wise: {atom_wise:?}");
}
