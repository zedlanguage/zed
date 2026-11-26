//! The residue arithmetic of [`super::Tx::mod_chain_pair`] (in `preimage_ref.rs`): the exact
//! projections of a two-input chain of modular links, such as the catalog family
//! `alternating_moduli` (row PERF-ref-memo-moduli-tables), with no table sized by a modulus.
//! The stage's methods on `Tx` stay in the parent so that this file imports nothing from it
//! (no import cycle, test `s_01f_import_graph`).
//!
//! The terms. The base is an input `x`; link `j` (counted from the base) is
//! `t_j = if g_j { t_(j-1) } else { c_j +- (t_(j-1) mod M_j) }` or the same with the arms
//! swapped. Its guard compares one input, `x` or a second input `y`, with a constant
//! ([`super::Tx::difference_guard`] with an input coordinate), and the mod arm reads the same
//! term as the plain arm. The values of the guard's input that take the mod arm are the link's
//! firing set. Two conditions: (1) on each input the firing sets are nested, `F_1 ⊇ F_2 ⊇ ...`
//! in the order of that input's links; (2) all links on `x` share one modulus `Mx` and all links
//! on `y` share one modulus `My` (the modulus is `|M_j|`: `mod` is Euclidean, and `v mod M` and
//! `v mod -M` agree, `zed_kernel::Prim::Mod`). Any other shape gets `None`, main's path.
//!
//! Why the answer splits into cells and classes (proof).
//! 1. By (1), the values of `x` that fire exactly the first `p` links on `x` form cell `p`:
//!    `x` fires its `k`-th link iff `x ∈ F_k`, and the `k` with `x ∈ F_k` are a prefix
//!    `1..=p` since the sets are nested. The same holds for `y` with cells `q`. Let `jx(p)` be
//!    the position of the `p`-th link on `x` (`jx(0) = 0`), and `jy(q)` alike.
//! 2. Take `x` in cell `p` and `y` in cell `q`, and `r = min(jx(p), jy(q))`. Every link at a
//!    position up to `r` fires (by step 1), so the value is `Phi_r(x)`, the chain with all links
//!    up to `r` fired, followed by the fired links after `r`, which are on one input only: the
//!    links on `x` in `(r, jx(p)]` when `jx(p) > r`, the links on `y` in `(r, jy(q)]` when
//!    `jy(q) > r`, and none when both are `r`.
//! 3. For `r >= 1`, `Phi_r(x)` depends on `x` only through `u = x mod M_1`, the class of `x`:
//!    link 1 fires and its value `c_1 +- (x mod M_1)` reads only `u`. So `Phi_r(u)` is the
//!    class's trajectory.
//! 4. The links on `x` act on residues: `(c +- v mod Mx) mod Mx = (c +- (v mod Mx)) mod Mx`,
//!    a map `rho -> (a +- rho) mod Mx` ([`ResidueMap`]), a bijection of `Z/Mx`. Let `E_j` be
//!    the composition of the maps of the links on `x` up to position `j`. The links on `x` in
//!    `(r, jx(p)]` applied to a value `v` give `c +- rho` with `rho = E_prev(E_r^-1(v mod Mx))`,
//!    `prev` the position of the link on `x` before `jx(p)`: the first of them reads `v mod
//!    Mx`, and each later one reads the residue the earlier ones made. So the value fails the
//!    demand iff `E_r^-1(v mod Mx)` lies in `B_p = E_prev^-1(Bad_p)`, `Bad_p` the residues
//!    `rho` with `c +- rho` outside the wanted set. With `w = E_r^-1(v mod Mx)` the pair fails
//!    iff `w ∈ B_p`. The same holds for `y` with `O_j`, `z`, `C_q` and `My`.
//! 5. So, with `w_q(u) = E_(jy(q))^-1(Phi_(jy(q))(u) mod Mx)` and `z_p(u) =
//!    O_(jx(p))^-1(Phi_(jx(p))(u) mod My)`, the pair (`x` in cell `p` of class `u`, cell `q`)
//!    fails iff: `x ∉ wanted` for `p = q = 0`; `x mod My ∈ C_q` for `p = 0 < q` (`O_0` is the
//!    identity); `x mod Mx ∈ B_p` for `q = 0 < p`; `w_q(u) ∈ B_p` for `0 < jy(q) < jx(p)`; and
//!    `z_p(u) ∈ C_q` for `0 < jx(p) < jy(q)`.
//!
//! The sweep. One pass over the links per class `u` present in a cell `p >= 1` keeps the
//! ordered sets of the `w` of the cells `q` passed so far and of the `z` of the cells `p`
//! passed so far, and tests each against the next `B_p` or `C_q`, kept as sorted disjoint
//! pieces of residues ([`Pieces`]). A cell `y` passes when some pair with it passes, and a
//! value `x` passes when some pair with it passes; the box of the passing values is the
//! projection pair, and it is exact iff no pair inside it fails (a second pass, the same
//! sweep over the kept cells).
//!
//! Complexity tradeoff: with `K` classes (at most `min(M_1, W)`, `W` the number of values of
//! `x`), `n` links and `k` the number of pieces of the demand, the sweeps cost
//! O(K n (log n + k)) time and O(n k + K) space, and no step reads a modulus as a size, so a
//! modulus near 2^62 costs what 64 does once `M_1 >= W`. `K` is a count of values, not a
//! modulus, but a wide domain with a wide `M_1` makes it large (2^40 for `x` in `[-2^61, 2^61]`
//! and `M_1 = 2^40 + 15`), so past [`MOST_CLASSES`], a switchover measured against main's path,
//! the stage gives `None`. The dense tables of the cross-review
//! stage (`monotone_2var_mod`, kept in /home/luke/Work/wt/kept-files/preimg2-moduli-xr) cost
//! O(M_1 Mx + n Mx) and aborted near 2^40. The alternative of one pass for all classes, keys
//! merged where trajectories meet, would drop the factor `K` but needs a set of keys folded by
//! `mod` maps whose cost per fold is not proved; the reviewers' reachable-residue methods
//! (preimg2-xr, I15) cost O(R n^2). The holes of `x` are listed exactly, at a cost of one unit
//! per piece, while the units stay within `(K + K0 + P) (n + 1)` (`K0` the residues mod `My` of
//! the values of `x` that fire no link, `P` the pieces of the cells), the sweeps' own count
//! plus the input's; past that the cell is kept whole and the answer is marked not exact,
//! which is sound (the box still holds every passing point and the relation carries the
//! rest). The budget is never reached when the domain of `x` is no wider than the least
//! modulus (proof at the budget), and it keeps a domain of width 2^62 with a small modulus
//! from listing 2^60 holes; it is the rule forward revision uses (`IntervalSet::cap`: an image
//! bounded by its operands' pieces).
//!
//! Prior work: none found for this exact problem. The 19 searches of the cross-review
//! (preimg2-xr LIT.md) found no O(n log n) method for nested-threshold modular chains; the
//! closest tools are residue arithmetic on `Z/mZ` and persistent sets (Driscoll, Sarnak,
//! Sleator and Tarjan 1989, doi:10.1016/0022-0000(89)90034-2), which this stage does not need
//! because each class keeps its own sets.
//!
//! Tests: `ref_memo::alternating_moduli_at_2_links_gets_its_exact_projections` (the 18 holes),
//! `ref_memo::mod_chains_agree_with_the_interpreter` (random chains against a scan of the box),
//! `ref_memo::mod_chains_with_moduli_near_2_40_and_2_62_are_answered`, and the benches
//! `alternating_moduli_scales`, `alternating_moduli_big_scales` (over `n`) and
//! `mod_chain_modulus_scales` (over the modulus) in `bench::ref_memo`.

use std::collections::BTreeSet;

use zed_collections::intervals;

use zedc_lattice::interval::End::{self, Fin};
use zedc_lattice::interval::IntervalSet;

/// The most classes `K` the sweeps take; past it [`super::Tx::mod_chain_pair`] gives `None` and
/// main's path answers. A switchover measured over the classes, `n` and the modulus (row
/// PERF-ref-memo-moduli-tables, 2026-11-21, chain `alternating_moduli` with moduli
/// `2^62 - 57` and `2^40 - 87`, load about 55): the sweeps cost about 65 ns per class and link
/// (n = 6: 31, 68, 194 ms at K = 2^15, 2^17, 2^19; n = 24: 41, 205, 854 ms), and main's path on
/// the same chains costs 149, 750, 941, 4784 ms at n = 6, 12, 24, 48 on a domain of width 2^62
/// and 3.5 to 7.8 s at n = 6 on widths 2^9 to 2^31. At K = 2^19 the two meet at n = 24 (854
/// against 941 ms). Near the switch neither is cheaper at every `n`, and main's cost is not
/// monotone in the width: at K = 2^19 - 1 the sweeps took 252 ms at n = 6, where main's path
/// took 156 ms on width 2^19 + 1 (3457 ms on 2^21 + 1, 160 ms on 2^41 + 1), and 409 against
/// 445 ms at n = 24; up to K = 2^17 + 1 the sweeps took at most 75 ms at n = 6 against at
/// least 4.5 s for main's path, in every run measured. The rule
/// reads `K` alone, not `n`, so the stage's cost over `n` stays O(n (log n + k)) with no step;
/// a modulus is never read as a size. The classes are at most the width of the domain of `x`,
/// so every catalog family and bench here is below it. Past it main's path never aborts, but
/// its cost over `n` there is its own (the ratio of 32 for 6 to 48 above), not this stage's.
pub(super) const MOST_CLASSES: usize = 1 << 19;

/// Sorted, disjoint pieces `(lo, hi)` of integers, both ends included.
pub(super) type Pieces = Vec<(i128, i128)>;

/// `rho -> (a + rho) mod m`, or `(a - rho) mod m` when `neg`: the map of residues mod `m` that
/// a link `c +- (v mod m)` makes (step 4 of the module comment), and their compositions.
#[derive(Clone, Copy)]
pub(super) struct ResidueMap {
    neg: bool,
    a: i128,
}

impl ResidueMap {
    pub(super) const ID: ResidueMap = ResidueMap { neg: false, a: 0 };

    pub(super) fn at(self, rho: i128, m: i128) -> i128 {
        if self.neg { self.a - rho } else { self.a + rho }.rem_euclid(m)
    }

    /// `self` after `inner`: `a +- (b +- rho) = (a +- b) +- +- rho`.
    pub(super) fn after(self, inner: ResidueMap, m: i128) -> ResidueMap {
        let a = if self.neg {
            self.a - inner.a
        } else {
            self.a + inner.a
        };
        ResidueMap {
            neg: self.neg != inner.neg,
            a: a.rem_euclid(m),
        }
    }

    /// `y = a - rho` gives `rho = a - y`, the map itself; `y = a + rho` gives `rho = y - a`.
    pub(super) fn inverse(self, m: i128) -> ResidueMap {
        if self.neg {
            self
        } else {
            ResidueMap {
                neg: false,
                a: (-self.a).rem_euclid(m),
            }
        }
    }

    /// The image of `set`, residues in `[0, m)`. A piece maps to a piece shorter than `m`,
    /// which splits in two where it passes `m`. O(|set| log |set|).
    pub(super) fn image(self, set: &[(i128, i128)], m: i128) -> Pieces {
        let mut out = Vec::with_capacity(set.len() + 1);
        for &(l, h) in set {
            let (lo, hi) = if self.neg {
                (self.a - h, self.a - l)
            } else {
                (self.a + l, self.a + h)
            };
            let k = lo.div_euclid(m) * m;
            let (lo, hi) = (lo - k, hi - k);
            if hi < m {
                out.push((lo, hi));
            } else {
                out.push((lo, m - 1));
                out.push((0, hi - m));
            }
        }
        normal(out)
    }
}

/// One link, base outward: the input its guard reads (`on_x`), its mod arm `c +- (t mod m)`
/// (`neg` for `-`), and its firing set.
pub(super) struct ModLink {
    pub(super) on_x: bool,
    pub(super) neg: bool,
    pub(super) c: i128,
    pub(super) fire: IntervalSet,
}

impl ModLink {
    pub(super) fn value(&self, v: i128, m: i128) -> i128 {
        let r = v.rem_euclid(m);
        if self.neg { self.c - r } else { self.c + r }
    }

    pub(super) fn map(&self, m: i128) -> ResidueMap {
        ResidueMap {
            neg: self.neg,
            a: self.c.rem_euclid(m),
        }
    }

    /// The residues `rho` in `[0, m)` whose value `c +- rho` is in `unwanted`: the values form
    /// the window `[c, c + m - 1]` (or `[c - m + 1, c]`), met with `unwanted`, then mapped
    /// back. O(k log k) for `k` pieces of `unwanted` in the window.
    pub(super) fn bad(&self, m: i128, unwanted: &IntervalSet) -> Pieces {
        let (lo, hi) = if self.neg {
            (self.c - (m - 1), self.c)
        } else {
            (self.c, self.c + m - 1)
        };
        let hit = unwanted.meet(&IntervalSet::range(End::from(lo), End::from(hi)));
        let out = hit
            .pieces()
            .map(|(a, b)| {
                let (a, b) = (fin(a), fin(b));
                if self.neg {
                    (self.c - b, self.c - a)
                } else {
                    (a - self.c, b - self.c)
                }
            })
            .collect();
        normal(out)
    }
}

/// A finite end as `i128`. Every end here lies within a window of a link or a bounded cell,
/// at most `2^63` from a literal `i64`, so it fits.
fn fin(e: &End) -> i128 {
    match e {
        Fin(v) => v
            .to_i128()
            .expect("an end within 2^64 of an i64 fits in i128"),
        _ => unreachable!("only bounded sets reach here"),
    }
}

/// The pieces of a bounded set; `None` when it is unbounded.
pub(super) fn pieces_of(s: &IntervalSet) -> Option<Pieces> {
    s.pieces()
        .map(|(a, b)| match (a, b) {
            (Fin(a), Fin(b)) => Some((a.to_i128()?, b.to_i128()?)),
            _ => None,
        })
        .collect()
}

pub(super) fn set_of(p: &[(i128, i128)]) -> IntervalSet {
    IntervalSet::from_pieces(
        p.iter()
            .map(|&(a, b)| (End::from(a), End::from(b)))
            .collect(),
    )
}

// The interval helpers below are the library's (`zed_collections::intervals`): this file is a
// second implementation of the stage logic, not of interval arithmetic
// (DRY-sorted-intervals-2026-11-26, group 3).

/// Sorts and merges overlapping or adjacent pieces. O(m log m).
pub(super) fn normal(p: Vec<(i128, i128)>) -> Pieces {
    intervals::coalesce(p)
}

/// Whether some piece of `p` meets `[a, b]`, for `a <= b`. O(log |p|).
fn overlaps(p: &[(i128, i128)], a: i128, b: i128) -> bool {
    intervals::meets(p, &a, &b)
}

pub(super) fn contains(p: &[(i128, i128)], v: i128) -> bool {
    intervals::contains(p, &v)
}

/// Whether some member of `s` lies in `p`. O(|p| log |s|).
pub(super) fn hits(s: &BTreeSet<i128>, p: &[(i128, i128)]) -> bool {
    p.iter().any(|&(a, b)| s.range(a..=b).next().is_some())
}

/// The residues in `[0, m)` outside `p`. O(|p|).
pub(super) fn gaps(p: &[(i128, i128)], m: i128) -> Pieces {
    intervals::complement(p, 0, m - 1)
}

/// The intersection of two piece lists, by a merge. O(|a| + |b|).
pub(super) fn meet(a: &[(i128, i128)], b: &[(i128, i128)]) -> Pieces {
    intervals::intersect(a, b)
}

/// The residues mod `m` of the members of `cell`. A piece of `m` or more members has every
/// residue; a shorter one has one run, split in two where it passes a multiple of `m`.
/// O(|cell| log |cell|).
pub(super) fn residues(cell: &[(i128, i128)], m: i128) -> Pieces {
    let mut out = Vec::new();
    for &(l, h) in cell {
        if h - l + 1 >= m {
            return vec![(0, m - 1)];
        }
        let (a, b) = (l.rem_euclid(m), h.rem_euclid(m));
        if a <= b {
            out.push((a, b));
        } else {
            out.push((a, m - 1));
            out.push((0, b));
        }
    }
    normal(out)
}

/// Whether some member of `cell` has its residue mod `m` in `res`, by the residues of each
/// piece ([`residues`]). O(|cell| log |res|).
pub(super) fn any_in(cell: &[(i128, i128)], res: &[(i128, i128)], m: i128) -> bool {
    cell.iter().any(|&(l, h)| {
        if h - l + 1 >= m {
            return !res.is_empty();
        }
        let (a, b) = (l.rem_euclid(m), h.rem_euclid(m));
        if a <= b {
            overlaps(res, a, b)
        } else {
            overlaps(res, a, m - 1) || overlaps(res, 0, b)
        }
    })
}

/// The members of `cell` whose residue mod `m` is in `res`, as pieces, one unit of `budget` a
/// piece made; `None` when the budget runs out. Each block `[k m, k m + m)` met by a piece of
/// `cell` gives the pieces of `res` shifted into it and clipped, so the work is the pieces
/// made plus at most `2 |res|` empty clips per piece of `cell` (its end blocks; every other
/// block makes a piece for every piece of `res`). O(output + |cell| |res|).
pub(super) fn periodic(
    cell: &[(i128, i128)],
    res: &[(i128, i128)],
    m: i128,
    budget: &mut usize,
) -> Option<Pieces> {
    if res.is_empty() {
        return Some(Vec::new());
    }
    if res == [(0, m - 1)] {
        return Some(cell.to_vec());
    }
    let mut out = Vec::new();
    for &(l, h) in cell {
        for k in l.div_euclid(m)..=h.div_euclid(m) {
            let base = k * m;
            for &(a, b) in res {
                let (s, e) = ((base + a).max(l), (base + b).min(h));
                if s <= e {
                    *budget = budget.checked_sub(1)?;
                    out.push((s, e));
                }
            }
        }
    }
    Some(normal(out))
}

/// A rough count of the pieces [`periodic`] makes, to choose which of two residue conditions
/// to list first: per piece of `cell`, its blocks times the pieces of `res`. O(|cell|).
pub(super) fn estimate(cell: &[(i128, i128)], res: &[(i128, i128)], m: i128) -> i128 {
    let r = res.len() as i128;
    cell.iter()
        .map(|&(l, h)| ((h - l) / m + 2).saturating_mul(r))
        .fold(0i128, i128::saturating_add)
}
