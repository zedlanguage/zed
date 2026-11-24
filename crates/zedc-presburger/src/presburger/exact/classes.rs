//! A set of integers as a union of [`Classed`] sets, at most one for each class, so that the
//! cover ([`super::cells_cover`]) holds the values of a strided part, and the values left
//! between them, without listing them (row PERF-exact-strided-unlisted).
//!
//! Complexity tradeoff: naive version (before), the values found and the gap of the cover as
//! one [`IntervalSet`], each value of a strided part a range of its own: O(v) pieces for v
//! values, made, cut from the gap, joined, read by the residue questions and charged, so the
//! cover of `w` in `0 <= a, b <= R && (a <= 2 || b >= 8) && a + b == w && w == 2·t` read
//! 8.4M units at R = 10^5 and was refused (`l01_38_presburger::strided`, 2026-11-23: 152,734
//! units at R = 10^3, 827,734 at 10^4, 8,377,793 at 10^5, 12,828,374 at 10^6). Used: one
//! [`Classed`] for each class, O(p) pieces for p ranges, whatever the number of values; the
//! difference of two classes is one class, or `l/m - 1` classes modulo `l` (the lcm of the
//! moduli, `m` the one cut), or listed where listing makes fewer pieces ([`cut`]).
//!
//! The union itself is zedc-lattice's `ClassUnion` (moved there by row
//! LIMITS-classed-listing-per-set, for the reduced product's joins); the operations that charge
//! the cover's meter are here, as [`Charged`].

use std::collections::BTreeMap;

use zedc_lattice::interval::{IntervalSet, Num};
use zedc_lattice::lattice::{Congruence, Lattice};

use super::super::meter::{LISTED, PIECE, Work};
use super::super::{Classed, Refusal};

pub(super) use zedc_lattice::class_union::ClassUnion;

/// The operations of a [`ClassUnion`] that charge the cover's [`Work`] meter, and are refused
/// at its limit.
pub(super) trait Charged: Sized {
    /// The values of `self` not in `other`, exact (see the `impl`).
    fn minus(&self, other: &Self, work: &mut Work) -> Result<Self, Refusal>;
    /// The union as ranges alone, each value of a strided set listed (see the `impl`).
    fn met(&self, work: &mut Work) -> Result<IntervalSet, Refusal>;
}

impl Charged for ClassUnion {
    /// The values of `self` not in `other`, exact: each set of `self` cut by each set of
    /// `other` in turn ([`cut`]), `A \ (B1 ∪ B2) = (A \ B1) \ B2`. The ranges each round leaves
    /// are charged [`PIECE`] units each to `work`, and [`cut`] charges its own classes and
    /// values, so the call is refused at the meter's limit as the cover is. The sets left are
    /// then gathered by class, each class's ranges made one set at once.
    // Complexity tradeoff: naive version, uncharged, each set left joined by [`ClassUnion::add`]
    // in turn: a cut can split one set into `l/m - 1` classes, so the sets grew by that factor
    // for each set of `other`, and joining N sets of one class one at a time rebuilt the class's
    // ranges N times, O(N·P log P) for P ranges. Part 38 of
    // `l01_39_reduced_product::pendants::the_projections_by_pendants_and_of_the_whole_part_are_sound`,
    // `ZED_TEST_SEED=94081993546161772`, ran past 60 s there (gdb: `ClassUnion::add` under
    // `minus` under `cells_cover`; 2 s on origin/main, which lists the gap as ranges and charges
    // each piece). Used: each range made charged [`PIECE`], as main's listed gap charges each
    // piece, so at most `limit / PIECE` ranges are made before a refusal; the ranges of each
    // class gathered and sorted once, O(P log P) in all.
    //
    // Complexity tradeoff: naive version (b76c672c7), every set left cut by each set of `other`
    // and every range left charged each round, O(|self|·|other|) cuts and charges where the
    // classes share no value: a gap of the `m - 1` classes `1..m mod m` less those same
    // classes (the cover of `s == m·t`, `outside` dropping them) made (m - 1)^2 cuts, 6,893
    // units at m = 16 and 140,513 at m = 128, 20.4 times at 8m
    // (`exact::tests::bench::a_gap_of_classes_less_its_classes_is_linear_in_them`). Used: the
    // sets left kept by class (modulus, then residue); a set of `other` of class `r mod m` cuts
    // only the sets whose class meets it, those `r' mod m'` with `r' ≡ r (mod gcd(m, m'))`
    // (`Congruence::meet`, Chinese remainder theorem): the others share no value with it, and
    // `cut` gives them back unchanged. Those are found for each modulus `m'` held, by its
    // residues that are so, or by reading its residues, whichever are fewer:
    // O(D + Σ min(c_{m'}, m'/g)) lookups for D moduli held, `c_{m'}` classes of modulus `m'`,
    // plus the cuts themselves; the m - 1 classes above each meet one, O(m log m) in all. Each
    // round charges the ranges it made, not every range left.
    fn minus(&self, other: &ClassUnion, work: &mut Work) -> Result<ClassUnion, Refusal> {
        if other.is_empty() {
            return Ok(self.clone());
        }
        // The ranges left of each class, by modulus, then residue: every set in the one form of
        // `Classed::new` has a class `Class` with modulus at least 1, never `Bottom`.
        let mut left: BTreeMap<Num, BTreeMap<Num, Vec<Classed>>> = BTreeMap::new();
        let keep = |left: &mut BTreeMap<Num, BTreeMap<Num, Vec<Classed>>>, s: Classed| {
            let Congruence::Class { modulus, residue } = &s.class else {
                unreachable!("a nonempty set has a class")
            };
            let at = left.entry(modulus.clone()).or_default();
            at.entry(residue.clone()).or_default().push(s);
        };
        for s in self.sets() {
            keep(&mut left, s.clone());
        }
        for b in other.sets() {
            let Congruence::Class {
                modulus: mb,
                residue: rb,
            } = &b.class
            else {
                unreachable!("a nonempty set has a class")
            };
            // The classes held that meet `b`'s, taken out to be cut.
            let mut met: Vec<Classed> = Vec::new();
            for (ma, by_residue) in left.iter_mut() {
                let g = ma.gcd(mb);
                let r0 = rb.rem_euclid(&g);
                let step_count = ma.div_floor(&g);
                let few = !matches!(step_count.to_i128(), Some(k) if k < by_residue.len() as i128);
                let hits: Vec<Num> = if few {
                    (by_residue.keys())
                        .filter(|r| r.rem_euclid(&g) == r0)
                        .cloned()
                        .collect()
                } else {
                    let mut hits = Vec::new();
                    let mut r = r0.clone();
                    while &r < ma {
                        if by_residue.contains_key(&r) {
                            hits.push(r.clone());
                        }
                        r = &r + &g;
                    }
                    hits
                };
                for r in hits {
                    met.extend(by_residue.remove(&r).unwrap_or_default());
                }
            }
            left.retain(|_, by_residue| !by_residue.is_empty());
            let mut ranges = 0usize;
            for a in &met {
                for s in cut(a, b, work)? {
                    ranges += s.ranges.len();
                    keep(&mut left, s);
                }
            }
            work.charge(PIECE.saturating_mul(ranges as u64 + 1))?;
        }
        // The ranges of each class gathered, in the order of the classes (no hash order read).
        let mut u = ClassUnion::empty();
        for (modulus, by_residue) in left {
            for (residue, sets) in by_residue {
                let pieces = sets.into_iter().flat_map(|s| s.ranges.into_pieces());
                let ranges = IntervalSet::from_pieces(pieces.collect());
                u.add(Classed::new(
                    ranges,
                    Congruence::new(modulus.clone(), residue),
                ));
            }
        }
        Ok(u)
    }

    /// The union as ranges alone, each value of a strided set a range of its own
    /// ([`Classed::met`]), O(v) for v values: each such value charged [`LISTED`] units of
    /// `work` before any is listed ([`Classed::count`], O(p) for p ranges), the rate
    /// `projection::listed` charges (`block_set`, which keeps the class and lists nothing,
    /// charges one piece a class). Without the charge, a stride of 10^8 values
    /// that the cover now keeps as one class (its progression charged one unit a range, not a
    /// value) was listed here at no cost and ran the test process out of memory (11.6 GB, test
    /// `euclidean_division_and_remainder_by_a_constant_invert_exactly` of
    /// `l01_25_preimage_catalog::entries`, `i mod 10 == 3` on `[0, 10^9]`, 2026-11-23); with
    /// it, the cover is refused at the limit
    /// and the answer is necessary only, as before the classes were kept.
    fn met(&self, work: &mut Work) -> Result<IntervalSet, Refusal> {
        for s in self.sets() {
            if s.strided().is_some() {
                work.charge(LISTED.saturating_mul(s.count()))?;
            }
        }
        Ok(IntervalSet::from_pieces(
            (self.sets().iter())
                .flat_map(|s| s.met().into_pieces())
                .collect(),
        ))
    }
}

/// `a \ b`, as sets each in the one form of [`Classed`]. With `a = R ∩ C` and `b = S ∩ D`,
/// `a \ b = ((R \ S) ∩ C) ∪ ((R ∩ S) ∩ (C \ D))`, and `C \ D` is:
/// - `C`, where `C` and `D` share no value (`C ∩ D` is `Bottom`);
/// - nothing, where `C` lies in `D` (`C ∩ D = C`);
/// - else, with `C ∩ D` the class `t mod l` (Chinese remainder theorem, `Congruence::meet`),
///   `C = r mod m` with `m | l`: `C` is the `l/m` classes `r + i·m mod l`, `i < l/m`, one of
///   which is `t mod l`, so `C \ D` is the other `l/m - 1`.
///
/// In the last case the values of `(R ∩ S) ∩ (C \ D)` are kept as those classes, each met with
/// `R ∩ S`, or listed, whichever makes fewer sets: `l/m - 1` classes against the values listed.
/// Both are exact, so the choice changes only the cost, never the set; it compares the two
/// sizes, with no constant chosen. `R ∩ S` is finite wherever a class other than every integer
/// is made: `D` is then not every integer (else `C` would lie in it), so `S` is finite.
///
/// The classes made are charged [`PIECE`] units each to `work`, and the values listed
/// [`LISTED`] each, before either is made, so that a cut too large for the meter is refused
/// before its work is done ([`Charged::minus`]).
pub(super) fn cut(a: &Classed, b: &Classed, work: &mut Work) -> Result<Vec<Classed>, Refusal> {
    let inside = a.ranges.meet(&b.ranges);
    let met = a.class.meet(&b.class);
    if inside.is_empty() || met == Congruence::Bottom {
        return Ok(vec![a.clone()]);
    }
    let mut out = vec![Classed::new(a.ranges.minus(&b.ranges), a.class.clone())];
    if met != a.class {
        let (
            Congruence::Class {
                modulus: m,
                residue: r,
            },
            Congruence::Class { modulus: l, .. },
        ) = (&a.class, &met)
        else {
            unreachable!("neither class is `Bottom`, shown above")
        };
        // `m` is at least 1 (the one form gives one value every integer as its class, not
        // modulus 0), and `l` a multiple of it.
        let classes = l.div_floor(m);
        let listed = Classed::new(inside.clone(), a.class.clone()).count();
        let k = classes.to_i128().and_then(|k| u64::try_from(k).ok());
        if let Some(k) = k.filter(|k| k - 1 <= listed) {
            work.charge(PIECE.saturating_mul(k))?;
            let mut i = Num::ZERO;
            while i < classes {
                let class = Congruence::new(l.clone(), r + &(&i * m));
                if class != met {
                    out.push(Classed::new(inside.clone(), class));
                }
                i = &i + &Num::ONE;
            }
        } else {
            work.charge(LISTED.saturating_mul(listed))?;
            let left = Classed::new(inside.clone(), a.class.clone()).met();
            let taken = Classed::new(inside, met).met();
            out.push(Classed::plain(left.minus(&taken)));
        }
    }
    out.retain(|s| !s.is_empty());
    Ok(out)
}

#[cfg(test)]
mod tests;
