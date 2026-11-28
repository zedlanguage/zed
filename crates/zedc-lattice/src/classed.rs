//! A set of integers written as ranges met with one congruence class ([`Classed`]): the form in
//! which the exact projection of zedc-presburger gives a set whose values are every `m`-th value
//! of some ranges, and in which the preimage of zedc-preimage answers it (row
//! DOMAINS-classed-sets), never listed value by value. Kept here, below both crates, so that
//! each names the one type (moved from zedc-presburger `presburger/refusal.rs`, which
//! re-exports it).

use std::cmp::{max, min};
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use crate::interval::{End, IntervalSet, Num};
use crate::lattice::{Congruence, Lattice};

/// A set of integers written as ranges met with one congruence class: the values of `ranges`
/// that lie in `class`. The set the exact projection gives where its values are every second
/// (or every `m`-th) value of some ranges, as the odd values of `-b..=b`, which ranges alone
/// hold only as one range for each value (PRES-interval-strided-piece).
///
/// Kept in one form for each set ([`Classed::new`]), so that two equal sets compare equal:
/// the class is the least one holding the set (its modulus the gcd of the differences of its
/// members; every integer where that is 1 or the set has one member or none), and the ranges
/// are its maximal runs of members one modulus apart, each from its least member to its
/// greatest. Proof that this is a function of the set alone: the gcd of the differences of a
/// set's members and the residue of any member modulo it depend on the members only, and so
/// do the maximal runs. A class other than every integer is kept only with finite ranges: a set
/// with an infinite range holds two consecutive integers, so its gcd is 1.
// Complexity tradeoff: naive version, every value of the class within the ranges listed as a
// range of its own (`exact::block_set` before PRES-interval-strided-piece), O(v) pieces for v
// values, for every set built and every set read; used: the ranges and the class, O(p) for p
// ranges (one in the benchmarks of `l01_39_scope_relations::xst::s4::bench`), with the values
// listed only where a reader asks for the plain set ([`Classed::met`]), O(v) there, or a join
// meets two different classes ([`Classed::join`]). Design B of the plan row, scored against a
// strided piece inside `IntervalSet` (no one form for equality, every reader of its pieces
// expanding it again).
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Classed {
    /// The ranges, each from a member of the set to a member.
    pub ranges: IntervalSet,
    /// The class; every integer (modulus 1) for a set of ranges alone.
    pub class: Congruence,
    /// The ends of the set where its values repeat without end ([`Tails`], row
    /// CLASSED-periodic-tail), `None` for a set of ranges met with a class alone. Where they
    /// are given, `ranges` and `class` hold a wider set, each tail's ray whole, and the set is
    /// read from the tails past their ends.
    ///
    /// Membership ([`Classed::contains_end`]), `==`, `Hash`, and [`Classed::meet`],
    /// [`Classed::meet_ranges`], [`Classed::join`], [`Classed::join_all`] and
    /// [`Classed::minus`] read the tails; those operations are exact and give the one form
    /// (module `tails`: the tables of the lcm of the periods, the stretch between the ends
    /// listed, as the form keeps it). The readers of the ranges themselves (`met`, `pieces`,
    /// `hull`, `count`, `Display`, `type_text`) read the wider set, which holds the set, and
    /// [`Classed::minus_unlisted`] gives `None` for a set with tails. zedc-presburger still keeps
    /// the cause `Refusal::Repeats` with every set with tails, and its consumers of a difference
    /// still refuse on it; with the exact difference here that refusal can be narrowed, which
    /// is not done in this row. Listing between the ends charges no work here, as zedc-lattice has
    /// no work meter; it costs what [`Classed::join`] and [`Classed::minus`] of two classes cost
    /// without tails (module `tails`, complexity).
    pub tails: Option<Arc<Tails>>,
}

/// One end of a set of integers whose values repeat without end there (row
/// CLASSED-periodic-tail): from `end` on, away from the middle of the set, its members are
/// exactly the values `v` with `have[v mod step]`. The set of the even integers is the tail
/// above with `end` `-inf`, `step` 2 and `have` `[true, false]`.
///
/// Why such ends, and why they are enough. A set of integers definable in Presburger
/// arithmetic, as every projection of a formula of zedc-presburger onto one symbol is, is
/// ultimately periodic in each direction: Ginsburg and Spanier, "Semigroups, Presburger
/// formulas, and languages", Pacific J. Math. 16:285–296, 1966, doi:10.2140/pjm.1966.16.285
/// (read 2026-11-26 from the journal's scanned pages), p. 288: "THEOREM 1.3. The family of
/// Presburger sets of N^n is identical with the family of semilinear sets of N^n.
/// Furthermore, each description is effectively calculable from the other.", with, from its
/// abstract, "a subset of lattice points being semilinear if it is the finite union of cosets
/// of finitely generated sub-semigroups of the set of all lattice points with nonnegative
/// coordinates"; and as restated in V. Marsault and J. Sakarovitch, "Ultimate periodicity of
/// b-recognisable sets: a quasilinear procedure", arXiv:1301.2691 (paperclip full text, read
/// 2026-11-26), lines 10 and 24: "A set of numbers is recognisable if, and only if it is
/// ultimately periodic (UP)", and "Rational sets of \mathbb{N}^d have been characterised by
/// Ginsburg and Spanier as sets definable in the Presburger arithmetic". In dimension 1 a
/// semilinear set is a finite union of progressions `{a + k·p : k >= 0}`, so past the largest
/// `a` it agrees with the residues modulo the lcm of the `p`; on the integers each direction is
/// one such set read on `v` or on `-v`. So a finite part between two such tails holds every
/// projection exactly, which a finite union of ranges met with one class does not (the even
/// integers, `#k0 == 9 * t`). The table is kept at its least period ([`Tail::new`]), as
/// granularities are kept at their minimal period in C. Bettini, S. Mascetti and X. S. Wang,
/// "Supporting temporal reasoning by mapping calendar expressions to minimal periodic sets",
/// arXiv:1110.2213 (paperclip full text, read 2026-11-26), line 256: "each granularity can have
/// different periodical representations and, for a given granularity, it is possible to
/// identify a set of representations that are minimal i.e. adopting the smallest period
/// length"; here the minimal one is what makes the form one for each set (proof at
/// [`Classed::tailed`]).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Tail {
    /// For the tail above, the least value from which it holds, or `-inf` where it holds
    /// every value; for the tail below, the greatest value up to which it holds. A member of
    /// the set where finite.
    pub end: End,
    /// The period, the length of `have`, at least 2.
    pub step: Num,
    /// `have[r]`: whether the values `r mod step` are members. Neither all `true` nor all
    /// `false`.
    pub have: Arc<[bool]>,
}

impl Tail {
    /// The tail from `end` with the residue table `have` modulo `have.len()`, kept at its least
    /// period: the table cut to the shortest block that `have` repeats (zed-collections
    /// `period::least_period`, O(n) for n residues, with its proof). Reading `v mod d` for a
    /// divisor `d` of `n` in place of `v mod n` is the same where `have` is `have[..d]`
    /// repeated, since `(v mod n) mod d == v mod d` for `d` dividing `n`. `have` must hold both
    /// kinds of residue.
    pub fn new(end: End, have: &[bool]) -> Tail {
        debug_assert!(have.contains(&true) && have.contains(&false));
        let d = zed_collections::period::least_period(have);
        Tail {
            end,
            step: Num::from(d as i64),
            have: have[..d].into(),
        }
    }

    /// Whether the residue of `v` is marked: O(1) for a value of a word, and for a kept value
    /// its residue by modular powering ([`Num::rem_euclid`]), nothing as wide as it built.
    pub fn at(&self, v: &Num) -> bool {
        let r = v
            .rem_euclid(&self.step)
            .to_i128()
            .expect("a residue below the table's length");
        self.have[r as usize]
    }
}

/// The tails of a [`Classed`]: one below, one above, or both. A set periodic everywhere has
/// only the tail above, with the end `-inf`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Tails {
    /// The tail toward minus infinity: the values at or below its end.
    pub below: Option<Tail>,
    /// The tail toward plus infinity: the values at or above its end.
    pub above: Option<Tail>,
}

impl Classed {
    /// The set `set`, in the form of [`Classed`]: O(p log p) for p ranges.
    pub fn plain(set: IntervalSet) -> Classed {
        Classed::new(set, Congruence::top())
    }

    /// The values of `ranges` in `class`, in the one form of [`Classed`]. `class` other than
    /// every integer must come with finite ranges (or none). O(p log p) for p ranges.
    pub fn new(ranges: IntervalSet, class: Congruence) -> Classed {
        let empty = || Classed {
            ranges: IntervalSet::empty(),
            class: Congruence::top(),
            tails: None,
        };
        let (m, r) = match class {
            Congruence::Bottom => return empty(),
            Congruence::Class { modulus, residue } => (modulus, residue),
        };
        if m.is_zero() {
            // One value, `r`.
            return if ranges.contains_end(&End::Fin(r.clone())) {
                Classed::plain_unchecked(IntervalSet::point(r))
            } else {
                empty()
            };
        }
        // Complexity tradeoff: naive version, the pieces of a plain set copied out and built
        // into a new set below, O(p) bytes for p pieces at every call, which made a walk that
        // builds a box of a set of `k` pieces at each of `k` levels allocate `Θ(k²)` bytes
        // (`l01_39_reduced_product::if_shortcut::bench::
        // the_walk_over_blocks_whose_names_tests_read_scales` form 6, 55.8 times the bytes of
        // `interval::build` at 8 times the depth, dhat, FAIL-l01-39-bytes-arm-callee-if-shortcut).
        // Used: a plain set whose members lie in no class of modulus above 1 is its own ranges,
        // kept as given, with no byte allocated. Why it is the one form: an `IntervalSet`'s
        // pieces are sorted, disjoint and not adjacent (`IntervalSet::from_normal`), so they are
        // its maximal runs of consecutive integers, which is what the code below gives for
        // modulus 1, and `from_pieces` of them is the same set. [`Classed::wider_class`] reads
        // the pieces only up to the first that rules a wider class out. Given up: nothing.
        // Measured (hm1, 2026-11-24): form 6 9.20 times the instructions and 8.7 times the
        // bytes at 8 times the depth (was 11.9 times the bytes), and
        // `arm_test_through_call::bench::tests_calling_one_deep_callee_scale` 8.73 and 8.1 (was
        // 11.6 times the bytes); test `bench::classed::n_plain_sets_of_n_pieces_scale` (l01_25)
        // 8.31 and 8.0. Negative control, not kept (this test skipped): 63.9, 11.7 and 12.0
        // times the bytes.
        if m == Num::ONE && !Classed::wider_class(&ranges) && plain_shortcut::taken() {
            return Classed::plain_unchecked(ranges);
        }
        // Each range's ends moved in to the nearest members of the class (as
        // `revision::reduce_congruence`), so every end is a member.
        let reduced: Vec<(End, End)> = if m == Num::ONE {
            ranges.into_pieces()
        } else {
            (ranges.pieces())
                .filter_map(|(lo, hi)| {
                    let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                        unreachable!("a class other than every integer comes with finite ranges")
                    };
                    let lo = lo + &(&r - lo).rem_euclid(&m);
                    let hi = hi - &(hi - &r).rem_euclid(&m);
                    (lo <= hi).then_some((End::Fin(lo), End::Fin(hi)))
                })
                .collect()
        };
        // The gcd `g` of the differences of the members from the least one, `a0`: every member
        // is `a0 + (lo_i - a0) + k m` for a range `[lo_i, hi_i]`, so `g` is the gcd of the
        // `lo_i - a0` and, where a range holds two members, of `m`.
        let Some((End::Fin(a0), _)) = reduced.first().cloned() else {
            return match reduced.first() {
                None => empty(),
                // An infinite range holds two consecutive integers: every integer.
                Some(_) => Classed::plain_unchecked(IntervalSet::from_pieces(reduced)),
            };
        };
        let mut g = Num::ZERO;
        for (lo, hi) in &reduced {
            let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                // An infinite end: two consecutive integers, so `m` is 1 and `g` would be 1.
                return Classed::plain_unchecked(IntervalSet::from_pieces(reduced));
            };
            if hi > lo {
                g = g.gcd(&m);
            }
            g = g.gcd(&(lo - &a0));
        }
        if g.is_zero() || g == Num::ONE {
            // One member, or every integer: the ranges alone.
            return Classed::plain_unchecked(IntervalSet::from_pieces(reduced));
        }
        // Every member lies in `a0 mod g`; the maximal runs of members `g` apart. With `g`
        // above `m` every range holds one member, so the runs join single values; with `g`
        // equal to `m`, ranges whose ends are `m` apart.
        let mut runs: Vec<(Num, Num)> = Vec::new();
        for (lo, hi) in reduced {
            let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                unreachable!("every range is finite here, shown above")
            };
            match runs.last_mut() {
                Some((_, end)) if (&lo - &*end) == g => *end = hi,
                _ => runs.push((lo, hi)),
            }
        }
        let class = Congruence::new(g.clone(), a0);
        Classed {
            tails: None,
            ranges: IntervalSet::from_pieces(
                (runs.into_iter())
                    .map(|(lo, hi)| (End::Fin(lo), End::Fin(hi)))
                    .collect(),
            ),
            class,
        }
    }

    /// Whether the members of the plain set `set` lie in a class of modulus above 1, so that
    /// its one form ([`Classed::new`]) has a class other than every integer: it has two members
    /// or more, and each piece is one value (a piece of two values holds two consecutive
    /// integers, whose difference 1 makes the gcd 1), the gcd of their differences from the
    /// first above 1. Proof of the early answers: the gcd only falls as values are added, so a
    /// gcd of 1, an infinite end or a piece of two values settles `false` for the rest.
    ///
    /// Complexity tradeoff: naive version, the walk alone, which reads every piece before the
    /// first wider than one value: a set of `k` single values below one wide range took `O(k)`
    /// at each call, and a name whose holes are tested one at a time from below (`x != 1`,
    /// `x != 2`, `x != 4`, … over `0..=6n`) built such a set at each of its `4n` tests,
    /// `Θ(n²)` in all (`l01_39_scope_relations::xst::holes::bench::
    /// laps_without_the_closing_edge_take_near_linear_time`, 11.1 times the work at 8 times
    /// the size, FAIL-xst-holes-laps-ratio). Used: the walk only when every piece is one
    /// value, which holds exactly when the set has as many members as pieces (each piece holds
    /// at least one integer, and the pieces are disjoint, so the count of members is at least
    /// the count of pieces, with equality exactly when each holds one). The count of members
    /// is [`IntervalSet::members`], kept at each node of the tree: `O(p)` the first time,
    /// `O(log p)` for a set made from one already asked by a change along one path, as each
    /// test's narrowing is; `len` is `O(1)`. So a set with a piece of two values or more is
    /// answered in that time, and the walk runs only on a set of single values, where
    /// [`Classed::new`] builds its strided form in `O(p)` anyway when the answer is `true`,
    /// and the walk stops at the first value outside the first two values' class otherwise.
    /// Measured (b23-band4, job d8 on a Colab VM): pieces walked per call in that bench's open
    /// lap, 43.06 at n = 128 and 128.39 at n = 384 by the walk alone, 0.33 at both with the
    /// check; the bench went from 11.1 to 9.09 and 9.11 times the instructions at 8n (jobs d8
    /// and d9), under the limit of 10.5 and above the preferred 9. Given up:
    /// nothing; the answer is the same. Worst case still `O(p)`: a set of `p` single values
    /// every one in the class of the first two but the last.
    ///
    /// Proof that the answer is that of the walk alone ([`Classed::wider_class_walk`]). The
    /// check returns `false` early only when the count of members is not `Some(p)` for the
    /// `p = set.len()` pieces; otherwise it returns what the walk returns. So it is enough
    /// to show that the walk returns `false` whenever the count is not `Some(p)`.
    /// (1) The count is `None` exactly when an end is infinite ([`IntervalSet::members`]).
    /// An infinite end lies in the first piece (a lower end) or the last (an upper end),
    /// since only the outer ends of a set are infinite. The walk reads the first piece
    /// through `let Some((End::Fin(a0), End::Fin(hi0)))`, which fails, giving `false`, when
    /// either of its ends is infinite; it reads each later piece through `let (End::Fin(lo),
    /// End::Fin(hi))`, which fails the same way, unless an earlier return came first, which
    /// also gives `false` (every return inside the walk is `false`). So with an infinite end
    /// the walk returns `false`. (2) With every end finite, the pieces are disjoint and each
    /// holds `hi - lo + 1 >= 1` integers, so the count is the sum of those, which is `p`
    /// exactly when every piece has `lo == hi`. So a count other than `Some(p)` with every
    /// end finite means some piece has `lo != hi`. The walk returns `true` only on its last
    /// line, reached only after it has read every piece, the first one with `hi0 == a0` and
    /// every later one with `lo == hi` (any other piece returns `false` before), so it
    /// cannot return `true` here. (3) The empty set has count `Some(0)` and `p = 0`, so it
    /// goes to the walk, as before. Test: `tests::the_members_check_gives_the_walks_answer`
    /// (the walk as the reference on random sets of single values, mixed, wide and empty,
    /// with a negative control).
    fn wider_class(set: &IntervalSet) -> bool {
        if set.members() != Some(Num::from(set.len() as u64)) {
            return false;
        }
        Classed::wider_class_walk(set)
    }

    /// The answer of [`Classed::wider_class`] by reading the pieces in order: `O(p)` for `p`
    /// pieces in the worst case, `O(1)` when the first piece is wider than one value.
    fn wider_class_walk(set: &IntervalSet) -> bool {
        let mut pieces = set.pieces();
        let Some((End::Fin(a0), End::Fin(hi0))) = pieces.next() else {
            return false;
        };
        if hi0 != a0 {
            return false;
        }
        let mut g = Num::ZERO;
        for piece in pieces {
            let (End::Fin(lo), End::Fin(hi)) = piece else {
                return false;
            };
            if lo != hi {
                return false;
            }
            g = g.gcd(&(lo - a0));
            if g == Num::ONE {
                return false;
            }
        }
        !g.is_zero()
    }

    /// `set` with every integer as its class, `set` known to be in the one form already.
    fn plain_unchecked(set: IntervalSet) -> Classed {
        Classed {
            ranges: set,
            class: Congruence::top(),
            tails: None,
        }
    }

    /// `wider` with the tails `below` and `above` (row CLASSED-periodic-tail): the set whose
    /// members are, from each tail's end on away from the middle, the values its table marks,
    /// and between the tails' ends the members of `wider`. `wider` must hold the set (each
    /// tail's ray whole), so that every operation that does not read the tails, and every
    /// reader of `ranges` and `class`, gets a set that holds this one, the answer it got before
    /// this row. A tail whose end is `-inf` (above) holds every value and comes alone.
    ///
    /// Proof that the form is one for each set, so that the derived `==` and `Hash` compare
    /// sets. Let S be a set with an end above that repeats and is not every value from some
    /// point on. (1) The table: the least `T` such that S agrees with a set of period `T` above
    /// some value is unique, and any period that S has above some value is a multiple of it (two
    /// periods `p` and `q` of S above a common value give the period `gcd(p, q)` there, as
    /// `v + gcd = v + a·p - b·q` for some `a, b >= 0` with each step staying above that value;
    /// the residues so reached are the same set). [`Tail::new`] cuts the table to its least
    /// period as a word, which is that `T`, since a table of length `n` repeating a block of
    /// length `d` dividing `n` is exactly a set of period `d`. (2) The end: the least value `u`
    /// from which S agrees with that table is a function of S (`exact::ray_from` finds it, with
    /// its proof). The same for the end below on `-v`. (3) `wider` is the form of
    /// [`Classed::new`] of whatever the one caller (zedc-presburger `exact::ended`) gives, and
    /// that is a function of S and the tails' ends: the rays from them whole and the finite part
    /// between. So two forms of one set are equal field by field. Tests:
    /// `tests::tailed_sets_agree_with_the_values_listed` (random tables and ends against the
    /// values listed one by one) and `tests::tailed_sets_of_one_set_are_equal`.
    pub fn tailed(wider: Classed, below: Option<Tail>, above: Option<Tail>) -> Classed {
        debug_assert!(!(below.is_some() && above.as_ref().is_some_and(|t| t.end == End::NegInf)));
        if below.is_none() && above.is_none() {
            return wider;
        }
        Classed {
            tails: Some(Arc::new(Tails { below, above })),
            ..wider
        }
    }

    /// The set with its tails dropped: `ranges` met with `class`, which holds it (each tail's
    /// ray whole).
    pub fn without_tails(&self) -> Classed {
        Classed::new(self.ranges.clone(), self.class.clone())
    }

    /// Whether the set has no value.
    pub fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    /// Whether `v` is a member: in a range and in the class, or past a tail's end and marked
    /// in its table. O(log p) for p ranges.
    pub fn contains(&self, v: i64) -> bool {
        self.contains_end(&End::of(v))
    }

    /// Whether the end `v` is a member; an infinite end is one where the ranges reach it, which
    /// only a set of every integer's class does. A finite `v` past the end of a tail is read
    /// from its table alone, by [`Tail::at`]: O(1) for a word, and for a kept value of many
    /// digits its residue by modular powering, nothing as wide as the value built (the reason
    /// for this row: `3^(2^40)` against the even integers). An infinite end of a set with
    /// tails is answered from `ranges`, the wider set (the hull's end, as before this row).
    // Proof. By [`Classed::tailed`], a member at or past the end of a tail (`v >= u` above,
    // `v <= l` below, any `v` for an end `-inf`) is exactly a value whose residue the table
    // marks, and every other member is a member of `ranges` met with `class`. A value past both
    // ends (the rays meet, `l >= u`) is read from either; they agree there, both being the set.
    pub fn contains_end(&self, v: &End) -> bool {
        if let (Some(tails), End::Fin(n)) = (&self.tails, v) {
            if let Some(above) = &tails.above
                && *v >= above.end
            {
                return above.at(n);
            }
            if let Some(below) = &tails.below
                && *v <= below.end
            {
                return below.at(n);
            }
        }
        self.ranges.contains_end(v)
            && match v {
                End::Fin(n) => self.class.contains(n),
                _ => true,
            }
    }

    /// The modulus of the class and its residue, where it is not every integer.
    pub fn strided(&self) -> Option<(&Num, &Num)> {
        match &self.class {
            Congruence::Class { modulus, residue } if *modulus > Num::ONE => {
                Some((modulus, residue))
            }
            _ => None,
        }
    }

    /// The set as ranges alone, each value of a class other than every integer listed as a
    /// range of its own: the set zedc-presburger `project_each` gave before the class was
    /// kept. O(v) for v values.
    pub fn met(&self) -> IntervalSet {
        match self.strided() {
            Some(_) => IntervalSet::from_pieces(self.listed()),
            None => self.ranges.clone(),
        }
    }

    /// The pieces of the plain set ([`Classed::met`]), in order: the ranges where the class is
    /// every integer, O(p), and otherwise each value, listed, O(v) for v values. For a reader
    /// that needs the pieces themselves, as a test comparing two answers piece by piece.
    // Complexity tradeoff: naive version, the pieces of `met()`, which builds the set's tree
    // from the listed values and takes it apart again, O(v log v) with an allocation per
    // node; it was 95% of the instructions of
    // `s22::remainder_splits_at_their_corners_keep_their_preimages`, 15.8 s of its 20 s
    // (plan row FAIL-s22-remainder-corners-under-load, callgrind on a VM, 2026-11-25). Used:
    // the listed values themselves, O(v), since they are the tree's pieces already (proof at
    // `listed`).
    pub fn pieces(&self) -> std::vec::IntoIter<(End, End)> {
        match self.strided() {
            Some(_) => self.listed().into_iter(),
            None => self.ranges.clone().into_pieces().into_iter(),
        }
    }

    /// Each value of a strided set, as a piece of its own, in increasing order. O(v) for v
    /// values. Proof that these are the pieces of the set they make
    /// (`IntervalSet::from_pieces`), unmerged: the ranges are in order and disjoint, and the
    /// values of one range rise by the modulus `m`, so the list is strictly increasing; any
    /// two members lie in one class modulo `m > 1`, so two consecutive ones differ by `m` or
    /// more, at least 2, and no two pieces touch.
    fn listed(&self) -> Vec<(End, End)> {
        let Some((m, _)) = self.strided() else {
            unreachable!("only a strided set is listed")
        };
        let mut pieces = Vec::new();
        for (lo, hi) in self.ranges.pieces() {
            let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                unreachable!("a class other than every integer comes with finite ranges")
            };
            let mut v = lo.clone();
            while &v <= hi {
                pieces.push((End::Fin(v.clone()), End::Fin(v.clone())));
                v = &v + m;
            }
        }
        pieces
    }

    /// The union. With one class, the union of the ranges in it; else the two sets listed
    /// ([`Classed::met`]) and joined.
    // Complexity tradeoff: the union of two different classes is in general no one class
    // within ranges (the odd values and the multiples of 4), so it is listed, O(v) for v
    // values, as every union was before PRES-interval-strided-piece; one class costs O(p).
    pub fn join(&self, other: &Classed) -> Classed {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }
        if self.tails.is_some() || other.tails.is_some() {
            return combined(self, other, Op::Join);
        }
        if self.class == other.class {
            return Classed::new(self.ranges.join(&other.ranges), self.class.clone());
        }
        Classed::plain(self.met().join(&other.met()))
    }

    /// The union of `sets`, as [`Classed::join`] of each in turn gives it, with the ranges of
    /// each class gathered and made one set at once.
    // Complexity tradeoff: naive version, `set = set.join(&p)` for each of k sets; a join of
    // one class is `Classed::new` over the whole union, O(p) for p ranges so far, so k sets of
    // one range each cost O(k^2) (the union of a disjunction of k blocks, `exact::blocks_set`,
    // before PRES-cover-moduli-two-disjunctions). Used: the ranges of each class listed, then
    // sorted and merged once (`IntervalSet::from_pieces`, O(P log P) for P ranges in all, O(P)
    // bytes) and `Classed::new` once per class, O(P log P) in all. The c sets of different
    // classes are then made one set at once, not joined in turn: a fold of `Classed::join`
    // lists the union so far at each join of two classes, O(c·V) for V values in all (46.9
    // times the instructions per eightfold c, 64 to 512, round-1 cross-review, codex seat;
    // test `joining_many_distinct_classes_scales_and_preserves_the_union`). Used: the class
    // of the union computed once (below), each set already in it kept as its ranges, each
    // set of another class listed once (O(v) for its v values, the cost `Classed::join` has
    // for two classes), then one `from_pieces` and one `Classed::new`: O(P log P + L) for L
    // values listed. The groups are kept in the order their class first came, so the answer
    // does not hang on a hash order.
    //
    // Proof that the union class is right. Let the sets be S_1..S_c, nonempty, each in the
    // one form of `Classed::new`, and b the least end of S_1. The differences of the members
    // of the union are generated (as a group under +) by the differences within each S_i and
    // the differences b_i - b of one member b_i of each (x - y = (x - b_i) + (b_i - b_j) +
    // (b_j - y) for x in S_i, y in S_j). Within S_i, the gcd of the differences is its
    // modulus where S_i is strided (the form keeps the gcd of the members' differences as
    // the modulus), 1 where it is plain with two or more values (a plain set with two
    // values of gcd g > 1 would have been given class g by `Classed::new`), 0 for one value.
    // An infinite end gives two consecutive members, gcd 1. So `step`, the gcd of these, is
    // the gcd of all the differences of the union, and every member is b mod step. Each
    // piece then listed is within the union and holds members only where it is a set's
    // ranges in the union class (kept) or a single listed value or a plain set's range
    // (where step is 1, or the plain set has one value, itself b mod step). So the pieces'
    // union met with the class b mod step is the union of the sets: a kept set's ranges met
    // with its own class give itself, and every other piece holds members only. A set with an
    // infinite end is plain in the form of `Classed::new` (a strided class comes only with
    // finite ranges), so it is kept as its ranges and makes `step` 1, and no infinite set is
    // listed. Test: zedc-presburger
    // `exact::tests::joining_mixed_classes_and_rays_agrees_with_the_fold` (2 000 random lists
    // against the fold of `Classed::join`, rays included); it checks agreement with the fold,
    // so an error the fold shares is not caught.
    pub fn join_all(sets: impl IntoIterator<Item = Classed>) -> Classed {
        // Sets with tails are joined in after the rest, one by one, exact ([`Classed::join`]).
        let (tailed, sets): (Vec<Classed>, Vec<Classed>) =
            sets.into_iter().partition(|c| c.tails.is_some());
        if !tailed.is_empty() {
            let rest = Classed::join_all(sets);
            return tailed.iter().fold(rest, |set, t| set.join(t));
        }
        let merged = by_class(sets);
        if merged.len() <= 1 {
            return (merged.into_iter().next())
                .unwrap_or_else(|| Classed::plain(IntervalSet::empty()));
        }
        // The class of the union, by the proof above: the gcd `step` of each set's own
        // modulus (1 for a plain set of two or more values) and of its least end less `b`.
        let mut class = Congruence::top();
        if let Some((End::Fin(b), _)) = merged[0].ranges.bounds() {
            let mut step = Num::ZERO;
            for set in &merged {
                // The sets are in the order their class first came, not sorted, so a later
                // one may have no least end: two consecutive members, gcd 1.
                let Some((End::Fin(lo), hi)) = set.ranges.bounds() else {
                    step = Num::ONE;
                    break;
                };
                step = step.gcd(&(lo - b));
                if End::Fin(lo.clone()) != *hi {
                    match set.strided() {
                        Some((m, _)) => step = step.gcd(m),
                        None => step = Num::ONE,
                    }
                }
                if step == Num::ONE {
                    break;
                }
            }
            if step > Num::ONE {
                class = Congruence::new(step, b.clone());
            }
        }
        let pieces = (merged.into_iter())
            .flat_map(|set| {
                if set.class == class || set.strided().is_none() {
                    set.ranges.into_pieces()
                } else {
                    set.met().into_pieces()
                }
            })
            .collect();
        Classed::new(IntervalSet::from_pieces(pieces), class)
    }

    /// The intersection: the ranges met, in the meet of the classes (by the Chinese remainder
    /// theorem, `Congruence::meet`), exact, as `(A ∩ C) ∩ (B ∩ D) = (A ∩ B) ∩ (C ∩ D)`.
    pub fn meet(&self, other: &Classed) -> Classed {
        if self.tails.is_some() || other.tails.is_some() {
            return combined(self, other, Op::Meet);
        }
        Classed::new(
            self.ranges.meet(&other.ranges),
            self.class.meet(&other.class),
        )
    }

    /// The intersection with the ranges `other`, in this set's class: `(A ∩ C) ∩ B = (A ∩ B) ∩
    /// C`, exact, with no value listed. O(p log p) for p ranges.
    pub fn meet_ranges(&self, other: &IntervalSet) -> Classed {
        if self.tails.is_some() {
            let other = Classed::plain(other.clone());
            return combined(self, &other, Op::Meet);
        }
        Classed::new(self.ranges.meet(other), self.class.clone())
    }

    /// The hull: every end of the ranges is a member.
    pub fn hull(&self) -> IntervalSet {
        self.ranges.hull()
    }

    /// The number of values, `u64::MAX` for a set with no end or past `u64`. O(p) for p
    /// ranges.
    pub fn count(&self) -> u64 {
        let m = self.strided().map_or(Num::ONE, |(m, _)| m.clone());
        let mut n: u64 = 0;
        for (lo, hi) in self.ranges.pieces() {
            let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                return u64::MAX;
            };
            // `lo` and `hi` are members, so the range holds `(hi - lo) / m + 1` of them.
            let k = (&(hi - lo).div_floor(&m) + &Num::ONE).to_i128();
            let k = k.and_then(|k| u64::try_from(k).ok()).unwrap_or(u64::MAX);
            n = n.saturating_add(k);
        }
        n
    }

    /// The number of ranges of the plain set ([`Classed::met`]), counted, not listed: each
    /// value with a class other than every integer is a range of its own (no two members are
    /// next to each other), else the ranges, maximal in the one form. O(p) for p ranges.
    pub fn listed_len(&self) -> u64 {
        if self.strided().is_some() {
            self.count()
        } else {
            self.ranges.len() as u64
        }
    }

    /// The values of `self` not in `other`, exact. With `A = R ∩ C` and `B = S ∩ D`,
    /// `A \ B = ((R \ S) ∩ C) ∪ ((R ∩ S) ∩ (C \ D))`; `C \ D` is `C` where the classes do not
    /// meet, nothing where `C` lies in `D`, and the one class of `C` left where `D` takes one
    /// of the two classes modulo `lcm(m, k)` into which it cuts `C` (as the even values left
    /// of every integer once the odd ones are taken). Where `C \ D` is more classes than one,
    /// the sets are listed ([`Classed::met`]) and their difference taken.
    // Complexity tradeoff: naive version, both sets listed and subtracted, O(v) for v values,
    // as `projection::Held::push` did before PRES-interval-strided-piece; used: the ranges and
    // the classes, O(p log p) for p ranges, in the cases above, which are the ones the exact
    // projection of a stride makes (a range with the odd values taken, then the even ones),
    // and the listed difference in every other, O(v) as before.
    pub fn minus(&self, other: &Classed) -> Classed {
        if !self.is_empty() && !other.is_empty() && (self.tails.is_some() || other.tails.is_some())
        {
            return combined(self, other, Op::Minus);
        }
        (self.minus_unlisted(other))
            .unwrap_or_else(|| Classed::plain(self.met().minus(&other.met())))
    }

    /// [`Classed::minus`] where it lists no value, O(p log p) for p ranges: `None` where the
    /// difference is no one class within ranges (`C \ D` more classes than one, or the values
    /// outside `other`'s ranges in another class than those inside them), which `minus` lists.
    pub fn minus_unlisted(&self, other: &Classed) -> Option<Classed> {
        if self.is_empty() || other.is_empty() {
            return Some(self.clone());
        }
        // A set with tails is [`Classed::minus`]'s, which lists between the ends.
        if self.tails.is_some() || other.tails.is_some() {
            return None;
        }
        let met = self.class.meet(&other.class);
        // `C \ D`, where it is one class or none (`Bottom`).
        let rest = if met == Congruence::Bottom {
            Some(self.class.clone())
        } else if met == self.class {
            Some(Congruence::Bottom)
        } else {
            match (&self.class, &met) {
                (
                    Congruence::Class {
                        modulus: m,
                        residue: a,
                    },
                    Congruence::Class { modulus: l, .. },
                ) if !m.is_zero() && *l == m * &Num::from(2) => {
                    // `C` is two classes modulo `l`; `D` holds the one `met`, so `C \ D` is
                    // the other, `a + m` or `a` modulo `l`, whichever is not `met`.
                    let shifted = Congruence::new(l.clone(), a + m);
                    Some(if shifted == met {
                        Congruence::new(l.clone(), a.clone())
                    } else {
                        shifted
                    })
                }
                _ => None,
            }
        };
        let rest = rest?;
        // Complexity tradeoff: naive version, always run `minus` and `meet` over all p pieces,
        // O(p) allocations when `self.ranges` and `other.ranges` share the same `Arc<Node>`
        // (common in `Held::push` when the projected stride covers the full finite goal); used:
        // O(1) equality check (`Arc::ptr_eq` inside `IntervalSet::eq`) skips both tree walks.
        if self.ranges == other.ranges {
            return Some(if rest == Congruence::Bottom {
                Classed::plain(IntervalSet::empty())
            } else {
                Classed::new(self.ranges.clone(), rest)
            });
        }
        let outside = Classed::new(self.ranges.minus(&other.ranges), self.class.clone());
        if rest == Congruence::Bottom {
            return Some(outside);
        }
        let inside = self.ranges.meet(&other.ranges);
        // `rest` other than every integer needs finite ranges: `other`'s class is not every
        // integer (else `C` would lie in it), so `other`'s ranges, and their meet, are finite.
        let inside = Classed::new(inside, rest);
        // `Classed::join` lists where the two classes differ.
        (outside.is_empty() || inside.is_empty() || outside.class == inside.class)
            .then(|| outside.join(&inside))
    }

    /// The set as a type a program could write (DESIGN.md sec:diagnostics, "Types in a
    /// message"; row DOMAINS-classed-sets): its ranges as [`IntervalSet::type_text`] writes
    /// them, and where the class is not every integer the refinement `where x mod m == r`
    /// after them, `r` in `0..m` as Zed's `mod` gives it (zed-kernel `Prim::Mod`,
    /// `rem_euclid`). With a name, the text is the type of that binding, `int[3..=993] where
    /// i mod 10 == 3`, written after `i: ` by the caller, with no parentheses, since the
    /// `where` then ends the binding's type; with none, the refinement of the grammar rule
    /// `FieldType` with the bound name `x`, `(x: int[3..=993] where x mod 10 == 3)`, which
    /// stands anywhere a type does. No new syntax: both parse by the rules `Type` and
    /// `FieldType` of `zed/grammar/syntax.peg` (test
    /// `l01_25_preimage_catalog::classed::a_classed_set_prints_as_a_refinement_that_parses`).
    /// The form is the one form of [`Classed::new`] (ranges trimmed to members, the least
    /// class), so two equal sets print the same where they were made by [`Classed::new`].
    /// Where the members listed print no longer than the class ([`Classed::printed_members`]),
    /// they print instead, as `int[1..=1, 4..=4]`. O(p) for p ranges, plus the members where
    /// they print, which are fewer than the class text's characters.
    pub fn type_text(&self, name: Option<&str>) -> String {
        let ranges = self.ranges.type_text();
        let Some((m, r)) = self.strided() else {
            return ranges;
        };
        if let Some(members) = self.printed_members() {
            return members.type_text();
        }
        let x = name.unwrap_or("x");
        let refined = format!("{ranges} where {x} mod {m} == {r}");
        match name {
            Some(_) => refined,
            None => format!("({x}: {refined})"),
        }
    }

    /// The members of a set with a class other than every integer, listed, where their text
    /// is no longer than the class's, `int[1..=1, 4..=4]` (17 characters) against `int[1..=4]
    /// where x mod 3 == 1` (29); `None` where the class prints shorter, or the class is every
    /// integer. The text that a message prints, the shorter one, with no constant chosen;
    /// both texts are compared with the bound name `x`, so that the choice is a function of
    /// the set alone and two equal sets print alike (DESIGN.md "Types in a message").
    /// Complexity tradeoff: naive version, the members listed to compare their text, O(v) for
    /// v values (the class `i mod 10 == 3` over `[0, 10^9]` holds 10^8); used: each member
    /// prints as `a..=a`, five characters at least, so where `5·v` passes the class text's
    /// length the class is shorter and nothing is listed; O(p) for p ranges, and the members
    /// listed only where they are fewer than a fifth of that length.
    pub fn printed_members(&self) -> Option<IntervalSet> {
        let (m, r) = self.strided()?;
        let class = format!("{} where x mod {m} == {r}", self.ranges.type_text());
        if self.count().saturating_mul(5) > class.len() as u64 {
            return None;
        }
        let members = self.met();
        (members.type_text().len() <= class.len()).then_some(members)
    }
}

/// The switch of the plain-set shortcut of [`Classed::new`], for the tests of its callers
/// (VERIFY-classed-wider-class-callers): each runs its own work with the shortcut taken and
/// again with it not taken, and compares the two answers.
///
/// Why the shortcut changes no value (the claim these tests check through every caller): for
/// modulus 1 and a set `S` that `Classed::wider_class` rules out, the full path reaches
/// `IntervalSet::from_pieces(S.into_pieces())` (the gcd `g` is 0 for one member, or 1 once a
/// piece holds two values or two pieces' starts differ by a gcd of 1, or the first end is
/// infinite), and that is `S` as a set: `S`'s pieces are sorted, disjoint and not adjacent
/// (the invariant of `IntervalSet`), so `normal_pieces` returns them unchanged. `IntervalSet`'s
/// `==`, `Hash`, `Display` and `Debug` read the pieces only. What can differ is sharing: the
/// shortcut returns `S`'s own tree, the full path a new one, so a caller that asks
/// `ptr_eq`-style questions (a "changed" flag, a cache keyed by the tree) may do more or less
/// work, and a caller that counts work against a budget could then answer differently. The
/// tests compare whole answers, refusals included, so they would see that.
#[doc(hidden)]
pub mod plain_shortcut {
    use std::cell::Cell;

    /// 0: taken (the default); 1: taken and counted; 2: not taken.
    const TAKEN: u8 = 0;
    const COUNTED: u8 = 1;
    const SKIPPED: u8 = 2;

    thread_local! {
        static MODE: Cell<u8> = const { Cell::new(TAKEN) };
        static COUNT: Cell<u64> = const { Cell::new(0) };
    }

    /// Whether [`super::Classed::new`] takes the shortcut for a set it allows: one read of a
    /// thread-local byte, and a count where a test asked for it.
    pub(super) fn taken() -> bool {
        match MODE.with(Cell::get) {
            TAKEN => true,
            COUNTED => {
                COUNT.with(|c| c.set(c.get() + 1));
                true
            }
            _ => false,
        }
    }

    /// `f` run with the shortcut taken, then with it not taken: both answers, and the count of
    /// calls of [`super::Classed::new`] that took the shortcut in the first run. The mode is
    /// put back to taken even when `f` panics.
    pub fn both<R>(mut f: impl FnMut() -> R) -> (R, R, u64) {
        struct Restore;
        impl Drop for Restore {
            fn drop(&mut self) {
                MODE.with(|m| m.set(TAKEN));
            }
        }
        let _restore = Restore;
        COUNT.with(|c| c.set(0));
        MODE.with(|m| m.set(COUNTED));
        let with = f();
        let count = COUNT.with(Cell::get);
        MODE.with(|m| m.set(SKIPPED));
        let without = f();
        (with, without, count)
    }

    /// Whether the shortcut is switched off on this thread, as in the second run of [`both`]:
    /// a memo of answers reads it so that it asks a question again rather than answer it
    /// with what the shortcut's path gave (`zedc_presburger`'s `memo_off`). O(1).
    pub fn skipped() -> bool {
        MODE.with(Cell::get) == SKIPPED
    }
}

impl PartialEq<IntervalSet> for Classed {
    /// Whether the two sets hold the same values: both in the one form of [`Classed::new`]
    /// and compared, O(p log p) for p ranges, with no value listed. A set with tails is never
    /// a set of ranges: a tail's table marks some residue and not another, so it has holes
    /// without end, which a finite union of ranges does not.
    fn eq(&self, other: &IntervalSet) -> bool {
        self.tails.is_none()
            && Classed::new(self.ranges.clone(), self.class.clone())
                == Classed::plain(other.clone())
    }
}

impl PartialEq<Classed> for IntervalSet {
    /// [`Classed`]'s comparison with a set of ranges, from the other side.
    fn eq(&self, other: &Classed) -> bool {
        other == self
    }
}

impl fmt::Display for Classed {
    /// The ranges as [`IntervalSet`] writes them, `[0..=4]`, where the class is every integer,
    /// and the members so where they print no longer ([`Classed::printed_members`]); else the
    /// refinement of [`Classed::type_text`] with the bound name `x`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.strided(), self.printed_members()) {
            (None, _) => write!(f, "{}", self.ranges),
            (Some(_), Some(members)) => write!(f, "{members}"),
            (Some(_), None) => write!(f, "{}", self.type_text(None)),
        }
    }
}

impl fmt::Debug for Classed {
    /// The ranges as [`IntervalSet`]'s `Debug` writes them where the class is every integer,
    /// so that an answer of ranges alone reads as before row DOMAINS-classed-sets; else both
    /// fields, the class as `r mod m`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(tails) = &self.tails {
            return f
                .debug_struct("Classed")
                .field("ranges", &self.ranges)
                .field("class", &format_args!("{}", self.class))
                .field("tails", tails)
                .finish();
        }
        match self.strided() {
            None => write!(f, "{:?}", self.ranges),
            Some(_) => f
                .debug_struct("Classed")
                .field("ranges", &self.ranges)
                .field("class", &format_args!("{}", self.class))
                .finish(),
        }
    }
}

/// `sets` with those of one class made one ([`Classed::new`] of their ranges joined) and the
/// empty ones left out, in the order each class first comes. Each class found in O(1) expected,
/// O(p log p) for p ranges in all.
fn by_class(sets: impl IntoIterator<Item = Classed>) -> Vec<Classed> {
    let mut at: HashMap<Congruence, usize> = HashMap::new();
    let mut groups: Vec<(Congruence, Vec<(End, End)>)> = Vec::new();
    for c in sets {
        if c.is_empty() {
            continue;
        }
        let i = *at.entry(c.class.clone()).or_insert_with(|| {
            groups.push((c.class.clone(), Vec::new()));
            groups.len() - 1
        });
        groups[i].1.extend(c.ranges.into_pieces());
    }
    (groups.into_iter())
        .map(|(class, pieces)| Classed::new(IntervalSet::from_pieces(pieces), class))
        .filter(|set| !set.is_empty())
        .collect()
}

// Exact meet, union and difference of sets with tails (row CLASSED-periodic-tail), each answer
// in the one form of [`Classed::tailed`], the form zedc-presburger `exact::ended` builds, so
// that a set made by these and the same set read by the cover are equal. `Classed::meet`,
// `join`, `join_all`, `meet_ranges` and `minus` come to [`combined`] where a set has tails. It
// is in this file, not a file of its own, because the two call each other: those operations
// call it, and it calls them on sets without tails (zed-tools `imports`: no import cycle
// between files).
//
// The method. Each set is, far enough up, the values whose residue a table marks: its tail
// above, or a table of one letter (every value, for a ray, or none, for a set bounded above).
// The same below. Far up, the answer is the two tables combined value by value: for ends `u1`
// and `u2`, from `u = max(u1, u2)` up, over a table of length `lcm(T1, T2)` read at `r mod T1`
// and `r mod T2`, cut to its least period (`Table::new`). The same below at the lesser end.
// Between the two ends each set is cut to the stretch and held as a few classes (`within`: its
// tail's residues each a class within the stretch, and its own ranges and class), and the
// operation is done there by the operations of sets without tails (`apply`). Last, the ends
// are moved in to where the answer starts to agree with its tables, which is the one form
// (`normal`).
//
// Complexity. The table of the answer has `lcm(T1, T2)` letters, its exact size before the
// cut, so it is the cost of the answer and not a limit to add: O(lcm) to build and cut
// (zed-collections `period::least_period`). Between the ends the operation is that of sets
// without tails, at their cost: O(p log p) for p ranges where it keeps one class, and where
// the classes of the two sides differ the values of the stretch listed, O(v) for the v values
// of both sets there, as [`Classed::join`] and [`Classed::minus`] list two classes without
// tails. That may be more than the answer's own values (`[0, 10^6)` with the even values past
// it, joined with the odd values from 1, lists the odd values below `10^6` to give
// `[0, +inf)`), as the same union without tails does. The answer's form keeps its values
// between its two ends as plain ranges, each value of a class listed (the form of
// `exact::ended`), O(v) for those v values. The walk that moves an end in is O(1) for each gap
// and each piece of every integer passed, O(T) for each piece of a class passed, and O(lcm) of
// the two tables of the answer past the other end, where a scan compares them. Test:
// `tests::tailed_operations_agree_with_the_values_listed` (random sets against the values
// listed one by one and against the one form built from them); bench: zedc-presburger
// `exact::tests::bench::tailed_operations_scale_with_the_table` (coprime steps, so the table is
// their product).

/// The operation [`combined`] does.
#[derive(Clone, Copy, Debug)]
enum Op {
    /// The values in both.
    Meet,
    /// The values in either.
    Join,
    /// The values in the first and not the second.
    Minus,
}

impl Op {
    fn of(self, a: bool, b: bool) -> bool {
        match self {
            Op::Meet => a && b,
            Op::Join => a || b,
            Op::Minus => a && !b,
        }
    }
}

/// A residue table modulo its length, at its least period, with for each residue the distance
/// back and forward to the nearest residue of each kind, so that the nearest value of a kind is
/// found in O(1).
struct Table {
    have: Vec<bool>,
    /// The length, as a number.
    n: Num,
    /// `back[k][r]`: the least `d >= 0` with `have[(r - d) mod len] == (k == 1)`; `usize::MAX`
    /// where no residue is of that kind.
    back: [Vec<usize>; 2],
    /// `fwd[k][r]`: the least `d >= 0` with `have[(r + d) mod len] == (k == 1)`.
    fwd: [Vec<usize>; 2],
}

impl Table {
    /// The table `have`, cut to its least period (zed-collections `period::least_period`, O(n)),
    /// so that one periodic set has one table: two tables of one set read from residue 0 repeat
    /// one least block, which is that set's least period (proof at [`Classed::tailed`]).
    fn new(mut have: Vec<bool>) -> Table {
        let d = zed_collections::period::least_period(&have);
        have.truncate(d);
        let len = have.len();
        let dist = |kind: bool, back: bool| {
            // Two rounds of the cycle, so that a residue's nearest of a kind may lie across the
            // wrap; the distance is kept from the second round on. O(len).
            let mut out = vec![usize::MAX; len];
            let mut cur = usize::MAX;
            for i in 0..2 * len {
                let r = if back {
                    i % len
                } else {
                    (2 * len - 1 - i) % len
                };
                cur = if have[r] == kind {
                    0
                } else {
                    cur.saturating_add(1)
                };
                if i >= len {
                    out[r] = cur;
                }
            }
            out
        };
        Table {
            n: Num::from(len as u64),
            back: [dist(false, true), dist(true, true)],
            fwd: [dist(false, false), dist(true, false)],
            have,
        }
    }

    /// The one letter of a table of one value or none.
    fn uniform(&self) -> Option<bool> {
        (self.have.len() == 1).then(|| self.have[0])
    }

    fn residue(&self, v: &Num) -> usize {
        let r = v.rem_euclid(&self.n).to_i128();
        r.expect("a residue below the table's length") as usize
    }

    fn at(&self, v: &Num) -> bool {
        self.have[self.residue(v)]
    }

    /// The greatest value at or below `v` whose residue is of the kind `kind`.
    fn last(&self, kind: bool, v: &Num) -> Option<Num> {
        let d = self.back[usize::from(kind)][self.residue(v)];
        (d != usize::MAX).then(|| v - &Num::from(d as u64))
    }

    /// The least value at or above `v` whose residue is of the kind `kind`.
    fn first(&self, kind: bool, v: &Num) -> Option<Num> {
        let d = self.fwd[usize::from(kind)][self.residue(v)];
        (d != usize::MAX).then(|| v + &Num::from(d as u64))
    }

    /// The table of the values negated: `v` marked where `-v` was.
    fn negated(&self) -> Table {
        let len = self.have.len();
        Table::new((0..len).map(|r| self.have[(len - r) % len]).collect())
    }

    fn tail(&self, end: End) -> Tail {
        Tail::new(end, &self.have)
    }
}

/// The table of length `lcm(a, b)` with `op` of `a` at `r mod |a|` and `b` at `r mod |b|`, cut
/// to its least period. Proof that it is the answer's table: for `v` past both ends, `v mod |a|`
/// is `(v mod lcm) mod |a|`, as `|a|` divides the lcm, and the same for `b`.
fn combined_table(a: &[bool], b: &[bool], op: Op) -> Table {
    let (la, lb) = (a.len(), b.len());
    let g = gcd(la, lb);
    let len = (la / g)
        .checked_mul(lb)
        .expect("the table of the answer, its own size, fits in memory");
    Table::new((0..len).map(|i| op.of(a[i % la], b[i % lb])).collect())
}

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The set far up: from the end on, the values its table marks. A tail above gives its own; a
/// set with none is a ray there (one letter `true`, from the ray's start) or bounded (one
/// letter `false`, from one past its greatest value), and never from at or below the end of a
/// tail below, where that tail reads the values.
fn view_above(s: &Classed) -> (End, Vec<bool>) {
    let tails = s.tails.as_deref();
    if let Some(t) = tails.and_then(|t| t.above.as_ref()) {
        return (t.end.clone(), t.have.to_vec());
    }
    let floor = (tails.and_then(|t| t.below.as_ref())).map_or(End::NegInf, |t| t.end.succ());
    match s.ranges.last() {
        None => (End::NegInf, vec![false]),
        Some((lo, End::PosInf)) => (max(lo.clone(), floor), vec![true]),
        Some((_, hi)) => (max(hi.succ(), floor), vec![false]),
    }
}

/// [`view_above`] below: the end up to which the table reads the set. A tail above with the end
/// `-inf` reads every value, so the set below is that tail.
fn view_below(s: &Classed) -> (End, Vec<bool>) {
    let tails = s.tails.as_deref();
    if let Some(t) = tails.and_then(|t| t.below.as_ref()) {
        return (t.end.clone(), t.have.to_vec());
    }
    let above = tails.and_then(|t| t.above.as_ref());
    if let Some(t) = above.filter(|t| t.end == End::NegInf) {
        return (End::PosInf, t.have.to_vec());
    }
    let ceil = above.map_or(End::PosInf, |t| t.end.pred());
    match s.ranges.first() {
        None => (End::PosInf, vec![false]),
        Some((End::NegInf, hi)) => (min(hi.clone(), ceil), vec![true]),
        Some((lo, _)) => (min(lo.pred(), ceil), vec![false]),
    }
}

/// The values of `s` within `[lo, hi]` (both finite), as sets without tails, one for each
/// class ([`by_class`]): each residue a tail marks, a class within the part of the stretch the
/// tail reads, and `s`'s own ranges and class within the part between its tails. Exact: by
/// [`Classed::tailed`], those are its values there. O(T) classes for a table of `T` letters.
fn within(s: &Classed, lo: &End, hi: &End) -> Vec<Classed> {
    let mut sets = Vec::new();
    let tails = s.tails.as_deref();
    let below = tails.and_then(|t| t.below.as_ref());
    let above = tails.and_then(|t| t.above.as_ref());
    let mut periodic = |t: &Tail, a: End, b: End| {
        if a <= b {
            for (r, _) in t.have.iter().enumerate().filter(|(_, m)| **m) {
                let class = Congruence::new(t.step.clone(), Num::from(r as u64));
                sets.push(Classed::new(
                    IntervalSet::range(a.clone(), b.clone()),
                    class,
                ));
            }
        }
    };
    if let Some(t) = above {
        periodic(t, max(t.end.clone(), lo.clone()), hi.clone());
    }
    if let Some(t) = below {
        periodic(t, lo.clone(), min(t.end.clone(), hi.clone()));
    }
    let a = below.map_or(lo.clone(), |t| max(lo.clone(), t.end.succ()));
    let b = above.map_or(hi.clone(), |t| min(hi.clone(), t.end.pred()));
    if a <= b {
        sets.push(Classed::new(
            s.ranges.meet(&IntervalSet::range(a, b)),
            s.class.clone(),
        ));
    }
    by_class(sets)
}

/// `op` of the two unions of sets, none with tails, by the operations of sets without tails:
/// the union joined, the meet of each pair (`(∪A) ∩ (∪B) = ∪(A ∩ B)`), and for the difference
/// each set of the first with every set of the second taken away in turn; the result joined
/// by [`Classed::join_all`].
fn apply(a: &[Classed], b: &[Classed], op: Op) -> Classed {
    let sets: Vec<Classed> = match op {
        Op::Join => a.iter().chain(b).cloned().collect(),
        Op::Meet => (a.iter())
            .flat_map(|x| b.iter().map(move |y| x.meet(y)))
            .collect(),
        Op::Minus => (a.iter())
            .map(|x| {
                let mut left = x.clone();
                for y in b {
                    if left.is_empty() {
                        break;
                    }
                    left = left.minus(y);
                }
                left
            })
            .collect(),
    };
    Classed::join_all(sets)
}

/// `op` of `a` and `b`, at least one with tails, exact, in the one form (the comment above
/// [`Op`]).
fn combined(a: &Classed, b: &Classed, op: Op) -> Classed {
    let ((ua, ta), (ub, tb)) = (view_above(a), view_above(b));
    let ((la, sa), (lb, sb)) = (view_below(a), view_below(b));
    let (u_end, above) = (max(ua, ub), combined_table(&ta, &tb, op));
    let (l_end, below) = (min(la, lb), combined_table(&sa, &sb, op));
    // The stretch between: finite or empty, as a view's end above is finite or `-inf`, and below
    // finite or `+inf`.
    let (lo, hi) = (l_end.succ(), u_end.pred());
    let middle = if lo <= hi {
        apply(&within(a, &lo, &hi), &within(b, &lo, &hi), op)
    } else {
        Classed::plain(IntervalSet::empty())
    };
    normal(l_end, &below, middle, u_end, &above)
}

/// The set that is `below`'s values up to `l_end`, `middle` (no tails, within `(l_end, u_end)`)
/// between, and `above`'s values from `u_end` up, in the one form of `exact::ended`: where the
/// tables are of one letter, no tails and the set as [`Classed::new`] keeps it; else the tail
/// above from `u`, the least value of the set at or above `p`, one more than the greatest value
/// where the set and the table above differ ([`ray_start`]); the same below on the values
/// negated; one tail over every value (end `-inf`) where the set is its table everywhere; both
/// tails over a wider set of every integer where the two ends meet; and else the wider set
/// `(-inf, l] ∪ (E ∩ (l, u)) ∪ [u, +inf)` as plain ranges. Each is a function of the set alone
/// (proof at `exact::ended` and [`Classed::tailed`]), so the form is.
fn normal(l_end: End, below: &Table, middle: Classed, u_end: End, above: &Table) -> Classed {
    let ray = |lo: End, hi: End| Classed::plain(IntervalSet::range(lo, hi));
    if let (Some(b), Some(a)) = (below.uniform(), above.uniform()) {
        let mut set = middle;
        if a {
            set = set.join(&ray(u_end, End::PosInf));
        }
        if b {
            set = set.join(&ray(End::NegInf, l_end));
        }
        return set;
    }
    let whole = |t: &Table| {
        let top = Classed::plain(IntervalSet::top());
        Classed::tailed(top, None, Some(t.tail(End::NegInf)))
    };
    let u = match above.uniform() {
        None => match ray_start(above, &u_end, &middle, &l_end, below) {
            None => return whole(above),
            u => u,
        },
        Some(_) => None,
    };
    let l = match below.uniform() {
        None => {
            let negated = Classed::new(
                middle.ranges.neg(),
                match &middle.class {
                    Congruence::Class { modulus, residue } => {
                        Congruence::new(modulus.clone(), -residue)
                    }
                    c => c.clone(),
                },
            );
            let (b, a) = (below.negated(), above.negated());
            match ray_start(&b, &-&l_end, &negated, &-&u_end, &a) {
                None => return whole(below),
                l => l.map(|l| -&l),
            }
        }
        Some(_) => None,
    };
    let fin = |v: &Num| End::Fin(v.clone());
    if let (Some(l), Some(u)) = (&l, &u)
        && &(l + &Num::ONE) >= u
    {
        let top = Classed::plain(IntervalSet::top());
        return Classed::tailed(top, Some(below.tail(fin(l))), Some(above.tail(fin(u))));
    }
    let lo = l.as_ref().map_or(End::NegInf, |l| fin(&(l + &Num::ONE)));
    let hi = u.as_ref().map_or(End::PosInf, |u| fin(&(u - &Num::ONE)));
    let between = IntervalSet::range(lo.clone(), hi.clone());
    let mut pieces: Vec<(End, End)> =
        (Classed::new(middle.ranges.meet(&between), middle.class.clone()).pieces()).collect();
    listed(above, max(u_end, lo.clone()), hi.clone(), &mut pieces);
    listed(below, lo, min(l_end, hi), &mut pieces);
    if let Some(l) = &l {
        pieces.push((End::NegInf, fin(l)));
    }
    if let Some(u) = &u {
        pieces.push((fin(u), End::PosInf));
    }
    let wider = Classed::plain(IntervalSet::from_pieces(pieces));
    Classed::tailed(
        wider,
        l.as_ref().map(|l| below.tail(fin(l))),
        u.as_ref().map(|u| above.tail(fin(u))),
    )
}

/// The values of `[a, b]` that `t` marks, pushed as pieces: the stretch whole for a table of
/// one `true`, nothing for one `false`, and else each marked value. A table of more letters is
/// listed only between its view's end and the end of the answer's tail on that side, fewer
/// than its length of values: the end above `u` is less than `p + T` (the next marked value
/// from `p`), and `p` is at most the view's end `u_end`, as the walk compares from below it
/// (the same below).
fn listed(t: &Table, a: End, b: End, pieces: &mut Vec<(End, End)>) {
    if a > b {
        return;
    }
    match t.uniform() {
        Some(true) => pieces.push((a, b)),
        Some(false) => {}
        None => {
            let (End::Fin(a), End::Fin(b)) = (a, b) else {
                unreachable!("a table of two kinds is listed between finite ends");
            };
            let mut v = a;
            while v <= b {
                if t.at(&v) {
                    pieces.push((End::Fin(v.clone()), End::Fin(v.clone())));
                }
                v = &v + &Num::ONE;
            }
        }
    }
}

/// For [`normal`], with `above` of two kinds: the least value `u` of the set at or above `p`,
/// one more than the greatest value where the set and `above` differ; `None` where they never
/// differ. The set below `u_end` is `middle` within `(l_end, u_end)` and `below`'s values up to
/// `l_end`.
fn ray_start(
    above: &Table,
    u_end: &End,
    middle: &Classed,
    l_end: &End,
    below: &Table,
) -> Option<Num> {
    let d = last_differing(above, u_end, middle, l_end, below)?;
    Some(
        (above.first(true, &(&d + &Num::ONE)))
            .expect("a table of two kinds marks a value at or above any"),
    )
}

/// The greatest value below `u_end` where the set differs from `above` (see [`ray_start`]).
/// Walk: from `u_end - 1` down through the pieces of `middle` and the gaps between them, each in
/// O(1) by the table's distances, or O(T) for a piece of a class ([`differs_in`]); then past
/// `l_end`, where the set is `below`, a scan of at most the lcm of the two tables' lengths, as
/// two different periodic sets differ within any run of their periods' lcm.
fn last_differing(
    above: &Table,
    u_end: &End,
    middle: &Classed,
    l_end: &End,
    below: &Table,
) -> Option<Num> {
    let End::Fin(u) = u_end else {
        // `-inf`: the table reads every value.
        return None;
    };
    let mut cur = u - &Num::ONE;
    if End::Fin(cur.clone()) > *l_end {
        let step = middle.strided();
        for (a, b) in middle.ranges.pieces().rev() {
            let (End::Fin(a), End::Fin(b)) = (a, b) else {
                unreachable!("the stretch between the ends is finite");
            };
            // The gap `(b, cur]`, no member: a marked value there differs.
            let x = above.last(true, &cur).expect("a table of two kinds");
            if &x > b {
                return Some(x);
            }
            if let Some(x) = differs_in(above, a, b, step) {
                return Some(x);
            }
            cur = a - &Num::ONE;
        }
        let x = above.last(true, &cur).expect("a table of two kinds");
        if End::Fin(x.clone()) > *l_end {
            return Some(x);
        }
        let End::Fin(l) = l_end else {
            unreachable!("an end below under a finite value is finite");
        };
        cur = l.clone();
    }
    if below.have == above.have {
        return None;
    }
    let (lb, la) = (below.have.len(), above.have.len());
    let span = (lb / gcd(lb, la)) * la;
    let (mut rb, mut ra) = (below.residue(&cur), above.residue(&cur));
    for k in 0..span {
        if below.have[rb] != above.have[ra] {
            return Some(&cur - &Num::from(k as u64));
        }
        rb = (rb + lb - 1) % lb;
        ra = (ra + la - 1) % la;
    }
    unreachable!("two different least-period tables differ within the lcm of their lengths")
}

/// The greatest `x` in `[a, b]`, a piece of a set (its values those of `step`'s class there, or
/// every value where `step` is `None`), where membership and `t` differ. With a class `r mod m`:
/// a value `t` marks out of the class (for each marked residue `s` the greatest `x <= b` with
/// `x ≡ s (mod T)`, or the one `T` below it where `x` is in the class and `T` is no multiple of
/// `m`, as `x - T` is then out of it; none where `m` divides `T`, as then all such `x` are in it),
/// or a value of the class `t` does not mark (each unmarked `s` met with the class by the Chinese
/// remainder theorem, [`Congruence::meet`]). O(T).
fn differs_in(t: &Table, a: &Num, b: &Num, step: Option<(&Num, &Num)>) -> Option<Num> {
    let Some((m, r)) = step else {
        return t.last(false, b).filter(|x| x >= a);
    };
    let n = &t.n;
    let divides = n.rem_euclid(m).is_zero();
    let r = &r.rem_euclid(m);
    let mut best: Option<Num> = None;
    for (s, &mark) in t.have.iter().enumerate() {
        let s = Num::from(s as u64);
        let x = if mark {
            let x = b - &(b - &s).rem_euclid(n);
            if x.rem_euclid(m) != *r {
                Some(x)
            } else if !divides {
                Some(&x - n)
            } else {
                None
            }
        } else {
            match Congruence::new(n.clone(), s).meet(&Congruence::new(m.clone(), r.clone())) {
                Congruence::Class { modulus, residue } => {
                    Some(b - &(b - &residue).rem_euclid(&modulus))
                }
                Congruence::Bottom => None,
            }
        };
        if let Some(x) = x
            && &x >= a
            && best.as_ref().is_none_or(|y| &x > y)
        {
            best = Some(x);
        }
    }
    best
}

#[cfg(test)]
mod tests;
