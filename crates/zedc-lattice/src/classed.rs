//! A set of integers written as ranges met with one congruence class ([`Classed`]): the form in
//! which the exact projection of zedc-presburger gives a set whose values are every `m`-th value
//! of some ranges, and in which the preimage of zedc-preimage answers it (row
//! DOMAINS-classed-sets), never listed value by value. Kept here, below both crates, so that
//! each names the one type (moved from zedc-presburger `presburger/refusal.rs`, which
//! re-exports it).

use std::collections::HashMap;
use std::fmt;

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
    /// gcd of 1, an infinite end or a piece of two values settles `false` for the rest. O(1) for
    /// a set whose first piece is wider than one value, O(p) at most for p pieces; nothing is
    /// allocated but the iterator's stack, O(log p).
    fn wider_class(set: &IntervalSet) -> bool {
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
        }
    }

    /// Whether the set has no value.
    pub fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    /// Whether `v` is a member: in a range and in the class. O(log p) for p ranges.
    pub fn contains(&self, v: i64) -> bool {
        self.ranges.contains(v) && self.class.contains(&Num::from(v))
    }

    /// Whether the end `v` is a member; an infinite end is one where the ranges reach it, which
    /// only a set of every integer's class does.
    pub fn contains_end(&self, v: &End) -> bool {
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
        let Some((m, _)) = self.strided() else {
            return self.ranges.clone();
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
        IntervalSet::from_pieces(pieces)
    }

    /// The pieces of the plain set ([`Classed::met`]), in order: the ranges where the class is
    /// every integer, O(p), and otherwise each value, listed, O(v) for v values. For a reader
    /// that needs the pieces themselves, as a test comparing two answers piece by piece.
    pub fn pieces(&self) -> std::vec::IntoIter<(End, End)> {
        self.met().into_pieces().into_iter()
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
        let merged: Vec<Classed> = (groups.into_iter())
            .map(|(class, pieces)| Classed::new(IntervalSet::from_pieces(pieces), class))
            .filter(|set| !set.is_empty())
            .collect();
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
        Classed::new(
            self.ranges.meet(&other.ranges),
            self.class.meet(&other.class),
        )
    }

    /// The intersection with the ranges `other`, in this set's class: `(A ∩ C) ∩ B = (A ∩ B) ∩
    /// C`, exact, with no value listed. O(p log p) for p ranges.
    pub fn meet_ranges(&self, other: &IntervalSet) -> Classed {
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
}

impl PartialEq<IntervalSet> for Classed {
    /// Whether the two sets hold the same values: both in the one form of [`Classed::new`]
    /// and compared, O(p log p) for p ranges, with no value listed.
    fn eq(&self, other: &IntervalSet) -> bool {
        Classed::new(self.ranges.clone(), self.class.clone()) == Classed::plain(other.clone())
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

#[cfg(test)]
mod tests;
