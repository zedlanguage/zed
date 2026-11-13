//! The exact answer of rows over atoms each confined to a finite union of ranges, found by
//! joining tables of the rows' partial sums, in alternation with the solver
//! (PRES-overlap-fast, question A87).
//!
//! A formula such as `(y[i] == 0 || y[i] == w[i])` for each i, with `y[0] + .. + y[a-1] == t1`
//! and `y[b] + .. + y[k-1] == t2` (b < a), is two subset sums that share the atoms `y[b..a]`.
//! The solver searches its disjunctions greedily and refuses where its choices meet no point
//! (`overlap_rows` decided: 57.7M instructions at k = 8; refused after 4,378M at k = 16,
//! 27,741M at k = 32 and 209,064M at k = 64). The overlap gives a faster path: the atoms fall
//! into groups by the rows they appear in (here `{t1}`, `{t1, t2}` and `{t2}`), and the rows
//! are met by joining one table per group, each the set of the group's possible sums on its
//! rows.
//!
//! The method:
//! - each atom's signature is the set of rows it appears in; atoms of one signature form a
//!   group. A group's rows fall into classes of proportional coefficients, and a vector of
//!   class sums is one integer key (one digit per class, mixed radix). The group's table is
//!   the set of keys of its sums over all values of its atoms, a bitset ([`Set`]), built one
//!   atom at a time as the union of the table so far shifted by each value's key (Bellman's
//!   dynamic program for subset sum). A range of n values is added in log n shifts and unions
//!   by doubling, and each table keeps only the keys that the atoms after it can still bring
//!   to the rows' targets (the bound pruning of Horowitz and Sahni, [`Group::window`]);
//! - the groups are joined in the order of their signatures (rows numbered as the formula
//!   gives them). Each layer is the set of keys of the sums on the rows still open, those
//!   with a group before and a group after; a row closes at its last group, where it must
//!   meet its relation. An equation that closes is met by looking up the one sum it needs on
//!   the other side, not by trying every pair (meet in the middle: Horowitz and Sahni), and
//!   where the layer and the group each have one digit the join is a shift or a reflection
//!   and an intersection of whole words ([`Plan::word_join`]). In general the join is bucket
//!   elimination over the rows (Dechter) with the groups as its buckets;
//! - a projection is a pass back over the same joins, which marks the keys of each layer that
//!   some later choice completes, and then, inside each group, the prefix sums and the values
//!   of each atom that a marked key completes. A point is read off the marks.
//!
//! Every answer is exact: no point, a point, or each atom's set of values over all points.
//! Where it applies the solver's answer is never finer, so no answer becomes coarser.
//!
//! The parity example of A87 (`a1 + a2 + c + d == 4`, `b1 + b2 + c + d == 3`, the `a`s and `b`s
//! over {0, 2}, `c` and `d` over {0, 1}) shows why the sums cannot be decided one at a time:
//! each value of `c` and of `d` is possible in each sum alone. Here `c + d` is the table of the
//! group `{c, d}`, and its join with the other two keeps no key.
//!
//! Cost. A table holds at most the number of assignments of its atoms (2^g for g two-way
//! atoms) and at most one key per value of its box, the product over its classes of the range
//! of their sums. It is held as words of 64 keys and as intervals of keys that are all in it
//! ([`Set`]), and an operation on it costs its words that are not full plus its intervals.
//! Adding an atom of r ranges of n values each costs O(r · log n) operations on the table, so a
//! group of g atoms whose sums span W keys costs O(g · log n · W/64) at most, and a family of k
//! atoms whose groups' sums grow as k times the largest weight costs O(k² · w/64) at most for
//! weights of w keys: pseudo-polynomial. With binary weights the class holds subset sum, which
//! is NP-complete (Karp), so no method is polynomial in the bits of the weights unless P = NP,
//! and none is O(n log n) in general. The overlap gives the faster path where the sums of a
//! group are dense: once a group has enough atoms, every sum in the middle of its range is
//! reached (Galil and Margalit), those keys are a few intervals, and only the words near the
//! ends of the range are not full. A table then costs O(1) per operation, about the same at
//! every k, and a family of k atoms costs O(k · log n) operations. Measured (instructions,
//! decide): `overlap_rows` costs 1.83M at k = 64, 13.0M at k = 512 and 25.3M at k = 1,024
//! (7.10 times from 64 to 512); with words alone (round 1 below) it cost 1.87M, 34.0M and 341M.
//! From k = 8 its cost grows 2.06, 2.34 and 2.23 times per doubling of k (10.70 times from 8 to
//! 64, past the limit of 10.5: the solver's reading of the formula is 60% of the cost at k = 8,
//! and, inferred, the sums of a group turn from sparse to dense), and 1.97, 1.89 and 1.90 from
//! 64 to 512. Subset sum with no point costs 1.21M at k = 64, 9.91M at k = 512 and 20.0M at
//! k = 1,024.
//! A range of 0..1e9 makes a table of up to 1.6·10^7 words where the solver may answer at
//! once by its bounds.
//!
//! That is why the method runs in alternation with the solver (after Levin's universal
//! search, which runs two methods with doubling allowances, the first to finish answering).
//! Before any table is built, a bound on the method's work is computed from the ranges alone
//! ([`Plan::bound`]): each table bounded by its keys and its words, as if none were full, each
//! operation by the charge it is given, and the join's pairs from these. The bound is not
//! proved: a set can hold more intervals than it would hold words where an intersection or a
//! clip cuts intervals short, and a run that exceeds its allowance stops, leaving the answer to
//! the solver; no measured run did. Where the bound is at most [`FIRST`] · [`RATE`] times the
//! formula's size, the method runs first and alone, with the bound, but at most [`FIRST`] times
//! the size, as its allowance: the intervals keep most runs far below their bound
//! (`overlap_rows` at k = 1,024, whose bound is past [`FIRST`] per unit of size, answers in
//! this first run). Otherwise, or where that run stops, the solver runs, each system it is
//! asked charging its number of terms, and when the charge reaches the bound over [`RATE`] the
//! method runs once more, with the whole bound as its allowance. When it answers, the solver is
//! left at once and its answer dropped; a bound past `u64` never runs. The work units of both
//! sides are counts, so the answer and its cost are the same at every run. [`RATE`] is set
//! where the method's whole run costs about what the solver spent before it, so a question
//! costs at most about twice the cheaper of the two. Building the plan costs more than main
//! spends on some questions the solver settles by its bounds, so a floor of the bound, read
//! from the ranges of the atoms that are on one row alone ([`Rows::floor`], O(a + e)), comes
//! first: where it is past [`FIRST`] · [`RATE`] times the size, the plan is built only when the
//! charge reaches the floor over [`RATE`], and the method then runs when the charge reaches
//! the plan's bound over [`RATE`], as before. On `wide` the bound is about 10^17 and the floor
//! 2.8·10^9 at k = 4, so neither the plan nor the method is ever built or run: 683.1K to 683.9K
//! instructions decided at k = 4 against 690.3K to 690.9K on main (three runs each); building
//! the plan at once cost 695.6K to 696.3K, 0.8% past main.
//!
//! Two other schedules were measured. Rerunning the method each time the charge doubles, from
//! an allowance of the formula's size, cost at most 5% more than the solver alone but reran
//! the method from the start at each doubling: `overlap_rows` decided at k = 64 cost 33,600M,
//! and subset sum with no point was refused from k = 14 on, where its tables need 2.4M
//! instructions. Running it at each doubling of the charge, with [`RATE`] times the charge as
//! its allowance (round 2 below), ran it on `wide`, where it never finishes, and cost 1.097
//! times the solver alone there (764.6K instructions against 697.5K decided at k = 4).
//!
//! The six rounds of PRES-disj-cost-xr (2026-11-11) tried endpoint reports, a rank table and a
//! queue inside the search, and a binary search over the points of the hull after a refusal;
//! each kept the greedy search and gained a constant factor at most (5.7 at best), and on
//! `overlap_rows` some cost more. Pisinger's balanced subset sum (A87 option B) decides one sum
//! in O(kW) and does not join two; deciding each sum alone cannot decide the parity example.
//! The join of group tables is chosen because its cost is set by the number of distinct sums
//! of each group, which the overlap keeps small: the shared group is joined once with each
//! side by lookups instead of being searched under every choice of the other atoms. Its first
//! version kept each table as a sorted list of keys (`overlap_rows` decided at k = 32 in
//! 24.1M). The cross-review of PRES-overlap-fast (2026-11-13) replaced the lists by words of 64
//! keys with signature groups and joins of whole words (round 1), and then added the
//! intervals of full words, projection by intervals, buffers kept between steps, and the rate
//! 2048 (round 2); a set of intervals alone and a set of repeated words were smaller but grew
//! more than 10.5 times from k = 64 to 512. After round 2 the floor of the bound above kept the
//! plan from costing more than main on `wide`. Two sums whose shared atoms have different
//! coefficients in each (1 and 2 in one, 1 in the other) split the shared atoms into classes
//! whose box is the product of their ranges, so the bound passes [`FIRST`] · [`RATE`] and the
//! method waits for the solver: faster than main, but not of order k (plan row
//! PRES-overlap-coeffs). Sumsets by FFT (K. Koiliaris
//! and C. Xu, "A faster pseudopolynomial time algorithm for subset sum", SODA 2017; K.
//! Bringmann, "A near-linear pseudopolynomial time algorithm for subset sum", SODA 2017) cost
//! O(W log W log n) for the sumset of n atoms whose sums span W, against O(n · log m · W/64)
//! word steps at most for the shifts here (ranges of m values). They need floating point or a
//! number-theoretic transform, and a transform spends several multiplications per key and
//! level where a shift spends 1/64 of a word step per key, so they gain only on groups of tens
//! of thousands of atoms (inferred from these counts, not measured).
//!
//! Papers. R. Bellman, *Dynamic Programming*, Princeton University Press, 1957. E. Horowitz and
//! S. Sahni, "Computing partitions with applications to the knapsack problem", Journal of the
//! ACM 21(2), 1974. R. Dechter, "Bucket elimination: a unifying framework for reasoning",
//! Artificial Intelligence 113(1-2), 1999. L. A. Levin, "Universal sequential search
//! problems", Problems of Information Transmission 9(3), 1973. R. M. Karp, "Reducibility among
//! combinatorial problems", Complexity of Computer Computations, 1972. D. Pisinger, "Linear
//! time algorithms for knapsack problems with bounded weights", Journal of Algorithms 33(1),
//! 1999. Z. Galil and O. Margalit, "An almost linear-time algorithm for the dense subset-sum
//! problem", SIAM Journal on Computing 20(6), 1991. K. Koiliaris and C. Xu, SODA 2017, and K.
//! Bringmann, SODA 2017, as above.
//!
//! The formula is recognized as: top-level conjuncts each either a constraint (a row, of any
//! number of atoms, `== 0` or `>= 0`) or a disjunction whose arms each confine one and the same
//! atom to a range with both ends finite, with at least one disjunction. A constraint on one
//! atom alone (`0 <= c`) is read as a bound on it: it cuts the ranges of an atom with a
//! disjunction, and the bounds of an atom without one, which must be finite on both sides, are
//! its one range (the parity example writes `c` and `d` so). An atom with a disjunction and no
//! row takes any value of it. Any other conjunct, an atom of a row with neither a disjunction
//! nor two bounds, a second disjunction on one atom, or a number past `i128` leaves the
//! formula to the solver alone.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};

use super::formula::{Atom, Conjuncts, Formula, Id, Model, Rel, one_bound};
use super::refusal::{Each, Refusal};
use super::row_domains::{self, Settled, range};

/// A row `Σ c·y + k`, `== 0` or `>= 0`, over the atoms' indices.
struct Row {
    terms: Vec<(usize, i128)>,
    k: i128,
    eq: bool,
}

/// A formula of the class the module note names, read into numbers.
pub(super) struct Rows {
    atoms: Vec<Atom>,
    /// Each atom's values: sorted ranges, disjoint and not adjacent.
    domains: Vec<Vec<(i128, i128)>>,
    rows: Vec<Row>,
    /// Some conjunct has no point.
    empty: bool,
    /// The number of terms and arms read: the method's first allowance.
    size: u64,
}

impl Rows {
    /// The formula given as its top-level conjuncts (`Formula::conjunct_list`), when it is of
    /// the class the module note names; `None` otherwise, and under [`ROW_SUMS_OFF`],
    /// so that the solver alone runs as before this module, and within a race.
    // Complexity tradeoff: each conjunct is read once, an arm that several disjunctions share
    // once by its id (as `row_domains::settle` reads them), the domains sorted once and each
    // term's atom found by binary search: O(n log n) in the size n of the formula. A formula
    // outside the class is left at its first conjunct of another shape. An ordered map of the
    // domains and a hash map of every arm read, the first version, cost 260K instructions on
    // wide k=32 (3.5% of the solver's 7.46M, for a formula the method cannot take): one tree
    // step per atom compares symbol strings, and each arm was hashed and cloned. Now only an
    // arm another holder shares is kept (`Id::of`).
    pub(super) fn of(conjuncts: &Conjuncts) -> Option<Rows> {
        if ROW_SUMS_OFF.with(Cell::get) {
            return None;
        }
        // Within a race (a question the solver asks while it answers another the method did
        // not answer at once) the solver's steps are charged to the outer race, which an
        // inner race would take: the outer method then ran later or never. Leaving inner
        // questions to the solver took m2_p5 from 0.66 to 0.24 of main's units, m2_p8 from
        // 1.0 to 0.60 and w_p from 1.04 to 1.003 (2026-11-13).
        if RACES.with(|races| !races.borrow().is_empty()) {
            return None;
        }
        let mut domains: Vec<(Atom, Vec<(i128, i128)>)> = Vec::new();
        let mut cons = Vec::new();
        let mut arms_read: HashMap<Id, (Atom, Int, Int)> = HashMap::new();
        // Bounds of one atom (`0 <= c && c <= 1` is written so, not as a disjunction): the
        // least and greatest value each allows.
        let mut bounds: BTreeMap<Atom, (Option<Int>, Option<Int>)> = BTreeMap::new();
        let (mut size, mut empty) = (0u64, false);
        for g in conjuncts.iter() {
            let arms = match g {
                Formula::Con(c) => {
                    size += c.lin.terms.len() as u64 + 1;
                    if let Some((a, l, h)) = one_bound(c)
                        && !matches!(a, Atom::Product(..))
                    {
                        let (lo, hi) = bounds.entry(a.clone()).or_default();
                        if let Some(l) = l
                            && lo.as_ref().is_none_or(|v| l > *v)
                        {
                            *lo = Some(l);
                        }
                        if let Some(h) = h
                            && hi.as_ref().is_none_or(|v| h < *v)
                        {
                            *hi = Some(h);
                        }
                    } else {
                        cons.push(c);
                    }
                    continue;
                }
                Formula::Or(arms) => arms,
                _ => return None,
            };
            let mut atom: Option<Atom> = None;
            let mut ranges = Vec::new();
            for arm in arms.iter() {
                size += 1;
                // Only an arm another holder shares can be met again ([`Id::of`]).
                let key = Id::of(arm);
                let (a, l, h) = match key.and_then(|key| arms_read.get(&key).cloned()) {
                    Some(read) => read,
                    None => {
                        let read = range(arm)?;
                        if let Some(key) = key {
                            arms_read.insert(key, read.clone());
                        }
                        read
                    }
                };
                if atom.as_ref().is_some_and(|b| *b != a) {
                    return None;
                }
                atom = Some(a);
                if l <= h {
                    ranges.push((l.to_i128()?, h.to_i128()?));
                }
            }
            let Some(a) = atom else {
                // `false`.
                empty = true;
                continue;
            };
            // Sorted, then merged in place: `kept` ranges are final.
            ranges.sort_unstable();
            let mut kept = 0usize;
            for i in 0..ranges.len() {
                let (l, h) = ranges[i];
                match kept.checked_sub(1).map(|last| &mut ranges[last]) {
                    Some(last) if l <= last.1.checked_add(1)? => last.1 = last.1.max(h),
                    _ => {
                        ranges[kept] = (l, h);
                        kept += 1;
                    }
                }
            }
            ranges.truncate(kept);
            empty |= ranges.is_empty();
            domains.push((a, ranges));
        }
        // An atom with two disjunctions leaves the formula to the solver.
        domains.sort_unstable_by(|x, y| x.0.cmp(&y.0));
        if domains.windows(2).any(|w| w[0].0 == w[1].0) {
            return None;
        }
        // Without a disjunction the solver searches no cases, and the method is not tried.
        if domains.is_empty() {
            return None;
        }
        // The bounds cut the ranges of an atom with a disjunction, and are the one range of an
        // atom without one; an atom bounded on one side only and with no disjunction leaves the
        // formula to the solver.
        // The atoms bounded alone are pushed after the others, in order, and merged in after.
        let with_disjunction = domains.len();
        for (a, (lo, hi)) in bounds {
            let at = domains[..with_disjunction].binary_search_by(|d| d.0.cmp(&a));
            let (lo, hi) = match at {
                Ok(_) => (
                    lo.map_or(Some(i128::MIN), |v| v.to_i128()),
                    hi.map_or(Some(i128::MAX), |v| v.to_i128()),
                ),
                Err(_) => (lo?.to_i128(), hi?.to_i128()),
            };
            let (lo, hi) = (lo?, hi?);
            let ranges = match at {
                Ok(i) => &mut domains[i].1,
                Err(_) => {
                    domains.push((a, vec![(lo, hi)]));
                    &mut domains.last_mut()?.1
                }
            };
            ranges.retain_mut(|r| {
                *r = (r.0.max(lo), r.1.min(hi));
                r.0 <= r.1
            });
            empty |= ranges.is_empty();
        }
        // Both runs are sorted, so a stable sort merges them in linear time.
        domains.sort_by(|x, y| x.0.cmp(&y.0));
        let (atoms, domains): (Vec<Atom>, Vec<_>) = domains.into_iter().unzip();
        let mut rows = Vec::with_capacity(cons.len());
        for c in cons {
            let k = c.lin.constant.to_i128()?;
            let eq = c.rel == Rel::Eq;
            if c.lin.terms.is_empty() {
                empty |= if eq { k != 0 } else { k < 0 };
                continue;
            }
            let mut terms = Vec::with_capacity(c.lin.terms.len());
            for (a, coef) in &c.lin.terms {
                terms.push((atoms.binary_search(a).ok()?, coef.to_i128()?));
            }
            rows.push(Row { terms, k, eq });
        }
        Some(Rows {
            atoms,
            domains,
            rows,
            empty,
            size,
        })
    }
}

/// The formula, given as its top-level conjuncts, read once: what the residue or the ends of
/// its one equation settle ([`row_domains::settle`]), or else its rows ([`Rows::of`]) when it
/// is of the class.
// Complexity tradeoff: `row_domains::settle` and `Rows::of` each read every arm of a formula
// of one equation over unions of ranges, the shape of both. Naive version: both reads, which
// cost 3.0% over the solver alone on wide k=32 and 3.9% at k=4, where neither settles nor the
// method can run; used: the rule of `settle` applied to the rows read here, in O(n) more,
// and `settle` itself only where the rows are not read (a value past `i128`, within a race,
// under `ROW_SUMS_OFF`) or the rule's sums pass `i128`, so every formula `settle` answered
// is still answered.
pub(super) fn read(conjuncts: &Conjuncts) -> Result<Settled, Option<Rows>> {
    let rows = Rows::of(conjuncts);
    let settled = match &rows {
        Some(rows) => rows.settled(),
        None => None,
    };
    match settled {
        Some(Some(s)) => Ok(s),
        Some(None) => Err(rows),
        None => row_domains::settle(conjuncts).ok_or(rows),
    }
}

impl Rows {
    /// [`row_domains::settle`] of the formula read: `Some(None)` where the rows are other
    /// than one equation over every atom, or neither its residue nor its ends settle it;
    /// `None` where a sum passes `i128`.
    fn settled(&self) -> Option<Option<Settled>> {
        if self.empty {
            return Some(Some(Settled::Empty));
        }
        let [row] = &self.rows[..] else {
            return Some(None);
        };
        if !row.eq || row.terms.len() != self.atoms.len() {
            return Some(None);
        }
        // `residue`: the row at each atom's least value; `step`: the gcd of the moves from it.
        let (mut least, mut most, mut residue, mut step) = (row.k, row.k, row.k, 0u128);
        let end = |j: usize| {
            let ranges = &self.domains[j];
            (ranges[0].0, ranges[ranges.len() - 1].1)
        };
        for &(j, c) in &row.terms {
            let (l, h) = end(j);
            residue = residue.checked_add(c.checked_mul(l)?)?;
            for &(rl, rh) in &self.domains[j] {
                step = gcd(step, c.checked_mul(rl.checked_sub(l)?)?.unsigned_abs());
                if rl != rh {
                    step = gcd(step, c.unsigned_abs());
                }
            }
            let (vl, vh) = if c > 0 { (l, h) } else { (h, l) };
            least = least.checked_add(c.checked_mul(vl)?)?;
            most = most.checked_add(c.checked_mul(vh)?)?;
        }
        let off_lattice = match step {
            0 => residue != 0,
            step => residue.unsigned_abs() % step != 0,
        };
        // The corner where the row is zero: each atom at the end that gives the least value
        // (`at_least`) or the greatest.
        let corner = |at_least: bool| {
            let point = row.terms.iter().map(|&(j, c)| {
                let (l, h) = end(j);
                let v = if (c > 0) == at_least { l } else { h };
                (self.atoms[j].clone(), Int::from(v))
            });
            Some(Settled::Point(point.collect()))
        };
        Some(if off_lattice || least > 0 || most < 0 {
            Some(Settled::Empty)
        } else if least == 0 {
            corner(true)
        } else if most == 0 {
            corner(false)
        } else {
            None
        })
    }

    /// A lower bound on [`Plan::bound`] of every pass, read from the rows alone, for a formula
    /// whose plan the method could not run first: the charges of the first table of each
    /// group of atoms on one row. Such a group has one class, so its key is the sum itself
    /// over one primitive coefficient p ≠ 0 per atom: for its first atom, with values from L to
    /// H, `n` values and the step |p| ≥ 1, the table may hold `cap` = min(n, (H - L)/64 + 1)
    /// words and a range of m values `min((m - 1)/64 + 3, cap)` of them, charged times
    /// `bits(m - 1)` as [`Plan::bound`] charges it. A group's first atom is not known before
    /// the sort, so each group counts its least such charge.
    // Complexity tradeoff: O(a + e) for a atoms and e terms, no table built, where building
    // the plan to learn its bound cost 5.3K instructions more than main on `wide` at k = 4
    // (+0.78%), whose bound is far past what the method may run first: [`planned`] then
    // builds the plan only when the race would run it.
    fn floor(&self) -> u64 {
        // Each atom's only row, `usize::MAX` where it has none or several.
        let (none, many) = (usize::MAX, usize::MAX - 1);
        let mut only = vec![none; self.atoms.len()];
        // Each row's least charge of an atom on it alone, `None` where it has none; 0 where an
        // atom has the coefficient 0, which [`Plan::bound`] does not charge as above.
        let mut least: Vec<Option<u64>> = vec![None; self.rows.len()];
        for (r, row) in self.rows.iter().enumerate() {
            for &(j, c) in &row.terms {
                only[j] = if only[j] == none { r } else { many };
                if c == 0 {
                    least[r] = Some(0);
                }
            }
        }
        for (j, &r) in only.iter().enumerate() {
            if r >= many {
                continue;
            }
            // Saturating: the floor is read before [`Plan::of`], which refuses a key past
            // [`LIMIT`], so a span past `u64` never meets a bound.
            let span = |l: i128, h: i128| u64::try_from(h.saturating_sub(l)).unwrap_or(u64::MAX);
            let d = &self.domains[j];
            let width = span(d[0].0, d[d.len() - 1].1);
            let n = (d.iter()).fold(0u64, |c, &(l, h)| {
                c.saturating_add(span(l, h)).saturating_add(1)
            });
            let cap = n.min(width / 64 + 1);
            let own = |m: u64| ((m - 1) / 64 + 3).min(cap);
            let charge = (d.iter()).fold(0u64, |u, &(l, h)| {
                let m = span(l, h).saturating_add(1);
                u.saturating_add(bits(m - 1).saturating_mul(3 * own(m) + 2))
            });
            least[r] = Some(least[r].map_or(charge, |u| u.min(charge)));
        }
        (least.iter().flatten()).fold(0u64, |s, &u| s.saturating_add(u))
    }
}

/// [`super::decide`] of a formula of the class, in alternation with the solver's `old`.
pub(super) fn decide(
    rows: Rows,
    old: impl FnOnce() -> Result<bool, Refusal>,
) -> Result<bool, Refusal> {
    if rows.empty {
        return Ok(false);
    }
    planned(
        rows,
        Vec::new(),
        |_| Pass::Decide,
        |plan, rows, _, allowance| Some(plan.forward(rows, &mut Work::new(allowance))?.is_some()),
        old,
    )
}

/// [`super::satisfiable`] of a formula of the class, in alternation with the solver's `old`.
pub(super) fn point(
    rows: Rows,
    old: impl FnOnce() -> Result<Option<Model>, Refusal>,
) -> Result<Option<Model>, Refusal> {
    if rows.empty {
        return Ok(None);
    }
    planned(
        rows,
        Vec::new(),
        |_| Pass::Point,
        |plan, rows, _, allowance| plan.point(rows, &mut Work::new(allowance)),
        old,
    )
}

/// [`super::project_each`] of a formula of the class onto `syms`, in alternation with the
/// solver's `old`.
pub(super) fn project(
    rows: Rows,
    syms: &[Atom],
    old: impl FnOnce() -> Result<Each, Refusal>,
) -> Result<Each, Refusal> {
    if rows.empty {
        return Ok((
            syms.iter().map(|_| Ok(IntervalSet::empty())).collect(),
            Vec::new(),
        ));
    }
    let wanted: Vec<Option<usize>> = (syms.iter())
        .map(|a| rows.atoms.binary_search(a).ok())
        .collect();
    let mut want = vec![false; rows.atoms.len()];
    for a in wanted.iter().flatten() {
        want[*a] = true;
    }
    planned(
        rows,
        want,
        |want| Pass::Project(want),
        move |plan, rows, want, allowance| {
            let mut sets = plan.project(rows, want, &mut Work::new(allowance))?;
            let each = (wanted.iter())
                .map(|w| {
                    Ok(match w.and_then(|a| sets[a].take()) {
                        Some(set) => set,
                        None => IntervalSet::range(End::NegInf, End::PosInf),
                    })
                })
                .collect();
            Some((each, Vec::new()))
        },
        old,
    )
}

/// The plan of `rows` for the atoms `want` and the pass `pass`, raced with the solver's `old`;
/// `run` runs the method on the plan with an allowance. The solver alone answers where there
/// is no plan.
// Complexity tradeoff: where [`Rows::floor`] is past what the method may run first, the plan
// and its bound are built only when the solver's charge reaches the floor over [`RATE`], and
// the method runs once the charge reaches the bound over the rate, as when they are built at
// once: O(a + e) where the solver answers before, against the plan's O((a + e) log a).
fn planned<T: 'static>(
    rows: Rows,
    want: Vec<bool>,
    pass: for<'a> fn(&'a [bool]) -> Pass<'a>,
    run: impl Fn(&Plan, &Rows, &[bool], u64) -> Option<T> + 'static,
    old: impl FnOnce() -> Result<T, Refusal>,
) -> Result<T, Refusal> {
    let (size, floor) = (rows.size, rows.floor());
    if floor <= size.saturating_mul(FIRST).saturating_mul(RATE) {
        let Some(plan) = Plan::of(&rows, &want) else {
            return old();
        };
        let bound = plan.bound(&rows, pass(&want));
        debug_assert!(floor <= bound, "floor {floor} past the bound {bound}");
        return race(
            size,
            bound,
            move |allowance| Ok(run(&plan, &rows, &want, allowance)),
            old,
        );
    }
    let mut built: Option<Option<(Plan, u64)>> = None;
    let new = move |_| {
        if let Some(built) = &built {
            return Ok(built
                .as_ref()
                .and_then(|(plan, bound)| run(plan, &rows, &want, *bound)));
        }
        let plan = Plan::of(&rows, &want).map(|plan| {
            let bound = plan.bound(&rows, pass(&want));
            (plan, bound)
        });
        let next = match &plan {
            Some((_, bound)) if *bound != u64::MAX => {
                debug_assert!(floor <= *bound, "floor {floor} past the bound {bound}");
                Err(bound.div_ceil(RATE))
            }
            _ => Ok(None),
        };
        built = Some(plan);
        next
    };
    race(size, floor, new, old)
}

/// The number of bits of `n`: 1 + the floor of its base-2 logarithm, 0 for 0.
fn bits(n: u64) -> u64 {
    u64::from(u64::BITS - n.leading_zeros())
}

/// The units charged for sorting `n` keys: `n · (1 + bits(n))`, saturating.
fn sorted(n: u64) -> u64 {
    n.saturating_mul(1 + bits(n))
}

/// The greatest common divisor of `a` and `b` (Euclid), `a` where `b` is 0.
fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The keys of a set lie below this: 2^62, so that a key plus a shift stays in `i64`.
const LIMIT: i128 = 1 << 62;

/// A finite set of keys, integers from 0 below [`LIMIT`], as runs of 64-bit words: word `i` of
/// a run that starts at block `b` holds the keys `64·(b + i) + j` as its bits `j`. Every word
/// is nonzero and runs do not touch, so a set has at most as many words as keys, and at most
/// one word per 64 keys of its range.
// Complexity tradeoff: a sorted list of keys costs one step per key, a bitset over the whole
// range one step per 64 keys of the range even where the set is sparse; the runs cost one step
// per word that holds a key, the smaller of the two, and a dense run is shifted and merged 64
// keys at a time. Roaring bitmaps (D. Lemire, G. Ssi-Yan-Kai and O. Kaser, "Consistently faster
// and smaller compressed bitmaps with Roaring", Software: Practice and Experience 46(11), 2016)
// switch each 2^16 keys between a sorted list and a bitset at 4,096 keys, a switch at a size;
// the runs need none.
#[derive(Clone, Default)]
struct Lits {
    /// Each run's first block and the start of its words in `words`.
    runs: Vec<(i64, usize)>,
    words: Vec<u64>,
}

impl Lits {
    fn one(key: i64) -> Lits {
        let mut s = Lits::default();
        s.put(key >> 6, 1 << (key & 63));
        s
    }

    /// The set of `keys`, which are sorted here.
    fn of(keys: &mut [i64]) -> Lits {
        keys.sort_unstable();
        let mut s = Lits::default();
        for &k in keys.iter() {
            s.put(k >> 6, 1 << (k & 63));
        }
        s
    }

    fn is_empty(&self) -> bool {
        self.runs.is_empty()
    }

    fn words(&self) -> u64 {
        self.words.len() as u64
    }

    fn run(&self, i: usize) -> (i64, &[u64]) {
        let to = self.runs.get(i + 1).map_or(self.words.len(), |r| r.1);
        (self.runs[i].0, &self.words[self.runs[i].1..to])
    }

    /// The block after the last run, `i64::MIN` for the empty set.
    fn end(&self) -> i64 {
        match self.runs.last() {
            None => i64::MIN,
            Some(&(b, from)) => b + (self.words.len() - from) as i64,
        }
    }

    /// Adds the keys of word `w` at block `b`, at or after the set's last block; the keys below
    /// 0 are dropped.
    fn put(&mut self, b: i64, w: u64) {
        if w == 0 || b < 0 {
            return;
        }
        let end = self.end();
        if b < end {
            let at = self.words.len() - (end - b) as usize;
            self.words[at] |= w;
            return;
        }
        if b > end {
            self.runs.push((b, self.words.len()));
        }
        self.words.push(w);
    }

    /// Adds the run of words `w` from block `b`, where `b` is at least the first block of the
    /// set's last run.
    #[inline]
    fn put_run(&mut self, b: i64, w: &[u64]) {
        let end = self.end();
        if b > end {
            self.runs.push((b, self.words.len()));
            self.words.extend_from_slice(w);
            return;
        }
        let back = (end - b) as usize;
        let over = back.min(w.len());
        let at = self.words.len() - back;
        for (x, y) in self.words[at..at + over].iter_mut().zip(w) {
            *x |= y;
        }
        self.words.extend_from_slice(&w[over..]);
    }

    /// Makes the words appended from `at` on, for the blocks from `b` on, runs, where `end` was
    /// the set's end before them and `b` is at least `end`: the words below block 0 and the zero
    /// words are dropped, each stretch of nonzero words moved down in one copy.
    fn settle(&mut self, b: i64, at: usize, end: i64) {
        let len = self.words.len();
        let (mut put, mut open) = (at, end);
        let mut k = at + usize::try_from(-b).unwrap_or(0).min(len - at);
        while let Some(p) = self.words[k..].iter().position(|&x| x != 0) {
            let from = k + p;
            let to = self.words[from..]
                .iter()
                .position(|&x| x == 0)
                .map_or(len, |q| from + q);
            let blk = b + (from - at) as i64;
            if blk != open {
                self.runs.push((blk, put));
            }
            if put != from {
                self.words.copy_within(from..to, put);
            }
            (put, open, k) = (put + to - from, blk + (to - from) as i64, to);
        }
        self.words.truncate(put);
    }

    /// `{x + d}`, the keys below 0 dropped, written over `out`.
    fn shifted_into(&self, d: i64, out: &mut Lits) {
        let runs = (0..self.runs.len()).map(|i| {
            let (b, w) = self.run(i);
            (b, w.iter().copied())
        });
        Lits::shifted_runs(runs, d, self.runs.len(), self.words.len(), out);
    }

    /// The runs given, each its first block and its words, in increasing
    /// block, not touching and with every word nonzero, shifted by `d`, the keys below 0
    /// dropped, written over `out`; `runs` and `words` are their counts.
    fn shifted_runs<W: Iterator<Item = u64>>(
        it: impl Iterator<Item = (i64, W)>,
        d: i64,
        runs: usize,
        words: usize,
        out: &mut Lits,
    ) {
        let (q, r) = (d.div_euclid(64), d.rem_euclid(64) as u32);
        out.runs.clear();
        out.words.clear();
        out.runs.reserve(runs);
        out.words.reserve(words + runs);
        for (b, mut w) in it {
            let (at, end) = (out.words.len(), out.end());
            let (mut blk, mut gap) = (b + q, false);
            if r == 0 {
                out.words.extend(w);
            } else if let Some(first) = w.next() {
                // Word k of the run shifted: the low bits of word k, the high bits of k - 1.
                // Only the first and the last can be zero but for a gap inside, noted.
                if first.wrapping_shl(r) != 0 {
                    out.words.push(first.wrapping_shl(r));
                } else {
                    blk += 1;
                }
                let mut prev = first;
                for x in w {
                    let y = x.wrapping_shl(r) | prev.wrapping_shr(64 - r);
                    gap |= y == 0;
                    out.words.push(y);
                    prev = x;
                }
                let last = prev.wrapping_shr(64 - r);
                if last != 0 {
                    out.words.push(last);
                }
            }
            if gap || blk < 0 {
                out.settle(blk, at, end);
            } else if blk != end && out.words.len() > at {
                out.runs.push((blk, at));
            }
        }
    }

    /// `{c - x}`, the keys below 0 dropped, written over `out`.
    // Complexity tradeoff: one pass, the runs read from the last with each word's bits reversed
    // (block `m - b` for block b, `m` the last block, so key x is `64·m + 63 - x`) and shifted
    // to `c - x` as they are read; the mirror needs no settling, as its runs do not touch and
    // its words are nonzero. Before: the mirror built, then shifted, two sets of words.
    fn reflected_into(&self, c: i64, out: &mut Lits) {
        if self.runs.is_empty() {
            out.runs.clear();
            out.words.clear();
            return;
        }
        let m = self.end() - 1;
        let runs = (0..self.runs.len()).rev().map(|i| {
            let (b, w) = self.run(i);
            (
                m - b - w.len() as i64 + 1,
                w.iter().rev().map(|x| x.reverse_bits()),
            )
        });
        Lits::shifted_runs(
            runs,
            c - 64 * m - 63,
            self.runs.len(),
            self.words.len(),
            out,
        );
    }

    fn union(&self, o: &Lits) -> Lits {
        let mut out = Lits::default();
        self.union_into(o, &mut out);
        out
    }

    /// The union, written over `out`.
    fn union_into(&self, o: &Lits, out: &mut Lits) {
        out.runs.clear();
        out.words.clear();
        out.runs.reserve(self.runs.len() + o.runs.len());
        out.words.reserve(self.words.len() + o.words.len());
        let (mut i, mut j) = (0, 0);
        while i < self.runs.len() || j < o.runs.len() {
            let (b, w) =
                if j == o.runs.len() || (i < self.runs.len() && self.runs[i].0 <= o.runs[j].0) {
                    i += 1;
                    self.run(i - 1)
                } else {
                    j += 1;
                    o.run(j - 1)
                };
            out.put_run(b, w);
        }
    }

    /// The intersection, written over `out`.
    fn and_into(&self, o: &Lits, out: &mut Lits) {
        out.runs.clear();
        out.words.clear();
        let (mut i, mut j) = (0, 0);
        while i < self.runs.len() && j < o.runs.len() {
            let ((a, x), (b, y)) = (self.run(i), o.run(j));
            let (from, to) = (a.max(b), (a + x.len() as i64).min(b + y.len() as i64));
            if from < to {
                let (at, end) = (out.words.len(), out.end());
                let (x, y) = (
                    &x[(from - a) as usize..(to - a) as usize],
                    &y[(from - b) as usize..(to - b) as usize],
                );
                out.words.extend(x.iter().zip(y).map(|(p, q)| p & q));
                out.settle(from, at, end);
            }
            if a + x.len() as i64 <= b + y.len() as i64 {
                i += 1;
            } else {
                j += 1;
            }
        }
    }

    /// The keys from `lo` to `hi`, both at least 0, `lo` at most `hi`.
    fn clipped(&self, lo: i64, hi: i64) -> Lits {
        let mut out = Lits::default();
        let (first, last) = (lo >> 6, hi >> 6);
        let start = self
            .runs
            .partition_point(|&(b, _)| b <= first)
            .saturating_sub(1);
        for i in start..self.runs.len() {
            let (b, w) = self.run(i);
            let (from, to) = (b.max(first), (b + w.len() as i64).min(last + 1));
            if from >= to {
                if b > last {
                    break;
                }
                continue;
            }
            let (at, end) = (out.words.len(), out.end());
            out.words
                .extend_from_slice(&w[(from - b) as usize..(to - b) as usize]);
            if from == first {
                out.words[at] &= u64::MAX << (lo & 63);
            }
            if to == last + 1 {
                let n = out.words.len() - 1;
                out.words[n] &= u64::MAX >> (63 - (hi & 63));
            }
            out.settle(from, at, end);
        }
        out
    }

    /// Keeps the keys from `lo` to `hi`, both at least 0, in place.
    fn keep(&mut self, lo: i64, hi: i64) {
        if lo > hi {
            self.runs.clear();
            self.words.clear();
            return;
        }
        let (first, last) = (lo >> 6, hi >> 6);
        while let Some(&(b, at)) = self.runs.last() {
            if b > last {
                self.words.truncate(at);
                self.runs.pop();
                continue;
            }
            let end = at + (last - b) as usize + 1;
            if end <= self.words.len() {
                self.words.truncate(end);
                self.words[end - 1] &= u64::MAX >> (63 - (hi & 63));
                if self.words[end - 1] == 0 {
                    self.words.pop();
                    if self.words.len() == at {
                        self.runs.pop();
                    }
                }
            }
            break;
        }
        let i = self.runs.partition_point(|&(b, _)| b <= first);
        if i == 0 {
            return;
        }
        let (b, at) = self.runs[i - 1];
        let to = self.runs.get(i).map_or(self.words.len(), |r| r.1);
        let part = first - b < (to - at) as i64;
        let cut = if part { at + (first - b) as usize } else { to };
        self.words.drain(..cut);
        self.runs.drain(..i - usize::from(part));
        for r in &mut self.runs {
            r.1 = r.1.saturating_sub(cut);
        }
        if part {
            self.runs[0].0 = first;
            self.words[0] &= u64::MAX << (lo & 63);
            if self.words[0] == 0 {
                self.words.remove(0);
                self.runs[0].0 += 1;
                for r in &mut self.runs[1..] {
                    r.1 -= 1;
                }
                if self.runs.get(1).map_or(self.words.len(), |r| r.1) == 0 {
                    self.runs.remove(0);
                }
            }
        }
    }

    fn contains(&self, key: i64) -> bool {
        let blk = key >> 6;
        let i = self.runs.partition_point(|&(b, _)| b <= blk);
        if key < 0 || i == 0 {
            return false;
        }
        let (b, w) = self.run(i - 1);
        w.get((blk - b) as usize)
            .is_some_and(|x| x >> (key & 63) & 1 == 1)
    }

    fn min(&self) -> Option<i64> {
        let &(b, at) = self.runs.first()?;
        Some(64 * b + i64::from(self.words[at].trailing_zeros()))
    }

    fn max(&self) -> Option<i64> {
        let w = self.words.last()?;
        Some(64 * (self.end() - 1) + 63 - i64::from(w.leading_zeros()))
    }

    /// The keys from `lo` (at least 0) below `hi`, in increasing order: the words from the one
    /// holding `lo` to one past the one holding `hi - 1` are read.
    fn keys_in(&self, lo: i64, hi: i64) -> impl Iterator<Item = i64> + '_ {
        let (first, top) = (lo >> 6, (hi - 1) >> 6);
        let i = self
            .runs
            .partition_point(|&(b, _)| b <= first)
            .saturating_sub(1);
        (i..self.runs.len())
            .flat_map(move |r| {
                let (b, w) = self.run(r);
                let skip = (first - b).clamp(0, w.len() as i64) as usize;
                (w[skip..].iter().enumerate()).map(move |(k, &x)| (b + (skip + k) as i64, x))
            })
            .take_while(move |&(b, _)| b <= top)
            .flat_map(|(b, mut x)| {
                std::iter::from_fn(move || {
                    let j = (x != 0).then(|| x.trailing_zeros())?;
                    x &= x - 1;
                    Some(64 * b + i64::from(j))
                })
            })
            .filter(move |&k| lo <= k && k < hi)
    }
}

impl Lits {
    /// The words of the keys from `lo` to `hi`, both at least 0, appended to `out` after its
    /// last block.
    fn clip_into(&self, lo: i64, hi: i64, out: &mut Lits) {
        let part = self.clipped(lo, hi);
        for i in 0..part.runs.len() {
            let (c, w) = part.run(i);
            out.put_run(c, w);
        }
    }
}

/// The words of `w` before its first stretch of at least `MIN_FILL` full words, and that
/// stretch's length (0 where there is none).
fn full_stretch(w: &[u64]) -> (usize, usize) {
    let mut i = 0;
    while let Some(p) = w[i..].iter().position(|&x| x == u64::MAX) {
        let f = w[i + p..].iter().take_while(|&&x| x == u64::MAX).count();
        if f >= MIN_FILL {
            return (i + p, f);
        }
        i += p + f;
    }
    (w.len(), 0)
}

/// The fewest full words, one after another and apart from any interval, that a settled set
/// holds as an interval; a full word next to an interval joins it at any length.
// Complexity tradeoff: an interval costs one item where its words cost one each, but a stretch
// made an interval is cut again by the next shift that does not move it by a multiple of 64,
// and each cut costs a copy of the words around it. Measured (instructions, `overlap_rows`
// decided at k = 64 and 512): 1.977M and 13.15M at 2, 1.922M and 12.54M at 4, 1.829M and
// 12.39M at 8, 1.805M and 12.30M at 16, 1.813M and 12.58M at 32, 1.825M and 12.90M at 64, and
// 1.849M and 13.25M at 256. The least of both is at 16.
const MIN_FILL: usize = 16;

/// The bits of block `blk` that lie in the keys from `lo` to `hi`.
#[inline]
fn span_mask((lo, hi): (i64, i64), blk: i64) -> u64 {
    let (a, z) = (
        lo.max(64 * blk) - 64 * blk,
        hi.min(64 * blk + 63) - 64 * blk,
    );
    if a > z {
        0
    } else {
        (u64::MAX << a) & (u64::MAX >> (63 - z))
    }
}

/// A finite set of keys as the words of [`Lits`] and intervals of keys: `fill` holds sorted
/// intervals `[lo, hi]` that do not touch, and `lit` keys of the set, which may lie in an
/// interval too. Each table of the forward pass is settled: no key of `lit` lies in an interval.
// Complexity tradeoff: the table of a group of g atoms with values up to W holds sums from 0 to
// about g·W, and in its middle every sum is reached (Galil and Margalit, "An almost linear-time
// algorithm for the dense subset-sum problem", SIAM J. Comput. 20(6), 1991); in `overlap_rows`
// the words not full fall from 159 at k = 64 to 39 at k = 1,024 while the full ones grow with k.
// Stored as words, each operation reads the whole table, O(g·W/64), and the g additions cost
// O(g²·W/64); with the full words kept as intervals, an operation reads the words not full and
// one item per interval. A shift or a reflection maps the intervals and the words each on its
// own, and the two stay apart; a union lays the words over the intervals, once.
#[derive(Clone, Default)]
struct Set {
    lit: Lits,
    fill: Vec<(i64, i64)>,
}

impl Set {
    fn one(key: i64) -> Set {
        Set {
            lit: Lits::one(key),
            fill: Vec::new(),
        }
    }

    /// The set of `keys`, which are sorted here.
    fn of(keys: &mut [i64]) -> Set {
        Set::settled(Lits::of(keys), Vec::new())
    }

    /// The set of the keys of `lit` and of the intervals `fill`, sorted by first key, which may
    /// overlap `lit` and each other: the keys of `lit` inside an interval are dropped, a word
    /// whose block the intervals and `lit` cover is made an interval, and intervals that touch
    /// are joined. The words of blocks no interval meets are copied as they are.
    fn settled(mut lit: Lits, fill: Vec<(i64, i64)>) -> Set {
        if fill.is_empty() && !lit.words.contains(&u64::MAX) {
            return Set { lit, fill };
        }
        // The words kept are moved down in place: `put` is where the next one goes, `open` the
        // block after the last one kept.
        let (mut runs, mut out) = (
            Vec::with_capacity(lit.runs.len() + 1),
            Vec::with_capacity(fill.len() + 1),
        );
        let (mut put, mut open) = (0, i64::MIN);
        let mut keep = |words: &mut Vec<u64>, blk: i64, from: usize, n: usize| {
            if blk != open {
                runs.push((blk, put));
            }
            if from != put {
                words.copy_within(from..from + n, put);
            }
            (put, open) = (put + n, blk + n as i64);
        };
        let join = |f: &mut Vec<(i64, i64)>, (lo, hi): (i64, i64)| match f.last_mut() {
            Some(l) if l.1 + 1 >= lo => l.1 = l.1.max(hi),
            _ => f.push((lo, hi)),
        };
        let mut j = 0;
        for i in 0..lit.runs.len() {
            let (b, at) = lit.runs[i];
            let to = lit.runs.get(i + 1).map_or(lit.words.len(), |r| r.1);
            let mut k = at;
            while k < to {
                let blk = b + (k - at) as i64;
                while j < fill.len() && fill[j].0 < 64 * blk {
                    join(&mut out, fill[j]);
                    j += 1;
                }
                let last = out.last().copied();
                if let Some(l) = last
                    && l.1 >= 64 * blk + 63
                {
                    k = (at as i64 + ((l.1 + 1) >> 6) - b).min(to as i64) as usize;
                    continue;
                }
                let mut m = last
                    .filter(|l| l.1 >= 64 * blk)
                    .map_or(0, |l| span_mask(l, blk));
                let mut t = j;
                while t < fill.len() && fill[t].0 <= 64 * blk + 63 {
                    m |= span_mask(fill[t], blk);
                    t += 1;
                }
                if m != 0 {
                    // A block an interval meets: its word outside the intervals.
                    let x = lit.words[k] & !m;
                    if x | m == u64::MAX {
                        join(&mut out, (64 * blk, 64 * blk + 63));
                    } else if x != 0 {
                        lit.words[k] = x;
                        keep(&mut lit.words, blk, k, 1);
                    }
                    k += 1;
                    continue;
                }
                // The words up to the next interval's block, cut at the first full one.
                let stop = fill.get(j).map_or(to, |f| {
                    (at as i64 + (f.0 >> 6) - b).clamp(k as i64, to as i64) as usize
                });
                let (n, f) = full_stretch(&lit.words[k..stop]);
                if n > 0 {
                    keep(&mut lit.words, blk, k, n);
                }
                if f > 0 {
                    let at = 64 * (blk + n as i64);
                    join(&mut out, (at, at + 64 * f as i64 - 1));
                }
                k += n + f;
            }
        }
        for &f in &fill[j..] {
            join(&mut out, f);
        }
        lit.words.truncate(put);
        lit.runs = runs;
        Set { lit, fill: out }
    }

    fn is_empty(&self) -> bool {
        self.lit.is_empty() && self.fill.is_empty()
    }

    /// Empties the set, its buffers kept.
    fn clear(&mut self) {
        self.lit.runs.clear();
        self.lit.words.clear();
        self.fill.clear();
    }

    /// The items an operation reads: the words and the intervals.
    fn words(&self) -> u64 {
        self.lit.words() + self.fill.len() as u64
    }

    /// The units of a lookup: `1 + bits(runs and intervals)`.
    fn lookup(&self) -> u64 {
        1 + bits((self.lit.runs.len() + self.fill.len()) as u64)
    }

    fn contains(&self, key: i64) -> bool {
        let i = self.fill.partition_point(|&(lo, _)| lo <= key);
        (i > 0 && key <= self.fill[i - 1].1) || self.lit.contains(key)
    }

    fn min(&self) -> Option<i64> {
        match (self.lit.min(), self.fill.first()) {
            (Some(a), Some(f)) => Some(a.min(f.0)),
            (a, f) => a.or(f.map(|f| f.0)),
        }
    }

    fn max(&self) -> Option<i64> {
        match (self.lit.max(), self.fill.last()) {
            (Some(a), Some(f)) => Some(a.max(f.1)),
            (a, f) => a.or(f.map(|f| f.1)),
        }
    }

    /// The intervals mapped by `f`, in the order of `it`, the keys below 0 dropped, written over
    /// `out`.
    fn mapped(
        it: impl Iterator<Item = (i64, i64)>,
        f: impl Fn((i64, i64)) -> (i64, i64),
        out: &mut Vec<(i64, i64)>,
    ) {
        out.clear();
        out.extend(
            it.map(f)
                .filter(|&(_, hi)| hi >= 0)
                .map(|(lo, hi)| (lo.max(0), hi)),
        );
    }

    /// `{x + d}`, the keys below 0 dropped.
    fn shifted(&self, d: i64) -> Set {
        let mut out = Set::default();
        self.shifted_into(d, &mut out);
        out
    }

    /// `{x + d}`, the keys below 0 dropped, written over `out`.
    fn shifted_into(&self, d: i64, out: &mut Set) {
        if d == 0 {
            // Field by field: the derived `clone_from` clones whole and frees the old buffers.
            out.lit.runs.clone_from(&self.lit.runs);
            out.lit.words.clone_from(&self.lit.words);
            out.fill.clone_from(&self.fill);
            return;
        }
        Set::mapped(
            self.fill.iter().copied(),
            |(lo, hi)| (lo + d, hi + d),
            &mut out.fill,
        );
        self.lit.shifted_into(d, &mut out.lit);
    }

    /// `{c - x}`, the keys below 0 dropped.
    fn reflected(&self, c: i64) -> Set {
        let mut out = Set::default();
        self.reflected_into(c, &mut out);
        out
    }

    /// `{c - x}`, the keys below 0 dropped, written over `out`.
    fn reflected_into(&self, c: i64, out: &mut Set) {
        Set::mapped(
            self.fill.iter().rev().copied(),
            |(lo, hi)| (c - hi, c - lo),
            &mut out.fill,
        );
        self.lit.reflected_into(c, &mut out.lit);
    }

    fn union(&self, o: &Set) -> Set {
        let mut out = Set::default();
        self.union_into(o, &mut out);
        out
    }

    /// The union, written over `out`.
    fn union_into(&self, o: &Set, out: &mut Set) {
        let fill = &mut out.fill;
        fill.clear();
        fill.reserve(self.fill.len() + o.fill.len());
        let (mut i, mut j) = (0, 0);
        while i < self.fill.len() || j < o.fill.len() {
            let f = if j == o.fill.len() || (i < self.fill.len() && self.fill[i].0 <= o.fill[j].0) {
                i += 1;
                self.fill[i - 1]
            } else {
                j += 1;
                o.fill[j - 1]
            };
            match fill.last_mut() {
                Some(l) if l.1 + 1 >= f.0 => l.1 = l.1.max(f.1),
                _ => fill.push(f),
            }
        }
        self.lit.union_into(&o.lit, &mut out.lit);
    }

    /// The words of `lit` inside the intervals of `fill`.
    fn within(lit: &Lits, fill: &[(i64, i64)]) -> Lits {
        let mut out = Lits::default();
        for &(lo, hi) in fill {
            if lit.is_empty() || 64 * lit.end() <= lo {
                break;
            }
            lit.clip_into(lo, hi, &mut out);
        }
        out
    }

    fn and(&self, o: &Set) -> Set {
        let mut out = Set::default();
        self.and_into(o, &mut out);
        out
    }

    /// The intersection, written over `out`.
    fn and_into(&self, o: &Set, out: &mut Set) {
        let fill = &mut out.fill;
        fill.clear();
        let (mut i, mut j) = (0, 0);
        while i < self.fill.len() && j < o.fill.len() {
            let ((a, x), (b, y)) = (self.fill[i], o.fill[j]);
            if a.max(b) <= x.min(y) {
                fill.push((a.max(b), x.min(y)));
            }
            if x <= y {
                i += 1;
            } else {
                j += 1;
            }
        }
        self.lit.and_into(&o.lit, &mut out.lit);
        for part in [
            Set::within(&self.lit, &o.fill),
            Set::within(&o.lit, &self.fill),
        ] {
            if !part.is_empty() {
                out.lit = out.lit.union(&part);
            }
        }
    }

    /// The keys from `lo` to `hi`, both at least 0, `lo` at most `hi`.
    fn clipped(&self, lo: i64, hi: i64) -> Set {
        let from = self.fill.partition_point(|&(_, h)| h < lo);
        let fill = (self.fill[from..].iter())
            .take_while(|f| f.0 <= hi)
            .map(|&(a, z)| (a.max(lo), z.min(hi)))
            .collect();
        Set {
            lit: self.lit.clipped(lo, hi),
            fill,
        }
    }

    /// Keeps the keys from `lo` to `hi`, both at least 0, in place.
    fn keep(&mut self, lo: i64, hi: i64) {
        self.lit.keep(lo, hi);
        self.fill.retain(|f| f.1 >= lo && f.0 <= hi);
        for f in &mut self.fill {
            *f = (f.0.max(lo), f.1.min(hi));
        }
    }

    /// The keys from `lo` (at least 0) below `hi`, in increasing order.
    fn keys_in(&self, lo: i64, hi: i64) -> impl Iterator<Item = i64> + '_ {
        let mut lit = self.lit.keys_in(lo, hi).peekable();
        let from = self.fill.partition_point(|&(_, h)| h < lo);
        let mut full = (self.fill[from..].iter())
            .take_while(move |f| f.0 < hi)
            .flat_map(move |&(a, z)| a.max(lo)..=z.min(hi - 1))
            .peekable();
        // A key of the words may lie in an interval too: it is given once.
        let mut last = i64::MIN;
        std::iter::from_fn(move || {
            loop {
                let x = match (lit.peek(), full.peek()) {
                    (Some(a), Some(b)) if a < b => lit.next(),
                    (Some(_), None) => lit.next(),
                    _ => full.next(),
                }?;
                if x > last {
                    last = x;
                    return Some(x);
                }
            }
        })
    }

    fn keys(&self) -> impl Iterator<Item = i64> + '_ {
        self.keys_in(0, i64::MAX)
    }

    /// The set as sorted intervals of keys that do not touch, or `None` once there are more
    /// than `cap`. O(words + intervals).
    fn intervals(&self, cap: u64) -> Option<Vec<(i64, i64)>> {
        let mut out: Vec<(i64, i64)> = Vec::new();
        let push = |out: &mut Vec<(i64, i64)>, (lo, hi): (i64, i64)| match out.last_mut() {
            Some(l) if l.1 + 1 >= lo => l.1 = l.1.max(hi),
            _ => out.push((lo, hi)),
        };
        let mut f = 0;
        for r in 0..self.lit.runs.len() {
            let (b, w) = self.lit.run(r);
            for (k, &x) in w.iter().enumerate() {
                let (base, mut x) = (64 * (b + k as i64), x);
                while x != 0 {
                    let lo = x.trailing_zeros();
                    let end = lo + (x >> lo).trailing_ones();
                    let run = (base + i64::from(lo), base + i64::from(end) - 1);
                    while f < self.fill.len() && self.fill[f].0 <= run.0 {
                        push(&mut out, self.fill[f]);
                        f += 1;
                    }
                    push(&mut out, run);
                    if out.len() as u64 > cap {
                        return None;
                    }
                    x = if end == 64 { 0 } else { x & (u64::MAX << end) };
                }
            }
        }
        for &i in &self.fill[f..] {
            push(&mut out, i);
        }
        (out.len() as u64 <= cap).then_some(out)
    }
}

/// Sorts intervals and joins those that overlap or touch.
fn joined(mut v: Vec<(i64, i64)>) -> Vec<(i64, i64)> {
    v.sort_unstable();
    let mut out: Vec<(i64, i64)> = Vec::with_capacity(v.len());
    for (lo, hi) in v {
        match out.last_mut() {
            Some(l) if l.1 + 1 >= lo => l.1 = l.1.max(hi),
            _ => out.push((lo, hi)),
        }
    }
    out
}

/// The work the method may still do, in units: each operation on sets is charged the words it
/// reads and one more, before it is done ([`Plan::bound`] adds up the same charges).
// Complexity tradeoff: a shifted or reflected set read once by an intersection or a union is
// built in `tmp`, kept from one operation to the next, where a set made and freed per operation
// cost two allocations and two frees (eqchain projected at k = 128: five such sets per group,
// about a tenth of the projection's instructions); the charges are those of the two operations.
struct Work {
    left: u64,
    tmp: Set,
}

impl Work {
    fn new(allowance: u64) -> Work {
        Work {
            left: allowance,
            tmp: Set::default(),
        }
    }

    fn spend(&mut self, units: u64) -> Option<()> {
        self.left = self.left.checked_sub(units)?;
        Some(())
    }

    /// `a ∩ (b + d)`, charged as the shift and the intersection.
    fn and_shifted(&mut self, a: &Set, b: &Set, d: i64) -> Option<Set> {
        self.spend(b.words() + 1)?;
        if d == 0 {
            return self.and(a, b);
        }
        let mut t = std::mem::take(&mut self.tmp);
        b.shifted_into(d, &mut t);
        let r = self.and(a, &t);
        self.tmp = t;
        r
    }

    /// `a ∩ (b + d)` written over `out`, charged as [`Work::and_shifted`].
    fn and_shifted_into(&mut self, a: &Set, b: &Set, d: i64, out: &mut Set) -> Option<()> {
        self.spend(b.words() + 1)?;
        if d == 0 {
            self.spend(a.words() + b.words() + 1)?;
            a.and_into(b, out);
            return Some(());
        }
        let mut t = std::mem::take(&mut self.tmp);
        b.shifted_into(d, &mut t);
        let r = self.spend(a.words() + t.words() + 1);
        if r.is_some() {
            a.and_into(&t, out);
        }
        self.tmp = t;
        r
    }

    /// `a ∪ b` written over `out`, charged as [`Work::union`].
    fn union_into(&mut self, a: &Set, b: &Set, out: &mut Set) -> Option<()> {
        self.spend(a.words() + b.words() + 1)?;
        a.union_into(b, out);
        Some(())
    }

    /// `a ∩ (c - b)`, charged as the reflection and the intersection.
    fn and_reflected(&mut self, a: &Set, b: &Set, c: i64) -> Option<Set> {
        self.spend(2 * (b.words() + 1))?;
        let mut t = std::mem::take(&mut self.tmp);
        b.reflected_into(c, &mut t);
        let r = self.and(a, &t);
        self.tmp = t;
        r
    }

    /// `a ∪ (a + d)`, charged as the shift and the union.
    fn union_shifted(&mut self, a: &Set, d: i64) -> Option<Set> {
        self.spend(a.words() + 1)?;
        let mut t = std::mem::take(&mut self.tmp);
        a.shifted_into(d, &mut t);
        let r = self.union(a, &t);
        self.tmp = t;
        r
    }

    fn copy(&mut self, s: &Set) -> Option<Set> {
        self.spend(s.words() + 1)?;
        Some(s.clone())
    }

    fn shift(&mut self, s: &Set, d: i64) -> Option<Set> {
        self.spend(s.words() + 1)?;
        Some(s.shifted(d))
    }

    fn reflect(&mut self, s: &Set, c: i64) -> Option<Set> {
        self.spend(2 * (s.words() + 1))?;
        Some(s.reflected(c))
    }

    fn union(&mut self, a: &Set, b: &Set) -> Option<Set> {
        self.spend(a.words() + b.words() + 1)?;
        Some(a.union(b))
    }

    fn and(&mut self, a: &Set, b: &Set) -> Option<Set> {
        self.spend(a.words() + b.words() + 1)?;
        Some(a.and(b))
    }

    fn clip(&mut self, s: &Set, lo: i128, hi: i128) -> Option<Set> {
        self.spend(s.words() + 1)?;
        let (lo, hi) = (lo.max(0), hi.min(LIMIT));
        Some(if lo > hi {
            Set::default()
        } else {
            s.clipped(lo as i64, hi as i64)
        })
    }
}

/// The values `s` of `l·s + c` that meet `== 0` (`eq`) or `>= 0`: from the first to the second
/// number, none where the first is greater.
fn meets(l: i128, c: i128, eq: bool) -> (i128, i128) {
    let (q, exact) = ((-c).div_euclid(l), (-c).rem_euclid(l) == 0);
    // `q` is `-c / l` rounded down for l > 0 and up for l < 0 (the remainder is not negative).
    match (eq, exact, l > 0) {
        (true, true, _) => (q, q),
        (true, false, _) => (1, 0),
        (false, _, true) => (if exact { q } else { q + 1 }, i128::MAX),
        (false, _, false) => (i128::MIN, if exact { q } else { q - 1 }),
    }
}

/// An atom's step: the key added per unit of its value, `delta`, and the key added for its
/// least value, `base`; for its value `v`, `base + (v - least)·delta`.
#[derive(Clone, Copy)]
struct Step {
    delta: i128,
    base: i128,
}

/// A digit of a key: its least value, its number of values and its weight.
#[derive(Clone, Copy)]
struct Digit {
    lo: i128,
    radix: i64,
    mult: i64,
}

/// The atoms of one signature. Their rows fall into classes whose coefficients on the atoms
/// are proportional: row = λ times the class's primitive vector `p`, and the class sum `p·y` is
/// its digit, less its least value, in the key of a sum of the group (`digits[c]`).
/// A view of the group's items in [`Groups`].
#[derive(Clone, Copy)]
struct Group<'a> {
    sig: &'a [usize],
    atoms: &'a [usize],
    /// For each row of `sig`: its class and λ.
    of_row: &'a [(usize, i128)],
    digits: &'a [Digit],
    steps: &'a [Step],
    /// For the table of the first t atoms: its largest key, the product of its digits'
    /// ranges, and the largest value of its most significant digit.
    fill: &'a [(u64, u64, i64)],
    /// The values of the most significant digit that meet the group's rows of its class, with
    /// the other groups' least and greatest sums on them ([`Plan::of`]).
    top: (i64, i64),
}

/// Where a group's items lie in [`Groups`]: its s rows (`sig`, `of_row`) from `rows`, its n
/// atoms (`atoms`, `steps`) from `atoms` and their n + 1 tables (`fill`) from `atoms + i` for
/// group i, its m classes from `digits`.
#[derive(Clone, Copy)]
struct GroupAt {
    rows: usize,
    s: usize,
    atoms: usize,
    n: usize,
    digits: usize,
    m: usize,
    top: (i64, i64),
}

/// The groups of a plan, each field of every group in one vector.
// Complexity tradeoff: six vectors per group made and freed cost more than the group's plan on
// the one or two rows and atoms of most groups (wide at k = 16: the plan's drop alone 3.6 times
// main's); here one set of vectors per plan, grown as the groups are planned.
#[derive(Default)]
struct Groups {
    at: Vec<GroupAt>,
    sig: Vec<usize>,
    of_row: Vec<(usize, i128)>,
    atoms: Vec<usize>,
    steps: Vec<Step>,
    fill: Vec<(u64, u64, i64)>,
    digits: Vec<Digit>,
}

impl Groups {
    /// Room for the groups of `a` atoms whose signatures hold `e` rows in all: at most `a`
    /// groups and `a` atoms with their `a` + (groups) tables, and at most `e` rows and classes.
    // Complexity tradeoff: O(a + e) reserved once, where growing each vector push by push
    // copies it up to log a times (a saving inferred, not measured apart).
    fn with_capacity(a: usize, e: usize) -> Groups {
        Groups {
            at: Vec::with_capacity(a),
            sig: Vec::with_capacity(e),
            of_row: Vec::with_capacity(e),
            atoms: Vec::with_capacity(a),
            steps: Vec::with_capacity(a),
            fill: Vec::with_capacity(2 * a),
            digits: Vec::with_capacity(e),
        }
    }

    #[inline]
    fn get(&self, i: usize) -> Group<'_> {
        let a = self.at[i];
        Group {
            sig: &self.sig[a.rows..a.rows + a.s],
            atoms: &self.atoms[a.atoms..a.atoms + a.n],
            of_row: &self.of_row[a.rows..a.rows + a.s],
            digits: &self.digits[a.digits..a.digits + a.m],
            steps: &self.steps[a.atoms..a.atoms + a.n],
            fill: &self.fill[a.atoms + i..a.atoms + i + a.n + 1],
            top: a.top,
        }
    }
}

/// The working vectors of [`Groups::push`], kept from one group to the next.
// Complexity tradeoff: a group's plan is O(s·g) for s rows over g atoms, and most groups have
// one or two of each, so four vectors made and freed per group are a cost of their own: the
// holes check of eqchain at k = 128, a group per atom, took 4.75M instructions with them and
// 4.62M with them kept (2.9%); kept, they cost nothing past the largest group.
#[derive(Default)]
struct Scratch {
    prim: Vec<i128>,
    order: Vec<usize>,
    ps: Vec<i128>,
    dmax: Vec<u128>,
}

impl Groups {
    /// Plans the group of the atoms `atoms`, whose rows are `sig`, after the groups planned.
    fn push(
        &mut self,
        rows: &Rows,
        sigs: &Sigs,
        sig: &[usize],
        atoms: &[usize],
        sc: &mut Scratch,
    ) -> Option<()> {
        let n = atoms.len();
        let coef = |t: usize, k: usize| sigs.coefs[sigs.at[atoms[t]] + k];
        // Complexity tradeoff: each row's coefficients are reduced to a primitive vector and
        // the rows sorted by it, O(s·g·log s) for s rows over g atoms, against O(s²·g)
        // comparing each pair of rows; a hash map costs O(s·g) but more on the one or two
        // rows of most groups.
        let s = sig.len();
        let (prim, order, ps, dmax) = (&mut sc.prim, &mut sc.order, &mut sc.ps, &mut sc.dmax);
        prim.clear();
        let r0 = self.of_row.len();
        let of_row = &mut self.of_row;
        for k in 0..s {
            let g = (0..n)
                .fold(0u128, |g, t| gcd(g, coef(t, k).unsigned_abs()))
                .max(1);
            let g = i128::try_from(g).ok()?;
            let l = if (0..n)
                .map(|t| coef(t, k))
                .find(|&c| c != 0)
                .is_some_and(|c| c < 0)
            {
                -g
            } else {
                g
            };
            prim.extend((0..n).map(|t| coef(t, k) / l));
            of_row.push((0, l));
        }
        let row = |k: usize| &prim[k * n..(k + 1) * n];
        order.clear();
        order.extend(0..s);
        order.sort_unstable_by(|&a, &b| row(a).cmp(row(b)));
        // The classes' primitive vectors, class c at `c·n..(c + 1)·n`.
        ps.clear();
        for (i, &k) in order.iter().enumerate() {
            if i == 0 || row(k) != row(order[i - 1]) {
                ps.extend_from_slice(row(k));
            }
            of_row[r0 + k].0 = ps.len() / n - 1;
        }
        let m = ps.len() / n;
        let ends = |t: usize| {
            let d = &rows.domains[atoms[t]];
            (d[0].0, d[d.len() - 1].1)
        };
        // Class c's least and greatest contribution of atom t.
        let part = |c: usize, t: usize| -> Option<(i128, i128)> {
            let (l, h) = ends(t);
            let (x, y) = (ps[c * n + t].checked_mul(l)?, ps[c * n + t].checked_mul(h)?);
            Some((x.min(y), x.max(y)))
        };
        let d0 = self.digits.len();
        let mut size = 1i128;
        for c in 0..m {
            let (mut a, mut b) = (0i128, 0i128);
            for t in 0..n {
                let (x, y) = part(c, t)?;
                a = a.checked_add(x)?;
                b = b.checked_add(y)?;
            }
            let r = b.checked_sub(a)?.checked_add(1)?;
            self.digits.push(Digit {
                lo: a,
                radix: i64::try_from(r).ok()?,
                mult: i64::try_from(size).ok()?,
            });
            size = size.checked_mul(r).filter(|s| *s <= LIMIT)?;
        }
        let digits = &self.digits[d0..];
        let (a0, fill, steps) = (self.atoms.len(), &mut self.fill, &mut self.steps);
        dmax.clear();
        dmax.resize(m, 0);
        fill.push((0, 1, 0));
        for t in 0..n {
            let (mut delta, mut base) = (0i128, 0i128);
            for c in 0..m {
                let (x, y) = part(c, t)?;
                // Within the box: each digit stays below its radix.
                delta += ps[c * n + t] * i128::from(digits[c].mult);
                base += (ps[c * n + t] * ends(t).0 - x) * i128::from(digits[c].mult);
                dmax[c] += (y - x) as u128;
            }
            steps.push(Step { delta, base });
            let reach = (0..m).map(|c| dmax[c] as u64 * digits[c].mult as u64).sum();
            let boxes = dmax
                .iter()
                .fold(1u64, |p, d| p.saturating_mul(*d as u64 + 1));
            fill.push((reach, boxes, dmax[m - 1] as i64));
        }
        let top = (0, digits[m - 1].radix - 1);
        self.sig.extend_from_slice(sig);
        self.atoms.extend_from_slice(atoms);
        self.at.push(GroupAt {
            rows: r0,
            s,
            atoms: a0,
            n,
            digits: d0,
            m,
            top,
        });
        Some(())
    }
}

impl Group<'_> {
    /// The keys of the table of the first t atoms that some choice of the other atoms
    /// completes to a sum whose most significant digit is in `top`: its digit from
    /// `top.0` less the most the atoms after t add, to `top.1`.
    // Complexity tradeoff: O(1) per table. Bellman's tables (Bellman, "Dynamic Programming",
    // Princeton University Press, 1957) hold every sum of the first t atoms; this keeps only
    // those that can still meet the row, the bound pruning of Horowitz and Sahni ("Computing
    // partitions with applications to the knapsack problem", J. ACM 21(2), 1974). Exact: a key
    // outside it is the prefix of no point. Measured on subset sum with no point at k = 64:
    // the tables of the second half of the atoms hold only the sums within the rest of the
    // target, about half the words.
    fn window(&self, t: usize) -> (i64, i64) {
        let (last, top) = (self.fill[self.atoms.len()].2, self.fill[t].2);
        let (a, b) = (self.top.0 - (last - top), self.top.1.min(top));
        let m = self.digits[self.digits.len() - 1].mult;
        (a.max(0) * m, (b + 1) * m - 1)
    }

    /// Atom t's values as ranges: each its first value, the key added for it and the number of
    /// its values. Each key lies inside the group's box, below [`LIMIT`].
    fn ranges<'a>(
        &self,
        rows: &'a Rows,
        t: usize,
    ) -> impl Iterator<Item = (i128, i64, i64)> + Clone + 'a {
        let (Step { delta, base }, d) = (self.steps[t], &rows.domains[self.atoms[t]]);
        (d.iter()).map(move |&(l, h)| (l, (base + (l - d[0].0) * delta) as i64, (h - l + 1) as i64))
    }

    /// Atom t's key per unit of value, where it has two values or more (else unused).
    fn delta(&self, t: usize) -> i64 {
        i64::try_from(self.steps[t].delta).unwrap_or(i64::MAX)
    }

    /// Class c's sum in the key `g`.
    #[inline]
    fn sum(&self, g: i64, c: usize) -> i128 {
        let d = self.digits[c];
        i128::from(g / d.mult % d.radix) + d.lo
    }
}

/// The key of a layer: one digit per open row, its partial sum less its least value; the rows
/// that close at the next group are the most significant digits, the equations last.
#[derive(Clone, Copy)]
struct Layout<'a> {
    /// Each row with its digit, sorted by row.
    by_row: &'a [(usize, usize)],
    digits: &'a [Digit],
    size: i64,
}

/// The layouts of a plan, as [`Groups`]: layout i's r rows and digits from `at[i].0`, and its
/// number of keys.
#[derive(Default)]
struct Layouts {
    at: Vec<(usize, usize, i64)>,
    by_row: Vec<(usize, usize)>,
    digits: Vec<Digit>,
}

impl Layouts {
    #[inline]
    fn get(&self, i: usize) -> Layout<'_> {
        let (a, r, size) = self.at[i];
        Layout {
            by_row: &self.by_row[a..a + r],
            digits: &self.digits[a..a + r],
            size,
        }
    }

    /// Adds the layout of the rows `open`, sorted, by `kind`: 0 for a row that stays open, 1
    /// for an inequality and 2 for an equation that closes at the next group.
    // Complexity tradeoff: the digits are put in order of kind, then row, by one pass over the
    // sorted rows per kind, O(r), where sorting them cost O(r log r) and two more vectors.
    fn push(
        &mut self,
        open: &[usize],
        kind: impl Fn(usize) -> u8,
        lo: &[i128],
        hi: &[i128],
    ) -> Option<()> {
        debug_assert!(open.is_sorted());
        let a = self.by_row.len();
        self.by_row.resize(a + open.len(), (0, 0));
        let mut size = 1i128;
        for k in 0..3 {
            for (i, &r) in open.iter().enumerate() {
                if kind(r) != k {
                    continue;
                }
                let n = hi[r].checked_sub(lo[r])?.checked_add(1)?;
                self.by_row[a + i] = (r, self.digits.len() - a);
                self.digits.push(Digit {
                    lo: lo[r],
                    radix: i64::try_from(n).ok()?,
                    mult: i64::try_from(size).ok()?,
                });
                size = size.checked_mul(n).filter(|s| *s <= LIMIT)?;
            }
        }
        self.at.push((a, open.len(), size as i64));
        Some(())
    }
}

impl Layout<'_> {
    fn digit(&self, r: usize) -> Option<usize> {
        let i = self.by_row.binary_search_by_key(&r, |p| p.0).ok()?;
        Some(self.by_row[i].1)
    }
}

/// A row in the join of a layer and a group: its digit in the layer (weight, radix, least
/// value), its class and λ in the group, its constant and relation where it closes here, and
/// its digit in the next layer (least value, weight).
#[derive(Clone, Copy)]
struct Entry {
    x: Option<(i64, i64, i128)>,
    g: Option<(usize, i128)>,
    close: Option<(i128, bool)>,
    out: Option<(i128, i64)>,
}

/// The layer's one row, where the join is made with whole words: an equation with λ = ±1 that
/// maps the layer's digit `u` to the class digit `c - u` (`reflect`) or `u - c`, or an
/// inequality.
#[derive(Clone, Copy)]
enum Side {
    Eq { reflect: bool, c: i64 },
    Ge { l: i128, k: i128, lo: i128 },
}

/// A join made with whole words: the group has one class, and the layer at most one row,
/// which closes here; the next layer has at most one row, with λ = ±1 (`out`). `s`: the class
/// sums the rows that open and close here allow.
#[derive(Clone, Copy)]
struct Word {
    side: Option<Side>,
    s: (i128, i128),
    out: Option<bool>,
}

/// The equations closing at a join with a digit in the layer: weight, radix, least value,
/// class, λ, constant.
type Keyed = (i64, i64, i128, usize, i128, i128);

/// Closed intervals of values, `(least, greatest)`, in increasing order.
type Pieces = Vec<(i128, i128)>;

#[derive(Clone, Copy)]
struct Join<'a> {
    entries: &'a [Entry],
    keyed: &'a [Keyed],
    /// The number of keys of the layer with the keyed digits fixed.
    span: i64,
    word: Option<Word>,
}

/// Where a join's items lie in [`Joins`]: its entries and its keyed equations, each a start
/// and a count.
#[derive(Clone, Copy)]
struct JoinAt {
    entries: (usize, usize),
    keyed: (usize, usize),
    span: i64,
    word: Option<Word>,
}

/// The joins of a plan, as [`Groups`].
#[derive(Default)]
struct Joins {
    at: Vec<JoinAt>,
    entries: Vec<Entry>,
    keyed: Vec<Keyed>,
}

impl Joins {
    #[inline]
    fn get(&self, i: usize) -> Join<'_> {
        let JoinAt {
            entries: (e, ne),
            keyed: (k, nk),
            span,
            word,
        } = self.at[i];
        Join {
            entries: &self.entries[e..e + ne],
            keyed: &self.keyed[k..k + nk],
            span,
            word,
        }
    }
}

/// The joins of a formula, planned from its rows before any table is built.
struct Plan {
    groups: Groups,
    /// Layout i: the key of the layer before group i.
    layouts: Layouts,
    /// Join i: of the layer before group i and the group's table.
    joins: Joins,
    /// The atoms in no row.
    free: Vec<usize>,
}

/// The tables of a forward pass: each group's prefix tables, and the layers.
struct Tables {
    /// Every group's prefix tables, group after group: table k of group i, the sum of its
    /// first k atoms, at [`Plan::table`]`(i) + k`.
    // Complexity tradeoff: one vector, in place of one made and freed per group.
    prefix: Vec<Set>,
    layers: Vec<Set>,
    /// For a join made with words, the class digits that meet the rows closing there.
    met: Vec<Set>,
}

#[derive(Clone, Copy)]
enum Pass<'a> {
    Decide,
    Point,
    Project(&'a [bool]),
}

/// Each atom's signature, its rows in order, and its coefficients on them: those of atom j at
/// `at[j]..at[j + 1]`.
struct Sigs {
    at: Vec<usize>,
    rows: Vec<usize>,
    coefs: Vec<i128>,
}

impl Sigs {
    fn of(rows: &Rows) -> Sigs {
        let n = rows.atoms.len();
        let mut at = vec![0; n + 1];
        for row in &rows.rows {
            for &(j, _) in &row.terms {
                at[j + 1] += 1;
            }
        }
        for j in 0..n {
            at[j + 1] += at[j];
        }
        let (mut sig, mut coefs) = (vec![0; at[n]], vec![0; at[n]]);
        // Each atom's start serves as its cursor, ending at the next atom's start.
        for (r, row) in rows.rows.iter().enumerate() {
            for &(j, c) in &row.terms {
                (sig[at[j]], coefs[at[j]]) = (r, c);
                at[j] += 1;
            }
        }
        at.rotate_right(1);
        at[0] = 0;
        Sigs {
            at,
            rows: sig,
            coefs,
        }
    }

    fn sig(&self, j: usize) -> &[usize] {
        &self.rows[self.at[j]..self.at[j + 1]]
    }
}

impl Plan {
    /// The plan, or `None` where a key passes [`LIMIT`] or a sum `i128`: the solver answers.
    fn of(rows: &Rows, want: &[bool]) -> Option<Plan> {
        let sigs = Sigs::of(rows);
        // The groups: the atoms of each signature, in order of signature, the atoms projected
        // onto last (so the pass back over a group's atoms, [`Plan::project`], stops at the
        // first of them), then by atom.
        // Complexity tradeoff: one sort of the atoms, O(a log a) comparisons of signatures, as
        // the map from each signature to its atoms it replaces, without a vector per group.
        let wanted = |j: usize| want.get(j).copied().unwrap_or(false);
        let (mut free, mut order) = (Vec::new(), Vec::with_capacity(rows.atoms.len()));
        for j in 0..rows.atoms.len() {
            if sigs.sig(j).is_empty() {
                free.push(j)
            } else {
                order.push(j)
            }
        }
        order.sort_unstable_by(|&a, &b| {
            sigs.sig(a)
                .cmp(sigs.sig(b))
                .then(wanted(a).cmp(&wanted(b)))
                .then(a.cmp(&b))
        });
        let mut groups = Groups::with_capacity(order.len(), sigs.rows.len());
        let mut last = vec![0; rows.rows.len()];
        let mut sc = Scratch::default();
        for atoms in order.chunk_by(|&a, &b| sigs.sig(a) == sigs.sig(b)) {
            let (i, sig) = (groups.at.len(), sigs.sig(atoms[0]));
            for &r in sig {
                last[r] = i;
            }
            groups.push(rows, &sigs, sig, atoms, &mut sc)?;
        }
        // Each row's least and greatest partial sum, after each group in turn.
        let n = rows.rows.len();
        let (mut lo, mut hi) = (vec![0i128; n], vec![0i128; n]);
        let (mut open, mut next): (Vec<usize>, Vec<usize>) = (Vec::new(), Vec::new());
        let mut layouts = Layouts::default();
        for i in 0..groups.at.len() {
            let g = groups.get(i);
            let kind = |r: usize| match (last[r] == i, rows.rows[r].eq) {
                (false, _) => 0,
                (true, false) => 1,
                (true, true) => 2,
            };
            layouts.push(&open, kind, &lo, &hi)?;
            for (&r, &(c, l)) in g.sig.iter().zip(g.of_row) {
                let d = g.digits[c];
                let hi_c = d.lo.checked_add(i128::from(d.radix) - 1)?;
                let (a, b) = (l.checked_mul(d.lo)?, l.checked_mul(hi_c)?);
                lo[r] = lo[r].checked_add(a.min(b))?;
                hi[r] = hi[r].checked_add(a.max(b))?;
            }
            merge_into(&open, g.sig, |r| last[r] != i, &mut next);
            std::mem::swap(&mut open, &mut next);
        }
        layouts.push(&[], |_| 0, &lo, &hi)?;
        // Every sum with its row's constant stays well inside `i128`.
        let small = |v: i128| v.checked_abs().is_some_and(|a| a < 1 << 120);
        for (r, row) in rows.rows.iter().enumerate() {
            if !(small(row.k) && small(lo[r]) && small(hi[r])) {
                return None;
            }
        }
        // Each group's most significant class: the values of its sum that meet each of the
        // group's rows of it, the other groups' sums on the row between their least and
        // greatest.
        for i in 0..groups.at.len() {
            let g = groups.get(i);
            let (c, d) = (g.digits.len() - 1, g.digits[g.digits.len() - 1]);
            let (a, b) = (d.lo, d.lo + i128::from(d.radix) - 1);
            let mut s = (a, b);
            for (&r, &(cr, l)) in g.sig.iter().zip(g.of_row) {
                if cr != c {
                    continue;
                }
                let (x, y) = ((l * a).min(l * b), (l * a).max(l * b));
                let (k, others) = (
                    rows.rows[r].k,
                    (lo[r].checked_sub(x)?, hi[r].checked_sub(y)?),
                );
                let ge = meets(l, k.checked_add(others.1)?, false);
                let le = match rows.rows[r].eq {
                    true => meets(-l, k.checked_add(others.0)?.checked_neg()?, false),
                    false => (i128::MIN, i128::MAX),
                };
                s = (s.0.max(ge.0).max(le.0), s.1.min(ge.1).min(le.1));
            }
            // Within -1 and the digit's radix, also where no value meets the rows.
            groups.at[i].top = (
                (s.0 - a).min(i128::from(d.radix)) as i64,
                (s.1 - a).max(-1) as i64,
            );
        }
        let mut joins = Joins::default();
        for i in 0..groups.at.len() {
            joins.push(
                rows,
                &last,
                i,
                groups.get(i),
                layouts.get(i),
                layouts.get(i + 1),
            )?;
        }
        Some(Plan {
            groups,
            layouts,
            joins,
            free,
        })
    }
}

impl Joins {
    /// Adds the join of layout `x`, before group i, with group `g`, the next layer `y`; `last`:
    /// each row's last group.
    fn push(
        &mut self,
        rows: &Rows,
        last: &[usize],
        i: usize,
        g: Group,
        x: Layout,
        y: Layout,
    ) -> Option<()> {
        // The rows of the layer and of the group, both sorted by row, merged.
        let (xs, gs) = (x.by_row, g.sig);
        let e0 = self.entries.len();
        let entries = &mut self.entries;
        let (mut a, mut b) = (0, 0);
        while a < xs.len() || b < gs.len() {
            let r = match (xs.get(a), gs.get(b)) {
                (Some(&(p, _)), Some(&q)) => p.min(q),
                (Some(&(p, _)), None) => p,
                (None, Some(&q)) => q,
                (None, None) => break,
            };
            let mut e = Entry {
                x: None,
                g: None,
                close: (last[r] == i).then(|| (rows.rows[r].k, rows.rows[r].eq)),
                out: y.digit(r).map(|d| (y.digits[d].lo, y.digits[d].mult)),
            };
            if let Some(&(p, d)) = xs.get(a)
                && p == r
            {
                let d = x.digits[d];
                e.x = Some((d.mult, d.radix, d.lo));
                a += 1;
            }
            if gs.get(b) == Some(&r) {
                e.g = Some(g.of_row[b]);
                b += 1;
            }
            entries.push(e);
        }
        let k0 = self.keyed.len();
        let entries = &self.entries[e0..];
        self.keyed
            .extend((entries.iter()).filter_map(|e| match (e.x, e.g, e.close) {
                (Some((m, r, lo)), Some((c, l)), Some((k, true))) => Some((m, r, lo, c, l, k)),
                _ => None,
            }));
        let keyed = &self.keyed[k0..];
        let span = keyed.iter().map(|k| k.0).min().unwrap_or(x.size);
        // The join is made with words where the group has one class, the layer at most one
        // row and it closes here, and the next layer at most one row with λ = ±1.
        let word = (|| {
            if g.digits.len() != 1 || x.by_row.len() > 1 || y.by_row.len() > 1 {
                return None;
            }
            let lc = g.digits[0].lo;
            let mut s = (i128::MIN, i128::MAX);
            let mut side = None;
            for e in entries {
                let (c, l) = e.g?;
                debug_assert_eq!(c, 0);
                match (e.x, e.close) {
                    (None, Some((k, eq))) => {
                        let (a, b) = meets(l, k, eq);
                        s = (s.0.max(a), s.1.min(b));
                    }
                    (Some((_, _, lo)), Some((k, true))) if l.abs() == 1 => {
                        // l = 1: s = -k - σ, the digit `-k - lo - lc - u`; l = -1: `k + lo - lc + u`.
                        let c = if l == 1 { -k - lo - lc } else { k + lo - lc };
                        side = Some(Side::Eq {
                            reflect: l == 1,
                            c: i64::try_from(c).ok()?,
                        });
                    }
                    (Some((_, _, lo)), Some((k, false))) => side = Some(Side::Ge { l, k, lo }),
                    (None, None) if l.abs() == 1 => {}
                    _ => return None,
                }
            }
            let out = match y.by_row.first() {
                None => None,
                Some(&(r, _)) => Some(g.of_row[g.sig.binary_search(&r).ok()?].1 == 1),
            };
            Some(Word { side, s, out })
        })();
        self.at.push(JoinAt {
            entries: (e0, entries.len()),
            keyed: (k0, keyed.len()),
            span,
            word,
        });
        Some(())
    }
}

impl Plan {
    #[inline]
    fn group(&self, i: usize) -> Group<'_> {
        self.groups.get(i)
    }

    #[inline]
    fn join(&self, i: usize) -> Join<'_> {
        self.joins.get(i)
    }

    /// Where the tables of group i start in [`Tables::prefix`]: after the a + 1 tables of each
    /// group before it, as its sums start in [`Groups::fill`].
    #[inline]
    fn table(&self, i: usize) -> usize {
        self.groups.at[i].atoms + i
    }

    /// Group i's table of its whole sum, the last of its prefix tables.
    #[inline]
    fn sum<'t>(&self, prefix: &'t [Set], i: usize) -> &'t Set {
        &prefix[self.table(i) + self.groups.at[i].n]
    }

    /// The number of groups, and of joins.
    #[inline]
    fn len(&self) -> usize {
        self.groups.at.len()
    }

    /// The key in the next layer of the pair of `x` in the layer and `g` in the table of group
    /// `gr`, where the pair meets every row that closes at its join `j`.
    #[inline]
    fn meet(gr: Group, j: Join, x: i64, g: i64) -> Option<i64> {
        let mut y = 0;
        for e in j.entries {
            let mut t = 0;
            if let Some((m, r, lo)) = e.x {
                t += i128::from(x / m % r) + lo;
            }
            if let Some((c, l)) = e.g {
                t += l * gr.sum(g, c);
            }
            if let Some((k, eq)) = e.close
                && (if eq { t + k != 0 } else { t + k < 0 })
            {
                return None;
            }
            if let Some((lo, m)) = e.out {
                y += (t - lo) as i64 * m;
            }
        }
        Some(y)
    }

    /// Each pair of `x` in `layer` and `g` in `table` that meets the rows closing at group i,
    /// given to `visit` with the key of the totals in the next layer.
    // Complexity tradeoff: the layer's digits of the equations closing here are its most
    // significant, so each g finds the keys it needs as one interval of the layer, read word by
    // word: O(|t| · (log + words of the interval)) plus the pairs that match. Naive version:
    // every pair, |f|·|t|; used: the lookup (Horowitz and Sahni's meet in the middle), so two
    // tables joined on an equation cost the sum of their sizes, not the product.
    fn pairs(
        &self,
        i: usize,
        layer: &Set,
        table: &Set,
        work: &mut Work,
        mut visit: impl FnMut(i64, i64, i64, &mut Work) -> Option<()>,
    ) -> Option<()> {
        let (gr, j) = (self.group(i), self.join(i));
        work.spend(table.words())?;
        let scan = layer.lookup() + layer.words().min(j.span as u64 / 64 + 2);
        'g: for g in table.keys() {
            work.spend(1 + scan)?;
            let mut from = 0;
            for &(m, r, lo, c, l, k) in j.keyed {
                let u = -k - l * gr.sum(g, c) - lo;
                if u < 0 || u >= i128::from(r) {
                    continue 'g;
                }
                from += u as i64 * m;
            }
            for x in layer.keys_in(from, from + j.span) {
                work.spend(1)?;
                if let Some(y) = Plan::meet(gr, j, x, g) {
                    visit(x, g, y, work)?;
                }
            }
        }
        Some(())
    }

    /// The class digits of group i's `table` that meet the rows closing there with some key of
    /// `layer`, and the next layer, for a join made with words.
    fn word_join(
        &self,
        i: usize,
        w: Word,
        layer: &Set,
        table: &Set,
        work: &mut Work,
    ) -> Option<(Set, Set)> {
        let gr = self.group(i);
        let (lc, span) = (gr.digits[0].lo, gr.digits[0].radix - 1);
        let mut s = w.s;
        let mut met = None;
        match w.side {
            Some(Side::Eq { reflect, c }) => {
                met = Some(if reflect {
                    work.and_reflected(table, layer, c)?
                } else {
                    work.and_shifted(table, layer, c)?
                });
            }
            Some(Side::Ge { l, k, lo }) => {
                work.spend(1)?;
                let (a, b) = meets(l, k + lo + i128::from(layer.max()?), false);
                s = (s.0.max(a), s.1.min(b));
            }
            None => {}
        }
        let met = work.clip(
            met.as_ref().unwrap_or(table),
            s.0.saturating_sub(lc),
            s.1.saturating_sub(lc),
        )?;
        let next = match w.out {
            None if met.is_empty() => Set::default(),
            None => {
                work.spend(1)?;
                Set::one(0)
            }
            Some(true) => work.copy(&met)?,
            Some(false) => work.reflect(&met, span)?,
        };
        Some((met, next))
    }

    /// The forward pass, or `None` where the allowance runs out; `Some(None)` where the rows
    /// have no point.
    fn forward(&self, rows: &Rows, work: &mut Work) -> Option<Option<Tables>> {
        let mut prefix: Vec<Set> = Vec::with_capacity(self.groups.atoms.len() + self.len());
        for (i, g) in (0..self.len()).map(|i| self.group(i)).enumerate() {
            debug_assert_eq!(prefix.len(), self.table(i));
            prefix.push(Set::one(0));
            for k in 0..g.atoms.len() {
                let mut next = self.add(prefix.last()?, g.ranges(rows, k), g.delta(k), work)?;
                let (lo, hi) = g.window(k + 1);
                work.spend(1)?;
                if (next.min())
                    .zip(next.max())
                    .is_some_and(|(a, b)| a < lo || b > hi)
                {
                    work.spend(next.words() + 1)?;
                    next.keep(lo, hi);
                }
                next = Set::settled(next.lit, next.fill);
                prefix.push(next);
            }
        }
        let mut layers = vec![Set::one(0)];
        let mut met = Vec::with_capacity(self.len());
        for i in 0..self.len() {
            let (layer, table) = (&layers[i], self.sum(&prefix, i));
            let (m, next) = match self.join(i).word {
                Some(w) => self.word_join(i, w, layer, table, work)?,
                None => {
                    let mut ys = Vec::new();
                    self.pairs(i, layer, table, work, |_, _, y, _| {
                        ys.push(y);
                        Some(())
                    })?;
                    work.spend(sorted(ys.len() as u64) + ys.len() as u64)?;
                    (Set::default(), Set::of(&mut ys))
                }
            };
            if next.is_empty() {
                return Some(None);
            }
            met.push(m);
            layers.push(next);
        }
        Some(Some(Tables {
            prefix,
            layers,
            met,
        }))
    }

    /// `t` with the atom of step `st` added: the union over its values v of `t` shifted by v's
    /// key. A range of n values is added by doubling: the shifts by 1, 2, 4, .. steps, merged,
    /// in `bits(n - 1)` rounds (each value is reached by the binary digits of its distance
    /// from the range's first).
    // Complexity tradeoff: value by value costs n shifts and unions of the table for a range
    // of n values; doubling costs log n.
    fn add(
        &self,
        t: &Set,
        ranges: impl Iterator<Item = (i128, i64, i64)>,
        delta: i64,
        work: &mut Work,
    ) -> Option<Set> {
        let mut acc: Option<Cow<Set>> = None;
        for (_, off, n) in ranges {
            if off == 0 && n == 1 {
                // `t` itself, charged as its copy.
                work.spend(t.words() + 1)?;
                acc = Some(match acc {
                    None => Cow::Borrowed(t),
                    Some(a) => Cow::Owned(work.union(&a, t)?),
                });
                continue;
            }
            let mut u = work.shift(t, off)?;
            let mut done = 1;
            while done < n {
                let s = done.min(n - done);
                u = work.union_shifted(&u, s * delta)?;
                done += s;
            }
            acc = Some(Cow::Owned(match acc {
                None => u,
                Some(a) => work.union(&a, &u)?,
            }));
        }
        Some(acc.map_or_else(Set::default, Cow::into_owned))
    }

    /// The pass back: each layer's keys and each group's sums that some choice after them
    /// completes to a point.
    // Complexity tradeoff: the same operations as the forward pass, each run back: O(forward).
    fn back(&self, t: &Tables, work: &mut Work) -> Option<(Vec<Set>, Vec<Set>)> {
        let p = self.len();
        let mut good: Vec<Set> = std::iter::repeat_with(Set::default).take(p + 1).collect();
        let mut sums: Vec<Set> = std::iter::repeat_with(Set::default).take(p).collect();
        good[p] = work.copy(&t.layers[p])?;
        for i in (0..p).rev() {
            let (layer, gy) = (&t.layers[i], &good[i + 1]);
            let (gx, gg) = match self.join(i).word {
                Some(w) => {
                    let gr = self.group(i);
                    let (lc, span, met) = (gr.digits[0].lo, gr.digits[0].radix - 1, &t.met[i]);
                    let gm = match w.out {
                        None if gy.is_empty() => Set::default(),
                        None => work.copy(met)?,
                        Some(true) => work.and(met, gy)?,
                        Some(false) => work.and_reflected(met, gy, span)?,
                    };
                    let gx = match w.side {
                        _ if gm.is_empty() => Set::default(),
                        None => work.copy(layer)?,
                        Some(Side::Eq { reflect: true, c }) => work.and_reflected(layer, &gm, c)?,
                        Some(Side::Eq { reflect: false, c }) => work.and_shifted(layer, &gm, -c)?,
                        Some(Side::Ge { l, k, lo }) => {
                            work.spend(1)?;
                            let s = if l > 0 { gm.max()? } else { gm.min()? };
                            // σ + l·s + k >= 0 for the best s.
                            let from = -k - l * (i128::from(s) + lc) - lo;
                            work.clip(layer, from, LIMIT)?
                        }
                    };
                    (gx, gm)
                }
                None => {
                    let (mut xs, mut gs) = (Vec::new(), Vec::new());
                    let table = self.sum(&t.prefix, i);
                    self.pairs(i, layer, table, work, |x, g, y, work| {
                        work.spend(gy.lookup())?;
                        if gy.contains(y) {
                            xs.push(x);
                            gs.push(g);
                        }
                        Some(())
                    })?;
                    let n = xs.len() as u64;
                    work.spend(2 * (sorted(n) + n))?;
                    (Set::of(&mut xs), Set::of(&mut gs))
                }
            };
            good[i] = gx;
            sums[i] = gg;
        }
        Some((good, sums))
    }

    /// A point of the rows, `Some(None)` where they have none.
    fn point(&self, rows: &Rows, work: &mut Work) -> Option<Option<Model>> {
        let Some(t) = self.forward(rows, work)? else {
            return Some(None);
        };
        let (good, sums) = self.back(&t, work)?;
        let mut m = Model::new();
        let mut x = 0;
        for (i, gr) in (0..self.len()).map(|i| self.group(i)).enumerate() {
            work.spend(sums[i].words())?;
            let j = self.join(i);
            let each = 2 + good[i + 1].lookup();
            let mut pick = None;
            for g in sums[i].keys() {
                work.spend(each)?;
                if let Some(y) = Plan::meet(gr, j, x, g)
                    && good[i + 1].contains(y)
                {
                    pick = Some((g, y));
                    break;
                }
            }
            let (mut key, y) = pick?;
            // The group's sum is taken apart from its last atom back: some value of the atom
            // leaves a sum of the table before it.
            for tt in (0..gr.atoms.len()).rev() {
                let (a, before, delta) =
                    (gr.atoms[tt], &t.prefix[self.table(i) + tt], gr.delta(tt));
                let each = before.lookup();
                let mut found = None;
                'v: for (v0, off, n) in gr.ranges(rows, tt) {
                    for e in 0..n {
                        work.spend(each)?;
                        let rest = key - off - if e == 0 { 0 } else { e * delta };
                        if before.contains(rest) {
                            found = Some((v0 + i128::from(e), rest));
                            break 'v;
                        }
                    }
                }
                let (v, rest) = found?;
                m.insert(rows.atoms[a].clone(), Int::from(v));
                key = rest;
            }
            x = y;
        }
        for &a in &self.free {
            m.insert(rows.atoms[a].clone(), Int::from(rows.domains[a][0].0));
        }
        Some(Some(m))
    }

    /// Each wanted atom's set of values over the points of the rows.
    fn project(
        &self,
        rows: &Rows,
        want: &[bool],
        work: &mut Work,
    ) -> Option<Vec<Option<IntervalSet>>> {
        let fin = |v: i128| End::Fin(Num::from(v));
        let mut sets: Vec<Option<IntervalSet>> = vec![None; rows.atoms.len()];
        let Some(t) = self.forward(rows, work)? else {
            for (a, w) in want.iter().enumerate() {
                if *w {
                    sets[a] = Some(IntervalSet::empty());
                }
            }
            return Some(sets);
        };
        for &a in &self.free {
            if want[a] {
                let ranges = rows.domains[a].iter().map(|&(l, h)| (fin(l), fin(h)));
                sets[a] = Some(IntervalSet::from_pieces(ranges.collect()));
            }
        }
        let (_, mut sums) = self.back(&t, work)?;
        // The sets of the walk value by value, written over from one value, atom and group to the
        // next: the sums kept so far, one value's sums, and the union of the two.
        // Complexity tradeoff: a set made and freed per value and per union cost two to three
        // allocations each (xst collective chain: the walk 17% above the tables of main).
        let (mut kept, mut s, mut spare) = (Set::default(), Set::default(), Set::default());
        for (i, gr) in (0..self.len()).map(|i| self.group(i)).enumerate() {
            let Some(first) = gr.atoms.iter().position(|&a| want[a]) else {
                continue;
            };
            // From the group's last atom back to its first wanted one: the sums before each
            // atom that some value of it completes to a marked sum, and the values that do.
            // Moved out, charged as its copy.
            let mut good = std::mem::take(&mut sums[i]);
            work.spend(good.words() + 1)?;
            for tt in (first..gr.atoms.len()).rev() {
                let (before, delta) = (&t.prefix[self.table(i) + tt], gr.delta(tt));
                if let Some((kept, pieces)) =
                    Plan::by_intervals(before, &good, gr.ranges(rows, tt), delta, work)?
                {
                    if want[gr.atoms[tt]] {
                        let pieces = pieces.into_iter().map(|(l, h)| (fin(l), fin(h))).collect();
                        sets[gr.atoms[tt]] = Some(IntervalSet::from_pieces(pieces));
                    }
                    good = kept;
                    continue;
                }
                kept.clear();
                let mut pieces: Vec<(End, End)> = Vec::new();
                for (v0, off, n) in gr.ranges(rows, tt) {
                    for e in 0..n {
                        let d = off + if e == 0 { 0 } else { e * delta };
                        // The sums b of `before` with b + d in `good`: `before ∩ (good − d)`, one
                        // shift (no key of `good` below d is b + d for a key b >= 0).
                        work.and_shifted_into(before, &good, -d, &mut s)?;
                        if s.is_empty() {
                            continue;
                        }
                        if kept.is_empty() {
                            work.spend(s.words() + 1)?;
                            std::mem::swap(&mut kept, &mut s);
                        } else {
                            work.union_into(&kept, &s, &mut spare)?;
                            std::mem::swap(&mut kept, &mut spare);
                        }
                        let v = v0 + i128::from(e);
                        match pieces.last_mut() {
                            Some((_, End::Fin(h))) if *h == Num::from(v - 1) => *h = Num::from(v),
                            _ => pieces.push((fin(v), fin(v))),
                        }
                    }
                }
                if want[gr.atoms[tt]] {
                    sets[gr.atoms[tt]] = Some(IntervalSet::from_pieces(pieces));
                }
                std::mem::swap(&mut good, &mut kept);
            }
        }
        Some(sets)
    }

    /// One step of [`Plan::project`] read from intervals: an atom's values (`ranges`, its key
    /// changing by `delta` per value) that some sum of `before` completes to a sum of `good`, as
    /// pieces of values, and the sums of `before` that some such value completes. `Some(None)`
    /// where the atom's key moves by more than one per value, or where this costs more than the
    /// value-by-value walk would; `None` where the allowance runs out.
    // Complexity tradeoff: value by value, each of the atom's c values costs a shift of `before`
    // and an intersection with `good`, O(c·(w_b + w_g)) for sets of w_b and w_g words; for a
    // difference row `x − y >= 0` over two atoms of 1,025 values each, a question of size 7,
    // that walk cost 105K units and 48K allocations, and the solver answers it from intervals.
    // Here a value d of the key works exactly where d lies in `good − before`, the union of
    // `[g.lo − b.hi, g.hi − b.lo]` over the r_b intervals of `before` and the r_g of `good`; the
    // keys kept are `before ∩ (good − K)` for the keys K of the values that work, again by
    // pairs of intervals: O(w_b + w_g + r_b·r_g·log(r_b·r_g) + r_g·r_k·log) for r_k intervals of
    // K. Both are exact; the cheaper one runs, by the costs predicted from the counts, so this
    // never spends more than the walk would beyond reading the two sets once.
    fn by_intervals(
        before: &Set,
        good: &Set,
        ranges: impl Iterator<Item = (i128, i64, i64)> + Clone,
        delta: i64,
        work: &mut Work,
    ) -> Option<Option<(Set, Pieces)>> {
        let (mut len, mut count, mut wide) = (0u64, 0u64, false);
        for (_, _, n) in ranges.clone() {
            (len, count, wide) = (len + 1, count.saturating_add(n as u64), wide || n > 1);
        }
        work.spend(1 + len)?;
        if wide && delta.abs() != 1 {
            return Some(None);
        }
        if before.is_empty() || good.is_empty() {
            // No sum of `before` completes to one of `good`: no value works and no sum is kept.
            return Some(Some((Set::default(), Vec::new())));
        }
        let (wb, wg) = (before.words(), good.words());
        let walk = count.saturating_mul(wb + wg + 2);
        // The least cost predicted below, at one interval in each set, read from the counts
        // alone: where it exceeds the walk, the walk runs and neither set is read.
        let least = sorted(1)
            .saturating_add(sorted(1 + len).saturating_mul(2))
            .saturating_add(1 + len)
            .saturating_add(wb + 1);
        if least > walk {
            return Some(None);
        }
        let ranges: Vec<(i128, i64, i64)> = ranges.collect();
        // With the `1 + len` above, `wb + wg + 2 + len` in all before the sets are read.
        work.spend(wb + wg + 1)?;
        // Reading the intervals stops past `walk` of them, which is charged.
        let Some(bs) = before.intervals(walk) else {
            work.spend(walk)?;
            return Some(None);
        };
        work.spend(bs.len() as u64)?;
        let Some(gs) = good.intervals(walk) else {
            work.spend(walk)?;
            return Some(None);
        };
        work.spend(gs.len() as u64)?;
        let (rb, rg) = (bs.len() as u64, gs.len() as u64);
        let pairs = rb.saturating_mul(rg);
        let rk = pairs.saturating_add(ranges.len() as u64);
        let cost = |n: u64| n.saturating_mul(1 + bits(n));
        let predicted = cost(pairs)
            .saturating_add(cost(rk))
            .saturating_add(cost(rg.saturating_mul(rk)))
            .saturating_add(rg.saturating_mul(rk))
            .saturating_add(wb + 1);
        if predicted > walk {
            return Some(None);
        }
        work.spend(cost(pairs))?;
        let mut diff = Vec::with_capacity(pairs as usize);
        for &(ga, gh) in &gs {
            for &(ba, bh) in &bs {
                diff.push((ga - bh, gh - ba));
            }
        }
        let diff = joined(diff);
        // Each range's values whose key change lies in `diff`, in increasing value; the key
        // changes that work.
        let (mut pieces, mut ks): (Pieces, Vec<(i64, i64)>) = (Vec::new(), Vec::new());
        for &(v0, off, n) in &ranges {
            let d = if n == 1 { 1 } else { delta };
            let (lo, hi) = (off.min(off + (n - 1) * d), off.max(off + (n - 1) * d));
            let from = diff.partition_point(|&(_, h)| h < lo);
            work.spend(1 + bits(diff.len() as u64))?;
            let start = pieces.len();
            for &(p, q) in diff[from..].iter().take_while(|&&(p, _)| p <= hi) {
                work.spend(1)?;
                let (p, q) = (p.max(lo), q.min(hi));
                ks.push((p, q));
                // Value v0 + e has key change off + e·d.
                let (e1, e2) = if d == 1 {
                    (p - off, q - off)
                } else {
                    (off - q, off - p)
                };
                pieces.push((v0 + i128::from(e1), v0 + i128::from(e2)));
            }
            if d == -1 {
                pieces[start..].reverse();
            }
        }
        work.spend(cost(ks.len() as u64))?;
        let ks = joined(ks);
        let mut back = Vec::with_capacity(gs.len() * ks.len());
        work.spend(cost((gs.len() * ks.len()) as u64))?;
        for &(ga, gh) in &gs {
            for &(ka, kh) in &ks {
                if gh - ka >= 0 {
                    back.push(((ga - kh).max(0), gh - ka));
                }
            }
        }
        let back = Set {
            lit: Lits::default(),
            fill: joined(back),
        };
        let kept = work.and(before, &back)?;
        Some(Some((kept, pieces)))
    }

    /// A bound on the units the pass spends, adding up each operation's charge with each set
    /// bounded by the number of its keys and by its words: a table of the first t atoms of a
    /// group holds at most the product of their numbers of values, at most the product of its
    /// digits' ranges, and one word per 64 keys up to its largest key. A run given this
    /// allowance is never stopped for want of it. Saturates at `u64::MAX`.
    // Complexity tradeoff: O(a + p·r) for a atoms, p groups and r rows, no table built.
    fn bound(&self, rows: &Rows, pass: Pass) -> u64 {
        let mut units = 0u64;
        let mut add = |u: u64| units = units.saturating_add(u);
        let count = |t: usize, g: &Group| {
            (rows.domains[g.atoms[t]].iter())
                .fold(0u64, |c, &(l, h)| c.saturating_add((h - l + 1) as u64))
        };
        // Each group's tables: keys and words, in one vector, group after group: group i's
        // a + 1 entries start at `o`, after those of the groups before it.
        let mut nw: Vec<(u64, u64)> = Vec::with_capacity(self.groups.atoms.len() + self.len());
        let mut last = Vec::with_capacity(self.len());
        for g in (0..self.len()).map(|i| self.group(i)) {
            let o = nw.len();
            nw.push((1u64, 1u64));
            for t in 0..g.atoms.len() {
                let (reach, boxes, _) = g.fill[t + 1];
                let n = nw[o + t].0.saturating_mul(count(t, &g)).min(boxes);
                // A range's table, and each set its doubling makes, is within the table shifted
                // by all the range's values: of w0 words, so at most w0 runs, each run of L words
                // covering at most L + 2 + (len - 1)·delta/64 words. The union of the ranges'
                // tables is within the sum of theirs.
                let (w0, cap) = (nw[o + t].1, n.min(reach / 64 + 1));
                let mut w1 = 0u64;
                for (k, r) in g.ranges(rows, t).enumerate() {
                    let spread = ((r.2 - 1) as u64).saturating_mul(g.delta(t) as u64) / 64;
                    let own = w0.saturating_mul(spread.saturating_add(3)).min(cap);
                    w1 = w1.saturating_add(own).min(cap);
                    add(w0 + 1);
                    add(bits(r.2 as u64 - 1).saturating_mul(3 * own + 2));
                    if k > 0 {
                        add(2 * w1 + 1);
                    }
                }
                // The clip to the window, and the table within it.
                add(w1 + 2);
                let (lo, hi) = g.window(t + 1);
                let width = u64::try_from(hi - lo + 1).unwrap_or(0);
                nw.push((n.min(width), w1.min(width / 64 + 2)));
            }
            last.push(nw[nw.len() - 1]);
        }
        // The layers, and each join's charges forward and back.
        let (mut layers, mut met) = (
            Vec::with_capacity(self.len() + 1),
            Vec::with_capacity(self.len()),
        );
        layers.push((1u64, 1u64));
        let mut back = 0u64;
        for (i, j) in (0..self.len()).map(|i| self.join(i)).enumerate() {
            let ((nx, wx), (ng, wg)) = (layers[i], last[i]);
            let size = self.layouts.get(i + 1).size as u64;
            let (mut ny, mut wy);
            match j.word {
                Some(w) => {
                    let (nm, wm) = match w.side {
                        Some(Side::Eq { .. }) => {
                            add(2 * (wx + 1) + wg + (2 * wx).min(nx) + 1);
                            (ng.min(nx), wg.min(nx))
                        }
                        _ => {
                            add(1);
                            (ng, wg)
                        }
                    };
                    add(wg + 1);
                    add(2 * (wm + 1));
                    (ny, wy) = (nm, (2 * wm).min(nm));
                    if w.out.is_none() {
                        (ny, wy) = (1, 1);
                    }
                    // Back: the marks of the class digits, then of the layer.
                    back = back.saturating_add(2 * (wy + 1) + wm + (2 * wy).min(ny) + 1);
                    back = back.saturating_add(2 * (wm + 1) + wx + (2 * wm).min(nm) + 1 + 1);
                    met.push((nm, wm));
                }
                None => {
                    let span = j.span as u64;
                    let matched = ng.saturating_mul(nx.min(span));
                    let walk = (wg + ng.saturating_mul(2 + bits(wx) + wx.min(span / 64 + 2)))
                        .saturating_add(matched);
                    add(walk.saturating_add(sorted(matched)).saturating_add(matched));
                    (ny, wy) = (matched, matched);
                    let marks = 2 * (sorted(matched).saturating_add(matched));
                    let looked = matched.saturating_mul(1 + bits(wy.min(size / 64 + 1)));
                    back = back
                        .saturating_add(walk)
                        .saturating_add(marks)
                        .saturating_add(looked);
                    met.push((ng, wg));
                }
            }
            ny = ny.min(size);
            wy = wy.min(ny).min((size - 1) / 64 + 1);
            layers.push((ny, wy));
        }
        if matches!(pass, Pass::Decide) {
            return units;
        }
        add(back.saturating_add(layers.last().map_or(1, |l| l.1) + 1));
        let mut o = 0;
        for (i, g) in (0..self.len()).map(|i| self.group(i)).enumerate() {
            let t = &nw[o..o + g.atoms.len() + 1];
            o += g.atoms.len() + 1;
            let (ng, wg) = met[i];
            match pass {
                Pass::Point => {
                    add(wg + ng.saturating_mul(2 + 1 + bits(layers[i + 1].1)));
                    for (k, tk) in t[..g.atoms.len()].iter().enumerate() {
                        add(count(k, &g).saturating_mul(1 + bits(tk.1)));
                    }
                }
                Pass::Project(want) => {
                    let Some(first) = g.atoms.iter().position(|&a| want[a]) else {
                        continue;
                    };
                    add(wg + 1);
                    for k in first..g.atoms.len() {
                        // The walk value by value, and before it at most three times its cost reading the
                        // sets as intervals ([`Plan::by_intervals`]).
                        add(count(k, &g).saturating_mul(8 * t[k].1 + 5 * t[k + 1].1 + 11));
                    }
                }
                Pass::Decide => {}
            }
        }
        units
    }
}

/// The rows of `a` and of `b`, both sorted, that `keep` keeps, once each and sorted, written to
/// `out`.
// Complexity tradeoff: one merge, O(|a| + |b|), into a vector kept from one group to the next;
// before, the two were joined, sorted and filtered into a new vector, O((|a| + |b|) log).
fn merge_into(a: &[usize], b: &[usize], keep: impl Fn(usize) -> bool, out: &mut Vec<usize>) {
    out.clear();
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        let r = match (a.get(i), b.get(j)) {
            (Some(&p), Some(&q)) => p.min(q),
            (Some(&p), None) => p,
            (None, Some(&q)) => q,
            (None, None) => break,
        };
        i += usize::from(a.get(i) == Some(&r));
        j += usize::from(b.get(j) == Some(&r));
        if keep(r) {
            out.push(r);
        }
    }
}

/// The allowance, in units per unit of the formula's size, of the method's run before the solver
/// starts; it is run so where its bound is at most this times [`RATE`] units per unit of size.
// Complexity tradeoff: measured in round 1, with words alone (the module note). A run first
// costs the method's instructions per unit, c_m, times at most FIRST units per unit of size.
// Measured c_m: 6.7 on `overlap_rows` at k = 1024 (112M
// instructions for 16.6M units), 8.2 at k = 512, 16 on `mid2` at k = 192 (10.8M for 676K),
// with its fixed cost (the formula read, plan and bound) above that on small runs. At 4096
// and c_m = 16 a run first costs at most about 65K instructions per unit of size, about the
// least the solver alone was measured to spend per unit of size (54K on `wide` decided at
// k = 4, 64K at k = 32; 186K or more on every family the method applies to). The families'
// bounds are at most 483 per unit of size (`overlap_rows` projected at k = 64), so each runs
// first, as do all 5,334 races of the 3,000 random2 formulas; `overlap_rows` reaches 1,548 per
// unit at k = 256 and 3,092 at k = 512, where at FIRST 1024 it waited for the solver and cost
// 145.8M and 535M decided, against 11.7M and 34.0M first. Measured on the families and
// random2 at FIRST 256 to 65536: the families cost 608M to 799M at 256 and 550M to 551M from
// 1024, random2 1,230M to 1,519M at 256, 1,137M to 1,151M at 1024 and 1,131M from 4096; with
// this bound random2 costs 1,143.1M at 1024 (rate 256) and 1,133.8M at 4096 (rate 2048), the
// families 551.5M and 551.3M. The case it makes costly: a formula of the class that the solver
// answers in far less than 54K instructions per unit of size (its bounds alone settle it) and
// whose bound is near 4096 per unit; none was found. `overlap_rows` passes 4096 per unit near
// k = 680, from where in round 1 the race below decided it (341M instructions at k = 1,024).
// Round 2, with intervals: a run costs far less than its bound, so the run first is kept up
// to FIRST · RATE per unit, with FIRST per unit as its allowance; a run that stops there costs
// at most what a run first cost before, and the race follows. `overlap_rows` at k = 1,024 now
// answers in it (25.3M), and random2 costs 1,114.6M (1,226.0M on main). On `wide` the floor
// of the bound ([`Rows::floor`]) is past FIRST · RATE, so the plan is not built: 683.1K
// decided at k = 4 (690.3K on main).
const FIRST: u64 = 4096;

/// The method runs once the solver has been charged its bound over this number.
// Complexity tradeoff: measured in round 1, with words alone, and kept in round 2. The race
// of Levin (Problems of Information Transmission 9(3), 1973) with one run of the method, at
// the charge where its whole run costs about what the solver has spent: rate = c_s / c_m, for
// the solver's instructions per unit charged c_s. Measured c_s, as the instructions spent
// before the method ran over the units charged: 22.5K on
// `overlap_rows` decided at k = 1024 (229M for 10,187 units) and on subset sum with no point
// at k = 512, 26K to 48K on `overlap_rows` at k = 256 and 34K on subset sum at k = 256 (rates
// 256 and 1024; the charge comes in steps, so it overshoots). With c_m from 6.7 to 16 (above),
// c_s / c_m is 1.4K to 3.4K, and 2048 lies between. Where the method answers after the
// solver started, the race costs 1 + (c_s / (rate · c_m)) · (bound / units) times the method
// alone: 3.05 on `overlap_rows` decided at k = 1024 (341M against 112M; bound / units = 1.26),
// 2.0 predicted at rate 4096. Where the solver would answer just after the method starts, it
// costs up to 1 + rate · c_m / c_s times the solver alone: 2.5 at c_m = 16 and c_s = 22.5K,
// the case this rate makes costly; no measured case is of this kind. Measured at rates 64 to
// 1024: from FIRST 4096 the rate changes neither the families nor random2 (1,130.9M at every
// rate); at FIRST 1024 random2 costs 1,151.1M at 64 and 1,136.7M at 1024. Past FIRST the rate
// shows (FIRST 1024): `overlap_rows` projected at k = 512 costs 12,952M at 256, 236M at 1024,
// 144M at 2048 and 112M at 4096.
const RATE: u64 = 2048;

/// A method run beside the solver: what the solver has been charged, the charge at which the
/// method next runs, the method, and whether it has answered. The method answers whether it
/// has answered, or the charge at which it runs again.
struct Race {
    charged: u64,
    next: u64,
    bound: u64,
    run: Box<dyn FnMut(u64) -> Result<bool, u64>>,
    done: bool,
}

thread_local! {
    /// The races under way on this thread, innermost last.
    static RACES: RefCell<Vec<Race>> = const { RefCell::new(Vec::new()) };
    /// Test control: the solver alone, with no method run in alternation with it, for the
    /// tests that compare the two (PRES-overlap-fast). Kept here and re-exported by the parent,
    /// which does not read it, so that this file names nothing of the parent's own.
    pub static ROW_SUMS_OFF: Cell<bool> = const { Cell::new(false) };
    /// The units charged on this thread so far, whether or not a race was under way, and the
    /// races started on it so far ([`charged`]).
    static CHARGED: Cell<(u64, u64)> = const { Cell::new((0, 0)) };
}

/// The units charged on this thread so far and the races started on it so far, both counted
/// from the thread's start: a caller that reads them before and after a solve knows what the
/// solve charged and whether a race started inside it (`solve_repair` in the parent).
pub(super) fn charged() -> (u64, u64) {
    CHARGED.with(Cell::get)
}

/// Test control: counts a race started, as [`race`] does, for the test of the parent's memo of
/// repairs, which needs a solve inside which a race starts.
#[cfg(test)]
pub(super) fn count_race_started() {
    CHARGED.with(|c| {
        let (u, r) = c.get();
        c.set((u, r.wrapping_add(1)));
    });
}

/// Charges the innermost race under way `units` of the solver's work: the terms of a system
/// the solver is asked, or of a row its elimination makes. The race's method runs when the
/// charge reaches the method's bound over [`RATE`], or, built when first needed ([`planned`]),
/// a floor of the bound over the rate, and then the charge it names.
// Complexity tradeoff: O(1) where no race has answered; the method's own runs are paid for by
// the charge, as the module note says. The charge counts only rows, which the solver makes at
// a cost of at least their terms, so it is below the solver's work: measured on
// `overlap_rows` at k = 16, the solver spends about 90K instructions per term of the systems
// it is asked, which alone left the method too little to answer.
pub(super) fn charge(units: u64) {
    CHARGED.with(|c| {
        let (u, r) = c.get();
        c.set((u.wrapping_add(units), r));
    });
    let answered = RACES.with(|races| {
        let mut races = races.borrow_mut();
        let Some(r) = races.last_mut() else {
            return false;
        };
        if r.done {
            return false;
        }
        r.charged = r.charged.saturating_add(units);
        while !r.done && r.charged >= r.next {
            r.next = u64::MAX;
            match (r.run)(r.bound) {
                Ok(done) => r.done = done,
                Err(at) => r.next = at,
            }
        }
        r.done
    });
    // The solver is left at once, by an unwind that the race stops, where the build unwinds;
    // otherwise each system asked after this one is refused (`stopped`), and the solver's
    // own work between the systems it asks is still done. Measured on the random2 formulas:
    // refusing each system alone left up to 143 systems asked after the answer, the run 6.5
    // times main's.
    #[cfg(panic = "unwind")]
    if answered {
        std::panic::resume_unwind(Box::new(Stop));
    }
    #[cfg(not(panic = "unwind"))]
    let _ = answered;
}

/// The payload of the unwind that leaves the solver once the innermost race's method has
/// answered.
struct Stop;

/// Whether the solver stops at the system it is asked: some race under way has been answered
/// by its method. O(d) for d races nested on the thread, the depth of nested public questions.
pub(super) fn stopped() -> bool {
    RACES.with(|races| races.borrow().iter().any(|r| r.done))
}

/// Takes the innermost race off the thread when dropped, also when the solver panics.
struct Off;

impl Drop for Off {
    fn drop(&mut self) {
        RACES.with(|races| races.borrow_mut().pop());
    }
}

/// The answer of `new` (the method, given an allowance) or of `old` (the solver), whichever
/// finishes first, as the module note describes; `bound` is the most `new` spends, `u64::MAX`
/// where it cannot be told, or at most that where `new` answers `Err(at)`: it runs again once
/// the solver has been charged `at` ([`planned`]).
fn race<T: 'static>(
    size: u64,
    bound: u64,
    mut new: impl FnMut(u64) -> Result<Option<T>, u64> + 'static,
    old: impl FnOnce() -> Result<T, Refusal>,
) -> Result<T, Refusal> {
    let first = size.saturating_mul(FIRST);
    if bound <= first.saturating_mul(RATE)
        && let Ok(Some(t)) = new(bound.min(first))
    {
        return Ok(t);
    }
    let found: Rc<RefCell<Option<T>>> = Rc::default();
    let slot = Rc::clone(&found);
    let run = Box::new(move |allowance| {
        let t = new(allowance)?;
        let done = t.is_some();
        *slot.borrow_mut() = t;
        Ok(done)
    });
    CHARGED.with(|c| {
        let (u, r) = c.get();
        c.set((u, r.wrapping_add(1)));
    });
    RACES.with(|races| {
        races.borrow_mut().push(Race {
            charged: 0,
            next: if bound <= first || bound == u64::MAX {
                u64::MAX
            } else {
                bound.div_ceil(RATE)
            },
            bound,
            run,
            done: false,
        })
    });
    let off = Off;
    // Only the innermost race is charged, and a race nested in the solver stops its own
    // unwind, so a `Stop` that reaches here is this race's.
    #[cfg(panic = "unwind")]
    let answer = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(old)) {
        Ok(answer) => answer,
        Err(stop) if stop.is::<Stop>() => Err(Refusal::Growth),
        Err(panic) => std::panic::resume_unwind(panic),
    };
    #[cfg(not(panic = "unwind"))]
    let answer = old();
    drop(off);
    match found.borrow_mut().take() {
        Some(t) => Ok(t),
        None => answer,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A stand-in method that answers 1 when its allowance is at least `cost`, and counts its
    /// runs in `runs`.
    fn method(
        cost: u64,
        runs: &Rc<Cell<u32>>,
    ) -> impl FnMut(u64) -> Result<Option<u32>, u64> + 'static {
        let runs = Rc::clone(runs);
        move |allowance| {
            runs.set(runs.get() + 1);
            Ok((allowance >= cost).then_some(1))
        }
    }

    /// A stand-in solver that charges `units` one at a time and then answers 2.
    fn solver(units: u64) -> impl FnOnce() -> Result<u32, Refusal> {
        move || {
            for _ in 0..units {
                charge(1);
            }
            Ok(2)
        }
    }

    /// Each branch of [`race`] at size 1, where the first allowance is `FIRST` and the run
    /// first is tried for a bound of at most `FIRST · RATE`.
    #[test]
    fn each_branch_of_the_race() {
        let runs = Rc::new(Cell::new(0));
        let ask = |bound, cost, units| {
            runs.set(0);
            let answer = race(1, bound, method(cost, &runs), solver(units));
            (answer, runs.get())
        };
        // The run first answers; the solver never starts.
        assert_eq!(ask(FIRST, FIRST, u64::MAX), (Ok(1), 1));
        // The run first stops at its allowance; the bound is within it, so the method does not
        // run again and the solver answers.
        assert_eq!(ask(FIRST, FIRST + 1, 10 * FIRST), (Ok(2), 1));
        // The run first stops at its allowance; the method runs again, with its whole bound,
        // once the solver's charge reaches the bound over the rate, and answers.
        let bound = 4 * FIRST;
        assert_eq!(ask(bound, bound, bound / RATE + 5), (Ok(1), 2));
        // The same, where the solver answers before its charge reaches the bound over the rate.
        assert_eq!(ask(bound, bound, bound / RATE - 1), (Ok(2), 1));
        // The bound is past the run first: the method runs only beside the solver.
        let bound = 4 * FIRST * RATE;
        assert_eq!(ask(bound, bound, bound / RATE + 5), (Ok(1), 1));
        assert_eq!(ask(bound, bound, bound / RATE - 1), (Ok(2), 0));
        // A bound that cannot be told: the method never runs.
        assert_eq!(ask(u64::MAX, 0, 1000), (Ok(2), 0));
        // A method built when first run ([`planned`]): it names the charge at which it runs
        // with its bound, and runs there; where the solver answers before, it never runs.
        let lazy = |at: u64, units: u64| {
            runs.set(0);
            let mut named = false;
            let r = Rc::clone(&runs);
            let new = move |_| {
                r.set(r.get() + 1);
                match std::mem::replace(&mut named, true) {
                    false => Err(at),
                    true => Ok(Some(1)),
                }
            };
            (race(1, 4 * FIRST * RATE, new, solver(units)), runs.get())
        };
        let at = 8 * FIRST;
        assert_eq!(lazy(at, at + 5), (Ok(1), 2));
        assert_eq!(lazy(at, at - 1), (Ok(2), 1));
        // A charge already past the one named: the method runs at once.
        assert_eq!(lazy(1, 4 * FIRST + 5), (Ok(1), 2));
        // No race is left on the thread.
        assert!(RACES.with(|r| r.borrow().is_empty()));
    }

    /// [`Rows::floor`] is at most [`Plan::bound`] of each pass: on `wide` (each atom from 0 to
    /// 1e9 or from 2e9 to 3e9, their sum 1e9 + 7), where it is past what the method may run
    /// first, and on rows with negative and non-unit coefficients, atoms on two rows, narrow
    /// ranges, and a row no sum meets.
    #[test]
    fn floor_within_the_bound() {
        let rows = |domains: Vec<Vec<(i128, i128)>>, rows: Vec<(Vec<(usize, i128)>, i128)>| Rows {
            atoms: (0..domains.len())
                .map(|i| Atom::Sym(format!("y{i}").into()))
                .collect(),
            domains,
            rows: (rows.into_iter())
                .map(|(terms, k)| Row { terms, k, eq: true })
                .collect(),
            empty: false,
            size: 16,
        };
        let wide = vec![(0, 1_000_000_000), (2_000_000_000, 3_000_000_000)];
        let two = vec![(0, 0), (5, 5)];
        let cases = [
            rows(
                vec![wide.clone(); 4],
                vec![((0..4).map(|j| (j, 1)).collect(), -1_000_000_007)],
            ),
            rows(
                vec![wide.clone(); 3],
                vec![(vec![(0, 3), (1, -6), (2, 9)], -7)],
            ),
            rows(
                vec![wide.clone(), vec![(0, 70), (100, 300)], two.clone(), two],
                vec![
                    (vec![(0, 1), (1, 1), (2, 1)], -50),
                    (vec![(2, 2), (3, -1)], 0),
                ],
            ),
            rows(vec![vec![(0, 3)]; 2], vec![(vec![(0, 1), (1, 1)], -3)]),
            // No sum meets the row, so the tables after the first are empty: only the first
            // atom of a group is charged as the floor charges it.
            rows(
                vec![vec![(0, 1)], wide.clone(), wide.clone(), wide.clone()],
                vec![((0..4).map(|j| (j, 1)).collect(), 5)],
            ),
        ];
        for (i, rows) in cases.iter().enumerate() {
            let floor = rows.floor();
            let all = vec![true; rows.atoms.len()];
            for (want, pass) in [
                (&[][..], Pass::Decide),
                (&[][..], Pass::Point),
                (&all[..], Pass::Project(&all)),
            ] {
                let plan = Plan::of(rows, want).expect("a plan");
                let bound = plan.bound(rows, pass);
                assert!(
                    floor <= bound,
                    "case {i}: floor {floor} past the bound {bound}"
                );
            }
        }
        // On `wide` the floor alone shows the method cannot run first.
        assert!(cases[0].floor() > 16 * FIRST * RATE);
        // Ranges whose widths pass `i128` and `u64`: the floor is read before the plan, which
        // refuses them, so it saturates instead of overflowing.
        let huge = rows(
            vec![vec![(i128::MIN + 1, 0), (1, i128::MAX)]],
            vec![(vec![(0, 1)], 0)],
        );
        assert_eq!(huge.floor(), u64::MAX);
        assert!(Plan::of(&huge, &[]).is_none());
    }

    /// One step of [`Plan::project`] value by value, as its walk does it: the sums of `before`
    /// kept, and the values that work.
    fn by_values(
        before: &[i64],
        good: &[i64],
        ranges: &[(i128, i64, i64)],
        delta: i64,
    ) -> (Vec<i64>, Vec<i128>) {
        let (mut kept, mut values) = (std::collections::BTreeSet::new(), Vec::new());
        for &(v0, off, n) in ranges {
            for e in 0..n {
                let d = off + if e == 0 { 0 } else { e * delta };
                let hit: Vec<i64> = before
                    .iter()
                    .copied()
                    .filter(|b| good.contains(&(b + d)))
                    .collect();
                if !hit.is_empty() {
                    values.push(v0 + i128::from(e));
                    kept.extend(hit);
                }
            }
        }
        (kept.into_iter().collect(), values)
    }

    /// The sums kept and the values that work.
    type Kept = (Vec<i64>, Vec<i128>);

    /// [`Plan::by_intervals`] on the sets of `before` and `good`: its answer, as the sums kept
    /// and the values that work, and the units it spent.
    fn by_intervals(
        before: &[i64],
        good: &[i64],
        ranges: &[(i128, i64, i64)],
        delta: i64,
    ) -> (Option<Kept>, u64) {
        let (b, g) = (Set::of(&mut before.to_vec()), Set::of(&mut good.to_vec()));
        let mut work = Work::new(u64::MAX);
        let answer = Plan::by_intervals(&b, &g, ranges.iter().copied(), delta, &mut work)
            .expect("within the allowance");
        let answer = answer.map(|(kept, pieces)| {
            (
                kept.keys().collect(),
                pieces.iter().flat_map(|&(l, h)| l..=h).collect(),
            )
        });
        (answer, u64::MAX - work.left)
    }

    /// Each branch of [`Plan::by_intervals`]: the answers it gives are those of the walk value
    /// by value, and each decline is told apart by the units spent before it.
    #[test]
    fn each_branch_of_the_step_by_intervals() {
        let span = |lo: i64, hi: i64| (lo..=hi).collect::<Vec<i64>>();
        let every_other = |n: i64| (0..n).map(|i| 2 * i).collect::<Vec<i64>>();
        let answered = |before: &[i64], good: &[i64], ranges: &[(i128, i64, i64)], delta: i64| {
            let (got, _) = by_intervals(before, good, ranges, delta);
            assert_eq!(
                got,
                Some(by_values(before, good, ranges, delta)),
                "{ranges:?} by {delta}"
            );
        };
        // Answered from intervals: key changes rising and falling, two ranges, a gap in `good`,
        // a value of one key change alone where the others move by 2.
        let gapped: Vec<i64> = span(50, 60).into_iter().chain(span(90, 95)).collect();
        answered(&span(0, 100), &span(50, 60), &[(0, 0, 200)], 1);
        answered(&span(0, 100), &gapped, &[(0, 150, 200)], -1);
        answered(&span(10, 40), &gapped, &[(-5, 0, 30), (40, 70, 20)], 1);
        let single: Vec<(i128, i64, i64)> =
            (0..20).map(|i| (3 * i128::from(i), 50 * i, 1)).collect();
        answered(&span(0, 1000), &span(500, 520), &single, 2);
        // A range of several values whose key moves by 2 per value: declined at once.
        assert_eq!(
            by_intervals(&span(0, 9), &span(0, 9), &[(0, 0, 10)], 2),
            (None, 2)
        );
        // No sum before or no sum marked: nothing works and nothing is kept.
        assert_eq!(
            by_intervals(&[], &span(0, 9), &[(0, 0, 10)], 1),
            (Some((vec![], vec![])), 2)
        );
        assert_eq!(
            by_intervals(&span(0, 9), &[], &[(0, 0, 10)], 1),
            (Some((vec![], vec![])), 2)
        );
        // One value: the least cost from intervals is above the walk's, so neither set is read.
        assert_eq!(by_intervals(&[1], &[4], &[(0, 3, 1)], 1), (None, 2));
        // 128 intervals in each set, more than the walk's 80 units: declined after reading 81
        // of them, the walk's units charged.
        assert_eq!(
            by_intervals(&every_other(128), &every_other(128), &[(0, 0, 8)], 1),
            (None, 2 + 9 + 80)
        );
        // 10 intervals in each set, read, but 100 pairs cost more than the walk's 32 units.
        assert_eq!(
            by_intervals(&every_other(10), &every_other(10), &[(0, 0, 8)], 1),
            (None, 2 + 3 + 20)
        );
    }
}
