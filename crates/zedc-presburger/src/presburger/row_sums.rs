//! The exact answer of rows over atoms each confined to a finite union of ranges, found by
//! joining tables of the rows' partial sums, in alternation with the solver
//! (PRES-overlap-fast, question A87).
//!
//! A formula such as `(y[i] == 0 || y[i] == w[i])` for each i, with `y[0] + .. + y[a-1] == t1`
//! and `y[b] + .. + y[k-1] == t2` (b < a), is two subset sums that share the atoms `y[b..a]`.
//! The solver searches its disjunctions greedily and refuses where its choices meet no point,
//! at a cost that grows as k^6 (`overlap_rows`: 5,443M instructions and a refusal at k = 16,
//! 33,783M at k = 32). The overlap gives a faster path: the atoms fall into groups by the rows
//! they appear in (here `{t1}`, `{t1, t2}` and `{t2}`), and the rows are met by joining one
//! table per group, each the set of the group's possible sums on its rows.
//!
//! The method:
//! - each atom's signature is the set of rows it appears in; atoms of one signature form a
//!   group. A group's table is the set of vectors of its sums on its rows over all values of its
//!   atoms, built one atom at a time as the sumset of the table so far and the atom's values
//!   times its coefficients (Bellman's dynamic program for subset sum), kept sorted without
//!   repeats, so equal sums are kept once;
//! - the groups are joined in the order of their signatures (rows numbered as the formula
//!   gives them). The join keeps the set of vectors of the sums on the rows still open, those
//!   with a group before and a group after; a row closes at its last group, where it must
//!   meet its relation. An equation that closes is met by looking up the one sum it needs on
//!   the other side, not by trying every pair (meet in the middle: Horowitz and Sahni); with
//!   the groups in this order `overlap_rows` costs |T1| + |T12| + |T2| lookups, its three
//!   tables, each of at most 2^(k/3) sums and at most k/3 times the largest weight. In
//!   general the join is bucket elimination over the rows (Dechter) with the groups as its
//!   buckets;
//! - a projection is a pass back over the same joins, which marks the vectors of each layer
//!   that some later choice completes, and then, inside each group, the prefix sums and the
//!   values of each atom that a marked vector completes. A point is read off the marks.
//!
//! Every answer is exact: no point, a point, or each atom's set of values over all points.
//! Where it applies the solver's answer is never finer, so no answer becomes coarser.
//!
//! The parity example of A87 (`a1 + a2 + c + d == 4`, `b1 + b2 + c + d == 3`, the `a`s and `b`s
//! over {0, 2}, `c` and `d` over {0, 1}) shows why the sums cannot be decided one at a time:
//! each value of `c` and of `d` is possible in each sum alone. Here `c + d` is the table of the
//! group `{c, d}`, and its join with the other two keeps no vector.
//!
//! Cost. The tables count distinct sums, so they are bounded both by the number of
//! assignments of their atoms (2^g for g two-way atoms) and by the product, over their rows,
//! of the range of the sums (g times the largest weight W for one row): the method is
//! pseudo-polynomial. With binary weights the class holds subset sum, which is NP-complete
//! (Karp), so no method is polynomial in the bits of W unless P = NP, and none is O(n log n)
//! in general. Each pair the join visits is a distinct class of assignments of the atoms
//! before it, so the work is also at most about twice the number of assignments: never above
//! plain enumeration. The ranges are read value by value, so a wide range (`0..1e9`) makes a
//! large table where the solver may answer at once by its bounds.
//!
//! That is why the method runs in alternation with the solver (after Levin's universal
//! search, which runs two methods with doubling allowances, the first to finish answering).
//! Before any table is built, a bound on the method's work is computed from the ranges alone
//! (`Rows::bound`): each table bounded by the number of assignments of its atoms and by the
//! product over its rows of the range of its sums, and the join's pairs from these. A run
//! given the bound as its allowance is never stopped for want of it. Where the bound is at
//! most [`FIRST`] times the formula's size, the method runs first and alone. Otherwise the
//! solver runs, each system it is asked charging its number of terms, and when the charge
//! reaches the bound over [`RATE`] the method runs once, with the bound as its allowance. When
//! it answers, the solver is left at once and its answer dropped; a bound past `u64` never
//! runs. The work units of both sides are counts, so the answer and its cost are the same at
//! every run. The method's run costs at most a constant times the solver's work before it
//! (about 1 on large runs, by the instructions per unit measured, at [`RATE`]). On the 67
//! questions of the families measured, where the method does not answer first, a question
//! costs at most 1.010 times the solver alone: the formula read and its bound computed
//! (`mid2` decided at k = 12: 44K and 25K instructions, against the solver's 11.2M); where the
//! solver refuses and the method answers after it, the answer costs less than the refusal.
//!
//! Doubling, tried first (rerunning the method each time the charge doubles, from an allowance
//! of the formula's size), cost at most 5% more than the solver alone but reran the method from
//! the start at each doubling: `overlap_rows` decided at k = 64 cost 33,600M, and subset sum with
//! no point was refused from k = 14 on, where its tables need 2.4M instructions. With the
//! bound the method runs once, when it can finish: 1,199M and 30.6M.
//!
//! The six rounds of PRES-disj-cost-xr (2026-11-11) tried endpoint reports, a rank table and a
//! queue inside the search, and a binary search over the points of the hull after a refusal;
//! each kept the greedy search and gained a constant factor at most (5.7 at best), and on
//! `overlap_rows` some cost more. Pisinger's balanced subset sum (A87 option B) decides one sum
//! in O(kW) and does not join two; deciding each sum alone cannot decide the parity example.
//! The join of group tables is chosen because its cost is set by the number of distinct sums
//! of each group, which the overlap keeps small: the shared group is joined once with each
//! side by lookups instead of being searched under every choice of the other atoms.
//!
//! Papers. R. Bellman, *Dynamic Programming*, Princeton University Press, 1957. E. Horowitz and
//! S. Sahni, "Computing partitions with applications to the knapsack problem", Journal of the
//! ACM 21(2), 1974. R. Dechter, "Bucket elimination: a unifying framework for reasoning",
//! Artificial Intelligence 113(1-2), 1999. L. A. Levin, "Universal sequential search
//! problems", Problems of Information Transmission 9(3), 1973. R. M. Karp, "Reducibility among
//! combinatorial problems", Complexity of Computer Computations, 1972. D. Pisinger, "Linear
//! time algorithms for knapsack problems with bounded weights", Journal of Algorithms 33(1),
//! 1999.
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

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};

use super::refusal::{Each, Refusal};
use super::formula::{Atom, Conjuncts, Formula, Id, Model, Rel, one_bound};
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
}

/// [`super::decide`] of a formula of the class, in alternation with the solver's `old`.
pub(super) fn decide(
    rows: Rows,
    old: impl FnOnce() -> Result<bool, Refusal>,
) -> Result<bool, Refusal> {
    let (size, bound) = (rows.size, rows.bound(false, false));
    race(
        size,
        bound,
        move |allowance| Some(rows.joined(&mut Budget(allowance))?.is_some()),
        old,
    )
}

/// [`super::satisfiable`] of a formula of the class, in alternation with the solver's `old`.
pub(super) fn point(
    rows: Rows,
    old: impl FnOnce() -> Result<Option<Model>, Refusal>,
) -> Result<Option<Model>, Refusal> {
    let (size, bound) = (rows.size, rows.bound(true, false));
    race(
        size,
        bound,
        move |allowance| rows.point(&mut Budget(allowance)),
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
    let (size, bound) = (rows.size, rows.bound(true, true));
    let syms = syms.to_vec();
    race(
        size,
        bound,
        move |allowance| {
            let sets = rows.project(&syms, &mut Budget(allowance))?;
            Some((sets.into_iter().map(Ok).collect(), Vec::new()))
        },
        old,
    )
}

/// The number of bits of `n`: 1 + the floor of its base-2 logarithm, 0 for 0.
fn bits(n: u64) -> u64 {
    u64::from(u64::BITS - n.leading_zeros())
}

/// The units charged for sorting `n` vectors: `n · (1 + bits(n))`, the comparisons of a merge sort
/// with one unit for each vector moved, which saturates at `u64::MAX`.
fn sorted(n: u64) -> u64 {
    n.saturating_mul(1 + bits(n))
}

/// The units charged for the union of `count` runs of up to `n + 1` vectors each, merged in pairs
/// round by round: `count · (n + 1) · (1 + bits(count))`, which saturates at `u64::MAX`.
fn merging(count: u64, n: u64) -> u64 {
    (count.saturating_mul(n.saturating_add(1))).saturating_mul(1 + bits(count))
}

/// The greatest common divisor of `a` and `b` (Euclid), `a` where `b` is 0.
fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The work the method may still do, in units of one vector made, visited or compared: a sort or
/// a merge of `n` vectors is charged its `log n` comparisons for each ([`sorted`], [`merging`]),
/// and a lookup in a table of `n` its `1 + bits(n)`.
struct Budget(u64);

impl Budget {
    fn spend(&mut self, units: u64) -> Option<()> {
        self.0 = self.0.checked_sub(units)?;
        Some(())
    }
}

/// Vectors of `w` numbers, sorted and without repeats.
struct Table {
    w: usize,
    n: usize,
    data: Vec<i128>,
}

impl Table {
    /// The one vector of `w` zeros.
    fn zero(w: usize) -> Table {
        Table {
            w,
            n: 1,
            data: vec![0; w],
        }
    }

    /// The `n` vectors of `data`, sorted and each kept once.
    // Complexity tradeoff: a sort of the indices, O(n log n) comparisons of w numbers, and one
    // copy. Naive version: a hash set of vectors, O(n) expected, with one allocation per
    // vector; used: the sort, whose order also serves the lookups by binary search.
    fn of(w: usize, n: usize, data: Vec<i128>) -> Table {
        if w == 0 {
            return Table {
                w,
                n: n.min(1),
                data,
            };
        }
        let row = |i: usize| &data[i * w..(i + 1) * w];
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_unstable_by(|&a, &b| row(a).cmp(row(b)));
        order.dedup_by(|a, b| row(*a) == row(*b));
        let mut sorted = Vec::with_capacity(order.len() * w);
        for &i in &order {
            sorted.extend_from_slice(row(i));
        }
        Table {
            w,
            n: order.len(),
            data: sorted,
        }
    }

    /// The union of `runs`, each a list of vectors of `w` numbers sorted and without repeats.
    // Complexity tradeoff: the runs are merged in pairs, round by round: O(N log m)
    // comparisons for N vectors in m runs, and O(N) for the two runs of an atom of two
    // values. Naive version: all N vectors sorted together (`Table::of`), O(N log N); used:
    // the merge.
    fn union(w: usize, mut runs: Vec<Vec<i128>>) -> Table {
        if w == 0 {
            let n = usize::from(!runs.is_empty());
            return Table {
                w,
                n,
                data: Vec::new(),
            };
        }
        while runs.len() > 1 {
            let mut next = Vec::with_capacity(runs.len().div_ceil(2));
            let mut it = runs.into_iter();
            while let Some(a) = it.next() {
                next.push(match it.next() {
                    Some(b) => merge_two(w, &a, &b),
                    None => a,
                });
            }
            runs = next;
        }
        let data = runs.pop().unwrap_or_default();
        Table {
            w,
            n: data.len() / w,
            data,
        }
    }

    fn row(&self, i: usize) -> &[i128] {
        &self.data[i * self.w..(i + 1) * self.w]
    }

    /// The index of `v`, by binary search.
    fn find(&self, v: &[i128]) -> Option<usize> {
        if self.w == 0 {
            return (self.n > 0).then_some(0);
        }
        let (mut lo, mut hi) = (0, self.n);
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            match self.row(mid).cmp(v) {
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
                std::cmp::Ordering::Equal => return Some(mid),
            }
        }
        None
    }
}

/// The union of two lists of vectors of `w` numbers, each sorted and without repeats, in one
/// pass.
fn merge_two(w: usize, a: &[i128], b: &[i128]) -> Vec<i128> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    if w == 1 {
        // One row: the vectors are numbers, compared as numbers, not as slices.
        while i < a.len() && j < b.len() {
            let (x, y) = (a[i], b[j]);
            out.push(x.min(y));
            i += usize::from(x <= y);
            j += usize::from(y <= x);
        }
        out.extend_from_slice(&a[i..]);
        out.extend_from_slice(&b[j..]);
        return out;
    }
    while i < a.len() && j < b.len() {
        let (x, y) = (&a[i..i + w], &b[j..j + w]);
        match x.cmp(y) {
            std::cmp::Ordering::Less => {
                out.extend_from_slice(x);
                i += w;
            }
            std::cmp::Ordering::Greater => {
                out.extend_from_slice(y);
                j += w;
            }
            std::cmp::Ordering::Equal => {
                out.extend_from_slice(x);
                i += w;
                j += w;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// The atoms of one signature: their rows, in order, and the tables of the sums of the first
/// t atoms on those rows, for t from 0 to all of them.
struct Group {
    sig: Vec<usize>,
    atoms: Vec<usize>,
    prefix: Vec<Table>,
}

/// The forward pass: the groups, with the rows open after each and the layers of the join.
struct Joined {
    groups: Vec<Group>,
    /// `open[i]`: the rows open after the first i groups; `open[0]` is empty.
    open: Vec<Vec<usize>>,
    /// `layers[i]`: the vectors of the sums on `open[i]` the first i groups reach.
    layers: Vec<Table>,
    /// `last[r]`: the index of row r's last group.
    last: Vec<usize>,
}

impl Rows {
    /// Each atom's coefficients on the rows of its signature, and the signature.
    fn signatures(&self) -> Vec<(Vec<usize>, Vec<i128>)> {
        let mut sigs = vec![(Vec::new(), Vec::new()); self.atoms.len()];
        for (r, row) in self.rows.iter().enumerate() {
            for &(j, c) in &row.terms {
                sigs[j].0.push(r);
                sigs[j].1.push(c);
            }
        }
        sigs
    }

    /// The forward pass, or `None` where the allowance runs out or a number leaves `i128`.
    /// Atoms in no row are not in it: each takes any of its values.
    fn forward(&self, budget: &mut Budget) -> Option<Joined> {
        let sigs = self.signatures();
        let mut by_sig: BTreeMap<&[usize], Vec<usize>> = BTreeMap::new();
        for (j, (sig, _)) in sigs.iter().enumerate() {
            if !sig.is_empty() {
                by_sig.entry(sig).or_default().push(j);
            }
        }
        let mut groups = Vec::with_capacity(by_sig.len());
        let mut last = vec![0; self.rows.len()];
        for (i, (sig, atoms)) in by_sig.into_iter().enumerate() {
            for &r in sig {
                last[r] = i;
            }
            let mut prefix = vec![Table::zero(sig.len())];
            for &j in &atoms {
                let next = self.step(prefix.last()?, &sigs[j].1, j, budget)?;
                prefix.push(next);
            }
            groups.push(Group {
                sig: sig.to_vec(),
                atoms,
                prefix,
            });
        }
        let mut open = vec![Vec::new()];
        let mut layers = vec![Table::zero(0)];
        for (i, g) in groups.iter().enumerate() {
            let a = &open[i];
            let out: Vec<usize> = merged(a, &g.sig)
                .into_iter()
                .filter(|&r| last[r] != i)
                .collect();
            let (mut data, mut n) = (Vec::new(), 0);
            self.pairs(
                &layers[i],
                a,
                g.prefix.last()?,
                &g.sig,
                i,
                &last,
                &out,
                budget,
                |_, _, v| {
                    data.extend_from_slice(v);
                    n += 1;
                },
            )?;
            layers.push(Table::of(out.len(), n, data));
            open.push(out);
        }
        Some(Joined {
            groups,
            open,
            layers,
            last,
        })
    }

    /// The table of `t` with atom j added: every vector of `t` plus each value of j times its
    /// coefficients `c`.
    // Complexity tradeoff: |t| times the number of j's values, then a sort; the sort keeps
    // equal sums once, which bounds the table by the range of the sums as well as by the
    // number of assignments. Naive version: one vector per assignment, 2^g for g atoms of two
    // values; used: the sumset, at most min(2^g, (g·W)^s) vectors for s rows.
    fn step(&self, t: &Table, c: &[i128], j: usize, budget: &mut Budget) -> Option<Table> {
        // The whole step is paid for before any of it is done, so a step past the allowance
        // (a wide range) costs one count, not the work up to the allowance.
        budget.spend(merging(self.count(j)?, t.n as u64))?;
        // `t` shifted by one vector stays sorted and without repeats: one run per value.
        let mut runs = Vec::new();
        for &(l, h) in &self.domains[j] {
            let mut v = l;
            loop {
                let shift: Vec<i128> = c
                    .iter()
                    .map(|ci| ci.checked_mul(v))
                    .collect::<Option<_>>()?;
                let mut run = Vec::with_capacity(t.data.len());
                for (x, s) in t.data.iter().zip(shift.iter().cycle()) {
                    run.push(x.checked_add(*s)?);
                }
                runs.push(run);
                if v == h {
                    break;
                }
                v += 1;
            }
        }
        Some(Table::union(c.len(), runs))
    }

    /// Each pair of a vector x of `f` (sums on the rows `a`) and g of `t` (sums of group i on
    /// its rows `sig`) whose totals meet every row closing at group i, given to `visit` with
    /// the indices of x and g and the vector of the totals on the rows `out`.
    // Complexity tradeoff: the vectors of `f` are sorted by their sums on the equations that
    // close here, and each g looks up the one key it needs by binary search: O((|f| + |t|)
    // log |f|) plus the pairs that match. Naive version: every pair, |f|·|t|; used: the
    // lookup (Horowitz and Sahni's meet in the middle), so two tables joined on an equation
    // cost the sum of their sizes, not the product. An inequality that closes is checked on
    // each pair of a key's bucket: each such pair is a distinct class of assignments, so the
    // work stays below enumeration.
    #[allow(clippy::too_many_arguments)]
    fn pairs(
        &self,
        f: &Table,
        a: &[usize],
        t: &Table,
        sig: &[usize],
        i: usize,
        last: &[usize],
        out: &[usize],
        budget: &mut Budget,
        mut visit: impl FnMut(usize, usize, &[i128]),
    ) -> Option<()> {
        let closing = |r: &usize| last[*r] == i;
        // Equations that close here with a sum on both sides: the key.
        let key: Vec<(usize, usize, usize)> = (sig.iter().enumerate())
            .filter(|(_, r)| closing(r) && self.rows[**r].eq)
            .filter_map(|(s, &r)| Some((a.binary_search(&r).ok()?, s, r)))
            .collect();
        // Inequalities that close here with a sum on both sides, checked on each pair.
        let ge: Vec<(usize, usize, usize)> = (sig.iter().enumerate())
            .filter(|(_, r)| closing(r) && !self.rows[**r].eq)
            .filter_map(|(s, &r)| Some((a.binary_search(&r).ok()?, s, r)))
            .collect();
        // Rows that open and close at this group: met by g alone.
        let own: Vec<(usize, usize)> = (sig.iter().enumerate())
            .filter(|(_, r)| closing(r) && a.binary_search(r).is_err())
            .map(|(s, &r)| (s, r))
            .collect();
        let places: Vec<(Option<usize>, Option<usize>)> = out
            .iter()
            .map(|r| (a.binary_search(r).ok(), sig.binary_search(r).ok()))
            .collect();
        let x_key = |x: usize| key.iter().map(move |&(p, _, _)| f.row(x)[p]);
        budget.spend(sorted(f.n as u64))?;
        let mut order: Vec<usize> = (0..f.n).collect();
        order.sort_by(|&x, &y| x_key(x).cmp(x_key(y)));
        let (mut need, mut total) = (vec![0; key.len()], vec![0; out.len()]);
        'g: for gi in 0..t.n {
            budget.spend(1 + bits(f.n as u64))?;
            let g = t.row(gi);
            for &(s, r) in &own {
                let v = g[s].checked_add(self.rows[r].k)?;
                if if self.rows[r].eq { v != 0 } else { v < 0 } {
                    continue 'g;
                }
            }
            for (n, &(_, s, r)) in need.iter_mut().zip(&key) {
                *n = self.rows[r].k.checked_neg()?.checked_sub(g[s])?;
            }
            let from = order.partition_point(|&x| x_key(x).lt(need.iter().copied()));
            for &x in order[from..]
                .iter()
                .take_while(|&&x| x_key(x).eq(need.iter().copied()))
            {
                budget.spend(1 + bits((f.n as u64).saturating_mul(t.n as u64)))?;
                let xs = f.row(x);
                let mut meets = true;
                for &(p, s, r) in &ge {
                    meets &= xs[p].checked_add(g[s])?.checked_add(self.rows[r].k)? >= 0;
                }
                if !meets {
                    continue;
                }
                for (v, &(p, s)) in total.iter_mut().zip(&places) {
                    *v = p.map_or(0, |p| xs[p]).checked_add(s.map_or(0, |s| g[s]))?;
                }
                visit(x, gi, &total);
            }
        }
        Some(())
    }

    /// The forward pass, or `None` where the allowance runs out; `Some(None)` where the rows
    /// have no point.
    fn joined(&self, budget: &mut Budget) -> Option<Option<Joined>> {
        if self.empty {
            return Some(None);
        }
        let j = self.forward(budget)?;
        Some((j.layers.last()?.n > 0).then_some(j))
    }

    /// The pass back: for each layer i, which of its vectors some choice of the groups after
    /// it completes, and for each, the first such choice (the group's vector and the next
    /// layer's); and for each group, which of its sums do.
    // Complexity tradeoff: the same pairs as the forward pass, each with a binary search in
    // the next layer: O(forward · log). Naive version: the forward pass again for each atom
    // projected; used: one pass back for all of them.
    #[allow(clippy::type_complexity)]
    fn back(
        &self,
        j: &Joined,
        budget: &mut Budget,
    ) -> Option<(Vec<Vec<Option<(usize, usize)>>>, Vec<Vec<bool>>)> {
        let p = j.groups.len();
        let mut good = vec![true; j.layers[p].n];
        let mut next = vec![Vec::new(); p];
        let mut sums = vec![Vec::new(); p];
        for i in (0..p).rev() {
            let g = &j.groups[i];
            let (f, t, after) = (&j.layers[i], g.prefix.last()?, &j.layers[i + 1]);
            let mut via = vec![None; f.n];
            let mut good_g = vec![false; t.n];
            self.pairs(
                f,
                &j.open[i],
                t,
                &g.sig,
                i,
                &j.last,
                &j.open[i + 1],
                budget,
                |x, gi, v| {
                    if let Some(o) = after.find(v)
                        && good[o]
                    {
                        via[x].get_or_insert((gi, o));
                        good_g[gi] = true;
                    }
                },
            )?;
            good = via.iter().map(Option::is_some).collect();
            next[i] = via;
            sums[i] = good_g;
        }
        Some((next, sums))
    }

    /// A point of the rows, `Some(None)` where they have none.
    fn point(&self, budget: &mut Budget) -> Option<Option<Model>> {
        let Some(j) = self.joined(budget)? else {
            return Some(None);
        };
        let (next, _) = self.back(&j, budget)?;
        let sigs = self.signatures();
        let mut m = Model::new();
        let mut x = 0;
        for (i, g) in j.groups.iter().enumerate() {
            let (gi, o) = next[i][x]?;
            // The group's sum `gi` is taken apart from its last atom back: some value of the
            // atom leaves a sum of the table before it.
            let mut at = gi;
            for (t, &a) in g.atoms.iter().enumerate().rev() {
                let (before, now) = (&g.prefix[t], &g.prefix[t + 1]);
                let v = self.values(a).find_map(|v| {
                    let rest: Option<Vec<i128>> = (now.row(at).iter().zip(&sigs[a].1))
                        .map(|(s, c)| s.checked_sub(c.checked_mul(v)?))
                        .collect();
                    Some((v, before.find(&rest?)?))
                });
                let (v, p) = v?;
                budget.spend(1)?;
                m.insert(self.atoms[a].clone(), Int::from(v));
                at = p;
            }
            x = o;
        }
        for (a, sig) in sigs.iter().enumerate() {
            if sig.0.is_empty() {
                m.insert(self.atoms[a].clone(), Int::from(self.domains[a][0].0));
            }
        }
        Some(Some(m))
    }

    /// The number of values of atom j; `None` past `u64`.
    fn count(&self, j: usize) -> Option<u64> {
        (self.domains[j].iter()).try_fold(0u64, |n, &(l, h)| {
            n.checked_add(u64::try_from(h.checked_sub(l)?).ok()?.checked_add(1)?)
        })
    }

    /// A bound on the units the method spends: the forward pass, and with `back` the pass back
    /// and then, with `each`, a second pass over every group's atoms (`project`) or one unit
    /// per atom (`point`). It follows the passes step by step, each table bounded by the
    /// number of assignments of its atoms and by the product over its rows of the range of
    /// the sums on that row, so a run given this allowance is never stopped for want of it.
    /// Each step is charged as the run charges it, with the `log n` of its sorts, merges and
    /// lookups ([`Budget`]). Saturates at `u64::MAX`. Measured on the families of COMPLEXITY.md
    /// PRES-overlap-fast and the 3,000 random2 formulas (5,328 runs), the bound is 1.0 to 5.1
    /// times the units spent where `each` is false and up to 15 times where it is true (the
    /// sorts of `project`, bounded by every table's whole size), and no run was stopped.
    // Complexity tradeoff: O(a·s + p·r) for a atoms on at most s rows each and p groups over r
    // rows, no table built. Naive version: run the method to see what it spends; used: the
    // bound, which tells before any run whether the run can finish within what it may spend.
    fn bound(&self, back: bool, each: bool) -> u64 {
        // Rows with an atom of no value, or a false constant row, are answered with no unit
        // spent (`joined`), and every atom below has a value.
        if self.empty {
            return 0;
        }
        let sigs = self.signatures();
        let mut by_sig: BTreeMap<&[usize], Vec<usize>> = BTreeMap::new();
        for (j, (sig, _)) in sigs.iter().enumerate() {
            if !sig.is_empty() {
                by_sig.entry(sig).or_default().push(j);
            }
        }
        let width = |j: usize| {
            let (l, h) = (
                self.domains[j][0].0,
                self.domains[j][self.domains[j].len() - 1].1,
            );
            u64::try_from(h.abs_diff(l)).unwrap_or(u64::MAX)
        };
        let product = |xs: &mut dyn Iterator<Item = u64>| {
            xs.fold(1u64, |p, x| p.saturating_mul(x.saturating_add(1)))
        };
        let (mut steps, mut finds, mut pairs) = (0u64, 0u64, 0u64);
        // Each group's table bound, and the range of its sums on each of its rows.
        let mut groups = Vec::with_capacity(by_sig.len());
        let mut last = vec![0; self.rows.len()];
        for (i, (sig, atoms)) in by_sig.iter().enumerate() {
            for &r in *sig {
                last[r] = i;
            }
            // Rows whose coefficients on the group's atoms are proportional have sums each fixed
            // by another's, on the whole group and on every prefix of its atoms; the table
            // holds one vector per sum of the first row of each class (`first`). Two equal sums
            // over the same atoms count their range once, where the product of both ranges
            // gave `overlap_rows` ten times what the method spends (2026-11-13).
            let mut classes: HashMap<Vec<i128>, usize> = HashMap::new();
            let first: Vec<bool> = (0..sig.len())
                .map(|k| {
                    let coefs: Vec<i128> = atoms.iter().map(|&j| sigs[j].1[k]).collect();
                    let g = coefs.iter().fold(0u128, |g, c| gcd(g, c.unsigned_abs()));
                    let sign = if coefs[0] < 0 { -1 } else { 1 };
                    // A key past `i128` leaves the row a class of its own, which only counts its
                    // range.
                    let key: Option<Vec<i128>> = (coefs.iter())
                        .map(|c| (c / g as i128).checked_mul(sign))
                        .collect();
                    key.is_none_or(|key| *classes.entry(key).or_insert(k) == k)
                })
                .collect();
            let (mut n, mut assignments, mut range) = (1u64, 1u64, vec![0u64; sig.len()]);
            for &j in atoms {
                let count = self.count(j).unwrap_or(u64::MAX);
                steps = steps.saturating_add(merging(count, n));
                finds = finds.saturating_add(sorted(count.saturating_mul(n.saturating_add(1))));
                for (r, c) in range.iter_mut().zip(&sigs[j].1) {
                    let c = u64::try_from(c.unsigned_abs()).unwrap_or(u64::MAX);
                    *r = r.saturating_add(c.saturating_mul(width(j)));
                }
                assignments = assignments.saturating_mul(count);
                let ranges = range.iter().zip(&first).filter(|(_, f)| **f);
                n = assignments.min(product(&mut ranges.map(|(r, _)| *r)));
            }
            groups.push((*sig, n, range));
        }
        // The join, as `forward` makes it: the layer before group i, and the pairs `pairs`
        // visits. The layer is bounded by the number of values of the sum of each open row so
        // far: at most the integers of its range (`sums`), and at most the product of the table
        // bounds of the groups on it (`values`), since each group adds one value per entry of
        // its table. The second is the smaller where few values are spread wide, as two values
        // `{0, w}` per atom on rows of two atoms each, where the range alone gives `(2w + 1)²`
        // for a layer of at most 16.
        let rows = self.rows.len();
        let (mut layer, mut open) = (1u64, Vec::new());
        let (mut sums, mut values) = (vec![0u64; rows], vec![1u64; rows]);
        let spread =
            |r: usize, sums: &[u64], values: &[u64]| sums[r].min(values[r].saturating_sub(1));
        for (i, (sig, t, range)) in groups.iter().enumerate() {
            let key: Vec<usize> = sig
                .iter()
                .filter(|&&r| last[r] == i && self.rows[r].eq && open.contains(&r))
                .copied()
                .collect();
            let unkeyed = product(
                &mut (open.iter())
                    .filter(|r| !key.contains(r))
                    .map(|&r| spread(r, &sums, &values)),
            );
            let matched = t.saturating_mul(layer.min(unkeyed));
            let kept = matched.saturating_mul(1 + bits(layer.saturating_mul(*t)));
            let looked = t.saturating_mul(1 + bits(layer));
            pairs = pairs.saturating_add(sorted(layer).saturating_add(looked).saturating_add(kept));
            for (&r, x) in sig.iter().zip(range) {
                sums[r] = sums[r].saturating_add(*x);
                values[r] = values[r].saturating_mul(*t);
            }
            open = merged(&open, sig)
                .into_iter()
                .filter(|&r| last[r] != i)
                .collect();
            layer = matched.min(product(
                &mut open.iter().map(|&r| spread(r, &sums, &values)),
            ));
        }
        let mut units = steps.saturating_add(pairs);
        if back {
            units = units.saturating_add(pairs);
            units = units.saturating_add(if each { finds } else { self.atoms.len() as u64 });
        }
        units
    }

    /// The values of atom j, in increasing order.
    fn values(&self, j: usize) -> impl Iterator<Item = i128> + '_ {
        self.domains[j].iter().flat_map(|&(l, h)| l..=h)
    }

    /// Each of `syms`'s set of values over the points of the rows.
    fn project(&self, syms: &[Atom], budget: &mut Budget) -> Option<Vec<IntervalSet>> {
        let fin = |v: i128| End::Fin(Num::from(v));
        let Some(j) = self.joined(budget)? else {
            return Some(syms.iter().map(|_| IntervalSet::empty()).collect());
        };
        let wanted: Vec<Option<usize>> = syms
            .iter()
            .map(|a| self.atoms.binary_search(a).ok())
            .collect();
        let (_, sums) = self.back(&j, budget)?;
        let sigs = self.signatures();
        let mut sets: Vec<Option<Vec<(End, End)>>> = vec![None; self.atoms.len()];
        for (a, (sig, _)) in sigs.iter().enumerate() {
            if sig.is_empty() && wanted.contains(&Some(a)) {
                let ranges = self.domains[a].iter().map(|&(l, h)| (fin(l), fin(h)));
                sets[a] = Some(ranges.collect());
            }
        }
        for (i, g) in j.groups.iter().enumerate() {
            if !g.atoms.iter().any(|a| wanted.contains(&Some(*a))) {
                continue;
            }
            // Inside the group, from its last atom back: the prefix sums that some values of
            // the atoms after them complete to a marked sum, and the values that do.
            let mut good = sums[i].clone();
            for (t, &a) in g.atoms.iter().enumerate().rev() {
                let (before, now) = (&g.prefix[t], &g.prefix[t + 1]);
                let mut good_before = vec![false; before.n];
                let mut pieces: Vec<(End, End)> = Vec::new();
                let mut sum = vec![0; before.w];
                // Paid for before it is done, as in `step`.
                budget.spend(sorted(self.count(a)?.checked_mul(before.n as u64 + 1)?))?;
                for v in self.values(a) {
                    let mut taken = false;
                    for (p, kept) in good_before.iter_mut().enumerate() {
                        for ((s, x), c) in sum.iter_mut().zip(before.row(p)).zip(&sigs[a].1) {
                            *s = x.checked_add(c.checked_mul(v)?)?;
                        }
                        if now.find(&sum).is_some_and(|q| good[q]) {
                            *kept = true;
                            taken = true;
                        }
                    }
                    if taken {
                        match pieces.last_mut() {
                            Some((_, End::Fin(h))) if *h == Num::from(v - 1) => *h = Num::from(v),
                            _ => pieces.push((fin(v), fin(v))),
                        }
                    }
                }
                sets[a] = Some(pieces);
                good = good_before;
            }
        }
        Some(
            wanted
                .iter()
                .map(|w| match w.and_then(|a| sets[a].take()) {
                    Some(pieces) => IntervalSet::from_pieces(pieces),
                    None => IntervalSet::range(End::NegInf, End::PosInf),
                })
                .collect(),
        )
    }
}

/// The rows of `a` and of `b`, both sorted, once each and sorted.
fn merged(a: &[usize], b: &[usize]) -> Vec<usize> {
    let mut m: Vec<usize> = a.iter().chain(b).copied().collect();
    m.sort_unstable();
    m.dedup();
    m
}

/// The method runs before the solver starts when its bound is at most this many units per unit
/// of the formula's size.
// Complexity tradeoff: measured at FIRST 256, 512, 1024, 2048, 4096 and 8192 (rate 1024), a
// larger FIRST answers small formulas of the method's class before the solver runs (`mid2`
// decided at k = 3: 1.36 times the solver alone at 256 and 512, 0.75 from 1024; subset sum
// with no point at k = 10: 0.054 at 256, 0.009 from 1024), and the 3,000 random2 formulas
// cost 13,742M at 256, 13,357M at 1024 and 13,347M at 8192 (348,275M for the solver alone).
// A run first costs at most about 46·FIRST instructions per unit of size, against the
// solver's 12K or more per unit charged, so at 1024 at most about 4 times a solver charged
// the formula's size, and at 8192 about 31 times; no measured case was slower at 8192, but no
// family measured has a solver that answers at a charge far below the size. 1024 takes the
// gains measured on `mid2` and subset sum with the smaller worst case.
const FIRST: u64 = 1024;

/// The method runs once the solver has been charged its bound over this number.
// Complexity tradeoff: the solver costs 12K to 28K instructions per unit charged and the
// method 13 to 46 per unit it spends on large runs (100 to 1,000 on runs under 1M
// instructions, its fixed cost), which is below its bound, so at this rate the method's whole
// run costs about 256·46/12K ≈ 1 times what the solver had spent when it started. Measured in
// instructions on the 67 probes of the families of COMPLEXITY.md PRES-overlap-fast at rates
// 128, 192, 256, 320, 384, 512, 768, 1024 and 1536: a higher rate answers sooner (`overlap_rows`
// decided at k = 64: 1,751M at 128, 1,198M at 256, 968M at 384, 479M at 1536, against
// 252,285M refused by the solver alone and 223M for the method alone), and costs more where
// the method runs on a question the solver answers or refuses anyway. At 320 `mid2` decided at
// k = 4 costs 1.52 times the solver's refusal (an answer where it refused), at 384 subset sum
// with no point at k = 24 costs 1.14 times the refusal, and at 768 `mid2` decided at k = 6
// costs 2.02 times the refusal (these three measured before inner races were left to the
// solver). At 256 no question costs more than 1.010 times the solver alone (`mid2` decided at
// k = 6, where reading the formula and its bound shows), and each answer found after a
// refusal costs less than the refusal (subset sum with no point at k = 18: 91.3M against
// 101.1M). Its cost: subset sum with no point is refused, as
// by the solver alone, from k = 20, where the method alone answers in 17.9M; a tighter bound
// would answer it.
const RATE: u64 = 256;

/// A method run beside the solver: what the solver has been charged, the charge at which the
/// method next runs, the method, and whether it has answered.
struct Race {
    charged: u64,
    next: u64,
    bound: u64,
    run: Box<dyn FnMut(u64) -> bool>,
    done: bool,
}

thread_local! {
    /// The races under way on this thread, innermost last.
    static RACES: RefCell<Vec<Race>> = const { RefCell::new(Vec::new()) };
    /// Test control: the solver alone, with no method run in alternation with it, for the
    /// tests that compare the two (PRES-overlap-fast). Kept here and re-exported by the parent,
    /// which does not read it, so that this file names nothing of the parent's own.
    pub static ROW_SUMS_OFF: Cell<bool> = const { Cell::new(false) };
}

/// Charges the innermost race under way `units` of the solver's work: the terms of a system
/// the solver is asked, or of a row its elimination makes. The race's method runs, once, when
/// the charge reaches the method's bound over [`RATE`].
// Complexity tradeoff: O(1) where no race has answered; the method's own runs are paid for by
// the charge, as the module note says. The charge counts only rows, which the solver makes at
// a cost of at least their terms, so it is below the solver's work: measured on
// `overlap_rows` at k = 16, the solver spends about 90K instructions per term of the systems
// it is asked, which alone left the method too little to answer.
pub(super) fn charge(units: u64) {
    let answered = RACES.with(|races| {
        let mut races = races.borrow_mut();
        let Some(r) = races.last_mut() else {
            return false;
        };
        if r.done {
            return false;
        }
        r.charged = r.charged.saturating_add(units);
        if r.charged >= r.next {
            r.next = u64::MAX;
            r.done = (r.run)(r.bound);
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
/// where it cannot be told.
fn race<T: 'static>(
    size: u64,
    bound: u64,
    mut new: impl FnMut(u64) -> Option<T> + 'static,
    old: impl FnOnce() -> Result<T, Refusal>,
) -> Result<T, Refusal> {
    let first = size.saturating_mul(FIRST);
    if bound <= first
        && let Some(t) = new(bound)
    {
        return Ok(t);
    }
    let found: Rc<RefCell<Option<T>>> = Rc::default();
    let slot = Rc::clone(&found);
    let run = Box::new(move |allowance| {
        let t = new(allowance);
        let done = t.is_some();
        *slot.borrow_mut() = t;
        done
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
