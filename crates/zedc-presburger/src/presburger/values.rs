//! The values a linear form may take, read from the rows on that form alone, and the removal
//! of each disjunct whose own rows put a form outside them ([`drop_outside_values`]).
//!
//! A row reads a form up to its sign and constant: `y >= 1` and `y <= 3` are both rows on
//! `y`, so a disjunct's rows give each form it bounds one range ([`form_bounds`]). The base
//! allows a form the range its rows give it, and a disjunction whose every disjunct bounds the
//! form allows it the union of their ranges, which may have gaps: `y == 0 || y == 2` allows
//! `y` the values 0 and 2, where the rows that disjunction implies (`0 <= y <= 2`) allow 1
//! too. The values left to a form are those that the base and every such disjunction allow.

use std::collections::{BTreeMap, BTreeSet};

use zedc_int::int::Int;

use super::formula::{Atom, Con, Rel};

/// A linear form, its terms with the first coefficient positive.
pub(super) type Form = Vec<(Atom, Int)>;

/// The least and greatest value of a form, `None` where that side is open.
pub(super) type Bounds = (Option<Int>, Option<Int>);

/// The range of each form that some rows bound: its least and greatest value, `None` where
/// the rows leave that side open. A range whose least value is above its greatest is empty.
pub(super) type FormBounds = BTreeMap<Form, Bounds>;

/// The range that `cons` put on each form they bound, reading each row on its form alone.
/// One pass over the rows.
pub(super) fn form_bounds<'a>(cons: impl IntoIterator<Item = &'a Con>) -> FormBounds {
    let mut out = FormBounds::new();
    for c in cons {
        let Some((_, first)) = c.lin.terms.iter().next() else {
            continue;
        };
        let flip = first.is_negative();
        let terms: Form = (c.lin.terms.iter())
            .map(|(a, k)| (a.clone(), if flip { -k } else { k.clone() }))
            .collect();
        // `form + k >= 0` (or `== 0`) with `k` the constant read with the form's sign.
        let k = if flip {
            -&c.lin.constant
        } else {
            c.lin.constant.clone()
        };
        let (lo, hi) = out.entry(terms).or_insert((None, None));
        let at_least = || -&k;
        if !flip || c.rel == Rel::Eq {
            let v = at_least();
            *lo = Some(lo.take().map_or(v.clone(), |l: Int| l.max(v)));
        }
        if flip || c.rel == Rel::Eq {
            let v = at_least();
            *hi = Some(hi.take().map_or(v.clone(), |h: Int| h.min(v)));
        }
    }
    out
}

/// Removes from `ors` each disjunct whose own rows (`rows`) put a form outside the values left
/// to it, until none is: the values that `base`'s rows on the form and each disjunction whose
/// every disjunct still there bounds the form allow it (see the module's comment). A disjunct
/// removed has no point with the base and the disjunctions, so the formula's points are as they
/// were. `false` when a disjunction is left with no disjunct or the base's rows on one form
/// leave it no value: the formula has no point. On a pipeline whose stage `k` has `y[k]` 0 or
/// 2, `y[k] == 1 || z[k] >= 0` and `z[k] <= 5`, each `y[k] == 1` is removed, so that `z[k]`
/// projects to `[0..=5]`, where the rows the disjunctions imply (`0 <= y[k] <= 2`) keep it
/// and leave `z[k]` no lower bound.
///
/// The result is the greatest set of disjuncts closed under this test, so it does not depend
/// on the order of the disjunctions, their disjuncts or the names of the atoms: removing a
/// disjunct only narrows the values left, so a disjunct removed in one order is removed in any.
/// The values of each form are kept as the segments between the ends of its ranges, each
/// removed once; for each disjunction and form, how many of its disjuncts cover each segment,
/// in a tree that finds the segments a removal leaves uncovered; and for each form, its
/// disjuncts' ranges in a tree by least segment that finds those with no segment left. With
/// `r` ranges in all, the cost is O(r log r), whatever the order of the removals.
// Complexity tradeoff: each form is read alone, so a disjunct empty only by the values of
// several forms at once is kept, as are its points in the projection: with `x` and `y` each 0
// or 2, the disjunct `x + y == 1` of `x + y == 1 || z >= 0` is kept, though `x + y` is 0, 2 or
// 4, and `z` keeps no lower bound. Why: the values of a sum of forms with gaps is a sum of sets,
// up to the product of their sizes, and the test across forms is case reasoning over the
// disjunctions, a search exponential in their number in the worst case (finding a point of a
// conjunction of disjunctions of linear rows is NP-complete). Trigger: a disjunct whose form is
// a sum of forms the disjunctions bound with gaps. Tests:
// `l01_38_presburger::omega::pipeline_stage_hulls_are_exact` (the forms read alone) and
// `l01_38_presburger::omega::a_sum_of_forms_with_gaps_is_not_read`; COMPLEXITY.md row
// PROJECT-hull-credit-lower. A complete answer would project each choice of disjuncts.
pub(super) fn drop_outside_values<D>(
    base: &[Con],
    ors: &mut [Vec<D>],
    rows: fn(&D) -> &[Con],
) -> bool {
    // The disjuncts numbered in order, each with its disjunction and its ranges.
    let mut owner: Vec<usize> = Vec::new();
    let mut ranges: Vec<FormBounds> = Vec::new();
    for (j, ds) in ors.iter().enumerate() {
        for d in ds {
            owner.push(j);
            ranges.push(form_bounds(rows(d)));
        }
    }
    let base_bounds = form_bounds(base);
    if (base_bounds.values()).any(|(l, h)| matches!((l, h), (Some(l), Some(h)) if l > h)) {
        return false;
    }
    // Each form a disjunct bounds, numbered, with the ranges on it; the forms each disjunct
    // bounds; and the ranges of each disjunction on each form, as places in the form's list.
    let mut ids: BTreeMap<&Form, usize> = BTreeMap::new();
    let mut named: Vec<&Form> = Vec::new();
    let mut on: Vec<Vec<(usize, &Bounds)>> = Vec::new();
    let mut forms_of: Vec<Vec<usize>> = vec![Vec::new(); owner.len()];
    let mut members: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
    for (u, bs) in ranges.iter().enumerate() {
        for (form, bounds) in bs {
            let f = *ids.entry(form).or_insert_with(|| {
                on.push(Vec::new());
                named.push(form);
                on.len() - 1
            });
            members.entry((owner[u], f)).or_default().push(on[f].len());
            on[f].push((u, bounds));
            forms_of[u].push(f);
        }
    }
    let mut dead = vec![false; owner.len()];
    let mut stack: Vec<usize> = Vec::new();
    // Each form's segments, the values between the ends of its ranges and of the base's:
    // segment `i` holds the values from `cuts[i - 1]` to `cuts[i] - 1`, the first and the last
    // open on their outer side. Those outside the base's range are taken out at once.
    let mut values: Vec<Values> = Vec::with_capacity(on.len());
    for (f, &form) in named.iter().enumerate() {
        let own = base_bounds.get(form);
        let (blo, bhi) = own.map_or((None, None), |(l, h)| (l.as_ref(), h.as_ref()));
        let mut cuts: Vec<Int> = Vec::new();
        let mut cut = |lo: Option<&Int>, hi: Option<&Int>| {
            cuts.extend(lo.cloned());
            cuts.extend(hi.map(|h| h + &Int::ONE));
        };
        cut(blo, bhi);
        for &(_, (lo, hi)) in &on[f] {
            cut(lo.as_ref(), hi.as_ref());
        }
        cuts.sort_unstable();
        cuts.dedup();
        let at = |v: &Int| cuts.binary_search(v).expect("an end of a range is a cut");
        // The first and last segment of a range; the first past the last when it is empty.
        let span = |lo: Option<&Int>, hi: Option<&Int>| -> (usize, usize) {
            let first = lo.map_or(0, |l| at(l) + 1);
            let last = hi.map_or(cuts.len(), |h| at(&(h + &Int::ONE)));
            (first, last)
        };
        let spans: Vec<(usize, usize)> = (on[f].iter())
            .map(|&(_, (lo, hi))| span(lo.as_ref(), hi.as_ref()))
            .collect();
        let (bf, bl) = span(blo, bhi);
        let whose: Vec<usize> = on[f].iter().map(|&(u, _)| u).collect();
        let mut v = Values::new(cuts.len() + 1, spans, &whose);
        // A range with no segment is empty: its disjunct is out.
        for (k, &(a, b)) in v.spans.iter().enumerate() {
            if a > b {
                kill(whose[k], &mut dead, &mut stack);
            }
        }
        if bf > 0 {
            v.take_out(0, bf - 1, &mut dead, &mut stack);
        }
        if bl + 1 < v.segments() {
            v.take_out(bl + 1, v.segments() - 1, &mut dead, &mut stack);
        }
        values.push(v);
    }
    // A disjunction constrains a form once every disjunct of it still there bounds the form:
    // the form then takes only the values in the union of their ranges, and each that a
    // removal leaves uncovered is taken out ([`Cover`]). For each disjunction, `left` counts
    // its disjuncts still there and `waiting` holds, by how many of them bound it, each form
    // they bound that it does not constrain yet; removing one that does not bound a form
    // leaves the count, so the form constrains when its count reaches `left`.
    let mut left: Vec<usize> = ors.iter().map(Vec::len).collect();
    let mut bounding: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    let mut waiting: BTreeMap<(usize, usize), BTreeSet<usize>> = BTreeMap::new();
    let mut covers: Vec<Cover> = Vec::new();
    // For each disjunct, the covers it takes part in: the form, the cover, and its first and
    // last pieces there.
    let mut in_cover: Vec<Vec<(usize, usize, usize, usize)>> = vec![Vec::new(); owner.len()];
    let mut ready: Vec<(usize, usize)> = Vec::new();
    for (&(j, f), ks) in &members {
        if ks.len() == left[j] {
            ready.push((j, f));
        } else {
            bounding.insert((j, f), ks.len());
            waiting.entry((j, ks.len())).or_default().insert(f);
        }
    }
    let mut zeros: Vec<usize> = Vec::new();
    loop {
        for (j, f) in ready.drain(..) {
            let v = &mut values[f];
            let ks: Vec<usize> = (members[&(j, f)].iter().copied())
                .filter(|&k| !dead[on[f][k].0] && v.spans[k].0 <= v.spans[k].1)
                .collect();
            // The union of the ranges as runs of segments; the segments between them go.
            let mut runs: Vec<(usize, usize)> = ks.iter().map(|&k| v.spans[k]).collect();
            runs.sort_unstable();
            let mut from = 0;
            for (a, b) in runs {
                if a > from {
                    v.take_out(from, a - 1, &mut dead, &mut stack);
                }
                from = from.max(b + 1);
            }
            if from < v.segments() {
                v.take_out(from, v.segments() - 1, &mut dead, &mut stack);
            }
            // How many of the ranges cover each piece between their ends.
            let mut ends: Vec<usize> = (ks.iter())
                .flat_map(|&k| [v.spans[k].0, v.spans[k].1 + 1])
                .collect();
            ends.sort_unstable();
            ends.dedup();
            let mut diff = vec![0i64; ends.len()];
            let id = covers.len();
            for &k in &ks {
                let (a, b) = v.spans[k];
                let (pa, pb) = (piece(&ends, a), piece(&ends, b + 1));
                diff[pa] += 1;
                diff[pb] -= 1;
                in_cover[on[f][k].0].push((f, id, pa, pb));
            }
            let mut counts = Vec::with_capacity(ends.len().saturating_sub(1));
            let mut c = 0i64;
            for d in diff.iter().take(ends.len().saturating_sub(1)) {
                c += d;
                counts.push(c);
            }
            covers.push(Cover::new(ends, &counts));
        }
        // Each disjunct taken out may leave pieces of its disjunction's covers uncovered,
        // which their forms then no longer take, each range with no segment left takes its
        // disjunct out in turn, and its disjunction may come to constrain more forms.
        let Some(u) = stack.pop() else {
            break;
        };
        let j = owner[u];
        left[j] -= 1;
        if left[j] == 0 {
            return false;
        }
        for &(f, id, pa, pb) in &in_cover[u] {
            zeros.clear();
            covers[id].remove(pa, pb, &mut zeros);
            for &z in &zeros {
                let (a, b) = (covers[id].ends[z], covers[id].ends[z + 1] - 1);
                values[f].take_out(a, b, &mut dead, &mut stack);
            }
        }
        for &f in &forms_of[u] {
            if let Some(c) = bounding.get_mut(&(j, f)) {
                if let Some(w) = waiting.get_mut(&(j, *c)) {
                    w.remove(&f);
                }
                *c -= 1;
                waiting.entry((j, *c)).or_default().insert(f);
            }
        }
        if let Some(fs) = waiting.remove(&(j, left[j])) {
            for f in fs {
                bounding.remove(&(j, f));
                ready.push((j, f));
            }
        }
    }
    let mut u = 0;
    for ds in ors.iter_mut() {
        ds.retain(|_| {
            u += 1;
            !dead[u - 1]
        });
    }
    true
}

/// Marks disjunct `u` taken out, once.
fn kill(u: usize, dead: &mut [bool], stack: &mut Vec<usize>) {
    if !dead[u] {
        dead[u] = true;
        stack.push(u);
    }
}

/// The place of the end `e` in `ends`, which holds it.
fn piece(ends: &[usize], e: usize) -> usize {
    ends.binary_search(&e)
        .expect("an end of a range is an end of its cover")
}

/// The segments of one form's values still left, and the disjuncts' ranges on it.
struct Values {
    /// For each segment, a link toward the first segment left at or after it; the last entry,
    /// one past the segments, is never removed.
    next: Vec<usize>,
    /// The same toward the last segment left at or before it, over the segments counted from
    /// the end.
    prev: Vec<usize>,
    /// The first and last segment of each range on the form, in the order of the form's list.
    spans: Vec<(usize, usize)>,
    /// The first segment of each range, in order of first segments.
    firsts: Vec<usize>,
    /// The last segment of each range in that order, `usize::MAX` once taken out.
    lasts: MinTree,
    /// The disjunct of each range in that order.
    whose: Vec<usize>,
}

impl Values {
    /// `segments` segments, all left, and the ranges `spans` of the disjuncts `whose`, in the
    /// order of the form's list; an empty range is held as taken out.
    fn new(segments: usize, spans: Vec<(usize, usize)>, whose: &[usize]) -> Values {
        let mut order: Vec<usize> = (0..spans.len()).collect();
        order.sort_unstable_by_key(|&k| spans[k].0);
        let firsts = order.iter().map(|&k| spans[k].0).collect();
        let lasts: Vec<usize> = (order.iter())
            .map(|&k| match spans[k] {
                (a, b) if a > b => usize::MAX,
                (_, b) => b,
            })
            .collect();
        Values {
            next: (0..=segments).collect(),
            prev: (0..=segments).collect(),
            whose: order.iter().map(|&k| whose[k]).collect(),
            spans,
            firsts,
            lasts: MinTree::new(&lasts),
        }
    }

    fn segments(&self) -> usize {
        self.next.len() - 1
    }

    /// The root of `i` in `links`, halving the path to it.
    fn find(links: &mut [usize], mut i: usize) -> usize {
        while links[i] != i {
            links[i] = links[links[i]];
            i = links[i];
        }
        i
    }

    /// The first segment left at or after `i`, or one past the last segment.
    fn next(&mut self, i: usize) -> usize {
        Values::find(&mut self.next, i)
    }

    /// The last segment left before `i`, `None` when there is none.
    fn before(&mut self, i: usize) -> Option<usize> {
        let n = self.segments();
        // Segment `s` is entry `n - 1 - s`, so the one before `i` is at or after `n - i`.
        let r = Values::find(&mut self.prev, n - i);
        (r < n).then(|| n - 1 - r)
    }

    /// Removes segment `s`, which is left.
    fn remove(&mut self, s: usize) {
        let n = self.segments();
        self.next[s] = s + 1;
        self.prev[n - 1 - s] = n - s;
    }

    /// Removes the segments `a..=b` still left, and takes out each disjunct whose range then
    /// has no segment left: those inside the run of removed segments around them.
    fn take_out(&mut self, a: usize, b: usize, dead: &mut [bool], stack: &mut Vec<usize>) {
        let mut s = self.next(a);
        if s > b {
            return;
        }
        while s <= b {
            self.remove(s);
            s = self.next(s + 1);
        }
        let lo = self.before(a).map_or(0, |p| p + 1);
        let hi = self.next(b) - 1;
        let from = self.firsts.partition_point(|&x| x < lo);
        let to = self.firsts.partition_point(|&x| x <= hi);
        while let Some((last, k)) = self.lasts.least(from, to)
            && last <= hi
        {
            self.lasts.set(k, usize::MAX);
            kill(self.whose[k], dead, stack);
        }
    }
}

/// A tree over a list of numbers that finds the least in a range of places and its place.
struct MinTree {
    /// The leaves start at `size`; each node holds the least of its leaves and its place.
    nodes: Vec<(usize, usize)>,
    size: usize,
}

impl MinTree {
    fn new(xs: &[usize]) -> MinTree {
        let size = xs.len().next_power_of_two();
        let mut nodes = vec![(usize::MAX, usize::MAX); 2 * size];
        for (k, &x) in xs.iter().enumerate() {
            nodes[size + k] = (x, k);
        }
        for i in (1..size).rev() {
            nodes[i] = nodes[2 * i].min(nodes[2 * i + 1]);
        }
        MinTree { nodes, size }
    }

    fn set(&mut self, k: usize, x: usize) {
        let mut i = self.size + k;
        self.nodes[i] = (x, k);
        while i > 1 {
            i /= 2;
            self.nodes[i] = self.nodes[2 * i].min(self.nodes[2 * i + 1]);
        }
    }

    /// The least number at places `from..to` and its place, `None` when the range is empty.
    fn least(&self, from: usize, to: usize) -> Option<(usize, usize)> {
        let (mut l, mut r) = (from + self.size, to + self.size);
        let mut best: Option<(usize, usize)> = None;
        while l < r {
            if l % 2 == 1 {
                best = Some(best.map_or(self.nodes[l], |b| b.min(self.nodes[l])));
                l += 1;
            }
            if r % 2 == 1 {
                r -= 1;
                best = Some(best.map_or(self.nodes[r], |b| b.min(self.nodes[r])));
            }
            l /= 2;
            r /= 2;
        }
        best
    }
}

/// For one disjunction and form, the pieces between the ends of its disjuncts' ranges (in
/// segments of the form), each with how many of its disjuncts left cover it.
struct Cover {
    /// The ends: piece `i` holds the segments `ends[i]..ends[i + 1]`.
    ends: Vec<usize>,
    /// The least count below each node, the leaves from 1 + the number of pieces rounded up.
    least: Vec<i64>,
    /// The count to add to every piece below each node, not yet added below it.
    add: Vec<i64>,
    size: usize,
}

impl Cover {
    fn new(ends: Vec<usize>, counts: &[i64]) -> Cover {
        let size = counts.len().max(1).next_power_of_two();
        let mut least = vec![i64::MAX; 2 * size];
        least[size..size + counts.len()].copy_from_slice(counts);
        for i in (1..size).rev() {
            least[i] = least[2 * i].min(least[2 * i + 1]);
        }
        Cover {
            ends,
            least,
            add: vec![0; 2 * size],
            size,
        }
    }

    /// Lowers the count of pieces `from..to` by one, a disjunct covering them having been
    /// taken out, and gives each that no disjunct covers now: none of them was uncovered
    /// before, since the disjunct covered it.
    fn remove(&mut self, from: usize, to: usize, out: &mut Vec<usize>) {
        // An explicit stack of (node, its first piece, one past its last), depth log2 of the
        // pieces.
        let mut stack = vec![(1usize, 0usize, self.size)];
        let mut path: Vec<usize> = Vec::new();
        while let Some((i, l, r)) = stack.pop() {
            if r <= from || to <= l {
                continue;
            }
            if from <= l && r <= to {
                self.least[i] -= 1;
                self.add[i] -= 1;
                self.zeros(i, l, r, out);
                continue;
            }
            self.push(i);
            path.push(i);
            let m = (l + r) / 2;
            stack.push((2 * i + 1, m, r));
            stack.push((2 * i, l, m));
        }
        // The nodes split above, deepest first, take the least of their children.
        while let Some(i) = path.pop() {
            self.least[i] = self.least[2 * i].min(self.least[2 * i + 1]);
        }
    }

    /// Adds the count held at node `i` to its children.
    fn push(&mut self, i: usize) {
        let a = std::mem::take(&mut self.add[i]);
        if a != 0 {
            for c in [2 * i, 2 * i + 1] {
                self.least[c] = self.least[c].saturating_add(a);
                self.add[c] += a;
            }
        }
    }

    /// The pieces below node `i`, holding pieces `l..r`, with count 0.
    fn zeros(&mut self, i: usize, l: usize, r: usize, out: &mut Vec<usize>) {
        let mut stack = vec![(i, l, r)];
        while let Some((i, l, r)) = stack.pop() {
            if self.least[i] != 0 {
                continue;
            }
            if r - l == 1 {
                out.push(l);
                continue;
            }
            self.push(i);
            let m = (l + r) / 2;
            stack.push((2 * i + 1, m, r));
            stack.push((2 * i, l, m));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::formula::Lin;
    use super::*;
    use crate::scaling;

    fn atom(name: &str) -> Lin {
        Lin::atom(Atom::Sym(name.into()))
    }

    /// The disjunct `l == v`.
    fn is(l: &Lin, v: i128) -> Vec<Con> {
        vec![Con::eq(l, &Lin::constant(v))]
    }

    /// The rows of each disjunct left, written out.
    fn kept(ors: &[Vec<Vec<Con>>]) -> Vec<Vec<String>> {
        let row = |d: &Vec<Con>| d.iter().map(|c| format!("{c:?}")).collect::<String>();
        ors.iter().map(|ds| ds.iter().map(row).collect()).collect()
    }

    /// `x0` in {0, 2} and at each stage `k` below `n`, `x[k] == 1 || x[k + 1] == 0 ||
    /// x[k + 1] == 2`: each `x[k] == 1` goes once `x[k]` is 0 or 2, and only then does the
    /// stage's disjunction bound `x[k + 1]`, so the removals run along the chain, one at a time.
    fn chain(n: usize) -> Vec<Vec<Vec<Con>>> {
        let x = |k: usize| atom(&format!("x{k:05}"));
        let mut ors = vec![vec![is(&x(0), 0), is(&x(0), 2)]];
        for k in 0..n {
            ors.push(vec![is(&x(k), 1), is(&x(k + 1), 0), is(&x(k + 1), 2)]);
        }
        ors
    }

    /// `x` in {0, 2, .., 2m - 2} and for each `i` below `m`, `x == 2i + 1 || z[i] == 0`: each
    /// `x == 2i + 1` falls in a gap of `x`'s values, which are `m` values on one form.
    fn wide(m: i128) -> Vec<Vec<Vec<Con>>> {
        let x = atom("x");
        let mut ors = vec![(0..m).map(|i| is(&x, 2 * i)).collect()];
        for i in 0..m {
            ors.push(vec![is(&x, 2 * i + 1), is(&atom(&format!("z{i:05}")), 0)]);
        }
        ors
    }

    #[test]
    fn removals_run_along_a_chain_in_any_order() {
        let n = 64;
        let mut expected = chain(n);
        for ds in expected.iter_mut().skip(1) {
            ds.remove(0);
        }
        let mut expected = kept(&expected);
        expected.sort();
        let mut s = 0x9e37_79b9_7f4a_7c15_u64;
        for order in 0..4 {
            let mut ors = chain(n);
            match order {
                0 => {}
                1 => ors.reverse(),
                2 => ors.iter_mut().for_each(|ds| ds.reverse()),
                _ => {
                    for i in (1..ors.len()).rev() {
                        s ^= s << 13;
                        s ^= s >> 7;
                        s ^= s << 17;
                        ors.swap(i, (s % (i as u64 + 1)) as usize);
                    }
                }
            }
            assert!(
                drop_outside_values(&[], &mut ors, Vec::as_slice),
                "order {order}"
            );
            let mut got = kept(&ors);
            got.iter_mut().for_each(|ds| ds.sort());
            got.sort();
            let mut want = expected.clone();
            want.iter_mut().for_each(|ds| ds.sort());
            want.sort();
            assert_eq!(got, want, "order {order}");
        }
    }

    #[test]
    fn values_in_the_gaps_of_one_form_are_removed() {
        let mut ors = wide(50);
        assert!(drop_outside_values(&[], &mut ors, Vec::as_slice));
        assert_eq!(ors[0].len(), 50);
        assert!(ors[1..].iter().all(|ds| ds.len() == 1));
        // With the base's rows `3 <= x <= 7`, `x` is 4 or 6: the other values of the first
        // disjunction go, and `x == 5`, inside the base's range, goes as a gap between them.
        let x = atom("x");
        let base = [
            Con::ge(&x, &Lin::constant(3)),
            Con::ge(&Lin::constant(7), &x),
        ];
        let mut ors = wide(50);
        assert!(drop_outside_values(&base, &mut ors, Vec::as_slice));
        assert_eq!(ors[0].len(), 2, "x is 4 or 6");
        assert!(ors[1..].iter().all(|ds| ds.len() == 1));
    }

    #[test]
    fn no_value_left_is_no_point() {
        let x = atom("x");
        let mut ors = vec![vec![is(&x, 0), is(&x, 2)], vec![is(&x, 1), is(&x, 3)]];
        assert!(!drop_outside_values(&[], &mut ors, Vec::as_slice));
        let base = [
            Con::ge(&x, &Lin::constant(3)),
            Con::ge(&Lin::constant(1), &x),
        ];
        let mut ors = vec![vec![is(&atom("y"), 0), is(&atom("y"), 2)]];
        assert!(!drop_outside_values(&base, &mut ors, Vec::as_slice));
        // A disjunct that bounds a form no other row bounds is kept.
        let mut ors = vec![vec![is(&x, 1), is(&atom("y"), 2)]];
        assert!(drop_outside_values(&[], &mut ors, Vec::as_slice));
        assert_eq!(ors[0].len(), 2);
    }

    /// Both families at `n` and `8n`: O(r log r) in the `r` ranges, a removal at a time along
    /// the chain and many gaps on one form.
    #[test]
    fn removals_scale() {
        scaling::check_order("removals by the values of each form", 1000, 1, |n| {
            let mut ors = chain(n);
            assert!(drop_outside_values(&[], &mut ors, Vec::as_slice));
            let mut ors = wide(i128::try_from(n).expect("a size fits"));
            assert!(drop_outside_values(&[], &mut ors, Vec::as_slice));
        });
    }
}
