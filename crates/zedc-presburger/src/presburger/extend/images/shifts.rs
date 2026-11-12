//! Images of chains of shifts on residue intervals: steps `if h mod m < s { h + a } else {
//! h + b }`, with any comparison and nesting, whose every branch moves h by a constant
//! (LOAD-max-div-unsolved, I49). Each such step commutes with h + m, so the image of a link
//! is the integers whose residue mod m lies in a set of intervals of Z_m.

use std::ops::Bound;
use std::sync::Arc;

use imbl::{OrdMap, Vector};

use super::super::super::formula::{Atom, Formula, Lin, Rel};
use super::{Image, ScalarImages, choice, lone_atom};
use zedc_int::int::Int;

/// Disjoint intervals [lo, hi) of Z_m by lo, none touching another.
pub(super) type Intervals = OrdMap<Int, Int>;

/// A step on Z_m whose every branch is h + C: residue r in piece i, `[starts[i], starts[i + 1])`
/// (the last up to m), goes to `r + offs[i]` mod m. Adjacent pieces have unequal offsets, so
/// two equal maps have one form.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct Shift {
    m: Arc<Int>,
    starts: Vec<Int>,
    offs: Vec<Int>,
}

impl Shift {
    fn constant(m: &Arc<Int>, c: &Int) -> Self {
        Shift {
            m: Arc::clone(m),
            starts: vec![Int::ZERO],
            offs: vec![c.mod_floor(m)],
        }
    }

    fn end(&self, i: usize) -> &Int {
        self.starts.get(i + 1).unwrap_or(&self.m)
    }

    /// The index of the piece holding residue r, 0 <= r < m.
    fn piece(&self, r: &Int) -> usize {
        self.starts.partition_point(|s| s <= r) - 1
    }

    /// Pushes the pieces of this map over [from, to) on `out`, merging equal offsets.
    fn push_range(&self, from: &Int, to: &Int, out: &mut Vec<(Int, Int)>) {
        if from >= to {
            return;
        }
        let mut i = self.piece(from);
        while i < self.starts.len() && self.starts[i] < *to {
            let start = (&self.starts[i]).max(from);
            if out.last().is_none_or(|(_, off)| *off != self.offs[i]) {
                out.push((start.clone(), self.offs[i].clone()));
            }
            i += 1;
        }
    }

    /// This map on [lo, hi) and `other` elsewhere, 0 <= lo < hi <= m.
    fn within(&self, lo: &Int, hi: &Int, other: &Shift) -> Shift {
        let mut out = Vec::with_capacity(self.starts.len() + other.starts.len());
        other.push_range(&Int::ZERO, lo, &mut out);
        self.push_range(lo, hi, &mut out);
        other.push_range(hi, &self.m, &mut out);
        let (starts, offs) = out.into_iter().unzip();
        Shift {
            m: Arc::clone(&self.m),
            starts,
            offs,
        }
    }

    /// This map followed by h + c.
    fn then_add(&self, c: &Int) -> Shift {
        Shift {
            m: Arc::clone(&self.m),
            starts: self.starts.clone(),
            offs: self
                .offs
                .iter()
                .map(|o| (o + c).mod_floor(&self.m))
                .collect(),
        }
    }

    /// Pushes the image of [lo, hi), 0 <= lo < hi <= m, on `out`, unsorted.
    fn map_interval(&self, lo: &Int, hi: &Int, out: &mut Vec<(Int, Int)>) {
        let mut i = self.piece(lo);
        while i < self.starts.len() && self.starts[i] < *hi {
            let a = (&self.starts[i]).max(lo);
            let b = self.end(i).min(hi);
            moved(a, b, &self.offs[i], &self.m, out);
            i += 1;
        }
    }

    /// The image of sorted disjoint intervals, normalized: O(k log k + pieces touched).
    fn map<'a>(&self, ivs: impl Iterator<Item = (&'a Int, &'a Int)>) -> Vec<(Int, Int)> {
        let mut out = Vec::new();
        for (lo, hi) in ivs {
            self.map_interval(lo, hi, &mut out);
        }
        normalize(out)
    }

    /// The image of `set` inside the windows `w`, normalized. A point y of a window is in
    /// it iff some piece holds y - off with y - off in `set`, so each window is read back
    /// through each piece: O(|w| p (log |set| + k)) for p pieces and k intervals read.
    fn image_in(&self, set: &Intervals, w: &[(Int, Int)]) -> Vec<(Int, Int)> {
        let m = &*self.m;
        let mut out = Vec::new();
        let mut back = Vec::new();
        for (wlo, whi) in w {
            for (i, off) in self.offs.iter().enumerate() {
                back.clear();
                moved(wlo, whi, &(m - off), m, &mut back);
                for (a, b) in &back {
                    let a = a.max(&self.starts[i]);
                    let b = b.min(self.end(i));
                    for (x, y) in window(set, a, b) {
                        moved(&x, &y, off, m, &mut out);
                    }
                }
            }
        }
        normalize(out)
    }
}

/// Pushes [lo + off, hi + off) mod m, 0 <= lo < hi <= m and 0 <= off < m, as one or two
/// intervals.
fn moved(lo: &Int, hi: &Int, off: &Int, m: &Int, out: &mut Vec<(Int, Int)>) {
    if lo >= hi {
        return;
    }
    let (a, b) = (lo + off, hi + off);
    if b <= *m {
        out.push((a, b));
    } else if a >= *m {
        out.push((&a - m, &b - m));
    } else {
        out.push((a, m.clone()));
        out.push((Int::ZERO, &b - m));
    }
}

/// Sorted, disjoint and untouching.
fn normalize(mut ivs: Vec<(Int, Int)>) -> Vec<(Int, Int)> {
    ivs.sort_unstable();
    let mut out: Vec<(Int, Int)> = Vec::with_capacity(ivs.len());
    for (lo, hi) in ivs {
        match out.last_mut() {
            Some(last) if lo <= last.1 => {
                if hi > last.1 {
                    last.1 = hi;
                }
            }
            _ => out.push((lo, hi)),
        }
    }
    out
}

/// The intervals of `set` meeting [a, b), clipped to it: O(log |set| + k).
fn window<'a>(set: &'a Intervals, a: &'a Int, b: &'a Int) -> impl Iterator<Item = (Int, Int)> + 'a {
    let first = set
        .get_prev(a)
        .filter(|(_, hi)| *hi > a)
        .map(|(_, hi)| (a.clone(), hi.min(b).clone()));
    let rest = set
        .range::<_, Int>((Bound::Excluded(a), Bound::Unbounded))
        .take_while(move |(lo, _)| *lo < b)
        .map(move |(lo, hi)| (lo.clone(), hi.min(b).clone()));
    first.into_iter().chain(rest).filter(|(x, y)| x < y)
}

/// a less b, both sorted and disjoint: O(|a| + |b|).
fn minus<'a>(a: impl Iterator<Item = (&'a Int, &'a Int)>, b: &[(Int, Int)]) -> Vec<(Int, Int)> {
    let mut out = Vec::new();
    let mut j = 0;
    for (lo, hi) in a {
        let mut cur = lo.clone();
        while j < b.len() && b[j].1 <= cur {
            j += 1;
        }
        let mut k = j;
        while k < b.len() && b[k].0 < *hi {
            if b[k].0 > cur {
                out.push((cur.clone(), b[k].0.clone()));
            }
            cur = cur.max(b[k].1.clone());
            k += 1;
        }
        if cur < *hi {
            out.push((cur, hi.clone()));
        }
    }
    out
}

fn listed(set: &Intervals) -> Vec<(Int, Int)> {
    set.iter().map(|(x, y)| (x.clone(), y.clone())).collect()
}

fn pairs(v: &[(Int, Int)]) -> impl Iterator<Item = (&Int, &Int)> {
    v.iter().map(|(a, b)| (a, b))
}

/// Removes [lo, hi) from `set`: O(log |set|) per interval it meets.
fn remove(set: &mut Intervals, lo: &Int, hi: &Int) {
    let met: Vec<(Int, Int)> = set
        .get_prev(lo)
        .filter(|(_, y)| *y > lo)
        .into_iter()
        .chain(
            set.range::<_, Int>((Bound::Excluded(lo), Bound::Unbounded))
                .take_while(|(x, _)| *x < hi),
        )
        .map(|(x, y)| (x.clone(), y.clone()))
        .collect();
    for (x, y) in met {
        set.remove(&x);
        if x < *lo {
            set.insert(x, lo.clone());
        }
        if y > *hi {
            set.insert(hi.clone(), y);
        }
    }
}

/// Adds [lo, hi) to `set`, merging the intervals it meets or touches: O(log |set|) each.
fn add(set: &mut Intervals, lo: &Int, hi: &Int) {
    let (mut a, mut b) = (lo.clone(), hi.clone());
    if let Some((x, y)) = set.get_prev(lo)
        && *y >= *lo
    {
        a = x.clone();
        b = b.max(y.clone());
    }
    let met: Vec<(Int, Int)> = set
        .range::<_, Int>((Bound::Included(&a), Bound::Included(hi)))
        .map(|(x, y)| (x.clone(), y.clone()))
        .collect();
    for (x, y) in met {
        set.remove(&x);
        b = b.max(y);
    }
    set.insert(a, b);
}

/// Intervals in order, shared.
type Listed = Arc<[(Int, Int)]>;

/// The image of a link of a chain of shifts, with what the difference rule needs: the steps
/// of its segment (the links since the period last changed), their prefix function and the
/// images of their inputs, and the difference from the image L links back.
pub(super) struct Run {
    m: Arc<Int>,
    pub(super) image: Intervals,
    steps: Vector<u32>,
    prefix: Vector<usize>,
    inputs: Vector<Intervals>,
    /// (L, image less the image L links back, that image less this one).
    diff: Option<(usize, Listed, Listed)>,
}

impl Run {
    fn whole(m: &Arc<Int>) -> Run {
        Run {
            m: Arc::clone(m),
            image: OrdMap::unit(Int::ZERO, (**m).clone()),
            steps: Vector::new(),
            prefix: Vector::new(),
            inputs: Vector::new(),
            diff: None,
        }
    }

    // Complexity tradeoff: the graph path splits each link on its residues, exponent 2.1
    // in the depth at M = 10^9 + 7 (I49); translating every interval of the image at every
    // step is O(|I|) a step, quadratic when the image gains intervals at each step. Here,
    // once the steps repeat with period L (found online by the prefix function of the
    // segment's step identities, amortized O(1) a step), step j equals step j - L, so the
    // image I_{j+1} differs from I_{j+1-L} only by
    //   A_{j+1} = g(A_j) \ g(I_{j-L})  and  D_{j+1} = g(D_j) \ g(I_j),
    // with A_j = I_j \ I_{j-L} and D_j = I_{j-L} \ I_j: a point of g(I_j) outside g(I_{j-L})
    // comes from A_j, and a point of g(I_{j-L}) outside g(I_j) from D_j. Each is read only in
    // the windows g(A_j) and g(D_j), and I_{j+1} is I_{j+1-L} edited there, the persistent
    // map sharing all else: O(p (|A| + |D|) log |I|) a step for p pieces. Not proved: that
    // |A| + |D| stays small; measured on the families of LOAD-max-div-unsolved (R <= 8.7 at
    // 256 → 2048 links). Given up: a step that breaks the period starts a new segment, whose
    // first L steps and steps of a chain with no period translate every interval (O(|I|)).
    /// The run after one more step, `id` naming its map.
    fn step(&self, id: u32, shift: &Shift) -> Run {
        let j = self.steps.len();
        let mut p = 0;
        if j > 0 {
            p = self.prefix[j - 1];
            let period = j - p;
            while p > 0 && self.steps[p] != id {
                p = self.prefix[p - 1];
            }
            if self.steps[p] == id {
                p += 1;
            }
            if self.prefix[j - 1] > 0 && j + 1 - p != period {
                let fresh = Run {
                    m: Arc::clone(&self.m),
                    image: self.image.clone(),
                    steps: Vector::new(),
                    prefix: Vector::new(),
                    inputs: Vector::new(),
                    diff: None,
                };
                return fresh.step(id, shift);
            }
        }
        let period = j + 1 - p;
        let (image, diff) = if j >= period {
            let old = &self.inputs[j - period];
            let (a, d) = match &self.diff {
                Some((l, a, d)) if *l == period => (Arc::clone(a), Arc::clone(d)),
                _ => (
                    minus(self.image.iter(), &listed(old)).into(),
                    minus(old.iter(), &listed(&self.image)).into(),
                ),
            };
            let ga = shift.map(pairs(&a));
            let gd = shift.map(pairs(&d));
            let a = minus(pairs(&ga), &shift.image_in(old, &ga));
            let d = minus(pairs(&gd), &shift.image_in(&self.image, &gd));
            let mut image = if period == 1 {
                self.image.clone()
            } else {
                self.inputs[j + 1 - period].clone()
            };
            for (lo, hi) in &d {
                remove(&mut image, lo, hi);
            }
            for (lo, hi) in &a {
                add(&mut image, lo, hi);
            }
            (image, Some((period, a.into(), d.into())))
        } else {
            (shift.map(self.image.iter()).into_iter().collect(), None)
        };
        let mut next = Run {
            m: Arc::clone(&self.m),
            image,
            steps: self.steps.clone(),
            prefix: self.prefix.clone(),
            inputs: self.inputs.clone(),
            diff,
        };
        next.steps.push_back(id);
        next.prefix.push_back(p);
        next.inputs.push_back(self.image.clone());
        next
    }
}

impl ScalarImages {
    /// The residues [lo, hi) of 0..m on which a guard on h mod m holds: (h, m, lo, hi).
    fn residue_range(
        &self,
        guard: &Formula,
        def: &dyn Fn(u32) -> Formula,
    ) -> Option<(Atom, Arc<Int>, Int, Int)> {
        let Formula::Con(c) = guard else { return None };
        if c.lin.terms.len() != 1 {
            return None;
        }
        let (r, kr) = c.lin.terms.first_key_value()?;
        if !kr.is_unit() {
            return None;
        }
        let (false, arg, m) = self.fact(r, def)?.division? else {
            return None;
        };
        if m.is_zero() {
            return None;
        }
        let m = Arc::new(m.abs());
        // kr r + k (== or >=) 0.
        let s = -&(kr * &c.lin.constant);
        let (lo, hi) = match (c.rel, kr.is_positive()) {
            (Rel::Eq, _) => (s.clone(), &s + &Int::ONE),
            (Rel::Ge, true) => (s, (*m).clone()),
            (Rel::Ge, false) => (Int::ZERO, &s + &Int::ONE),
        };
        let lo = lo.max(Int::ZERO);
        let hi = hi.min((*m).clone());
        Some((lone_atom(&arg)?.clone(), m, lo, hi))
    }

    /// The map of a branch value h + C, or q + C with q a shift of h by modulus m.
    fn arm_shift(&self, e: &Lin, h: &Atom, m: &Arc<Int>) -> Option<Shift> {
        let [(a, k)] = e.terms.iter().collect::<Vec<_>>()[..] else {
            return None;
        };
        if *k != Int::ONE {
            return None;
        }
        if a == h {
            return Some(Shift::constant(m, &e.constant));
        }
        let (g, shift, _) = self.shifts.get(a)?;
        (g == h && shift.m == *m).then(|| shift.then_add(&e.constant))
    }

    /// Records the map of a single-output choice whose branches are shifts of its guard's h,
    /// with an identity per distinct map: O(p log p) for p pieces.
    pub(super) fn record_shift(
        &mut self,
        f: &Formula,
        output: &Atom,
        def: &dyn Fn(u32) -> Formula,
    ) {
        let Some((guard, left, right)) = choice(f, output) else {
            return;
        };
        let Some((h, m, lo, hi)) = self.residue_range(&guard, def) else {
            return;
        };
        let (Some(yes), Some(no)) = (
            self.arm_shift(&left, &h, &m),
            self.arm_shift(&right, &h, &m),
        ) else {
            return;
        };
        let shift = if lo < hi {
            yes.within(&lo, &hi, &no)
        } else {
            no
        };
        let next = self.shift_ids.len() as u32;
        let shift = Arc::new(shift);
        let id = *self.shift_ids.entry(Arc::clone(&shift)).or_insert(next);
        self.shifts.insert(output.clone(), (h, shift, id));
    }

    /// The image of a link of a chain of shifts that starts from all integers, computed on
    /// demand and kept for each link on the way, so that the branches of a nested if, which
    /// no question reads, are never stepped. Each link is stepped once, its inputs found by
    /// walking back to a link already known: O(n) walk over the chain in all.
    pub(super) fn shift_image(&mut self, a: &Atom, def: &dyn Fn(u32) -> Formula) -> Option<Image> {
        let mut path = Vec::new();
        let mut at = a.clone();
        let start = loop {
            if let Some(run) = self.runs.get(&at) {
                break run.clone();
            }
            match self.shifts.get(&at) {
                Some((h, _, _)) => {
                    path.push(at.clone());
                    at = h.clone();
                }
                None => {
                    let whole = self
                        .fact(&at, def)
                        .and_then(|f| f.image)
                        .and_then(|i| i.exponent())
                        == Some(0);
                    break path
                        .last()
                        .filter(|_| whole)
                        .map(|first| Arc::new(Run::whole(&self.shifts[first].1.m)));
                }
            }
        };
        let mut run = start;
        for link in path.into_iter().rev() {
            run = run.and_then(|r| {
                let (_, shift, id) = &self.shifts[&link];
                (*shift.m == *r.m).then(|| Arc::new(r.step(*id, shift)))
            });
            self.runs.insert(link, run.clone());
        }
        let run = run?;
        Some(Image::Intervals(Arc::clone(&run.m), run.image.clone()))
    }
}

/// Whether residue r of 0..m is in `set`: O(log |set|).
pub(super) fn holds(set: &Intervals, r: &Int) -> bool {
    set.get_prev(r).is_some_and(|(_, hi)| hi > r)
}
