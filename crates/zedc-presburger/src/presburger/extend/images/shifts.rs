//! Images of chains of shifts on residue intervals: steps `if h mod m < s { h + a } else {
//! h + b }`, with any comparison and nesting, whose every branch moves h by a constant
//! (LOAD-max-div-unsolved, I49). Each such step commutes with h + m, so the image of a link
//! is the integers whose residue mod m lies in a set of intervals of Z_m.

use std::sync::Arc;

use super::super::super::formula::{Atom, Formula, Lin, Rel};
use super::intervals;
use super::{Image, ScalarImages, choice, lone_atom};
use zedc_int::int::Int;

/// Disjoint intervals [lo, hi) of Z_m, none touching another except at the wrap (m and 0).
pub(super) type Intervals = intervals::Tree;

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

    /// The image of `set`: each piece cut out and moved by its offset, the part past m by
    /// its offset less m, and the parts united.
    // Complexity tradeoff: moving every interval is O(|set|) a step, quadratic on a chain
    // whose image gains intervals at each step (main before LOAD-max-div-unsolved: 3.45e10
    // instructions at 40 links, exponent 2.08). Here a part moves in O(1) by its subtree
    // offset, so a step costs O(p log |set|) expected for its p pieces' cuts, plus
    // O(log |set|) for each run of one part's intervals in the union's order and for each
    // interval the union fuses (`intervals::union`). Summed over a chain of n steps, with the
    // potential sum over gaps g between ends of log2 g plus 2 log2 m per end, the runs and
    // fusions number O(n p log m), so the chain costs O(n p log m log n) expected, for any
    // chain, periodic or not (Claude seat, LOAD-max-div-unsolved hybrid round 1; the merge
    // inequality checked on 20000 random merges, not proved in Lean). Measured at n and 8n
    // links (test `the_questions_of_a_chain_of_residue_intervals_scale`; aperiodic, switching
    // and prefixed chains): 8.1 to 8.6 times the instructions. Open: a bound free of log m;
    // a chain interleaving two halves at the finest scale needs about n log2(m / n) runs.
    fn apply(&self, set: &Intervals) -> Intervals {
        let m = &*self.m;
        let mut rest = set.clone();
        let mut out = None;
        for (i, off) in self.offs.iter().enumerate() {
            let (part, after) = intervals::cut(&rest, self.end(i));
            rest = after;
            let (low, high) = intervals::cut(&part, &(m - off));
            out = intervals::union(out, intervals::moved(&low, off));
            out = intervals::union(out, intervals::moved(&high, &(off - m)));
        }
        out
    }
}

/// The image of a link of a chain of shifts.
pub(super) struct Run {
    m: Arc<Int>,
    pub(super) image: Intervals,
}

impl Run {
    fn whole(m: &Arc<Int>) -> Run {
        Run {
            m: Arc::clone(m),
            image: intervals::single(Int::ZERO, (**m).clone()),
        }
    }

    /// The run after one more step.
    fn step(&self, shift: &Shift) -> Run {
        Run {
            m: Arc::clone(&self.m),
            image: shift.apply(&self.image),
        }
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
        let (g, shift) = self.shifts.get(a)?;
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
        self.shifts.insert(output.clone(), (h, Arc::new(shift)));
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
                Some((h, _)) => {
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
                let (_, shift) = &self.shifts[&link];
                (*shift.m == *r.m).then(|| Arc::new(r.step(shift)))
            });
            self.runs.insert(link, run.clone());
        }
        let run = run?;
        Some(Image::Intervals(Arc::clone(&run.m), run.image.clone()))
    }
}

/// Whether residue r of 0..m is in `set`: O(log |set|).
pub(super) fn holds(set: &Intervals, r: &Int) -> bool {
    intervals::holds(set, r)
}
