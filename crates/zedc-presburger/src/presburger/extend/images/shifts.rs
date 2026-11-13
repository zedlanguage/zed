//! Images of chains of shifts on residue intervals: steps `if h mod m < s { h + a } else {
//! h + b }`, with any comparison and nesting, whose every branch moves h by a constant
//! (LOAD-max-div-unsolved, I49). Each such step commutes with h + m, so the image of a link
//! is the integers whose residue mod m lies in a set of intervals of Z_m.

use std::sync::Arc;

use super::intervals;
use zedc_int::int::Int;

/// Disjoint intervals [lo, hi) of Z_m, none touching another except at the wrap (m and 0).
pub(super) type Intervals = intervals::Tree;

/// A step on Z_m whose every branch is h + C: residue r in piece i, `[starts[i], starts[i + 1])`
/// (the last up to m), goes to `r + offs[i]` mod m. Adjacent pieces have unequal offsets, so
/// two equal maps have one form.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct Shift {
    pub(super) m: Arc<Int>,
    starts: Vec<Int>,
    offs: Vec<Int>,
}

impl Shift {
    pub(super) fn constant(m: &Arc<Int>, c: &Int) -> Self {
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
    pub(super) fn within(&self, lo: &Int, hi: &Int, other: &Shift) -> Shift {
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
    pub(super) fn then_add(&self, c: &Int) -> Shift {
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
    pub(super) m: Arc<Int>,
    pub(super) image: Intervals,
}

impl Run {
    pub(super) fn whole(m: &Arc<Int>) -> Run {
        Run {
            m: Arc::clone(m),
            image: intervals::single(Int::ZERO, (**m).clone()),
        }
    }

    /// The run after one more step.
    pub(super) fn step(&self, shift: &Shift) -> Run {
        Run {
            m: Arc::clone(&self.m),
            image: shift.apply(&self.image),
        }
    }
}

/// Whether residue r of 0..m is in `set`: O(log |set|).
pub(super) fn holds(set: &Intervals, r: &Int) -> bool {
    intervals::holds(set, r)
}
