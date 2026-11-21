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
    // interval the union fuses (`intervals::union`). Summed over a chain of n steps of
    // P = p_1 + .. + p_n pieces in all, the runs and fusions number O(P log m), so the chain
    // costs O(P log m log N) expected, N <= 1 + 2P the most intervals a set can hold, for any
    // chain, periodic or not (Claude seat, LOAD-max-div-unsolved hybrid round 1). Cost only:
    // the bound counts work and no answer reads it.
    //
    // Proof (PROOF-shift-apply-merge-bound), every step. Write φ(g) = log2 g for g >= 1 and
    // φ(0) = 0, and for a set S with lower ends l_1 < .. < l_k (distinct, as the intervals are
    // disjoint and not empty) the potential Φ(S) = Σ φ(l_(i+1) - l_i), so 0 <= Φ(S) <=
    // (k - 1) log2 m. One step, with p pieces:
    // 1. Blocks. The 2p cuts split `set` into t <= 2p nonempty blocks Y_1, .., Y_t (in the
    //    order the loop unites them), each a run of consecutive intervals of `set`, moved by
    //    one constant into [0, m) (`low` by `off`, `high` by `off - m`: the cut at `m - off`
    //    keeps both inside). A cut at c inside an interval [l_a, h) makes c the lower end of
    //    the next block's first interval, so the gap l_(a+1) - l_a becomes l_(a+1) - c, which
    //    is smaller; a cut between intervals drops the gap across it. Moving keeps the gaps
    //    inside a block. So, with Φ_int(Y) the potential of a block alone,
    //    Σ_X Φ_int(Y_X) <= Φ(set).
    // 2. The merged order. Order the lower ends of all blocks by value, ties by block index.
    //    It has R runs (maximal stretches from one block); block X has r_X of them, Σ r_X = R.
    //    Each gap between neighbors in this order is either kept (two neighbors of one block,
    //    neighbors in that block too) or a switch (two blocks), and there are R - 1 switches.
    //    A gap of a block with other ends between its ends is lost; block X has r_X - 1 lost
    //    gaps, R - t in all.
    // 3. One lost gap. Let x < x' be neighbors in X with ends y_1 <= .. <= y_j of other blocks
    //    between, j >= 1. The merged gaps s_f = y_1 - x and s_l = x' - y_j are two different
    //    switches, and L = x' - x >= s_f + s_l, L >= 1. If s_f, s_l >= 1, L >= 2 sqrt(s_f s_l)
    //    (the means), so log2 L >= 1 + (φ(s_f) + φ(s_l)) / 2. If one is 0, L >= the other, so
    //    log2 L >= φ(other) / 2; if both are 0, log2 L >= 0. So in all cases
    //    log2 L >= 1 + (φ(s_f) + φ(s_l)) / 2 - [s_f = 0] - [s_l = 0].
    // 4. Each switch, from u in U to v in V, is the s_f of the lost gap of U that starts at u
    //    (when u is not U's last end) and the s_l of the lost gap of V that ends at v (when v
    //    is not V's first end), and of no other. So in Σ_lost (φ(s_f) + φ(s_l)) each switch
    //    is counted twice, but for at most 2t missing counts (one at each block's first and
    //    last end), each worth at most φ(m) = log2 m; and a switch s = 0 is counted at most
    //    twice. With Z the switches of
    //    length 0, summing step 3 over the R - t lost gaps:
    //    Σ_lost log2 L >= (R - t) + Σ_switch φ(s) - t log2 m - 2Z.
    // 5. The merged potential Φ_M = Σ_kept φ + Σ_switch φ(s) and Σ_X Φ_int(Y_X) = Σ_kept φ +
    //    Σ_lost log2 L, so by steps 1 and 4, Φ_M <= Φ(set) - R + t (1 + log2 m) + 2Z.
    // 6. Fusions. The union's intervals are the blocks' intervals with F fused away, each
    //    union interval taking the least lower end of its group, so the lower ends of the new
    //    set S' are those of step 2 with F removed. Removing an end joins two gaps g1, g2 into
    //    g1 + g2, and φ(g1 + g2) <= φ(g1) + φ(g2) + 1 (equal when one is 0; else
    //    log2(g1 + g2) <= 1 + log2 max(g1, g2)), or drops a gap at an end of the order, so
    //    Φ(S') <= Φ_M + F. Two equal lower ends belong to overlapping intervals, which fuse, so
    //    Z <= F.
    // 7. So R <= Φ(set) - Φ(S') + 2p (1 + log2 m) + 3F.
    // 8. The unions as made. The loop unites `out` with Y_j for j = 1..t. The lower ends of
    //    `out` are a subset of those of Y_1..Y_(j-1) (step 6), so two runs of Y_j in that union's
    //    order have an end of an earlier block between them, which separates them in the order
    //    of step 2 as well: Y_j has at most B_j runs there, B_j its runs in step 2, and `out`
    //    at most B_j + 1. With f_j the union's fusions, the union costs
    //    O((2 B_j + 1 + f_j) log N) (`intervals::union`; its runs read in the order of lower
    //    ends, as its comment states, inferred and not proved here), and Σ_j B_j = R, Σ f_j = F.
    // 9. The chain. A set starts as one interval and gains at most one interval at each cut,
    //    2 p_i cuts in step i, and a fusion removes one, so the fusions of the chain number at
    //    most 1 + 2P and N <= 1 + 2P. Summing step 7 over the chain, Φ telescopes from Φ(whole)
    //    = 0 to Φ(last) >= 0: Σ R <= 2P (1 + log2 m) + 3 (1 + 2P) = O(P log m). The cuts cost
    //    O(log N) expected each and the moves O(1), so with step 8 the chain costs
    //    O((P + Σ R + Σ F) log N) = O(P log m log N) expected.
    // Checked: 20000 random merges before the proof; measured at n and 8n links (test
    // `the_questions_of_a_chain_of_residue_intervals_scale`; aperiodic, switching and
    // prefixed chains): 8.1 to 8.6 times the instructions. The tests cannot see a chain they
    // do not draw; the bound rests on steps 1 to 9. Open: a bound free of log m; a chain
    // interleaving two halves at the finest scale needs about n log2(m / n) runs.
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
