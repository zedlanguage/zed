//! A memory plan in bytes, so an executable carries the plan its code was made from and its
//! start reads it instead of planning again (plan row EXE-plan-carried; DESIGN.md sec:kernel,
//! "Facts carried, and the stripped form": no runtime works a fact out again).
//!
//! The bytes are written as ZIR's binary form writes its numbers ([`super::super::binary`]):
//! every count and index in 8 bytes, little end first. In order: `fuse` as one byte, the
//! number of regions, then each region in the plan's preorder: its link up (one byte, 0 for
//! the root, else 1 and the three numbers `(up, k, i)`), its arguments' modes (a count, then
//! one byte each, 0 owned and 1 borrowed), its entry drops, its nodes and its result dups.
//! A node is its inputs' modes, its dups, its drops and its last uses (each edge a tag byte, 0
//! for argument `i` and 1 for output `p` of node `m`, then the numbers), its callee (one byte,
//! then the index when there is one) and its regions.
//!
//! Reading checks every count and index against the graph the plan is of, so a damaged plan
//! is refused before anything indexes by it: region `at`'s link names an earlier region, a
//! node of it and a region of that node in the graph; each region has a mode for each of its
//! arguments and a plan for each of its nodes; each node a mode for each input; each index
//! names an argument, input, result, node output or region that exists; and each region a node
//! links to links back to that node. What these checks cannot see, a plan that names real
//! edges but the wrong ones, [`Plan::recheck`] finds by planning again.

use super::super::{Region, Src};
use super::{Mode, NodePlan, Plan, RegionPlan, plan};

/// The message of bytes that end where more was expected.
const ENDS: &str = "the data ends, and more was expected";

impl Plan {
    /// The plan as bytes (module comment).
    // Complexity tradeoff: O(size of the plan) time and bytes, 8 bytes for each index, as ZIR's
    // binary form writes its numbers. A variable-length number would make the plan about a
    // third the size for the small indices plans hold, at a branch for each byte read; the
    // executable holds the graph at 8 bytes a number already, and the plan is read once.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![u8::from(self.fuse)];
        let n = |out: &mut Vec<u8>, x: usize| out.extend_from_slice(&(x as u64).to_le_bytes());
        let list = |out: &mut Vec<u8>, xs: &[usize]| {
            n(out, xs.len());
            xs.iter().for_each(|&x| n(out, x));
        };
        let modes = |out: &mut Vec<u8>, ms: &[Mode]| {
            n(out, ms.len());
            out.extend(ms.iter().map(|m| u8::from(*m == Mode::Borrowed)));
        };
        let srcs = |out: &mut Vec<u8>, ss: &[Src]| {
            n(out, ss.len());
            for s in ss {
                match *s {
                    Src::Arg(i) => {
                        out.push(0);
                        n(out, i);
                    }
                    Src::Out(m, p) => {
                        out.push(1);
                        n(out, m);
                        n(out, p);
                    }
                    // The planner makes each drop and last use from an edge number
                    // (`Planner::region`'s `src`), which is an argument or a node's output.
                    Src::Const(_) => unreachable!("a plan drops edges, not constants"),
                }
            }
        };
        n(&mut out, self.regions.len());
        for r in &self.regions {
            match r.up {
                None => out.push(0),
                Some((up, k, i)) => {
                    out.push(1);
                    [up, k, i].into_iter().for_each(|x| n(&mut out, x));
                }
            }
            modes(&mut out, &r.args);
            list(&mut out, &r.entry_drops);
            n(&mut out, r.nodes.len());
            for p in &r.nodes {
                modes(&mut out, &p.modes);
                list(&mut out, &p.dups);
                srcs(&mut out, &p.drops);
                srcs(&mut out, &p.last);
                match p.callee {
                    None => out.push(0),
                    Some(c) => {
                        out.push(1);
                        n(&mut out, c);
                    }
                }
                list(&mut out, &p.regions);
            }
            list(&mut out, &r.result_dups);
        }
        out
    }

    /// The plan of graph `g` that `bytes` hold, as [`Plan::to_bytes`] writes it, every count and
    /// index checked against `g` (module comment); the message names the byte where reading
    /// stopped.
    // Complexity tradeoff: O(b + r) for b bytes and r regions: each byte read once, each check
    // a comparison against a length of `g`, the regions of `g` found by their links up, each
    // from one already found, in O(1). A count is refused when the bytes left cannot hold its
    // items, before any memory is asked for them, so damaged bytes cost no more memory than
    // the bytes themselves. Test: `l01_36a_executables::plan_carried`.
    pub fn from_bytes(bytes: &[u8], g: &Region) -> Result<Plan, String> {
        let mut r = Reader { b: bytes, i: 0 };
        let fuse = match r.byte()? {
            0 => false,
            1 => true,
            t => return r.err(r.i - 1, format!("{t} is not a value of `fuse`")),
        };
        let count = r.count(1)?;
        // The region of `g` each region of the plan is of, by index.
        let mut of: Vec<&Region> = Vec::with_capacity(count);
        let mut regions = Vec::with_capacity(count);
        for at in 0..count {
            let start = r.i;
            let up = match r.byte()? {
                0 if at == 0 => None,
                1 if at > 0 => Some((r.n()?, r.n()?, r.n()?)),
                _ => return r.err(start, "a link up only every region but the first has"),
            };
            let region = match up {
                None => g,
                Some((u, k, i)) => {
                    let found = (u < at)
                        .then(|| of[u].nodes.get(k)?.regions.get(i))
                        .flatten();
                    match found {
                        Some(found) => &**found,
                        None => {
                            let why = format!(
                                "region {at} links up to region {i} of node {k} of region {u}, \
                                 which the graph does not have"
                            );
                            return r.err(start, why);
                        }
                    }
                }
            };
            of.push(region);
            let args = r.modes(region.args.len(), "arguments")?;
            let entry_drops = r.indices(region.args.len(), "an argument")?;
            let start = r.i;
            if r.count(1)? != region.nodes.len() {
                return r.err(start, "a count of nodes other than the region's");
            }
            let mut nodes = Vec::with_capacity(region.nodes.len());
            for (k, node) in region.nodes.iter().enumerate() {
                let modes = r.modes(node.inputs.len(), "inputs")?;
                let dups = r.indices(node.inputs.len(), "an input")?;
                // Node `k` drops its own outputs and edges made before it, and is the last use
                // only of edges made before it (`Reader::srcs`).
                let drops = r.srcs(region, k + 1)?;
                let last = r.srcs(region, k)?;
                let callee = match r.byte()? {
                    0 => None,
                    1 => Some(r.n()?),
                    t => return r.err(r.i - 1, format!("{t} is not a tag of a callee")),
                };
                let regions = r.indices(usize::MAX, "a region")?;
                nodes.push(NodePlan {
                    modes,
                    dups,
                    drops,
                    last,
                    callee,
                    regions,
                });
            }
            let result_dups = r.indices(region.results.len(), "a result")?;
            regions.push(RegionPlan {
                up,
                args,
                entry_drops,
                nodes,
                result_dups,
            });
        }
        if r.i != bytes.len() {
            return r.err(r.i, "bytes follow the plan, which ends here");
        }
        let plan = Plan { regions, fuse };
        // The links down, now that every region is read: each names a region that links back.
        for (at, rp) in plan.regions.iter().enumerate() {
            for (k, p) in rp.nodes.iter().enumerate() {
                let back = |&(i, &d): &(usize, &usize)| {
                    plan.regions
                        .get(d)
                        .is_some_and(|d| d.up == Some((at, k, i)))
                };
                let linked = p.regions.iter().enumerate().all(|x| back(&x));
                if !linked || p.callee.is_some_and(|c| c >= count) {
                    return Err(format!(
                        "node {} names a region the plan does not have, or one that does not \
                         link back to it",
                        plan.node_path(at, k)
                    ));
                }
            }
        }
        Ok(plan)
    }

    /// Whether this plan is the one [`plan`] makes of `g` with its `fuse`: the plan worked out
    /// again and compared, so a stored plan is trusted only after it. The message names the
    /// first region that differs.
    // Complexity tradeoff: the cost of planning `g`, O(occurrences + edges) ([`plan`]), plus a
    // comparison linear in the plan; the start of an executable reads the plan without this,
    // and this is what a check of an executable runs.
    pub fn recheck(&self, g: &Region) -> Result<(), String> {
        let fresh = plan(g, self.fuse);
        if fresh.regions.len() != self.regions.len() {
            return Err(format!(
                "the stored plan has {} regions, and the plan of the graph worked out again {}",
                self.regions.len(),
                fresh.regions.len()
            ));
        }
        match (fresh.regions.iter().zip(&self.regions)).position(|(a, b)| a != b) {
            None => Ok(()),
            Some(at) => Err(format!(
                "the stored plan of region {} differs from the plan of the graph worked out again",
                fresh.path(at)
            )),
        }
    }

    /// The path of node `k` of region `at`, for a message.
    fn node_path(&self, at: usize, k: usize) -> String {
        format!("{}.{k}", self.path(at))
    }
}

/// The bytes of a plan being read, and the place reached.
struct Reader<'a> {
    b: &'a [u8],
    i: usize,
}

impl Reader<'_> {
    fn err<T>(&self, at: usize, why: impl std::fmt::Display) -> Result<T, String> {
        Err(format!("byte {at} of the memory plan: {why}"))
    }

    fn byte(&mut self) -> Result<u8, String> {
        let b = *self
            .b
            .get(self.i)
            .map_or_else(|| self.err(self.i, ENDS), Ok)?;
        self.i += 1;
        Ok(b)
    }

    fn n(&mut self) -> Result<usize, String> {
        let Some(bytes) = self.b.get(self.i..).and_then(|b| b.first_chunk::<8>()) else {
            return self.err(self.i, ENDS);
        };
        let n = usize::try_from(u64::from_le_bytes(*bytes)).unwrap_or(usize::MAX);
        self.i += 8;
        Ok(n)
    }

    /// A count of items of at least `size` bytes each: no more than the bytes left hold.
    fn count(&mut self, size: usize) -> Result<usize, String> {
        let at = self.i;
        let n = self.n()?;
        match n <= (self.b.len() - self.i) / size {
            true => Ok(n),
            false => self.err(
                at,
                format!("the count {n} is more than the bytes left hold"),
            ),
        }
    }

    /// `want` modes, one for each of the `what`.
    fn modes(&mut self, want: usize, what: &str) -> Result<Vec<Mode>, String> {
        let at = self.i;
        if self.count(1)? != want {
            return self.err(
                at,
                format!("a count of modes other than the count of {what}"),
            );
        }
        (0..want)
            .map(|_| match self.byte()? {
                0 => Ok(Mode::Owned),
                1 => Ok(Mode::Borrowed),
                t => self.err(self.i - 1, format!("{t} is not a mode")),
            })
            .collect()
    }

    /// A list of indices, each below `below`, of `what`.
    fn indices(&mut self, below: usize, what: &str) -> Result<Vec<usize>, String> {
        let n = self.count(8)?;
        (0..n)
            .map(|_| match self.n()? {
                x if x < below => Ok(x),
                x => self.err(self.i - 8, format!("{x} does not name {what}")),
            })
            .collect()
    }

    /// A list of edges of `region`: each an argument of it or an output of one of its nodes
    /// numbered below `before`.
    ///
    /// Why the bound holds of every plan [`plan`] makes, and why it is needed. The planner
    /// (`Planner::region` in memory.rs) puts an edge made by node `m` among the drops of node
    /// `m` itself when nothing uses it, else among the drops or last uses of node `k`, its last
    /// use (`Uses::last`). A use at node `k` is an input of node `k`, and a node's inputs are its
    /// region's arguments, earlier nodes' outputs and constants (zir/mod.rs, "Regions are
    /// isolated"), so `m < k`. Hence the drops of node `k` name outputs of nodes `m <= k`
    /// (`before = k + 1`) and its last uses outputs of nodes `m < k` (`before = k`). The code
    /// generator reads a drop of node `k` after the node's outputs are kept
    /// (`codegen.rs` `finish`, `outs[m][p]`), when exactly nodes `0..=k` have outputs: a drop
    /// of a later node's output, which a plan with every index in range could hold, would
    /// index past them and panic. Test: `l01_36a_executables::plan_carried`
    /// (`each_kind_of_damage_is_refused_and_makes_no_panic_in_part_*`, and the corpus plans read
    /// back, which shows no plan the planner makes is refused by the bound).
    fn srcs(&mut self, region: &Region, before: usize) -> Result<Vec<Src>, String> {
        let n = self.count(9)?;
        (0..n)
            .map(|_| {
                let at = self.i;
                match self.byte()? {
                    0 => match self.n()? {
                        a if a < region.args.len() => Ok(Src::Arg(a)),
                        a => self.err(at, format!("{a} does not name an argument")),
                    },
                    1 => {
                        let (m, p) = (self.n()?, self.n()?);
                        let made = m < before && region.nodes[m].outputs.len() > p;
                        match made {
                            true => Ok(Src::Out(m, p)),
                            false => self.err(
                                at,
                                format!("no node {m} before node {before} with an output {p}"),
                            ),
                        }
                    }
                    t => self.err(at, format!("{t} is not a tag of an edge")),
                }
            })
            .collect()
    }
}
