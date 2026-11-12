//! The cost scalarization (DESIGN.md sec:runtime, "Cost model, two tiers", written by step
//! M0.6).
//!
//! The symbolic tier gives each alternative plan a work, a depth and a peak live footprint per
//! placed region, and the bytes crossing each cut edge between devices. Plans are held as a
//! Pareto frontier over those quantities until the scalarization picks one: it turns a plan
//! into one integer, an estimate of its running time in the target's time unit, and breaks a
//! tie by content address, so extraction is reproducible. The placement solver of step L24.5
//! uses the same function, so placement and extraction agree on what a plan costs.
//!
//! All arithmetic is on integers and saturates, so the result is the same on every host.

use rustc_hash::FxHashMap;

use crate::address::ContentAddress;

/// One device of a target: CPU cores, a GPU, a remote node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Device {
    /// The device's name in `target(…)`, such as `cpu` or `gpu`.
    pub name: &'static str,
    /// Processors the device runs in parallel.
    pub cores: u64,
    /// Time units per unit of work on one core.
    pub op_time: u64,
    /// The largest live footprint, in bytes, a plan may place on the device.
    pub capacity: u64,
}

/// A target profile: its devices and the cost of moving data between them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Target {
    /// The devices, the first being the one unplaced code runs on.
    pub devices: Vec<Device>,
    /// Time units for each transfer over a cut edge, whatever its size.
    pub transfer_latency: u64,
    /// Time units per 64 bytes transferred, rounded up to whole blocks.
    pub transfer_per_block: u64,
    /// The size the scalarization assumes for a cardinality the domains leave unbounded.
    pub nominal_size: u64,
}

impl Target {
    /// The default target profile: one CPU of 8 cores, one time unit (read as a nanosecond)
    /// per unit of work, 16 GiB of memory. With one device no edge is cut. Unbounded
    /// cardinalities are taken as 2^20.
    pub fn default_profile() -> Self {
        Target {
            devices: vec![Device {
                name: "cpu",
                cores: 8,
                op_time: 1,
                capacity: 1 << 34,
            }],
            transfer_latency: 0,
            transfer_per_block: 0,
            nominal_size: 1 << 20,
        }
    }

    /// The size a cost is evaluated at for a cardinality with upper bound `bound`.
    pub fn size(&self, bound: Option<u64>) -> u64 {
        bound.unwrap_or(self.nominal_size)
    }

    /// The cost of one transfer of `bytes` over a cut edge.
    pub fn transfer(&self, bytes: u64) -> u64 {
        self.transfer_latency
            .saturating_add(bytes.div_ceil(64).saturating_mul(self.transfer_per_block))
    }
}

/// The symbolic cost of one region placed on one device, evaluated at the target's sizes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Region {
    /// The index of the device in [`Target::devices`].
    pub device: usize,
    /// Work: operations summed over the region's graph, shared nodes once.
    pub work: u64,
    /// Depth: the operations on its critical path.
    pub depth: u64,
    /// The largest live set the static plan admits while the region runs, in bytes.
    pub footprint: u64,
    /// The bytes of the region's results that stay live for later regions on its device, at
    /// most `footprint` (a larger value is read as `footprint`). Whoever builds the plan fills
    /// it from the region's live results at its end: the cost model of step L3.23 and the
    /// placement solver of step L24.5 (DESIGN.md step M0.6a).
    pub retained: u64,
}

/// One alternative plan: its regions, when it runs them, the bytes crossing each cut edge, and
/// its address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    /// The plan's content address, the tie-break.
    pub address: ContentAddress,
    /// The placed regions.
    pub regions: Vec<Region>,
    /// The bytes crossing each edge whose ends lie on different devices.
    pub cut_edges: Vec<u64>,
    /// When the regions run, which decides the regions a device holds at once.
    pub schedule: Schedule,
}

/// When a plan runs its regions (DESIGN.md step M0.6a). A schedule that does not name each
/// region exactly once makes the plan infeasible.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Schedule {
    /// A static schedule (strategy i of sec:runtime): each region's start time and length, in
    /// the target's time unit, in the order of [`Plan::regions`]. The times already respect
    /// each device's cores.
    Timed(Vec<Span>),
    /// Work stealing (strategy ii): the series-parallel nesting of the regions, in postfix.
    Nested(Vec<Nest>),
}

impl Schedule {
    /// `r` regions run one after another in the order the plan lists them.
    pub fn sequence(r: usize) -> Self {
        Schedule::Nested(
            (0..r)
                .map(Nest::Region)
                .chain([Nest::Sequence(r)])
                .collect(),
        )
    }
}

/// When a region of a static schedule runs: from `start` until `start + length`. A region of
/// length 0 runs at the instant `start`, beside every region that runs then.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    /// The time the region starts.
    pub start: u64,
    /// The time it runs.
    pub length: u64,
}

/// One step of a series-parallel nesting written in postfix: a region pushes one entry on a
/// stack, and a composition replaces the `k` entries on top with one. A nesting ends with one
/// entry, or with none when the plan has no region.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Nest {
    /// The region of this index in [`Plan::regions`].
    Region(usize),
    /// The `k` entries on top run one after another, the deepest first.
    Sequence(usize),
    /// The `k` entries on top may run at once.
    Parallel(usize),
}

/// The time bound for `work` and `depth` on `cores` processors, by Brent's theorem: the
/// critical path, plus the rest of the work shared among the cores, rounded up.
pub fn brent(work: u64, depth: u64, cores: u64) -> u64 {
    let depth = depth.min(work);
    (work - depth).div_ceil(cores.max(1)).saturating_add(depth)
}

/// Whether the plan respects every device's capacity: the footprint of each device (see
/// `footprints`) is at most its capacity. A plan that names a device the target lacks, or whose
/// schedule does not name each region exactly once, is infeasible.
pub fn feasible(plan: &Plan, target: &Target) -> bool {
    footprints(plan, target).is_some_and(|f| {
        f.iter()
            .zip(&target.devices)
            .all(|(&bytes, device)| bytes <= device.capacity)
    })
}

/// The work and depth a plan places on each device, in device order: they add, whatever the
/// schedule. A region on a device the target lacks is left out (the plan is infeasible).
fn work_and_depth(plan: &Plan, devices: usize) -> Vec<[u64; 2]> {
    let mut out = vec![[0u64; 2]; devices];
    for r in &plan.regions {
        if let Some(d) = out.get_mut(r.device) {
            d[0] = d[0].saturating_add(r.work);
            d[1] = d[1].saturating_add(r.depth);
        }
    }
    out
}

/// The footprint of each device, in device order: the largest number of bytes its regions hold
/// at once under the plan's schedule, a running region holding its footprint and a finished one
/// its retained bytes (DESIGN.md step M0.6a). `None` when a region names a device the target
/// lacks or the schedule does not name each region exactly once.
///
/// The footprint is monotone in every region's footprint and retained bytes, so a plan no worse
/// in those is no worse in the frontier's footprint, and the frontier stays sound (step M0.6).
///
/// Complexity tradeoff: a region's retained bytes stay counted until the end of its device's
/// schedule, not freed after their last reader. The answer is an upper bound on the live set,
/// never above the sum of footprints step M0.6 used, so a plan whose retained results die early
/// may be judged infeasible when its true peak fits. Freeing at the last reader needs each
/// region's last reader on its device, which `Region` does not carry; with it, a release event
/// at that reader's end gives the exact peak at the same cost. Triggered by a region that
/// retains bytes read only by the next region, followed by large regions. Test:
/// m0_06_cost_scalarization::peak::retained_bytes_count_until_the_schedule_ends;
/// COMPLEXITY.md C27.
fn footprints(plan: &Plan, target: &Target) -> Option<Vec<u64>> {
    let devices = target.devices.len();
    if plan.regions.iter().any(|r| r.device >= devices) {
        return None;
    }
    match &plan.schedule {
        Schedule::Timed(spans) => {
            (spans.len() == plan.regions.len()).then(|| sweep(&plan.regions, spans, devices))
        }
        Schedule::Nested(steps) => nested(&plan.regions, steps, target),
    }
}

/// The exact footprint of each device under a static schedule: a sweep over the regions' starts
/// and ends in time order, O(r log r + devices) for r regions. At one instant the regions that
/// end there are counted as ended, then those that start there as running, then the regions of
/// length 0 there end, so a region of length 0 counts beside every region running at its
/// instant. The bytes running and kept are summed in `u128`, exactly, since an end subtracts.
fn sweep(regions: &[Region], spans: &[Span], devices: usize) -> Vec<u64> {
    const END: u8 = 0;
    const START: u8 = 1;
    const END_OF_INSTANT: u8 = 2;
    let mut events: Vec<(usize, u64, u8, usize)> = Vec::with_capacity(2 * regions.len());
    for (i, (r, s)) in regions.iter().zip(spans).enumerate() {
        let end = s.start.saturating_add(s.length);
        events.push((r.device, s.start, START, i));
        events.push((
            r.device,
            end,
            if end > s.start { END } else { END_OF_INSTANT },
            i,
        ));
    }
    events.sort_unstable();
    let mut peak = vec![0u64; devices];
    let mut running = vec![0u128; devices];
    let mut kept = vec![0u128; devices];
    for (d, _, kind, i) in events {
        let r = &regions[i];
        if kind == START {
            running[d] += u128::from(r.footprint);
            let live = u64::try_from(kept[d] + running[d]).unwrap_or(u64::MAX);
            peak[d] = peak[d].max(live);
        } else {
            running[d] -= u128::from(r.footprint);
            kept[d] += u128::from(r.retained.min(r.footprint));
        }
    }
    peak
}

/// What a part of a plan holds on one device: its peak, and the bytes its regions retain after
/// it ends, at most the peak. The zero load, a part with no region on the device, is the
/// identity of each composition below.
#[derive(Clone, Copy, Debug, Default)]
struct Load {
    peak: u64,
    kept: u64,
}

impl Load {
    fn of(r: &Region) -> Load {
        Load {
            peak: r.footprint,
            kept: r.retained.min(r.footprint),
        }
    }

    /// `self`, then `b`: `b` runs on what `self` keeps.
    fn then(self, b: Load) -> Load {
        Load {
            peak: self.peak.max(self.kept.saturating_add(b.peak)),
            kept: self.kept.saturating_add(b.kept),
        }
    }

    /// `self` and `b` at once on a device of several cores: both may be at their peaks.
    fn beside(self, b: Load) -> Load {
        Load {
            peak: self.peak.saturating_add(b.peak),
            kept: self.kept.saturating_add(b.kept),
        }
    }

    /// `self` and `b` at once on a device of one core: one region runs at a time, in either
    /// order, so one part is at most at its peak while the other holds at most what it keeps.
    fn interleaved(self, b: Load) -> Load {
        Load {
            peak: self
                .peak
                .saturating_add(b.kept)
                .max(b.peak.saturating_add(self.kept)),
            kept: self.kept.saturating_add(b.kept),
        }
    }
}

/// The loads of a part of a plan on the devices that hold its regions.
type Loads = FxHashMap<usize, Load>;

/// A part of a plan on the stack of [`nested`]: on one device, held without a map (every region,
/// and every part whose regions share a device), or on several.
enum Part {
    One(usize, Load),
    Many(Loads),
}

/// The footprint of each device under work stealing: the series-parallel nesting evaluated in
/// one pass over its postfix steps, with an explicit stack. On each device a sequence takes
/// the peak of each part on what the parts before it keep; a parallel composition adds its
/// parts' peaks on a device of several cores, and on a device of one core (0 is read as 1)
/// takes one part's peak on what the others keep, since one region runs there at a time.
/// `None` when a step names a region that does not exist or was named before (the visited set
/// `seen`), a composition takes more entries than the stack holds, a region is never named, or
/// more than one entry is left.
///
/// Complexity tradeoff: this is an upper bound. Under work stealing on several cores a task
/// whose children were stolen lets its worker take another task, so more regions than cores
/// may have started, and a parallel composition counts all its parts at their peaks at once.
/// Where the regions' dependences form a DAG that is not series-parallel, whoever builds the
/// plan writes a nesting whose parallel compositions hold every pair of regions the DAG lets
/// run at once (at worst, all of a level's regions in one parallel composition), which is again
/// an upper bound: the exact footprint there is the heaviest set of regions no two of which are
/// ordered, a maximum-weight antichain, found through a minimum flow in O(r·e) or more for e
/// dependences, above O(N log N). A plan judged so may be refused where its exact footprint
/// fits. Test: m0_06_cost_scalarization::overlap::a_dag_that_is_not_series_parallel_is_judged_at_the_upper_bound;
/// COMPLEXITY.md C53.
// Complexity tradeoff: the naive evaluation keeps an array of every device's load at each stack
// entry, O(r · devices) for r regions; here each entry holds only the devices its regions use,
// and two entries are joined by moving the smaller map into the larger, so a region's device
// entry moves O(log r) times (a map holds at most as many entries as its part has regions):
// O(r log r + devices) expected time. A part on one device, the common case of a region and of
// a sequence on one device, needs no map, so the nesting of `Schedule::sequence` costs one
// map per device in all.
fn nested(regions: &[Region], steps: &[Nest], target: &Target) -> Option<Vec<u64>> {
    let one_core = |d: usize| target.devices[d].cores <= 1;
    let in_series = |_: usize, x: Load, y: Load| x.then(y);
    let at_once = |d: usize, x: Load, y: Load| {
        if one_core(d) {
            x.interleaved(y)
        } else {
            x.beside(y)
        }
    };
    let mut seen = vec![false; regions.len()];
    let mut stack: Vec<Part> = Vec::new();
    for &step in steps {
        let (k, parallel) = match step {
            Nest::Region(i) => {
                let r = regions.get(i)?;
                if std::mem::replace(&mut seen[i], true) {
                    return None;
                }
                stack.push(Part::One(r.device, Load::of(r)));
                continue;
            }
            Nest::Sequence(k) => (k, false),
            Nest::Parallel(k) => (k, true),
        };
        let at = stack.len().checked_sub(k)?;
        let part = stack
            .drain(at..)
            .reduce(|a, b| {
                if parallel {
                    join(a, b, at_once)
                } else {
                    join(a, b, in_series)
                }
            })
            .unwrap_or_else(|| Part::Many(Loads::default()));
        stack.push(part);
    }
    if stack.len() > 1 || seen.contains(&false) {
        return None;
    }
    let mut out = vec![0u64; target.devices.len()];
    match stack.pop() {
        None => {}
        Some(Part::One(d, load)) => out[d] = load.peak,
        Some(Part::Many(loads)) => {
            for (d, load) in loads {
                out[d] = load.peak;
            }
        }
    }
    Some(out)
}

/// The loads of `a` composed with those of `b` (`a` the earlier part) by `op` on each device,
/// iterating over the smaller part. A device missing from one part is the zero load there, the
/// identity of `op`.
fn join(a: Part, b: Part, op: impl Fn(usize, Load, Load) -> Load) -> Part {
    match (a, b) {
        (Part::One(d, x), Part::One(e, y)) if d == e => Part::One(d, op(d, x, y)),
        (Part::One(d, x), Part::One(e, y)) => Part::Many(Loads::from_iter([(d, x), (e, y)])),
        (Part::Many(mut a), Part::One(d, y)) => {
            let x = a.entry(d).or_default();
            *x = op(d, *x, y);
            Part::Many(a)
        }
        (Part::One(d, x), Part::Many(mut b)) => {
            let y = b.entry(d).or_default();
            *y = op(d, x, *y);
            Part::Many(b)
        }
        (Part::Many(mut a), Part::Many(mut b)) => {
            if a.len() >= b.len() {
                for (d, y) in b {
                    let x = a.entry(d).or_default();
                    *x = op(d, *x, y);
                }
                Part::Many(a)
            } else {
                for (d, x) in a {
                    let y = b.entry(d).or_default();
                    *y = op(d, x, *y);
                }
                Part::Many(b)
            }
        }
    }
}

/// The scalar cost of a feasible plan on a target: for each device, the Brent bound of the
/// work and depth placed on it, times the device's time per operation, plus one transfer per
/// cut edge. Devices are summed as if they ran one after another, an upper bound on the
/// plan's running time that is monotone in every component of [`vector`].
pub fn scalarize(plan: &Plan, target: &Target) -> u64 {
    let compute = work_and_depth(plan, target.devices.len())
        .iter()
        .zip(&target.devices)
        .fold(0u64, |s, (w, device)| {
            s.saturating_add(brent(w[0], w[1], device.cores).saturating_mul(device.op_time))
        });
    plan.cut_edges.iter().fold(compute, |s, &bytes| {
        s.saturating_add(target.transfer(bytes))
    })
}

/// The plan's cost vector on a target, the quantities the frontier compares: the work, depth
/// and footprint on each device, then the number of cut edges and the 64-byte blocks they
/// carry. The footprint of a plan whose schedule or devices are malformed is `u64::MAX` on
/// every device. The scalar is monotone in each component, and feasibility is antitone in each,
/// so the frontier never drops the plan [`pick`] would choose.
pub fn vector(plan: &Plan, target: &Target) -> Vec<u64> {
    let devices = target.devices.len();
    let bytes = footprints(plan, target).unwrap_or_else(|| vec![u64::MAX; devices]);
    let mut v: Vec<u64> = work_and_depth(plan, devices)
        .into_iter()
        .zip(bytes)
        .flat_map(|([work, depth], bytes)| [work, depth, bytes])
        .collect();
    v.push(plan.cut_edges.len() as u64);
    v.push(
        plan.cut_edges
            .iter()
            .fold(0u64, |s, &b| s.saturating_add(b.div_ceil(64))),
    );
    v
}

/// Whether `a` dominates `b`: no worse in every quantity and better in one.
pub fn dominates(a: &[u64], b: &[u64]) -> bool {
    a.iter().zip(b).all(|(x, y)| x <= y) && a != b
}

/// The Pareto frontier of the feasible `plans` on `target`: the feasible plans no other
/// feasible plan dominates, in content-address order (`order`). Plans with equal cost vectors are all
/// kept.
///
/// A plan's dominators all precede it in the lexicographic order of the vectors, and a
/// dominated dominator is itself dominated by a plan of the frontier, so each plan is compared
/// only with the frontier found before it: `O(P log P + P·F·devices)` for `F` plans on the
/// frontier. No known algorithm finds a Pareto frontier of more than three quantities in
/// `O(P log P)`, and this vector has `3·devices + 2`.
// Complexity tradeoff (COMPLEXITY.md F20): the naive frontier compares every pair of plans,
// O(P² · devices); the lexicographic sort lets each plan be compared only with the frontier
// found before it, O(P log P + P · F · devices). It is still O(P² · devices) when every plan
// is on the frontier (F = P), the size of the output's pairwise check; no known algorithm does
// better for more than three quantities. Memory: one cost vector per feasible plan.
pub fn frontier(plans: &[Plan], target: &Target) -> Vec<Plan> {
    let mut live: Vec<(&Plan, Vec<u64>)> = plans
        .iter()
        .filter(|p| feasible(p, target))
        .map(|p| (p, vector(p, target)))
        .collect();
    live.sort_by(|a, b| a.1.cmp(&b.1));
    let mut front: Vec<(&Plan, Vec<u64>)> = Vec::new();
    for (p, v) in live {
        if !front.iter().any(|(_, w)| dominates(w, &v)) {
            front.push((p, v));
        }
    }
    let mut kept: Vec<Plan> = front.into_iter().map(|(p, _)| p.clone()).collect();
    kept.sort_by(|a, b| order(a).cmp(&order(b)));
    kept
}

/// The order plans are kept and tied in: by content address, and of equal addresses by their
/// regions, cut edges and schedule, so that two distinct plans whose addresses collide still have one
/// order and the pick does not depend on the order the plans were given in (step L1.37a).
fn order(p: &Plan) -> (ContentAddress, &[Region], &[u64], &Schedule) {
    (p.address, &p.regions, &p.cut_edges, &p.schedule)
}

/// The plan the scalarization picks: on the frontier, the least scalar cost, then the least
/// content address, and of equal addresses the first in `order`. `None` when no plan is
/// feasible, where the placement solver falls back to its list schedule (sec:runtime).
pub fn pick(plans: &[Plan], target: &Target) -> Option<Plan> {
    let mut front = frontier(plans, target);
    let i = (0..front.len()).min_by_key(|&i| (scalarize(&front[i], target), order(&front[i])))?;
    Some(front.swap_remove(i))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn brent_bounds_lie_between_depth_and_work() {
        for work in 0..40u64 {
            for depth in 0..=work {
                for cores in 1..6 {
                    let t = brent(work, depth, cores);
                    assert!(depth <= t && t <= work, "{work} {depth} {cores}");
                    assert!(t >= work.div_ceil(cores));
                }
            }
        }
        // Zero cores are read as one, and a depth above the work as the work.
        assert_eq!(brent(10, 3, 0), 10);
        assert_eq!(brent(10, 30, 4), 10);
    }

    #[test]
    fn arithmetic_saturates() {
        let t = Target::default_profile();
        let plan = Plan {
            address: ContentAddress([0; 32]),
            regions: vec![
                Region {
                    device: 0,
                    work: u64::MAX,
                    depth: u64::MAX,
                    footprint: u64::MAX,
                    retained: u64::MAX,
                };
                2
            ],
            cut_edges: vec![],
            schedule: Schedule::sequence(2),
        };
        assert_eq!(scalarize(&plan, &t), u64::MAX);
        // The second region's footprint on top of the first's retained bytes saturates.
        assert_eq!(vector(&plan, &t), vec![u64::MAX, u64::MAX, u64::MAX, 0, 0]);
        assert!(!feasible(&plan, &t));
    }
}
