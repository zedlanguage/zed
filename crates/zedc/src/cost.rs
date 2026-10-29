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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Region {
    /// The index of the device in [`Target::devices`].
    pub device: usize,
    /// Work: operations summed over the region's graph, shared nodes once.
    pub work: u64,
    /// Depth: the operations on its critical path.
    pub depth: u64,
    /// The largest live set the static plan admits, in bytes.
    pub footprint: u64,
}

/// One alternative plan: its regions, the bytes crossing each cut edge, and its address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    /// The plan's content address, the tie-break.
    pub address: ContentAddress,
    /// The placed regions.
    pub regions: Vec<Region>,
    /// The bytes crossing each edge whose ends lie on different devices.
    pub cut_edges: Vec<u64>,
}

/// The time bound for `work` and `depth` on `cores` processors, by Brent's theorem: the
/// critical path, plus the rest of the work shared among the cores, rounded up.
pub fn brent(work: u64, depth: u64, cores: u64) -> u64 {
    let depth = depth.min(work);
    (work - depth).div_ceil(cores.max(1)).saturating_add(depth)
}

/// Whether the plan respects every device's capacity: the footprints placed on a device sum to
/// at most its capacity. A plan that names a device the target lacks is infeasible.
pub fn feasible(plan: &Plan, target: &Target) -> bool {
    let n = target.devices.len();
    plan.regions.iter().all(|r| r.device < n)
        && per_device(plan, n)
            .iter()
            .zip(&target.devices)
            .all(|(w, device)| w[2] <= device.capacity)
}

/// The work, depth and footprint a plan places on each device, in device order: the regions
/// on one device run one after another, so their work, depth and footprint add.
fn per_device(plan: &Plan, devices: usize) -> Vec<[u64; 3]> {
    let mut out = vec![[0u64; 3]; devices];
    for r in &plan.regions {
        let d = &mut out[r.device];
        d[0] = d[0].saturating_add(r.work);
        d[1] = d[1].saturating_add(r.depth);
        d[2] = d[2].saturating_add(r.footprint);
    }
    out
}

/// The scalar cost of a feasible plan on a target: for each device, the Brent bound of the
/// work and depth placed on it, times the device's time per operation, plus one transfer per
/// cut edge. Devices are summed as if they ran one after another, an upper bound on the
/// plan's running time that is monotone in every component of [`vector`].
pub fn scalarize(plan: &Plan, target: &Target) -> u64 {
    let compute = per_device(plan, target.devices.len())
        .iter()
        .zip(&target.devices)
        .fold(0u64, |s, (w, device)| {
            s.saturating_add(brent(w[0], w[1], device.cores).saturating_mul(device.op_time))
        });
    plan.cut_edges.iter().fold(compute, |s, &bytes| {
        s.saturating_add(target.transfer(bytes))
    })
}

/// The plan's cost vector on a target with `devices` devices, the quantities the frontier
/// compares: the work, depth and footprint on each device, then the number of cut edges and
/// the 64-byte blocks they carry. The scalar is monotone in each component, and feasibility
/// is antitone in each, so the frontier never drops the plan [`pick`] would choose.
pub fn vector(plan: &Plan, devices: usize) -> Vec<u64> {
    let mut v: Vec<u64> = per_device(plan, devices).into_iter().flatten().collect();
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
/// feasible plan dominates, in content-address order. Plans with equal cost vectors are all
/// kept.
pub fn frontier(plans: &[Plan], target: &Target) -> Vec<Plan> {
    let n = target.devices.len();
    let live: Vec<(&Plan, Vec<u64>)> = plans
        .iter()
        .filter(|p| feasible(p, target))
        .map(|p| (p, vector(p, n)))
        .collect();
    let mut kept: Vec<Plan> = live
        .iter()
        .filter(|(_, v)| !live.iter().any(|(_, w)| dominates(w, v)))
        .map(|(p, _)| (*p).clone())
        .collect();
    kept.sort_by_key(|p| p.address);
    kept
}

/// The plan the scalarization picks: on the frontier, the least scalar cost, then the least
/// content address. `None` when no plan is feasible, where the placement solver falls back to
/// its list schedule (sec:runtime).
pub fn pick(plans: &[Plan], target: &Target) -> Option<Plan> {
    frontier(plans, target)
        .into_iter()
        .min_by_key(|p| (scalarize(p, target), p.address))
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
                    footprint: 0,
                };
                2
            ],
            cut_edges: vec![],
        };
        assert_eq!(scalarize(&plan, &t), u64::MAX);
    }
}
