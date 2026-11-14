//! Step M0.6a: a device's footprint counts together the regions the plan may run at once. A
//! static schedule gives each region a start and a length, and the footprint is found exactly by
//! a sweep over them; work stealing gives a series-parallel nesting, and the footprint is an
//! upper bound found in one pass: a parallel composition adds its parts' peaks on a device of
//! several cores, a sequence takes the peak. The regions are batch jobs on a 16 GiB machine.

use super::{addr, workstation};
use Nest::{Parallel, Region as R, Sequence};
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::cost::{
    Device, Nest, Plan, Region, Schedule, Span, Target, feasible, pick, scalarize, vector,
};

const GIB: u64 = 1 << 30;

fn job(device: usize, footprint: u64, retained: u64) -> Region {
    Region {
        device,
        work: footprint / 64,
        depth: 64,
        footprint,
        retained,
    }
}

fn scheduled(address: u8, regions: Vec<Region>, schedule: Schedule) -> Plan {
    Plan {
        address: addr(address),
        regions,
        cut_edges: vec![],
        schedule,
    }
}

fn nested(address: u8, regions: Vec<Region>, steps: &[Nest]) -> Plan {
    scheduled(address, regions, Schedule::Nested(steps.to_vec()))
}

fn timed(address: u8, regions: Vec<Region>, spans: &[(u64, u64)]) -> Plan {
    let spans = spans
        .iter()
        .map(|&(start, length)| Span { start, length })
        .collect();
    scheduled(address, regions, Schedule::Timed(spans))
}

/// The footprints in the plan's cost vector, one per device of the target.
fn footprints(p: &Plan, t: &Target) -> Vec<u64> {
    vector(p, t)
        .chunks(3)
        .take(t.devices.len())
        .map(|w| w[2])
        .collect()
}

/// The default profile with `cores` cores: one device of 16 GiB.
fn machine(cores: u64) -> Target {
    let mut t = Target::default_profile();
    t.devices[0].cores = cores;
    t
}

#[test]
fn two_regions_that_run_at_once_count_together() {
    // Two independent 10 GiB jobs on 8 cores: a work-stealing schedule may run them at once,
    // 20 GiB, over 16 GiB. Before step M0.6a's clause the peak took them one after another,
    // 10 GiB, and the plan was feasible: that answer is the sequence below.
    let t = machine(8);
    let both = || vec![job(0, 10 * GIB, 0), job(0, 10 * GIB, 0)];
    let stolen = nested(1, both(), &[R(0), R(1), Parallel(2)]);
    assert_eq!(footprints(&stolen, &t), vec![20 * GIB]);
    assert!(!feasible(&stolen, &t));
    assert!(pick(std::slice::from_ref(&stolen), &t).is_none());
    // A static schedule that overlaps them, from time 5 to 10, holds both too.
    let overlapping = timed(2, both(), &[(0, 10), (5, 10)]);
    assert_eq!(footprints(&overlapping, &t), vec![20 * GIB]);
    assert!(!feasible(&overlapping, &t));
}

#[test]
fn the_same_regions_one_after_another_fit() {
    let t = machine(8);
    let both = || vec![job(0, 10 * GIB, 0), job(0, 10 * GIB, 0)];
    let in_order = nested(1, both(), &[R(0), R(1), Sequence(2)]);
    assert_eq!(footprints(&in_order, &t), vec![10 * GIB]);
    assert!(feasible(&in_order, &t));
    assert_eq!(in_order.schedule, Schedule::sequence(2));
    // The static schedule that starts the second when the first ends: the two do not overlap.
    let touching = timed(2, both(), &[(0, 10), (10, 10)]);
    assert_eq!(footprints(&touching, &t), vec![10 * GIB]);
    assert!(feasible(&touching, &t));
    assert_eq!(pick(std::slice::from_ref(&touching), &t), Some(touching));
}

#[test]
fn a_device_of_one_core_holds_the_peak_of_the_worse_order() {
    // On one core the two jobs run one after another, in either order: the sort keeping 4 GiB
    // first gives 4 + 8 = 12 GiB, the scan first gives 10 GiB. The footprint is the worse,
    // 12 GiB, the sequential peak of that order, not the sum 18 GiB.
    let jobs = || vec![job(0, 10 * GIB, 4 * GIB), job(0, 8 * GIB, 0)];
    let par = [R(0), R(1), Parallel(2)];
    for cores in [0, 1] {
        let t = machine(cores);
        assert_eq!(footprints(&nested(1, jobs(), &par), &t), vec![12 * GIB]);
        let sort_first = nested(2, jobs(), &[R(0), R(1), Sequence(2)]);
        let scan_first = nested(3, jobs(), &[R(1), R(0), Sequence(2)]);
        assert_eq!(footprints(&sort_first, &t), vec![12 * GIB]);
        assert_eq!(footprints(&scan_first, &t), vec![10 * GIB]);
    }
    assert_eq!(
        footprints(&nested(1, jobs(), &par), &machine(2)),
        vec![18 * GIB]
    );
    // On the workstation the GPU's two jobs of one parallel composition add, and the CPU's job
    // beside them counts on the CPU alone.
    let t = workstation();
    let mixed = nested(
        4,
        vec![job(0, 3 * GIB, 0), job(1, GIB, 0), job(1, 2 * GIB, GIB)],
        &[R(0), R(1), R(2), Parallel(3)],
    );
    assert_eq!(footprints(&mixed, &t), vec![3 * GIB, 3 * GIB]);
}

#[test]
fn a_static_schedule_counts_what_runs_at_each_instant() {
    let t = workstation();
    // The first job keeps 2 GiB after time 4; the second runs from 4, the third from 6.
    let p = timed(
        1,
        vec![job(0, 3 * GIB, 2 * GIB), job(0, 5 * GIB, 0), job(0, GIB, 0)],
        &[(0, 4), (4, 4), (6, 1)],
    );
    assert_eq!(footprints(&p, &t), vec![8 * GIB, 0]);
    // Jobs of length 0 at one instant count together and beside a job running then, but not
    // beside one that ends at that instant.
    let instant = timed(
        2,
        vec![
            job(0, 3 * GIB, 0),
            job(0, 3 * GIB, 0),
            job(0, 4 * GIB, 0),
            job(0, 2 * GIB, 0),
        ],
        &[(3, 0), (3, 0), (1, 5), (0, 3)],
    );
    assert_eq!(footprints(&instant, &t), vec![10 * GIB, 0]);
    // A job of length 0 keeps its bytes after its instant.
    let kept = timed(
        3,
        vec![job(1, GIB, GIB), job(1, 3 * GIB + 1, 0)],
        &[(2, 0), (5, 1)],
    );
    assert_eq!(footprints(&kept, &t), vec![0, 4 * GIB + 1]);
    assert!(!feasible(&kept, &t));
    // A span reaching past the largest time ends there, before a region that starts there.
    let late = timed(
        4,
        vec![job(1, GIB, 0), job(1, GIB, 0)],
        &[(u64::MAX - 1, 5), (u64::MAX, 0)],
    );
    assert_eq!(footprints(&late, &t), vec![0, GIB]);
}

#[test]
fn huge_sizes_saturate() {
    let t = machine(8);
    let half = u64::MAX / 2 + 1;
    let huge = || vec![job(0, half, half), job(0, half, half), job(0, 1, 0)];
    let par = nested(1, huge(), &[R(0), R(1), R(2), Parallel(3)]);
    assert_eq!(footprints(&par, &t), vec![u64::MAX]);
    let at_once = timed(2, huge(), &[(0, 1), (0, 1), (0, 1)]);
    assert_eq!(footprints(&at_once, &t), vec![u64::MAX]);
    // In a sweep the running bytes fall again after an end; the sum is held exactly.
    let apart = timed(3, huge(), &[(0, 1), (0, 1), (2, 1)]);
    assert_eq!(footprints(&apart, &t), vec![u64::MAX]);
    let single = timed(4, vec![job(0, half, 0), job(0, half, 0)], &[(0, 1), (1, 1)]);
    assert_eq!(footprints(&single, &t), vec![half]);
}

#[test]
fn a_schedule_that_does_not_name_each_region_once_makes_the_plan_infeasible() {
    let t = workstation();
    let jobs = || vec![job(0, GIB, 0), job(1, GIB, 0)];
    let bad: Vec<Plan> = vec![
        nested(1, jobs(), &[R(0), R(1)]),
        nested(2, jobs(), &[R(0), R(0), Parallel(2)]),
        nested(3, jobs(), &[R(0), Sequence(1)]),
        nested(4, jobs(), &[R(0), R(2), Sequence(2)]),
        nested(5, jobs(), &[R(0), R(1), Parallel(3)]),
        nested(6, jobs(), &[]),
        timed(7, jobs(), &[(0, 1)]),
        timed(8, jobs(), &[(0, 1), (0, 1), (0, 1)]),
        // A region on a device the target lacks; the cost vector once panicked here.
        nested(
            9,
            vec![job(0, GIB, 0), job(2, GIB, 0)],
            &[R(0), R(1), Sequence(2)],
        ),
    ];
    for p in &bad {
        assert!(!feasible(p, &t), "{p:?}");
        assert_eq!(footprints(p, &t), vec![u64::MAX; 2], "{p:?}");
        assert!(pick(std::slice::from_ref(p), &t).is_none());
    }
    // The work and depth of the regions on the target's devices are still counted.
    assert_eq!(vector(&bad[8], &t)[..2], [GIB / 64, 64]);
    assert!(scalarize(&bad[8], &t) > 0);
    // A plan with no region: an empty nesting, a composition of nothing, or no spans.
    for p in [
        nested(10, vec![], &[]),
        nested(11, vec![], &[Sequence(0)]),
        nested(12, vec![], &[Parallel(0)]),
        timed(13, vec![], &[]),
        nested(14, vec![job(0, GIB, 0)], &[R(0), Parallel(0), Sequence(2)]),
    ] {
        assert!(feasible(&p, &t), "{p:?}");
    }
}

#[test]
fn a_dag_that_is_not_series_parallel_is_judged_at_the_upper_bound() {
    // The complexity tradeoff at `nested` (COMPLEXITY.md C53). Jobs a, b, c, d with c after a
    // and b, and d after b: a may run beside b or d, and c beside d. No series-parallel nesting
    // has exactly these orders; a(b(c d)) with a in parallel keeps every pair that may run at
    // once: a ∥ (b ; (c ∥ d)). It also lets a run beside c, so the bound is a + c + d = 18 GiB,
    // over 16 GiB, where the heaviest set of jobs the DAG lets run at once is {a, d} or {c, d},
    // 12 GiB. A static schedule of the DAG is measured exactly.
    let t = machine(8);
    let jobs = || {
        vec![
            job(0, 6 * GIB, 0),
            job(0, GIB, 0),
            job(0, 6 * GIB, 0),
            job(0, 6 * GIB, 0),
        ]
    };
    let stolen = nested(
        1,
        jobs(),
        &[
            R(0),
            R(1),
            R(2),
            R(3),
            Parallel(2),
            Sequence(2),
            Parallel(2),
        ],
    );
    assert_eq!(footprints(&stolen, &t), vec![18 * GIB]);
    assert!(!feasible(&stolen, &t));
    // a from 0 to 4, b from 0 to 1, d from 1 to 6, c from 4 to 6.
    let exact = timed(2, jobs(), &[(0, 4), (0, 1), (4, 2), (1, 5)]);
    assert_eq!(footprints(&exact, &t), vec![12 * GIB]);
    assert!(feasible(&exact, &t));
}

/// A random series-parallel nesting of `ids` in postfix, each composition of two or three
/// parts, with `before[i][j]` set where the nesting runs `i` before `j`.
fn random_nesting(rng: &mut Rng, ids: &[usize], before: &mut [Vec<bool>], out: &mut Vec<Nest>) {
    if let [i] = ids {
        out.push(R(*i));
        return;
    }
    let k = 2 + rng.below(ids.len().min(3) - 1);
    let mut cuts: Vec<usize> = Vec::new();
    while cuts.len() < k - 1 {
        let c = 1 + rng.below(ids.len() - 1);
        if !cuts.contains(&c) {
            cuts.push(c);
        }
    }
    cuts.sort_unstable();
    let bounds: Vec<usize> = [0].into_iter().chain(cuts).chain([ids.len()]).collect();
    let parts: Vec<&[usize]> = bounds.windows(2).map(|w| &ids[w[0]..w[1]]).collect();
    for part in &parts {
        random_nesting(rng, part, before, out);
    }
    if rng.below(2) == 0 {
        for (x, first) in parts.iter().enumerate() {
            for later in &parts[x + 1..] {
                for &i in *first {
                    for &j in *later {
                        before[i][j] = true;
                    }
                }
            }
        }
        out.push(Sequence(k));
    } else {
        out.push(Parallel(k));
    }
}

/// The footprint of each device by its definition, over every state the precedence allows:
/// each region not started, running or finished, a region started only after every region
/// before it finished, and at most one region running on a device of one core. A running region
/// holds its footprint, a finished one its retained bytes, at most its footprint.
fn footprints_by_states(regions: &[Region], before: &[Vec<bool>], t: &Target) -> Vec<u64> {
    let r = regions.len();
    let mut peak = vec![0u128; t.devices.len()];
    let mut state = vec![0u8; r];
    for code in 0..3usize.pow(r as u32) {
        let mut c = code;
        for s in &mut state {
            *s = (c % 3) as u8;
            c /= 3;
        }
        let allowed =
            (0..r).all(|j| state[j] == 0 || (0..r).all(|i| !before[i][j] || state[i] == 2));
        let crowded = (0..t.devices.len()).any(|d| {
            t.devices[d].cores <= 1
                && (0..r)
                    .filter(|&i| regions[i].device == d && state[i] == 1)
                    .count()
                    > 1
        });
        if !allowed || crowded {
            continue;
        }
        let mut live = vec![0u128; t.devices.len()];
        for (x, s) in regions.iter().zip(&state) {
            live[x.device] += match s {
                1 => u128::from(x.footprint),
                2 => u128::from(x.retained.min(x.footprint)),
                _ => 0,
            };
        }
        for (p, l) in peak.iter_mut().zip(live) {
            *p = (*p).max(l);
        }
    }
    peak.into_iter()
        .map(|p| u64::try_from(p).unwrap_or(u64::MAX))
        .collect()
}

/// The footprint of each device by its definition under a static schedule: the most bytes held
/// at any region's start, each region running from its start until before its end (at its start
/// alone if its length is 0) and then keeping its retained bytes.
fn footprints_by_instants(regions: &[Region], spans: &[Span], devices: usize) -> Vec<u64> {
    let mut peak = vec![0u128; devices];
    for s in spans {
        let now = s.start;
        let mut live = vec![0u128; devices];
        for (x, y) in regions.iter().zip(spans) {
            let end = y.start.saturating_add(y.length);
            let running = (y.start <= now && now < end) || (y.start == now && end == now);
            if running {
                live[x.device] += u128::from(x.footprint);
            } else if end <= now {
                live[x.device] += u128::from(x.retained.min(x.footprint));
            }
        }
        for (p, l) in peak.iter_mut().zip(live) {
            *p = (*p).max(l);
        }
    }
    peak.into_iter()
        .map(|p| u64::try_from(p).unwrap_or(u64::MAX))
        .collect()
}

/// Two devices: 8 cores, then one core.
fn two_kinds() -> Target {
    let mut t = workstation();
    t.devices[1].cores = 1;
    t
}

fn random_regions(rng: &mut Rng, r: usize, devices: usize) -> Vec<Region> {
    (0..r)
        .map(|_| {
            let footprint = rng.below(1 << 20) as u64;
            Region {
                device: rng.below(devices),
                work: rng.below(10_000) as u64,
                depth: 1,
                footprint,
                retained: rng.below(2 * footprint as usize + 1) as u64,
            }
        })
        .collect()
}

/// A random plan of up to `max` regions on `t`'s devices, with a random nesting or a random
/// static schedule; for a nesting, also the precedence it sets.
fn random_scheduled(rng: &mut Rng, max: usize, t: &Target) -> (Plan, Vec<Vec<bool>>) {
    let r = 1 + rng.below(max);
    let regions = random_regions(rng, r, t.devices.len());
    let mut before = vec![vec![false; r]; r];
    let schedule = if rng.below(2) == 0 {
        let mut ids: Vec<usize> = (0..r).collect();
        for i in (1..r).rev() {
            ids.swap(i, rng.below(i + 1));
        }
        let mut steps = Vec::new();
        random_nesting(rng, &ids, &mut before, &mut steps);
        Schedule::Nested(steps)
    } else {
        Schedule::Timed(
            (0..r)
                .map(|_| Span {
                    start: rng.below(8) as u64,
                    length: rng.below(4) as u64,
                })
                .collect(),
        )
    };
    (scheduled(rng.below(256) as u8, regions, schedule), before)
}

#[test]
fn the_footprint_agrees_with_its_definition() {
    let t = two_kinds();
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_footprint_agrees_with_its_definition",
    ));
    let (mut nestings, mut timings) = (0, 0);
    for _ in 0..RANDOM_INSTANCES / 4 {
        let (p, before) = random_scheduled(&mut rng, 7, &t);
        let expected = match &p.schedule {
            Schedule::Nested(_) => {
                nestings += 1;
                footprints_by_states(&p.regions, &before, &t)
            }
            Schedule::Timed(spans) => {
                timings += 1;
                footprints_by_instants(&p.regions, spans, 2)
            }
        };
        assert_eq!(footprints(&p, &t), expected, "{p:?}");
        // The regions one after another, by nesting or by back-to-back spans on each device,
        // give the sequential peak of step M0.6a.
        let r = p.regions.len();
        let in_order = scheduled(0, p.regions.clone(), Schedule::sequence(r));
        let mut ends = [0u64; 2];
        let spans: Vec<Span> = p
            .regions
            .iter()
            .map(|x| {
                let length = 1 + x.work % 3;
                let start = ends[x.device];
                ends[x.device] += length;
                Span { start, length }
            })
            .collect();
        let back_to_back = scheduled(0, p.regions.clone(), Schedule::Timed(spans));
        let mut chain = vec![vec![false; r]; r];
        for (i, row) in chain.iter_mut().enumerate() {
            for b in &mut row[i + 1..] {
                *b = true;
            }
        }
        let sequential = footprints_by_states(&p.regions, &chain, &t);
        assert_eq!(footprints(&in_order, &t), sequential, "{p:?}");
        assert_eq!(footprints(&back_to_back, &t), sequential, "{p:?}");
    }
    assert!(nestings > 20 && timings > 20);
}

#[test]
fn the_footprint_is_monotone_so_pruning_to_the_frontier_keeps_the_pick() {
    let mut t = two_kinds();
    for d in &mut t.devices {
        d.capacity = 3 << 19;
    }
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_footprint_is_monotone_so_pruning_to_the_frontier_keeps_the_pick",
    ));
    let (mut feasible_seen, mut infeasible_seen) = (0, 0);
    for _ in 0..RANDOM_INSTANCES / 4 {
        let (p, _) = random_scheduled(&mut rng, 5, &t);
        let i = rng.below(p.regions.len());
        let mut larger = p.clone();
        larger.regions[i].footprint += rng.below(1 << 20) as u64;
        let mut keeps_more = p.clone();
        keeps_more.regions[i].retained += rng.below(1 << 20) as u64;
        for q in [&larger, &keeps_more] {
            let (a, b) = (footprints(q, &t), footprints(&p, &t));
            assert!(a.iter().zip(&b).all(|(x, y)| x >= y), "{p:?} {q:?}");
            assert!(!feasible(q, &t) || feasible(&p, &t));
        }
        let plans: Vec<Plan> = (0..2 + rng.below(6))
            .map(|_| random_scheduled(&mut rng, 5, &t).0)
            .collect();
        let ok: Vec<&Plan> = plans.iter().filter(|q| feasible(q, &t)).collect();
        feasible_seen += ok.len();
        infeasible_seen += plans.len() - ok.len();
        let best = ok
            .iter()
            .min_by_key(|q| (scalarize(q, &t), q.address))
            .map(|q| (scalarize(q, &t), q.address));
        let picked = pick(&plans, &t).map(|q| (scalarize(&q, &t), q.address));
        assert_eq!(picked, best);
    }
    assert!(feasible_seen > 0 && infeasible_seen > 0);
}

/// A target of `d` devices of 1 GiB, of one core and of 8 cores in turn.
fn many_devices(d: usize) -> Target {
    Target {
        devices: (0..d)
            .map(|i| Device {
                name: "dev",
                cores: if i % 2 == 0 { 1 } else { 8 },
                op_time: 1,
                capacity: GIB,
            })
            .collect(),
        ..Target::default_profile()
    }
}

fn sized(i: usize, device: usize) -> Region {
    let i = i as u64;
    job(device, (i % 97 + 1) * 4096, (i % 13) * 64)
}

/// `r` jobs alternating between two devices, each lasting 1 to 8 time units and starting 2
/// apart, so up to four overlap on each device.
pub(super) fn static_schedule(r: usize) -> Plan {
    let regions: Vec<Region> = (0..r).map(|i| sized(i, i % 2)).collect();
    let spans = (0..r as u64)
        .map(|i| Span {
            start: 2 * i,
            length: 1 + i * 7 % 8,
        })
        .collect();
    scheduled(0, regions, Schedule::Timed(spans))
}

/// The postfix of a balanced nesting of regions `lo..hi`, sequences and parallel compositions
/// in turn by depth.
fn balanced(lo: usize, hi: usize, depth: usize, out: &mut Vec<Nest>) {
    if hi - lo == 1 {
        out.push(R(lo));
        return;
    }
    let mid = lo + (hi - lo) / 2;
    balanced(lo, mid, depth + 1, out);
    balanced(mid, hi, depth + 1, out);
    out.push(if depth.is_multiple_of(2) {
        Sequence(2)
    } else {
        Parallel(2)
    });
}

/// `r` regions (`r` at least 4) in a balanced nesting on `r/4` devices, region i on device i
/// mod r/4: the parts of each composition share devices, so their loads are joined, not only
/// moved.
pub(super) fn balanced_nesting(r: usize) -> (Plan, Target) {
    let d = r / 4;
    let regions = (0..r).map(|i| sized(i, i % d)).collect();
    let mut steps = Vec::new();
    balanced(0, r, 0, &mut steps);
    (
        scheduled(0, regions, Schedule::Nested(steps)),
        many_devices(d),
    )
}

/// `r` regions (`r` even) on `r/2` devices in `r/2` parallel pairs, each pair on two devices,
/// the pairs nested to the right: each sequence joins one pair to the loads of all the pairs
/// after it. Joining into the larger part keeps this within r log r; joining into the earlier
/// part, the naive way, reads O(r) devices per step.
pub(super) fn deep_nesting(r: usize) -> (Plan, Target) {
    let d = r / 2;
    let regions = (0..r).map(|i| sized(i, i % d)).collect();
    let steps = (0..r / 2)
        .flat_map(|i| [R(2 * i), R(2 * i + 1), Parallel(2)])
        .chain(std::iter::repeat_n(Sequence(2), r / 2 - 1))
        .collect();
    (
        scheduled(0, regions, Schedule::Nested(steps)),
        many_devices(d),
    )
}

/// The footprint of each input `bench/overlap.rs` times, at small sizes: every job is far below
/// a device's capacity, so each plan is feasible, and its cost vector is found.
#[test]
fn the_footprint_of_each_benchmark_input_is_found_at_small_sizes() {
    let t = workstation();
    for r in [1, 2, 9] {
        let p = static_schedule(r);
        assert!(feasible(&p, &t));
        assert!(!vector(&p, &t).is_empty());
    }
    for r in [4, 8, 32] {
        let (p, t) = balanced_nesting(r);
        assert!(feasible(&p, &t));
        assert!(!vector(&p, &t).is_empty());
    }
    for r in [2, 4, 18] {
        let (p, t) = deep_nesting(r);
        assert!(feasible(&p, &t));
        assert!(!vector(&p, &t).is_empty());
    }
}
