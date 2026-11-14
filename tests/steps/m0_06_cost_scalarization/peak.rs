//! Step M0.6a: a device's footprint is the peak over its schedule of each region's footprint
//! plus the bytes the regions before it retain, not the sum of the footprints. The regions are
//! batch jobs on a 16 GiB machine: a sort that keeps its output for a later join, a scan that
//! keeps nothing.

use super::{plan, random_plan, workstation};
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::cost::{
    Device, Plan, Region, Target, dominates, feasible, frontier, pick, scalarize, vector,
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

/// The footprint the cost vector holds for `device` of `devices`: on the default profile for one
/// device, on the workstation for two.
fn footprint(p: &Plan, devices: usize, device: usize) -> u64 {
    let t = if devices == 1 {
        Target::default_profile()
    } else {
        workstation()
    };
    vector(p, &t)[3 * device + 2]
}

#[test]
fn two_jobs_that_each_fit_run_one_after_another() {
    // Two 10 GiB jobs that keep nothing: the second starts after the first has freed its
    // memory, so the machine holds 10 GiB at most. The sum, 20 GiB, would reject the plan.
    let t = Target::default_profile();
    let p = plan(1, vec![job(0, 10 * GIB, 0), job(0, 10 * GIB, 0)], vec![]);
    assert_eq!(footprint(&p, 1, 0), 10 * GIB);
    assert!(feasible(&p, &t));
    assert_eq!(pick(std::slice::from_ref(&p), &t), Some(p));
}

#[test]
fn bytes_a_job_keeps_for_later_ones_count_while_those_run() {
    // The sort keeps 8 GiB of sorted output for the join: 8 + 10 = 18 GiB, over 16 GiB.
    let t = Target::default_profile();
    let p = plan(
        1,
        vec![job(0, 10 * GIB, 8 * GIB), job(0, 10 * GIB, 0)],
        vec![],
    );
    assert_eq!(footprint(&p, 1, 0), 18 * GIB);
    assert!(!feasible(&p, &t));
    assert!(pick(&[p], &t).is_none());
    // What the last job keeps adds to nothing after it.
    let last = plan(
        2,
        vec![job(0, 10 * GIB, 0), job(0, 10 * GIB, 10 * GIB)],
        vec![],
    );
    assert_eq!(footprint(&last, 1, 0), 10 * GIB);
    // A small first job's footprint is below the second's, and the peak is the second plus
    // what the first keeps.
    let small_first = plan(3, vec![job(0, 2 * GIB, GIB), job(0, 12 * GIB, 0)], vec![]);
    assert_eq!(footprint(&small_first, 1, 0), 13 * GIB);
    assert!(feasible(&small_first, &t));
}

#[test]
fn retained_bytes_above_the_footprint_are_read_as_the_footprint() {
    let p = plan(
        1,
        vec![job(0, 4 * GIB, 100 * GIB), job(0, 10 * GIB, 0)],
        vec![],
    );
    assert_eq!(footprint(&p, 1, 0), 14 * GIB);
    assert!(feasible(&p, &Target::default_profile()));
}

#[test]
fn bytes_kept_on_one_device_do_not_count_on_another() {
    // The GPU job keeps 3 GiB of its 4 GiB; the CPU jobs between and after it do not see them,
    // and the next GPU job does.
    let t = workstation();
    let p = plan(
        1,
        vec![
            job(1, 4 * GIB, 3 * GIB),
            job(0, 12 * GIB, 2 * GIB),
            job(1, GIB, 0),
            job(0, 4 * GIB, 0),
        ],
        vec![GIB],
    );
    assert_eq!(footprint(&p, 2, 0), 12 * GIB);
    assert_eq!(footprint(&p, 2, 1), 4 * GIB);
    assert!(feasible(&p, &t));
    let more = plan(
        2,
        vec![job(1, 4 * GIB, 3 * GIB), job(1, 2 * GIB, 0)],
        vec![],
    );
    assert_eq!(footprint(&more, 2, 1), 5 * GIB);
    assert!(!feasible(&more, &t));
}

#[test]
fn retained_bytes_count_until_the_schedule_ends() {
    // The tradeoff of DESIGN.md M0.6a (COMPLEXITY.md C27): the sort keeps 8 GiB that only the
    // 6 GiB join right after it reads, so a schedule that frees them after the join peaks at
    // 14 GiB. The plan carries no last reader, so they are counted while the 10 GiB job runs
    // too, giving 18 GiB, and the plan is judged infeasible. The answer is never above the
    // sum of the footprints, 25 GiB.
    let t = Target::default_profile();
    let jobs = vec![
        job(0, 9 * GIB, 8 * GIB),
        job(0, 6 * GIB, 0),
        job(0, 10 * GIB, 0),
    ];
    let sum: u64 = jobs.iter().map(|r| r.footprint).sum();
    let p = plan(1, jobs, vec![]);
    assert_eq!(footprint(&p, 1, 0), 18 * GIB);
    assert!(footprint(&p, 1, 0) <= sum);
    assert!(!feasible(&p, &t));
}

#[test]
fn the_peak_saturates_at_huge_sizes() {
    let t = Target::default_profile();
    let half = u64::MAX / 2 + 1;
    // The retained bytes of the first two jobs alone overflow; the peak saturates.
    let p = plan(
        1,
        vec![job(0, half, half), job(0, half, half), job(0, 1, 0)],
        vec![],
    );
    assert_eq!(footprint(&p, 1, 0), u64::MAX);
    assert!(!feasible(&p, &t));
    // One job of the largest footprint, alone.
    let one = plan(2, vec![job(0, u64::MAX, u64::MAX)], vec![]);
    assert_eq!(footprint(&one, 1, 0), u64::MAX);
    // A device of unbounded capacity takes any footprint.
    let unbounded = Target {
        devices: vec![Device {
            capacity: u64::MAX,
            ..t.devices[0].clone()
        }],
        ..t
    };
    assert!(feasible(&p, &unbounded));
    // The scalar reads work and depth only: the retained bytes do not change it.
    let mut kept_none = p.clone();
    for r in &mut kept_none.regions {
        r.retained = 0;
    }
    assert_eq!(scalarize(&p, &unbounded), scalarize(&kept_none, &unbounded));
}

/// The peak by its definition: for each region, its footprint plus what every earlier region
/// on its device retains, recomputed from the start each time.
fn peak_by_definition(p: &Plan, device: usize) -> u64 {
    let on: Vec<&Region> = p.regions.iter().filter(|r| r.device == device).collect();
    (0..on.len())
        .map(|i| {
            on[..i].iter().fold(on[i].footprint, |s, r| {
                s.saturating_add(r.retained.min(r.footprint))
            })
        })
        .max()
        .unwrap_or(0)
}

#[test]
fn the_peak_agrees_with_its_definition_and_lies_between_the_largest_and_the_sum() {
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_peak_agrees_with_its_definition_and_lies_between_the_largest_and_the_sum",
    ));
    for _ in 0..RANDOM_INSTANCES / 4 {
        let p = random_plan(&mut rng, 2);
        for d in 0..2 {
            let on = p.regions.iter().filter(|r| r.device == d);
            let largest = on.clone().map(|r| r.footprint).max().unwrap_or(0);
            let sum: u64 = on.map(|r| r.footprint).sum();
            let peak = footprint(&p, 2, d);
            assert_eq!(peak, peak_by_definition(&p, d), "{p:?}");
            assert!(largest <= peak && peak <= sum, "{p:?}");
        }
    }
}

#[test]
fn the_peak_is_monotone_so_pruning_to_the_frontier_keeps_the_pick() {
    // A device of 1.5 MiB holds some random plans (regions below 1 MiB) and not others, so the
    // retained bytes decide feasibility. Raising a region's footprint or retained bytes never
    // lowers its device's peak; hence a plan that dominates a feasible one is feasible, and the
    // pick from the frontier is the least scalar, then address, of every feasible plan.
    let mut t = workstation();
    for d in &mut t.devices {
        d.capacity = 3 << 19;
    }
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_peak_is_monotone_so_pruning_to_the_frontier_keeps_the_pick",
    ));
    let (mut feasible_seen, mut infeasible_seen) = (0, 0);
    for _ in 0..RANDOM_INSTANCES / 4 {
        let p = random_plan(&mut rng, 2);
        let i = rng.below(p.regions.len());
        let mut larger = p.clone();
        larger.regions[i].footprint += rng.below(1 << 20) as u64;
        let mut keeps_more = p.clone();
        keeps_more.regions[i].retained += rng.below(1 << 20) as u64;
        for q in [&larger, &keeps_more] {
            for d in 0..2 {
                assert!(footprint(q, 2, d) >= footprint(&p, 2, d), "{p:?} {q:?}");
            }
            assert!(!feasible(q, &t) || feasible(&p, &t));
        }

        let plans: Vec<Plan> = (0..2 + rng.below(6))
            .map(|_| random_plan(&mut rng, 2))
            .collect();
        let ok: Vec<&Plan> = plans.iter().filter(|q| feasible(q, &t)).collect();
        feasible_seen += ok.len();
        infeasible_seen += plans.len() - ok.len();
        for a in &plans {
            for b in &ok {
                if dominates(&vector(a, &t), &vector(b, &t)) {
                    assert!(feasible(a, &t), "{a:?} dominates {b:?}");
                }
            }
        }
        let best = ok.iter().min_by_key(|q| (scalarize(q, &t), q.address));
        assert_eq!(pick(&plans, &t).as_ref(), best.copied());
        assert!(frontier(&plans, &t).iter().all(|q| feasible(q, &t)));
    }
    assert!(feasible_seen > 0 && infeasible_seen > 0);
}

/// `r` jobs alternating between the CPU and the GPU with footprints and retained bytes that
/// repeat, so the peak moves through the whole schedule.
pub(super) fn alternating(r: usize) -> Plan {
    let regions = (0..r)
        .map(|i| {
            let i = i as u64;
            job((i % 2) as usize, (i % 97 + 1) * 4096, (i % 13) * 64)
        })
        .collect();
    plan(0, regions, vec![])
}

/// The peak of [`alternating`] at small sizes: every job is far below a device's capacity, so
/// each plan is feasible, and its cost vector is found. The time is held in `bench/peak.rs`.
#[test]
fn the_peak_of_alternating_jobs_is_found_at_small_sizes() {
    let t = workstation();
    for r in [1, 2, 9] {
        let p = alternating(r);
        assert!(feasible(&p, &t));
        assert!(!vector(&p, &t).is_empty());
    }
}
