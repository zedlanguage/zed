//! Step M0.6: the cost scalarization (DESIGN.md sec:runtime). Plans for a log-processing
//! pipeline (parse each line, keep the errors, count them by service) placed on a CPU alone or
//! split with a GPU, compared by the scalar cost and by content address.

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::address::ContentAddress;
use zedc::cost::{
    Device, Plan, Region, Target, brent, dominates, feasible, frontier, pick, scalarize, vector,
};

/// The address whose last byte is `n` and whose other bytes are zero.
fn addr(n: u8) -> ContentAddress {
    let mut b = [0u8; 32];
    b[31] = n;
    ContentAddress(b)
}

/// A workstation: 8 CPU cores and a GPU of 1,024 lanes, each lane four times slower than a
/// core, with 4 GiB of GPU memory; a transfer costs 5,000 units plus 2 per 64-byte block.
fn workstation() -> Target {
    Target {
        devices: vec![
            Device {
                name: "cpu",
                cores: 8,
                op_time: 1,
                capacity: 1 << 34,
            },
            Device {
                name: "gpu",
                cores: 1024,
                op_time: 4,
                capacity: 1 << 32,
            },
        ],
        transfer_latency: 5_000,
        transfer_per_block: 2,
        nominal_size: 1 << 20,
    }
}

const LINES: u64 = 1 << 20;

/// Parsing 2^20 log lines: 40 operations a line, every line independent.
fn parse(device: usize) -> Region {
    Region {
        device,
        work: 40 * LINES,
        depth: 40,
        footprint: 64 * LINES,
    }
}

/// Counting errors by service: a tree reduction, depth logarithmic in the lines.
fn count(device: usize) -> Region {
    Region {
        device,
        work: 2 * LINES,
        depth: 2 * 20,
        footprint: 8 * LINES,
    }
}

fn plan(address: u8, regions: Vec<Region>, cut_edges: Vec<u64>) -> Plan {
    Plan {
        address: addr(address),
        regions,
        cut_edges,
    }
}

#[test]
fn plans_of_equal_cost_are_ordered_by_content_address() {
    // The same two regions listed in either order are two plans with different addresses and
    // the same cost; the lower address wins, whatever order the plans arrive in.
    let t = Target::default_profile();
    let a = plan(9, vec![parse(0), count(0)], vec![]);
    let b = plan(3, vec![count(0), parse(0)], vec![]);
    assert_eq!(scalarize(&a, &t), scalarize(&b, &t));
    assert_eq!(pick(&[a.clone(), b.clone()], &t).unwrap().address, addr(3));
    assert_eq!(pick(&[b, a], &t).unwrap().address, addr(3));
}

#[test]
fn a_plan_that_cuts_one_more_edge_costs_one_more_transfer() {
    // Parse on the GPU and count on the CPU cuts the edge carrying the parsed records (8 bytes
    // a line); also sending the counts back to the GPU for a final step cuts one more.
    let t = workstation();
    let split = plan(1, vec![parse(1), count(0)], vec![8 * LINES]);
    let more = plan(2, vec![parse(1), count(0)], vec![8 * LINES, 4096]);
    assert_eq!(
        scalarize(&more, &t) - scalarize(&split, &t),
        t.transfer(4096)
    );
    assert_eq!(t.transfer(4096), 5_000 + 64 * 2);
    // A transfer of a partial block costs the whole block.
    assert_eq!(t.transfer(1), 5_002);
    assert_eq!(t.transfer(0), 5_000);
}

#[test]
fn the_default_profile_runs_everything_on_eight_cores() {
    let t = Target::default_profile();
    assert_eq!(t.devices.len(), 1);
    assert_eq!((t.devices[0].cores, t.devices[0].op_time), (8, 1));
    assert_eq!(t.devices[0].capacity, 16 << 30);
    assert_eq!(t.size(None), 1 << 20);
    assert_eq!(t.size(Some(100)), 100);
    // Parsing: the 40-operation critical path plus the rest of the work shared by 8 cores.
    let p = plan(0, vec![parse(0)], vec![]);
    assert_eq!(scalarize(&p, &t), (40 * LINES - 40) / 8 + 40);
}

#[test]
fn the_gpu_wins_when_the_work_is_large_enough_to_pay_for_the_transfer() {
    let t = workstation();
    let cpu = plan(1, vec![parse(0), count(0)], vec![]);
    let gpu = plan(2, vec![parse(1), count(0)], vec![8 * LINES]);
    assert!(scalarize(&gpu, &t) < scalarize(&cpu, &t));
    assert_eq!(
        pick(&[cpu.clone(), gpu.clone()], &t).unwrap().address,
        addr(2)
    );
    // On a small input the transfer dominates and the CPU plan wins.
    let small = |r: Region| Region {
        work: r.work / 4096,
        footprint: r.footprint / 4096,
        ..r
    };
    let cpu = plan(1, vec![small(parse(0)), small(count(0))], vec![]);
    let gpu = plan(
        2,
        vec![small(parse(1)), small(count(0))],
        vec![8 * LINES / 4096],
    );
    assert_eq!(pick(&[cpu, gpu], &t).unwrap().address, addr(1));
}

#[test]
fn a_plan_over_a_device_capacity_is_not_picked() {
    // Keeping 2^27 lines on the GPU needs 8 GiB, more than its 4 GiB.
    let t = workstation();
    let big = |r: Region| Region {
        work: r.work * 128,
        footprint: r.footprint * 128,
        ..r
    };
    let gpu = plan(1, vec![big(parse(1)), big(count(0))], vec![8 * LINES * 128]);
    let cpu = plan(2, vec![big(parse(0)), big(count(0))], vec![]);
    assert!(!feasible(&gpu, &t));
    assert!(scalarize(&gpu, &t) < scalarize(&cpu, &t));
    assert_eq!(pick(&[gpu.clone(), cpu], &t).unwrap().address, addr(2));
    // With no feasible plan, nothing is picked and the solver falls back to its list schedule.
    assert!(pick(&[gpu], &t).is_none());
    // A plan naming a device the target lacks is infeasible.
    assert!(!feasible(&plan(3, vec![parse(2)], vec![]), &t));
}

#[test]
fn the_frontier_keeps_incomparable_plans_and_drops_dominated_ones() {
    // Fused: less work, deeper. Split: more work, shallower. Wasteful: worse than split in
    // every quantity.
    let fused = plan(
        5,
        vec![Region {
            device: 0,
            work: 100,
            depth: 50,
            footprint: 10,
        }],
        vec![],
    );
    let split = plan(
        4,
        vec![Region {
            device: 0,
            work: 120,
            depth: 10,
            footprint: 10,
        }],
        vec![],
    );
    let waste = plan(
        6,
        vec![Region {
            device: 0,
            work: 130,
            depth: 10,
            footprint: 20,
        }],
        vec![],
    );
    let twin = plan(
        1,
        vec![Region {
            device: 0,
            work: 120,
            depth: 10,
            footprint: 10,
        }],
        vec![],
    );
    let kept: Vec<ContentAddress> =
        frontier(&[fused, split, waste, twin], &Target::default_profile())
            .iter()
            .map(|p| p.address)
            .collect();
    assert_eq!(kept, vec![addr(1), addr(4), addr(5)]);
}

fn random_plan(rng: &mut Rng, devices: usize) -> Plan {
    let regions = (0..1 + rng.below(4))
        .map(|_| {
            let work = rng.below(10_000) as u64;
            Region {
                device: rng.below(devices),
                work,
                depth: rng.below(work as usize + 1) as u64,
                footprint: rng.below(1 << 20) as u64,
            }
        })
        .collect();
    let cut_edges = (0..rng.below(3))
        .map(|_| rng.below(1 << 16) as u64)
        .collect();
    plan(rng.below(256) as u8, regions, cut_edges)
}

#[test]
fn the_scalar_is_monotone_in_work_depth_and_cut_edges() {
    let t = workstation();
    let mut rng = Rng::new(0x6c05);
    for _ in 0..RANDOM_INSTANCES {
        let p = plan_with(&mut rng);
        let base = scalarize(&p, &t);
        let i = rng.below(p.regions.len());
        let mut more_work = p.clone();
        more_work.regions[i].work += 1 + rng.below(100) as u64;
        assert!(scalarize(&more_work, &t) >= base);
        let mut deeper = p.clone();
        deeper.regions[i].depth = (deeper.regions[i].depth + 1).min(deeper.regions[i].work);
        assert!(scalarize(&deeper, &t) >= base);
        let mut cut = p.clone();
        let bytes = rng.below(1 << 16) as u64;
        cut.cut_edges.push(bytes);
        assert_eq!(scalarize(&cut, &t), base + t.transfer(bytes));
    }
}

fn plan_with(rng: &mut Rng) -> Plan {
    random_plan(rng, 2)
}

#[test]
fn the_pick_is_the_same_in_every_arrival_order_and_minimal_over_every_feasible_plan() {
    let t = workstation();
    let mut rng = Rng::new(0xf00d);
    let mut pruned = 0;
    for _ in 0..RANDOM_INSTANCES {
        let mut plans: Vec<Plan> = (0..2 + rng.below(6))
            .map(|_| random_plan(&mut rng, 2))
            .collect();
        let first = pick(&plans, &t);
        for _ in 0..4 {
            let i = rng.below(plans.len());
            let j = rng.below(plans.len());
            plans.swap(i, j);
            assert_eq!(pick(&plans, &t), first);
        }
        // Pruning to the frontier loses nothing: the pick has the least scalar of every
        // feasible plan, and a plan the frontier drops is never cheaper than one it keeps.
        let feasible_plans: Vec<&Plan> = plans.iter().filter(|q| feasible(q, &t)).collect();
        let kept = frontier(&plans, &t);
        pruned += feasible_plans.len() - kept.len();
        match first {
            None => assert!(feasible_plans.is_empty()),
            Some(p) => {
                for q in &feasible_plans {
                    assert!(scalarize(q, &t) >= scalarize(&p, &t));
                    if !kept.contains(q) {
                        assert!(kept.iter().any(|k| dominates(&vector(k, 2), &vector(q, 2))
                            && scalarize(k, &t) <= scalarize(q, &t)));
                    }
                }
            }
        }
    }
    assert!(
        pruned > RANDOM_INSTANCES / 2,
        "the frontier pruned only {pruned} plans"
    );
    assert_eq!(brent(0, 0, 8), 0);
}
