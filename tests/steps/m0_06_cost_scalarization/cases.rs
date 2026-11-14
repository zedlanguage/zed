//! Completeness cases for the cost scalarization (TEST-complete-m0, author P189): each formula
//! DESIGN.md step M0.6 fixes, checked at its boundaries with values worked out by hand. The
//! case list is `COMPLETENESS.md`.

use super::{addr, plan, workstation};
use zedc::address::ContentAddress;
use zedc::cost::{
    Device, Plan, Region, Schedule, Target, brent, dominates, feasible, frontier, pick, scalarize,
    vector,
};

const GIB: u64 = 1 << 30;

fn region(device: usize, work: u64, depth: u64, footprint: u64) -> Region {
    Region {
        device,
        work,
        depth,
        footprint,
        retained: 0,
    }
}

#[test]
fn the_default_profile_is_one_cpu_of_8_cores_with_16_gib() {
    // DESIGN.md M0.6: "one CPU of 8 cores at one time unit per unit of work with 16 GiB and no
    // other device, and every profile takes an unbounded cardinality as 2^20".
    let t = Target::default_profile();
    assert_eq!(
        t.devices,
        [Device {
            name: "cpu",
            cores: 8,
            op_time: 1,
            capacity: 16 * GIB,
        }]
    );
    assert_eq!(t.nominal_size, 1 << 20);
    assert_eq!(t.size(None), 1 << 20);
    assert_eq!(t.size(Some(0)), 0);
    assert_eq!(t.size(Some(5)), 5);
    assert_eq!(t.size(Some(u64::MAX)), u64::MAX);
    // With one device no edge is cut, and a transfer costs nothing.
    assert_eq!(t.transfer(1 << 40), 0);
}

#[test]
fn a_transfer_is_a_latency_plus_whole_64_byte_blocks() {
    // The workstation: 5,000 units a transfer plus 2 per 64-byte block, rounded up.
    let t = workstation();
    for (bytes, blocks) in [
        (0, 0),
        (1, 1),
        (63, 1),
        (64, 1),
        (65, 2),
        (128, 2),
        (129, 3),
    ] {
        assert_eq!(t.transfer(bytes), 5_000 + 2 * blocks, "{bytes} bytes");
    }
    assert_eq!(t.transfer(u64::MAX), 5_000 + 2 * (u64::MAX / 64 + 1));
    let mut dear = workstation();
    dear.transfer_per_block = u64::MAX;
    assert_eq!(dear.transfer(65), u64::MAX, "saturates");
    let mut no_latency = workstation();
    no_latency.transfer_latency = 0;
    assert_eq!(no_latency.transfer(64), 2);
}

#[test]
fn brent_is_the_rest_of_the_work_shared_among_the_cores_plus_the_depth() {
    // ⌈(work − depth) / cores⌉ + depth.
    for (work, depth, cores, t) in [
        (0, 0, 8, 0),
        (8, 0, 8, 1),
        (9, 0, 8, 2),
        (100, 4, 8, 16),
        (100, 100, 8, 100),
        (100, 1, 1, 100),
        (u64::MAX, 0, 1, u64::MAX),
        (u64::MAX, u64::MAX, 8, u64::MAX),
    ] {
        assert_eq!(brent(work, depth, cores), t, "{work} {depth} {cores}");
    }
}

#[test]
fn the_scalar_sums_the_devices_and_adds_one_transfer_per_cut_edge() {
    let t = workstation();
    // CPU: ⌈(100 − 4) / 8⌉ + 4 = 16 at 1 unit; GPU: ⌈(4096 − 0) / 1024⌉ + 0 = 4 at 4 units;
    // two cut edges of 64 and 65 bytes: 5,002 and 5,004.
    let p = plan(
        1,
        vec![region(0, 100, 4, 0), region(1, 4096, 0, 0)],
        vec![64, 65],
    );
    assert_eq!(scalarize(&p, &t), 16 + 4 * 4 + 5_002 + 5_004);
    // Work and depth on one device add before the bound is taken.
    let two = plan(2, vec![region(0, 50, 2, 0), region(0, 50, 2, 0)], vec![]);
    assert_eq!(scalarize(&two, &t), 16);
    // A device with no region costs nothing, and a plan with no region costs its transfers.
    assert_eq!(scalarize(&plan(3, vec![], vec![]), &t), 0);
    assert_eq!(scalarize(&plan(4, vec![], vec![1]), &t), 5_002);
}

#[test]
fn the_vector_lists_work_depth_footprint_per_device_then_edges_and_blocks() {
    let t = workstation();
    let p = plan(
        1,
        vec![region(0, 100, 4, 10), region(1, 4096, 3, 20)],
        vec![64, 65, 0],
    );
    assert_eq!(vector(&p, &t), [100, 4, 10, 4096, 3, 20, 3, 1 + 2]);
    assert_eq!(
        vector(&plan(2, vec![], vec![]), &Target::default_profile()),
        [0, 0, 0, 0, 0]
    );
}

#[test]
fn a_plan_is_feasible_up_to_each_device_capacity_and_no_further() {
    let t = workstation();
    let at = plan(1, vec![region(1, 1, 1, 4 * GIB)], vec![]);
    assert!(feasible(&at, &t));
    let over = plan(2, vec![region(1, 1, 1, 4 * GIB + 1)], vec![]);
    assert!(!feasible(&over, &t));
    // The same bytes fit on the CPU's 16 GiB.
    assert!(feasible(
        &plan(3, vec![region(0, 1, 1, 4 * GIB + 1)], vec![]),
        &t
    ));
    // A target of no device admits only plans with no region.
    let none = Target {
        devices: vec![],
        ..workstation()
    };
    assert!(feasible(&plan(4, vec![], vec![]), &none));
    assert!(!feasible(&plan(5, vec![region(0, 1, 1, 0)], vec![]), &none));
    assert_eq!(vector(&plan(6, vec![], vec![7]), &none), [1, 1]);
}

#[test]
fn dominance_is_no_worse_everywhere_and_better_somewhere() {
    assert!(!dominates(&[1, 2], &[1, 2]), "equal vectors");
    assert!(dominates(&[1, 2], &[1, 3]));
    assert!(dominates(&[0, 0], &[1, 3]));
    assert!(!dominates(&[1, 3], &[1, 2]));
    assert!(!dominates(&[0, 3], &[1, 2]), "incomparable");
    assert!(!dominates(&[1, 2], &[0, 3]), "incomparable");
    assert!(!dominates(&[], &[]));
}

#[test]
fn no_plan_and_no_feasible_plan_give_an_empty_frontier_and_no_pick() {
    let t = workstation();
    assert!(frontier(&[], &t).is_empty());
    assert_eq!(pick(&[], &t), None);
    let over = plan(1, vec![region(1, 1, 1, u64::MAX)], vec![]);
    assert!(frontier(std::slice::from_ref(&over), &t).is_empty());
    assert_eq!(pick(&[over.clone(), over], &t), None);
}

#[test]
fn plans_of_equal_vectors_are_all_kept_in_address_order() {
    let t = workstation();
    let same = |a| plan(a, vec![region(0, 10, 2, 5)], vec![]);
    let worse = plan(0, vec![region(0, 11, 2, 5)], vec![]);
    let kept = frontier(&[same(9), worse.clone(), same(3), same(6)], &t);
    let addresses: Vec<ContentAddress> = kept.iter().map(|p| p.address).collect();
    assert_eq!(addresses, [addr(3), addr(6), addr(9)]);
    assert_eq!(
        pick(&[same(9), worse, same(3)], &t).unwrap().address,
        addr(3)
    );
}

#[test]
fn a_lower_scalar_wins_over_a_lower_address() {
    let t = workstation();
    // Incomparable vectors (less work, more depth), so both stay on the frontier.
    let cheap = plan(9, vec![region(0, 8, 8, 0)], vec![]);
    let dear = plan(1, vec![region(0, 800, 0, 0)], vec![]);
    assert_eq!(scalarize(&cheap, &t), 8);
    assert_eq!(scalarize(&dear, &t), 100);
    assert_eq!(frontier(&[cheap.clone(), dear.clone()], &t).len(), 2);
    assert_eq!(pick(&[dear, cheap.clone()], &t), Some(cheap));
}

#[test]
fn plans_whose_addresses_collide_are_ordered_by_their_contents() {
    // Step L1.37a: the pick does not depend on the order the plans arrive in.
    let t = workstation();
    let a = Plan {
        schedule: Schedule::Nested(vec![]),
        ..plan(5, vec![], vec![])
    };
    let b = plan(5, vec![], vec![]);
    assert_ne!(a, b);
    assert_eq!(pick(&[a.clone(), b.clone()], &t), pick(&[b, a], &t));
}
