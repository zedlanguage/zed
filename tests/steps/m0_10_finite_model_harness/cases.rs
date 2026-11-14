//! Completeness cases for step M0.10 (TEST-complete-m0, author P189): the harness's instances
//! are the ones DESIGN.md M0.10 names, its enumerations and random generator give what they
//! promise, and it reports a wrong claim. The case list is `COMPLETENESS.md`.

use zed_kernel::{Schedule, Value};
use zed_tests::check::{property, property_refuted};
use zed_tests::instances::{
    BMC_FLOATS, BMC_INT, ENUMERATION_BUDGET, RANDOM_INSTANCES, Rng, bmc_floats, bmc_ints,
    partial_maps, shortlex,
};

use super::int_maps;
use super::recursion::schedules;

#[test]
fn the_instances_are_the_ones_design_names() {
    // DESIGN.md M0.10: "The instances are `int[-8..=8]`, ..., and for floats `0.0`, `-0.0`,
    // `1.0`, `0.1`, `0.2`, `0.3`, both infinities and a NaN, with at most 4,096 bindings of
    // each law's binder domains ... plus 512 seeded random instances beyond them".
    assert_eq!(BMC_INT, -8..=8);
    assert_eq!(bmc_ints(), (-8..=8).collect::<Vec<i64>>());
    let want = [
        0.0,
        -0.0,
        1.0,
        0.1,
        0.2,
        0.3,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ];
    let bits = |xs: &[f64]| xs.iter().map(|x| x.to_bits()).collect::<Vec<_>>();
    assert_eq!(bits(&BMC_FLOATS[..8]), bits(&want));
    assert!(BMC_FLOATS[8].is_nan());
    assert_eq!(BMC_FLOATS.len(), 9);
    let values = bmc_floats();
    assert_eq!(values[1], Value::float(-0.0));
    assert_ne!(values[0], values[1]);
    assert_eq!(ENUMERATION_BUDGET, 4_096);
    assert_eq!(RANDOM_INSTANCES, 512);
    // The one-level maps: all 6^4 partial maps of the keys 0..4, then the random ones, within
    // the budget, and every random one over keys and values of `int[-8..=8]`.
    let maps = int_maps(7);
    assert_eq!(maps.len(), 1_296 + 512);
    assert!(maps.len() as u64 <= ENUMERATION_BUDGET);
    for m in &maps[1_296..] {
        assert!(
            m.iter()
                .all(|(k, v)| BMC_INT.contains(k) && BMC_INT.contains(v))
        );
        assert!(m.windows(2).all(|w| w[0].0 < w[1].0));
    }
}

#[test]
fn every_recursion_runs_under_the_wavefront_pull_and_eight_chaotic_orders() {
    // DESIGN.md M0.10: "runs each definedness recursion under the wavefront, memoized pull,
    // and eight seeded chaotic orders".
    let s = schedules();
    assert_eq!(s.len(), 10);
    assert!(matches!(s[0], Schedule::Rounds));
    assert!(matches!(s[1], Schedule::Pull));
    let seeds: std::collections::BTreeSet<u64> = s[2..]
        .iter()
        .map(|x| match x {
            Schedule::Chaotic(seed) => *seed,
            other => panic!("{other:?} is not a chaotic order"),
        })
        .collect();
    assert_eq!(seeds.len(), 8);
}

#[test]
fn shortlex_gives_every_sequence_once_by_length_then_alphabet() {
    // Sequences of length at most 4 over five values: 1 + 5 + 25 + 125 + 625.
    let alphabet = [-2i64, -1, 0, 1, 2];
    let all = shortlex(&alphabet, 4);
    assert_eq!(all.len(), 781);
    let rank = |s: &Vec<i64>| {
        let digits: Vec<usize> = s.iter().map(|x| (x + 2) as usize).collect();
        (s.len(), digits)
    };
    assert!(all.windows(2).all(|w| rank(&w[0]) < rank(&w[1])));
    assert_eq!(all[0], Vec::<i64>::new());
    assert_eq!(all[780], vec![2; 4]);
    // No length, and an empty alphabet: the empty sequence alone.
    assert_eq!(shortlex(&alphabet, 0), vec![Vec::<i64>::new()]);
    assert_eq!(shortlex::<i64>(&[], 3), vec![Vec::<i64>::new()]);
}

#[test]
fn partial_maps_give_each_key_absent_or_bound_once() {
    let maps = partial_maps(&[0, 1, 2], &['a', 'b']);
    assert_eq!(maps.len(), 27);
    let distinct: std::collections::BTreeSet<_> = maps.iter().collect();
    assert_eq!(distinct.len(), 27);
    assert!(maps.iter().all(|m| m.windows(2).all(|w| w[0].0 < w[1].0)));
    assert_eq!(maps[0], vec![]);
    // No keys: the empty map alone; no values: the empty map alone too.
    assert_eq!(partial_maps::<char>(&[], &['a']), vec![vec![]]);
    assert_eq!(partial_maps::<char>(&[0, 1], &[]), vec![vec![]]);
}

#[test]
fn the_random_generator_repeats_from_its_seed_and_stays_in_range() {
    let (mut a, mut b) = (Rng::new(42), Rng::new(42));
    let xs: Vec<u64> = (0..16).map(|_| a.next_u64()).collect();
    let ys: Vec<u64> = (0..16).map(|_| b.next_u64()).collect();
    assert_eq!(xs, ys);
    assert_ne!(Rng::new(43).next_u64(), xs[0]);
    // SplitMix64 from the state 0 (Steele, Lea and Flood 2014).
    assert_eq!(Rng::new(0).next_u64(), 0xe220_a839_7b1d_cdaf);
    let mut r = Rng::new(1);
    let ints: Vec<i64> = (0..2_000).map(|_| r.int(-8, 8)).collect();
    assert!(ints.iter().all(|x| (-8..=8).contains(x)));
    assert!(ints.contains(&-8) && ints.contains(&8));
    // A sequence of at most 4 elements: every length from 0 to 4, elements of the alphabet.
    let mut lens = [0usize; 5];
    for _ in 0..2_000 {
        let s = r.seq(&['x', 'y'], 4);
        lens[s.len()] += 1;
        assert!(s.iter().all(|c| *c == 'x' || *c == 'y'));
    }
    assert!(lens.iter().all(|&n| n > 0), "{lens:?}");
    // A fresh generator is the one its returned seed gives, so the seed repeats the run.
    let (mut fresh, seed) = Rng::fresh("m0_10 cases");
    assert_eq!(fresh.next_u64(), Rng::new(seed).next_u64());
}

#[test]
fn a_property_that_fails_is_reported_with_its_instance_and_reason() {
    let report = std::panic::catch_unwind(|| {
        property(0..5, |i| {
            if *i == 3 {
                Err("three".to_string())
            } else {
                Ok(())
            }
        })
    })
    .expect_err("the harness must report the failure");
    assert_eq!(
        report.downcast_ref::<String>().map(String::as_str),
        Some("the property fails on 3: three")
    );
}

#[test]
fn a_counterexample_that_is_not_found_is_reported() {
    let report = std::panic::catch_unwind(|| property_refuted(0..5, |_| Ok(())))
        .expect_err("the harness must report that no instance refutes the property");
    assert_eq!(
        report.downcast_ref::<&str>().copied(),
        Some("no instance refutes the property")
    );
}
