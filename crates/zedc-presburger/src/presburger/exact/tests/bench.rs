//! The two-pin reading's time per unit of its counted work (BENCH-two-pin-per-unit), run by
//! `tools/run_tests.sh --bench`.

use super::*;

/// The thread CPU time, in ns, of the whole two-pin reading of `f` (`guarded::prepare`,
/// `Prep::two_pins` and `TwoPins::values` for each of `names`, and the drop of what they made,
/// which the checker pays too), the least of five runs ([`crate::scaling::least_cpu_ns`]), with
/// the units it charged, the same in each run.
fn timed(f: &Formula, names: &[&str]) -> (u128, u64) {
    let syms: Vec<Atom> = names.iter().map(|s| a(s)).collect();
    crate::scaling::least_cpu_ns(5, || {
        let mut work = Work {
            used: 0,
            limit: u64::MAX,
            solver: SOLVER,
        };
        let prep = guarded::prepare(f, &mut work)
            .expect("no refusal")
            .expect("prepared");
        let two = prep
            .two_pins(syms.len(), &mut work)
            .expect("no refusal")
            .expect("the part is read with two pins");
        for s in &syms {
            let set = two.values(s, &mut work).expect("no refusal");
            assert!(set.is_some(), "{s:?} declined");
            std::hint::black_box(set);
        }
        work.used
    })
}

/// `p` in `0..=n` on the line `7·q == 5·p`, read with two pins `p` and `q` and the name
/// `y == p + 2·q`. The polygon is flat, so each name reads the half-planes whole
/// (`u_values`), and its dark shadow is empty: the values are tried one by one, each
/// charged a piece for each half-plane.
fn line(n: i64) -> Formula {
    Formula::and(vec![
        eq(&[("q", 7), ("p", -5)], 0),
        ge(&[("p", 1)], 0),
        ge(&[("p", -1)], n),
        eq(&[("y", 1), ("p", -1), ("q", -2)], 0),
    ])
}

/// The same line with `p` in `0..=10` and `h` more sides `p + i·q <= 10^6 + i` that no point
/// meets: each name reads `h + 4` half-planes, `3·h² + h` pieces for its shadows.
fn sides(h: i64) -> Formula {
    let mut all = vec![
        eq(&[("q", 7), ("p", -5)], 0),
        ge(&[("p", 1)], 0),
        ge(&[("p", -1)], 10),
        eq(&[("y", 1), ("p", -1), ("q", -2)], 0),
    ];
    for i in 1..=h {
        all.push(ge(&[("p", -1), ("q", -i)], 1_000_000 + i));
    }
    Formula::and(all)
}

/// A strip `0 <= 7·q - 5·p <= 3` with `p` in `0..=n`, bounded with interior: each name is
/// read off the polygon's edges (`poly_values`).
fn strip(n: i64) -> Formula {
    Formula::and(vec![
        ge(&[("q", 7), ("p", -5)], 0),
        ge(&[("q", -7), ("p", 5)], 3),
        ge(&[("p", 1)], 0),
        ge(&[("p", -1)], n),
        eq(&[("y", 1), ("p", -1), ("q", -2)], 0),
    ])
}

/// The reading's time per unit, each case at 10^5 units or more so that the fixed costs do not
/// count. The worst, times `EXACT_LIMIT` (the reading's own allowance, `exact::tried`), is the
/// most time a reading stopped there takes; it is checked against
/// [`crate::scaling::AT_THE_LIMIT_MS`], twice A99's 250 ms for the load of the test machine
/// ([`crate::scaling::per_unit_bound`]), as the cover's own test is
/// (`l01_38_omega_test::bench::exact_cover`). The reading asks no question of the solver, so
/// its time is measured whole, with nothing subtracted.
///
/// Measured (2026-11-19, four runs at load5 27 to 36 on 32 cores): `line n=4000` 551,792 units
/// at 1.3 to 2.5 ns a unit, `sides h=60` 627,888 at 0.1 to 0.3 ns, `strip n=4000` 558,464 at
/// 4.7 to 8.1 ns; 15 to 25 ms at the limit. The reading's units cost far less time than the cover's (26.5 to 27.8 ns a unit,
/// `exact_cover`), so it stops at its allowance well before 250 ms; it is charged more than its
/// time, not less (the shadows of `u_values` at 16 units a pair of half-planes, a few ns each).
#[test]
fn the_two_pin_reading_takes_a_bounded_time_per_unit_of_work() {
    let names = ["p", "q", "y"];
    let cases: Vec<(String, Formula)> = vec![
        ("line n=4000".into(), line(4000)),
        ("sides h=60".into(), sides(60)),
        ("strip n=4000".into(), strip(4000)),
    ];
    let measured: Vec<(String, u128, u64)> = (cases.into_iter())
        .map(|(name, f)| {
            let (ns, units) = timed(&f, &names);
            (name, ns, units)
        })
        .collect();
    crate::scaling::per_unit_bound("two pins", &measured, 100_000, EXACT_LIMIT);
}
