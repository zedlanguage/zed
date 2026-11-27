//! The two-pin reading's time per unit of its counted work (BENCH-two-pin-per-unit), and the
//! scaling checks of `exact` (BENCH-meters-outside-bench), run by `tools/run_tests.sh --bench`.

use super::*;

/// The thread CPU time, in ns, of the whole two-pin reading of `f` (`guarded::prepare`,
/// `Prep::two_pins` and `TwoPins::values` for each of `names`, and the drop of what they made,
/// which the checker pays too), the least of five runs ([`crate::scaling::least_cpu_ns`]), with
/// the units it charged, the same in each run.
fn timed(f: &Formula, names: &[&str]) -> (u128, u64) {
    let syms: Vec<Atom> = names.iter().map(|s| a(s)).collect();
    crate::scaling::least_cpu_ns(5, || read(f, &syms))
}

/// The units of the whole two-pin reading of `f` for each of `syms`, as [`timed`] times it.
fn read(f: &Formula, syms: &[Atom]) -> u64 {
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
    for s in syms {
        let set = two.values(s, &mut work).expect("no refusal");
        assert!(set.is_some(), "{s:?} declined");
        std::hint::black_box(set);
    }
    work.used
}

/// `p` in `0..=n` on the line `7·q == 5·p`, read with two pins `p` and `q` and the name
/// `y == p + 2·q`. The polygon is flat, so each name reads the half-planes whole
/// (`u_values`). Two of them are one equation, which is solved (`on_line`, a unit a half-plane);
/// with [`TWO_PIN_LINE_OFF`] the dark shadow is empty and the values are tried one by one,
/// each charged a unit for each half-plane.
fn line(n: i64) -> Formula {
    Formula::and(vec![
        eq(&[("q", 7), ("p", -5)], 0),
        ge(&[("p", 1)], 0),
        ge(&[("p", -1)], n),
        eq(&[("y", 1), ("p", -1), ("q", -2)], 0),
    ])
}

/// The same line with `p` in `0..=10` and `h` more sides `p + i·q <= 10^6 + i` that no point
/// meets: each name reads `h + 4` half-planes, `3·h² + h` pairs for its shadows.
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
/// 4.7 to 8.1 ns; 15 to 25 ms at the limit. The reading's units then cost far less time than the
/// cover's (26.5 to 27.8 ns a unit, `exact_cover`), so it stopped at its allowance after a tenth
/// of the time the cover takes there, and declined (`sides` past h of about 140).
/// PRES-two-pin-charge-fit fit the charges of the three sites these cases measure to their time
/// (a unit for each 16 pairs of half-planes the shadows of `u_values` meet, a unit a half-plane
/// for each value `u_runs` tries, 4 units a bit for each step of `poly_values`); `line` and
/// `sides` grew to keep 10^5 units. Measured (2026-11-22, VM, one run, before the sides charge
/// went from 4 to 16 pairs a unit): `line n=16000` 137,747 units at 52.3 ns a unit, `sides
/// h=240` 183,115 at 5.6 ns, `strip n=4000` 140,000 at 37.3 ns; at most 162 ms at the limit.
/// Since PERF-cover-union-of-classes-listed the line's equation is solved (`on_line`), a few
/// units a name, so `line` and `sides` run with [`TWO_PIN_LINE_OFF`], which keeps the two
/// sites they measure, and `sides on a line` measures the site that replaces them, a unit a
/// half-plane, at 3·(h + 4) units for its three names; it is O(h), checked at n and 8n below
/// ([`the_two_pin_reading_of_a_line_costs_the_same_at_8n`]).
#[test]
fn the_two_pin_reading_takes_a_bounded_time_per_unit_of_work() {
    let names = ["p", "q", "y"];
    let cases: Vec<(String, Formula, bool)> = vec![
        ("line n=16000".into(), line(16000), true),
        ("sides h=480".into(), sides(480), true),
        ("strip n=4000".into(), strip(4000), false),
        ("sides on a line h=34000".into(), sides(34_000), false),
    ];
    let measured: Vec<(String, u128, u64)> = (cases.into_iter())
        .map(|(name, f, off)| {
            TWO_PIN_LINE_OFF.set(off);
            let (ns, units) = timed(&f, &names);
            TWO_PIN_LINE_OFF.set(false);
            (name, ns, units)
        })
        .collect();
    crate::scaling::per_unit_bound("two pins", &measured, 100_000, EXACT_LIMIT);
}

/// PERF-cover-union-of-classes-listed: a line ([`line`], `7·q == 5·p` with `p` in `0..=n`) and
/// the face a leaf choice's guard cuts out of a square ([`super::face`], `q == n` with `p` in
/// `0..=n`) are read by their equation (`two_pins::on_line`), O(h) a name for h half-planes,
/// so they cost the same at 8n, in units and in instructions. The red control,
/// [`TWO_PIN_LINE_OFF`], is the line's values tried one by one, as before: it grows with n,
/// over the limit of a constant. The face has no red control: before, it was read the narrower
/// way of `two_pins::u_runs`, whose cost did not grow with n either (1656 units at n 2000 and
/// 16000, local run, 2026-11-27); its control is printed only.
#[test]
fn the_two_pin_reading_of_a_line_costs_the_same_at_8n() {
    let syms: Vec<Atom> = ["p", "q", "y"].iter().map(|s| a(s)).collect();
    type Case = (&'static str, fn(i64) -> Formula, bool);
    let cases: [Case; 2] = [("line", line, true), ("face", super::face, false)];
    for (what, f, red_control) in cases {
        let units = |n: i64| read(&f(n), &syms);
        TWO_PIN_LINE_OFF.set(true);
        let (small, large) = (units(2_000), units(16_000));
        TWO_PIN_LINE_OFF.set(false);
        let red = large as f64 / small.max(1) as f64;
        println!("{what}, line off: {small} and {large} units, {red:.2} times at 8n");
        if red_control {
            assert!(
                red > crate::scaling::limit(0),
                "the control must fail the limit: {red:.2}"
            );
        }
        let (small, large) = (units(2_000), units(16_000));
        println!("{what}: {small} and {large} units");
        crate::scaling::hold(
            &format!("two pins on a {what} at n 2000 and 16000"),
            "units",
            small,
            large,
            0,
        );
        crate::scaling::check_order(&format!("two pins on a {what}"), 2_000, 0, |n| {
            std::hint::black_box(units(n as i64));
        });
    }
}

// The scaling checks below were in `exact::tests`, where a correctness piece runs them 8 at a
// time and the meter falls back to processor time (BENCH-meters-outside-bench); here each runs
// alone with `--exact --nocapture` and counts instructions.

/// Q4 complexity: `k` two-point sets `{0, 3i + 1}` each have a distinct congruence class
/// `0 mod (3i + 1)` in `Classed`. Folding classes one by one with `Classed::join` rebuilds the
/// whole union at each step, O(k^2) time and bytes; merging all pieces once is O(k log k).
#[test]
fn classed_join_all_many_distinct_classes_scales() {
    let make = |k: i64| -> Vec<Classed> {
        (1..=k)
            .map(|i| {
                Classed::plain(IntervalSet::from_pieces(vec![
                    (End::of(0), End::of(0)),
                    (End::of(3 * i + 1), End::of(3 * i + 1)),
                ]))
            })
            .collect()
    };
    let check_exact = |k: i64| {
        let got = Classed::join_all(make(k));
        let mut want = vec![(End::of(0), End::of(0))];
        want.extend((1..=k).map(|i| (End::of(3 * i + 1), End::of(3 * i + 1))));
        assert_eq!(got, Classed::plain(IntervalSet::from_pieces(want)));
    };
    check_exact(16);
    crate::scaling::check("classed_join_all_distinct_classes", 64, |k| {
        let inputs = make(k as i64);
        std::hint::black_box(Classed::join_all(inputs));
    });
}

/// Q3(a) & Q3(b): two disjunctions of `m` blocks each, pairwise disjoint on shared atom `y`
/// (`y == 2i && x == y` vs `y == 2j + 1 && x >= y`, empty answer), and a variant with `m`
/// disjoint matching pairs (`y == i && x >= 3i` vs `y == j && x <= 3j + 1`, `m`-piece answer).
/// Without bounding-box interval sweep both cost Theta(m^2); with the 1D sweep both are O(m log m).
#[test]
fn two_disjunctions_disjoint_on_shared_atom_scale_near_linear() {
    let x = a("x");
    let disjoint_empty = |m: i64| {
        let a_or = Formula::or(
            (0..m)
                .map(|i| Formula::and(vec![eq(&[("y", 1)], -2 * i), eq(&[("x", 1), ("y", -1)], 0)]))
                .collect(),
        );
        let b_or = Formula::or(
            (0..m)
                .map(|j| {
                    Formula::and(vec![
                        eq(&[("y", 1)], -(2 * j + 1)),
                        ge(&[("x", 1), ("y", -1)], 0),
                    ])
                })
                .collect(),
        );
        Formula::and(vec![a_or, b_or])
    };
    let matching_partitions = |m: i64| {
        let a_or = Formula::or(
            (0..m)
                .map(|i| Formula::and(vec![eq(&[("y", 1)], -i), ge(&[("x", 1)], -3 * i)]))
                .collect(),
        );
        let b_or = Formula::or(
            (0..m)
                .map(|j| Formula::and(vec![eq(&[("y", 1)], -j), ge(&[("x", -1)], 3 * j + 1)]))
                .collect(),
        );
        Formula::and(vec![a_or, b_or])
    };
    let run_empty = |m: i64| {
        let f = disjoint_empty(m);
        let mut work = Work {
            used: 0,
            limit: u64::MAX,
            solver: SOLVER,
        };
        let got = direct(&f, &x, &IntervalSet::top(), &mut work)
            .unwrap()
            .expect("answered");
        assert!(got.is_empty(), "m={m}: {got:?}");
        work.used
    };
    let run_match = |m: i64| {
        let f = matching_partitions(m);
        let mut work = Work {
            used: 0,
            limit: u64::MAX,
            solver: SOLVER,
        };
        let got = direct(&f, &x, &IntervalSet::top(), &mut work)
            .unwrap()
            .expect("answered");
        let want = IntervalSet::from_pieces(
            (0..m)
                .map(|j| (End::of(3 * j), End::of(3 * j + 1)))
                .collect(),
        );
        assert_eq!(got.met(), want, "m={m}");
        work.used
    };
    let (u16, u128) = (run_empty(16), run_empty(128));
    println!(
        "disjoint_empty work units: m=16 -> {u16}, m=128 -> {u128}, ratio={:.2}x",
        u128 as f64 / u16.max(1) as f64
    );
    crate::scaling::check("two_disj_disjoint_empty", 16, |m| {
        std::hint::black_box(run_empty(m as i64));
    });
    let (m16, m128) = (run_match(16), run_match(128));
    println!(
        "matching_partitions work units: m=16 -> {m16}, m=128 -> {m128}, ratio={:.2}x",
        m128 as f64 / m16.max(1) as f64
    );
    crate::scaling::check("two_disj_matching_partitions", 16, |m| {
        std::hint::black_box(run_match(m as i64));
    });
}

/// Q1 audit: empty blocks (`Formula::top()` inside `Formula::Or(Shared::new(...))`) in two
/// disjunctions must charge at least one unit per block processed/cloned, so `tried`'s allowance
/// cannot be bypassed by O(m^2) empty-block work charged as O(m).
#[test]
fn two_disjunctions_empty_blocks_charge_work_per_block() {
    let x = a("x");
    let make = |m: usize| {
        let mut a_blocks = vec![Formula::and(vec![eq(&[("y", 1)], 0), eq(&[("x", 1)], 0)])];
        a_blocks.extend((1..m).map(|_| Formula::top()));
        let mut b_blocks = vec![Formula::and(vec![eq(&[("y", 1)], 0), eq(&[("x", 1)], 0)])];
        b_blocks.extend((1..m).map(|_| Formula::top()));
        Formula::And(Shared::new(vec![
            Formula::Or(Shared::new(a_blocks)),
            Formula::Or(Shared::new(b_blocks)),
        ]))
    };
    let mut meter = crate::scaling::Meter::new();
    // Counted here and held by the asserts below, not by a check: beside other tests on a machine
    // with no counter of instructions the test runs again alone, in a new process
    // (BENCH-self-counted-meters-processor-time).
    if crate::scaling::ran_alone_in_a_new_process(&meter) {
        return;
    }
    let mut counts = Vec::new();
    for m in [32usize, 256] {
        let f = make(m);
        let mut used = 0u64;
        let w = meter.work(|| {
            let mut work = Work {
                used: 0,
                limit: u64::MAX,
                solver: SOLVER,
            };
            let got = direct(&f, &x, &IntervalSet::top(), &mut work)
                .unwrap()
                .expect("answered");
            assert_eq!(got.met(), IntervalSet::top());
            used = work.used;
        });
        println!(
            "empty_blocks m={m}: work_units={used} instr={} bytes={}",
            w.units, w.bytes
        );
        counts.push((used, w.units, w.bytes));
    }
    let work_ratio = counts[1].0 as f64 / counts[0].0.max(1) as f64;
    let instr_ratio = counts[1].1 as f64 / counts[0].1.max(1) as f64;
    println!("empty_blocks ratios (8x m): work={work_ratio:.2}x instr={instr_ratio:.2}x");
    // A disjunction with an empty block is `true` and is dropped (`two_distributed`), so no
    // pair is formed: instructions within the scaling limit.
    assert!(
        instr_ratio < crate::scaling::LIMIT,
        "empty blocks: {instr_ratio:.2}x instructions per 8x m"
    );
    // If actual instructions grow quadratically (> 20x), counted work must grow comparably, not 8x.
    if instr_ratio > 20.0 {
        assert!(
            work_ratio > 20.0,
            "uncharged quadratic empty blocks: work grew {work_ratio:.2}x while instructions grew {instr_ratio:.2}x"
        );
    }
}

/// `direct` on [`two_over_a_chain`] at m and 8m: its counted work and its instructions grow
/// linearly in m with the smaller disjunction fixed (PRES-cover-moduli-two-disjunctions; the
/// worst case, both disjunctions growing, is quadratic and proved unavoidable at
/// `exact::two_distributed`). Before `two_distributed`, `direct` declined it.
#[test]
fn two_disjunctions_one_of_fixed_size_cost_linear_work() {
    let x = a("x");
    let answer = |m: i64| {
        let f = two_over_a_chain(m);
        let mut work = Work {
            used: 0,
            limit: u64::MAX,
            solver: SOLVER,
        };
        let set = direct(&f, &x, &IntervalSet::top(), &mut work)
            .expect("no refusal")
            .expect("answered");
        (set, work.used)
    };
    let run = |m: i64| {
        let (set, used) = answer(m);
        let want = IntervalSet::from_pieces(
            (0..m)
                .map(|j| (End::of(3 * j), End::of(3 * j + 1)))
                .collect(),
        );
        assert_eq!(set.met(), want, "m {m}");
        used
    };
    TWO_DISTRIBUTED_OFF.set(true);
    let mut work = Work {
        used: 0,
        limit: u64::MAX,
        solver: SOLVER,
    };
    let before = direct(&two_over_a_chain(8), &x, &IntervalSet::top(), &mut work);
    TWO_DISTRIBUTED_OFF.set(false);
    assert!(matches!(before, Ok(None)), "{before:?}");
    crate::scaling::hold(
        "two_distributed at m 64 and 512",
        "units",
        run(64),
        run(512),
        1,
    );
    crate::scaling::check("two_distributed", 64, |m| {
        std::hint::black_box(answer(m as i64));
    });
}

/// Two disjunctions of n disjoint ranges each (`6j..=6j+1` and `6j+3..=6j+4`) of `y == x`:
/// the answer is empty, and the work grows near-linearly in n, where distributing them formed
/// all n² pairs (59.5 times the instructions per eightfold n, 16 to 128, codex seat, round 1).
#[test]
fn disjoint_shared_intervals_scale_without_forming_pairs() {
    let run = |n: usize| {
        let n = n as i64;
        let f = Formula::and(vec![
            eq(&[("x", 1), ("y", -1)], 0),
            interval_disjunction((0..n).map(|j| (6 * j, 6 * j + 1))),
            interval_disjunction((0..n).map(|j| (6 * j + 3, 6 * j + 4))),
        ]);
        let mut w = Work {
            used: 0,
            limit: u64::MAX,
            solver: SOLVER,
        };
        let got = direct(&f, &a("x"), &IntervalSet::top(), &mut w).expect("no refusal");
        assert!(got.expect("answered").is_empty());
        w.used
    };
    println!("disjoint intervals: work {} / {}", run(16), run(128));
    crate::scaling::check("disjoint shared intervals", 16, |n| {
        std::hint::black_box(run(n));
    });
}

/// [`Classed::join_all`] of n sets, each of its own class, gives the set the pairwise fold of
/// [`Classed::join`] gives, in either order, and grows near-linearly in n (the fold listed
/// the union so far at each join: 47 times the instructions per eightfold n, 64 to 512).
#[test]
fn joining_many_distinct_classes_scales_and_preserves_the_union() {
    let inputs = |n: usize| {
        (0..n as i64).map(move |i| {
            let lo = 4 * n as i64 * i;
            let step = i + 2;
            Classed::new(
                IntervalSet::of(lo, lo + step),
                Congruence::new(Num::from(step), Num::from(lo)),
            )
        })
    };
    let sets: Vec<_> = inputs(20).collect();
    let old = sets
        .iter()
        .fold(Classed::plain(IntervalSet::empty()), |acc, p| acc.join(p));
    let actual = Classed::join_all(sets.iter().cloned());
    assert_eq!(actual.count(), 40);
    assert_eq!(actual, old);
    assert_eq!(Classed::join_all(sets.into_iter().rev()), old);
    crate::scaling::check("joining distinct classes", 64, |n| {
        std::hint::black_box(Classed::join_all(inputs(n)));
    });
}

/// A union whose class is that of a long run (step 2 to 32 000) costs a fixed multiple of the
/// union of the run alone when a set of another class (step 4) and a single value come with it,
/// not one listing of its 16 000 values; the answers are checked by
/// `joining_classes_keeps_the_run_at_the_union_stride` (BENCH-meters-outside-bench).
#[test]
fn joining_classes_keeps_the_run_cheap() {
    crate::scaling::compare_costs(
        "the union stride keeps its long run",
        "a constant number of ranges should be combined without listing the long run",
        crate::scaling::LIMIT,
        || {
            std::hint::black_box(direct_stride_union(32_000));
        },
        || {
            std::hint::black_box(mixed_stride_union(32_000));
        },
    );
}

/// [`super::classed_bounds::evens`] with `n` more atoms, each in `0..=1`: `2n + 3`
/// constraints, so the class of `s`'s cell, `n + 1` values, fits in the room of `size`.
fn evens_padded(n: i64) -> Formula {
    let names: Vec<String> = (0..n).map(|j| format!("y{j}")).collect();
    let mut rows = vec![super::classed_bounds::evens(n)];
    for y in &names {
        rows.push(ge(&[(y.as_str(), 1)], 0));
        rows.push(ge(&[(y.as_str(), -1)], 1));
    }
    Formula::and(rows)
}

/// Fix A of VERIFY-classed-charge-refusals: the class [`shared_cells`] lists for `s` holds
/// `n + 1` values within a part of `2n + 3` constraints, so the listing is O(size) and the
/// step's units grow near 8 times at 8n. Each run checks the listing happened: the gap left
/// is the odd values, and its question finds no point.
#[test]
fn a_shared_cells_listed_class_grows_with_the_part() {
    let run = |n: i64| {
        let f = evens_padded(n);
        let (points, _, used) =
            super::classed_bounds::shared_for_s(&f, IntervalSet::of(0, 2 * n), constraints(&f));
        assert_eq!(points, 1, "n {n}: the class was listed");
        used
    };
    crate::scaling::hold(
        "listed class at n 64 and 512",
        "units",
        run(64),
        run(512),
        1,
    );
    crate::scaling::check("listed class", 64, |n| {
        std::hint::black_box(run(n as i64));
    });
}

/// Fix A's room: a class of `n + 1` values in a part of 3 constraints is dropped, so the step
/// costs the same at 8n. The red control, [`CLASS_ROOM_OFF`] (every class listed, the first
/// cut of PERF-exact-strided-unlisted), grows with the class: over the limit of a constant.
#[test]
fn a_shared_cells_class_past_size_costs_the_same_at_8n() {
    let run = |n: i64| {
        let f = super::classed_bounds::evens(n);
        let (points, _, used) =
            super::classed_bounds::shared_for_s(&f, IntervalSet::of(0, 2 * n), constraints(&f));
        (points, used)
    };
    CLASS_ROOM_OFF.set(true);
    let (small, large) = (run(64), run(512));
    CLASS_ROOM_OFF.set(false);
    let red = large.1 as f64 / small.1.max(1) as f64;
    println!("room off: {small:?} and {large:?}, {red:.2} times at 8n");
    assert!(
        red > crate::scaling::limit(0),
        "the control must fail the limit: {red:.2}"
    );
    let (small, large) = (run(64), run(512));
    assert_eq!(
        (small.0, large.0),
        (2, 2),
        "dropped: a point in the gap found"
    );
    crate::scaling::hold(
        "class past size at n 64 and 512",
        "units",
        small.1,
        large.1,
        0,
    );
    crate::scaling::check_order("class past size", 64, 0, |n| {
        std::hint::black_box(run(n as i64));
    });
}

/// The cover of `s == m·t`, `0 <= t <= 4`, in `[0, 4m]`: its gap is the `m - 1` classes
/// `1..m mod m`, which `outside` drops, `ClassUnion::minus` of those classes from themselves.
/// Linear in m: before, every class left was cut by each class taken, (m - 1)^2 cuts, 6,893
/// units at m = 16 and 140,513 at m = 128 (20.4 times, the red run of this row).
#[test]
fn a_gap_of_classes_less_its_classes_is_linear_in_them() {
    let run = |m: i64| {
        let f = super::classed_bounds::multiples(m, 4);
        let (_, used, _) = super::classed_bounds::cover_s(&f, &IntervalSet::of(0, 4 * m));
        used
    };
    crate::scaling::hold(
        "gap of classes at m 16 and 128",
        "units",
        run(16),
        run(128),
        1,
    );
    crate::scaling::check("gap of classes", 16, |m| {
        std::hint::black_box(run(m as i64));
    });
}

/// Gap G closed (row LIMITS-exact-join-remove, `cells_cover`): the cover of `s` over
/// `(s >= 0 ∧ s == 2·y) ∨ (40 <= s <= 40 + 4·n ∧ s == 4·z)`, `h` = [-10, +inf), with the points
/// `s = 0` and `s = 40` read first, so the piece [0, +inf) is kept with the even residues (held
/// exactly by a tail past 0, row CLASSED-periodic-tail) and
/// the stride of step 4 over [40, 40 + 4·n] meets it. Its work, instructions and bytes at n and
/// 8n grow at most linearly (the stride's values listed, O(n); `kept_residues` reads one piece
/// of one marked residue, O(1)): within 10.5, the goal 9. Negative control: on the code before
/// the fix (946c0c265), the cover is refused at n = 64 with `Questions` after 3,112,608 units
/// (each question of the stride finds a point inside the kept piece, until the limit), so the
/// `expect` below fails there and the run stops before 8n.
#[test]
fn a_stride_meeting_a_kept_piece_scales_linearly() {
    let s = a("s");
    let make = |n: i64| {
        Formula::or(vec![
            Formula::and(vec![ge(&[("s", 1)], 0), eq(&[("s", 1), ("y", -2)], 0)]),
            Formula::and(vec![
                ge(&[("s", 1)], -40),
                ge(&[("s", -1)], 40 + 4 * n),
                eq(&[("s", 1), ("z", -4)], 0),
            ]),
        ])
    };
    let point = |s: i64, y: i64, z: i64| -> Model {
        [(a("s"), s), (a("y"), y), (a("z"), z)]
            .into_iter()
            .map(|(k, v)| (k, Int::from(v)))
            .collect()
    };
    let h = IntervalSet::range(fin(&Int::from(-10)), End::PosInf);
    let mut meter = crate::scaling::Meter::new();
    // As in `two_disjunctions_empty_blocks_charge_work_per_block`.
    if crate::scaling::ran_alone_in_a_new_process(&meter) {
        return;
    }
    let mut counts = Vec::new();
    for n in [64i64, 512] {
        let f = make(n);
        let mut used = 0u64;
        let w = meter.work(|| {
            let mut points = vec![point(0, 0, 0), point(40, 0, 10)];
            let mut work = Work {
                used: 0,
                limit: EXACT_LIMIT,
                solver: SOLVER,
            };
            let got = cells_cover(
                &f,
                &s,
                &h,
                constraints(&f),
                &HashSet::new(),
                &mut points,
                &mut PartCache::default(),
                &mut work,
            );
            let (set, cause) = got.expect("the cover ends");
            let want = IntervalSet::range(fin(&Int::from(0)), End::PosInf);
            let tail = zedc_lattice::classed::Tail::new(End::of(0), &[true, false]);
            assert_eq!(set, Classed::tailed(Classed::plain(want), None, Some(tail)));
            assert!(cause, "a kept piece gives the cause");
            used = work.used;
        });
        println!(
            "kept_stride n={n}: work_units={used} instr={} bytes={}",
            w.units, w.bytes
        );
        counts.push((used, w.units, w.bytes));
    }
    let ratio = |i: usize, c: &[(u64, u64, u64)]| {
        let pick = |t: &(u64, u64, u64)| [t.0, t.1, t.2][i];
        pick(&c[1]) as f64 / pick(&c[0]).max(1) as f64
    };
    let (work, instr, bytes) = (ratio(0, &counts), ratio(1, &counts), ratio(2, &counts));
    println!("kept_stride ratios (8x n): work={work:.2}x instr={instr:.2}x bytes={bytes:.2}x");
    let limit = crate::scaling::LIMIT;
    assert!(work < limit, "work {work:.2}x per 8x n");
    assert!(instr < limit, "{instr:.2}x instructions per 8x n");
    assert!(bytes < limit, "{bytes:.2}x bytes per 8x n");
}

/// The exact meet, union and difference of two sets with tails (zedc-lattice `classed::tails`,
/// row CLASSED-periodic-tail) cost linear time in the answer's table: the multiples of `p` from
/// 0 and the multiples of `q = p + 1` from 0, coprime, so each answer's table has `p·q` letters
/// at its least period (`p = round(√n)`, so about n, and 7.99 times at 8n for n = 100 000). Each
/// run checks each answer's step and a few members, O(1) each.
#[test]
fn tailed_operations_scale_with_the_table() {
    use zedc_lattice::classed::Tail;
    let multiples = |p: usize| {
        let mut table = vec![false; p];
        table[0] = true;
        let wider = Classed::plain(IntervalSet::range(End::of(0), End::PosInf));
        Classed::tailed(wider, None, Some(Tail::new(End::of(0), &table)))
    };
    let make = |n: usize| {
        let p = (n as f64).sqrt().round() as usize;
        (p as i64, multiples(p), multiples(p + 1))
    };
    crate::scaling::check_inputs("tailed_operations", 100_000, make, |(p, a, b)| {
        let (p, q) = (*p, p + 1);
        let (meet, join, minus) = (a.meet(b), a.join(b), a.minus(b));
        for set in [&meet, &join, &minus] {
            let tails = set.tails.as_deref().expect("an answer with a tail");
            let above = tails.above.as_ref().expect("a tail above");
            assert_eq!(above.step, Num::from(p * q));
        }
        assert!(meet.contains(p * q) && meet.contains(0) && !meet.contains(p));
        assert!(join.contains(p) && join.contains(q) && !join.contains(1) && !join.contains(-p));
        assert!(minus.contains(p) && !minus.contains(q) && !minus.contains(p * q));
    });
}
