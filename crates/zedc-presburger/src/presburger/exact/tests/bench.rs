//! The two-pin reading's time per unit of its counted work (BENCH-two-pin-per-unit), and the
//! scaling checks of `exact` (BENCH-meters-outside-bench), run by `tools/run_tests.sh --bench`.

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
/// charged a unit for each half-plane.
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
#[test]
fn the_two_pin_reading_takes_a_bounded_time_per_unit_of_work() {
    let names = ["p", "q", "y"];
    let cases: Vec<(String, Formula)> = vec![
        ("line n=16000".into(), line(16000)),
        ("sides h=480".into(), sides(480)),
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
        instr_ratio < 10.5,
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
        10.5,
        || {
            std::hint::black_box(direct_stride_union(32_000));
        },
        || {
            std::hint::black_box(mixed_stride_union(32_000));
        },
    );
}

/// Gap G closed (row LIMITS-exact-join-remove, `cells_cover`): the cover of `s` over
/// `(s >= 0 ∧ s == 2·y) ∨ (40 <= s <= 40 + 4·n ∧ s == 4·z)`, `h` = [-10, +inf), with the points
/// `s = 0` and `s = 40` read first, so the piece [0, +inf) is kept with the even residues and
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
            assert_eq!(set, Classed::plain(want));
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
    assert!(work < 10.5, "work {work:.2}x per 8x n");
    assert!(instr < 10.5, "{instr:.2}x instructions per 8x n");
    assert!(bytes < 10.5, "{bytes:.2}x bytes per 8x n");
}
