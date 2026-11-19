//! The growth of the exact projection of module `exact` of zedc-presburger
//! (PRES-project-exact-solver; author P197, P219, A99), asked through `project_each_exact`, the
//! cover's entry while the checker asks the solver alone (row PRES-cover-wire), and the
//! cover's time per unit of its counted work, which checks `EXACT_LIMIT`
//! (PRES-cover-time-per-unit).

use zedc::store::interval::IntervalSet;
use zedc::store::presburger::project_each_exact;
use zedc::store::presburger::{Atom, Con, Formula, Lin, member};

fn a(s: &str) -> Atom {
    Atom::Sym(s.into())
}

fn l(s: &str) -> Lin {
    Lin::atom(a(s))
}

/// `x == c * v` for the atom `v`.
fn multiple(c: i64, v: &str) -> Formula {
    Formula::Con(Con::eq(&l("x"), &l(v).times(c)))
}

/// The multiples of each of `cs` in `0..=n` as values of `x`: `x == c * v_c` for some `c`,
/// each `v_c` in `0..=n`, and `pad` more conjuncts over atoms of their own, a chain
/// `w_i <= w_{i+1}` in `0..=1`, that make each question longer. The answer has a piece for each
/// run of multiples, and the cover asks about each gap between them.
fn multiples(cs: &[i64], n: i64, pad: usize) -> Formula {
    let mut all = vec![
        Formula::or(cs.iter().map(|c| multiple(*c, &format!("v{c}"))).collect()),
        member(&a("x"), &IntervalSet::of(0, n)),
    ];
    for c in cs {
        all.push(member(&a(&format!("v{c}")), &IntervalSet::of(0, n)));
    }
    for i in 0..pad {
        let w = format!("w{i}");
        all.push(member(&a(&w), &IntervalSet::of(0, 1)));
        if i > 0 {
            all.push(Formula::Con(Con::ge(&l(&w), &l(&format!("w{}", i - 1)))));
        }
    }
    Formula::and(all)
}

/// The least thread CPU time, in ns, of five projections of `f` onto `x` with the cover
/// (`project_each_exact`) and of five by the solver alone (`project_each_solver`), with the
/// cover's units and questions.
fn timed(f: &Formula) -> (u128, u128, u64, u64) {
    use zed_tests::scaling::cpu_time;
    use zedc::store::presburger::exact::{EXACT_QUESTIONS, EXACT_WORK};
    use zedc::store::presburger::project_each_solver;
    let least = |run: &dyn Fn()| {
        (0..5)
            .map(|_| {
                let t = cpu_time();
                run();
                (cpu_time() - t).as_nanos()
            })
            .min()
            .expect("five runs")
    };
    // The counters of the last run, the same in each: the cover's work is a count.
    let with = least(&|| {
        EXACT_WORK.set(0);
        EXACT_QUESTIONS.set(0);
        let r = std::hint::black_box(project_each_exact(f, &[a("x")]));
        assert!(matches!(&r, Ok((e, _)) if e[0].is_ok()), "{r:?}");
    });
    let (units, questions) = (EXACT_WORK.get(), EXACT_QUESTIONS.get());
    let alone = least(&|| {
        std::hint::black_box(project_each_solver(f, &[a("x")])).ok();
    });
    (with, alone, units, questions)
}

/// The cover's time per unit, each case at some 10^5 units or more so that the fixed costs
/// do not count. The worst, times `EXACT_LIMIT`, is the most time a cover stopped at the limit
/// takes; it is checked against twice A99's 250 ms, the factor for the load of the test
/// machine. Measured: see `EXACT_LIMIT`.
///
/// The time of a cover is the thread CPU time a projection takes with the cover less the time
/// the solver alone takes on the same formula, since the limit bounds what the cover adds: the
/// solver's own run is the checker's without the cover and is not charged to the cover's
/// meter. Before (PRES-cover-time-per-unit), the whole projection was timed by the wall clock,
/// and `evens n=400 pad=400` gave 278 to 335 ns a unit, read then as its questions charged too
/// little for their length; but its padding chain shares no atom with `x`, so `exact::split`
/// leaves it out of every question (one question, of 2 rows), and the solver alone took 30 to
/// 43 ms of its 42 to 109 ms (load 60 to 77, 2026-11-17), the cover's share about 58 ns a
/// unit. A fixed cost outside the cover, divided by 137,785 units and multiplied by
/// `EXACT_LIMIT`, counted 22 times over.
///
/// Each case is checked to reach the cover (a question or more) and to count 10^5 units or
/// more (BENCH-cover-per-unit-few-units). The cases once had the evens written as one multiple,
/// `x == 2 * v2`; since the two-pin reading (zed-impl cd403f3b0, `guarded::two_pins`) a part
/// with no choice is read off its polygon with no question, and `evens n=4000` counted 1,056 to
/// 1,312 units, so the fixed costs of the projection, some 0.3 ms, gave 290 to 515 ns a unit and
/// 900 ms or more at the limit. The evens are now `x == 2 * v2 or x == 4 * v4`, the same set
/// through a choice, which the two-pin reading declines; `n=2000 pad=50` replaces `n=1000
/// pad=50`, which counted 63,332 units with one multiple and 102,959 with the choice.
///
/// Since PRES-one-block-changes-goal (2026-11-19) `exact::block_set` keeps a stride as its range
/// met with its class, so `direct` answers the choice of two multiples with no question
/// (`2, 4 n=4000`: 107,684 units, 0 questions). The cases are timed with `direct` off
/// (`DIRECT_OFF`), so that the cells and questions are what is timed whatever `direct` comes to
/// answer: 122,220 to 1,427,169 units and 1 to 1,001 questions a case, worst 67.9 ns a unit,
/// 211 ms at the limit (load 67).
#[test]
fn the_cover_takes_a_bounded_time_per_unit_of_work() {
    use zedc::store::presburger::exact::{DIRECT_OFF, EXACT_LIMIT};
    let cases: Vec<(&str, Formula)> = vec![
        ("2, 4 n=4000", multiples(&[2, 4], 4000, 0)),
        ("2, 3 n=3000", multiples(&[2, 3], 3000, 0)),
        ("2, 3, 5, 7 n=1000", multiples(&[2, 3, 5, 7], 1000, 0)),
        ("2, 4 n=2000 pad=50", multiples(&[2, 4], 2000, 50)),
        ("2, 4 n=400 pad=400", multiples(&[2, 4], 400, 400)),
    ];
    // The cells and questions are what is timed, so `direct` is not tried first.
    DIRECT_OFF.set(true);
    let mut worst = 0f64;
    for (name, f) in &cases {
        let (with, alone, units, questions) = timed(f);
        assert!(
            units >= 100_000 && questions >= 1,
            "exact cover: {name}: {units} units, {questions} questions; the case must reach the \
             cover and count 10^5 units or more, or its time is the fixed costs"
        );
        let ns = with.saturating_sub(alone);
        let per = ns as f64 / units as f64;
        worst = worst.max(per);
        eprintln!(
            "exact cover: {name}: {units} units, {questions} questions in {ns} ns of CPU time \
             ({with} ns with the cover, {alone} ns alone), {per:.1} ns per unit, {:.0} ns per \
             question",
            ns as f64 / questions as f64
        );
    }
    DIRECT_OFF.set(false);
    let most = worst * EXACT_LIMIT as f64 / 1e6;
    eprintln!("exact cover: worst {worst:.1} ns per unit; the limit takes at most {most:.0} ms");
    assert!(most <= 500.0, "{most:.0} ms at the limit");
}

/// The cover's work at sizes n and 8n (PRES-pugh-exact-projection-research): the multiples of
/// 2 in `0..=n`, whose answer has n/2 + 1 pieces and a question for each gap, and the evens
/// in `0..=20` with a padding chain of n conjuncts, which makes each question n long while
/// their number stays the same. Each is of order n. The in-cell method is Pugh's
/// (`METHOD` unset; its environment switch was removed in PRES-pugh-xr round 3).
#[test]
fn the_cover_is_of_order_n_in_its_answer_and_in_its_questions() {
    use zed_tests::scaling;
    let evens = scaling::inputs(250, |n| multiples(&[2], n as i64, 0));
    scaling::check_order("exact cover: evens in 0..=n", 250, 1, |n| {
        let r = std::hint::black_box(project_each_exact(&evens[&n], &[a("x")]));
        assert!(matches!(&r, Ok((e, _)) if e[0].is_ok()), "{r:?}");
    });
    let padded = scaling::inputs(25, |n| multiples(&[2], 20, n));
    scaling::check_order("exact cover: evens with n padding conjuncts", 25, 1, |n| {
        let r = std::hint::black_box(project_each_exact(&padded[&n], &[a("x")]));
        assert!(matches!(&r, Ok((e, _)) if e[0].is_ok()), "{r:?}");
    });
}

/// The answer for a set with holes without end (PRES-cover-tail-writing, `exact::ended`): the
/// even integers and the `n + 1` odd values `4z + 1`, z in `0..=n`, agree with their period, the
/// evens, below 0 and above `4n + 1`, so the answer is `(-inf, 0]`, the set exactly between, and
/// `[4n + 2, +inf)`, with the cause `Repeats`. The walks of `ended` pass the pieces of the set
/// between and list the values of the tails kept there: of order n.
#[test]
fn the_answer_for_holes_without_end_is_of_order_n_in_its_exceptions() {
    use zed_tests::scaling;
    use zedc::store::interval::End;
    use zedc::store::presburger::Refusal;
    let make = |n: usize| {
        let n = n as i64;
        Formula::or(vec![
            Formula::Con(Con::eq(&l("x"), &l("y").times(2))),
            Formula::and(vec![
                Formula::Con(Con::eq(&l("x"), &l("z").times(4).plus(&Lin::constant(1)))),
                member(&a("z"), &IntervalSet::of(0, n)),
            ]),
        ])
    };
    let want = |n: i64| {
        let mut pieces = vec![(End::NegInf, End::of(0))];
        pieces.extend(
            (1..=4 * n + 1)
                .filter(|v| v % 2 == 0 || v % 4 == 1)
                .map(|v| (End::of(v), End::of(v))),
        );
        pieces.push((End::of(4 * n + 2), End::PosInf));
        IntervalSet::from_pieces(pieces)
    };
    let small = project_each_exact(&make(4), &[a("x")]);
    assert_eq!(small, Ok((vec![Ok(want(4))], vec![Refusal::Repeats])));
    let inputs = scaling::inputs(400, make);
    scaling::check_order("exact cover: evens and n odd exceptions", 400, 1, |n| {
        let r = std::hint::black_box(project_each_exact(&inputs[&n], &[a("x")]));
        assert_eq!(r, Ok((vec![Ok(want(n as i64))], vec![Refusal::Repeats])));
    });
}
