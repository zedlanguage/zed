//! The measurements behind the work limit of the exact projection (module `exact` of
//! zedc-presburger, PRES-project-exact-solver; author P197, P219, A99): the cover's time per
//! unit of its counted work, which sets `EXACT_LIMIT`.

use std::time::Instant;

use zedc::store::presburger::exact::{EXACT_LIMIT, EXACT_QUESTIONS, EXACT_WORK};
use zedc::store::presburger::{Atom, Con, Formula, Lin, member, project_each};
use zedc::store::interval::IntervalSet;

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

/// The least time of three projections of `f` onto `x`, with the cover's units and questions.
fn timed(f: &Formula) -> (u128, u64, u64) {
    let mut best = u128::MAX;
    let (mut units, mut questions) = (0, 0);
    for _ in 0..3 {
        EXACT_WORK.set(0);
        EXACT_QUESTIONS.set(0);
        let t = Instant::now();
        let r = std::hint::black_box(project_each(f, &[a("x")]));
        best = best.min(t.elapsed().as_nanos());
        assert!(matches!(&r, Ok((e, _)) if e[0].is_ok()), "{r:?}");
        units = EXACT_WORK.get();
        questions = EXACT_QUESTIONS.get();
    }
    (best, units, questions)
}

/// The cover's time per unit, each case at some 10^5 units or more so that the fixed costs
/// do not count. The worst, times `EXACT_LIMIT`, is the most time a cover stopped at the limit
/// takes; it is checked against twice A99's 250 ms, the factor for the load of the test
/// machine. Measured: see `EXACT_LIMIT`.
#[test]
fn the_cover_takes_a_bounded_time_per_unit_of_work() {
    let cases: Vec<(&str, Formula)> = vec![
        ("evens n=4000", multiples(&[2], 4000, 0)),
        ("2, 3 n=3000", multiples(&[2, 3], 3000, 0)),
        ("2, 3, 5, 7 n=1000", multiples(&[2, 3, 5, 7], 1000, 0)),
        ("evens n=1000 pad=50", multiples(&[2], 1000, 50)),
        ("evens n=400 pad=400", multiples(&[2], 400, 400)),
    ];
    let mut worst = 0f64;
    for (name, f) in &cases {
        let (ns, units, questions) = timed(f);
        let per = ns as f64 / units as f64;
        worst = worst.max(per);
        eprintln!(
            "exact cover: {name}: {units} units, {questions} questions in {ns} ns, {per:.1} ns \
             per unit, {:.0} ns per question",
            ns as f64 / questions as f64
        );
    }
    let most = worst * EXACT_LIMIT as f64 / 1e6;
    eprintln!("exact cover: worst {worst:.1} ns per unit; the limit takes at most {most:.0} ms");
    assert!(most <= 500.0, "{most:.0} ms at the limit");
}
