//! The growth of the exact projection of module `exact` of zedc-presburger
//! (PRES-project-exact-solver; author P197, P219, A99), asked through `project_each_exact`, the
//! cover's entry while the checker asks the solver alone (row PRES-cover-wire). The benchmark
//! of the cover's time per unit of its counted work, which checks `EXACT_LIMIT`, fails on
//! `evens n=400 pad=400` (278 to 335 ns a unit) and stays on branch wt/pugh-xr until row
//! PRES-cover-time-per-unit closes.

use zedc::store::interval::IntervalSet;
use zedc::store::presburger::exact::project_each_exact;
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
