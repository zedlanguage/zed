//! The greedy walk over disjoint unit rows (`try_pick_disjoint_wide`), called directly on parts
//! built by hand and checked against enumeration (row TEST-presburger-unreached-paths).
//!
//! Called directly because no test reaches these branches through `decide`, `satisfiable` or
//! `project_each` (llvm-cov, 2026-11-14): a disjunction of one point, a fixed name, a row with no
//! disjunction, and an arm met at once on a row of unbounded names. The passes before the walk
//! join a disjunction they leave with one disjunct into the conjunction and put fixed names in
//! for their values, which removes most such shapes; that none can reach the walk is not shown.

use super::*;

fn y(s: &str) -> Lin {
    Lin::atom(Atom::Sym(s.into()))
}

fn k(v: i128) -> Lin {
    Lin::constant(v)
}

fn is(a: &str, v: i128) -> Con {
    Con::eq(&y(a), &k(v))
}

fn sum_is(names: &[&str], v: i128) -> Con {
    let s = names.iter().fold(k(0), |s, n| s.plus(&y(n)));
    Con::eq(&s, &k(v))
}

fn within(a: &str, hi: i128) -> [Con; 2] {
    [Con::ge(&y(a), &k(0)), Con::ge(&k(hi), &y(a))]
}

/// One disjunct per value, each `a == v`.
fn points(a: &str, vs: &[i128]) -> Vec<Rc<Parts>> {
    vs.iter()
        .map(|&v| {
            let mut d = Parts::default();
            d.cons.push(is(a, v));
            Rc::new(d)
        })
        .collect()
}

/// Whether `p` holds at `m`, with each disjunction met by one of its disjuncts.
fn holds(p: &Parts, m: &Model) -> bool {
    p.cons.iter().all(|c| c.holds_linear(m))
        && p.ors
            .iter()
            .all(|o| o.iter().any(|d| d.cons.iter().all(|c| c.holds_linear(m))))
}

/// Whether `p` has a point with each of `names` in `-1..=9`.
fn has_point(p: &Parts, names: &[&str]) -> bool {
    let n = names.len() as u32;
    (0..11u64.pow(n)).any(|mut code| {
        let mut m = Model::new();
        for a in names {
            m.insert(Atom::Sym((*a).into()), Int::from((code % 11) as i128 - 1));
            code /= 11;
        }
        holds(p, &m)
    })
}

/// What the walk answers, with `deep` off and on: `Some(true)` a point (which must hold, and
/// whose disjuncts must be those of `p`), `Some(false)` a refusal, `None` not taken. The walk
/// is greedy, as `pick_by` is, so a refusal does not mean there is no point: each test says
/// which, by enumeration.
fn walk(p: &Parts) -> Option<bool> {
    let mut seen = Vec::new();
    for deep in [false, true] {
        seen.push(match try_pick_disjoint_wide(p, deep) {
            None => None,
            Some(Err(_)) => Some(false),
            Some(Ok((m, took))) => {
                assert!(holds(p, &m), "the point {m:?} fails");
                assert_eq!(took.len(), p.ors.len());
                for (j, d) in took.iter().rev().enumerate() {
                    assert!(p.ors[j].iter().any(|e| std::ptr::eq(&**e, *d)));
                    assert!(d.cons.iter().all(|c| c.holds_linear(&m)));
                }
                Some(true)
            }
        });
    }
    assert_eq!(seen[0], seen[1], "deep changes the answer");
    seen[0]
}

#[test]
fn a_disjunction_of_one_point_on_a_row_of_unbounded_names() {
    // The walk reads the disjunctions last to first. `c` is the greatest name and holds the
    // rest of the row, so `a` is 0 and meets `a == 0` at once; `c == 4` is a disjunction of one
    // point that `c`'s value misses, so `c` is set to 4; `b`, the one name left, takes the rest.
    let p = Parts::by_hand(
        vec![sum_is(&["a", "b", "c"], 7)],
        vec![
            points("b", &[0, 3]),
            points("c", &[4]),
            points("a", &[0, 2]),
        ],
    );
    assert_eq!(walk(&p), Some(true));
    // With 6, the rest left to `b` is 2, which neither of `b`'s disjuncts takes, so the walk
    // refuses, though `a = 2, b = 0, c = 4` is a point: it kept `a = 0`, as `pick_by` does.
    let p = Parts::by_hand(
        vec![sum_is(&["a", "b", "c"], 6)],
        vec![
            points("b", &[0, 3]),
            points("c", &[4]),
            points("a", &[0, 2]),
        ],
    );
    assert_eq!(walk(&p), Some(false));
    assert!(has_point(&p, &["a", "b", "c"]));
    // `pick_by` refuses it too, fast and not (PRES-unreached-3-left): the walk is its exact
    // form here, and its general body, run once with the walk skipped, refused it at both
    // `deep`. `decide` and `satisfiable` find the point, with `c`'s disjunction of one point or
    // of two (one cut off by a bound): the passes before any search join the first into the
    // conjunction, and 120 such formulas (each order of the names, targets 0 to 9) never had
    // the walk refuse on 2026-11-14.
    for deep in [false, true] {
        assert!(pick_by(&p, deep, true).is_err());
        assert!(pick_by(&p, deep, false).is_err());
    }
    let one_of =
        |a: &str, vs: &[i128]| Formula::or(vs.iter().map(|&v| Formula::Con(is(a, v))).collect());
    for cs in [vec![4], vec![4, 100]] {
        let f = Formula::and(vec![
            Formula::Con(sum_is(&["a", "b", "c"], 6)),
            one_of("b", &[0, 3]),
            one_of("c", &cs),
            Formula::Con(Con::ge(&k(50), &y("c"))),
            one_of("a", &[0, 2]),
        ]);
        assert_eq!(decide(&f), Ok(true));
        let m = satisfiable(&f).expect("answered").expect("a point");
        assert!(f.holds(&m), "{m:?}");
    }
}

#[test]
fn a_disjunction_of_one_point_on_a_row_of_bounded_names() {
    for (c_val, total) in [(5, 8), (0, 7), (5, 5)] {
        let mut cons = vec![sum_is(&["a", "b", "c"], total)];
        cons.extend(within("a", 3));
        cons.extend(within("b", 4));
        cons.extend(within("c", 5));
        let p = Parts::by_hand(
            cons,
            vec![
                points("a", &[0, 3]),
                points("b", &[0, 4]),
                points("c", &[c_val]),
            ],
        );
        assert_eq!(walk(&p), Some(true), "c = {c_val}, total {total}");
    }
}

#[test]
fn a_disjunction_of_one_point_on_a_fixed_name() {
    let fixed = |v: i128| {
        Parts::by_hand(
            vec![sum_is(&["a", "b"], 4), is("f", 2)],
            vec![
                points("a", &[0, 4]),
                points("b", &[0, 4]),
                points("f", &[v]),
            ],
        )
    };
    assert_eq!(walk(&fixed(2)), Some(true));
    assert_eq!(walk(&fixed(5)), Some(false));
    assert!(!has_point(&fixed(5), &["a", "b", "f"]));
}

#[test]
fn a_row_with_no_disjunction() {
    let p = Parts::by_hand(
        vec![
            sum_is(&["a", "b"], 4),
            is("a", 1),
            is("b", 3),
            sum_is(&["c", "d"], 4),
        ],
        vec![points("c", &[0, 4]), points("d", &[0, 4])],
    );
    assert_eq!(walk(&p), Some(true));
}

/// A row its bounds cannot meet is found empty before the walk: a bounded row whose target lies
/// past the sum of its weights or below zero, and a row of fixed names whose sum is not its
/// target. So the walk never sees such a row.
#[test]
fn a_row_its_bounds_cannot_meet_is_not_walked() {
    for total in [-1, 8] {
        let mut cons = vec![sum_is(&["a", "b"], total)];
        cons.extend(within("a", 3));
        cons.extend(within("b", 4));
        let p = Parts::by_hand(cons, vec![points("a", &[0, 3]), points("b", &[0, 4])]);
        assert_eq!(walk(&p), None, "total {total}");
    }
    let p = Parts::by_hand(
        vec![
            sum_is(&["a", "b"], 5),
            is("a", 1),
            is("b", 3),
            sum_is(&["c", "d"], 4),
        ],
        vec![points("c", &[0, 4]), points("d", &[0, 4])],
    );
    assert_eq!(walk(&p), None);
}
