//! `@exact` scopes: the scope is bottom exactly when no point of its names' intervals and
//! classes meets the written constraints. The names keep their algebraic bounds; a question
//! about the exact set is a test assumed in the scope.

use std::sync::Arc;

use zed_kernel::term::build::{lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term};
use zedc::store::product::{Product, Scope};

fn none() -> zedc::store::cell::Premises {
    zedc::store::cell::Premises::new()
}

/// The scope of integer names `ns`, each within `lo..=hi`, exact or not.
fn within(ns: &[(&str, i64, i64)], exact: bool) -> Scope {
    let names = ns
        .iter()
        .map(|&(n, _, _)| (Arc::from(n), Product::of_type(Type::int())));
    let mut s = if exact {
        Scope::exact(names)
    } else {
        Scope::new(names)
    };
    for &(n, lo, hi) in ns {
        let range = prim(
            Prim::And,
            vec![
                prim(Prim::Ge, vec![var(n), lit(lo)]),
                prim(Prim::Le, vec![var(n), lit(hi)]),
            ],
        );
        s = s.assume(&range, true, &none());
    }
    s
}

/// `a * b mod 10 == r`.
fn product_mod_10(a: &str, b: &str, r: i64) -> Term {
    let ab = prim(Prim::Mul, vec![var(a), var(b)]);
    prim(Prim::Eq, vec![prim(Prim::Mod, vec![ab, lit(10)]), lit(r)])
}

fn written(mut s: Scope, ts: &[Term]) -> Scope {
    for t in ts {
        s.write(t.clone());
    }
    s.reduce();
    s
}

/// `n == v`.
fn is(n: &str, v: i64) -> Term {
    prim(Prim::Eq, vec![var(n), lit(v)])
}

/// The values of `n` in `lo..=hi` that the scope allows, each found by assuming `n == v`.
fn allowed(s: &Scope, n: &str, lo: i64, hi: i64) -> Vec<i64> {
    (lo..=hi)
        .filter(|&v| !s.assume(&is(n, v), true, &none()).bottom)
        .collect()
}

#[test]
fn an_exact_scope_allows_only_the_points_that_meet_a_written_constraint() {
    let t = product_mod_10("n", "n", 9);
    let exact = written(within(&[("n", 0, 30)], true), &[t]);
    // The bounds stay algebraic: nothing lists the exact set.
    assert_eq!(exact.get("n").ints().to_string(), "[0..=30]");
    assert_eq!(allowed(&exact, "n", 0, 30), [3, 7, 13, 17, 23, 27]);
}

#[test]
fn a_constraint_through_a_shared_name_decides_the_other_name() {
    // `m * n mod 10 == 1` alone allows every odd `m` not a multiple of 5; with `n` among
    // 3, 7, 13, 17, 23 and 27, only `m` ending in 3 or 7 has a partner.
    let ts = [product_mod_10("m", "n", 1), product_mod_10("n", "n", 9)];
    let s = written(within(&[("m", 0, 20), ("n", 0, 30)], true), &ts);
    assert!(!s.bottom);
    assert_eq!(allowed(&s, "m", 0, 20), [3, 7, 13, 17]);
}

#[test]
fn an_exact_scope_with_no_point_meeting_its_constraints_is_bottom() {
    // `n * n` never ends in 9 when `n` ends in 5.
    let five = prim(
        Prim::Eq,
        vec![prim(Prim::Mod, vec![var("n"), lit(10)]), lit(5)],
    );
    let ts = [product_mod_10("n", "n", 9), five];
    let plain = written(within(&[("n", 0, 30)], false), &ts);
    assert!(!plain.bottom && !plain.get("n").is_empty());
    let s = written(within(&[("n", 0, 30)], true), &ts);
    assert!(s.bottom || s.get("n").is_empty(), "{}", s.get("n"));
}

#[test]
fn a_point_inside_a_huge_range_is_excluded_without_listing_the_range() {
    // Over `0..=10^12` the exact set of `n * n mod 10 == 9` has 4·10^11 members; excluding
    // 4 assumes `n == 4`, a box of one point, and a witness for the whole range is found by
    // halving toward the first point.
    let t = product_mod_10("n", "n", 9);
    let s = written(within(&[("n", 0, 1_000_000_000_000)], true), &[t]);
    assert!(!s.bottom);
    let t0 = zed_tests::scaling::cpu_time();
    assert!(s.assume(&is("n", 4), true, &none()).bottom);
    assert!(!s.assume(&is("n", 999_999_999_997), true, &none()).bottom);
    let took = zed_tests::scaling::cpu_time() - t0;
    assert!(took.as_secs() < 5, "took {took:?}");
}

#[test]
fn constraints_that_share_no_name_are_searched_apart() {
    // Each of `a`, `b` and `c` has 10^6 values and a set of 4·10^5; searched together the
    // box would have 10^18 points, apart each search is a halving.
    let ts = [
        product_mod_10("a", "a", 9),
        product_mod_10("b", "b", 9),
        product_mod_10("c", "c", 9),
    ];
    let r = 1_000_000;
    let s = written(within(&[("a", 0, r), ("b", 0, r), ("c", 0, r)], true), &ts);
    assert!(!s.bottom);
    assert_eq!(s.exactly.len(), 3);
    assert!(s.assume(&is("b", 4), true, &none()).bottom);
}

#[test]
fn a_witness_still_within_the_bounds_is_kept() {
    let t = product_mod_10("n", "n", 9);
    let s = written(within(&[("n", 0, 30)], true), &[t]);
    let w = s.exactly.get("n").cloned().expect("a witness");
    // Narrowing to a range that keeps the witness keeps it; one that drops it finds another.
    let v = w.to_i64().expect("a witness in 0..=30");
    let keep = s.assume(&prim(Prim::Ge, vec![var("n"), lit(v)]), true, &none());
    assert_eq!(keep.exactly, s.exactly);
    let drop = s.assume(&prim(Prim::Gt, vec![var("n"), lit(v)]), true, &none());
    assert!(!drop.bottom);
    let w2 = drop.exactly.get("n").expect("a witness").to_i64();
    let w2 = w2.expect("a witness in 0..=30");
    assert!(w2 > v && (w2 * w2) % 10 == 9, "{w2}");
}

/// A chain of four names, each pair of neighbors with a product ending in 1, and the last
/// name's square ending in 9: the constraints of a scope that tracks, say, four gears whose
/// tooth counts must mesh in turn.
fn gear_chain() -> [Term; 4] {
    [
        product_mod_10("a", "b", 1),
        product_mod_10("b", "c", 1),
        product_mod_10("c", "d", 1),
        product_mod_10("d", "d", 9),
    ]
}

/// A program that checks one constraint per line reduces after each; the exact sets must be
/// those of reducing once after all of them. Building the two scopes takes about 50 ms; nearly
/// all the time is the 31 searches of [`allowed`] for each name in each scope, about 40 ms each
/// (COMPLEXITY.md S17). As one test of the four names it took 10.6 to 12.1 s alone at load 24
/// and 32 s at load 39 as SPLIT-l01_39-slow measured it, so each pair of names is a test
/// (item SPLIT-l01_39-rest).
mod constraints_reduced_one_at_a_time_decide_as_all_at_once {
    use super::*;

    const NAMES: [(&str, i64, i64); 4] = [("a", 0, 30), ("b", 0, 30), ("c", 0, 30), ("d", 0, 30)];

    /// The values each of `checked` allows in the scope reduced after each constraint, which
    /// must be those it allows in the scope reduced once after all of them.
    fn part(checked: &[&str]) -> Vec<Vec<i64>> {
        let at_once = written(within(&NAMES, true), &gear_chain());
        let mut one_by_one = within(&NAMES, true);
        for t in gear_chain() {
            one_by_one = written(one_by_one, &[t]);
        }
        assert!(!at_once.bottom && !one_by_one.bottom);
        let names = NAMES.iter().filter(|(n, _, _)| checked.contains(n));
        names
            .map(|&(n, lo, hi)| {
                let got = allowed(&one_by_one, n, lo, hi);
                assert_eq!(got, allowed(&at_once, n, lo, hi), "{n}");
                got
            })
            .collect()
    }

    #[test]
    fn names_a_and_b() {
        let got = part(&["a", "b"]);
        // `d` ends in 3 or 7, so `c`, `b` and `a` do too.
        assert_eq!(got[0], [3, 7, 13, 17, 23, 27]);
    }

    #[test]
    fn names_c_and_d() {
        part(&["c", "d"]);
    }
}

#[test]
fn a_later_constraint_that_breaks_the_chain_makes_the_scope_bottom() {
    // After the chain is reduced, a last line asks for `a` ending in 5: no product of it
    // ends in 1, so no point is left. Only the group of `a` holds the change.
    let names = [("a", 0, 30), ("b", 0, 30), ("c", 0, 30), ("d", 0, 30)];
    let s = written(within(&names, true), &gear_chain());
    assert!(!s.bottom);
    let five = prim(
        Prim::Eq,
        vec![prim(Prim::Mod, vec![var("a"), lit(10)]), lit(5)],
    );
    let s = written(s, &[five]);
    assert!(s.bottom || s.get("a").is_empty(), "{}", s.get("a"));
}

#[test]
fn a_name_fixed_in_the_middle_of_a_chain_still_decides_both_sides() {
    // Fixing `b` to 3 splits the chain in two; `a` must then end in 7 and so must `c`, and
    // with `b` ending in 5 no point is left.
    let names = [("a", 0, 30), ("b", 0, 30), ("c", 0, 30), ("d", 0, 30)];
    let s = written(within(&names, true), &gear_chain());
    let three = s.assume(&is("b", 3), true, &none());
    assert!(!three.bottom);
    assert_eq!(allowed(&three, "a", 0, 30), [7, 17, 27]);
    assert_eq!(allowed(&three, "c", 0, 30), [7, 17, 27]);
    assert!(s.assume(&is("b", 5), true, &none()).bottom);
}
