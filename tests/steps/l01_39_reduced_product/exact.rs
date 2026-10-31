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
    let t0 = std::time::Instant::now();
    assert!(s.assume(&is("n", 4), true, &none()).bottom);
    assert!(!s.assume(&is("n", 999_999_999_997), true, &none()).bottom);
    assert!(t0.elapsed().as_secs() < 5, "took {:?}", t0.elapsed());
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
    let w = s.exactly.values().next().cloned().expect("a witness");
    // Narrowing to a range that keeps the witness keeps it; one that drops it finds another.
    let v = w["n"];
    let keep = s.assume(&prim(Prim::Ge, vec![var("n"), lit(v)]), true, &none());
    assert_eq!(keep.exactly.values().next(), Some(&w));
    let drop = s.assume(&prim(Prim::Gt, vec![var("n"), lit(v)]), true, &none());
    assert!(!drop.bottom);
    let w2 = drop.exactly.values().next().expect("a witness")["n"];
    assert!(w2 > v && (w2 * w2) % 10 == 9, "{w2}");
}
