//! `@exact` scopes: a written constraint narrows each open name to the projection of the
//! points that meet it, and the narrowing of one name re-projects the constraints that read it.

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

#[test]
fn an_exact_scope_holds_the_points_that_meet_a_written_constraint() {
    let t = product_mod_10("n", "n", 9);
    let plain = written(within(&[("n", 0, 30)], false), std::slice::from_ref(&t));
    let exact = written(within(&[("n", 0, 30)], true), &[t]);
    assert_eq!(plain.get("n").ints().to_string(), "[0..=30]");
    assert_eq!(
        exact.get("n").ints().to_string(),
        "[3..=3, 7..=7, 13..=13, 17..=17, 23..=23, 27..=27]"
    );
}

#[test]
fn narrowing_one_name_re_projects_the_constraints_that_read_it() {
    // `m * n mod 10 == 1` alone allows every odd `m` not a multiple of 5; with `n` among
    // 3, 7, 13, 17, 23 and 27, only `m` ending in 3 or 7 has a partner.
    let ts = [product_mod_10("m", "n", 1), product_mod_10("n", "n", 9)];
    let s = written(within(&[("m", 0, 20), ("n", 0, 30)], true), &ts);
    assert_eq!(
        s.get("m").ints().to_string(),
        "[3..=3, 7..=7, 13..=13, 17..=17]"
    );
    assert!(!s.bottom);
}

#[test]
fn an_exact_scope_with_no_point_meeting_its_constraints_is_bottom() {
    // `n * n` never ends in 9 when `n` ends in 5.
    let five = prim(
        Prim::Eq,
        vec![prim(Prim::Mod, vec![var("n"), lit(10)]), lit(5)],
    );
    let ts = [product_mod_10("n", "n", 9), five];
    let s = written(within(&[("n", 0, 30)], true), &ts);
    assert!(s.bottom || s.get("n").is_empty(), "{}", s.get("n"));
}
