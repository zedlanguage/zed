//! The exact preimage of `@exact` is searched for only in a scope declared `@exact`: n plain
//! scopes beside one exact scope of a fixed size take the boxes that one takes, at n as at 8n.

use std::sync::Arc;

use zed_kernel::term::build::{lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term};
use zedc::store::preimage::exact_steps;
use zedc::store::product::{Product, Scope};

/// The scope of the integer `n` within `0..=30` with `n * n mod 10 == 9` written, reduced;
/// exact or not.
fn squares_ending_in_9(exact: bool) -> Scope {
    let names = [(Arc::from("n"), Product::of_type(Type::int()))];
    let mut s = if exact {
        Scope::exact(names)
    } else {
        Scope::new(names)
    };
    let range: Term = prim(
        Prim::And,
        vec![
            prim(Prim::Ge, vec![var("n"), lit(0)]),
            prim(Prim::Le, vec![var("n"), lit(30)]),
        ],
    );
    s = s.assume(&range, true, &zedc::store::cell::Premises::new());
    let nn = prim(Prim::Mul, vec![var("n"), var("n")]);
    s.write(prim(
        Prim::Eq,
        vec![prim(Prim::Mod, vec![nn, lit(10)]), lit(9)],
    ));
    s.reduce();
    s
}

/// The boxes searched for `n` plain scopes and, if `exact`, one exact scope.
fn boxes(n: usize, exact: bool) -> u64 {
    exact_steps();
    for _ in 0..n {
        assert!(!squares_ending_in_9(false).bottom);
    }
    if exact {
        assert!(!squares_ending_in_9(true).bottom);
    }
    exact_steps()
}

#[test]
fn plain_scopes_search_no_exact_preimage() {
    assert_eq!(boxes(40, false), 0);
}

#[test]
fn one_exact_scope_searches_the_same_boxes_among_n_plain_scopes_as_among_8n() {
    let one = boxes(0, true);
    assert!(one > 0);
    assert_eq!(boxes(40, true), one);
    assert_eq!(boxes(320, true), one);
}
