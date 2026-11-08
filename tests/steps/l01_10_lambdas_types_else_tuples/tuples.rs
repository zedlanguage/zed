//! A tuple has one or more components; one trailing comma is allowed, and `(e,)` is the one-tuple (QUESTIONS A21).

use super::check;

#[test]
fn tuples() {
    check(&[
        ("(1, \"one\")", "(tuple 1 (str \"one\"))"),
        ("(lo, hi,)", "(tuple lo hi)"),
        ("((1, 2), 3)", "(tuple (tuple 1 2) 3)"),
        ("(x, y).swap", "(. (tuple x y) swap)"),
        ("(e)", "e"),
        ("(e,)", "(tuple e)"),
    ]);
}
