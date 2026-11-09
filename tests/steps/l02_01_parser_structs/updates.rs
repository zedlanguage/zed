//! `with` updates: `p with { x = 3 }`, a path one level in per step, the suffixes after the
//! braces, and the precedence `with` shares with `><`.

use super::check;

#[test]
fn with_updates_fields() {
    check(&[
        (
            "moved = p with { x = 3.0 };",
            "(= (moved) (with p (= x 3.0)))",
        ),
        (
            "a2 = a with { bal = a.bal - amt, frozen = true };",
            "(= (a2) (with a (= bal (- (. a bal) amt)) (= frozen true)))",
        ),
        (
            "k2 = k with { c.x = 0.0, c.y = 1.0, };",
            "(= (k2) (with k (= c.x 0.0) (= c.y 1.0)))",
        ),
    ]);
}

#[test]
fn a_with_nests_and_chains() {
    check(&[
        (
            "k2 = k with { c = k.c with { x = 0.0 } };",
            "(= (k2) (with k (= c (with (. k c) (= x 0.0)))))",
        ),
        (
            "q = p with { x = 1 } with { y = 2 };",
            "(= (q) (with (with p (= x 1)) (= y 2)))",
        ),
    ]);
}

#[test]
fn suffixes_after_the_braces_apply_to_the_update() {
    check(&[
        (
            "n = (p with { x = 3 }).norm;",
            "(= (n) (. (with p (= x 3)) norm))",
        ),
        (
            "n = p with { x = 3 }.norm;",
            "(= (n) (. (with p (= x 3)) norm))",
        ),
        (
            "n = p with { x = 3 }.scale(2);",
            "(= (n) (call (. (with p (= x 3)) scale) 2))",
        ),
    ]);
}

#[test]
fn with_takes_the_arithmetic_to_its_left() {
    check(&[
        (
            "s = a + b with { x = 1 };",
            "(= (s) (with (+ a b) (= x 1)))",
        ),
        (
            "t = a < b with { x = 1 };",
            "(= (t) (< a (with b (= x 1))))",
        ),
        (
            "u = p with { x = 1 } is Point;",
            "(= (u) (is (with p (= x 1)) Point))",
        ),
    ]);
}

#[test]
fn a_path_updated_twice_is_an_error() {
    check(&[
        (
            "q = p with { x = 1, y = 2, x = 3 };",
            "error: the field `x` is updated twice in one `with`, and a `with` updates each field \
             once. Remove one of the two updates.; the first update of `x` at byte 13",
        ),
        (
            "q = s with { c.x = 1, c.x = 2 };",
            "error: the field `c.x` is updated twice in one `with`, and a `with` updates each field \
             once. Remove one of the two updates.; the first update of `c.x` at byte 13",
        ),
    ]);
}

#[test]
fn keyed_paths_are_of_layer_5() {
    check(&[(
        "m2 = m with { [k].bal = 0 };",
        concat!(
            "error: ",
            zed_tests::not_yet!("the field update `[k].bal = 0`")
        ),
    )]);
}
