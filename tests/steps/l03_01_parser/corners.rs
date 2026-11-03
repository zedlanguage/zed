//! The corner cases: empty displays and ranges, nested sections, `not in` beside `!(a in b)`,
//! chains of `><`, `::` on a call, `[T]` as a type beside a display, and mixed displays.

use super::check;

#[test]
fn empty_displays_and_ranges() {
    check(&[
        ("f(x) = [];", "(def f (x) = (array))"),
        ("f(x) = {};", "(def f (x) = (map))"),
        ("f(x) = 0..<0;", "(def f (x) = (..< 0 0))"),
        ("f(x) = (0..<0)::len;", "(def f (x) = (:: (..< 0 0) len))"),
        ("f(x) = { 1, };", "(def f (x) = (set 1))"),
        ("f(x) = [1, ];", "(def f (x) = (array 1))"),
    ]);
}

#[test]
fn nested_sections_are_one_section() {
    check(&[
        ("f(x) = ((+));", "(def f (x) = (section +))"),
        ("f(x) = { (+) };", "(def f (x) = (set (section +)))"),
        (
            "f(x) = (-) >< (+);",
            "(def f (x) = (>< (section -) (section +)))",
        ),
        ("f(x) = (..<);", "syntax"),
    ]);
}

#[test]
fn not_in_is_one_test_and_negation_is_another() {
    check(&[
        ("f(x, s) = x not in s;", "(def f (x s) = (not in x s))"),
        ("f(x, s) = !(x in s);", "(def f (x s) = (! (in x s)))"),
        ("f(x, s) = not (x in s);", "syntax"),
        ("f(x, s) = x in s in s;", "syntax"),
        (
            "f(x, s) = x in s == true;",
            "(def f (x s) = (== (in x s) true))",
        ),
    ]);
}

#[test]
fn reductions_chain_from_the_left() {
    check(&[
        (
            "f(m) = m >< (+) >< (*);",
            "(def f (m) = (>< (>< m (section +)) (section *)))",
        ),
        (
            "f(x) = { x } >< (+);",
            "(def f (x) = (>< (set x) (section +)))",
        ),
        (
            "f(x) = (x >< (+))::len;",
            "(def f (x) = (:: (>< x (section +)) len))",
        ),
    ]);
}

#[test]
fn a_read_applies_to_a_call_result() {
    check(&[
        ("f(xs) = g(xs)::len;", "(def f (xs) = (:: (call g xs) len))"),
        (
            "f(xs) = xs.h()::card;",
            "(def f (xs) = (:: (call (. xs h)) card))",
        ),
    ]);
}

#[test]
fn a_family_type_is_not_a_display() {
    check(&[
        (
            "f(x: [int]) = [int];",
            "(def f ((x: (array int))) = (array int))",
        ),
        ("f(x: [int]) = [];", "(def f ((x: (array int))) = (array))"),
    ]);
}

#[test]
fn a_display_is_a_set_or_a_map() {
    check(&[
        (
            "f(x) = { 1, 2 -> 3 };",
            "error: a map entry `k -> v` in a display whose first entry is a set element: \
             a display is a set or a map, not both; the first entry, a set element at byte 9",
        ),
        (
            "f(x) = { 1 -> 2, 3 };",
            "error: a set element in a display whose first entry is a map entry `k -> v`: \
             a display is a set or a map, not both; the first entry, a map entry `k -> v` at byte 9",
        ),
    ]);
}

#[test]
fn a_for_nests_in_its_head_and_in_displays() {
    check(&[
        (
            "f(m) = for x in (for y in m { y }) { x };",
            "(def f (m) = (for (x) (for (y) m (block (return y))) (block (return x))))",
        ),
        (
            "f(m) = [for x in m { x }];",
            "(def f (m) = (array (for (x) m (block (return x)))))",
        ),
        (
            "f(m) = for x in { 1, 2 } { x };",
            "(def f (m) = (for (x) (set 1 2) (block (return x))))",
        ),
    ]);
}
