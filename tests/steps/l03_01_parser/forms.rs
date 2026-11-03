//! Each form of layer L3 builds to its s-expression.

use super::check;

#[test]
fn ranges_build_with_each_end() {
    check(&[
        ("f(x) = 1..<2;", "(def f (x) = (..< 1 2))"),
        ("f(n) = 1..=n + 1;", "(def f (n) = (..= 1 (+ n 1)))"),
        ("f(x) = 0..;", "(def f (x) = (.. 0))"),
        ("f(x) = -1..<-0;", "(def f (x) = (..< (- 1) (- 0)))"),
        ("f(x) = 1.5..<2.5;", "(def f (x) = (..< 1.5 2.5))"),
        ("f(x) = 0..<x::len;", "(def f (x) = (..< 0 (:: x len)))"),
    ]);
}

#[test]
fn displays_build_as_arrays_sets_and_maps() {
    check(&[
        ("f(x) = [1, 2, 3];", "(def f (x) = (array 1 2 3))"),
        ("f(x) = [[x]];", "(def f (x) = (array (array x)))"),
        ("f(x) = { 1, x };", "(def f (x) = (set 1 x))"),
        ("f(x) = { x };", "(def f (x) = (set x))"),
        (
            "f(x) = { 1 -> \"a\", x -> \"b\" };",
            "(def f (x) = (map (-> 1 (str \"a\")) (-> x (str \"b\"))))",
        ),
        ("f(x) = { a: 1 };", "(def f (x) = (record (a: 1)))"),
    ]);
}

#[test]
fn indexing_and_membership_build() {
    check(&[
        ("f(xs) = xs[0];", "(def f (xs) = (index xs 0))"),
        ("f(x, s) = x in s;", "(def f (x s) = (in x s))"),
        ("f(x, s) = x not in s;", "(def f (x s) = (not in x s))"),
        ("f(x) = x in 0..<10;", "(def f (x) = (in x (..< 0 10)))"),
        (
            "f(x) = x::card in { 1, 2 };",
            "(def f (x) = (in (:: x card) (set 1 2)))",
        ),
    ]);
}

#[test]
fn reductions_folds_and_sections_build() {
    check(&[
        ("f(m) = m >< (+);", "(def f (m) = (>< m (section +)))"),
        ("f(m) = m >< g;", "(def f (m) = (>< m g))"),
        ("f(x) = (==);", "(def f (x) = (section ==))"),
        ("f(x) = (&&);", "(def f (x) = (section &&))"),
        (
            "f(xs) = xs.foldl(0, (+));",
            "(def f (xs) = (call (. xs foldl) 0 (section +)))",
        ),
        (
            "f(xs) = xs.foldr(0, (*));",
            "(def f (xs) = (call (. xs foldr) 0 (section *)))",
        ),
    ]);
}

#[test]
fn metadata_reads_build() {
    check(&[
        ("f(xs) = xs::len;", "(def f (xs) = (:: xs len))"),
        ("f(xs) = xs::domain;", "(def f (xs) = (:: xs domain))"),
        (
            "f(xs) = xs::origin.show;",
            "(def f (xs) = (. (:: xs origin) show))",
        ),
        (
            "f(x) = x::origin::len;",
            "(def f (x) = (:: (:: x origin) len))",
        ),
    ]);
}

#[test]
fn a_for_builds_its_binders_source_guard_and_body() {
    check(&[
        (
            "f(m) = for k -> v in m where v > 0 { k + v };",
            "(def f (m) = (for (k v) m (where (> v 0)) (block (return (+ k v)))))",
        ),
        (
            "f(m) = for x in m { x };",
            "(def f (m) = (for (x) m (block (return x))))",
        ),
        (
            "f(m) = for _ in m { 1 };",
            "(def f (m) = (for (_) m (block (return 1))))",
        ),
        (
            "f(m) = for k -> v -> w in m { k };",
            "(def f (m) = (for (k v w) m (block (return k))))",
        ),
        (
            "f(m) = for i in 0.. { i };",
            "(def f (m) = (for (i) (.. 0) (block (return i))))",
        ),
    ]);
}

#[test]
fn range_patterns_and_family_types_build() {
    check(&[
        (
            "f(x) = match x { 0..<10 -> 1, -5..=-1 -> 2, 10.. -> 3 };",
            "(def f (x) = (match x (-> (..< 0 10) 1) (-> (..= (- 5) (- 1)) 2) (-> (.. 10) 3)))",
        ),
        (
            "f(c) = match c { \"a\"..=\"z\" -> 1, _ -> 0 };",
            "(def f (c) = (match c (-> (..= (str \"a\") (str \"z\")) 1) (-> _ 0)))",
        ),
        ("f(x: [int]) = x;", "(def f ((x: (array int))) = x)"),
        (
            "f(x: [[int]]) = x;",
            "(def f ((x: (array (array int)))) = x)",
        ),
    ]);
}
