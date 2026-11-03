//! `match`: arms as display entries, `pattern -> body` with an optional `where` guard, and the
//! patterns of L2.1 together with type patterns `n is T` and literal patterns.

use super::check;

#[test]
fn a_tree_sum_matches_on_atoms_and_structs() {
    check(&[
        (
            "size(t) = match t { #leaf -> 0, Node(l:, r:) -> 1 + size(l) + size(r) };",
            "(def size (t) = (match t (-> #leaf 0) (-> Node(l:, r:) (+ (+ 1 (call size l)) (call size r)))))",
        ),
        (
            "describe(v) = match v {\n  n is int -> \"int\",\n  s is String -> s,\n  _ -> \"other\",\n};",
            "(def describe (v) = (match v (-> (is n int) (str \"int\")) (-> (is s String) s) (-> _ (str \"other\"))))",
        ),
    ]);
}

#[test]
fn guards_and_literals() {
    check(&[
        (
            "sign(n) = match n { 0 -> 0, k where k > 0 -> 1, _ -> -1 };",
            "(def sign (n) = (match n (-> 0 0) (-> k (where (> k 0)) 1) (-> _ (- 1))))",
        ),
        // A guard on every arm.
        (
            "grade(s) = match s { x where x >= 90 -> \"A\", x where x >= 80 -> \"B\", x where x >= 0 -> \"C\" };",
            "(def grade (s) = (match s (-> x (where (>= x 90)) (str \"A\")) (-> x (where (>= x 80)) (str \"B\")) (-> x (where (>= x 0)) (str \"C\"))))",
        ),
        (
            "neg(n) = match n { -1 -> true, -2.5 -> true, 3r -> false, \"one\" -> false, false -> true, true -> false };",
            "(def neg (n) = (match n (-> (- 1) true) (-> (- 2.5) true) (-> 3r false) (-> (str \"one\") false) (-> false true) (-> true false)))",
        ),
    ]);
}

#[test]
fn nested_and_typed_patterns() {
    check(&[
        (
            "f(r) = match r { #ok(Pair(a: (x, _), b: n is int | f64)) -> x, #err(m:) -> 0 };",
            "(def f (r) = (match r (-> #ok(Pair(a: (x, _), b: (is n (| int f64)))) x) (-> #err(m:) 0)))",
        ),
        (
            "g(v) = match v { is Point -> 1, (a, b) -> a + b };",
            "(def g (v) = (match v (-> (is Point) 1) (-> (a, b) (+ a b))))",
        ),
        (
            "h(e) = match e { #add(l:, r:) where l == r -> { d = l; d * 2 }, other -> eval(other) };",
            "(def h (e) = (match e (-> #add(l:, r:) (where (== l r)) (block (= (d) l) (return (* d 2)))) (-> other (call eval other))))",
        ),
    ]);
}

#[test]
fn a_match_is_an_operand() {
    check(&[
        (
            "k = 1 + match x { _ -> 2 } * 3;",
            "(= (k) (+ 1 (* (match x (-> _ 2)) 3)))",
        ),
        (
            "m = match match x { _ -> y } { _ -> 0 };",
            "(= (m) (match (match x (-> _ y)) (-> _ 0)))",
        ),
        (
            "n = match (if c { a } else { b }) { _ -> 0 };",
            "(= (n) (match (if c (block (return a)) (block (return b))) (-> _ 0)))",
        ),
    ]);
}

#[test]
fn malformed_matches_are_syntax_errors() {
    check(&[
        // An empty match has no arm; sec:grammar asks for one at least.
        ("e = match x { };", "syntax"),
        ("e = match x { 1 };", "syntax"),
        ("e = match x { 1 -> };", "syntax"),
        ("e = match x { 1 -> 2 3 -> 4 };", "syntax"),
        ("e = match x { x where -> 1 };", "syntax"),
        ("e = match x { n is -> 1 };", "syntax"),
        ("e = match x { - -> 1 };", "syntax"),
        ("e = match x;", "syntax"),
    ]);
}
