//! `type` declarations of unions and recursive unions, with parameters, and the record and
//! applied type forms of L2. A declaration names its type; step L2.5 gives it meaning.

use super::check;

#[test]
fn a_type_declaration_names_a_union() {
    check(&[
        (
            "type Tx = #open(id: String) | #deposit(id: String, amt: int) | #bad;",
            "(type Tx (| (#open (id: String)) (#deposit (id: String) (amt: int)) #bad))",
        ),
        (
            "type Shape = Circle | Square;",
            "(type Shape (| Circle Square))",
        ),
    ]);
}

#[test]
fn a_recursive_union_names_itself() {
    check(&[
        (
            "type Expr = #num(n: int) | #add(l: Expr, r: Expr) | #neg(e: Expr);",
            "(type Expr (| (#num (n: int)) (#add (l: Expr) (r: Expr)) (#neg (e: Expr))))",
        ),
        (
            "type Tree(T) = #leaf | #node(left: Tree(T), value: T, right: Tree(T));",
            "(type Tree (T) (| #leaf (#node (left: (Tree T)) (value: T) (right: (Tree T)))))",
        ),
    ]);
}

#[test]
fn record_and_applied_types() {
    check(&[
        (
            "type Pos = { x: f64, y: f64 };",
            "(type Pos (record (x: f64) (y: f64)))",
        ),
        ("type Pair(A, B) = (A, B);", "(type Pair (A B) (tuple A B))"),
        (
            "type Row = Map(key: String, value: geo.Point);",
            "(type Row (Map (key: String) (value: geo.Point)))",
        ),
        (
            "norm(p: { x: f64, y: f64 }) = p.x;",
            "(def norm ((p: (record (x: f64) (y: f64)))) = (. p x))",
        ),
    ]);
}

#[test]
fn names_declared_twice_are_errors() {
    check(&[
        (
            "type Pair(A, A) = (A, A);",
            "error: the type parameter `A` is declared twice, and each type parameter is declared once. Remove one of \
             the two.; the first type parameter `A` at byte 10",
        ),
        (
            "f(p: { x: f64, x: int }) = p;",
            "error: the field `x` is declared twice, and each field is declared once. Remove one of \
             the two.; the first field `x` at byte 7",
        ),
    ]);
}
