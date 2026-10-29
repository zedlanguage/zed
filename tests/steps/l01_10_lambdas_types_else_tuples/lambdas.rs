//! A lambda's parameters are one name or a declaration's parameter list; a brace after the
//! arrow is a block.

use super::check;

#[test]
fn parameters_are_a_name_or_a_list() {
    check(&[
        ("x -> x + 1", "(fn (x) (+ x 1))"),
        ("() -> 0", "(fn () 0)"),
        ("(a, b) -> a + b", "(fn (a b) (+ a b))"),
        ("(x: int) -> x * 2", "(fn ((x: int)) (* x 2))"),
        (
            "(positional v: f64, lo = 0.0) -> v - lo",
            "(fn ((positional v: f64) (lo = 0.0)) (- v lo))",
        ),
        ("(w: f64 = 1.0,) -> w", "(fn ((w: f64 = 1.0)) w)"),
        ("x -> y -> x * y", "(fn (x) (fn (y) (* x y)))"),
        (
            "orders.map(o -> o.qty * o.price)",
            "(call (. orders map) (fn (o) (* (. o qty) (. o price))))",
        ),
        (
            "pairs.sortBy((a, b) -> a.key < b.key)",
            "(call (. pairs sortBy) (fn (a b) (< (. a key) (. b key))))",
        ),
    ]);
}

#[test]
fn a_brace_after_the_arrow_is_a_block() {
    check(&[
        ("x -> { x }", "(fn (x) (block (return x)))"),
        // A record display after the arrow is parenthesized; displays arrive at L2.
        (
            "p -> ({ x: p.x })",
            "error: this form (Primary) is built from layer L2",
        ),
        ("p -> { x: p.x }", "syntax"),
    ]);
}

#[test]
fn a_tuple_parameter_is_destructured_from_layer_2() {
    check(&[(
        "((s, c)) -> s.region",
        "error: this form (PosParam) is built from layer L2",
    )]);
}
