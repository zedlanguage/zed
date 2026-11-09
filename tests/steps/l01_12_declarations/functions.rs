use super::check;

#[test]
fn an_equation_function_is_its_expression() {
    check(&[
        ("area(w, h) = w * h;", "(def area (w h) = (* w h))"),
        (
            "scale(x: f64, by: f64 = 2.0) = x * by;",
            "(def scale ((x: f64) (by: f64 = 2.0)) = (* x by))",
        ),
        ("zero() = 0;", "(def zero () = 0)"),
    ]);
}

#[test]
fn a_block_function_is_its_block() {
    check(&[(
        "hyp(a, b) { s = a * a + b * b; sqrt(s) }",
        "(def hyp (a b) (block (= (s) (+ (* a a) (* b b))) (return (call sqrt s))))",
    )]);
}

#[test]
fn main_declares_its_ports_and_may_only_push() {
    check(&[
        (
            "main(stdin: Lines) -> (stdout: Lines) { stdout <- stdin; }",
            "(def main ((stdin: Lines)) (-> (stdout: Lines)) (block (<- stdout stdin)))",
        ),
        (
            "main(stdin: Lines) -> (out: Lines, err: Lines) { out <- stdin; err <- stdin; }",
            "(def main ((stdin: Lines)) (-> (out: Lines) (err: Lines)) \
             (block (<- out stdin) (<- err stdin)))",
        ),
    ]);
}

#[test]
fn a_test_table_lists_input_and_expected_in_order() {
    check(&[
        (
            "double(x) = 2 * x test { 1 -> 2, 3 -> 6, }",
            "(def double (x) = (* 2 x) (test (1 2) (3 6)))",
        ),
        (
            "neg(x) { 0 - x } test { 1 -> -1 } test { 0 -> 0 }",
            "(def neg (x) (block (return (- 0 x))) (test (1 (- 1)) (0 0)))",
        ),
    ]);
}

#[test]
fn a_function_inside_a_block_is_a_statement() {
    check(&[(
        "f(x) { sq(v) = v * v; sq(x) }",
        "(def f (x) (block (def sq (v) = (* v v)) (return (call sq x))))",
    )]);
}

#[test]
fn the_unit_top_level_exports_nothing_and_block_bodies_still_export_once() {
    check(&[
        (
            "return 1;",
            "error: `return` gives the value a block exports, and this one stands at the top level of \
             the unit, outside every block. Write it inside the block whose value it gives, or \
             remove it.",
        ),
        (
            "f(x) { return x; x }",
            "error: this block exports a second time, and a block exports one value, once. Remove one \
             of the two exports.; the block's first export at byte 7",
        ),
    ]);
}

#[test]
fn a_form_of_a_later_layer_is_refused_as_not_compiled_yet() {
    check(&[
        (
            "f(x) -> int = x;",
            concat!(
                "error: ",
                zed_tests::not_yet!("the declared result type `-> int`")
            ),
        ),
        (
            "t[i] <- 1;",
            concat!(
                "error: ",
                zed_tests::not_yet!("the push at a key `t[i] <- 1;`")
            ),
        ),
        (
            "p(x) = x is 1;",
            concat!("error: ", zed_tests::not_yet!("the literal type `1`")),
        ),
        (
            "p(x) = x is -1;",
            concat!("error: ", zed_tests::not_yet!("the literal type `-1`")),
        ),
        (
            "p(x) = x is (\"h\");",
            concat!("error: ", zed_tests::not_yet!("the literal type `\"h\"`")),
        ),
    ]);
}
