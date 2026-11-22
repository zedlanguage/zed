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
fn main_takes_its_argument_and_pushes_to_its_fields() {
    check(&[
        (
            "main(m: MainArgs) { m.stdout <- m.stdin; }",
            "(def main ((m.stdin: Lines)) (-> (m.stdout: Lines)) (block (<- m.stdout m.stdin)))",
        ),
        (
            "main(m: MainArgs) { m.stdout <- m.stdin; m.stderr <- m.stdin; }",
            "(def main ((m.stdin: Lines)) (-> (m.stdout: Lines) (m.stderr: Lines)) \
             (block (<- m.stdout m.stdin) (<- m.stderr m.stdin)))",
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
            "error: Statement at the top level of the unit: `return 1;`. Move it into the body of \
             `main`, as in `main(m: MainArgs) { return 1; }`.; a unit's top level holds \
             declarations, which take any order and run in no frame; a statement has an order and \
             runs in a frame, so it stands in a body at byte 0; repair: `main(m: MainArgs) { \
             return 1; }` at byte 0",
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
        // In a body: at the top level a push is a statement out of place (TOP-statements-reject).
        (
            "f(t, i) { t[i] <- 1; }",
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
        // A literal type that writes an integer as its powers (LIT-power-values) parses whole.
        (
            "p(x) = x is 3^200000;",
            concat!(
                "error: ",
                zed_tests::not_yet!("the literal type `3^200000`")
            ),
        ),
        (
            "p(x) = x is -5*3^200000;",
            concat!(
                "error: ",
                zed_tests::not_yet!("the literal type `-5*3^200000`")
            ),
        ),
        (
            "p(x) = x is 2^3 | 12^100000*7;",
            concat!("error: ", zed_tests::not_yet!("the literal type `2^3`")),
        ),
    ]);
}
