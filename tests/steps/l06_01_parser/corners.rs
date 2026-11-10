//! The corner cases: a loop with and without a step name, nested loops whose `break` reads the
//! outer step, `with` sentinels, primes on a receiver and on a field, `while` and `until` in one
//! loop, an indexed definition with no key, `*.` on a call's result, and an expression
//! statement that writes no generation.

use super::{check, refused};

#[test]
fn a_loop_with_and_without_a_step_name() {
    check(&[
        (
            "f(x) = loop i { break i; };",
            "(def f (x) = (loop i (block (do (break i)))))",
        ),
        (
            "f(x) = loop { break x; };",
            "(def f (x) = (loop (block (do (break x)))))",
        ),
        // The step name is a name, not a keyword or an expression.
        ("f(x) = loop while { };", "syntax"),
        ("f(x) = loop (i) { };", "syntax"),
    ]);
}

/// `break` ends the innermost loop; a step name names the step index (DESIGN.md
/// sec:generations), so an inner `break i` reads the outer loop's step.
#[test]
fn nested_loops_whose_break_reads_the_outer_step() {
    check(&[
        (
            "f(n) = loop i { loop j { until j > n; break i; }; };",
            "(def f (n) = (loop i (block (do (loop j (block (do (break i)) (until (> \
             j n))))))))",
        ),
        (
            "f(n) = loop i { r' = loop j { break i + j; } with initial r = 0; };",
            "(def f (n) = (loop i (block (= (r') (loop j (block (do (break (+ i j))))) (with (initial \
             r 0))))))",
        ),
    ]);
}

#[test]
fn with_sentinels() {
    check(&[
        (
            "d[i][j] = d[i-1][j] + 1 with d[-1][j in 0..<n] = j + 1, d[i in 0..<m][-1] = i + 1;",
            "(indexed d ((at i) (at j)) (+ (index (index d (- i 1)) j) 1) (with (= d ((at (- \
             1)) (in j (..< 0 n))) (+ j 1)) (= d ((in i (..< 0 m)) (at (- 1))) (+ i 1))))",
        ),
        (
            "a', b' = (b, a + b) with initial a = 0, initial b = 1;",
            "(= (a' b') (tuple b (+ a b)) (with (initial a 0) (initial b 1)))",
        ),
        // A sentinel's value is a whole expression, a lambda included.
        (
            "g' = g with initial g = x -> x;",
            "(= (g') g (with (initial g (fn (x) x))))",
        ),
        ("x = 1 with;", "syntax"),
        ("x = 1 with y;", "syntax"),
        ("x = 1 with initial y = 0,;", "syntax"),
    ]);
}

#[test]
fn primes_on_a_receiver_and_on_a_field() {
    check(&[
        (
            "f(b) = loop { pos' = pos.step() with initial pos = start; until pos'.x > b; };",
            "(def f (b) = (loop (block (= (pos') (call (. pos step)) (with (initial pos start))) \
             (until (> (. pos' x) b)))))",
        ),
        ("f(c) = c.x' + c.x;", "(def f (c) = (+ (. c x') (. c x)))"),
        // A field is no target: `T.m = e` declares a method, so these are methods whose
        // receiver or name is primed, which name resolution refuses.
        ("p'.x = 1;", "(method p'.x = 1)"),
        ("p.x' = 1;", "(method p.x' = 1)"),
    ]);
    assert_eq!(
        refused("p'.x = 1;"),
        [concat!(
            zed_tests::not_yet!("the primed name `p'`"),
            " [p'.x = 1;]"
        )]
    );
    assert_eq!(
        refused("p.x' = 1;"),
        [concat!(
            zed_tests::not_yet!("the primed name `x'`"),
            " [p.x' = 1;]"
        )]
    );
}

#[test]
fn while_and_until_in_one_loop() {
    check(&[(
        "f(n) = loop t { x' = x + t with initial x = 0; until x' > n; while t < 10; };",
        "(def f (n) = (loop t (block (while (< t 10)) (= (x') (+ x t) (with (initial x 0))) \
         (until (> x' n)))))",
    )]);
}

/// An indexed definition has a key in each bracket: the grammar has no empty piece.
#[test]
fn an_indexed_definition_with_no_key_is_a_syntax_error() {
    check(&[
        ("x[] = 0;", "syntax"),
        ("x[i][] = 0;", "syntax"),
        ("x[i] = 0 with x[] = 1;", "syntax"),
        ("x[i];", "(do (index x i))"),
    ]);
}

#[test]
fn spread_on_a_call_result() {
    check(&[
        (
            "f(x) = g(x)*.h(1)*.k;",
            "(def f (x) = (*. (call (*. (call g x) h) 1) k))",
        ),
        (
            "f(x) = g(x)*.h::len;",
            "(def f (x) = (:: (*. (call g x) h) len))",
        ),
        ("f(x) = x*.(h);", "syntax"),
        ("f(x) = x *. h;", "(def f (x) = (*. x h))"),
    ]);
}

/// Whether an expression statement writes a generation, a port or an accumulator is a
/// question for checking (step L6.3): the parser takes any expression.
#[test]
fn an_expression_statement_that_writes_no_generation() {
    check(&[(
        "f(x) = { g(x) + 1; 0 };",
        "(def f (x) = (block (do (+ (call g x) 1)) (return 0)))",
    )]);
    assert_eq!(
        refused("f(x) = { x + 1; 0 };"),
        [concat!(
            zed_tests::not_yet!("an expression statement"),
            " [x + 1;]"
        )]
    );
}
