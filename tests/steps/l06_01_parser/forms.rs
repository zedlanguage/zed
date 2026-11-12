//! Each form of layer L6 builds to its s-expression.

use super::check;

#[test]
fn loops_build_with_and_without_a_step_name() {
    check(&[
        (
            "f(n) = loop t { while t < n; initial x = 0; x' = x + 1; };",
            "(def f (n) = (loop t (block (while (< t n)) (initial (x) 0) (= (x') (+ x 1)))))",
        ),
        (
            "f(n) = loop { initial x = 1; x' = x * 2; until x' > n; };",
            "(def f (n) = (loop (block (initial (x) 1) (= (x') (* x 2)) (until (> x' n)))))",
        ),
        ("f(x) = loop { };", "(def f (x) = (loop (block)))"),
        (
            "p = loop t { while t < edits::len && !closed; \
             initial doc = empty; doc' = doc.patch(edits[t]); };",
            "(= (p) (loop t (block (while (&& (< t (:: edits len)) (! closed))) \
             (initial (doc) empty) (= (doc') (call (. doc patch) (index edits t))))))",
        ),
    ]);
}

#[test]
fn breaks_build_as_expressions() {
    check(&[
        (
            "f(n) = loop { break n; };",
            "(def f (n) = (loop (block (do (break n)))))",
        ),
        ("f(x) = c || (break x);", "(def f (x) = (|| c (break x)))"),
        (
            "f(xs, v) = loop i { hit = if xs[i] == v { break i } else { i }; };",
            "(def f (xs v) = (loop i (block (= (hit) (if (== (index xs i) v) (block (return \
             (break i))) (block (return i)))))))",
        ),
        // The operand is an `Expr12`: a lambda there is parenthesized.
        (
            "f(x) = loop { break (y -> y); };",
            "(def f (x) = (loop (block (do (break (fn (y) y))))))",
        ),
        ("f(x) = loop { break y -> y; };", "syntax"),
    ]);
}

#[test]
fn mutable_bindings_and_spread_calls_build() {
    check(&[
        (
            "f(c) = { mutable d = c; prev = d*.bump(3); prev };",
            "(def f (c) = (block (mutable (= (d) c)) (= (prev) (call (*. d bump) 3)) (return \
             prev)))",
        ),
        (
            "f(n) = loop { mutable c = z; c' = Counter(n: 0); until c > n; };",
            "(def f (n) = (loop (block (mutable (= (c) z)) (= (c') (call Counter (n: 0))) \
             (until (> c n)))))",
        ),
        ("f(x) = g(x)*.h;", "(def f (x) = (*. (call g x) h))"),
        ("f(x) = x*.h*.k;", "(def f (x) = (*. (*. x h) k))"),
        ("mutable x;", "syntax"),
    ]);
}

#[test]
fn indexed_definitions_build_with_their_keys_and_boundary() {
    check(&[
        (
            "cdf[i] = cdf[i-1] + hist[i] with cdf[-1] = 0;",
            "(indexed cdf ((at i)) (+ (index cdf (- i 1)) (index hist i)) (with (= cdf ((at (- \
             1))) 0)))",
        ),
        (
            "g[i in 0..<n][j] = i + j with g[0][k in s] = 1, g[-1][k in s] = 2;",
            "(indexed g ((in i (..< 0 n)) (at j)) (+ i j) (with (= g ((at 0) (in k s)) 1) (= g ((at \
             (- 1)) (in k s)) 2)))",
        ),
        (
            "x[i in 0..<warm] = cold(i);\nx[i in warm..] = hot(x[i - 1]);",
            "(indexed x ((in i (..< 0 warm))) (call cold i))\n(indexed x ((in i (.. warm))) \
             (call hot (index x (- i 1))))",
        ),
        // A key that is a membership test is written in parentheses.
        ("x[(i in s)] = 1;", "(indexed x ((at (in i s))) 1)"),
        ("x[i not in s] = 1;", "(indexed x ((at (not in i s))) 1)"),
    ]);
}

#[test]
fn pushes_and_expression_statements_build() {
    check(&[
        (
            "f(x) = { out' <- x; g(x); 0 };",
            "(def f (x) = (block (<- out' x) (do (call g x)) (return 0)))",
        ),
        // A push reads the sentinel value an `initial` statement gives; a `with initial` item
        // is removed.
        (
            "f(x) = loop { initial acc = 0; acc' <- acc + x; };",
            "(def f (x) = (loop (block (initial (acc) 0) (<- acc' (+ acc x)))))",
        ),
        (
            "f(x) = loop { acc' <- acc + x with initial acc = 0; };",
            "syntax",
        ),
        (
            "f(x) = { (x); 0 };",
            "(def f (x) = (block (do x) (return 0)))",
        ),
    ]);
}

#[test]
fn primes_are_part_of_a_name() {
    check(&[(
        "f(x) = pos'.x + c.y';",
        "(def f (x) = (+ (. pos' x) (. c y')))",
    )]);
    // A name takes one prime: the lexer refuses a second.
    assert!(zedc::lex::lex("f(x) = x'' + 1;").is_err());
}

/// The indexed push `x[i+1] <- e` arrives with keyed pushes at layer L7.
#[test]
fn a_keyed_push_stays_refused() {
    check(&[
        (
            "f(x) = { x[i + 1] <- 3; 0 };",
            concat!(
                "error: ",
                zed_tests::not_yet!("the push at a key `x[i + 1] <- 3;`")
            ),
        ),
        (
            "f(x) = loop i { x[i][0] <- 3; };",
            concat!(
                "error: ",
                zed_tests::not_yet!("the push at a key `x[i][0] <- 3;`")
            ),
        ),
    ]);
}
