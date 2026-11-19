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

/// `break;` is a statement, with no value (DESIGN.md sec:grammar, `Break = 'break' ';'`;
/// author P310, "no `break e`"), at any depth of a loop's or a `for`'s body; a block that ends
/// in it exports nothing. With a value, as an operand, or with no `;`, it is a syntax error
/// (step L6.6b).
#[test]
fn breaks_build_as_statements() {
    check(&[
        (
            "f(n) = loop { break; };",
            "(def f (n) = (loop (block (break))))",
        ),
        (
            "f(xs, v) = loop i { if xs[i] == v { break; }; };",
            "(def f (xs v) = (loop i (block (do (if (== (index xs i) v) (block (break)) \
             (block))))))",
        ),
        (
            "f(xs) = for x in xs { if x > 0 { break; }; x };",
            "(def f (xs) = (for (x) xs (block (do (if (> x 0) (block (break)) (block))) \
             (return x))))",
        ),
        ("f(n) = loop { break n; };", "syntax"),
        ("f(n) = loop { break 3; };", "syntax"),
        ("f(c, x) = loop { y = c || (break x); };", "syntax"),
        ("f(c) = loop { if c || break { }; };", "syntax"),
        ("f(c) = loop { break };", "syntax"),
    ]);
}

#[test]
fn spread_calls_build() {
    check(&[
        (
            "f(c) = { d = c; prev = d*.bump(3); prev };",
            "(def f (c) = (block (= (d) c) (= (prev) (call (*. d bump) 3)) (return prev)))",
        ),
        ("f(x) = g(x)*.h;", "(def f (x) = (*. (call g x) h))"),
        ("f(x) = x*.h*.k;", "(def f (x) = (*. (*. x h) k))"),
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
            "f(x) = loop { initial out = 0; out' <- x; g(x); };",
            "(def f (x) = (loop (block (initial (out) 0) (<- out' x) (do (call g x)))))",
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
