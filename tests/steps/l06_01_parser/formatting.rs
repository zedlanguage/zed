//! The formatter writes each form of layer L6 so that it builds again to the same statements,
//! and is a fixed point.

use super::fmt;

#[track_caller]
fn check(cases: &[(&str, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = fmt(text);
            (got != want).then(|| format!("{text}\n  got  {got:?}\n  want {want:?}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn each_form_round_trips() {
    check(&[
        (
            "f(n)=loop t{while t<n;x'=x+1 with x=0;};",
            "f(n) = loop t {\n  while t < n;\n  x' = x + 1 with x = 0;\n};\n",
        ),
        ("f(x) = loop {   };", "f(x) = loop { };\n"),
        (
            "f(n) = loop { break n; };",
            "f(n) = loop {\n  break n;\n};\n",
        ),
        ("f(x) = loop { x };", "f(x) = loop { x };\n"),
        (
            "f(c)={mutable d=c;prev=d *. bump(3);prev};",
            "f(c) = {\n  mutable d = c;\n  prev = d*.bump(3);\n  prev\n};\n",
        ),
        (
            "cdf[ i ]=cdf[i-1]+hist[i]with cdf[-1]=0;",
            "cdf[i] = cdf[i - 1] + hist[i] with cdf[-1] = 0;\n",
        ),
        (
            "g[i in 0..<n][j]=i+j with g[0][k in s]=1,h=2;",
            "g[i in 0..<n][j] = i + j with g[0][k in s] = 1, h = 2;\n",
        ),
        (
            "f(x) = { out' <-x; g( x ); 0 };",
            "f(x) = {\n  out' <- x;\n  g(x);\n  0\n};\n",
        ),
        ("f(x) = g(x) *. h;", "f(x) = g(x)*.h;\n"),
        ("f(x) = pos'.x+c.y';", "f(x) = pos'.x + c.y';\n"),
        (
            "a',b'=(b,a+b)with a=0,b=1;",
            "a', b' = (b, a + b) with a = 0, b = 1;\n",
        ),
    ]);
}

/// The `while` guards are written first and the `until` guards last, before the export, with
/// the comments that go with them; the order among the rest is kept. The builder stores them in
/// the same order, so the text builds to the statements of `want`.
#[test]
fn guards_are_written_where_their_timing_is() {
    check(&[
        (
            "f(n) = loop t { x' = x + 1 with x = 0; until x' > n; y' = x; while t < 9; };",
            "f(n) = loop t {\n  while t < 9;\n  x' = x + 1 with x = 0;\n  y' = x;\n  until x' > \
             n;\n};\n",
        ),
        (
            "f(n) = loop {\n  until a; // last\n  // first\n  while b;\n  until c;\n  while d;\n};",
            "f(n) = loop {\n  // first\n  while b;\n  while d;\n  until a; // last\n  until \
             c;\n};\n",
        ),
        (
            "f(n) = { until a; while b; n };",
            "f(n) = {\n  while b;\n  until a;\n  n\n};\n",
        ),
    ]);
}

/// Parentheses go where the grammar needs them, and nowhere else.
#[test]
fn parentheses_where_the_grammar_needs_them() {
    check(&[
        // A `break` is a whole expression, like a lambda.
        ("f(c, x) = c || (break x);", "f(c, x) = c || (break x);\n"),
        (
            "f(x) = loop { break (y -> y); };",
            "f(x) = loop {\n  break (y -> y);\n};\n",
        ),
        (
            "f(x) = loop { break (x else 0); };",
            "f(x) = loop {\n  break x else 0;\n};\n",
        ),
        (
            "f(x) = loop { y = (break x) else 0; };",
            "f(x) = loop {\n  y = (break x) else 0;\n};\n",
        ),
        // A `loop` has no head, so it takes a suffix or an operator as a block does; in an `if`
        // condition its block would open the branch, so there it is parenthesized.
        (
            "f(x) = (loop { break 1; })::len;",
            "f(x) = loop {\n  break 1;\n}::len;\n",
        ),
        ("f(x) = loop { x }.v + 1;", "f(x) = loop { x }.v + 1;\n"),
        (
            "f(x) = if (loop { x }) { 1 } else { 2 };",
            "f(x) = if (loop { x }) { 1 } else { 2 };\n",
        ),
        // An index key that would read as `i in s` is parenthesized.
        ("x[(i in s)] = 1;", "x[(i in s)] = 1;\n"),
        ("x[(i in s) == t] = 1;", "x[(i in s == t)] = 1;\n"),
        ("x[i not in s] = 1;", "x[i not in s] = 1;\n"),
        ("x[i in (j in s)] = 1;", "x[i in j in s] = 1;\n"),
        // An expression statement that starts with a brace is parenthesized.
        ("f(x) = { ({ x }); 0 };", "f(x) = {\n  ({ x });\n  0\n};\n"),
        (
            "f(x) = { { x }.g(); 0 };",
            "f(x) = {\n  ({ x }.g());\n  0\n};\n",
        ),
        // A number before `*.` is parenthesized, as before `.`.
        ("f(x) = (1)*.g;", "f(x) = (1)*.g;\n"),
    ]);
}

/// A comment inside a boundary or a loop stays with its statement.
#[test]
fn comments_are_kept() {
    check(&[(
        "f(n) = loop t {\n  // the step\n  x' = x + 1 with x = 0; // from zero\n};",
        "f(n) = loop t {\n  // the step\n  x' = x + 1 with x = 0; // from zero\n};\n",
    )]);
}
