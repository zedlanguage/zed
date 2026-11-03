//! The formatter writes each form of layer L3 so that it builds again to the same statements,
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
        ("f(x)=1..<2;", "f(x) = 1..<2;\n"),
        ("f(n) = 1 ..= n+1;", "f(n) = 1..=n + 1;\n"),
        ("f(x) = 0..;", "f(x) = 0..;\n"),
        ("f(x) = [ 1,2, ];", "f(x) = [1, 2];\n"),
        ("f(x) = [ ];", "f(x) = [];\n"),
        ("f(x) = { };", "f(x) = {};\n"),
        ("f(x) = {1,2};", "f(x) = { 1, 2 };\n"),
        ("f(x) = {1->2,3->4,};", "f(x) = { 1 -> 2, 3 -> 4 };\n"),
        ("f(x, s) = x not  in s;", "f(x, s) = x not in s;\n"),
        ("f(x, s) = !( x in s );", "f(x, s) = !(x in s);\n"),
        ("f(m) = m><(+)><(*);", "f(m) = m >< (+) >< (*);\n"),
        ("f(xs) = xs.foldl(0,(+));", "f(xs) = xs.foldl(0, (+));\n"),
        ("f(xs) = g(xs) :: len;", "f(xs) = g(xs)::len;\n"),
        ("f(x) = ((+));", "f(x) = (+);\n"),
        ("f(x: [ int ]) = x;", "f(x: [int]) = x;\n"),
        (
            "f(m) = for k->v in m where v>0 { k+v };",
            "f(m) = for k -> v in m where v > 0 { k + v };\n",
        ),
        (
            "f(x) = match x { 0..<10 -> 1, -5..=-1 -> 2, 10.. -> 3 };",
            "f(x) = match x {\n  0..<10 -> 1,\n  -5..=-1 -> 2,\n  10.. -> 3,\n};\n",
        ),
    ]);
}

#[test]
fn parentheses_stay_where_the_grammar_needs_them() {
    check(&[
        ("f(x) = (0..<3)::len;", "f(x) = (0..<3)::len;\n"),
        ("f(x) = (1..<2)..<3;", "f(x) = (1..<2)..<3;\n"),
        ("f(x) = (x >< (+))::len;", "f(x) = (x >< (+))::len;\n"),
        ("f(x) = (a + b) >< (+);", "f(x) = a + b >< (+);\n"),
        ("f(x) = (a >< (+)) + b;", "f(x) = (a >< (+)) + b;\n"),
        ("f(x) = (x in s) == true;", "f(x) = x in s == true;\n"),
        ("f(x) = (x == y) in s;", "f(x) = (x == y) in s;\n"),
        ("f(x) = -(0..<3);", "f(x) = -(0..<3);\n"),
    ]);
}

#[test]
fn a_statement_that_opens_with_a_display_stays_a_statement() {
    check(&[
        (
            "f(m) = { y = { 1 } >< (+); y };",
            "f(m) = {\n  y = { 1 } >< (+);\n  y\n};\n",
        ),
        ("f(m) = { { 1 } >< (+) };", "f(m) = { { 1 } >< (+) };\n"),
    ]);
}
