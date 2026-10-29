//! The layout the formatter writes, on small programs written carelessly.

use super::fmt;

#[track_caller]
fn check(text: &str, want: &str) {
    assert_eq!(fmt(text), want);
}

#[test]
fn spacing_and_parentheses_are_normalized() {
    check(
        "area(w,h)=w*h;\nmean(a,b)=((a+b))/2;\nf(x)=-(-x)**2;\n",
        "area(w, h) = w * h;\nmean(a, b) = (a + b) / 2;\nf(x) = -(-x) ** 2;\n",
    );
    check(
        "g(x)=(x-1)-(x-2);\nh(x)=x-(1-2);\nok(x)=(x<1)==(x<2);\n",
        "g(x) = x - 1 - (x - 2);\nh(x) = x - (1 - 2);\nok(x) = x < 1 == x < 2;\n",
    );
}

#[test]
fn a_block_puts_its_export_last() {
    check(
        "total(xs){return n+m;n=xs.length;m=1;}\n",
        "total(xs) {\n  n = xs.length;\n  m = 1;\n  n + m\n}\n",
    );
    check(
        "pair(x){a=x;return a,a;}\n",
        "pair(x) {\n  a = x;\n  return a, a;\n}\n",
    );
}

#[test]
fn a_block_of_one_export_stays_on_one_line() {
    check(
        "sign(x)=if x<0 {-1} else if x==0 {0} else {1};\n",
        "sign(x) = if x < 0 { -1 } else if x == 0 { 0 } else { 1 };\n",
    );
    // As an operand a block opens with a statement at L1, so its export is written `return`.
    check("f(x)={return x;}+1;\n", "f(x) = { return x; } + 1;\n");
}

#[test]
fn main_pushes_to_its_ports() {
    check(
        "main()->(stdout:Lines){name=\"Zed\";stdout<-\"hello, {name}\";}\n",
        "main() -> (stdout: Lines) {\n  name = \"Zed\";\n  stdout <- \"hello, {name}\";\n}\n",
    );
}

#[test]
fn test_tables_join_into_one_line_under_the_function() {
    check(
        "inc(x)=x+1 test{1->2} test{2->3}\n",
        "inc(x) = x + 1\n  test { 1 -> 2, 2 -> 3 }\n",
    );
    check(
        "twice(x){y=x+x;y} test{1->2}\n",
        "twice(x) {\n  y = x + x;\n  y\n}\n  test { 1 -> 2 }\n",
    );
}

#[test]
fn lambdas_calls_and_else_are_written_short() {
    check(
        "f(xs)=map(xs,(x)->x+1);\ng(a)=h(a:a,b:2,...);\nd(p)=p else #none->0;\n",
        "f(xs) = map(xs, x -> x + 1);\ng(a) = h(a:, b: 2, ...);\nd(p) = p else #none -> 0;\n",
    );
    check(
        "k(t)=t is not (int|#none);\nm()=(1).abs;\n",
        "k(t) = t is not int | #none;\nm() = (1).abs;\n",
    );
}

#[test]
fn comments_stay_with_their_statements() {
    check(
        "// Totals.\ntotal(xs) {\n  return n; // the count\n\n  // xs is a list\n  n = xs.length;\n  // done\n}\n",
        "// Totals.\ntotal(xs) {\n  // xs is a list\n  n = xs.length;\n  n // the count\n  // done\n}\n",
    );
    check(
        "f(x) = g(x, /* why */ 1); // after\n",
        "f(x) = g(x, 1); /* why */ // after\n",
    );
}

#[test]
fn blank_lines_collapse_to_one() {
    check(
        "a() = 1;\n\n\n\nb() = 2;\nc() = 3;\n",
        "a() = 1;\n\nb() = 2;\nc() = 3;\n",
    );
}

#[test]
fn parentheses_keep_a_block_from_opening_a_branch() {
    // An `if` condition's `{` would open the branch, and a default or a lambda body that
    // starts with `{` would be read as a block.
    check(
        "f(a,p)=if (p else {return a;}) {1} else {2};\n",
        "f(a, p) = if (p else { a }) { 1 } else { 2 };\n",
    );
    check(
        "g(p)=p else ({return 1;}+1);\nh(q)=x->({return q;}).k;\n",
        "g(p) = p else ({ return 1; } + 1);\nh(q) = x -> ({ return q; }.k);\n",
    );
}

#[test]
fn a_source_that_does_not_parse_is_reported_at_its_line_and_column() {
    let e = zedc::format::format_source(b"f(x) = 1;\ng(x) = ;\n").unwrap_err();
    assert!(e.starts_with("2:8: expected "), "{e}");
}
