//! A class solved to a carrier when a lambda ends is replaced outside the lambdas it holds
//! and read through the union-find inside them (CHK-carrier, COMPLEXITY.md F77). What the
//! checker finds of the calls, comparisons and messages that read those lambdas is what it
//! found when the class was replaced at every depth: `curried_classes.txt` is the output
//! of that build, this checker with `replace` in place of `replace_outside` in `generalize`.

use super::info;

/// `g` returns two curried lambdas whose parameters take int when each ends: `div` takes only
/// `int`, where `+ 1` would leave each generic (step L1.26a).
const G: &str = "g(positional a0) = (a1) -> (a2) -> (a0 div 1, a1 div 1, a2 div 1);\n";

const PROGRAMS: [&str; 25] = [
    "h = g(0);\nk = h(1);\nm = k(2);\n",
    "take(f: (int) -> (int) -> (int, int, int)) = f(1)(2);\nr = take(f: g(0));\n",
    "take(f: (String) -> (int) -> (int, int, int)) = f(\"a\")(2);\nr = take(f: g(0));\n",
    "h = g(0);\nk = h(\"x\");\n",
    "h = g(0)(1);\nk = h(\"x\");\n",
    "u(n: int) = g(n);\nv(n: int) = u(n)(n)(n);\n",
    "w(f: (int) -> (int) -> (int, int, int)) = f;\nr = w(f: g(0))(1)(2);\n",
    "w(f: (f64) -> (int) -> (int, int, int)) = f;\nr = w(f: g(0));\n",
    "t = (g(0), g(1));\nk = t;\n",
    "c(x: int) = if x > 0 { g(0) } else { g(1) };\nd = c(x: 1)(2)(3);\n",
    "y(q) = g(q)(q);\nz = y(1)(2);\nzz = y(1.5)(2.5);\n",
    "take(f: (int) -> (int) -> (int, int, int)) = f(1)(2);\nr = take(f: (a1) -> (a2) -> (0 + 1, a1 + 1, a2 + 1));\n",
    "k(x: int) = (a) -> (b) -> (x + 1, a div 1, b div 1);\nm(f: (f64) -> (int) -> (int, int, int)) = 0;\nr = m(f: k(x: 1));\n",
    "h = g(0)(1);\nq = h + 1;\n",
    "h = g;\nk = h(0)(\"a\");\n",
    "p(x) = (y) -> x + y;\nq = p(1)(2.5);\n",
    "p(x) = (y) -> (z) -> x + y + z;\nq = p(1)(2)(3);\nr = p(1.5)(2.5)(3.5);\n",
    "p(x) = (y) -> (z) -> (x div 1, y, z);\nq = p(1)(\"s\")(true);\nr = p(1)(2)(3) + 1;\n",
    "o(x) = (y) -> (z) -> x div 1;\nq = o(1)(2)(3) == 2;\nw = (o(1), 0);\n",
    // `is` and `is not` on a tuple that holds such a lambda: the test of the lambda reads
    // its classes as their types, so the branch that cannot be taken narrows to nothing.
    "h = g(0);\nt = (h, 1);\nr = if t is (((int) -> ((int) -> (int, int, int))), int) { 1 } else { t };\n",
    "h = g(0);\nt = (h, 1);\nr = if t is not (((int) -> ((int) -> (int, int, int))), int) { t } else { 2 };\n",
    "h = g(0)(1);\nt = (h, 1);\nr = if t is (((String) -> (int, int, int)), int) { 1 } else { t };\n",
    "f(c: bool) = if c { (g(0)(1), 1) } else { (g(1)(2), 2) };\nt = f(c: true);\nr = if t is (((int) -> (int, int, int)), int) { 1 } else { t };\n",
    "h = g(0)(1);\nt = (h, 1);\nr = if t is ((((int) -> (int, int, int)), int) | int) { 1 } else { t };\n",
    "h = g(0)(1);\nt = ((h, 1), 2);\nr = if t is ((((int) -> (int, int, int)), int), int) { 1 } else { t };\n",
];

/// The signatures, top-level types, call signatures and errors with their notes the checker
/// gives `G` and `program`, one per line in a fixed order.
fn findings(program: &str) -> String {
    let text = format!("{G}{program}");
    let (info, names) = info(&text);
    let mut out = format!("=== {program:?}\n");
    for (k, s) in &info.sigs {
        out += &format!("sig {} = {s}\n", names[*k]);
    }
    let mut tops: Vec<String> = (info.tops.iter())
        .map(|(k, t)| format!("top {k} = {t}\n"))
        .collect();
    tops.sort();
    out.extend(tops);
    let mut calls: Vec<_> = (info.calls.iter())
        .map(|(sp, s)| (sp.start, sp.end, s.to_string()))
        .collect();
    calls.sort();
    for (a, b, s) in calls {
        out += &format!("call {:?} = {s}\n", &text[a..b]);
    }
    for e in &info.errors {
        out += &format!("err {} [{}]\n", e.message, &text[e.span.start..e.span.end]);
        for n in &e.notes {
            out += &format!("  note {}\n", n.text);
        }
    }
    out
}

#[test]
fn lambdas_whose_classes_are_read_inside_check_as_when_replaced_at_every_depth() {
    let got: String = PROGRAMS.iter().map(|p| findings(p)).collect();
    let want = include_str!("curried_classes.txt");
    for (i, (g, w)) in got.lines().zip(want.lines()).enumerate() {
        assert_eq!(g, w, "line {}", i + 1);
    }
    assert_eq!(got.lines().count(), want.lines().count());
}
