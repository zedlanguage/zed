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

/// The lines `findings` gives `program` that start with `start`.
fn lines_of(program: &str, start: &str) -> Vec<String> {
    let got = findings(program);
    (got.lines().filter(|l| l.starts_with(start)))
        .map(String::from)
        .collect()
}

/// A class merged into another after a call's signature was kept is finished through the
/// binding of the one to the other (`Ck::finished`): the call `h(x)` keeps `h`'s signature
/// `(y) -> (y, z)` with the class of `z`, which `x + z` then merges into that of `x`, named `T`
/// as `p` ends. The call's signature names `h`'s own variable `T` too; `p`'s, a variable of the
/// function around that the call's signature does not bind, takes another name and prints as
/// `_` (FAIL-check-finished-names-clash).
#[test]
fn a_class_merged_after_a_call_is_finished_as_the_class_it_joined() {
    let program = "p(x, z) = { h = (y) -> (y, z); r = h(x); s = x + z; r };\n";
    let got = findings(program);
    let sig = got.lines().find(|l| l.starts_with("sig p = "));
    assert_eq!(
        sig,
        Some("sig p = (x: T, z: T) -> (T, T) for T in int | f32 | f64 | rat"),
        "{got}"
    );
    let call = got.lines().find(|l| l.starts_with("call \"h(x)\" = "));
    assert_eq!(call, Some("call \"h(x)\" = (T) -> (T, _)"), "{got}");
    assert!(!got.lines().any(|l| l.starts_with("err ")), "{got}");
}

/// A call's signature names its own variable and one of the function around apart, though
/// each function named its own `T` (FAIL-check-finished-names-clash): `h`'s `T` stays `T`,
/// and `p`'s, which the signature holds but does not bind, prints as `_`. Before, both were
/// named `T`, and the line read `(T) -> (T, T)`, as if `h` returned its argument twice.
#[test]
fn a_call_keeps_its_own_variable_apart_from_those_of_the_function_around() {
    let calls = |p| lines_of(p, "call ");
    assert_eq!(
        calls("p(x) = { h = (y) -> (y, x); r = h(1); r };\n"),
        ["call \"h(1)\" = (T) -> (T, _)"]
    );
    // The same when `p`'s variable sits inside a tuple, or comes through a name bound to it,
    // or `h` is read again after the call.
    assert_eq!(
        calls("p(x) = { h = (y) -> (y, (x, 1)); r = h(1); r };\n"),
        ["call \"h(1)\" = (T) -> (T, (_, 1))"]
    );
    assert_eq!(
        calls("p(x) = { k = x; h = (y) -> (y, k); r = h(1); r };\n"),
        ["call \"h(1)\" = (T) -> (T, _)"]
    );
    assert_eq!(
        calls("p(x) = { h = (y) -> (y, x); r = h(x); s = h; r };\n"),
        ["call \"h(x)\" = (T) -> (T, _)"]
    );
    // `p` has two variables, `x`'s and `z`'s; the call passes `z`, and `h` holds `x`'s.
    let p = "p(x, z) = { h = (y) -> (y, x); r = h(z); s = x == (z, 1); r };\n";
    assert_eq!(lines_of(p, "sig p = "), ["sig p = (x: T, z: U) -> (U, T)"]);
    assert_eq!(calls(p), ["call \"h(z)\" = (T) -> (T, _)"]);
    // Curried: the first call's signature has two variables of its own, `T` and `U`; the
    // second's has `w`'s, named `T`, and `p`'s, bound in `h(x)`.
    assert_eq!(
        calls("p(x) = { h = (y) -> (w) -> (w, y); r = h(x)((x, 1)); r };\n"),
        [
            "call \"h(x)\" = (T) -> (U) -> (U, T)",
            "call \"h(x)((x, 1))\" = (T) -> (T, _)"
        ]
    );
}

/// A call whose signature has one variable, of the function around, keeps its name: the
/// renaming of [`a_call_keeps_its_own_variable_apart_from_those_of_the_function_around`]
/// touches only a name that two variables share.
#[test]
fn a_call_of_one_variable_keeps_its_name() {
    let p = "p(x) = { h = (y) -> y; r = h(x); r };\n";
    assert_eq!(lines_of(p, "sig p = "), ["sig p = (x: T) -> T"]);
    assert_eq!(lines_of(p, "call "), ["call \"h(x)\" = (T) -> T"]);
}
