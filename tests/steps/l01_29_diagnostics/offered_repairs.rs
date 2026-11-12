//! Every repair a rejection offers checks as written (items MSG-converted-claims-checked and
//! MSG-suffix-menu-unchecked). Over a grid of one-line programs, each a binding of an
//! operator, a comparison or a call applied to two operands of many kinds, every offered
//! repair is written into the program, and the program it gives has no error: a note
//! "repair: write `t`" puts `t` at the note's place, a note "repair: wrap this in `w(…)`" puts
//! `w(` and `)` around it, and each line of a menu of fixes replaces the source line it
//! corrects.

use zed_tests::step_helpers::l01_26_type_resolution::{info, type_errors};

/// The declarations every program of the grid starts with: values of each carrier, and calls
/// whose types list literal values of two kinds.
const PRELUDE: &str = "gi(positional c: bool) = if c { 1 } else { true };
gf(positional c: bool) = if c { 1 } else { 2.5f64 };
gr(positional c: bool) = if c { 1 } else { 2.5r };
n = 1;
k = 3000000000000;
x = 2.5f64;
r = 2.5r;
s = \"1\";
b = true;
";

const OPERANDS: [&str; 16] = [
    "1", "0.5", "-0.5", "1.5", "2.5r", "1.0f64", "n", "k", "x", "r", "s", "b", "gi(true)",
    "gf(true)", "gr(true)", "-n",
];

/// The one-line programs of the grid, each `y = …;` after the prelude.
fn grid() -> Vec<String> {
    let mut lines = Vec::new();
    for a in OPERANDS {
        for w in ["f64", "int", "rat", "String", "abs"] {
            lines.push(format!("y = {w}({a});"));
        }
        for c in OPERANDS {
            for op in ["+", "-", "*", "/", "==", "!=", "<", "^"] {
                lines.push(format!("y = {a} {op} {c};"));
            }
            lines.push(format!("y = min({a}, {c});"));
        }
    }
    lines
}

/// The number of chars `a` and `b` share at their start and at their end.
fn alike(a: &str, b: &str) -> usize {
    let pre = a.chars().zip(b.chars()).take_while(|(x, y)| x == y).count();
    let suf = (a.chars().rev().zip(b.chars().rev()))
        .take_while(|(x, y)| x == y)
        .count();
    pre + suf
}

/// Each program the repairs offered for `src` give, with the repair it applies.
fn repaired(src: &str) -> Vec<(String, String)> {
    let (i, _) = info(src);
    let mut out = Vec::new();
    for e in &i.errors {
        for note in &e.notes {
            let at = &src[note.span.start..note.span.end];
            let text = if let Some(w) = note.text.strip_prefix("repair: wrap this in `") {
                let w = w.split_once("(…)`").expect("a wrap names its word").0;
                format!("{w}({at})")
            } else if let Some(t) = note.text.strip_prefix("repair: write `") {
                let (t, rest) = t.split_once('`').expect("a rewrite in backquotes");
                // `w(…)` around, or `[i]` after, one operand of the comparison at the note.
                let side = [" left operand", " right operand"].iter().position(|s| {
                    rest.starts_with(&format!(" around the{s}"))
                        || rest.starts_with(&format!(" after the{s}"))
                });
                match side {
                    Some(s) => {
                        let op = [" == ", " != "].into_iter().find(|op| at.contains(op));
                        let (l, r) = at
                            .split_once(op.expect("a comparison"))
                            .expect("two operands");
                        let wrap = |x: &str| match t.strip_suffix("(…)") {
                            Some(w) => format!("{w}({x})"),
                            None => format!("{x}{t}"),
                        };
                        let op = op.expect("a comparison");
                        match s {
                            0 => format!("{}{op}{r}", wrap(l)),
                            _ => format!("{l}{op}{}", wrap(r)),
                        }
                    }
                    None => t.replace("…", at),
                }
            } else {
                continue;
            };
            let fixed = format!("{}{text}{}", &src[..note.span.start], &src[note.span.end..]);
            out.push((fixed, note.text.clone()));
        }
        // Each fix of the menu is the corrected source line, then four spaces or more, then
        // what the program holds; it replaces the source line most like it.
        for fix in e.menu.lines().skip(2) {
            let fix = fix.trim();
            let line = fix.split_once("    ").map_or(fix, |(l, _)| l).trim_end();
            let lines: Vec<&str> = src.lines().collect();
            let Some(at) = (0..lines.len()).max_by_key(|&j| alike(lines[j].trim(), line)) else {
                continue;
            };
            let mut fixed = String::new();
            for (j, l) in lines.iter().enumerate() {
                fixed.push_str(if j == at { line } else { l });
                fixed.push('\n');
            }
            out.push((fixed, format!("menu: {line}")));
        }
    }
    out
}

#[test]
fn every_offered_repair_checks_as_written() {
    assert_eq!(type_errors(PRELUDE), Vec::<String>::new());
    let mut failed = Vec::new();
    let mut tried = 0;
    for line in grid() {
        let src = format!("{PRELUDE}{line}\n");
        for (fixed, repair) in repaired(&src) {
            tried += 1;
            let errors = std::panic::catch_unwind(|| type_errors(&fixed))
                .unwrap_or_else(|_| vec!["not resolved".to_string()]);
            if !errors.is_empty() {
                failed.push(format!(
                    "{line}\n  {repair}\n  -> {}",
                    errors.join("\n     ")
                ));
            }
        }
    }
    eprintln!("{tried} repairs tried, {} fail", failed.len());
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// Each offered repair of a construct inside another, `y = (a op c) + d` and
/// `y = min(a op c, d)`, as written: the program it gives has fewer errors than the program
/// had, so the repair fixes its own rejection and adds no error, in the construct around it
/// either, as `min(1.0r, 0.5r) + 2.5f64` would. A program can hold two rejections, one in
/// each construct, so one repair need not leave no error. The operands `-0.5` and `-n` put a
/// `-` between the two constructs. One test per outer construct keeps each under the time
/// limit.
fn nested_repairs_check(outer: fn(&str, &str) -> String) {
    let mut failed = Vec::new();
    let mut tried = 0;
    for a in OPERANDS {
        for c in OPERANDS {
            for op in ["+", "/", "^"] {
                for d in ["2.5f64", "2.5r", "1", "n"] {
                    let line = outer(&format!("{a} {op} {c}"), d);
                    let src = format!("{PRELUDE}{line}\n");
                    let before = type_errors(&src).len();
                    for (fixed, repair) in repaired(&src) {
                        tried += 1;
                        let errors = std::panic::catch_unwind(|| type_errors(&fixed))
                            .unwrap_or_else(|_| vec!["not resolved".to_string(); before]);
                        if errors.len() >= before {
                            failed.push(format!(
                                "{line}\n  {repair}\n  -> {}",
                                errors.join("\n     ")
                            ));
                        }
                    }
                }
            }
        }
    }
    eprintln!("{tried} repairs tried, {} fail", failed.len());
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

#[test]
fn every_offered_repair_inside_a_sum_checks_as_written() {
    nested_repairs_check(|inner, d| format!("y = ({inner}) + {d};"));
}

#[test]
fn every_offered_repair_inside_a_call_checks_as_written() {
    nested_repairs_check(|inner, d| format!("y = min({inner}, {d});"));
}

/// The message, the menu and the repair notes of each error of `src`, one string.
fn offered(src: &str) -> String {
    let (i, _) = info(src);
    let mut out = String::new();
    for e in &i.errors {
        out.push_str(&e.message);
        out.push_str(&e.menu);
        for n in e.notes.iter().filter(|n| n.text.starts_with("repair:")) {
            out.push('\n');
            out.push_str(&n.text);
        }
        out.push('\n');
    }
    out
}

const GI: &str = "gi(positional c: bool) = if c { 1 } else { true };\n";
const GR: &str = "gr(positional c: bool) = if c { 1r } else { true };\n";

/// The menu of a literal with a suffix: `y = 1.0 + gr(true)` and `y = 1.0r + gr(true)` do not
/// check, as `gr(true)` may be `true`, so they are no longer offered, and the message says no
/// fix is; a menu fix that checks is kept.
#[test]
fn a_menu_fix_that_does_not_check_is_dropped() {
    for line in ["y = 1.0f64 + gr(true);", "y = min(1.0f64, gr(true));"] {
        let got = offered(&format!("{GR}{line}"));
        assert!(!got.contains("gr(true);    "), "{got}");
        assert!(
            got.contains("No fix is offered: each one the checker tried is rejected too."),
            "{got}"
        );
    }
    let got = offered("y = 1.5f64 + 2r;");
    assert!(got.contains("Try `y = 1.5 + 2r` instead."), "{got}");
    assert!(!got.contains("No fix is offered"), "{got}");
}

/// A literal rewritten at another carrier: `2.5` in `1 ^ 2.5r` makes `1 ^ 2.5`, which has no
/// type until its value meets a carrier, so the repair writes `2.5f64`; `2.5` in `x ^ 2.5r`
/// and `2.0` in `1.5f64 + 2r` check and are kept.
#[test]
fn a_literal_repair_is_written_as_it_checks() {
    let got = offered("y = 1 ^ 2.5r;");
    assert!(got.contains("repair: write `2.5f64`"), "{got}");
    assert!(!got.contains("repair: write `2.5`;"), "{got}");
    let got = offered("x = 2.5f64;\ny = x ^ 2.5r;");
    assert!(
        got.contains("repair: write `2.5`; the checker accepts that"),
        "{got}"
    );
    let got = offered("y = 1.5f64 + 2r;");
    assert!(
        got.contains("repair: write `2.0`; the checker accepts that"),
        "{got}"
    );
}

/// The casts of a comparison of two carriers: `int(r)` always fails at `r = 2.5r`, so
/// `n == int(r)` is not offered and `rat(n) == r` is; where no cast checks, as `int(x)` at
/// `x = 2.5f64` beside `gi(true)`, the answer is offered in place of the comparison.
#[test]
fn a_comparison_cast_that_does_not_check_is_dropped() {
    let got = offered("n = 1;\nr = 2.5r;\ny = n == r;");
    assert!(got.contains("repair: write `rat(n) == r`"), "{got}");
    assert!(!got.contains("int(r)"), "{got}");
    let got = offered(&format!("{GI}x = 2.5f64;\ny = x == gi(true);"));
    assert!(!got.contains("int(…)"), "{got}");
    assert!(
        got.contains("repair: write `false` in place of the comparison"),
        "{got}"
    );
}

/// The cast of a value compared with a decimal literal checks as written and is kept:
/// `rat(k)` at a `k` past 2^53, where `f64(k)` would be inexact and is not offered.
#[test]
fn a_cast_beside_a_decimal_that_checks_is_kept() {
    let got = offered("k = 1152921504606846977;\ny = k == 0.5;");
    assert!(got.contains("repair: write `rat(k)`"), "{got}");
    assert!(!got.contains("f64(k)"), "{got}");
    let got = offered("n = 3;\ny = n == 0.5;");
    assert!(got.contains("repair: write `rat(n)`"), "{got}");
}

/// A call with several arguments rejected: each argument's fix is checked with the others
/// left as written, which the call's own check rejects too, so each argument offers its own
/// fix rather than none.
#[test]
fn each_rejected_argument_of_a_call_offers_its_own_fix() {
    let f = "f(positional p0: rat, positional p1: rat, positional p2: rat) = 1;\n";
    let got = offered(&format!("{f}y = f(1.0f64, 1.0f64, 1.0f64);"));
    assert!(!got.contains("No fix is offered"), "{got}");
    assert!(got.contains("y = f(1.0, 1.0f64, 1.0f64);"), "{got}");
    assert!(got.contains("y = f(1.0f64, 1.0, 1.0f64);"), "{got}");
    assert!(got.contains("y = f(1.0f64, 1.0f64, 1.0);"), "{got}");
}

/// A fix of an argument that the call rejects for another argument too: `h(1.0, 0.5f64)`
/// checks once `0.5f64` has its own repair, so the fix of `1.0f64` is kept; where the other
/// argument can never be a `rat`, as `true`, no fix is offered.
#[test]
fn a_fix_beside_another_rejected_argument_is_kept() {
    let h = "h(positional a: rat, positional b: rat) = a + b;\n";
    let got = offered(&format!("{h}y = h(1.0f64, 0.5f64);"));
    assert!(got.contains("Try `y = h(1.0, 0.5f64)` instead."), "{got}");
    let got = offered(&format!("{h}y = h(1.0f64, true);"));
    assert!(got.contains("No fix is offered"), "{got}");
    assert!(!got.contains("h(1.0, true)"), "{got}");
}

/// A fix that leaves its own rejection fixes nothing: `int(n)` in `min(1.0f64, n)` and in
/// `0.5 ^ n` leaves `1.0f64` or `0.5` rejected, so only `f64(n)` is offered.
#[test]
fn a_fix_that_leaves_its_own_rejection_is_dropped() {
    for line in ["y = min(1.0f64, n);", "y = 0.5 ^ n;"] {
        let got = offered(&format!("n = 1;\n{line}"));
        assert!(got.contains("repair: write `f64(n)`"), "{got}");
        assert!(!got.contains("int(n)"), "{got}");
    }
}

/// A fix inside a construct is checked by the construct around it: `min(1.0r, 0.5r)` is a
/// `rat`, which `+ 2.5f64` rejects, so it is dropped there and the note `0.5` is kept; beside
/// `+ 2.5r` it is kept, as is the note `rat(n)` of `(n + r) * 2.5r`.
#[test]
fn a_fix_the_construct_around_it_rejects_is_dropped() {
    let got = offered("y = min(1.0f64, 0.5r) + 2.5f64;");
    assert!(!got.contains("1.0r"), "{got}");
    assert!(got.contains("repair: write `0.5`"), "{got}");
    assert!(!got.contains("No fix is offered"), "{got}");
    let got = offered("y = min(1.0f64, 0.5r) + 2.5r;");
    assert!(
        got.contains("Try `y = min(1.0, 0.5r) + 2.5r` instead."),
        "{got}"
    );
    let got = offered("n = 1;\nr = 2.5r;\ny = (n + r) * 2.5r;");
    assert!(got.contains("repair: write `rat(n)`"), "{got}");
}

/// Where every repair note is dropped, the message says that no fix is offered: `rat(n)` in
/// `(n + r) + 1.0f64` makes a `rat`, which `+ 1.0f64` rejects.
#[test]
fn a_rejection_whose_notes_are_all_dropped_says_so() {
    let got = offered("n = 1;\nr = 2.5r;\ny = (n + r) + 1.0f64;");
    assert!(!got.contains("repair:"), "{got}");
    assert!(got.contains("No fix is offered"), "{got}");
}
