//! A term whose parts mixing has made literals is evaluated after mixing (plan row
//! STAGE-refold-mixed). `d && b`, with `d` the build-stage `#divByZero` and `b` read from a
//! port, is the `if d { b } else { false }` the elaborator writes; mixing takes its condition
//! to `#divByZero`, so `!(d && b)` is `!#divByZero`, which the build evaluates as it evaluates
//! any build-stage term. `b && d` keeps `b` first, to be read at run time.

use super::{out, staged, term};

/// `main` writing `${(if e { 1 } else { 0 }) else #divByZero -> 9}`, where `e` is `inner`
/// under `n` `!`s, with `d` the build-stage `#divByZero` and `b` read from `stdin`.
pub(crate) fn nots(n: usize, inner: &str) -> String {
    let e = format!("{}{inner}{}", "!(".repeat(n), ")".repeat(n));
    format!(
        "dz(k: int) = (5 div k) > 0;\n\
         main(m: MainArgs) {{\n  \
         d = dz(k: 0);\n  \
         b = (m.stdin[0] else \"\") == \"t\";\n  \
         m.stdout <- \"${{(if {e} {{ 1 }} else {{ 0 }}) else #divByZero -> 9}}\";\n}}\n"
    )
}

#[test]
fn a_not_of_a_mixed_failure_is_evaluated_at_build() {
    for n in [1, 2, 5] {
        let (p, s, report) = staged(&nots(n, "d && b"));
        let main = term(&s, "main");
        assert!(!main.contains("!#divByZero"), "{n}: {main}");
        assert!(!main.contains("divByZero"), "{n}: {main}");
        assert!(main.contains("\"9\""), "{n}: {main}");
        assert!(report.left.is_empty(), "{n}: {:?}", report.left);
        for input in ["t\n", "f\n", ""] {
            assert_eq!(out(&s, input), out(&p, input), "{n} on {input:?}");
            assert_eq!(out(&s, input), "9\n", "{n} on {input:?}");
        }
    }
}

#[test]
fn a_not_of_a_term_read_at_run_is_kept() {
    // Negative control: `b && d` reads `b` first, so no `!` around it is known at build.
    for n in [1, 2, 5] {
        let (p, s, report) = staged(&nots(n, "b && d"));
        let main = term(&s, "main");
        assert_eq!(main.matches('!').count(), n, "{n}: {main}");
        assert!(main.contains("if b {"), "{n}: {main}");
        assert!(report.left.is_empty(), "{n}: {:?}", report.left);
        // `b` false gives `false`, under `n` `!`s; `b` true gives `#divByZero`.
        let f = if n % 2 == 1 { "1\n" } else { "0\n" };
        for (input, want) in [("t\n", "9\n"), ("f\n", f)] {
            assert_eq!(out(&s, input), out(&p, input), "{n} on {input:?}");
            assert_eq!(out(&s, input), want, "{n} on {input:?}");
        }
    }
}
