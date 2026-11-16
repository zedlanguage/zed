//! The census's own work, finding the kinds of n diagnostics and counting them by kind, is O(n)
//! in the diagnostics times the kinds: one pass over each text per kind, and one pass over the
//! census lines per kind for the totals. The checker's work on each unit is measured by the
//! scaling tests of its own steps, and on the form of the census's slowest units by
//! `refused_guarded_divisions_scale_linearly`. The benchmarks of this step, run by
//! `tools/run_tests.sh --bench`. The census check asserts nothing besides its ratio: finding
//! kinds is checked by `kinds_are_found_by_their_phrases`, and the lines and totals by the snapshots.

use super::{kinds, line, refusals, totals};

/// The conditions of units 47, 48 and 49 of piece 4 of `programs.txt` (from
/// `l01_29_diagnostics`): four linear conditions on four integers, which the checker cannot
/// solve exactly, so every division or power under them draws a refusal.
const GUARD: &str = "4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y - \
                     11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && 0 - 8 * w - 5 \
                     * x + 12 * y - z + 31 >= 0";

/// Unit 49's form with `n` functions: each divides under [`GUARD`], one refusal each.
fn guard_functions(n: usize) -> String {
    let mut src = String::new();
    for k in 0..n {
        src += &format!(
            "guard{k}(x: int, y: int, z: int, w: int) = if {GUARD} {{ 100 div x }} else {{ 0 }};\n"
        );
    }
    src + "main() {\n}\n"
}

/// Unit 47's form with `n` names: one function whose body, under [`GUARD`], divides by each of
/// `n` names bound to `a * 2` and `n` times by `a`: one refusal for the conditions, one for each
/// name bound under them and one for each division by `a`.
fn guarded_divisions(n: usize) -> String {
    let mut src = format!(
        "f(a: int, x: int, y: int, z: int, w: int) =\n  if a - w - x - y - z >= 0 && {GUARD} {{\n    {{\n"
    );
    let mut sum = Vec::new();
    for k in 0..n {
        src += &format!("      b{k} = a * 2;\n");
        sum.push(format!("100 div b{k}"));
    }
    sum.extend((0..n).map(|_| "100 div a".to_string()));
    src + &format!(
        "      {}\n    }}\n  }} else {{\n    0\n  }};\nmain() {{\n}}\n",
        sum.join(" + ")
    )
}

/// PERF-check-l01_29-units: the census of units 47 to 49 took 3.8 to 8.9 s each, out of line
/// with their size, but the checker's work on them is linear in the number of refused sites
/// (in this census, about 67 million instructions per guarded function and 13 million per
/// refused site in one function, 2026-11-15, ratios 7.95 and 4.66 at load 68): a unit's time
/// follows its refusals, not its bytes. Each form is held linear here; the constant per refused
/// site is item PERF-refused-site-constant.
#[test]
fn refused_guarded_divisions_scale_linearly() {
    for (what, make) in [
        (
            "census of n guarded functions",
            guard_functions as fn(usize) -> String,
        ),
        (
            "census of one function with 2n guarded sites",
            guarded_divisions,
        ),
    ] {
        let texts = zed_tests::scaling::inputs(4, make);
        let refused = |n: usize| {
            let mut out = String::new();
            refusals("unit", &texts[&n], &mut out);
            out
        };
        let (small, large) = (refused(4), refused(32));
        assert_eq!(
            (small.lines().count(), large.lines().count()),
            if what.contains("sites") {
                (9, 65)
            } else {
                (4, 32)
            },
            "{what}: refusals linear in n:\n{small}"
        );
        zed_tests::scaling::check(what, 4, |n| {
            std::hint::black_box(refused(n));
        });
    }
}

#[test]
fn classifying_and_counting_scale_linearly() {
    let texts = zed_tests::scaling::inputs(200, |n| {
        (0..n)
            .map(|i| {
                let k = &kinds::KINDS[i % kinds::KINDS.len()];
                format!(
                    "unit {i}: the check of `f{i}` was not decided: {}.",
                    k.phrase
                )
            })
            .collect::<Vec<String>>()
    });
    zed_tests::scaling::check("census of n diagnostics", 200, |n| {
        let mut out = String::new();
        for (i, t) in texts[&n].iter().enumerate() {
            line(
                &mut out,
                &format!("u{i}"),
                "1:1",
                "warning",
                &kinds::of(t),
                t,
            );
        }
        std::hint::black_box(totals(&out));
    });
}
