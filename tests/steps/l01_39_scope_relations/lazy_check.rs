//! The checker's reads of a lazy scope against the same reads of a copy settled at every name,
//! which holds the eager products (the author's rule of 2026-11-28: lazy and eager give the
//! same result in every case; only the cost may differ). With `lazy_check` on, each image
//! `Ck::with_bound_read` reads for a summarized binding is read again from the settled copy,
//! and the two are compared. Each program here is checked whole by `zedc::run::load`.

use zedc::store::product::lazy_check;

/// `f(x: int, n: int, m: int)` of body `body` under the nested tests `tests`, each `else` 0,
/// with a `main` that does nothing.
fn program(tests: &[&str], body: &str) -> String {
    let open: String = tests.iter().map(|t| format!("if {t} {{ ")).collect();
    let close = "} else { 0 } ".repeat(tests.len());
    format!(
        "f(x: int, n: int, m: int) =\n  {open}{body} {close};\nmain(a: MainArgs) {{\n  a.stdout <- \"\";\n}}\n"
    )
}

/// The reads compared and the differences found while `src` is checked; `src` is accepted.
fn compared(src: &str) -> (u64, Vec<String>) {
    let (loaded, reads, differences) = checked(src);
    if let Err(e) = loaded {
        panic!("rejected:\n{src}\n{e}");
    }
    (reads, differences)
}

/// The check of `src`, its error as text if rejected, with the reads compared and the
/// differences found meanwhile.
fn checked(src: &str) -> (Result<(), String>, u64, Vec<String>) {
    let src = src.to_string();
    zed_tests::scaling::on_a_thread(1 << 29, move || {
        lazy_check::start();
        let loaded = zedc::run::load(src.as_bytes())
            .map(|_| ())
            .map_err(|e| e.to_string());
        let (reads, differences) = lazy_check::stop();
        (loaded, reads, differences)
    })
}

/// The bounds of the hubs `n` and `m` and the star `x >= n + m`: three names, so the solver
/// projects it and `Scope::extend_path` does not admit it onto a path, and `x` is a leaf of a
/// lazy scope that goes stale when a hub moves (XR-lazy-and-kernel-batch-1 round 4, Gemini
/// A2; with `x >= n`, a path, `x` was never stale).
const STAR: [&str; 5] = ["n >= -20", "n <= 20", "m >= -20", "m <= 20", "x >= n + m"];

/// `x >= n + m` makes `x` a leaf of the hubs `n` and `m`, and `n >= 5`, `m >= 5` move them
/// after; the binding `y = x + 1` is read by the binding `z = y + 1`: `Ck::with_bound_read`
/// binds `y` for `z` from `y`'s summary, and its image must be `[11, ∞)` from both scopes
/// (XR-lazy-and-kernel-batch-1 round 4, Gemini A2 (1)). Round 5: green with the settle of the
/// summary's inputs in `with_bound_read` taken out, since the tests on the path settle `x`
/// before the read; the settle is shown needed by the crate test
/// `check::walk::tests::with_bound_read_settles_a_stale_summary_input`. A binding read
/// only by a call or a test is not bound there, so each program has two (`reads > 0` checks
/// that the comparison ran). Corner cases: the leaf settled before the binding by a test on
/// it, a hub moved twice, a binding of two inputs, and the binding read under a later test.
#[test]
fn a_summarized_binding_of_a_stale_leaf_reads_the_eager_image() {
    let with =
        |more: &[&'static str]| -> Vec<&'static str> { STAR.iter().chain(more).copied().collect() };
    let cases = [
        (
            "the hubs moved",
            program(
                &with(&["n >= 5", "m >= 5"]),
                "{ y = x + 1; z = y + 1; popCount(z - 12) }",
            ),
        ),
        (
            "the leaf read before",
            program(
                &with(&["n >= 5", "m >= 5", "x <= 100"]),
                "{ y = x + 1; z = y + 1; popCount(z - 12) }",
            ),
        ),
        (
            "a hub moved twice",
            program(
                &with(&["n >= 2", "n >= 5", "m >= 5"]),
                "{ y = x + 1; z = y + 1; popCount(z - 12) }",
            ),
        ),
        (
            "two inputs",
            program(
                &with(&["n >= 5", "m >= 5"]),
                "{ y = x + n; z = y + 1; popCount(z - 16) }",
            ),
        ),
        (
            "a later test",
            program(
                &with(&["n >= 5", "m >= 5"]),
                "{ y = x + 1; z = y + 1; if n <= 10 { popCount(z - 12) } else { 0 } }",
            ),
        ),
    ];
    for (what, src) in cases {
        let (reads, differences) = compared(&src);
        assert!(
            differences.is_empty(),
            "{what}: a lazy read differs from the eager one:\n{}\n{src}",
            differences.join("\n")
        );
        assert!(reads > 0, "{what}: no summarized binding read\n{src}");
    }
}

/// XR-lazy-and-kernel-batch-1 round 4, Gemini A2 (2): `y = x + 1` is bound under the star
/// `x >= n + m` before the tests `n >= 5` and `m >= 5`, and read under them through the tuple
/// `z = (y, 0)`, which has no summary: `popCount(z[0] - 11)` is accepted only when `y` is
/// read from a settled `x` (`x >= 10`, so `z[0] >= 11`), and that without the settle in
/// `with_bound_read` it is rejected. Round 5: the checker rejects it with the settle and
/// without it, with "popCount takes x in int[0..]": the part of the tuple is read as `int`,
/// not from `y`'s image. So it cannot show the settle needed; it checks that the error is
/// that one and that no lazy read differs from the settled copy's.
#[test]
fn a_binding_read_under_later_tests_is_rejected_both_ways() {
    let src = program(
        &STAR,
        "{ y = x + 1; if n >= 5 { if m >= 5 { z = (y, 0); popCount(z[0] - 11) } else { 0 } } else { 0 } }",
    );
    let (loaded, _, differences) = checked(&src);
    let e = loaded.expect_err("accepted; the tuple part is read as int");
    assert!(e.contains("popCount"), "another error:\n{e}\n{src}");
    assert!(
        differences.is_empty(),
        "a lazy read differs from the eager one:\n{}\n{src}",
        differences.join("\n")
    );
}
