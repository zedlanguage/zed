//! Folds whose accumulator type settles only after many rounds of the checker's fixed point
//! (row FAIL-fold-rotating-tuple-rounds): a tuple of n parts whose function rotates it gains
//! `f64` at one more part each round, so its type settles at `(int | f64, ...)` after n
//! rounds, whatever n is. Each expected line is worked by hand: `foldl` with
//! `(a, x) -> (a[1], ..., a[n - 1], a[0])` moves the part at index i to index i - 1 (mod n),
//! so after k entries the 1.5 that starts at index 0 is at index (-k mod n); `foldr` with
//! `(x, a) -> (a[n - 1], a[0], ..., a[n - 2])` moves it to index k mod n.

use super::run;

/// The tuple of `n` parts with `1.5` at index `at` and `0` elsewhere, as zedc prints it.
fn with_one_at(n: usize, at: usize) -> String {
    let parts: Vec<&str> = (0..n).map(|i| if i == at { "1.5" } else { "0" }).collect();
    format!("({})", parts.join(", "))
}

/// The body that folds the 9 entries `[1, ..., 9]` from the tuple of `n` parts that holds
/// `1.5` at index 0, by `foldl` when `left`, else by `foldr`, each rotating the tuple.
fn rotating(n: usize, left: bool) -> String {
    let start = with_one_at(n, 0);
    let entries = "[1, 2, 3, 4, 5, 6, 7, 8, 9]";
    if left {
        let parts: Vec<String> = (0..n).map(|i| format!("a[{}]", (i + 1) % n)).collect();
        format!(
            "${{{entries}.foldl({start}, (a, x) -> ({}))}}",
            parts.join(", ")
        )
    } else {
        let parts: Vec<String> = (0..n).map(|i| format!("a[{}]", (i + n - 1) % n)).collect();
        format!(
            "${{{entries}.foldr((x, a) -> ({}), {start})}}",
            parts.join(", ")
        )
    }
}

#[test]
fn a_rotated_tuple_accumulator_settles_and_runs_at_any_width() {
    for n in [2, 6, 7, 8, 9, 12, 20] {
        for left in [true, false] {
            let body = rotating(n, left);
            let name = format!("rotate_{}_{n}", if left { "foldl" } else { "foldr" });
            let ran = run(&name, &body);
            let at = if left { (9 * (n - 1)) % n } else { 9 % n };
            assert_eq!(
                (ran.status, ran.stdout.trim_end()),
                (0, with_one_at(n, at).as_str()),
                "{name}: {body}\n{}",
                ran.stderr
            );
        }
    }
}

/// Rotations whose parts are tuples, and a result that drops the accumulator, settle: their
/// results keep one skeleton, so the fold's test of growth never refuses them. Worked by
/// hand: rotating `((1.5,), (0,), (0,))` left over 4 entries moves `(1.5,)` from index 0 to
/// index (-4 mod 3) = 2; `(a, x) -> (x, x)` over `[1, 2, 3]` ends at `(3, 3)`.
#[test]
fn a_rotation_of_nested_tuples_and_a_result_without_the_accumulator_settle() {
    for (name, body, expected) in [
        (
            "rotate_nested",
            "${[1, 2, 3, 4].foldl(((1.5,), (0,), (0,)), (a, x) -> (a[1], a[2], a[0]))}",
            "((0,), (0,), (1.5,))",
        ),
        (
            "drops_acc",
            "${[1, 2, 3].foldl(0, (a, x) -> (x, x))}",
            "(3, 3)",
        ),
    ] {
        let ran = run(name, body);
        assert_eq!(
            (ran.status, ran.stdout.trim_end()),
            (0, expected),
            "{name}: {body}\n{}",
            ran.stderr
        );
    }
}
