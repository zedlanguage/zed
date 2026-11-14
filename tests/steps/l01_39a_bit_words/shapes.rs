//! The shapes of program that the benchmarks of `bench::scaling` check at `k` and `8k`: nests,
//! chains and hubs of tests, and blocks of tested lets. Each shape's builder is here with a small
//! instance of it among the correctness tests, which checks its verdict and, for a rejection,
//! the tests its notes name.

use num_bigint::BigInt;
use num_traits::One;
use zed_kernel::{Prim, Value};
use zed_tests::scaling;

/// `x = bitAnd(bitAnd(…bitAnd(1, 1)…, 1), 1);`, `n` calls deep.
pub(super) fn nest_of_bit_and(n: usize) -> String {
    with_main(format!(
        "x = {}1{};\n",
        "bitAnd(".repeat(n),
        ", 1)".repeat(n)
    ))
}

/// `y0 = 255; y1 = bitXor(shr(y0, 1), 3); …`, `n` bindings each a call on the one before.
pub(super) fn chain_of_bit_xor(n: usize) -> String {
    let mut src = String::from("y0 = 255;\n");
    for i in 1..=n {
        src.push_str(&format!("y{i} = bitXor(shr(y{}, 1), 3);\n", i - 1));
    }
    with_main(src)
}

/// `x = 3^e + 5^e;`, with `x` read by nothing.
pub(super) fn unread_constant(e: usize) -> String {
    with_main(format!("x = 3^{e} + 5^{e};\n"))
}

/// `f(n) = if n >= 0 { popCount(n) + if n >= 1 { popCount(n) + … } else { 0 } } else { 0 }`,
/// `n` tests deep, a bit word read in each arm.
pub(super) fn nest_of_tests(n: usize) -> String {
    let mut body = String::from("0");
    for i in (0..n).rev() {
        body = format!("if n >= {i} {{ popCount(n) + {body} }} else {{ 0 }}");
    }
    with_main(format!("f(positional n: int) = {body};\n"))
}

/// `f(n) = n >= 0 && popCount(n) >= 0 && popCount(n) >= 0 && …`, `n` sides after the first.
pub(super) fn chain_of_and(n: usize) -> String {
    let sides = " && popCount(n) >= 0".repeat(n);
    with_main(format!("f(positional n: int) = n >= 0{sides};\n"))
}

/// The test of level `i` of [`nest_of_joins`] read where it holds: `ai >= i + 3 || ai == i`.
pub(super) fn or_test(i: usize) -> String {
    format!("a{i} >= {} || a{i} == {i}", i + 3)
}

/// The test of level `i` of [`nest_of_joins`] read where it fails: `ai < i && ai < i + 3`.
pub(super) fn failing_and_test(i: usize) -> String {
    format!("a{i} < {i} && a{i} < {}", i + 3)
}

/// A device's readings `ai`, each checked against one threshold `n` that is checked first:
/// `if n >= 0 { if ai >= n - 3 { popCount(ai) + … } }`, one level a line.
pub(super) fn nest_under_a_shared_name(k: usize) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let mut body = String::from("0");
    for i in (0..k).rev() {
        body = format!("if a{i} >= n - 3 {{\n  popCount(a{i}) + {body}\n}} else {{ 0 }}");
    }
    with_main(format!(
        "f(\npositional n: int,\n{}\n) =\nif n >= 0 {{\n{body}\n}} else {{ 0 }};\n",
        params.join(",\n")
    ))
}

/// `if n >= -bound(0) { popCount(n) + if n >= -bound(1) { … } else { 0 } } else { 0 }`, `k`
/// levels on the one name `n`, one level a line.
pub(super) fn nest_on_one_name(k: usize, bound: &dyn Fn(usize) -> usize) -> String {
    let mut body = String::from("0");
    for i in (0..k).rev() {
        body = format!(
            "if n >= -{} {{\n  popCount(n) + {body}\n}} else {{ 0 }}",
            bound(i)
        );
    }
    with_main(format!("f(positional n: int) =\n{body};\n"))
}

/// The relations of a reading `a#` to the hub `n` in [`hub`] that carry `n >= -1` to it.
pub(super) const HUB_RELATIONS: [&str; 4] = ["a# >= n", "n <= a#", "a# == n", "a# >= n - 1"];

/// The relations of a reading `a#` to the hub `n` or to the constant 5, in either order.
pub(super) const HUB_OR_RELATIONS: [&str; 2] = ["a# >= n || a# >= 5", "a# >= 5 || a# >= n"];

/// `program` with a `main` that reads none of its bindings.
pub(super) fn with_main(mut program: String) -> String {
    program.push_str("main(m: MainArgs) {\n  m.stdout <- \"\";\n}\n");
    program
}

/// `f(a0, …, a{k-1}) = if <test 0> { popCount(a0) + if <test 1> { … } else { 0 } } else { 0 }`
/// with each test written by `test(i)` on its own name `ai`, or with `holds` false the same
/// nest with the arms swapped, so each read is where the test fails.
pub(super) fn nest_of_joins(k: usize, holds: bool, test: impl Fn(usize) -> String) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let mut body = String::from("0");
    for i in (0..k).rev() {
        let read = format!("popCount(a{i}) + {body}");
        body = match holds {
            true => format!("if {} {{ {read} }} else {{ 0 }}", test(i)),
            false => format!("if {} {{ 0 }} else {{ {read} }}", test(i)),
        };
    }
    with_main(format!("f({}) = {body};\n", params.join(", ")))
}

/// `f(a0, …)` whose `k` arms each read `ai` where `ai >= i || ai <= -(i + 3)` holds, which a
/// test narrows but not to int[0..]: `k` rejections, each under the `k` tests around it.
pub(super) fn nest_of_rejections(k: usize) -> String {
    // One level a line, so each note quotes a line of constant length.
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let mut body = String::from("0");
    for i in (0..k).rev() {
        let test = format!("a{i} >= {i} || a{i} <= -{}", i + 3);
        body = format!("if {test} {{\n  popCount(a{i}) + {body}\n}} else {{ 0 }}");
    }
    with_main(format!("f(\n{}\n) =\n{body};\n", params.join(",\n")))
}

/// The number of notes at a test in the rejection of `src`, and the length of its text.
pub(super) fn test_notes(src: &str) -> (usize, usize) {
    match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => (e.matches("this test is").count(), e.len()),
    }
}

/// `k` readings `ai`, each related to `n` by `rel` (`#` for `i`), nested one level a line in
/// order `order`, and under them `if n >= -1 { popCount(a0) + … }`.
pub(super) fn hub(k: usize, outer: &str, rel: &str, order: &dyn Fn(usize) -> usize) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let reads: Vec<String> = (0..k).map(|i| format!("popCount(a{i})")).collect();
    let mut body = format!("if n >= -1 {{\n  {}\n}} else {{ 0 }}", reads.join(" +\n  "));
    for i in (0..k).rev() {
        let rel = rel.replace('#', &order(i).to_string());
        body = format!("if {rel} {{\n{body}\n}} else {{ 0 }}");
    }
    if !outer.is_empty() {
        body = format!("if {outer} {{\n{body}\n}} else {{ 0 }}");
    }
    with_main(format!(
        "f(\npositional n: int,\npositional m: int,\n{}\n) =\n{body};\n",
        params.join(",\n")
    ))
}

/// `k` tests `ai == n` under the test `n >= 0`, one level a line, then the reads
/// `popCount(ai)` of every reading.
pub(super) fn hub_equal(k: usize) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let reads: Vec<String> = (0..k).map(|i| format!("popCount(a{i})")).collect();
    let mut body = reads.join(" +\n  ");
    for i in (0..k).rev() {
        body = format!("if a{i} == n {{\n{body}\n}} else {{ 0 }}");
    }
    with_main(format!(
        "f(\npositional n: int,\n{}\n) =\nif n >= 0 {{\n{body}\n}} else {{ 0 }};\n",
        params.join(",\n")
    ))
}

/// `k` readings `ai`, each checked against one threshold `n` by `ai >= n`, one level a line,
/// then `m` tests `n >= -j`, each stronger than the one around it, then the reads of the
/// first `reads` readings.
pub(super) fn hub_strengthened(k: usize, m: usize, reads: usize) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let reads: Vec<String> = (0..reads).map(|i| format!("popCount(a{i})")).collect();
    let mut body = reads.join(" +\n  ");
    for j in 1..=m {
        body = format!("if n >= -{j} {{\n{body}\n}} else {{ 0 }}");
    }
    for i in (0..k).rev() {
        body = format!("if a{i} >= n {{\n{body}\n}} else {{ 0 }}");
    }
    with_main(format!(
        "f(\npositional n: int,\n{}\n) =\n{body};\n",
        params.join(",\n")
    ))
}

/// `k` levels, level `i` the test `ai >= n`, then `n >= -(k - i)`, then a read of `ai` added
/// to the level inside it: each test on `n` moves `n` under all the `ai >= n` above it.
pub(super) fn hub_interleaved(k: usize) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let mut body = String::from("0");
    for i in (0..k).rev() {
        body = format!(
            "if a{i} >= n {{\nif n >= -{} {{\npopCount(a{i}) + {body}\n}} else {{ 0 }}\n}} else {{ 0 }}",
            k - i
        );
    }
    with_main(format!(
        "f(\npositional n: int,\n{}\n) =\n{body};\n",
        params.join(",\n")
    ))
}

/// `k` levels `ai >= n && ai >= m`, then `k` tests on `n` and `k` on `m`, each stronger, then
/// one read of `a0`.
pub(super) fn two_hubs(k: usize) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let mut body = String::from("popCount(a0)");
    for j in 1..=k {
        body = format!("if m >= -{j} {{\n{body}\n}} else {{ 0 }}");
    }
    for j in 1..=k {
        body = format!("if n >= -{j} {{\n{body}\n}} else {{ 0 }}");
    }
    for i in (0..k).rev() {
        body = format!("if a{i} >= n && a{i} >= m {{\n{body}\n}} else {{ 0 }}");
    }
    with_main(format!(
        "f(\npositional n: int,\npositional m: int,\n{}\n) =\n{body};\n",
        params.join(",\n")
    ))
}

#[test]
fn two_hubs_on_one_block_settle_to_the_eager_answer() {
    // Each `ai` is a leaf of a star of two hubs, `n` and `m`, whose other conjuncts are bounds
    // on one hub alone: the answer and the notes are those of the eager scope, `a0` int[-1..]
    // under `a0 >= n` and the strongest test on `n`, which is enough without one on `m`.
    for k in [1, 2, 5] {
        let src = two_hubs(k);
        let e = scaling::on_a_thread(1 << 29, || zedc::run::load(src.as_bytes()).err())
            .expect("a0 may be negative");
        assert!(e.contains(" : int[-1..])`"), "k = {k}:\n{e}");
        assert!(e.contains("if n >= -1 {"), "k = {k}:\n{e}");
        assert_eq!(
            e.matches("this test is true here").count(),
            2,
            "k = {k}:\n{e}"
        );
        assert!(e.contains("if a0 >= n && a0 >= m {"), "k = {k}:\n{e}");
    }
}

/// `k` levels `ai >= n + m`, then `k` tests on `n` and `k` on `m`, each stronger, then one
/// read of `a0`.
pub(super) fn hub_sum(k: usize) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let mut body = String::from("popCount(a0)");
    for j in 1..=k {
        body = format!("if m >= -{j} {{\n{body}\n}} else {{ 0 }}");
    }
    for j in 1..=k {
        body = format!("if n >= -{j} {{\n{body}\n}} else {{ 0 }}");
    }
    for i in (0..k).rev() {
        body = format!("if a{i} >= n + m {{\n{body}\n}} else {{ 0 }}");
    }
    with_main(format!(
        "f(\npositional n: int,\npositional m: int,\n{}\n) =\n{body};\n",
        params.join(",\n")
    ))
}

#[test]
fn a_bound_on_a_sum_of_two_hubs_settles_to_the_eager_answer() {
    // `a0 >= n + m` with `n >= -1` and `m >= -1`: `a0` is int[-2..]. The notes name every
    // test the bound rests on (DESIGN step L1.29): the sum, `m >= -1`, which the relation
    // carried to `a0` by the sum, and `n >= -1`, the product of `n` the sum was read with,
    // which lies below the sum and was missing (item NARROW-notes-name).
    for k in [1, 2, 5] {
        let src = hub_sum(k);
        let e = scaling::on_a_thread(1 << 29, || zedc::run::load(src.as_bytes()).err())
            .expect("a0 may be negative");
        assert!(e.contains(" : int[-2..])`"), "k = {k}:\n{e}");
        sum_notes(&e, &format!("k = {k}"));
    }
}

/// The notes of a read of `a0` under `a0 >= n + m` and the tests `n >= -j`, `m >= -j` of
/// [`hub_sum`]: the sum and the strongest test on each hub, each once. The weaker tests
/// `n >= -2`, `m >= -2`, … are not listed: the sum gives `a0` its product from those of `n`
/// and `m` where `m >= -1` is, and `m >= -1` alone gives `m` its product there.
pub(super) fn sum_notes(e: &str, what: &str) {
    notes_are(e, &["a0 >= n + m", "n >= -1", "m >= -1"], what);
}

/// Asserts that the notes of `e` list exactly the tests `tests`, each once.
pub(super) fn notes_are(e: &str, tests: &[&str], what: &str) {
    for t in tests {
        assert_eq!(
            e.matches(&format!("if {t} {{")).count(),
            1,
            "{what}, {t}:\n{e}"
        );
    }
    assert_eq!(
        e.matches("this test is true here").count(),
        tests.len(),
        "{what}:\n{e}"
    );
}

#[test]
fn a_bound_on_a_sum_of_any_signs_or_a_wider_coefficient_settles_to_the_eager_answer() {
    // With `n >= -1` and `m` in [-1, 1]. A sum with a coefficient of two stays a written
    // constraint and pins `a0`; the others are the relation's alone.
    for (test, low) in [
        ("a0 >= n - m", -2),
        ("a0 + m >= n", -2),
        ("a0 >= n + n + m", -3),
    ] {
        let src = with_main(format!(
            "f(\npositional n: int,\npositional m: int,\npositional a0: int\n) =\n\
             if {test} {{\nif n >= -1 {{\nif m <= 1 {{\nif m >= -1 {{\npopCount(a0)\n\
             }} else {{ 0 }}\n}} else {{ 0 }}\n}} else {{ 0 }}\n}} else {{ 0 }};\n"
        ));
        let e = zedc::run::load(src.as_bytes())
            .err()
            .expect("a0 may be negative");
        assert!(e.contains(&format!(" : int[{low}..])`")), "{test}:\n{e}");
        assert!(e.contains(&format!("if {test} {{")), "{test}:\n{e}");
    }
}

/// `link` above `k` levels `ai >= n && ai >= m` (or `ai >= n + m` with `sum`), then `k` tests
/// on `n` and `k` on `m`, each stronger, then one read of `a0`.
pub(super) fn related_hubs(k: usize, link: &str, sum: bool) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let mut body = String::from("popCount(a0)");
    for j in 1..=k {
        body = format!("if m >= -{j} {{\n{body}\n}} else {{ 0 }}");
    }
    for j in 1..=k {
        body = format!("if n >= -{j} {{\n{body}\n}} else {{ 0 }}");
    }
    for i in (0..k).rev() {
        body = match sum {
            false => format!("if a{i} >= n && a{i} >= m {{\n{body}\n}} else {{ 0 }}"),
            true => format!("if a{i} >= n + m {{\n{body}\n}} else {{ 0 }}"),
        };
    }
    body = format!("if {link} {{\n{body}\n}} else {{ 0 }}");
    with_main(format!(
        "f(\npositional n: int,\npositional m: int,\n{}\n) =\n{body};\n",
        params.join(",\n")
    ))
}

#[test]
fn related_hubs_settle_to_the_eager_answer() {
    // A test among the hubs, `n` and `m`, above the stars of the `ai`: each `ai` is still a
    // star's leaf, projected with that test ([`Conjuncts::core`]), and the answer is the eager
    // scope's. With `n + m >= 0` a box of the hubs' bounds would give `a0` int[-1..]; the
    // test among them gives int[0..].
    for k in [1, 2, 5] {
        for (link, low, sum_low) in [
            ("n >= m", Some(-1), Some(-2)),
            ("m >= n", Some(-1), Some(-2)),
            ("n == m", Some(-1), Some(-2)),
            ("n - m <= 2", Some(-1), Some(-2)),
            ("n >= m && m >= n - 4", Some(-1), Some(-2)),
            ("n >= m + 3", None, None),
            ("n + m >= 0", None, None),
        ] {
            for (sum, low) in [(false, low), (true, sum_low)] {
                let src = related_hubs(k, link, sum);
                let e = scaling::on_a_thread(1 << 29, || zedc::run::load(src.as_bytes()).err());
                let Some(low) = low else {
                    assert_eq!(e, None, "k = {k}, {link}, sum {sum}");
                    continue;
                };
                let e =
                    e.unwrap_or_else(|| panic!("k = {k}, {link}, sum {sum}: a0 may be negative"));
                assert!(
                    e.contains(&format!(" : int[{low}..])`")),
                    "k = {k}, {link}, sum {sum}:\n{e}"
                );
                let test = if sum {
                    "a0 >= n + m"
                } else {
                    "a0 >= n && a0 >= m"
                };
                // Exactly the tests the bound rests on are named (DESIGN step L1.29): the
                // star's test, `n >= -1`, and with the sum the bound on `m`, from `m >= -1`
                // or, where the link bounds `m` by `n`, from the link, which carried
                // `n >= -1` to `m`. Not `m >= -2`, nor `n - m <= 2`, which carried `n >= -1`
                // to `m` above `m >= -1`: `m >= -1` alone gives `m` its product there.
                let m_by_n = matches!(link, "m >= n" | "n == m");
                let tests: &[&str] = match (sum, m_by_n) {
                    (false, _) => &[test, "n >= -1"],
                    (true, true) => &[test, "n >= -1", link],
                    (true, false) => &[test, "n >= -1", "m >= -1"],
                };
                notes_are(&e, tests, &format!("k = {k}, {link}, sum {sum}"));
            }
        }
    }
}

#[test]
fn a_longer_path_names_the_tests_that_bound_a_name() {
    // `n >= -1` moves `x` through the relation. The shortest path from `n` to `x` is the test
    // that reads both, `x <= n + 100`, which gives `x` no lower bound; `y >= n` then `x >= y`
    // give it int[-1..]. The notes listed `n >= -1` and `x <= n + 100`, and neither test the
    // bound rests on (item NARROW-eager-scope). Each order of the three tests above.
    let tests = ["x <= n + 100", "y >= n", "x >= y"];
    for (a, b, c) in [(0, 1, 2), (1, 2, 0), (2, 0, 1), (0, 2, 1)] {
        let (a, b, c) = (tests[a], tests[b], tests[c]);
        let src = with_main(format!(
            "f(\npositional n: int,\npositional y: int,\npositional x: int\n) =\n\
             if {a} {{\nif {b} {{\nif {c} {{\nif n >= -1 {{\npopCount(x)\n\
             }} else {{ 0 }}\n}} else {{ 0 }}\n}} else {{ 0 }}\n}} else {{ 0 }};\n"
        ));
        let e = zedc::run::load(src.as_bytes())
            .err()
            .expect("x may be negative");
        assert!(e.contains(" : int[-1..])`"), "{a}, {b}, {c}:\n{e}");
        notes_are(
            &e,
            &["n >= -1", "y >= n", "x >= y"],
            &format!("{a}, {b}, {c}"),
        );
    }
}
/// A chain `w1 <= n + 1` … `wk <= w(k-1) + 1`, then `x <= wk + 100`, which reaches `x` from `n`
/// in `k + 1` tests and gives it no lower bound; a chain `y1 >= n` … `y(k+1) >= yk`, one test
/// longer; then `x >= y(k+1)` and `k` tests `x <= y(k+1) + i` below it; then `n >= -1` and a
/// read of `x`. The `k + 1` tests that read `x` and `y(k+1)` are each reached from `n` by a
/// path of `k + 2` tests, and only `x >= y(k+1)` gives `x` its lower bound.
pub(super) fn longer_paths(k: usize) -> String {
    let mut src = String::from("f(\npositional n: int,\npositional x: int");
    for i in 1..=k {
        src.push_str(&format!(",\npositional w{i}: int"));
    }
    for i in 1..=k + 1 {
        src.push_str(&format!(",\npositional y{i}: int"));
    }
    src.push_str("\n) =\n");
    let mut from = String::from("n");
    for i in 1..=k {
        src.push_str(&format!("if w{i} <= {from} + 1 {{\n"));
        from = format!("w{i}");
    }
    src.push_str(&format!("if x <= {from} + 100 {{\n"));
    let mut from = String::from("n");
    for i in 1..=k + 1 {
        src.push_str(&format!("if y{i} >= {from} {{\n"));
        from = format!("y{i}");
    }
    src.push_str(&format!("if x >= {from} {{\n"));
    for i in 1..=k {
        src.push_str(&format!("if x <= {from} + {i} {{\n"));
    }
    src.push_str("if n >= -1 {\npopCount(x)\n} else { 0 }\n");
    for _ in 0..3 * k + 3 {
        src.push_str("} else { 0 }\n");
    }
    src.push_str(";\n");
    with_main(src)
}

/// A block of `d` bindings `x_k = x_(k-1) + 1` from `x_0 = n`, each tested by `x_k >= k`, which
/// holds where `n >= 0`, with a bit word on `n` in its arm.
pub(super) fn tested_let_chain(d: usize) -> String {
    let mut s = String::from("x0 = n; s0 = 0; ");
    for k in 1..=d {
        let j = k - 1;
        s += &format!(
            "x{k} = x{j} + 1; s{k} = s{j} + (if x{k} >= {k} {{ popCount(n) }} else {{ 0 }}); "
        );
    }
    format!("f(positional n: int) = {{ {s}s{d} }};\n")
}

/// A block of `d` bindings `x_k = x_(k-1) + 1` from `x_0 = v`, where `v is int` has narrowed
/// the parameter `v`, then one test `x_d >= d`, which holds where `v >= 0`, and in its arm a
/// bit word on each `x_k`, the first binding first or the last first. Each read is accepted
/// only through the summary of `x_k` over the narrowed `v` (item PA-let-narrow: a parameter
/// narrowed by `is` has summaries, and a name read under a test of a name over the same input
/// is narrowed by its summary).
pub(super) fn read_let_chain(d: usize, last_first: bool) -> String {
    let mut s = String::from("x0 = v; ");
    for k in 1..=d {
        s += &format!("x{k} = x{} + 1; ", k - 1);
    }
    let mut reads: Vec<usize> = (1..=d).collect();
    if last_first {
        reads.reverse();
    }
    let mut body = String::from("t0 = 0; ");
    for (i, k) in reads.iter().enumerate() {
        body += &format!("t{} = t{i} + popCount(x{k}); ", i + 1);
    }
    format!(
        "f(positional v: int | String) =\n  \
         if v is int {{ {s}if x{d} >= {d} {{ {body}t{d} }} else {{ 0 }} }} else {{ 0 }};\n"
    )
}

/// A block of `d` bindings over two inputs, `x_0 = n + m`, then `x_k = x_(k-1) + n` and
/// `x_k = x_(k-1) + m` in turn, where a test has bounded `m` to `0..=5`; each `x_k = a n + b m`
/// is tested by `x_k >= 5 b`, which holds where `n >= 0`, with a bit word on `n` in its arm.
pub(super) fn two_input_chain(d: usize) -> String {
    let mut b = 1u64;
    let mut s = String::from("x0 = n + m; s0 = 0; ");
    for k in 1..=d {
        let j = k - 1;
        let add = if k % 2 == 1 { "n" } else { "m" };
        if k % 2 == 0 {
            b += 1;
        }
        let at_least = 5 * b;
        s += &format!(
            "x{k} = x{j} + {add}; \
             s{k} = s{j} + (if x{k} >= {at_least} {{ popCount(n) }} else {{ 0 }}); "
        );
    }
    format!(
        "f(positional n: int, positional m: int) =\n  \
         if m >= 0 && m <= 5 {{ {s}s{d} }} else {{ 0 }};\n"
    )
}

/// The nodes `LetPa::sum` enters while the program `src` is loaded, on this thread.
pub(super) fn sum_nodes(src: &str) -> u64 {
    let before = zedc::store::preimage::counts::sum_nodes();
    if let Err(e) = zedc::run::load(src.as_bytes()) {
        panic!("rejected: {e}");
    }
    zedc::store::preimage::counts::sum_nodes() - before
}

/// The probe of item PA-let-multi: `x_0 = n`, then `q_k = n mod 4; x_k = x_(k-1) + q_k` for `k`
/// up to `d`, and one test `x_d >= 3 d`, which holds only where `n >= 0`, with a bit word on
/// `n` in its arm.
pub(super) fn remainder_chain(d: usize) -> String {
    let mut s = String::from("x0 = n; ");
    for k in 1..=d {
        s += &format!("q{k} = n mod 4; x{k} = x{} + q{k}; ", k - 1);
    }
    format!(
        "f(positional n: int) =\n  {{ {s}if x{d} >= {} {{ popCount(n) }} else {{ 0 }} }};\n",
        3 * d
    )
}

/// The bounds of terms of sums taken while the program `src` is loaded, on this thread.
pub(super) fn term_bounds(src: &str) -> u64 {
    let before = zedc::store::preimage::counts::term_bounds();
    if let Err(e) = zedc::run::load(src.as_bytes()) {
        panic!("rejected: {e}");
    }
    zedc::store::preimage::counts::term_bounds() - before
}

/// The probe of item PA-let-narrow-many: `x_0 = n`, then for `k` up to `d` a test that narrows
/// one input, `q_k = n mod 4` to `q_k >= 1` or the parameter `a_k` to `1..=3`, and under it
/// `x_k = x_(k-1) + q_k` (or `+ a_k`); then one test `x_d >= 3 d`, with a bit word on `n` in
/// its arm.
pub(super) fn nested_chain(d: usize, params: bool) -> String {
    let mut s = String::from("x0 = n; ");
    let mut close = String::new();
    for k in 1..=d {
        if params {
            s += &format!("if a{k} >= 1 && a{k} <= 3 {{ x{k} = x{} + a{k}; ", k - 1);
        } else {
            s += &format!("q{k} = n mod 4; if q{k} >= 1 {{ x{k} = x{} + q{k}; ", k - 1);
        }
        close += " } else { 0 }";
    }
    let ps: String = if params {
        (1..=d).map(|k| format!(", positional a{k}: int")).collect()
    } else {
        String::new()
    };
    format!(
        "f(positional n: int{ps}) =\n  {{ {s}if x{d} >= {} {{ popCount(n) }} else {{ 0 }}{close} }};\n",
        3 * d
    )
}

/// Parameters `x_1 … x_k`, each tested to `0..=1`, then `z = x_1 + … + x_k` and `k` nested
/// tests `z >= i`, with a bit word on `x_1` in the innermost arm.
pub(super) fn tests_of_one_sum(k: usize) -> String {
    let ps: String = (1..=k).map(|i| format!("positional x{i}: int, ")).collect();
    let mut s = String::new();
    for i in 1..=k {
        s += &format!("if x{i} >= 0 && x{i} <= 1 {{ ");
    }
    let sum: Vec<String> = (1..=k).map(|i| format!("x{i}")).collect();
    s += &format!("z = {}; ", sum.join(" + "));
    for i in 1..=k {
        s += &format!("if z >= {i} {{ ");
    }
    s += "popCount(x1)";
    for i in (1..=k).rev() {
        s += &format!(" }} else {{ {i} }}");
    }
    for _ in 1..=k {
        s += " } else { 0 }";
    }
    format!("f({}) =\n  {s};\n", ps.trim_end_matches(", "))
}

/// `k` levels `if ai >= n && ai >= m { … } else { arm(i) }`, the innermost body `0`: each
/// then-arm makes `ai` the leaf of a star of the two hubs `n` and `m`, and each else-arm makes
/// it a satellite of them, `ai >= n && ai < m` in one of its cases ([`Conjuncts::star`]).
pub(super) fn negated_hub_nest(k: usize, arm: impl Fn(usize) -> String) -> String {
    let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
    let mut body = String::from("0");
    for i in (0..k).rev() {
        body = format!(
            "if a{i} >= n && a{i} >= m {{\n{body}\n}} else {{ {} }}",
            arm(i)
        );
    }
    with_main(format!(
        "f(\npositional n: int,\npositional m: int,\n{}\n) =\n{body};\n",
        params.join(",\n")
    ))
}

// The small instances of the benchmarks of `bench::scaling`: each shape at `k` from 1 to 3,
// with its verdict and, for a rejection, the count of its notes or the tests they name.

/// Loads `src` on a stack that holds its nest and returns the rejection, or `None`.
fn rejection(src: &str) -> Option<String> {
    let src = src.to_owned();
    scaling::on_a_thread(1 << 29, move || {
        zedc::run::load(src.as_bytes()).err().map(|e| e.to_string())
    })
}

#[test]
fn the_accepted_shapes_are_accepted_at_small_sizes() {
    for k in 1..=3 {
        let shapes: [(&str, String); 11] = [
            ("nest_of_bit_and", nest_of_bit_and(k)),
            ("chain_of_bit_xor", chain_of_bit_xor(k)),
            ("unread_constant", unread_constant(k)),
            ("nest_of_tests", nest_of_tests(k)),
            ("chain_of_and", chain_of_and(k)),
            ("or_test", nest_of_joins(k, true, or_test)),
            (
                "failing_and_test",
                nest_of_joins(k, false, failing_and_test),
            ),
            ("hub_equal", hub_equal(k)),
            (
                "negated_hub_nest",
                negated_hub_nest(k, |i| format!("#s{i}")),
            ),
            ("tested_let_chain", super::program(&tested_let_chain(k))),
            ("two_input_chain", super::program(&two_input_chain(k))),
        ];
        for (what, src) in shapes {
            if let Some(e) = rejection(&src) {
                panic!("{what}, k = {k}: rejected\n{src}\n{e}");
            }
        }
        for last_first in [false, true] {
            let src = super::program(&read_let_chain(k, last_first));
            if let Some(e) = rejection(&src) {
                panic!("read_let_chain, last first {last_first}, k = {k}: rejected\n{e}");
            }
        }
    }
}

#[test]
fn an_unread_constant_of_a_large_exponent_is_accepted() {
    // The size `bench::scaling::a_constant_no_bit_word_reads_is_not_folded` starts at.
    assert_eq!(rejection(&unread_constant(200_000)), None);
}

#[test]
fn each_rejection_of_the_noted_shapes_names_its_own_tests() {
    // The count of notes of `bench::scaling`'s `check_notes` families at small sizes: `per`
    // tests named for each of the `k` reads.
    for k in 1..=3 {
        let mut shapes: Vec<(String, usize, String)> = vec![
            ("nest_of_rejections".into(), 2, nest_of_rejections(k)),
            (
                "nest_under_a_shared_name".into(),
                2,
                nest_under_a_shared_name(k),
            ),
            (
                "weaker tests on n".into(),
                1,
                nest_on_one_name(k, &|i| i + 1),
            ),
            (
                "stronger tests on n".into(),
                1,
                nest_on_one_name(k, &|i| k - i),
            ),
            (
                "reverse order".into(),
                2,
                hub(k, "", "a# >= n", &|i| k - 1 - i),
            ),
            ("through m".into(), 3, hub(k, "m == n", "a# == m", &|i| i)),
            ("hub_strengthened".into(), 2, hub_strengthened(k, k, k)),
            ("hub_interleaved".into(), 2, hub_interleaved(k)),
        ];
        for rel in HUB_RELATIONS {
            shapes.push((rel.into(), 2, hub(k, "", rel, &|i| i)));
        }
        for (what, per, src) in shapes {
            let (notes, _) = scaling::on_a_thread(1 << 29, || test_notes(&src));
            assert_eq!(notes, per * k, "{what}, k = {k}\n{src}");
        }
    }
}

#[test]
fn readings_related_to_a_hub_or_a_constant_are_each_rejected_as_int_from_minus_one() {
    for k in 1..=3 {
        for rel in HUB_OR_RELATIONS {
            let e = rejection(&hub(k, "", rel, &|i| i)).expect("rejected");
            assert_eq!(
                e.matches(" : int[-1..])`").count(),
                k,
                "{rel}, k = {k}\n{e}"
            );
        }
    }
}

#[test]
fn the_rejected_shapes_are_rejected_at_small_sizes() {
    for k in 1..=3 {
        let shapes: [(&str, String); 7] = [
            ("hub_strengthened(k, k, 1)", hub_strengthened(k, k, 1)),
            ("two_hubs", two_hubs(k)),
            ("hub_sum", hub_sum(k)),
            ("related_hubs", related_hubs(k, "n >= m", false)),
            ("related_hubs, sum", related_hubs(k, "n >= m", true)),
            ("a link among sums", related_hubs(k, "m >= n", true)),
            (
                "negated_hub_nest with reads",
                negated_hub_nest(k, |i| format!("popCount(a{i})")),
            ),
        ];
        for (what, src) in shapes {
            assert!(
                rejection(&src).is_some(),
                "{what}, k = {k}: accepted\n{src}"
            );
        }
    }
}

#[test]
fn the_longer_paths_to_a_name_name_the_tests_that_bound_it() {
    // The correctness half of `bench::scaling::the_longer_paths_to_a_name_are_searched_in_linear_time`.
    let e = rejection(&longer_paths(3)).expect("x may be negative");
    assert!(e.contains(" : int[-1..])`"), "{e}");
    let tests = [
        "n >= -1", "y1 >= n", "y2 >= y1", "y3 >= y2", "y4 >= y3", "x >= y4",
    ];
    notes_are(&e, &tests, "k = 3");
    for k in 1..=2 {
        assert!(rejection(&longer_paths(k)).is_some(), "k = {k}: accepted");
    }
}

#[test]
fn the_let_chains_form_their_summaries_and_bounds() {
    // The counts `bench::scaling` holds linear, nonzero at small sizes.
    for d in 1..=3 {
        let count =
            |f: fn(&str) -> u64, src: String| scaling::on_a_thread(1 << 29, move || f(&src));
        assert!(
            count(sum_nodes, super::program(&read_let_chain(d, true))) > 0,
            "d = {d}"
        );
        assert!(
            count(sum_nodes, super::program(&two_input_chain(d))) > 0,
            "d = {d}"
        );
        assert!(
            count(term_bounds, super::program(&remainder_chain(d))) > 0,
            "d = {d}"
        );
        for params in [false, true] {
            let src = super::program(&nested_chain(d, params));
            assert!(count(term_bounds, src) > 0, "parameters {params}, d = {d}");
        }
        assert!(
            count(term_bounds, super::program(&tests_of_one_sum(d))) > 0,
            "d = {d}"
        );
    }
}

#[test]
fn the_bit_words_on_operands_of_several_limbs_agree_with_the_written_out_value() {
    // The benchmarks of the bit words run on operands of 65,536 bits and more; here operands of
    // five limbs, against `BigInt`.
    let a = (BigInt::one() << 300u32) - BigInt::from(12_345_678_901u64);
    let b = (BigInt::one() << 299u32) + BigInt::from(987_654_321u64);
    let word = |p: Prim, args: &[Value]| zed_kernel::bits::word(p, args).expect("defined");
    let (va, vb) = (Value::int(a.clone()), Value::int(b.clone()));
    assert_eq!(
        word(Prim::BitAnd, &[va.clone(), vb.clone()]),
        Value::int(&a & &b)
    );
    assert_eq!(
        word(Prim::BitOr, &[va.clone(), vb.clone()]),
        Value::int(&a | &b)
    );
    assert_eq!(
        word(Prim::BitXor, &[va.clone(), vb.clone()]),
        Value::int(&a ^ &b)
    );
    assert_eq!(
        word(Prim::PopCount, std::slice::from_ref(&va)),
        Value::Int(a.magnitude().count_ones() as i64)
    );
    // `shl(3, 2^70)` is kept as its exponent, so it is built without its 2^70 digits.
    word(
        Prim::Shl,
        &[Value::Int(3), Value::int(BigInt::one() << 70u32)],
    );
}
