//! The words' time against the size of their operands (the rule of low complexity, DESIGN.md
//! Part G). The digit-wise words take time linear in the digits of their operands; the shifts,
//! `bitNot` and the rotations keep a power of two as its exponent, so their time grows with
//! the digits of the count and the width, not with the power. Every operand is built before the
//! timing.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_traits::One;
use zed_kernel::{Prim, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;

/// A random value of `bits` binary digits, its top digit 1.
fn wide(rng: &mut Rng, bits: usize) -> Value {
    let words: Vec<u64> = (0..bits.div_ceil(64)).map(|_| rng.next_u64()).collect();
    let mut n = BigInt::from(num_bigint::BigUint::from_slice(
        &words
            .iter()
            .flat_map(|w| [*w as u32, (*w >> 32) as u32])
            .collect::<Vec<_>>(),
    ));
    n &= (BigInt::one() << bits) - 1;
    n |= BigInt::one() << (bits - 1);
    Value::int(n)
}

fn run(p: Prim, args: &[Value]) {
    zed_kernel::bits::word(p, args).unwrap_or_else(|e| panic!("{p:?}: {e}"));
}

/// The operands of each size, built before the timing.
fn operands(n: usize) -> HashMap<usize, (Value, Value, Value)> {
    let mut rng = Rng::new(n as u64);
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let (a, b) = (wide(&mut rng, m), wide(&mut rng, m));
            (m, (a, b, Value::Int(m as i64)))
        })
        .collect()
}

#[test]
fn the_digit_wise_words_are_linear_in_the_digits() {
    let n = 1 << 16;
    let ops = operands(n);
    scaling::check_order(
        "bitAnd, bitOr, bitXor, popCount, leadingZeros, trailingZeros",
        n,
        1,
        |m| {
            let (a, b, w) = &ops[&m];
            for _ in 0..20 {
                run(Prim::BitAnd, &[a.clone(), b.clone()]);
                run(Prim::BitOr, &[a.clone(), b.clone()]);
                run(Prim::BitXor, &[a.clone(), b.clone()]);
                run(Prim::PopCount, std::slice::from_ref(a));
                run(Prim::LeadingZeros, &[a.clone(), w.clone()]);
                run(Prim::TrailingZeros, &[a.clone(), w.clone()]);
            }
        },
    );
}

#[test]
fn the_shifts_bit_not_and_the_rotations_are_linear_in_the_digits() {
    let n = 1 << 16;
    let ops = operands(n);
    scaling::check_order("shl, shr, bitNot, rotl, rotr", n, 1, |m| {
        let (a, _, w) = &ops[&m];
        let k = Value::Int(m as i64 / 3);
        for _ in 0..20 {
            run(Prim::Shl, &[a.clone(), k.clone()]);
            run(Prim::Shr, &[a.clone(), k.clone()]);
            run(Prim::BitNot, &[a.clone(), w.clone()]);
            run(Prim::Rotl, &[a.clone(), k.clone(), w.clone()]);
            run(Prim::Rotr, &[a.clone(), k.clone(), w.clone()]);
        }
    });
}

#[test]
fn a_shift_by_a_huge_count_keeps_the_power() {
    // `shl(1, k)` is `2^k`, kept as its exponent: the time grows with the digits of `k`.
    let n = 1 << 12;
    scaling::check_order("shl(3, 2^n)", n, 1, |m| {
        let k = Value::int(BigInt::one() << m);
        for _ in 0..20 {
            run(Prim::Shl, &[Value::Int(3), k.clone()]);
        }
    });
}

/// `program` with a `main` that reads none of its bindings.
fn with_main(mut program: String) -> String {
    program.push_str("main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- \"\";\n}\n");
    program
}

/// The work the checker does on each of `src`'s units, at sizes `n` and `8n`, on a stack that
/// holds `8n` levels: the parser and the checker recurse once a level, as step L1.28's tests of
/// deep bodies allow for. Each unit is loaded, then parsed and resolved, before the timing,
/// which takes the checker alone (COMPLEXITY.md F85, its CHECK-scaling-share part).
fn check_alone(what: &'static str, n: usize, power: u32, src: impl Fn(usize) -> String) {
    let srcs: HashMap<usize, String> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, src(m)))
        .collect();
    let t = std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(move || {
            let units: HashMap<usize, _> = srcs
                .iter()
                .map(|(&m, text)| {
                    zedc::run::load(text.as_bytes()).unwrap_or_else(|e| panic!("{e}"));
                    (m, zed_tests::deep::resolved(text))
                })
                .collect();
            scaling::check_order(what, n, power, |m| {
                let (stmts, res) = &units[&m];
                let info = zedc::check::check(stmts, res);
                assert!(info.errors.is_empty(), "{:?}", info.errors);
            });
        });
    t.unwrap().join().unwrap();
}

#[test]
fn the_checker_reads_each_operand_of_a_nest_once() {
    // `x = bitAnd(bitAnd(…bitAnd(1, 1)…, 1), 1);`, `n` calls deep. Each call checks its
    // operands' domains from what their text shows; each expression is read once, so the nest
    // is checked in O(n): 7.9 times the work at 80 and 640. With `Ck::known`'s memo cleared at
    // each call, so each call reads its operands again, it is O(n²): 51.8 times the work and
    // 45.9 times the bytes (BIT-memo-test, 2026-11-05). The sizes are small so that version
    // fails within seconds.
    check_alone("checking a nest of n bit-word calls", 80, 1, |n| {
        with_main(format!(
            "x = {}1{};\n",
            "bitAnd(".repeat(n),
            ", 1)".repeat(n)
        ))
    });
}

#[test]
fn the_checker_reads_each_binding_of_a_chain_once() {
    // `y0 = 255; y1 = bitXor(shr(y0, 1), 3); …`, `n` bindings each a call on the one before.
    // Each binding's value is read once: 8.0 times the work at 80 and 640. With `Ck::known`'s
    // memo cleared at each call, each call reads the whole chain before it again: 57.9 times
    // the work and 53.5 times the bytes (BIT-memo-test, 2026-11-05). At 200 and 1600 that
    // version ran past 60 seconds, so the sizes are small.
    check_alone(
        "checking a chain of n bindings of bit-word calls",
        80,
        1,
        |n| {
            let mut src = String::from("y0 = 255;\n");
            for i in 1..=n {
                src.push_str(&format!("y{i} = bitXor(shr(y{}, 1), 3);\n", i - 1));
            }
            with_main(src)
        },
    );
}

#[test]
fn a_constant_no_bit_word_reads_is_not_folded() {
    // `x = 3 ** e + 5 ** e;` with `x` read by nothing: the checker reads a binder's value only
    // for a bit word or an exponent that reads its name, so the work does not grow with `e`.
    // Folded at its binder, the sum takes time that grows faster than its digits.
    check_alone(
        "checking an unread constant 3 ** e + 5 ** e",
        200_000,
        0,
        |e| with_main(format!("x = 3 ** {e} + 5 ** {e};\n")),
    );
}

#[test]
fn a_nest_of_tests_narrows_each_operand_in_one_step_each() {
    // `f(n) = if n >= 0 { popCount(n) + if n >= 1 { popCount(n) + … } else { 0 } } else { 0 }`,
    // `n` tests deep, a bit word read in each arm. Each arm's scope is its parent's narrowed by
    // one test, kept once computed, so the nest costs O(n) narrowings. Computed again from the
    // outermost test at each read, it is O(n²).
    check_alone(
        "checking a nest of n tests, each arm reading a bit word",
        300,
        1,
        |n| {
            let mut body = String::from("0");
            for i in (0..n).rev() {
                body = format!("if n >= {i} {{ popCount(n) + {body} }} else {{ 0 }}");
            }
            with_main(format!("f(positional n: int) = {body};\n"))
        },
    );
}

#[test]
fn a_chain_of_and_narrows_each_side_in_one_step_each() {
    // `f(n) = n >= 0 && popCount(n) >= 0 && popCount(n) >= 0 && …`, `n` sides: each side is
    // read where every side before it holds, its scope the one before narrowed by one side.
    check_alone(
        "checking a chain of n sides of &&, each reading a bit word",
        300,
        1,
        |n| {
            let sides = " && popCount(n) >= 0".repeat(n);
            with_main(format!("f(positional n: int) = n >= 0{sides};\n"))
        },
    );
}

/// `f(a0, …, a{k-1}) = if <test 0> { popCount(a0) + if <test 1> { … } else { 0 } } else { 0 }`
/// with each test written by `test(i)` on its own name `ai`, or with `holds` false the same
/// nest with the arms swapped, so each read is where the test fails.
fn nest_of_joins(k: usize, holds: bool, test: impl Fn(usize) -> String) -> String {
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

// The two tests below check the shapes end to end; at these sizes the checker's own work per
// test is most of the cost, and a version that empties every name of a failing case
// (O(k²) for the nest) still passes them (measured at 200 and 400, against 1600 and 3200).
// `l01_39_reduced_product::scaling::a_failing_case_costs_its_test_and_not_the_names_in_scope`
// checks that cost alone, and fails for that version.

#[test]
fn a_nest_of_or_tests_on_distinct_names_joins_each_in_what_it_changed() {
    // Each arm is read where `ai >= i + 3 || ai == i` holds: the join of its two cases, both
    // reachable, which differ in `ai` alone, though the scope holds `i` names there.
    check_alone(
        "checking a nest of k || tests on k names, each arm reading a bit word",
        200,
        1,
        |k| nest_of_joins(k, true, |i| format!("a{i} >= {} || a{i} == {i}", i + 3)),
    );
}

#[test]
fn a_nest_of_failing_and_tests_on_distinct_names_joins_each_in_what_it_changed() {
    // The else arm of `ai < i && ai < i + 3`: the join of its two failing cases, the second
    // (`ai < i` and `ai >= i + 3`) unreachable.
    check_alone(
        "checking a nest of k failing && tests on k names, each else arm reading a bit word",
        200,
        1,
        |k| nest_of_joins(k, false, |i| format!("a{i} < {i} && a{i} < {}", i + 3)),
    );
}

/// `f(a0, …)` whose `k` arms each read `ai` where `ai >= i || ai <= -(i + 3)` holds, which a
/// test narrows but not to int[0..]: `k` rejections, each under the `k` tests around it.
fn nest_of_rejections(k: usize) -> String {
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
fn test_notes(src: &str) -> (usize, usize) {
    match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => (e.matches("this test is").count(), e.len()),
    }
}

/// Checks that the rejection of `src(k)`, `k` reads each rejected under tests, names exactly
/// `per` tests for each read at `k = n` and `8n`, that its text grows as the notes do, and that
/// the work, the rendering of every note included, is linear.
fn check_notes(what: &'static str, n: usize, per: usize, src: impl Fn(usize) -> String) {
    let srcs = check_note_counts(what, n, per, src);
    let t = std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(move || {
            scaling::check_order(what, n, 1, |m| {
                assert!(zedc::run::load(srcs[&m].as_bytes()).is_err())
            });
        });
    t.unwrap().join().unwrap();
}

/// The first part of [`check_notes`], the count of the notes and the size of their text, with
/// the sources of each size.
fn check_note_counts(
    what: &'static str,
    n: usize,
    per: usize,
    src: impl Fn(usize) -> String,
) -> HashMap<usize, String> {
    let srcs: HashMap<usize, String> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, src(m)))
        .collect();
    let notes = |m: usize| scaling::on_a_thread(1 << 29, || test_notes(&srcs[&m]));
    let ((small, small_text), (large, large_text)) = (notes(n), notes(scaling::FACTOR * n));
    assert_eq!(
        (small, large),
        (per * n, per * scaling::FACTOR * n),
        "{what}"
    );
    assert!(
        large_text as f64 <= scaling::RATIO * small_text as f64,
        "{what}: {small_text} and {large_text} bytes of text"
    );
    srcs
}

#[test]
fn a_nest_of_rejections_on_distinct_names_names_the_tests_of_each_name_only() {
    // Each rejection names the two sides of its own `||` (`ai >= i` where it holds and
    // `ai <= -(i + 3)` where it holds), found through the chain of its one name; the case where
    // the first side fails is not named, since the second side alone gives `ai` its bound
    // there, and no test on another name is. Naming every enclosing test, the nest gave
    // `3k(k + 1)/2` notes: 60,300 at 200 and 961,200 at 800.
    check_notes(
        "checking a nest of k rejections on k names, each under its || test",
        150,
        2,
        nest_of_rejections,
    );
}

#[test]
fn a_nest_of_rejections_under_tests_that_share_a_name_names_two_tests_each() {
    // A device's readings `ai`, each checked against one threshold `n` that is checked first:
    // `if n >= 0 { if ai >= n - 3 { popCount(ai) + … } }`, one level a line. The rejection of
    // `popCount(ai)` names the test on `ai` and `n >= 0`, which bounds `n` there; the tests
    // `aj >= n - 3` read `n` but change nothing of it, and are not named. Following `n` to
    // every test that reads it, each rejection named all `k` tests: 5,150 to 321,200 notes at
    // `k` = 100 to 800 (62.4 times for 8 times).
    check_notes(
        "checking a nest of k rejections under tests that share the name n",
        150,
        2,
        |k| {
            let params: Vec<String> = (0..k).map(|i| format!("positional a{i}: int")).collect();
            let mut body = String::from("0");
            for i in (0..k).rev() {
                body = format!("if a{i} >= n - 3 {{\n  popCount(a{i}) + {body}\n}} else {{ 0 }}");
            }
            with_main(format!(
                "f(\npositional n: int,\n{}\n) =\nif n >= 0 {{\n{body}\n}} else {{ 0 }};\n",
                params.join(",\n")
            ))
        },
    );
}

#[test]
fn a_nest_of_rejections_under_tests_on_one_name_names_the_test_that_bounds_it() {
    // `if n >= -1 { popCount(n) + if n >= -2 { … } }`: the inner tests change nothing of `n`,
    // so each rejection names `n >= -1` alone. And `if n >= -k { popCount(n) + if n >= -(k - 1)
    // { … } }`: each test bounds `n` on its own, so each rejection names its own test alone.
    // Naming each test on `n` around it, either nest gave `k(k + 1)/2` notes: 1,275 to 80,200
    // at `k` = 50 to 400 for the first.
    let nest = |k: usize, bound: &dyn Fn(usize) -> usize| {
        let mut body = String::from("0");
        for i in (0..k).rev() {
            body = format!(
                "if n >= -{} {{\n  popCount(n) + {body}\n}} else {{ 0 }}",
                bound(i)
            );
        }
        with_main(format!("f(positional n: int) =\n{body};\n"))
    };
    check_notes(
        "checking a nest of k rejections under weaker and weaker tests on n",
        150,
        1,
        |k| nest(k, &|i| i + 1),
    );
    check_notes(
        "checking a nest of k rejections under stronger and stronger tests on n",
        150,
        1,
        |k| nest(k, &|i| k - i),
    );
}

/// `k` readings `ai`, each related to `n` by `rel` (`#` for `i`), nested one level a line in
/// order `order`, and under them `if n >= -1 { popCount(a0) + … }`.
fn hub(k: usize, outer: &str, rel: &str, order: &dyn Fn(usize) -> usize) -> String {
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

#[test]
fn a_test_the_relation_carries_to_each_reading_names_the_path_to_it_only() {
    // Readings `ai`, each checked against one threshold `n` (`ai >= n`, or `n <= ai`, or
    // `ai == n`), and then `n >= -1`, which bounds every `ai` through its relation to `n`. The
    // rejection of `popCount(ai)` names `ai >= n` and `n >= -1`. Following `n` to every test
    // that reads it, each rejection named all `k + 1` tests: 650 to 40,200 notes at `k` = 25
    // to 200 (61.8 times for 8 times).
    for rel in ["a# >= n", "n <= a#", "a# == n", "a# >= n - 1"] {
        check_notes(
            "checking k readings related to n, under a test on n",
            150,
            2,
            |k| hub(k, "", rel, &|i| i),
        );
    }
}

#[test]
fn a_test_the_relation_carries_to_each_reading_names_the_path_to_it_in_any_order() {
    // The same in the other order, the last reading outermost.
    check_notes(
        "checking k readings related to n in reverse order, under a test on n",
        150,
        2,
        |k| hub(k, "", "a# >= n", &|i| k - 1 - i),
    );
    // Through a second name: `m == n` outermost, `ai == m` for each `i`, then `n >= -1`. The
    // rejection of `popCount(ai)` names `ai == m`, `m == n` and `n >= -1`.
    check_notes(
        "checking k readings related to m, m to n, under a test on n",
        150,
        3,
        |k| hub(k, "m == n", "a# == m", &|i| i),
    );
}

/// `k` readings `ai`, each checked against one threshold `n` by `ai >= n`, one level a line,
/// then `m` tests `n >= -j`, each stronger than the one around it, then the reads of the
/// first `reads` readings.
fn hub_strengthened(k: usize, m: usize, reads: usize) -> String {
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

#[test]
fn a_test_the_relation_carries_names_its_path_and_not_the_weaker_tests_around_it() {
    // Readings `ai`, each checked against `n` by `ai >= n`, then `k` tests on `n`, each
    // stronger than the last, `n >= -k` to `n >= -1`. Each strengthens every `ai` through the
    // relation, but `n >= -1` with `ai >= n` gives `ai` its bound alone, so the rejection of
    // `popCount(ai)` names those two. Following `ai` above the carrying test, each rejection
    // named every test on `n`: k(k + 1) notes, 650 to 40,200 at `k` = 25 to 200 (61.8 times for
    // 8 times). The time of this family is not checked here: settling the `k` scopes of the
    // tests on `n` costs `k` projections each (COMPLEXITY.md C26, open item NARROW-hub-settle;
    // `a_hub_settles_its_scopes_in_time_linear_in_the_tests`).
    check_note_counts(
        "checking k readings related to n, under k stronger and stronger tests on n",
        12,
        2,
        |k| hub_strengthened(k, k, k),
    );
}

/// Runs the checker on `src` at sizes `n` and `8n` and checks that each is rejected, in work
/// and bytes linear in the size, on a stack that holds the nest.
fn check_rejected_in_linear_work(what: &'static str, n: usize, src: impl Fn(usize) -> String) {
    let srcs = scaling::inputs(n, src);
    let t = std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(move || {
            scaling::check_order(what, n, 1, |m| {
                assert!(zedc::run::load(srcs[&m].as_bytes()).is_err())
            });
        });
    t.unwrap().join().unwrap();
}

#[test]
fn a_hub_settles_its_scopes_in_time_linear_in_the_tests() {
    // `k` tests `ai >= n`, then `k` tests on `n`, each stronger, then one read of `a0`: one
    // rejection with `2` notes. Each test on `n` moved `n`, which every `ai >= n` mentions,
    // and projected all `k` of them: 0.29, 1.26, 5.08 and 24.1 s at `k` = 25 to 200 (82 times
    // for 8 times, wt/narrow-if at fd8e5a29). The scopes are lazy now (`Scope::lazy`): each
    // `ai >= n` is a spoke whose leaf `ai` is settled where a read needs it.
    check_rejected_in_linear_work("settling the scopes of k tests on a hub", 25, |m| {
        hub_strengthened(m, m, 1)
    });
}

/// `k` levels, level `i` the test `ai >= n`, then `n >= -(k - i)`, then a read of `ai` added
/// to the level inside it: each test on `n` moves `n` under all the `ai >= n` above it.
fn hub_interleaved(k: usize) -> String {
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

#[test]
fn a_hub_tested_between_its_spokes_settles_in_time_linear_in_the_tests() {
    // Each level relates `ai` to `n`, strengthens `n` and reads `ai`: `k` rejections, each
    // naming its level's two tests. Settling every scope whole cost 0.19 to 12.9 s at `k` =
    // 25 to 200 (wt/narrow-if, NARROW-hub-settle ledger).
    check_notes(
        "checking k readings each related to n, each under a stronger test on n",
        25,
        2,
        hub_interleaved,
    );
}

/// `k` levels `ai >= n && ai >= m`, then `k` tests on `n` and `k` on `m`, each stronger, then
/// one read of `a0`.
fn two_hubs(k: usize) -> String {
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
fn two_hubs_on_one_block_settle_as_the_whole_scope() {
    // Each `ai` is related to two hubs, so no `ai >= n` is a spoke and every scope is
    // settled whole: the answer and the notes are those of the eager scope, `a0` int[-1..]
    // under `a0 >= n` and the strongest test on `n`, which is enough without one on `m`. The
    // time is not checked here: about `k²`, 20.6 s at `k` = 384 (COMPLEXITY.md C26, the
    // tradeoff at `Ck::compute`).
    for k in [1, 2, 5] {
        let src = two_hubs(k);
        let e = scaling::on_a_thread(1 << 29, || zedc::run::load(src.as_bytes()).err())
            .expect("a0 may be negative");
        assert!(e.contains("this `x` is int[-1..]"), "k = {k}:\n{e}");
        assert!(e.contains("if n >= -1 {"), "k = {k}:\n{e}");
        assert_eq!(
            e.matches("this test is true here").count(),
            2,
            "k = {k}:\n{e}"
        );
        assert!(e.contains("if a0 >= n && a0 >= m {"), "k = {k}:\n{e}");
    }
}
