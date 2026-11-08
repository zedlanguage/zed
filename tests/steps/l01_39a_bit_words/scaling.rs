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
                let info = zedc::check::walk::check(stmts, res);
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
fn two_hubs_on_one_block_settle_to_the_eager_answer() {
    // Each `ai` is a leaf of a star of two hubs, `n` and `m`, whose other conjuncts are bounds
    // on one hub alone: the answer and the notes are those of the eager scope, `a0` int[-1..]
    // under `a0 >= n` and the strongest test on `n`, which is enough without one on `m`.
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

#[test]
fn two_hubs_on_one_block_settle_in_time_linear_in_the_tests() {
    // Each `ai >= n && ai >= m` related `ai` to two hubs, so no scope was lazy and each of the
    // `2k` tests on a hub projected all `k` levels: about `k²`, 0.04 to 1.43 s at `k` = 12 to
    // 96 (wt/narrow-hub-settle at a18089b5). Each `ai` is now a star's leaf
    // (COMPLEXITY.md C26).
    check_rejected_in_linear_work("settling k levels each related to two hubs", 12, two_hubs);
}

/// `k` levels `ai >= n + m`, then `k` tests on `n` and `k` on `m`, each stronger, then one
/// read of `a0`.
fn hub_sum(k: usize) -> String {
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
        assert!(e.contains("this `x` is int[-2..]"), "k = {k}:\n{e}");
        sum_notes(&e, &format!("k = {k}"));
    }
}

/// The notes of a read of `a0` under `a0 >= n + m` and the tests `n >= -j`, `m >= -j` of
/// [`hub_sum`]: the sum and the strongest test on each hub, each once. The weaker tests
/// `n >= -2`, `m >= -2`, … are not listed: the sum gives `a0` its product from those of `n`
/// and `m` where `m >= -1` is, and `m >= -1` alone gives `m` its product there.
fn sum_notes(e: &str, what: &str) {
    notes_are(e, &["a0 >= n + m", "n >= -1", "m >= -1"], what);
}

/// Asserts that the notes of `e` list exactly the tests `tests`, each once.
fn notes_are(e: &str, tests: &[&str], what: &str) {
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
fn a_bound_on_a_sum_of_two_hubs_settles_in_time_linear_in_the_tests() {
    // `ai >= n + m` was a written constraint, which pinned `ai`, so no scope was lazy and each
    // test on a hub enumerated the levels: about `k³`, 0.31 to 19.4 s at `k` = 12 to 48
    // (wt/narrow-hub-settle at a18089b5). A bound on a sum of names of coefficients one and
    // minus one is now the relation's alone (`Scope::atom`), and `ai` a star's leaf. The
    // three notes are read once ([`sum_notes`]).
    check_rejected_in_linear_work(
        "settling k levels each a bound on a sum of two hubs",
        6,
        hub_sum,
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
        assert!(
            e.contains(&format!("this `x` is int[{low}..]")),
            "{test}:\n{e}"
        );
        assert!(e.contains(&format!("if {test} {{")), "{test}:\n{e}");
    }
}

/// `link` above `k` levels `ai >= n && ai >= m` (or `ai >= n + m` with `sum`), then `k` tests
/// on `n` and `k` on `m`, each stronger, then one read of `a0`.
fn related_hubs(k: usize, link: &str, sum: bool) -> String {
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
                    e.contains(&format!("this `x` is int[{low}..]")),
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
fn related_hubs_settle_in_time_linear_in_the_tests() {
    // With `n >= m` above them, the hubs of the `ai` were not clean, so no `ai` was a star's
    // leaf, all were one block, and each of the `2k` tests on a hub projected all `k` levels:
    // about `k²`, 0.09, 0.31, 1.16 and 4.91 s at `k` = 24 to 192 (wt/narrow-hub-rest at
    // 68a03534). A hub now admits a leaf whose hubs are all its free conjuncts mention, and
    // the star is projected with those conjuncts (COMPLEXITY.md C26).
    check_rejected_in_linear_work(
        "settling k levels each related to two related hubs",
        12,
        |k| related_hubs(k, "n >= m", false),
    );
    check_rejected_in_linear_work(
        "settling k levels each a bound on a sum of two related hubs",
        6,
        |k| related_hubs(k, "n >= m", true),
    );
}

#[test]
fn notes_through_a_link_among_many_sums_take_time_linear_in_the_tests() {
    // Under `m >= n`, the `k` sums `ai >= n + m` and the link each reach `m` from `n`, and only
    // the link gives `m` the product `n >= -1` carried to it: the notes try the other shortest
    // paths to `m` ([`Carried::others`]), each once, for the one rejection.
    check_rejected_in_linear_work("naming a link among k sums of two related hubs", 6, |k| {
        related_hubs(k, "m >= n", true)
    });
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
        assert!(e.contains("this `x` is int[-1..]"), "{a}, {b}, {c}:\n{e}");
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
fn longer_paths(k: usize) -> String {
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

#[test]
fn the_longer_paths_to_a_name_are_searched_in_linear_time() {
    // Each of the `k` tests `x <= y(k+1) + i` was tried as a path of its own, back along the
    // chain to `n`, before `x >= y(k+1)`: `k` paths of `k + 2` tests, 0.236, 0.720, 2.72 and
    // 10.6 s at `k` = 25 to 200, 46.1 times the bytes at 8 times `k` (item NARROW-eager-scope).
    let e = zedc::run::load(longer_paths(3).as_bytes())
        .err()
        .expect("x may be negative");
    assert!(e.contains("this `x` is int[-1..]"), "{e}");
    let tests = [
        "n >= -1", "y1 >= n", "y2 >= y1", "y3 >= y2", "y4 >= y3", "x >= y4",
    ];
    notes_are(&e, &tests, "k = 3");
    check_rejected_in_linear_work(
        "naming the tests of a longer path among k",
        25,
        longer_paths,
    );
}

/// A block of `d` bindings `x_k = x_(k-1) + 1` from `x_0 = n`, each tested by `x_k >= k`, which
/// holds where `n >= 0`, with a bit word on `n` in its arm.
fn tested_let_chain(d: usize) -> String {
    let mut s = String::from("x0 = n; s0 = 0; ");
    for k in 1..=d {
        let j = k - 1;
        s += &format!(
            "x{k} = x{j} + 1; s{k} = s{j} + (if x{k} >= {k} {{ popCount(n) }} else {{ 0 }}); "
        );
    }
    format!("f(positional n: int) = {{ {s}s{d} }};\n")
}

#[test]
fn a_block_of_tested_lets_is_checked_in_time_linear_in_the_bindings() {
    // Each test binds its name with the summary of its value, made once for the binder from
    // the summary of the binding before it, and formed from that one's sum (item PA-let-check):
    // `d` tests cost `O(d log d)`. Every read of `n` is accepted only through the summaries.
    // Measured 2026-11-07 (load 35 to 40): 0.16, 0.32, 0.63, 1.27 and 2.54 billion
    // instructions at `d` = 64 to 1024; with the summaries made again for each test, 0.23,
    // 0.58, 1.69, 5.50 and 19.4 billion, which this test rejects (26.7 times the bytes for 8 times).
    let what = "checking a block of d tested lets, each one more than the last";
    let n = 64;
    let srcs = scaling::inputs(n, |d| super::program(&tested_let_chain(d)));
    scaling::on_a_thread(1 << 29, || {
        scaling::check(what, n, |m| {
            let src = &srcs[&m];
            assert!(
                zedc::run::load(src.as_bytes()).is_ok(),
                "rejected at d = {m}"
            )
        })
    });
}

/// A block of `d` bindings `x_k = x_(k-1) + 1` from `x_0 = v`, where `v is int` has narrowed
/// the parameter `v`, then one test `x_d >= d`, which holds where `v >= 0`, and in its arm a
/// bit word on each `x_k`, the first binding first or the last first. Each read is accepted
/// only through the summary of `x_k` over the narrowed `v` (item PA-let-narrow: a parameter
/// narrowed by `is` has summaries, and a name read under a test of a name over the same input
/// is narrowed by its summary).
fn read_let_chain(d: usize, last_first: bool) -> String {
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

#[test]
fn the_names_of_a_tested_block_read_under_the_test_are_checked_in_time_linear_in_the_bindings() {
    // Each binder's summary is made once and formed from those of the binders it reads,
    // children first, so a read of `x_k` costs one evaluation of its formed summary over the
    // narrowed input, in either order of reads (item PA-let-narrow). Measured 2026-11-07, last
    // first: 3.57e8 instructions at d = 256 and 2.81e9 at d = 2048, 7.9 times. A negative
    // control in which a summary sums the whole chain of those it reads, not their formed sums,
    // measured 16.8 times; the limit of 24 at sizes this test can afford does not fail it.
    for last_first in [false, true] {
        let what = if last_first {
            "reading each of a block of d lets under a test, last first"
        } else {
            "reading each of a block of d lets under a test, first first"
        };
        let n = 64;
        let srcs = scaling::inputs(n, |d| super::program(&read_let_chain(d, last_first)));
        scaling::on_a_thread(1 << 29, || {
            scaling::check(what, n, |m| {
                let src = &srcs[&m];
                if let Err(e) = zedc::run::load(src.as_bytes()) {
                    panic!("rejected at d = {m}: {e}");
                }
            })
        });
    }
}

/// A block of `d` bindings over two inputs, `x_0 = n + m`, then `x_k = x_(k-1) + n` and
/// `x_k = x_(k-1) + m` in turn, where a test has bounded `m` to `0..=5`; each `x_k = a n + b m`
/// is tested by `x_k >= 5 b`, which holds where `n >= 0`, with a bit word on `n` in its arm.
fn two_input_chain(d: usize) -> String {
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

#[test]
fn a_block_of_tested_lets_over_two_inputs_is_checked_in_time_linear_in_the_bindings() {
    // Each summary is over `n` and `m` (item PA-let-narrow), made once and formed from the
    // one before it; each test narrows `n` by the bounds of `m`, `O(1)` for two inputs.
    // Measured 2026-11-07: 6.60e8 instructions at d = 256 and 5.27e9 at d = 2048, 8.0 times;
    // 16.1 times under the negative control of the test above.
    let what = "checking a block of d tested lets over two inputs";
    let n = 64;
    let srcs = scaling::inputs(n, |d| super::program(&two_input_chain(d)));
    scaling::on_a_thread(1 << 29, || {
        scaling::check(what, n, |m| {
            let src = &srcs[&m];
            if let Err(e) = zedc::run::load(src.as_bytes()) {
                panic!("rejected at d = {m}: {e}");
            }
        })
    });
}

/// The nodes `LetPa::sum` enters while the program `src` is loaded, on this thread.
fn sum_nodes(src: &str) -> u64 {
    let before = zedc::store::preimage::counts::sum_nodes();
    if let Err(e) = zedc::run::load(src.as_bytes()) {
        panic!("rejected: {e}");
    }
    zedc::store::preimage::counts::sum_nodes() - before
}

#[test]
fn the_summaries_of_a_tested_block_are_formed_from_each_node_a_bounded_number_of_times() {
    // The work of the two tests above is mostly linear in the bindings for other causes, so it
    // hides a summary formed from the whole chain below it, `Θ(d²)`: measured 16.8 times the
    // instructions at 8x, under the limit of 24. The nodes `LetPa::sum` enters are linear in the
    // bindings only when each summary is formed from the formed sums of those it reads (item
    // PA-let-narrow), and a count does not change with the load. Measured 2026-11-07: 129 nodes
    // at d = 64 and 1,025 at d = 512 (7.95 times) for each block. A negative control in which
    // `sum` ignores the formed sums entered 2,145 and 131,841 nodes for the first block (61.5
    // times) and failed this test.
    let n = 64;
    let large = n * scaling::FACTOR;
    for (what, make) in [
        (
            "a block of d lets read under a test, last first",
            Box::new(|d| read_let_chain(d, true)) as Box<dyn Fn(usize) -> String>,
        ),
        (
            "a block of d tested lets over two inputs",
            Box::new(two_input_chain),
        ),
    ] {
        let (small_src, large_src) = (super::program(&make(n)), super::program(&make(large)));
        let (a, b) =
            scaling::on_a_thread(1 << 29, || (sum_nodes(&small_src), sum_nodes(&large_src)));
        let ratio = b as f64 / a as f64;
        assert!(
            a > 0 && ratio <= 9.0,
            "{what}: `LetPa::sum` entered {a} nodes at d = {n} and {b} at d = {large}: \
             {ratio:.2} times, above 9"
        );
    }
}

/// The probe of item PA-let-multi: `x_0 = n`, then `q_k = n mod 4; x_k = x_(k-1) + q_k` for `k`
/// up to `d`, and one test `x_d >= 3 d`, which holds only where `n >= 0`, with a bit word on
/// `n` in its arm.
fn remainder_chain(d: usize) -> String {
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
fn term_bounds(src: &str) -> u64 {
    let before = zedc::store::preimage::counts::term_bounds();
    if let Err(e) = zedc::run::load(src.as_bytes()) {
        panic!("rejected: {e}");
    }
    zedc::store::preimage::counts::term_bounds() - before
}

#[test]
fn a_chain_of_sums_over_many_inputs_reads_each_summary_in_its_narrowed_inputs() {
    // `x_k` has a summary over `k + 1` inputs, `n` and every `q_j` (item PA-let-multi), and
    // the product of `x_k` reads that of `x_(k-1)` met with its summary's values. Read over
    // every input, that took the bounds of each of `x_(k-1)`'s terms, `Θ(d²)` for the chain;
    // the sum keeps its terms' bounds over the domains it was formed over
    // (`LetPa::image_shifted`), and a scope with none of the inputs reads none. A count does not
    // change with the load. Measured: 259 at d = 64 and 2051 at d = 512 (7.92 times); with
    // every input read, 2210 and 132354 (59.89 times).
    let n = 64;
    let large = n * scaling::FACTOR;
    let (small_src, large_src) = (
        super::program(&remainder_chain(n)),
        super::program(&remainder_chain(large)),
    );
    let (a, b) = scaling::on_a_thread(1 << 29, || {
        (term_bounds(&small_src), term_bounds(&large_src))
    });
    let ratio = b as f64 / a as f64;
    assert!(
        a > 0 && ratio <= 9.0,
        "`pa_bounds` ran {a} times at d = {n} and {b} at d = {large}: {ratio:.2} times, above 9"
    );
}

/// The probe of item PA-let-narrow-many: `x_0 = n`, then for `k` up to `d` a test that narrows
/// one input, `q_k = n mod 4` to `q_k >= 1` or the parameter `a_k` to `1..=3`, and under it
/// `x_k = x_(k-1) + q_k` (or `+ a_k`); then one test `x_d >= 3 d`, with a bit word on `n` in
/// its arm.
fn nested_chain(d: usize, params: bool) -> String {
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

#[test]
fn a_chain_of_sums_under_a_test_of_each_input_reads_each_summary_from_the_one_before() {
    // `x_(k-1)` is read in the scope of `x_k`, under the tests of `k - 1` of its inputs (item
    // PA-let-narrow-many). Read afresh, each binding took the bounds of `x_(k-1)`'s term of
    // every narrowed input, `Θ(d²)` for the chain; the inputs read are kept in a tree with the
    // sum of their shifts, and `x_(k-1)` is read from `x_(k-2)` in the scope of `x_(k-1)`,
    // which differ at one input (`images::updated`). A count does not change with the load.
    // Measured: 323 at d = 64 and 2563 at d = 512 (7.93 times), the same for remainders and
    // for parameters; read afresh, 2275 and 132867 (58.40 times).
    let n = 64;
    let large = n * scaling::FACTOR;
    for params in [false, true] {
        let (small_src, large_src) = (
            super::program(&nested_chain(n, params)),
            super::program(&nested_chain(large, params)),
        );
        let (a, b) = scaling::on_a_thread(1 << 29, || {
            (term_bounds(&small_src), term_bounds(&large_src))
        });
        let ratio = b as f64 / a as f64;
        assert!(
            a > 0 && ratio <= 9.0,
            "parameters {params}: `pa_bounds` ran {a} times at d = {n} and {b} at d = {large}: \
             {ratio:.2} times, above 9"
        );
    }
}

/// Parameters `x_1 … x_k`, each tested to `0..=1`, then `z = x_1 + … + x_k` and `k` nested
/// tests `z >= i`, with a bit word on `x_1` in the innermost arm.
fn tests_of_one_sum(k: usize) -> String {
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

#[test]
fn tests_of_a_name_over_many_inputs_take_the_bounds_of_the_inputs_they_narrow() {
    // `k` tests of `z`, a sum of `k` inputs, each read through its summary (item
    // PA-letpre-linear).
    let n = 40;
    let large = n * scaling::FACTOR;
    let (small_src, large_src) = (
        super::program(&tests_of_one_sum(n)),
        super::program(&tests_of_one_sum(large)),
    );
    let (a, b) = scaling::on_a_thread(1 << 29, || {
        (term_bounds(&small_src), term_bounds(&large_src))
    });
    let ratio = b as f64 / a as f64;
    assert!(
        a > 0 && ratio <= scaling::RATIO,
        "`pa_bounds` ran {a} times at k = {n} and {b} at k = {large}: {ratio:.2} times"
    );
}
