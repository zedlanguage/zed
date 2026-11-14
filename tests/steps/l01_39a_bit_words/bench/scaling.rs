//! The benchmarks of step L1.39a's checker shapes and bit words: the words' time against the size
//! of their operands (the rule of low complexity, DESIGN.md Part G), and the checker's work on
//! nests, chains and hubs of tests at `k` and `8k`. The digit-wise words take time linear in the
//! digits of their operands; the shifts, `bitNot` and the rotations keep a power of two as its
//! exponent, so their time grows with the digits of the count and the width, not with the power.
//! Every operand and program is built before the timing. Each shape has a small instance among
//! the correctness tests of `shapes.rs`, which checks its verdict and notes.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_traits::One;
use zed_kernel::{Prim, Value};
use zed_tests::instances::Rng;
use zed_tests::scaling;

use super::super::program;
use super::super::shapes::*;

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
    let n = 1 << 24;
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
    // Run 1500 times at 2^16 digits, not once at a size that takes 1 s: at 2^20 and 2^23 digits
    // `shr`, `rotl` and `rotr` allocate 13 to 15 times the bytes for 8 times the digits (their
    // instructions grow 7.8 to 7.9 times), against 8.1 times at 2^16 (TEST-bench-move-l0139,
    // 2026-11-14; plan row BIT-shift-bytes).
    let n = 1 << 16;
    let ops = operands(n);
    scaling::check_order("shl, shr, bitNot, rotl, rotr", n, 1, |m| {
        let (a, _, w) = &ops[&m];
        let k = Value::Int(m as i64 / 3);
        for _ in 0..1500 {
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
    check_alone(
        "checking a nest of n bit-word calls",
        80,
        1,
        nest_of_bit_and,
    );
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
        chain_of_bit_xor,
    );
}

#[test]
fn a_constant_no_bit_word_reads_is_not_folded() {
    // `x = 3 ^ e + 5 ^ e;` with `x` read by nothing: the checker reads a binder's value only
    // for a bit word or an exponent that reads its name, so the work does not grow with `e`.
    // Folded at its binder, the sum takes time that grows faster than its digits.
    check_alone(
        "checking an unread constant 3^e + 5^e",
        200_000,
        0,
        unread_constant,
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
        750,
        1,
        nest_of_tests,
    );
}

#[test]
fn a_chain_of_and_narrows_each_side_in_one_step_each() {
    // `f(n) = n >= 0 && popCount(n) >= 0 && popCount(n) >= 0 && …`, `n` sides: each side is
    // read where every side before it holds, its scope the one before narrowed by one side.
    check_alone(
        "checking a chain of n sides of &&, each reading a bit word",
        1000,
        1,
        chain_of_and,
    );
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
        300,
        1,
        |k| nest_of_joins(k, true, or_test),
    );
}

#[test]
fn a_nest_of_failing_and_tests_on_distinct_names_joins_each_in_what_it_changed() {
    // The else arm of `ai < i && ai < i + 3`: the join of its two failing cases, the second
    // (`ai < i` and `ai >= i + 3`) unreachable.
    check_alone(
        "checking a nest of k failing && tests on k names, each else arm reading a bit word",
        700,
        1,
        |k| nest_of_joins(k, false, failing_and_test),
    );
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
    scaling::hold(
        &format!("{what}: the text of its notes"),
        "bytes",
        small_text as u64,
        large_text as u64,
        1,
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
        500,
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
        400,
        2,
        nest_under_a_shared_name,
    );
}

// `if n >= -1 { popCount(n) + if n >= -2 { … } }`: the inner tests change nothing of `n`, so
// each rejection names `n >= -1` alone. And `if n >= -k { popCount(n) + if n >= -(k - 1) { … }
// }`: each test bounds `n` on its own, so each rejection names its own test alone. Naming each
// test on `n` around it, either nest gave `k(k + 1)/2` notes: 1,275 to 80,200 at `k` = 50 to
// 400 for the first.

#[test]
fn a_nest_of_rejections_under_weaker_tests_on_one_name_names_the_test_that_bounds_it() {
    check_notes(
        "checking a nest of k rejections under weaker and weaker tests on n",
        1000,
        1,
        |k| nest_on_one_name(k, &|i| i + 1),
    );
}

#[test]
fn a_nest_of_rejections_under_stronger_tests_on_one_name_names_the_test_that_bounds_it() {
    check_notes(
        "checking a nest of k rejections under stronger and stronger tests on n",
        500,
        1,
        |k| nest_on_one_name(k, &|i| k - i),
    );
}

/// Readings `ai`, each checked against one threshold `n` by `rel` (`ai >= n`, or `n <= ai`, or
/// `ai == n`, or `ai >= n - 1`), and then `n >= -1`, which bounds every `ai` through its
/// relation to `n`. The rejection of `popCount(ai)` names `ai >= n` and `n >= -1`. Following `n`
/// to every test that reads it, each rejection named all `k + 1` tests: 650 to 40,200 notes at
/// `k` = 25 to 200 (61.8 times for 8 times). At 150 and 1200 one relation took 9 s alone (item
/// NARROW-hub-seed-edges); a quadratic still reads 64 times the work, above 24.
fn check_path_only(rel: &str) {
    let what = format!("checking k readings related to n by {rel}, under a test on n");
    check_notes(what.leak(), 220, 2, |k| hub(k, "", rel, &|i| i));
}

#[test]
fn a_test_the_relation_carries_to_each_reading_names_the_path_to_it_only() {
    check_path_only(HUB_RELATIONS[0]);
}

#[test]
fn a_test_the_relation_carries_to_each_reading_names_the_path_to_it_only_written_backward() {
    check_path_only(HUB_RELATIONS[1]);
}

#[test]
fn a_test_the_relation_carries_to_each_reading_names_the_path_to_it_only_as_equality() {
    check_path_only(HUB_RELATIONS[2]);
}

#[test]
fn a_test_the_relation_carries_to_each_reading_names_the_path_to_it_only_with_an_offset() {
    check_path_only(HUB_RELATIONS[3]);
}

/// `k` readings `ai`, each under `rel`, `ai >= n || ai >= 5` in one order or the other, then
/// `n >= -1` and `popCount(ai)` of each: every read is rejected, since `ai` may be -1. The `||`
/// family of the probes of item NARROW-if (verify 6) that no test held, at 100 and 800 (test
/// audit 2026-11-08). Each `ai` is `int[-1..]`, the join of `ai >= n` with `n >= -1` and of
/// `ai >= 5`. Before item NARROW-or-order each was `int` in linear work in either order: the
/// join of the two sides kept neither relation. Kept by the join of each `||`, the relations
/// made the join settle every leaf hanging at `n`, the `k` of the tests before, so `k` such
/// tests took quadratic work; now the join settles only the leaves at a hub it holds unlike
/// either side (`Scope::join`).
fn check_hub_or_constant(rel: &'static str) {
    let what = format!("checking k readings each related by {rel}, under a test on n");
    check_rejected_as_in_linear_work(
        what.leak(),
        100,
        move |k| hub(k, "", rel, &|i| i),
        move |k, out| {
            let typed = out.matches(" : int[-1..])`").count();
            assert_eq!(
                typed, k,
                "{rel}, k = {k}: {typed} reads of int[-1..]\n{out}"
            );
        },
    );
}

#[test]
fn readings_each_related_to_a_hub_or_a_constant_are_checked_in_linear_work() {
    check_hub_or_constant(HUB_OR_RELATIONS[0]);
}

#[test]
fn readings_each_related_to_a_constant_or_a_hub_are_checked_in_linear_work() {
    check_hub_or_constant(HUB_OR_RELATIONS[1]);
}

#[test]
fn a_test_the_relation_carries_to_each_reading_names_the_path_to_it_in_any_order() {
    // The same in the other order, the last reading outermost.
    check_notes(
        "checking k readings related to n in reverse order, under a test on n",
        240,
        2,
        |k| hub(k, "", "a# >= n", &|i| k - 1 - i),
    );
}

#[test]
fn a_test_the_relation_carries_through_a_second_name_names_the_path_to_it() {
    // Through a second name: `m == n` outermost, `ai == m` for each `i`, then `n >= -1`. The
    // rejection of `popCount(ai)` names `ai == m`, `m == n` and `n >= -1`.
    check_notes(
        "checking k readings related to m, m to n, under a test on n",
        240,
        3,
        |k| hub(k, "m == n", "a# == m", &|i| i),
    );
}

#[test]
fn tests_that_equate_each_reading_to_a_hub_read_the_hub_once_each() {
    // `k` tests `ai == n`. An equality bounds `ai` on both sides, so it is no star
    // (`Conjuncts::star`): `n` is a hub with `2k` edges in one tree, and a name of the conjunct
    // each test adds. `Scope::bound_pass` read every edge at each name of a test, and its search
    // started from every such name, so it read the hub's `O(k)` edges at each of the `k` tests:
    // on main f9ddc6f1, before item NARROW-hub-seed-edges, 37.4 times the work and 29.1 times
    // the bytes at `k` = 150 and 1200 (limit 24); now 8.6 and 8.4 times. Only the edges of the
    // conjunct added are read at a name whose product did not change, and the search starts only
    // from names whose bound changed or moved.
    check_alone(
        "checking k tests that equate a reading to one name",
        225,
        1,
        hub_equal,
    );
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
    check_rejected_as_in_linear_work(what, n, src, |_, _| {});
}

/// [`check_rejected_in_linear_work`], with `expect` called on each size and its message.
fn check_rejected_as_in_linear_work(
    what: &'static str,
    n: usize,
    src: impl Fn(usize) -> String,
    expect: impl Fn(usize, &str) + Send + Sync + 'static,
) {
    let srcs = scaling::inputs(n, src);
    let t = std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(move || {
            scaling::check_order(what, n, 1, |m| match zedc::run::load(srcs[&m].as_bytes()) {
                Ok(_) => panic!("size {m}: accepted"),
                Err(e) => expect(m, &e.to_string()),
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
    check_rejected_in_linear_work("settling the scopes of k tests on a hub", 600, |m| {
        hub_strengthened(m, m, 1)
    });
}

#[test]
fn a_hub_tested_between_its_spokes_settles_in_time_linear_in_the_tests() {
    // Each level relates `ai` to `n`, strengthens `n` and reads `ai`: `k` rejections, each
    // naming its level's two tests. Settling every scope whole cost 0.19 to 12.9 s at `k` =
    // 25 to 200 (wt/narrow-if, NARROW-hub-settle ledger).
    // The size stays 25, though the larger run takes 0.6 s: at 225 and 1800 the checker took
    // 16.3 times the instructions and 11.9 times the bytes (TEST-bench-move-l0139, 2026-11-14;
    // plan row NARROW-hub-interleaved-scale).
    check_notes(
        "checking k readings each related to n, each under a stronger test on n",
        25,
        2,
        hub_interleaved,
    );
}

#[test]
fn two_hubs_on_one_block_settle_in_time_linear_in_the_tests() {
    // Each `ai >= n && ai >= m` related `ai` to two hubs, so no scope was lazy and each of the
    // `2k` tests on a hub projected all `k` levels: about `k²`, 0.04 to 1.43 s at `k` = 12 to
    // 96 (wt/narrow-hub-settle at a18089b5). Each `ai` is now a star's leaf
    // (COMPLEXITY.md C26).
    check_rejected_in_linear_work("settling k levels each related to two hubs", 280, two_hubs);
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
        400,
        hub_sum,
    );
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
        170,
        |k| related_hubs(k, "n >= m", false),
    );
}

#[test]
fn related_hubs_bounding_a_sum_settle_in_time_linear_in_the_tests() {
    // The family above with each level a bound on the sum of the two related hubs.
    check_rejected_in_linear_work(
        "settling k levels each a bound on a sum of two related hubs",
        240,
        |k| related_hubs(k, "n >= m", true),
    );
}

#[test]
fn notes_through_a_link_among_many_sums_take_time_linear_in_the_tests() {
    // Under `m >= n`, the `k` sums `ai >= n + m` and the link each reach `m` from `n`, and only
    // the link gives `m` the product `n >= -1` carried to it: the notes try the other shortest
    // paths to `m` ([`Carried::others`]), each once, for the one rejection.
    check_rejected_in_linear_work("naming a link among k sums of two related hubs", 250, |k| {
        related_hubs(k, "m >= n", true)
    });
}

#[test]
fn the_longer_paths_to_a_name_are_searched_in_linear_time() {
    // Each of the `k` tests `x <= y(k+1) + i` was tried as a path of its own, back along the
    // chain to `n`, before `x >= y(k+1)`: `k` paths of `k + 2` tests, 0.236, 0.720, 2.72 and
    // 10.6 s at `k` = 25 to 200, 46.1 times the bytes at 8 times `k` (item NARROW-eager-scope).
    // The size stays 25: at 60 and 480 the work grew 10.35 times, near the limit of 10.5, as
    // `n log n` work does (TEST-bench-move-l0139, 2026-11-14).
    // The notes of `longer_paths(3)` are checked in
    // `shapes::the_longer_paths_to_a_name_name_the_tests_that_bound_it`.
    check_rejected_in_linear_work(
        "naming the tests of a longer path among k",
        25,
        longer_paths,
    );
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
    let n = 640;
    let srcs = scaling::inputs(n, |d| program(&tested_let_chain(d)));
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

#[test]
fn the_names_of_a_tested_block_read_under_the_test_are_checked_in_time_linear_in_the_bindings() {
    // Each binder's summary is made once and formed from those of the binders it reads,
    // children first, so a read of `x_k` costs one evaluation of its formed summary over the
    // narrowed input, in either order of reads (item PA-let-narrow). Measured 2026-11-07, last
    // first: 3.57e8 instructions at d = 256 and 2.81e9 at d = 2048, 7.9 times. A negative
    // control in which a summary sums the whole chain of those it reads, not their formed sums,
    // measured 16.8 times, which the limit of 24 of that day let pass; the count of nodes in
    // `the_summaries_of_a_tested_block_are_formed_from_each_node_a_bounded_number_of_times`
    // finds it.
    check_read_let_chain(
        "reading each of a block of d lets under a test, first first",
        false,
    );
}

#[test]
fn the_names_of_a_tested_block_read_last_first_are_checked_in_time_linear_in_the_bindings() {
    // The test above with the reads in the other order.
    check_read_let_chain(
        "reading each of a block of d lets under a test, last first",
        true,
    );
}

/// Checks [`read_let_chain`] in the order of reads `last_first` at `d` and `8d` bindings.
fn check_read_let_chain(what: &'static str, last_first: bool) {
    let n = 1024;
    let srcs = scaling::inputs(n, |d| program(&read_let_chain(d, last_first)));
    scaling::on_a_thread(1 << 29, || {
        scaling::check(what, n, |m| {
            let src = &srcs[&m];
            if let Err(e) = zedc::run::load(src.as_bytes()) {
                panic!("rejected at d = {m}: {e}");
            }
        })
    });
}

#[test]
fn a_block_of_tested_lets_over_two_inputs_is_checked_in_time_linear_in_the_bindings() {
    // Each summary is over `n` and `m` (item PA-let-narrow), made once and formed from the
    // one before it; each test narrows `n` by the bounds of `m`, `O(1)` for two inputs.
    // Measured 2026-11-07: 6.60e8 instructions at d = 256 and 5.27e9 at d = 2048, 8.0 times;
    // 16.1 times under the negative control of the test above.
    let what = "checking a block of d tested lets over two inputs";
    let n = 640;
    let srcs = scaling::inputs(n, |d| program(&two_input_chain(d)));
    scaling::on_a_thread(1 << 29, || {
        scaling::check(what, n, |m| {
            let src = &srcs[&m];
            if let Err(e) = zedc::run::load(src.as_bytes()) {
                panic!("rejected at d = {m}: {e}");
            }
        })
    });
}

#[test]
fn the_summaries_of_a_tested_block_are_formed_from_each_node_a_bounded_number_of_times() {
    // The work of the two tests above is mostly linear in the bindings for other causes, so it
    // hides a summary formed from the whole chain below it, `Θ(d²)`: measured 16.8 times the
    // instructions at 8x, under the limit of 24 of that day; it would fail the limit of 13 now.
    // The nodes `LetPa::sum` enters are linear in the bindings only when each summary is formed
    // from the formed sums of those it reads (item PA-let-narrow), and a count does not change
    // with the load, so it is held to 9 (`scaling::hold_linear`). Measured 2026-11-07: 129 nodes
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
        let (small_src, large_src) = (program(&make(n)), program(&make(large)));
        let (a, b) =
            scaling::on_a_thread(1 << 29, || (sum_nodes(&small_src), sum_nodes(&large_src)));
        assert!(a > 0, "{what}: `LetPa::sum` entered no node at d = {n}");
        scaling::hold_linear(
            &format!("{what}: `LetPa::sum`, d = {n} and {large}"),
            "nodes entered",
            a,
            b,
        );
    }
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
        program(&remainder_chain(n)),
        program(&remainder_chain(large)),
    );
    let (a, b) = scaling::on_a_thread(1 << 29, || {
        (term_bounds(&small_src), term_bounds(&large_src))
    });
    assert!(a > 0, "`pa_bounds` did not run at d = {n}");
    scaling::hold_linear(
        &format!("a chain of sums over many inputs, d = {n} and {large}"),
        "runs of `pa_bounds`",
        a,
        b,
    );
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
            program(&nested_chain(n, params)),
            program(&nested_chain(large, params)),
        );
        let (a, b) = scaling::on_a_thread(1 << 29, || {
            (term_bounds(&small_src), term_bounds(&large_src))
        });
        assert!(
            a > 0,
            "parameters {params}: `pa_bounds` did not run at d = {n}"
        );
        scaling::hold_linear(
            &format!("a chain of sums under tests, parameters {params}, d = {n} and {large}"),
            "runs of `pa_bounds`",
            a,
            b,
        );
    }
}

#[test]
fn tests_of_a_name_over_many_inputs_take_the_bounds_of_the_inputs_they_narrow() {
    // `k` tests of `z`, a sum of `k` inputs, each read through its summary (item
    // PA-letpre-linear).
    let n = 40;
    let large = n * scaling::FACTOR;
    let (small_src, large_src) = (
        program(&tests_of_one_sum(n)),
        program(&tests_of_one_sum(large)),
    );
    let (a, b) = scaling::on_a_thread(1 << 29, || {
        (term_bounds(&small_src), term_bounds(&large_src))
    });
    assert!(a > 0, "`pa_bounds` did not run at k = {n}");
    scaling::hold(
        &format!("k tests of a sum of k inputs, k = {n} and {large}"),
        "runs of `pa_bounds`",
        a,
        b,
        1,
    );
}

#[test]
fn satellites_of_two_hubs_keep_the_stars_of_their_hubs_in_linear_time() {
    // The else-arm of level `i` gives `ai` conjuncts of both signs, `ai >= n` and `ai < m`, in
    // one of its cases, so `ai` has no shape and its conjuncts are free at `n` and `m`. Before
    // item STAR-hub-set the hubs then admitted none of the `k` stars `aj >= n && aj >= m`
    // above, which went into one block of the forest, projected at each level: 21.5 times the
    // bytes for 8 times the levels on main at b5a32b5c. `ai` is a satellite now, related to
    // `n` and `m` alone, which the hubs admit.
    // The size stays 24, though the larger run takes 0.5 s: at 240 and 1920 the checker took
    // 21.5 times the instructions and 14.2 times the bytes (TEST-bench-move-l0139, 2026-11-14;
    // plan row STAR-satellite-scale).
    check_alone(
        "k levels of stars of two hubs over satellites",
        24,
        1,
        |k| negated_hub_nest(k, |i| format!("#s{i}")),
    );
}

#[test]
fn reads_under_the_else_arms_of_satellites_of_two_hubs_scale() {
    // The nest above with `popCount(ai)` in each else-arm in place of a type: `k` rejections,
    // since `ai` may be below 0 there.
    check_rejected_in_linear_work(
        "k levels of stars of two hubs with a read in each else-arm",
        140,
        |k| negated_hub_nest(k, |i| format!("popCount(a{i})")),
    );
}
