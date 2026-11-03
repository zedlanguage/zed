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

/// The work `run.load` does on each of `srcs`, at sizes `n` and `8n`, on a stack that holds
/// `8n` levels: the parser and the checker recurse once a level, as step L1.28's tests of deep
/// bodies allow for.
fn check_load(what: &'static str, n: usize, power: u32, src: impl Fn(usize) -> String) {
    let srcs: HashMap<usize, String> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, src(m)))
        .collect();
    let t = std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(move || {
            scaling::check_order(what, n, power, |m| {
                zedc::run::load(srcs[&m].as_bytes()).unwrap_or_else(|e| panic!("{e}"));
            });
        });
    t.unwrap().join().unwrap();
}

#[test]
fn the_checker_reads_each_operand_of_a_nest_once() {
    // `x = bitAnd(bitAnd(…bitAnd(1, 1)…, 1), 1);`, `n` calls deep. Each call checks its
    // operands' domains from what their text shows; each expression is read once, so the nest
    // is checked in O(n). Read again at each call, it is O(n²): 37 times the work at 300 and
    // 2400 against 8 times.
    check_load("checking a nest of n bit-word calls", 300, 1, |n| {
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
    check_load(
        "checking a chain of n bindings of bit-word calls",
        200,
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
    check_load(
        "checking an unread constant 3 ** e + 5 ** e",
        200_000,
        0,
        |e| with_main(format!("x = 3 ** {e} + 5 ** {e};\n")),
    );
}
