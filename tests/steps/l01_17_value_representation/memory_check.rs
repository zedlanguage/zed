//! Step L1.17a: the number builds left after CAP-bits ask the system for their memory first.
//! Ordering two numbers that agree in many leading bits, rounding a number that lies near a
//! rounding boundary, and printing a number inside a tuple, keypath or family each stop the
//! run with an error naming the size when the system refuses, and give the right answer
//! otherwise.
//!
//! The refusal is real: each such test runs again in a child process, builds its operands,
//! and then lowers the child's address-space limit (`RLIMIT_AS`) to what it already uses plus
//! [`MARGIN`]. An allocation that was not asked for first would then abort the child, which
//! the parent reports as a failure.

use std::process::Command;

use num_bigint::{BigInt, BigUint};
use zed_kernel::num::bytes_of;
use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Evidence, Family, FixKind, KernelError, Pattern, Prim, Rat, Term, Value, eval};
use zed_tests::kernel::{bin, get, path};
use zed_tests::scaling::check_order;

/// Set in the child process that runs a test under the lowered limit.
const CHILD: &str = "ZED_L1_17A_UNDER_LIMIT";

/// The address space the child may take beyond what it holds once its operands are built.
pub(crate) const MARGIN: u64 = 64 << 20;

/// The width, in bits, of the operands in the child: 128 MiB, twice [`MARGIN`], so building
/// any of them again is refused.
pub(crate) const WIDE: u64 = 1 << 30;

/// In the parent, runs the test `name` of this module again in a child process and returns
/// `false` once it has passed there; in the child, returns `true`.
fn in_child(name: &str) -> bool {
    in_child_at(module_path!(), name)
}

/// [`in_child`] for the test `name` of the module `module`.
pub(crate) fn in_child_at(module: &str, name: &str) -> bool {
    if std::env::var_os(CHILD).is_some() {
        return true;
    }
    let module = module.strip_prefix("steps::").unwrap_or(module);
    let full = format!("{module}::{name}");
    let out = Command::new(std::env::current_exe().expect("the test binary has a path"))
        .args(["--exact", &full, "--nocapture", "--test-threads=1"])
        .env(CHILD, "1")
        // One malloc arena, so no thread reserves a new 64 MiB heap under the limit.
        .env("MALLOC_ARENA_MAX", "1")
        // A fixed mmap threshold, so an allocation of 128 KiB or more is its own mapping, which
        // the limit counts: glibc otherwise raises the threshold to the size of each mapped
        // block freed, up to 32 MiB, and serves a later large allocation from freed heap
        // inside the limit, where it is not refused.
        .env("MALLOC_MMAP_THRESHOLD_", "131072")
        .output()
        .expect("the test binary runs");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success() && stdout.contains("1 passed"),
        "{full} under the lowered limit: {}\n{stdout}\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    false
}

/// Lowers this process's address-space limit to what it uses now plus [`MARGIN`], and checks
/// that a request of twice the margin is then refused.
pub(crate) fn lower_limit() {
    lower_limit_by(MARGIN);
}

/// Lowers this process's address-space limit to what it uses now plus `margin` bytes, and
/// checks that a request of twice the margin is then refused.
pub(crate) fn lower_limit_by(margin: u64) {
    let status = std::fs::read_to_string("/proc/self/status").expect("Linux has /proc");
    let kib: u64 = status
        .lines()
        .find_map(|l| l.strip_prefix("VmSize:"))
        .and_then(|v| v.trim().strip_suffix("kB"))
        .and_then(|v| v.trim().parse().ok())
        .expect("/proc/self/status has VmSize in kB");
    let limit = (kib << 10) + margin;
    rustix::process::setrlimit(
        rustix::process::Resource::As,
        rustix::process::Rlimit {
            current: Some(limit),
            maximum: Some(limit),
        },
    )
    .expect("a process may lower its own limit");
    let words = usize::try_from(margin / 4).expect("the margin fits a usize");
    assert!(
        Vec::<u64>::new().try_reserve_exact(words).is_err(),
        "the lowered limit refuses twice the margin"
    );
}

fn int(n: u64) -> Rat {
    Rat::int(BigInt::from(n))
}

/// `2^s`, kept as a power and not built.
fn two_to(s: u64) -> Rat {
    int(2)
        .pow(&BigUint::from(s))
        .expect("a power of two is kept")
}

/// `2^(2^100)`, kept: building it would take `2^100` bits.
fn beyond_any_memory() -> Rat {
    int(2)
        .pow(&(BigUint::from(1u32) << 100u32))
        .expect("a power of two is kept")
}

/// `2^s + 1`, built in full: a number that agrees with `2^s` in all its `s` leading bits.
fn built_above(s: u64) -> Rat {
    Rat::int((BigInt::from(1u32) << s) + 1u32)
}

fn num(r: Rat) -> Term {
    lit(Value::integer(r))
}

/// `(2^s + 2^(s-53) - 1) / 2^s`: just below the point halfway between 1 and the next `f64`,
/// so rounding it to `f64` must read all `s` bits.
fn below_half_ulp(s: u64) -> Rat {
    let n = (BigInt::from(1u32) << s) + (BigInt::from(1u32) << (s - 53)) - 1u32;
    Rat::int(n)
        .div(&two_to(s))
        .unwrap()
        .expect("a power of two is not zero")
}

fn show(t: Term) -> Term {
    prim(Prim::Show, vec![t])
}

/// Two numbers that agree in their first `2^30` bits, compared with each order operator, `min`
/// and `max` when the system has too little memory left to tell them apart.
#[test]
fn ordering_numbers_that_agree_in_many_bits_is_refused_when_memory_is_short() {
    if !in_child("ordering_numbers_that_agree_in_many_bits_is_refused_when_memory_is_short") {
        return;
    }
    let a = num(built_above(WIDE));
    let b = num(two_to(WIDE));
    lower_limit();
    for (p, op) in [
        (Prim::Lt, "<"),
        (Prim::Le, "<="),
        (Prim::Gt, ">"),
        (Prim::Ge, ">="),
        (Prim::Min, "min"),
        (Prim::Max, "max"),
    ] {
        let err = eval(&bin(p, a.clone(), b.clone())).unwrap_err();
        let KernelError::OrderTooLarge { op: o, bits } = &err else {
            panic!("{op}: {err:?}")
        };
        assert_eq!(*o, op);
        assert_eq!(
            err.to_string(),
            format!(
                "`{op}` must compare two numbers that agree in their leading digits, and the \
                 system refused the {} bytes of memory asked to read enough of their digits; \
                 the numbers are exact and have no size limit, but this machine cannot hold \
                 enough of their digits to order them",
                bytes_of(bits)
            )
        );
    }
    // `2^n + 1` is odd, so no power of 2 moves out of it: equality reads the normal forms and
    // builds nothing, so it still answers.
    assert_eq!(
        eval(&bin(Prim::Eq, a.clone(), b.clone())).unwrap(),
        Value::Bool(false)
    );
    // Numbers apart in their leading bits still order at once.
    assert_eq!(
        eval(&bin(Prim::Lt, num(two_to(WIDE - 1)), a)).unwrap(),
        Value::Bool(true)
    );
}

/// Two plain rationals of `2^30`-bit numerators are ordered by cross-multiplying, which needs
/// a product wider than the memory left.
#[test]
fn ordering_wide_rationals_is_refused_when_memory_is_short() {
    if !in_child("ordering_wide_rationals_is_refused_when_memory_is_short") {
        return;
    }
    let thirds = |k: u32| {
        let r = Rat::new((BigInt::from(1u32) << WIDE) + k, BigInt::from(3)).unwrap();
        lit(Value::rat(r))
    };
    // `2^n` is 1 more than a multiple of 3, so `(2^n + 1) / 3` and `(2^n + 4) / 3` are reduced.
    let (a, b) = (thirds(1), thirds(4));
    lower_limit();
    let err = eval(&bin(Prim::Lt, a, b)).unwrap_err();
    let KernelError::OrderTooLarge { op: "<", bits } = &err else {
        panic!("{err:?}")
    };
    assert_eq!(*bits, BigUint::from(WIDE + 3));
}

/// `==` of a built multiple of 3 and a kept power of 3 moves the 3 out of the built one, which
/// copies it; when the system refuses that copy, `==` and `!=` stop with their own error.
#[test]
fn equality_that_must_copy_a_wide_number_is_refused_when_memory_is_short() {
    if !in_child("equality_that_must_copy_a_wide_number_is_refused_when_memory_is_short") {
        return;
    }
    let built = num(Rat::int(
        BigInt::from(3) * ((BigInt::from(1u32) << WIDE) + 1u32),
    ));
    let kept = num(int(3).pow(&BigUint::from(1u32 << 20)).unwrap());
    lower_limit();
    for (p, op) in [(Prim::Eq, "=="), (Prim::Ne, "!=")] {
        let err = eval(&bin(p, built.clone(), kept.clone())).unwrap_err();
        let KernelError::EqualityTooLarge { op: o, bits } = &err else {
            panic!("{op}: {err:?}")
        };
        assert_eq!(*o, op);
        assert_eq!(
            err.to_string(),
            format!(
                "`{op}` must compare two numbers in the same normal form, which moves a prime \
                 one keeps as a power out of the other's digits, and the system refused the {} \
                 bytes of memory asked for it; the numbers are exact and have no size limit, \
                 but this machine cannot hold enough of their digits to compare them",
                bytes_of(bits)
            )
        );
    }
}

/// With memory to spare, a built power of 3 equals the same power kept, and a built multiple
/// of 3 that is not a power of 3 does not; wide plain rationals order exactly.
#[test]
fn equality_and_order_of_wide_numbers_are_exact_when_memory_is_given() {
    let k = 1u32 << 16;
    let kept = int(3).pow(&BigUint::from(k)).unwrap();
    let built = Rat::int(BigInt::from(3).pow(k));
    let other = Rat::int(BigInt::from(3) * ((BigInt::from(1u32) << k) + 1u32));
    for (p, a, b, want) in [
        (Prim::Eq, &built, &kept, true),
        (Prim::Ne, &built, &kept, false),
        (Prim::Eq, &other, &kept, false),
        (Prim::Ne, &other, &kept, true),
    ] {
        assert_eq!(
            eval(&bin(p, num(a.clone()), num(b.clone()))).unwrap(),
            Value::Bool(want),
            "{p:?}"
        );
    }
    let thirds = |j: u32| Rat::new((BigInt::from(1u32) << k) + j, BigInt::from(3)).unwrap();
    let (a, b) = (thirds(1), thirds(4));
    assert_eq!(a.try_cmp(&b), Ok(std::cmp::Ordering::Less));
    assert_eq!(b.neg().try_cmp(&a.neg()), Ok(std::cmp::Ordering::Less));
    assert_eq!(a.try_cmp(&a), Ok(std::cmp::Ordering::Equal));
    assert_eq!(
        eval(&bin(Prim::Gt, lit(Value::rat(b)), lit(Value::rat(a)))).unwrap(),
        Value::Bool(true)
    );
}

/// A lookup in a family keyed by a wide number compares the key with its neighbors in the
/// key order; when that is refused, the run stops with its own error.
#[test]
fn a_family_key_order_refused_is_an_error() {
    if !in_child("a_family_key_order_refused_is_an_error") {
        return;
    }
    let a = Value::integer(built_above(WIDE));
    let b = num(two_to(WIDE));
    let family = lit(Value::Family(Family::of([(a, 1)])));
    lower_limit();
    let err = eval(&get(family, b)).unwrap_err();
    let KernelError::KeyOrderTooLarge { bits } = &err else {
        panic!("{err:?}")
    };
    assert_eq!(
        err.to_string(),
        format!(
            "two numbers placed in a family's key order agree in their leading digits, and \
             the system refused the {} bytes of memory asked to read enough of their \
             digits; the numbers are exact and have no size limit, but this machine cannot \
             hold enough of their digits to order them",
            bytes_of(bits)
        )
    );
}

/// `f64` of a number just below a rounding boundary must read all of its bits to tell which
/// way it rounds.
#[test]
fn rounding_near_a_boundary_is_refused_when_memory_is_short() {
    if !in_child("rounding_near_a_boundary_is_refused_when_memory_is_short") {
        return;
    }
    let q = lit(Value::rat(below_half_ulp(WIDE)));
    lower_limit();
    let err = eval(&prim(Prim::CastF64, vec![q])).unwrap_err();
    let KernelError::RoundTooLarge { to, bits } = &err else {
        panic!("{err:?}")
    };
    assert_eq!(*to, "f64");
    assert_eq!(
        err.to_string(),
        format!(
            "`f64` must round a number that lies near a rounding boundary, and the system \
             refused the {} bytes of memory asked to read enough of its digits; the number \
             is exact and has no size limit, but this machine cannot hold enough of its \
             digits to round it",
            bytes_of(bits)
        )
    );
    // `1.5` is a float exactly, and reads no more than its own bits.
    let half = Rat::int(BigInt::from(3)).div(&int(2)).unwrap().unwrap();
    assert_eq!(
        eval(&prim(Prim::CastF64, vec![lit(Value::rat(half))])).unwrap(),
        Value::float(1.5)
    );
}

/// A float literal just below the point halfway between 1 and the next `f64`, `1 + 2^-53`
/// less `10^-(54 + n)`: its digits to `...203124` and then `n = 2^22` nines, parsed, resolved
/// and checked, then elaborated under a limit `margin` bytes above what the child holds.
/// Returns the one error the elaborator reports, at the literal; it does not abort. Reading
/// the digits (`Rat::decimal`) asks for 64 bits of memory a digit, about 32 MiB; rounding the
/// number then reads about `3.3 n` bits of it to tell which side of the boundary it lies on,
/// and above about 64 MiB the literal rounds (COMPLEXITY.md K30).
fn a_literal_near_a_boundary_refused_under(margin: u64) -> String {
    let literal = format!(
        "1.00000000000000011102230246251565404236316680908203124{}",
        "9".repeat(1 << 22)
    );
    let text = format!("x = {literal};\n");
    let tokens = zedc::lex::lex_fence(&text).expect("the text lexes");
    let tree = zedc::parse::parse(&text, &tokens, "Unit", zedc::parse::TOP).expect("it parses");
    let stmts = zedc::ast::unit(&text, &tokens, &tree).expect("it is a unit");
    let res = zedc::resolve::resolve(&stmts).expect("it resolves");
    let info = zedc::check::check(&stmts, &res);
    assert!(info.errors.is_empty());
    lower_limit_by(margin);
    let Err(mut errs) = zedc::elab::elaborate_checked(&stmts, &res, &info) else {
        panic!("elaborated without error")
    };
    assert_eq!(errs.len(), 1);
    assert!(text[errs[0].span.start..errs[0].span.end] == *literal);
    errs.pop().expect("one error").message
}

/// The memory asked to read the literal's 54 digits and `2^22` nines, 64 bits a digit, in bytes.
fn literal_read_bytes() -> u64 {
    8 * (54 + (1 << 22))
}

/// [`a_literal_near_a_boundary_refused_under`] 16 MiB, where reading the digits, which asked
/// for nothing, aborted the child; it asks first and is refused.
#[test]
fn a_long_decimal_literal_is_refused_when_memory_is_short() {
    if !in_child("a_long_decimal_literal_is_refused_when_memory_is_short") {
        return;
    }
    assert_eq!(
        a_literal_near_a_boundary_refused_under(16 << 20),
        format!(
            "this literal has so many digits that the system refused the {} bytes of memory \
             asked to read them; a literal has no size limit, but this machine cannot hold \
             this one's value; write fewer digits",
            literal_read_bytes()
        )
    );
}

/// [`a_literal_near_a_boundary_refused_under`] 48 MiB: the digits are read, and a round of the
/// rounding that asked for `16k` bits was given them, rose above them in num-bigint's division
/// and aborted the child; it asks for `32k` and is refused (the Complexity tradeoff in
/// `bound::round`).
#[test]
fn a_literal_near_a_rounding_boundary_is_refused_below_the_peak_of_a_round() {
    if !in_child("a_literal_near_a_rounding_boundary_is_refused_below_the_peak_of_a_round") {
        return;
    }
    let message = a_literal_near_a_boundary_refused_under(48 << 20);
    let bytes = message
        .strip_prefix(
            "this literal lies so near a rounding boundary of f64 that telling which side it \
             is on needs more of its digits than the system gives: it refused the ",
        )
        .and_then(|e| e.strip_suffix(" bytes of memory asked to read them; write fewer digits"))
        .unwrap_or_else(|| panic!("another message: {message}"));
    let bytes: u64 = bytes.parse().expect("a size in bytes");
    assert!(bytes > 1 << 19, "{bytes} bytes");
}

/// With memory to spare the same operations give the exact answers.
#[test]
fn close_numbers_order_and_round_exactly_when_memory_is_given() {
    let s = 1 << 16;
    let (a, b) = (built_above(s), two_to(s));
    for (p, want) in [
        (Prim::Lt, Value::Bool(false)),
        (Prim::Gt, Value::Bool(true)),
        (Prim::Ge, Value::Bool(true)),
        (Prim::Min, Value::integer(b.clone())),
        (Prim::Max, Value::integer(a.clone())),
    ] {
        assert_eq!(
            eval(&bin(p, num(a.clone()), num(b.clone()))).unwrap(),
            want,
            "{p:?}"
        );
    }
    assert_eq!(a.try_cmp(&b), Ok(std::cmp::Ordering::Greater));
    assert_eq!(b.try_cmp(&b), Ok(std::cmp::Ordering::Equal));
    // `2^s` is found under the key `2^s`, and `2^s + 1` is not.
    let family = lit(Value::Family(Family::of([(Value::integer(b.clone()), 7)])));
    assert_eq!(
        eval(&get(family.clone(), num(b.clone()))).unwrap(),
        Value::Int(7)
    );
    assert_eq!(eval(&get(family, num(a))).unwrap(), Value::atom("notFound"));
    // Just below the halfway point rounds down to 1; it is not a float, so the cast is
    // `#inexact`, and `to_f64` gives the rounded value.
    let q = below_half_ulp(s);
    assert_eq!(q.to_f64(), Ok(1.0));
    assert_eq!(
        eval(&prim(Prim::CastF64, vec![lit(Value::rat(q))])).unwrap(),
        Value::atom("inexact")
    );
    // Powers far apart order without building: `2^(2^40)` has 2^40 bits.
    assert_eq!(
        eval(&bin(Prim::Lt, num(two_to(1 << 40)), num(two_to(1 << 41)))).unwrap(),
        Value::Bool(true)
    );
}

/// Printing a tuple, keypath or family prints each number inside it; one of `2^100` bits is
/// refused before anything is written.
#[test]
fn printing_a_composite_holding_a_number_too_large_to_build_is_an_error() {
    let huge = || num(beyond_any_memory());
    let in_family = Value::Family(Family::of([(
        Value::Int(1),
        Value::tuple(vec![
            Value::str("total"),
            Value::integer(beyond_any_memory()),
        ]),
    )]));
    for (what, t) in [
        ("tuple", prim(Prim::Tuple, vec![huge(), lit(0)])),
        ("keypath", path(vec![lit(1), huge()])),
        ("family", lit(in_family)),
    ] {
        let err = eval(&show(t)).unwrap_err();
        let KernelError::NumberTooLarge { op, bits } = &err else {
            panic!("{what}: {err:?}")
        };
        assert_eq!((what, *op), (what, "String"));
        // The memory asked: a byte for each of its `2^100 + 2` bits and eight for each byte of
        // its text, at most `0.301 (2^100 + 2) + 2` (`Rat::text_ask`).
        assert_eq!(
            bytes_of(bits).to_string(),
            "4322886617184547919947741790226",
            "{what}"
        );
    }
}

/// Composites of numbers that fit print in full.
#[test]
fn printing_a_composite_of_numbers_that_fit_writes_each_number() {
    let n = two_to(70);
    let t = Value::tuple(vec![Value::Int(1), Value::integer(n.clone())]);
    let Value::Str(s) = eval(&show(lit(t.clone()))).unwrap() else {
        panic!("a string")
    };
    assert_eq!(s.to_string(), "(1, 1180591620717411303424)");
    let f = Value::Family(Family::of([(Value::integer(n), t.clone())]));
    let Value::Str(s) = eval(&show(lit(f))).unwrap() else {
        panic!("a string")
    };
    assert_eq!(
        s.to_string(),
        "{1180591620717411303424 -> (1, 1180591620717411303424)}"
    );
}

/// Printing a tuple of many copies of one mid-sized number writes all their digits at once:
/// the whole text is asked for, not each number's digits one at a time.
#[test]
fn printing_many_copies_of_a_number_asks_for_the_whole_text() {
    if !in_child("printing_many_copies_of_a_number_asks_for_the_whole_text") {
        return;
    }
    // 40,000 copies of a 2^14-bit number of 4,933 digits: about 197 MB of text.
    let x = Value::integer(Rat::int((BigInt::from(1u32) << (1u32 << 14)) - 1u32));
    let t = show(lit(Value::tuple(vec![x; 40_000])));
    lower_limit();
    let err = eval(&t).unwrap_err();
    let KernelError::TextTooLarge { bytes: Some(n) } = &err else {
        panic!("{err:?}")
    };
    assert!((40_000 * 4_933..40_000 * 4_950).contains(n), "{n}");
    assert_eq!(
        err.to_string(),
        format!(
            "`String` must write a text of up to {n} bytes, counting each number inside it at \
             its widest, and the system refused the memory for it; the value has no size \
             limit, but this machine cannot hold its text"
        )
    );
}

/// The memory check reads a sequence shared many times once: a number too large to build,
/// read last, after `n` copies of one tuple of `n` numbers, is refused after reading `2n`
/// values, not `n^2`.
#[test]
fn a_shared_tuple_is_checked_once_before_printing() {
    let shared = |n: usize| {
        let row = Value::tuple(vec![Value::Int(7); n]);
        let mut outer = vec![Value::integer(beyond_any_memory())];
        outer.extend(std::iter::repeat_n(row, n));
        show(lit(Value::tuple(outer)))
    };
    let n = 1 << 12;
    let inputs = [(n, shared(n)), (8 * n, shared(8 * n))];
    check_order(
        "String of n copies of one shared tuple of n numbers",
        n,
        1,
        |m| {
            let (_, t) = inputs
                .iter()
                .find(|(k, _)| *k == m)
                .expect("each size was built");
            let err = eval(t).unwrap_err();
            assert!(
                matches!(&err, KernelError::NumberTooLarge { op: "String", .. }),
                "{err:?}"
            );
        },
    );
}

/// Comparing `2^n + 1`, built, with `2^n`, kept, doubles the precision of the bounds until it
/// reaches `n` bits and then builds the two once: O(n) in all.
#[test]
fn comparing_numbers_that_agree_in_n_bits_costs_order_n() {
    let n = 1 << 22;
    let inputs: Vec<(usize, Rat, Rat)> = [n, 8 * n]
        .into_iter()
        .map(|m| (m, built_above(m as u64), two_to(m as u64)))
        .collect();
    check_order("2^n + 1 against 2^n, compared", n, 1, |m| {
        let (_, a, b) = inputs
            .iter()
            .find(|(k, _, _)| *k == m)
            .expect("each size was built");
        assert_eq!(a.try_cmp(b), Ok(std::cmp::Ordering::Greater));
        assert!(a > b);
    });
}

/// The plan's example `2 ** 2 ** 40 + 1 < 2 ** 2 ** 40 + 2` stops before the comparison: each
/// sum needs `2^40` bits, and CAP-bits refuses the sum `+` itself.
#[test]
fn the_plan_example_is_refused_at_the_sum() {
    if !in_child("the_plan_example_is_refused_at_the_sum") {
        return;
    }
    let big = || num(two_to(1 << 40));
    let t = bin(
        Prim::Lt,
        bin(Prim::Add, big(), lit(1)),
        bin(Prim::Add, big(), lit(2)),
    );
    lower_limit();
    let err = eval(&t).unwrap_err();
    let KernelError::NumberTooLarge { op, .. } = &err else {
        panic!("{err:?}")
    };
    assert_eq!(*op, "+");
}

/// `2^n + 1`, an integer of `n + 1` bits, built.
fn wide_int() -> Value {
    Value::integer(built_above(WIDE))
}

fn third() -> Value {
    Value::rat(Rat::new(BigInt::from(1), BigInt::from(3)).unwrap())
}

/// An integer and a rational at one place in two tuples, or as a family's key and the key
/// looked up, are ordered by value with the wide one read where it is held; ordering them
/// multiplies the integer by 3, which the system refuses, and each stops with its own error.
#[test]
fn ordering_a_wide_integer_against_a_rational_is_refused_when_memory_is_short() {
    if !in_child("ordering_a_wide_integer_against_a_rational_is_refused_when_memory_is_short") {
        return;
    }
    let a = lit(Value::tuple(vec![wide_int()]));
    let b = lit(Value::tuple(vec![third()]));
    let family = lit(Value::Family(Family::of([(wide_int(), 1)])));
    lower_limit();
    let err = eval(&bin(Prim::Lt, a.clone(), b)).unwrap_err();
    let KernelError::OrderTooLarge { op: "<", bits } = &err else {
        panic!("{err:?}")
    };
    assert_eq!(*bits, BigUint::from(WIDE + 3));
    let err = eval(&get(family, lit(third()))).unwrap_err();
    assert!(
        matches!(&err, KernelError::KeyOrderTooLarge { .. }),
        "{err:?}"
    );
    // A small integer is apart from the wide one by its width, and builds nothing.
    assert_eq!(
        eval(&bin(Prim::Lt, a, lit(Value::tuple(vec![Value::Int(0)])))).unwrap(),
        Value::Bool(false)
    );
}

/// `int` and `rat` of a wide integer give the same digits as the other kind, shared and not
/// copied, so they answer under a limit that refuses a copy.
#[test]
fn casting_a_wide_number_shares_its_digits() {
    if !in_child("casting_a_wide_number_shares_its_digits") {
        return;
    }
    let x = wide_int();
    lower_limit();
    let as_rat = eval(&prim(Prim::CastRat, vec![lit(x.clone())])).unwrap();
    assert_eq!(as_rat.number_kind(), Some(1));
    let back = eval(&prim(Prim::CastInt, vec![lit(as_rat)])).unwrap();
    assert_eq!(back, x);
    assert_eq!(eval(&prim(Prim::CastInt, vec![lit(x.clone())])).unwrap(), x);
}

/// The casts of numbers that fit: an integer-valued rational in the 64-bit range is an `Int`,
/// a wide one a wide `int`, and one that is not an integer is `#inexact`.
#[test]
fn casts_between_int_and_rat_keep_the_value() {
    let wide = Value::integer(built_above(1 << 12));
    let rat = |v: &Value| eval(&prim(Prim::CastRat, vec![lit(v.clone())])).unwrap();
    let int = |v: Value| eval(&prim(Prim::CastInt, vec![lit(v)])).unwrap();
    assert_eq!(int(rat(&Value::Int(-5))), Value::Int(-5));
    assert_eq!(int(rat(&wide)), wide);
    assert_eq!(rat(&wide).number_kind(), Some(1));
    assert_eq!(int(third()), Value::atom("inexact"));
    assert_eq!(int(Value::float(4.0)), Value::Int(4));
    assert_eq!(rat(&third()), third());
}

/// `3 (2^n + 1)`, built, and `3^(2^20)`, kept: testing them for equality moves the 3 out of
/// the built one, which copies it.
fn equal_only_by_a_copy() -> (Value, Value) {
    let built = Value::integer(Rat::int(
        BigInt::from(3) * ((BigInt::from(1u32) << WIDE) + 1u32),
    ));
    let kept = Value::integer(int(3).pow(&BigUint::from(1u32 << 20)).unwrap());
    (built, kept)
}

/// A `match` arm whose literal pattern must be tested for equality by a copy the system
/// refuses stops with the error of `match`, not of a family's key order.
#[test]
fn a_literal_pattern_refused_its_equality_test_is_an_error_of_match() {
    if !in_child("a_literal_pattern_refused_its_equality_test_is_an_error_of_match") {
        return;
    }
    let (built, kept) = equal_only_by_a_copy();
    let t = Term::Match(
        zed_kernel::Shared::new(lit(built)),
        vec![(Pattern::Lit(kept), lit(1)), (Pattern::Wild, lit(2))],
    );
    lower_limit();
    let err = eval(&t).unwrap_err();
    let KernelError::EqualityTooLarge { op: "match", bits } = &err else {
        panic!("{err:?}")
    };
    assert_eq!(
        err.to_string(),
        format!(
            "`match` must compare two numbers in the same normal form, which moves a prime \
             one keeps as a power out of the other's digits, and the system refused the {} \
             bytes of memory asked for it; the numbers are exact and have no size limit, \
             but this machine cannot hold enough of their digits to compare them",
            bytes_of(bits)
        )
    );
}

/// The fixpoint test of a lattice `fix` whose iterates must be tested for equality by a copy
/// the system refuses stops with the error of `fix`.
#[test]
fn a_lattice_fixpoint_test_refused_is_an_error_of_fix() {
    if !in_child("a_lattice_fixpoint_test_refused_is_an_error_of_fix") {
        return;
    }
    use zed_kernel::term::build::{lam, var};
    let (built, kept) = equal_only_by_a_copy();
    // From `built`, one step gives `kept`, and the join keeps the newer iterate.
    let t = Term::Fix {
        init: zed_kernel::Shared::new(lit(built)),
        step: zed_kernel::Shared::new(lam(&["x"], lit(kept))),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Lattice {
            join: zed_kernel::Shared::new(lam(&["a", "b"], var("b"))),
        },
        ev: Evidence::new(),
    };
    lower_limit();
    let err = eval(&t).unwrap_err();
    assert!(
        matches!(&err, KernelError::EqualityTooLarge { op: "fix", .. }),
        "{err:?}"
    );
}

/// With memory to spare, the same `match` and `fix` give their answers: the two numbers
/// differ, so the literal arm does not match, and the ascent ends at `kept`.
#[test]
fn a_literal_pattern_and_a_lattice_fixpoint_answer_when_memory_is_given() {
    use zed_kernel::term::build::{lam, var};
    let built = Value::integer(Rat::int(
        BigInt::from(3) * ((BigInt::from(1u32) << 4096u32) + 1u32),
    ));
    let kept = Value::integer(int(3).pow(&BigUint::from(1u32 << 10)).unwrap());
    let t = Term::Match(
        zed_kernel::Shared::new(lit(built.clone())),
        vec![
            (Pattern::Lit(kept.clone()), lit(1)),
            (Pattern::Wild, lit(2)),
        ],
    );
    assert_eq!(eval(&t).unwrap(), Value::Int(2));
    let t = Term::Fix {
        init: zed_kernel::Shared::new(lit(built)),
        step: zed_kernel::Shared::new(lam(&["x"], lit(kept.clone()))),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Lattice {
            join: zed_kernel::Shared::new(lam(&["a", "b"], var("b"))),
        },
        ev: Evidence::new(),
    };
    assert_eq!(eval(&t).unwrap(), kept);
}

/// Two families written together that hold numbers at one key agree there only when the
/// numbers are equal; a test of them the system refuses stops with its own error.
#[test]
fn a_family_merge_refused_its_equality_test_is_an_error() {
    if !in_child("a_family_merge_refused_its_equality_test_is_an_error") {
        return;
    }
    let (built, kept) = equal_only_by_a_copy();
    let a = lit(Value::Family(Family::of([(1, built)])));
    let b = lit(Value::Family(Family::of([(1, kept)])));
    lower_limit();
    let err = eval(&bin(Prim::Union, a, b)).unwrap_err();
    let KernelError::FamilyEqualityTooLarge { bits } = &err else {
        panic!("{err:?}")
    };
    assert_eq!(
        err.to_string(),
        format!(
            "two numbers in families, compared to tell whether they are equal, must be put \
             in the same normal form, which moves a prime one keeps as a power out of the \
             other's digits, and the system refused the {} bytes of memory asked for it; \
             the numbers are exact and have no size limit, but this machine cannot hold \
             enough of their digits to compare them",
            bytes_of(bits)
        )
    );
}

/// Negating a wide number, or its `abs` when it is negative, copies its digits, which asks the
/// system first; `abs` of a wide number that is not negative is the number itself, shared.
#[test]
fn negating_a_wide_number_is_refused_when_memory_is_short() {
    if !in_child("negating_a_wide_number_is_refused_when_memory_is_short") {
        return;
    }
    let x = wide_int();
    let minus_x = Value::integer(Rat::int(-((BigInt::from(1u32) << WIDE) + 1u32)));
    lower_limit();
    for (p, op, v) in [(Prim::Neg, "-", x.clone()), (Prim::Abs, "abs", minus_x)] {
        let err = eval(&prim(p, vec![lit(v)])).unwrap_err();
        let KernelError::NumberTooLarge { op: o, bits } = &err else {
            panic!("{op}: {err:?}")
        };
        assert_eq!((*o, bits), (op, &BigUint::from(WIDE + 2)));
    }
    assert_eq!(eval(&prim(Prim::Abs, vec![lit(x.clone())])).unwrap(), x);
}

/// With memory to spare, `-` and `abs` of wide numbers give their values.
#[test]
fn negating_a_wide_number_gives_its_value_when_memory_is_given() {
    let x = Value::integer(built_above(1 << 12));
    let minus = eval(&prim(Prim::Neg, vec![lit(x.clone())])).unwrap();
    assert_eq!(
        minus,
        Value::integer(Rat::int(-((BigInt::from(1u32) << 4096u32) + 1u32)))
    );
    assert_eq!(eval(&prim(Prim::Abs, vec![lit(minus)])).unwrap(), x);
    let q = Value::rat(Rat::new(BigInt::from(-2), BigInt::from(7)).unwrap());
    assert_eq!(
        eval(&prim(Prim::Abs, vec![lit(q)])).unwrap(),
        Value::rat(Rat::new(BigInt::from(2), BigInt::from(7)).unwrap())
    );
}
