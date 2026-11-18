//! The shortcuts of 4e3f47abc (CHECK-literal-union-spaced, part 1) against the walks they skip
//! (TEST-ints-listed-shortcut-off): a reduction that finds a finite set filling its interval
//! by the interval's integer count (`fills`), one that cuts the set's members in an interval
//! a test narrowed (`kept_by_listed`), and a test that reads a name's interval as its listed
//! members (`ints_all_listed`). Each random program is checked with the shortcuts on and off
//! (`listed_shortcuts::off`), and the two checks must give the same verdict and message.
//!
//! The programs call a callee whose arms give integer literals, spaced at random so that the
//! interval of its result has several pieces, from tests that compare the call, or a name bound
//! to it, with constants near the literals, nested so that a second test narrows an interval
//! the first already narrowed. Each arm reads `popCount` of the call's input or result minus a
//! constant, rejected where the test lets that be negative.
//!
//! What it can see: a shortcut that narrows a domain more than the walk does changes a
//! verdict or a message (a `kept_by_listed` that cut only the interval's first piece made 97 of
//! the 400 programs differ, the first at round 1). A shortcut that only leaves a domain wider
//! than the walk does, where another domain of the product already holds the narrower bound
//! (a `kept_by_listed` with no count test, which keeps members the interval excludes), changes
//! no result, and neither these checks nor the arms' scopes of the store's walk
//! (`store::product::arms`, tried: they did not differ even under the first-piece break, so
//! they are not compared here) show it. The unit test
//! `product::tests::the_listed_shortcuts_give_what_the_walks_give` in zedc-preimage compares
//! `kept_by_listed` and `ints_all_listed` with the walks as exactly equal sets, and fails with
//! the count test or the subset test taken out. `fills` comparing the counts by `>=` gives the
//! same answers as `==`, since a set inside an interval never has more members than the
//! interval has integers (checked in `the_members_kept_by_an_interval_are_those_a_filter_keeps`).

use zed_tests::instances::Rng;
use zedc::run::load;
use zedc::store::product::listed_shortcuts;

fn check(src: &str) -> Option<String> {
    let src = format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n");
    load(src.as_bytes()).err()
}

const OPS: [&str; 6] = [">", "<", ">=", "<=", "==", "!="];

/// A callee `f` of `k + 1` arms, `x < j` for `j` in `0..k` and a last `else`, each giving a
/// literal: rising by random steps of 1 to 4 from a random start, so runs of adjacent
/// literals join into one piece and the others stand apart, or, one time in four, in random
/// order with repeats.
fn callee(rng: &mut Rng) -> (String, Vec<i64>) {
    let k = rng.int(1, 10) as usize;
    let mut lits = Vec::with_capacity(k + 1);
    let mut v = rng.int(-8, 8);
    let shuffled = rng.below(4) == 0;
    for _ in 0..=k {
        lits.push(if shuffled { rng.int(-12, 12) } else { v });
        v += rng.int(1, 4);
    }
    let mut f = format!("f(positional x: int) = if x < 0 {{ {} }}", lits[0]);
    for (j, l) in lits.iter().enumerate().take(k).skip(1) {
        f.push_str(&format!(" else if x < {j} {{ {l} }}"));
    }
    f.push_str(&format!(" else {{ {} }};\n", lits[k]));
    (f, lits)
}

/// A constant near the literals: one of them, or one of them moved by 1 or 2.
fn near(rng: &mut Rng, lits: &[i64]) -> i64 {
    rng.pick(lits) + rng.int(-2, 2)
}

/// One test of `subject` against a constant, whose arm reads `popCount` of `x` or of `y`
/// minus a constant, or holds a second test (`depth` deep at most).
fn test(rng: &mut Rng, subject: &str, lits: &[i64], k: i64, depth: usize) -> String {
    let op = rng.pick(&OPS);
    let c = near(rng, lits);
    let d = rng.int(1, 3);
    let (lhs, c) = match rng.below(6) {
        0 => (format!("{subject} + {d}"), c + d),
        1 => (format!("2 * {subject}"), 2 * c + rng.int(0, 1)),
        2 => (format!("{subject} mod {}", d + 1), rng.int(0, d)),
        3 => ("x".to_string(), rng.int(-1, k)),
        _ => (subject.to_string(), c),
    };
    let subject_test = format!("{lhs} {op} {c}");
    let arm = if depth > 0 && rng.below(2) == 0 {
        test(rng, subject, lits, k, depth - 1)
    } else if subject == "y" && rng.below(2) == 0 {
        format!("popCount(y - {})", near(rng, lits))
    } else {
        format!("popCount(x - {})", rng.int(-1, k))
    };
    format!("(if {subject_test} {{ {arm} }} else {{ 0 }})")
}

/// A random program: the callee and a function `g` of 1 to 4 tests, on `f(x)` itself or on a
/// name `y` bound to it.
fn program(rng: &mut Rng) -> String {
    let (f, lits) = callee(rng);
    let k = lits.len() as i64 - 1;
    let named = rng.below(2) == 0;
    let subject = if named { "y" } else { "f(x)" };
    let tests: Vec<String> = (0..rng.int(1, 4))
        .map(|_| test(rng, subject, &lits, k, 2))
        .collect();
    let sum = tests.join(" + ");
    if named {
        format!("{f}g(positional x: int) {{\n  y = f(x);\n  return {sum};\n}}\n")
    } else {
        format!("{f}g(positional x: int) = {sum};\n")
    }
}

/// The same verdict and message for every program with the shortcuts on and off, at a fixed
/// seed.
#[test]
fn checks_agree_with_the_listed_shortcuts_on_and_off() {
    let seed = 0x4e3f_47ab_c0de_0001;
    let mut rng = Rng::new(seed);
    for round in 0..400 {
        let src = program(&mut rng);
        let on = check(&src);
        let off = listed_shortcuts::off(|| check(&src));
        assert_eq!(
            on, off,
            "seed {seed:#x}, round {round}: shortcuts on (left) and off (right) differ on\n{src}"
        );
    }
}

/// The controls of the random programs' shape: a test that keeps `f(x)` at 9 or more lets
/// only `x >= 2` through, so `popCount(x - 2)` is accepted and `popCount(x - 3)` rejected; and
/// the same through a name bound to the call, read again by a second test. Both ways agree.
#[test]
fn the_shape_reaches_both_verdicts() {
    let f = "f(positional x: int) = if x < 0 { 0 } else if x < 1 { 3 } else if x < 2 { 6 } \
             else { 9 };\n";
    let cases = [
        (
            "g(positional x: int) = if f(x) > 7 { popCount(x - 2) } else { 0 };\n",
            true,
        ),
        (
            "g(positional x: int) = if f(x) > 7 { popCount(x - 3) } else { 0 };\n",
            false,
        ),
        (
            "g(positional x: int) {\n  y = f(x);\n  return \
             (if y > 2 { if y != 6 { popCount(y - 3) } else { 0 } } else { 0 });\n}\n",
            true,
        ),
        (
            "g(positional x: int) {\n  y = f(x);\n  return \
             (if y > 2 { if y != 6 { popCount(y - 4) } else { 0 } } else { 0 });\n}\n",
            false,
        ),
    ];
    for (g, accepted) in cases {
        let src = format!("{f}{g}");
        let on = check(&src);
        assert_eq!(on.is_none(), accepted, "{src}{on:?}");
        assert_eq!(on, listed_shortcuts::off(|| check(&src)), "{src}");
    }
}
