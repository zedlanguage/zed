//! The programs that left the census after its snapshots were taken, each checked to be decided
//! rightly before the snapshots were accepted without it (plan row
//! FAIL-census-programs-8-9-stale-snapshots, and for pieces 4 and 9
//! PRES-solver-equation-sign-free). A program, or one question of a test function, leaves the
//! census when the checker stops refusing it; that is right only if the answers it now gives
//! are the true ones. For each program the test asks the checker's two questions of its test function `ok`, whether
//! the condition can be true and whether it can be false (the questions `front` asks, through
//! `preimage::Scoped` and `Extending::defined_with`), and compares both answers with the
//! interpreter's values of `ok` at every point of a window that holds every case.

use std::sync::Arc;

use zed_kernel::{Shared, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zed_tests::step_helpers::l01_38_presburger::points::{at, window};
use zedc::elab::Cones;
use zedc::interp::prelude;
use zedc::query::Db;
use zedc::store::preimage::Scoped;
use zedc::store::presburger::extend::Extending;

use super::{programs, refusals};

/// A program of `programs.txt` that the census listed as refused, by the hash in its origin;
/// the window `lo..=hi` on every parameter of `ok` in which the interpreter is asked; and
/// whether `ok` can be true and whether it can be false; and, for a program on the bit words at
/// negative operands, which the interpreter refuses until INT-twos (DESIGN step L1.39d), `ok`
/// written in Rust with the two's-complement `&` of `i64` that L1.39d defines, asked in place
/// of the interpreter.
struct Left {
    hash: &'static str,
    lo: i64,
    hi: i64,
    can_hold: bool,
    can_fail: bool,
    twos: Option<fn(&[i64]) -> bool>,
}

/// The programs gone from pieces 8, 9 and 11. Each window holds every case of its program, so the
/// interpreter's values in it are a complete search:
/// - `baf57900`, `0 <= x && x <= 9 && 0 <= y && y <= 9 && 1 <= x + y && x + y <= 10 && (x <= 2
///   || x >= 7) && (y <= 2 || y >= 7)`: false wherever `x` or `y` is outside `0..=9`, so the
///   window `-1..=10` holds every point where it can be true and points where it is false. True
///   at `x = 0, y = 1`. Decided since 1e2056506 (FAIL-or-if-tie-refusal), which searches a tie
///   that the swap of `x` and `y` maps onto itself.
/// - the five of the form `(if a > 0 { 2 } else { 0 }) + (if b > 0 { 2 } else { 0 }) != 3`,
///   with the parameters renamed and the two conditionals in either order: the value depends
///   only on whether each parameter is positive, so the window `-1..=1` holds every case; the
///   sum is 0, 2 or 4, never 3, so `ok` is always true. Decided since e0a174b59
///   (PREIMAGE-tie-indep-let), though its coloring over the formula's nesting does not tell the
///   two parameters apart: `!= 3` was answered by the disjuncts of least color that
///   `settle_tied` chooses, and `!= 0` or `!= 4` was refused. Decided for every constant since
///   FAIL-tie-sum-ne-constant-refused (`Renamed::individualized`, and
///   `ladder::a_symmetric_sum_of_two_conditionals_is_decided_alike_on_every_path`).
/// - `143e2a38`, `bitAnd(a, b) <= -1 && bitAnd(a, b) <= a && bitAnd(a, b) <= b`, and
///   `e57066cb`, `0 <= bitAnd(i, n) && bitAnd(i, n) <= n && bitAnd(i, n) <= i`: refused as
///   `Unordered` on "can be false" (both) and "can be true" (`e57066cb`) until
///   FAIL-tie-sum-ne-constant-refused (`Renamed::individualized`; that the two operands tie
///   only jointly with other atoms of the bit and is inferred, not traced). Both answers are
///   true for both, so a point of each answer suffices, and the window `-2..=1` holds every
///   pair of signs of the operands: `143e2a38` is true at `a = b = -1` and false at
///   `a = b = 0`; `e57066cb` is true at `i = n = 0` and false at `i = n = -1`, false only at
///   negative operands. Both are asked of `twos`, since the interpreter refuses a negative
///   operand of `bitAnd` until INT-twos.
const LEFT: [Left; 8] = [
    Left {
        hash: "baf57900",
        lo: -1,
        hi: 10,
        can_hold: true,
        can_fail: true,
        twos: None,
    },
    Left {
        hash: "563b4155",
        lo: -1,
        hi: 1,
        can_hold: true,
        can_fail: false,
        twos: None,
    },
    Left {
        hash: "91584121",
        lo: -1,
        hi: 1,
        can_hold: true,
        can_fail: false,
        twos: None,
    },
    Left {
        hash: "25b276c1",
        lo: -1,
        hi: 1,
        can_hold: true,
        can_fail: false,
        twos: None,
    },
    Left {
        hash: "a273297f",
        lo: -1,
        hi: 1,
        can_hold: true,
        can_fail: false,
        twos: None,
    },
    Left {
        hash: "d377740e",
        lo: -1,
        hi: 1,
        can_hold: true,
        can_fail: false,
        twos: None,
    },
    Left {
        hash: "143e2a38",
        lo: -2,
        hi: 1,
        can_hold: true,
        can_fail: true,
        twos: Some(|p| {
            let x = p[0] & p[1];
            x <= -1 && x <= p[0] && x <= p[1]
        }),
    },
    Left {
        hash: "e57066cb",
        lo: -2,
        hi: 1,
        can_hold: true,
        can_fail: true,
        twos: Some(|p| {
            let x = p[0] & p[1];
            0 <= x && x <= p[1] && x <= p[0]
        }),
    },
];

/// A test function of a program of `programs.txt` that the census still lists for other
/// refusals, one or both of whose questions the census listed as refused and no longer does:
/// the program by the hash in its origin, the function, the window `lo..=hi` on its parameter,
/// and the answers to the questions that left, `None` for a question still refused.
struct LeftQuestion {
    hash: &'static str,
    name: &'static str,
    lo: i64,
    hi: i64,
    can_hold: Option<bool>,
    can_fail: Option<bool>,
}

/// The questions gone from pieces 4 and 9 with PRES-solver-equation-sign-free, which colors an
/// equation's two sides alike, so that no elimination order hangs on the sign an equation is
/// written with. Each window holds every case:
/// - `da5845a7`, `h_k(x) = (3 * h_(k-1)(x)) div 2 + 1` from `h0(x) = x`, and `t_k(x) =
///   h_k(x: x) mod 2 == 1 && x < 7 && x > 0 - 7`: false wherever `x` is outside `-6..=6`, so the
///   window `-8..=8` holds every point where it can be true and points where it is false. The
///   questions of `t5` and the first of `t3` and `t4` are still refused (Shadows).
/// - `0085bcdc`, `h_k(x) = (5 * h_(k-1)(x) + 2) div 3` from `h0(x) = x`, and `t_k(x) = h_k(x: x)
///   == 7 || h_k(x: x) == 12`: each `h_k` is nondecreasing in `x`, below 7 at `x = -10` and above
///   12 at `x = 10` (`h1(-10) = -16`, `h1(10) = 17`, and each step keeps the sign of the gap), so
///   `t_k` is false outside the window `-10..=10`.
const LEFT_QUESTIONS: [LeftQuestion; 6] = [
    LeftQuestion {
        hash: "da5845a7",
        name: "t2",
        lo: -8,
        hi: 8,
        can_hold: Some(true),
        can_fail: Some(true),
    },
    LeftQuestion {
        hash: "da5845a7",
        name: "t3",
        lo: -8,
        hi: 8,
        can_hold: None,
        can_fail: Some(true),
    },
    LeftQuestion {
        hash: "da5845a7",
        name: "t4",
        lo: -8,
        hi: 8,
        can_hold: None,
        can_fail: Some(true),
    },
    LeftQuestion {
        hash: "da5845a7",
        name: "t5",
        lo: -8,
        hi: 8,
        can_hold: None,
        can_fail: Some(true),
    },
    LeftQuestion {
        hash: "0085bcdc",
        name: "t3",
        lo: -10,
        hi: 10,
        can_hold: Some(true),
        can_fail: Some(true),
    },
    LeftQuestion {
        hash: "0085bcdc",
        name: "t4",
        lo: -10,
        hi: 10,
        can_hold: Some(true),
        can_fail: Some(true),
    },
];

/// The program of `programs.txt` whose origin ends with `#hash`.
fn program(hash: &str) -> (&'static str, &'static str) {
    let suffix = format!("#{hash}");
    (programs::all().iter())
        .find(|(o, _)| o.ends_with(&suffix))
        .map(|(o, t)| (o.as_str(), t.as_str()))
        .unwrap_or_else(|| panic!("{suffix} is a program of programs.txt"))
}

/// Checks the checker's answers to whether the test function `name` of `text` can be true and
/// whether it can be false, each where it is `Some`, against those answers and against the
/// interpreter's values of `name` at every point of the window `lo..=hi` on each parameter,
/// which must hold every case; or, where `twos` is given, against its values there in place of
/// the interpreter's ([`Left`]).
fn check(
    origin: &str,
    text: &str,
    name: &str,
    (lo, hi): (i64, i64),
    can_hold: Option<bool>,
    can_fail: Option<bool>,
    twos: Option<fn(&[i64]) -> bool>,
) {
    let unit = elab(text).unwrap_or_else(|e| panic!("{origin}: {e:?}"));
    let lets = prelude(
        (unit.defs.iter().rev()).fold(Term::Lit(Value::Bool(true)), |body, d| {
            Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
        }),
    );
    let (ps, body): (&[Arc<str>], &Term) = (unit.defs.iter())
        .find_map(|d| match &*d.term {
            Term::Lam(ps, body) if d.name.as_str() == name => Some((ps.as_slice(), &**body)),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{origin} defines `{name}`"));

    let mut scoped = Scoped::new(&lets);
    let r = (scoped.relation(body, ps, ps, true))
        .unwrap_or_else(|| panic!("{origin}: `{name}` is a linear question"));
    let answers = Extending::new().defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));

    let closed = prelude(Cones::new(&unit).close(body.clone()));
    let values: Vec<bool> = (window(ps.len(), lo, hi).iter())
        .map(|p| match twos.map_or_else(|| at(&closed, ps, p), |f| Some(Value::Bool(f(p)))) {
            Some(Value::Bool(b)) => b,
            v => panic!("{origin}: `{name}` at {p:?} gives {v:?}, not a truth value"),
        })
        .collect();
    if let Some(can_hold) = can_hold {
        assert_eq!(
            answers.holds.as_ref().ok(),
            Some(&can_hold),
            "{origin}: can `{name}` be true"
        );
        assert_eq!(
            values.contains(&true),
            can_hold,
            "{origin}: the interpreter's values of `{name}` in the window hold somewhere"
        );
    }
    if let Some(can_fail) = can_fail {
        assert_eq!(
            answers.fails.as_ref().ok(),
            Some(&can_fail),
            "{origin}: can `{name}` be false"
        );
        assert_eq!(
            values.contains(&false),
            can_fail,
            "{origin}: the interpreter's values of `{name}` in the window fail somewhere"
        );
    }
}

#[test]
fn each_program_that_left_the_census_is_decided_rightly() {
    for left in &LEFT {
        let (origin, text) = program(left.hash);
        let mut out = String::new();
        refusals(origin, text, &mut out);
        assert!(out.is_empty(), "{origin} has a refusal:\n{out}");
        check(
            origin,
            text,
            "ok",
            (left.lo, left.hi),
            Some(left.can_hold),
            Some(left.can_fail),
            left.twos,
        );
    }
}

#[test]
fn each_question_that_left_the_census_is_decided_rightly() {
    for left in &LEFT_QUESTIONS {
        let (origin, text) = program(left.hash);
        let mut out = String::new();
        refusals(origin, text, &mut out);
        let line = |l: &str, q: &str| {
            l.contains(&format!("the condition of `{}`", left.name))
                && l.contains(&format!("can be {q} for"))
        };
        for (asked, q) in [(left.can_hold, "true"), (left.can_fail, "false")] {
            assert!(
                asked.is_none() || !out.lines().any(|l| line(l, q)),
                "{origin}: whether `{}` can be {q} is refused:\n{out}",
                left.name
            );
        }
        check(
            origin,
            text,
            left.name,
            (left.lo, left.hi),
            left.can_hold,
            left.can_fail,
            None,
        );
    }
}

/// `1bbf06aa`, whose `f(a, x, y, z, w)` divides by `a + 1` (at 3:44) where `x < 3` under the
/// guard `a - w - x - y - z >= 0 && 4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x
/// - 10 * y - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && 0 - 8 * w - 5 * x + 12
/// * y - z + 31 >= 0`: the census listed a Growth warning there, and no longer lists one, nor
/// any warning of a division by zero. That is right because no whole numbers meet the guard with
/// `x < 3`: over the rationals its last four rows and `x <= 2` give `1.36 <= x`, `-0.95 <= y <=
/// -0.24`, `-0.41 <= z <= 0.55` and `1.13 <= w <= 2.24` (lp_solve), so `y` has no whole value
/// (z3 also finds no integer point). The window `-1..=3` on each of the five parameters holds
/// that box with `a = -1`, so the interpreter's values of the guard with `x < 3 && a + 1 == 0`
/// there are a complete search. (The checker refuses the guard as a test of its own, so only the
/// interpreter answers it here.)
#[test]
fn the_divisor_of_the_unreachable_branch_left_the_census_rightly() {
    let (origin, text) = program("1bbf06aa");
    let mut out = String::new();
    refusals(origin, text, &mut out);
    assert!(
        !out.lines().any(|l| l.split('\t').nth(1) == Some("3:44")),
        "{origin}: the division by `a + 1` is refused:\n{out}"
    );
    let warnings = match &*Db::new().front(text) {
        Ok((_, _, warnings)) => warnings.clone(),
        Err(ds) => panic!("{origin} is rejected: {ds:?}"),
    };
    assert!(
        !warnings.iter().any(|d| (d.line, d.col) == (3, 44)),
        "{origin}: a warning at 3:44"
    );
    let guard = "ok(a: int, x: int, y: int, z: int, w: int) = a - w - x - y - z >= 0 && 4 * x - 12 \
                 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y - 11 * z - 28 >= 0 \
                 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && 0 - 8 * w - 5 * x + 12 * y - z + 31 \
                 >= 0 && x < 3 && a + 1 == 0;\n";
    let unit = elab(guard).unwrap_or_else(|e| panic!("{origin}: {e:?}"));
    let (ps, body): (&[Arc<str>], &Term) = (unit.defs.iter())
        .find_map(|d| match &*d.term {
            Term::Lam(ps, body) => Some((ps.as_slice(), &**body)),
            _ => None,
        })
        .expect("the guard is a function");
    let closed = prelude(Cones::new(&unit).close(body.clone()));
    let point = (window(ps.len(), -1, 3).into_iter())
        .find(|p| at(&closed, ps, p) != Some(Value::Bool(false)));
    assert_eq!(point, None, "{origin}: the guard with `x < 3` holds or fails to evaluate");
}
