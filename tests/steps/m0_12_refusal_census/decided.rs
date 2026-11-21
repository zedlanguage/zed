//! The programs that left the census after its snapshots were taken, each checked to be decided
//! rightly before the snapshots were accepted without it (plan row
//! FAIL-census-programs-8-9-stale-snapshots). A program leaves the census when the checker
//! stops refusing it; that is right only if the answers it now gives are the true ones. For
//! each program the test asks the checker's two questions of its test function `ok`, whether
//! the condition can be true and whether it can be false (the questions `front` asks, through
//! `preimage::Scoped` and `Extending::defined_with`), and compares both answers with the
//! interpreter's values of `ok` at every point of a window that holds every case.

use std::sync::Arc;

use zed_kernel::{Shared, Term, Value};
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zed_tests::step_helpers::l01_38_presburger::points::{at, window};
use zedc::elab::Cones;
use zedc::interp::prelude;
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

#[test]
fn each_program_that_left_the_census_is_decided_rightly() {
    for left in &LEFT {
        let suffix = format!("#{}", left.hash);
        let (origin, text) = (programs::all().iter())
            .find(|(o, _)| o.ends_with(&suffix))
            .unwrap_or_else(|| panic!("{suffix} is a program of programs.txt"));
        let mut out = String::new();
        refusals(origin, text, &mut out);
        assert!(out.is_empty(), "{origin} has a refusal:\n{out}");

        let unit = elab(text).unwrap_or_else(|e| panic!("{origin}: {e:?}"));
        let lets = prelude(
            (unit.defs.iter().rev()).fold(Term::Lit(Value::Bool(true)), |body, d| {
                Term::Let(d.kernel.clone(), d.term.clone(), Shared::new(body))
            }),
        );
        let (ps, body): (&[Arc<str>], &Term) = (unit.defs.iter())
            .find_map(|d| match &*d.term {
                Term::Lam(ps, body) if d.name.as_str() == "ok" => Some((ps.as_slice(), &**body)),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{origin} defines `ok`"));

        let mut scoped = Scoped::new(&lets);
        let r = (scoped.relation(body, ps, ps, true))
            .unwrap_or_else(|| panic!("{origin}: `ok` is a linear question"));
        let answers =
            Extending::new().defined_with(&r, &|n| scoped.def(n), &|g| scoped.interface(g));
        assert_eq!(
            answers.holds.as_ref().ok(),
            Some(&left.can_hold),
            "{origin}: can `ok` be true"
        );
        assert_eq!(
            answers.fails.as_ref().ok(),
            Some(&left.can_fail),
            "{origin}: can `ok` be false"
        );

        let closed = prelude(Cones::new(&unit).close(body.clone()));
        let values: Vec<bool> = (window(ps.len(), left.lo, left.hi).iter())
            .map(|p| {
                match left
                    .twos
                    .map_or_else(|| at(&closed, ps, p), |f| Some(Value::Bool(f(p))))
                {
                    Some(Value::Bool(b)) => b,
                    v => panic!("{origin}: `ok` at {p:?} gives {v:?}, not a truth value"),
                }
            })
            .collect();
        assert_eq!(
            (values.contains(&true), values.contains(&false)),
            (left.can_hold, left.can_fail),
            "{origin}: the interpreter's values of `ok` in the window"
        );
    }
}

/// The programs gone from pieces 0 and 1 (plan row FAIL-census-programs-0-1-stale-snapshots):
/// the forms that the bucket tests of `l01_22_type_representation::kinds` had before
/// FAIL-types-fn-param-exact-domain, where `p` takes a function whose parameter is of one type
/// and is passed `g`, whose parameter is of another (`g`'s shapes with `bool`, or a variable,
/// where `p`'s has `int`, or the reverse). A function type's domain is exact (DESIGN.md
/// sec:type_language, "Morphism types carry two domain bounds": plain `K -> V` has L = U = K,
/// and `<:` needs L2 <: L1 and U1 <: U2), so two arrows whose domains differ are not subtypes
/// either way, and `p` does not take `g`: each program is now rejected, with no refusal. Before,
/// a domain was contravariant, and the checker refused to decide whether `g`'s domain held
/// `p`'s. Seven from piece 0 and six from piece 1; `3813bbfc`, whose `p` takes a function of a
/// variable, stayed refused then, and is accepted since 2ec6b9418 ([`BOUND_BY_ONE_CARRIER`]).
const REJECTED: [&str; 13] = [
    "b5505eff", "97525023", "5e38016f", "5b302ec0", "55276f5a", "e4aeab2c", "8c5b116c", "b0e081ed",
    "1b5698a6", "887a19a2", "efec117e", "1ba72d47", "57185a17",
];

#[test]
fn each_bucket_program_whose_domains_differ_is_rejected() {
    for hash in REJECTED {
        let suffix = format!("#{hash}");
        let (origin, text) = (programs::all().iter())
            .find(|(o, _)| o.ends_with(&suffix))
            .unwrap_or_else(|| panic!("{suffix} is a program of programs.txt"));
        let mut out = String::new();
        refusals(origin, text, &mut out);
        assert!(out.is_empty(), "{origin} has a refusal:\n{out}");
        let messages: Vec<String> = match &*zedc::query::Db::new().front(text) {
            Ok(_) => panic!("{origin} is accepted"),
            Err(ds) => ds.iter().map(|d| d.message.clone()).collect(),
        };
        assert!(
            messages.iter().any(|m| m.starts_with("`p` does not take")),
            "{origin}: {messages:?}"
        );
    }
}

/// The program gone from piece 0 (plan row FAIL-census-programs-0-stale-2ec6b9418), the form
/// the test
/// `l01_22_type_representation::kinds::a_rigid_type_variable_in_a_refused_bucket_prints_by_name_in_the_shape_offered`
/// had before 2ec6b9418:
///
/// ```text
/// p(f: (x: V) -> ((int, bool) | (int, bool, bool),) | ((V, V) | (V, V, V),) for V in int) = 0;
/// q(g: (x: W) -> ((W, W),) | ((W, W, W),) for W in int) = p(f: g);
/// ```
///
/// A bounded type variable is one carrier at a call (DESIGN.md sec:type_resolution, rule 6), and
/// `int` is the one carrier of the bound `int`, so `V` and `W` are `int` at every instance. Then
/// `g` is `(x: int) -> ((int, int),) | ((int, int, int),)` and `p` takes
/// `(x: int) -> ((int, bool) | (int, bool, bool),) | ((int, int) | (int, int, int),)`: the
/// domains are the same, and each of `g`'s two results, `((int, int),)` and
/// `((int, int, int),)`, is held by the second shape of `p`'s, so `p` takes `g` and the program
/// is right to check. Before 2ec6b9418 the checker compared `V` and `W` as variables and refused
/// to choose a shape for them (`Unchosen`). With a bound of two carriers, as the l01_22 test now
/// writes (`for V in int | f64`), the choice remains and the refusal stays (that test). The
/// census does not gain the new form: `programs.txt` holds the units the step tests compiled on
/// the day of the census, and a test that changes its source later does not change that file.
const BOUND_BY_ONE_CARRIER: &str = "3813bbfc";

#[test]
fn the_bucket_program_whose_variables_are_bounded_by_one_carrier_is_accepted() {
    let suffix = format!("#{BOUND_BY_ONE_CARRIER}");
    let (origin, text) = (programs::all().iter())
        .find(|(o, _)| o.ends_with(&suffix))
        .unwrap_or_else(|| panic!("{suffix} is a program of programs.txt"));
    let mut out = String::new();
    refusals(origin, text, &mut out);
    assert!(out.is_empty(), "{origin} has a refusal:\n{out}");
    match &*zedc::query::Db::new().front(text) {
        Ok((_, _, warnings)) => assert!(
            warnings.is_empty(),
            "{origin}: {:?}",
            warnings.iter().map(|d| &d.message).collect::<Vec<_>>()
        ),
        Err(ds) => panic!(
            "{origin} is rejected: {:?}",
            ds.iter().map(|d| &d.message).collect::<Vec<_>>()
        ),
    }
    // The contrast: with `g` giving a tuple of four, which neither shape of `p`'s result holds,
    // the same reading of `V` and `W` as `int` rejects the call.
    let wider = text.replace("((W, W, W),)", "((W, W, W, W),)");
    assert_ne!(&wider, text, "{origin} writes `((W, W, W),)`");
    match &*zedc::query::Db::new().front(&wider) {
        Ok(_) => panic!("{origin} with a tuple of four is accepted"),
        Err(ds) => assert!(
            ds.iter()
                .any(|d| d.message.starts_with("`p` does not take")),
            "{origin} with a tuple of four: {:?}",
            ds.iter().map(|d| &d.message).collect::<Vec<_>>()
        ),
    }
}
