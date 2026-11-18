//! Random-term helpers of step L1.38 (tests/steps/l01_38_presburger/random.rs); in `pncx`, those
//! of pncx_probe.rs; in `points`, the point and window helpers of both L1.38 folders; in
//! `small_cost`, those of small_cost.rs; and [`solver_alone`] and [`project_alone`], for the
//! tests of the solver's hull under the exact cover.

use zed_kernel::{Prim, Shared, Term, Value};
use zedc::store::presburger::exact::EXACT_OFF;
use zedc::store::presburger::{Atom, Each, Formula, Refusal, project_each, project_each_exact};

use crate::instances::Rng;

pub mod pncx;
pub mod points;
pub mod small_cost;

fn lit(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

/// A random integer term over `x` and `y` that the domain states, of depth at most `d`.
pub fn int_term(rng: &mut Rng, d: u32) -> Term {
    if d == 0 || rng.below(3) == 0 {
        return match rng.below(5) {
            0 | 1 => Term::Var("x".into()),
            2 | 3 => Term::Var("y".into()),
            _ => lit(rng.int(-6, 6)),
        };
    }
    let sub = |rng: &mut Rng| int_term(rng, d - 1);
    let nonzero = |rng: &mut Rng| {
        let c = rng.int(1, 5);
        lit(if rng.below(3) == 0 { -c } else { c })
    };
    match rng.below(11) {
        0 | 1 => prim(Prim::Add, vec![sub(rng), sub(rng)]),
        2 => prim(Prim::Sub, vec![sub(rng), sub(rng)]),
        3 => prim(Prim::Mul, vec![lit(rng.int(-3, 3)), sub(rng)]),
        4 => prim(Prim::IntDiv, vec![sub(rng), nonzero(rng)]),
        5 => prim(Prim::Mod, vec![sub(rng), nonzero(rng)]),
        6 => prim(Prim::Neg, vec![sub(rng)]),
        7 => prim(Prim::Abs, vec![sub(rng)]),
        8 => prim(rng.pick(&[Prim::Min, Prim::Max]), vec![sub(rng), sub(rng)]),
        _ => Term::If(
            Shared::new(bool_term(rng, d - 1)),
            Shared::new(sub(rng)),
            Shared::new(sub(rng)),
        ),
    }
}

/// A random test over `x` and `y` that the domain states, of depth at most `d`.
pub fn bool_term(rng: &mut Rng, d: u32) -> Term {
    let cmp = |rng: &mut Rng| {
        let p = rng.pick(&[Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge, Prim::Eq, Prim::Ne]);
        prim(p, vec![int_term(rng, d), int_term(rng, d)])
    };
    if d == 0 || rng.below(2) == 0 {
        return cmp(rng);
    }
    let sub = |rng: &mut Rng| bool_term(rng, d - 1);
    match rng.below(4) {
        0 => prim(Prim::Not, vec![sub(rng)]),
        1 => prim(Prim::And, vec![sub(rng), sub(rng)]),
        2 => prim(Prim::Or, vec![sub(rng), sub(rng)]),
        _ => Term::If(
            Shared::new(sub(rng)),
            Shared::new(sub(rng)),
            Shared::new(sub(rng)),
        ),
    }
}

/// `f()` with the solver's answer as it is, without the exact cover (`exact::EXACT_OFF`): for
/// the tests of the solver's own hull, which the cover would make exact or refuse.
pub fn solver_alone<T>(f: impl FnOnce() -> T) -> T {
    EXACT_OFF.set(true);
    let r = f();
    EXACT_OFF.set(false);
    r
}

/// `project_each(f, syms)` as the solver alone answers it ([`solver_alone`]), checked against
/// the answer with the exact cover ([`project_each_exact`]): inside the solver's set, or a
/// refusal with [`Refusal::Questions`] where the cover passed its work limit. A cover that
/// passes its limit refuses the projection (P197): it does not keep the solver's set, even
/// where that set is exact.
pub fn project_alone(f: &Formula, syms: &[Atom]) -> Each {
    let alone = solver_alone(|| project_each(f, syms)).expect("a projection");
    let covered = project_each_exact(f, syms).expect("a projection");
    for (a, c) in alone.0.iter().zip(&covered.0) {
        let inside = matches!((a, c), (Ok(a), Ok(c)) if c.is_subset(a));
        assert!(
            inside || c == a || matches!(c, Err(Refusal::Questions)),
            "{f}: the cover's {c:?} against the solver's {a:?}"
        );
    }
    alone
}
