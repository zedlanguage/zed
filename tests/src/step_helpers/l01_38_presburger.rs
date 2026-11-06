//! Random-term helpers of step L1.38 (tests/steps/l01_38_presburger/random.rs).

use zed_kernel::{Prim, Shared, Term, Value};

use crate::instances::Rng;

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
