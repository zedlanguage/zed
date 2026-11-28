//! Reading the one normal form of range bounds, sizes and costs (DESIGN.md step L1.17d,
//! sec:domains "One form for bounds, sizes and costs"; plan row KEPT-ast-normal-form) from a Zed
//! expression. The form itself, its arithmetic, order, readings and printer, is the kernel's
//! (zed-kernel `num::form`, plan row KEPT-form-into-kernel, phase 1), re-exported here so that
//! its users name it as before.
//!
//! It lives in the bootstrap checker until row KEPT-prelude-normal-form moves it into the
//! prelude as `boundNormalForm`.

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use zed_kernel::num::TooLarge;
pub use zed_kernel::num::form::*;
use zed_kernel::{Rat, Value};
use zedc_syntax::ast::{BinaryOp, Expr, ExprKind, UnaryOp};

/// Which reading an expression has (DESIGN.md L1.17d, "Two readings"). A range bound and a
/// size are exact and have no `log`; a cost is an upper bound, where `log` is base 2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reading {
    /// A range bound or a size: one value at each value of its symbols.
    Exact,
    /// A cost: a quantity at most its value, with `log` in base 2.
    Cost,
}
// ---------------------------------------------------------------------------------------------
// Reading.

/// The normal form of the Zed expression `text` under `reading`, or a message saying what it
/// cannot read: `log` outside a cost, an operator outside the ring, a division by 0.
pub fn read(text: &str, reading: Reading) -> Result<Form, String> {
    let tokens = zedc_syntax::lex::lex(text).map_err(|e| format!("{e:?}"))?;
    let tree = zedc_syntax::parse::parse(text, &tokens, "Expr", zedc_syntax::parse::TOP)
        .map_err(|e| format!("{e:?}"))?;
    let e = zedc_syntax::ast::build(text, &tokens, &tree).map_err(|e| format!("{e:?}"))?;
    from_expr(&e, reading)
}

fn too_large(e: TooLarge) -> String {
    format!("the normal form asks for more memory than the system gives: {e:?}")
}

/// The normal form of an expression of the AST.
pub fn from_expr(e: &Expr, reading: Reading) -> Result<Form, String> {
    let go = |e: &Expr| from_expr(e, reading);
    let some = |r: Result<Option<Form>, TooLarge>, what: &str| match r {
        Ok(Some(f)) => Ok(f),
        Ok(None) => Err(format!("{what} is not defined")),
        Err(e) => Err(too_large(e)),
    };
    match &e.kind {
        ExprKind::Int { radix, digits } => match Value::int_text(digits, *radix) {
            Ok(Some(Value::Int(i))) => Ok(Form::constant(Rat::int(BigInt::from(i)))),
            Ok(Some(Value::Big(r))) => Ok(Form::constant((*r).clone())),
            Ok(_) => Err(format!("`{digits}` is no integer")),
            Err(e) => Err(too_large(e)),
        },
        ExprKind::Rat(d) => match Rat::decimal(d) {
            Ok(Some(r)) => Ok(Form::constant(r)),
            Ok(None) => Err(format!("`{d}` is no rational")),
            Err(e) => Err(too_large(e)),
        },
        ExprKind::Name(x) => Ok(Form::sym(x)),
        ExprKind::Read { of, name } => match &of.kind {
            ExprKind::Name(x) => Ok(Form::sym(&format!("{x}::{name}"))),
            _ => Err("a metadata read of anything but a name".to_string()),
        },
        ExprKind::Unary(UnaryOp::Neg, a) => Ok(go(a)?.neg()),
        ExprKind::Binary(op, a, b) => {
            let (a, b) = (go(a)?, go(b)?);
            match op {
                BinaryOp::Add => a.plus(&b).map_err(too_large),
                BinaryOp::Sub => a.minus(&b).map_err(too_large),
                BinaryOp::Mul => a.mul(&b).map_err(too_large),
                BinaryOp::Div => {
                    let inv = some(b.pow_int(&BigInt::from(-1)), "a division by 0")?;
                    a.mul(&inv).map_err(too_large)
                }
                BinaryOp::Pow => some(power(&a, &b), "`0 ^ e` with `e < 0`"),
                _ => Err(format!("the operator {op:?} in a bound")),
            }
        }
        ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } if named.is_empty() => {
            let ExprKind::Name(f) = &callee.kind else {
                return Err("a call of anything but a name".to_string());
            };
            match (f.as_str(), positional.as_slice()) {
                ("log", [a]) => match reading {
                    Reading::Cost => some(log_of(&go(a)?), "`log` of a constant not above 0"),
                    Reading::Exact => Err(
                        "`log` in a range bound or a size; an integer logarithm is `ilog2(n)`"
                            .to_string(),
                    ),
                },
                ("realRoot", [cs, k]) => {
                    let ExprKind::Array(cs) = &cs.kind else {
                        return Err("`realRoot` takes an array of coefficients".to_string());
                    };
                    let int = |e: &Expr| -> Result<BigInt, String> {
                        let f = go(e)?;
                        match f.as_constant() {
                            Some(c) if c.is_integer() => c.to_integer().map_err(too_large),
                            None if f.is_zero() => Ok(BigInt::zero()),
                            _ => Err("`realRoot` takes integers".to_string()),
                        }
                    };
                    let cs = cs.iter().map(int).collect::<Result<Vec<_>, _>>()?;
                    let k = int(k)?
                        .to_u32()
                        .ok_or("`realRoot`'s index is a small integer")?;
                    Ok(Form::atom(
                        Atom::Exp(Base::Root(cs, k), Mono::one()),
                        BigInt::one(),
                    ))
                }
                _ => {
                    let args = positional.iter().map(go).collect::<Result<Vec<_>, _>>()?;
                    Ok(Form::atom(
                        Atom::Call(f.as_str().into(), args),
                        BigInt::one(),
                    ))
                }
            }
        }
        _ => Err("an expression outside the ring of bounds".to_string()),
    }
}
