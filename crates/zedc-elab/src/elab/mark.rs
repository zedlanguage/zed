//! The marks of a marked elaboration (step L25.8): the written operators and integer constants
//! a mutant may replace, as [`elaborate_marked`](super::elaborate_marked) finds them.

use zed_kernel::{Prim, Term, Value};
use zedc_syntax::lex::Span;

/// A written operator or integer constant that a mutant may replace (step L25.8), found by
/// [`elaborate_marked`](super::elaborate_marked).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Mark {
    /// For an operator, the text between its operands, which holds it; for a constant, the
    /// constant.
    pub span: Span,
    /// For `*`, whether `/` is defined there (the product holds no `int`).
    pub quotient: bool,
}

/// The operators a mutant may replace: `==`, `!=`, `<`, `<=`, `>`, `>=`, `+`, `-`, `*`, `/`.
pub fn mutable(p: Prim) -> bool {
    use Prim::*;
    matches!(p, Eq | Ne | Lt | Le | Gt | Ge | Add | Sub | Mul | Div)
}

/// The index of the mark on `t`, when `t` is a marked operator or constant of
/// [`elaborate_marked`](super::elaborate_marked).
pub fn mark_of(t: &Term) -> Option<usize> {
    match t {
        Term::Prim(p, args) if mutable(*p) => match &args[..] {
            [_, _, Term::Lit(Value::Int(m))] => usize::try_from(*m).ok(),
            _ => None,
        },
        Term::Prim(Prim::Neg, args) => match &args[..] {
            [Term::Lit(_), Term::Lit(Value::Int(m))] => usize::try_from(*m).ok(),
            _ => None,
        },
        _ => None,
    }
}
