//! The marks of a marked elaboration (step L25.8): the written nodes a mutant may change, as
//! [`elaborate_marked`](super::elaborate_marked) finds them. Which nodes, and why, is the set
//! of MUTATION.md (QUESTIONS A103).

use zed_kernel::{Prim, Term, Value};
use zedc_syntax::lex::Span;

/// What kind of written node a mark is on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// A binary operator of [`mutable`].
    Op,
    /// A numeric literal.
    Const,
    /// A written unary `-` or `!` not on a literal.
    Unary,
    /// `&&`, or `||` when `or`.
    Bool {
        /// Whether the operator is `||`.
        or: bool,
    },
    /// A written `if`.
    If,
}

/// A written node that a mutant may change (step L25.8), found by
/// [`elaborate_marked`](super::elaborate_marked).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Mark {
    /// For an operator or `&&` and `||`, the text between its operands, which holds it; for a
    /// constant, the constant; for a unary operator or an `if`, the whole expression.
    pub span: Span,
    /// What it is on.
    pub kind: Kind,
    /// For `*`, whether `/` is defined there (the product holds no `int`).
    pub quotient: bool,
    /// For `<`, `<=`, `>`, `>=` and `^`, whether both operands are `int`.
    pub ints: bool,
    /// For an [`arithmetic`] operator, whether it is written as an operand of another or of a
    /// written unary `-`: it is then not the root of its expression, and no `-` is inserted
    /// around it (MUTATION.md H6).
    pub inner: bool,
    /// For an operator, whether each operand is a numeric literal, under at most one `-`.
    pub literal: [bool; 2],
    /// The spans of the parts: an operator's left operand, right operand and whole
    /// expression; the operands of `&&` and `||`; a unary operator's operand; an `if`'s
    /// condition, then branch and else branch. Unused entries are empty.
    pub parts: [Span; 3],
}

impl Mark {
    /// A mark of kind `kind` on `span`, its flags false and its parts empty.
    pub fn on(span: Span, kind: Kind) -> Mark {
        let empty = Span { start: 0, end: 0 };
        Mark {
            span,
            kind,
            quotient: false,
            ints: false,
            inner: false,
            literal: [false; 2],
            parts: [empty; 3],
        }
    }
}

/// The binary operators a mutant may change: `==`, `!=`, `<`, `<=`, `>`, `>=`, `+`, `-`, `*`,
/// `/`, `div`, `mod`, `^` and string `++` (list `++` is built elsewhere and not marked).
pub fn mutable(p: Prim) -> bool {
    use Prim::*;
    matches!(
        p,
        Eq | Ne | Lt | Le | Gt | Ge | Add | Sub | Mul | Div | IntDiv | Mod | Pow | Concat
    )
}

/// The arithmetic operators: an expression of them has a root, where MUTATION.md H6 inserts a
/// `-`.
pub fn arithmetic(p: Prim) -> bool {
    use Prim::*;
    matches!(p, Add | Sub | Mul | Div | IntDiv | Mod | Pow)
}

/// The index of the mark on the operator whose term is `t`, as the marked elaboration builds
/// it: the operator itself, the last arm of the `match` that builds it once per carrier
/// (`walk::per_carrier`, each arm with the same mark), or the body of the `let`s that bind its
/// other operand where a literal follows it (`Elab::follow`).
// Complexity tradeoff: O(1) steps, at most one `match` and two `let`s, against a search of
// the marks by span, which costs the size of the subtree pushed since.
pub fn op_mark(mut t: &Term) -> Option<usize> {
    loop {
        t = match t {
            Term::Match(_, arms) => &arms.last()?.1,
            Term::Let(_, _, body) => &**body,
            Term::Prim(p, _) if mutable(*p) => return mark_of(t),
            _ => return None,
        };
    }
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

/// The node a marked elaboration wraps for a mark of kind [`Kind::Unary`], [`Kind::Bool`] or
/// [`Kind::If`], and the mark's index: such a node `t` is written `and(t, k)` with `k` the
/// index. The kernel's `and` takes two `bool`s, so no other term has an integer literal as its
/// second argument, and the wrapper is never taken for one.
pub fn wrapped(t: &Term) -> Option<(&Term, usize)> {
    match t {
        Term::Prim(Prim::And, args) => match &args[..] {
            [inner, Term::Lit(Value::Int(m))] => Some((inner, usize::try_from(*m).ok()?)),
            _ => None,
        },
        _ => None,
    }
}

/// `t` wrapped as the node of mark `k` ([`wrapped`]).
pub fn wrap(t: Term, k: usize) -> Term {
    Term::Prim(Prim::And, vec![t, Term::Lit(Value::Int(k as i64))])
}
