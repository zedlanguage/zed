//! The marks of a marked elaboration (step L25.8): the written nodes a mutant may change, as
//! [`elaborate_marked`](super::elaborate_marked) finds them. Which nodes, and why, is the set
//! of MUTATION.md (QUESTIONS A103).

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zedc_check::check::ty::{Ty, WrittenRange};
use zedc_syntax::lex::Span;

/// The parameter a numeric literal written as a call's argument fills (MUTATION.md 3.7, plan
/// row TESTS-L25.8-neighbors): the range it is declared with, its type in each arrow of the
/// callee's signature, and whether the argument is the literal under a written `-`. A
/// neighbor of the literal that the range, or one of these types holding the original's
/// value, does not hold is a program the checker rejects (a `u8` parameter given `255`, whose
/// neighbor `256` is no `u8`), so no mutant is made of it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Slot {
    /// The range the parameter is declared with, as `x: u8` or `x: int[-10..=0]`
    /// ([`SParam::range`](zedc_check::check::ty::SParam::range)). Its arrow types are then
    /// `int`, which holds every neighbor, so the range is what decides.
    pub range: Option<WrittenRange>,
    /// The parameter's type in each arrow, in the signature's order.
    pub tys: Arc<[Ty]>,
    /// Whether the argument is `-n` for the literal `n`.
    pub neg: bool,
}

impl Slot {
    /// Whether the neighbor `to` of the literal whose value is `was` fits the parameter: the
    /// declared range holds it, and every arrow whose parameter holds the argument's value
    /// holds the neighbor's. The checker tests each call against the range (an `InDomain` need
    /// of the signature), so a neighbor outside it is rejected whichever arrow is taken. The
    /// arrow the checker took for the original call holds the original's value, so the
    /// neighbor fits it too, and whichever arrow that was, the call is still one the checker
    /// accepts at this argument. Keeping a neighbor that some arrow holding the original does
    /// not hold would make, where that arrow is the one taken, a mutant that does not compile;
    /// dropping it where another arrow would take it loses one mutant, the cheaper error.
    /// O(arrows) tests of a value against a type, and two comparisons with the range's ends.
    pub fn fits(&self, was: &Value, to: &Value) -> bool {
        let signed = |v: &Value| match (self.neg, v) {
            (false, _) => v.clone(),
            (true, Value::Float(x)) => Value::float(-x.get()),
            (true, Value::Float32(x)) => Value::float32(-x.get()),
            (true, Value::Rat(r)) => Value::rat(r.neg()),
            (true, _) => match v.as_integer() {
                Some(n) => Value::integer(n.neg()),
                None => v.clone(),
            },
        };
        let (was, to) = (signed(was), signed(to));
        (self.range.as_ref()).is_none_or(|r| r.holds(&to))
            && (self.tys.iter())
                .filter(|t| t.contains(&was))
                .all(|t| t.contains(&to))
    }
}

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
    /// A written range `a..<b`, or `a..=b` when `through` (MUTATION.md 3.12, H12).
    Range {
        /// Whether the range is written `..=`.
        through: bool,
    },
}

/// A written node that a mutant may change (step L25.8), found by
/// [`elaborate_marked`](super::elaborate_marked).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Mark {
    /// For an operator, `&&` and `||`, or a range, the text between its operands, which holds
    /// it; for a constant, the constant; for a unary operator or an `if`, the whole expression.
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
    /// condition, then branch and else branch; a range's low end, high end and whole
    /// expression. Unused entries are empty.
    pub parts: [Span; 3],
    /// For a constant written as a call's argument, the parameter it fills ([`Slot`]).
    pub slot: Option<Slot>,
}

impl Mark {
    /// A mark of kind `kind` on `span`, its flags false, its parts empty and no slot.
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
            slot: None,
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

/// The node a marked elaboration wraps for a mark of kind [`Kind::Unary`], [`Kind::Bool`],
/// [`Kind::If`] or [`Kind::Range`], and the mark's index: such a node `t` is written
/// `and(t, k)` with `k` the index. The kernel's `and` takes two `bool`s, so no other term has
/// an integer literal as its second argument, and the wrapper is never taken for one. Proof,
/// over the terms of this
/// crate, which are what this reads: `Term::Prim(Prim::And, ..)` is built with a literal
/// second argument only in [`wrap`]. `a && b` becomes `if_(a, b, false)` (`Elab::binary`,
/// walk.rs), not `and`; a fold by `&&` is a `Term::Fold` whose operator is `Term::PrimFn`
/// (`remap_term`, walk.rs; `reducer_prim`, walk/fp_ops.rs); a scan by `&&` applies `and` to
/// variables and parts of them (`scan_push`, walk/fp_ops.rs). Any other `and` is of operands
/// the checker typed `bool`, and the elaboration of a `bool` is never an integer literal.
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
