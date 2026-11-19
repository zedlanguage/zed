//! The precedence levels of the grammar's expressions, from the loosest form of `Expr` to a
//! `Primary`, as sec:grammar orders them. An operand written at a lower level than its place
//! needs is parenthesized, and no other (P191). One table for the two printers that write
//! minimal parentheses: the source formatter (`zedc-syntax` `format`) and [`super::written`],
//! the printer of a term for a message.

use crate::term::Prim;

/// A lambda, `x -> e`, and a sort key.
pub const LAMBDA: u8 = 0;
/// `e else d`, and a `for` as an operand.
pub const ELSE: u8 = 1;
/// `||`.
pub const OR: u8 = 2;
/// `&&`.
pub const AND: u8 = OR + 1;
/// `==` and `!=`.
pub const EQUALITY: u8 = 4;
/// `<`, `<=`, `>`, `>=`, `is` and `in`.
pub const RELATION: u8 = 5;
/// `with`, `><` and the remaps.
pub const REDUCE: u8 = 6;
/// `a..b` and the other ranges.
pub const RANGE: u8 = 7;
/// A call written infix, `a ~f~ b`.
pub const INFIX: u8 = 8;
/// `+`, `-` and `++`.
pub const ADDITIVE: u8 = 9;
/// `*`, `/`, `div` and `mod`.
pub const MULTIPLICATIVE: u8 = ADDITIVE + 1;
/// A prefix `-` or `!`.
pub const PREFIX: u8 = 11;
/// `^`.
pub const POWER: u8 = 12;
/// A call, an index, a member and the other suffixes.
pub const POSTFIX: u8 = 13;
/// A name, a literal, a bracketed form, a block, an `if` and a `match`.
pub const PRIMARY: u8 = 14;

/// The level of the binary operator the primitive `p` is written as, if it is one: `Or` to
/// `Pow`. The order follows sec:grammar's rules `Or` to `Power`. O(1).
pub fn binary(p: Prim) -> Option<u8> {
    Some(match p {
        Prim::Or => OR,
        Prim::And => AND,
        Prim::Eq | Prim::Ne => EQUALITY,
        Prim::Lt | Prim::Le | Prim::Gt | Prim::Ge => RELATION,
        Prim::Add | Prim::Sub | Prim::Concat => ADDITIVE,
        Prim::Mul | Prim::Div | Prim::IntDiv | Prim::Mod => MULTIPLICATIVE,
        Prim::Pow => POWER,
        _ => return None,
    })
}

/// The lowest levels the left and the right operand of a binary operator of level `level`
/// are written at with no parentheses. The operators of one level group from the left, so the
/// right operand is one level up (`a - (b - c)`); comparisons do not chain, so both of
/// theirs are (`(a < b) < c` keeps its parentheses); `^` groups from the right, takes a
/// postfix expression on its left (`(-x)^2`) and a prefix one on its right (`x^-k`). O(1).
pub fn operands(level: u8) -> (u8, u8) {
    match level {
        POWER => (POSTFIX, PREFIX),
        EQUALITY | RELATION => (level + 1, level + 1),
        _ => (level, level + 1),
    }
}
