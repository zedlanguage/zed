//! The laws each built-in operator carries by axiom (DESIGN.md sec:property_tracking, the
//! `Axiom` grade; written by step M0.11, read by the obligation record of step L3.8). The
//! prelude's copy is `zed/prelude/axioms.zed`, and the step tests keep the two equal.
//!
//! An entry is per arrow: an operator at one carrier. A law that every arrow of a name must
//! have, as every `+` is commutative, is listed at each carrier the kernel has. The carriers
//! are the kernel's values: `int`, `f64`, `bool` and `String`; later layers add the arrows of
//! their own carriers (`rat`, the algebras of sec:linalg) to this table.

/// A carrier: the type of an arrow's operands.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Carrier {
    /// Integers.
    Int,
    /// 64-bit floats, compared bitwise after NaN canonicalization.
    F64,
    /// Booleans.
    Bool,
    /// Strings.
    String,
}

/// A constant an axiom names, of the arrow's carrier.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Const {
    /// An integer.
    Int(i64),
    /// A float.
    F64(f64),
    /// A boolean.
    Bool(bool),
    /// A string.
    Str(&'static str),
}

/// How a function moves with one argument, in the carrier's order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tonicity {
    /// Non-decreasing.
    Up,
    /// Non-increasing.
    Down,
}

/// A law an arrow carries.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Law {
    /// `op(op(a, b), c) == op(a, op(b, c))`.
    Associative,
    /// `op(a, b) == op(b, a)`.
    Commutative,
    /// `op(a, a) == a`.
    Idempotent,
    /// `op(e, a) == a` and `op(a, e) == a`.
    Identity(Const),
    /// `op(z, a) == z` and `op(a, z) == z`.
    Zero(Const),
    /// For a unary `op`, `g(op(a)) == a` and `op(g(a)) == a`, `g` the named operator.
    Inverse(&'static str),
    /// `op(a, add(b, c)) == add(op(a, b), op(a, c))`, `add` the named operator.
    LeftDistributesOver(&'static str),
    /// `op(add(b, c), a) == add(op(b, a), op(c, a))`.
    RightDistributesOver(&'static str),
    /// The tonicity in each argument.
    Monotone(&'static [Tonicity]),
    /// For a unary `op`, `op(a) == op(b)` only when `a == b`.
    Injective,
    /// For a predicate, `op(a, a)`.
    Reflexive,
    /// For a predicate, `!op(a, a)`.
    Irreflexive,
    /// For a predicate, `op(a, b)` implies `op(b, a)`.
    Symmetric,
    /// For a predicate, `op(a, b)` and `op(b, a)` imply `a == b`.
    Antisymmetric,
    /// For a predicate, `op(a, b)` and `op(b, c)` imply `op(a, c)`.
    Transitive,
    /// For a predicate, `op(a, b) || op(b, a)`.
    Total,
}

/// One axiom: an operator, the carrier of its arrow, and a law.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Axiom {
    /// The operator as written (`+`, `min`), with `neg` for unary minus.
    pub op: &'static str,
    /// The carrier of the arrow.
    pub carrier: Carrier,
    /// The law.
    pub law: Law,
}

use Carrier::*;
use Law::*;
use Tonicity::*;

const fn ax(op: &'static str, carrier: Carrier, law: Law) -> Axiom {
    Axiom { op, carrier, law }
}

/// The axioms, by operator. An operator with no entry, such as `-` at `f64`, `/`, `div` or
/// `mod`, carries no law by axiom; a law it has is found or proved like any other.
pub const AXIOMS: &[Axiom] = &[
    // `+`: commutative at every arrow (sec:lexical); associative only where it is exact.
    ax("+", Int, Associative),
    ax("+", Int, Commutative),
    ax("+", Int, Identity(Const::Int(0))),
    ax("+", Int, Monotone(&[Up, Up])),
    ax("+", F64, Commutative),
    // -0.0, not 0.0, which fails at -0.0: -0.0 + 0.0 is 0.0.
    ax("+", F64, Identity(Const::F64(-0.0))),
    ax("-", Int, Monotone(&[Up, Down])),
    ax("*", Int, Associative),
    ax("*", Int, Commutative),
    ax("*", Int, Identity(Const::Int(1))),
    ax("*", Int, Zero(Const::Int(0))),
    ax("*", Int, LeftDistributesOver("+")),
    ax("*", Int, RightDistributesOver("+")),
    ax("*", F64, Commutative),
    ax("*", F64, Identity(Const::F64(1.0))),
    ax("neg", Int, Inverse("neg")),
    ax("neg", Int, Injective),
    ax("neg", Int, Monotone(&[Down])),
    ax("neg", F64, Inverse("neg")),
    ax("neg", F64, Injective),
    // `++`: associative, not commutative.
    ax("++", String, Associative),
    ax("++", String, Identity(Const::Str(""))),
    // `min` and `max` in the total order of values: no identity on an unbounded carrier.
    ax("min", Int, Associative),
    ax("min", Int, Commutative),
    ax("min", Int, Idempotent),
    ax("min", Int, Monotone(&[Up, Up])),
    ax("min", F64, Associative),
    ax("min", F64, Commutative),
    ax("min", F64, Idempotent),
    ax("max", Int, Associative),
    ax("max", Int, Commutative),
    ax("max", Int, Idempotent),
    ax("max", Int, Monotone(&[Up, Up])),
    ax("max", F64, Associative),
    ax("max", F64, Commutative),
    ax("max", F64, Idempotent),
    ax("&&", Bool, Associative),
    ax("&&", Bool, Commutative),
    ax("&&", Bool, Idempotent),
    ax("&&", Bool, Identity(Const::Bool(true))),
    ax("&&", Bool, Zero(Const::Bool(false))),
    ax("&&", Bool, LeftDistributesOver("||")),
    ax("||", Bool, Associative),
    ax("||", Bool, Commutative),
    ax("||", Bool, Idempotent),
    ax("||", Bool, Identity(Const::Bool(false))),
    ax("||", Bool, Zero(Const::Bool(true))),
    ax("||", Bool, LeftDistributesOver("&&")),
    ax("!", Bool, Inverse("!")),
    ax("!", Bool, Injective),
    ax("!", Bool, Monotone(&[Down])),
    // `==` is structural, so it is an equivalence at every carrier, floats included.
    ax("==", Int, Reflexive),
    ax("==", Int, Symmetric),
    ax("==", Int, Transitive),
    ax("==", F64, Reflexive),
    ax("==", F64, Symmetric),
    ax("==", F64, Transitive),
    ax("==", String, Reflexive),
    ax("==", String, Symmetric),
    ax("==", String, Transitive),
    ax("!=", Int, Irreflexive),
    ax("!=", Int, Symmetric),
    // The comparisons are the total order of values at every carrier.
    ax("<", Int, Irreflexive),
    ax("<", Int, Transitive),
    ax("<", F64, Irreflexive),
    ax("<", F64, Transitive),
    ax("<", String, Irreflexive),
    ax("<", String, Transitive),
    ax("<=", Int, Reflexive),
    ax("<=", Int, Antisymmetric),
    ax("<=", Int, Transitive),
    ax("<=", Int, Total),
    ax("<=", F64, Reflexive),
    ax("<=", F64, Antisymmetric),
    ax("<=", F64, Transitive),
    ax("<=", F64, Total),
    ax("<=", String, Reflexive),
    ax("<=", String, Antisymmetric),
    ax("<=", String, Transitive),
    ax("<=", String, Total),
    ax(">", Int, Irreflexive),
    ax(">", Int, Transitive),
    ax(">=", Int, Reflexive),
    ax(">=", Int, Antisymmetric),
    ax(">=", Int, Transitive),
    ax(">=", Int, Total),
];

/// The axioms of `op` at `carrier`.
pub fn of(op: &str, carrier: Carrier) -> impl Iterator<Item = &'static Law> + '_ {
    AXIOMS
        .iter()
        .filter(move |a| a.op == op && a.carrier == carrier)
        .map(|a| &a.law)
}
