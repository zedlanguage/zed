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
    /// 64-bit floats; `==` and the comparisons are IEEE 754 on them (IEEE Std 754-2019,
    /// doi:10.1109/IEEESTD.2019.8766229, section 5.11; the full comment is in zed-kernel
    /// `value.rs`, `Value::surface_cmp`).
    F64,
    /// Booleans.
    Bool,
    /// Strings.
    String,
}

/// A constant an axiom names, of the arrow's carrier. Two constants are equal as the kernel's
/// values are, a float by its bits: `-0.0` is not `0.0`, and the NaN is equal to itself, so
/// `Zero(Const::F64(f64::NAN))` is found in the table.
#[derive(Clone, Copy, Debug)]
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

impl PartialEq for Const {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Const::Int(a), Const::Int(b)) => a == b,
            (Const::F64(a), Const::F64(b)) => a.to_bits() == b.to_bits(),
            (Const::Bool(a), Const::Bool(b)) => a == b,
            (Const::Str(a), Const::Str(b)) => a == b,
            _ => false,
        }
    }
}

/// How a function moves with one argument, the others fixed, in the carrier's order: the
/// grades of the property record's `monotone(per-arg ↑s/↑/const/↓/↓s)` (DESIGN.md
/// sec:property_tracking). For `a < b`, ↑s says `f(a) < f(b)`, ↑ `f(a) <= f(b)`, `const`
/// `f(a) == f(b)`, and ↓ and ↓s the reverse. A function with none of these has no grade, which
/// the readers write as `Option<Tonicity>`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Tonicity {
    /// Strictly increasing, ↑s.
    StrictUp,
    /// Non-decreasing, ↑.
    Up,
    /// Constant.
    Const,
    /// Non-increasing, ↓.
    Down,
    /// Strictly decreasing, ↓s.
    StrictDown,
}

impl Tonicity {
    /// The grade of `-f` for `f` of this grade: swapping the direction, as a negation or a
    /// factor below 0 does.
    pub fn flip(self) -> Tonicity {
        match self {
            Tonicity::StrictUp => Tonicity::StrictDown,
            Tonicity::Up => Tonicity::Down,
            Tonicity::Const => Tonicity::Const,
            Tonicity::Down => Tonicity::Up,
            Tonicity::StrictDown => Tonicity::StrictUp,
        }
    }

    /// The grade without its strictness: ↑s is ↑ and ↓s is ↓.
    pub fn weak(self) -> Tonicity {
        match self {
            Tonicity::StrictUp => Tonicity::Up,
            Tonicity::StrictDown => Tonicity::Down,
            t => t,
        }
    }

    /// Whether the grade is ↑s or ↓s.
    pub fn is_strict(self) -> bool {
        matches!(self, Tonicity::StrictUp | Tonicity::StrictDown)
    }

    /// The direction: 1 for ↑s and ↑, -1 for ↓ and ↓s, 0 for `const`.
    pub fn sign(self) -> i8 {
        match self {
            Tonicity::StrictUp | Tonicity::Up => 1,
            Tonicity::Const => 0,
            Tonicity::Down | Tonicity::StrictDown => -1,
        }
    }

    /// The grade of `g ∘ f`, `f` of this grade and `g` of grade `outer`: the directions
    /// multiply, `const` on either side is `const`, and the composite is strict only when both
    /// stages are (`↑s ∘ ↓s` is ↓s, `↑s ∘ ↑` is ↑). Proof: for `a < b`, `f` moves `f(a)` to
    /// `f(b)` in its direction (or not at all, under `const`), and `g` carries that order on in
    /// its own; `<` survives both stages only when each is strict.
    pub fn then(self, outer: Tonicity) -> Tonicity {
        let strict = self.is_strict() && outer.is_strict();
        match self.sign() * outer.sign() {
            0 => Tonicity::Const,
            1 if strict => Tonicity::StrictUp,
            1 => Tonicity::Up,
            _ if strict => Tonicity::StrictDown,
            _ => Tonicity::Down,
        }
    }

    /// The grade of `f + g`, `f` of this grade and `g` of grade `other`, on `int` or `rat`: a
    /// `const` term keeps the other's grade; two terms of one direction keep it, strict when
    /// either is, since `f(a) <= f(b)` and `g(a) < g(b)` give `f(a) + g(a) < f(b) + g(b)`; two
    /// of opposite directions have no grade (`x + (-x)` is constant, `x + (-2 * x)` falls).
    pub fn plus(self, other: Tonicity) -> Option<Tonicity> {
        match (self.sign(), other.sign()) {
            (0, _) => Some(other),
            (_, 0) => Some(self),
            (s, o) if s == o => Some(if self.is_strict() || other.is_strict() {
                self.strict()
            } else {
                self
            }),
            _ => None,
        }
    }

    /// The strict grade of this one's direction; `const` stays `const`.
    pub fn strict(self) -> Tonicity {
        match self.sign() {
            1 => Tonicity::StrictUp,
            -1 => Tonicity::StrictDown,
            _ => Tonicity::Const,
        }
    }
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
    /// `op(a, b) == a` or `op(a, b) == b`: the result is one of the operands.
    Selective,
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
    /// For a predicate, `op(a, b)` implies `other(a, b)`, `other` the named predicate.
    Implies(&'static str),
    /// For a predicate, `op(a, b)` and `next(b, c)` imply `result(a, c)`, written
    /// `Composes(next, result)`: one composition of an order chain (sec:verification).
    Composes(&'static str, &'static str),
    /// `op(a, a) == e`: every value is its own inverse, `e` the identity.
    SelfInverse(Const),
    /// For an `op(x, k)` with `k >= 0`, `op(x, k) == g(x, 2 ^ k)`, `g` the named operator: a
    /// shift is a product or a quotient by a power of two.
    PowerOfTwo(&'static str),
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
    ax("+", Int, Monotone(&[StrictUp, StrictUp])),
    ax("+", F64, Commutative),
    // -0.0, not 0.0, which fails at -0.0: -0.0 + 0.0 is 0.0.
    ax("+", F64, Identity(Const::F64(-0.0))),
    ax("-", Int, Monotone(&[StrictUp, StrictDown])),
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
    ax("neg", Int, Monotone(&[StrictDown])),
    ax("neg", F64, Inverse("neg")),
    ax("neg", F64, Injective),
    // `++`: associative, not commutative.
    ax("++", String, Associative),
    ax("++", String, Identity(Const::Str(""))),
    // `min` and `max`: at `int` in its order, with no identity on an unbounded carrier; at `f64`
    // IEEE 754-2019 `minimum` and `maximum` (sec:reduction, item 5), where a NaN in either
    // position gives the NaN and `-0.0` is below `0.0`. The NaN is the canonical one, so the
    // result is an operand bit for bit and selectivity holds with a NaN too; the infinities are
    // identities and the NaN a zero. No `Monotone` at `f64`: a NaN is in no order. Citation:
    // IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 9.6, "Minimum and maximum
    // operations"; the full comment is in zed-kernel `value.rs`, fn `ieee_min_max`.
    ax("min", Int, Associative),
    ax("min", Int, Commutative),
    ax("min", Int, Idempotent),
    ax("min", Int, Selective),
    ax("min", Int, Monotone(&[Up, Up])),
    ax("min", F64, Associative),
    ax("min", F64, Commutative),
    ax("min", F64, Idempotent),
    ax("min", F64, Selective),
    ax("min", F64, Identity(Const::F64(f64::INFINITY))),
    ax("min", F64, Zero(Const::F64(f64::NAN))),
    ax("max", Int, Associative),
    ax("max", Int, Commutative),
    ax("max", Int, Idempotent),
    ax("max", Int, Selective),
    ax("max", Int, Monotone(&[Up, Up])),
    ax("max", F64, Associative),
    ax("max", F64, Commutative),
    ax("max", F64, Idempotent),
    ax("max", F64, Selective),
    ax("max", F64, Identity(Const::F64(f64::NEG_INFINITY))),
    ax("max", F64, Zero(Const::F64(f64::NAN))),
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
    // `==` is an equivalence at every carrier but `f64`, where it is IEEE 754 equality, which a
    // NaN makes irreflexive (step L1.17). Citation: IEEE Std 754-2019,
    // doi:10.1109/IEEESTD.2019.8766229, section 5.11, "Details of comparison predicates"; the
    // full comment is in zed-kernel `value.rs`, `Value::surface_cmp`.
    ax("==", Int, Reflexive),
    ax("==", Int, Symmetric),
    ax("==", Int, Transitive),
    ax("==", F64, Symmetric),
    ax("==", F64, Transitive),
    ax("==", Bool, Reflexive),
    ax("==", Bool, Symmetric),
    ax("==", Bool, Transitive),
    ax("==", String, Reflexive),
    ax("==", String, Symmetric),
    ax("==", String, Transitive),
    ax("!=", Int, Irreflexive),
    ax("!=", Int, Symmetric),
    // `!=` at `f64` is only symmetric: `NaN != NaN` is true, so it is not irreflexive.
    ax("!=", F64, Symmetric),
    ax("!=", Bool, Irreflexive),
    ax("!=", Bool, Symmetric),
    ax("!=", String, Irreflexive),
    ax("!=", String, Symmetric),
    // The comparisons are the total order of values at every carrier but `f64`, where they are
    // IEEE 754 comparisons: a strict order, and `<=` only transitive, since a NaN compares false
    // (IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 5.11; the full comment is in
    // zed-kernel `value.rs`, `Value::surface_cmp`).
    // Strings compare by code point, which is the byte order of their UTF-8 (sec:order).
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
    ax("<=", F64, Transitive),
    ax("<=", String, Reflexive),
    ax("<=", String, Antisymmetric),
    ax("<=", String, Transitive),
    ax("<=", String, Total),
    ax(">", Int, Irreflexive),
    ax(">", Int, Transitive),
    ax(">", F64, Irreflexive),
    ax(">", F64, Transitive),
    ax(">", String, Irreflexive),
    ax(">", String, Transitive),
    ax(">=", Int, Reflexive),
    ax(">=", Int, Antisymmetric),
    ax(">=", Int, Transitive),
    ax(">=", Int, Total),
    ax(">=", F64, Transitive),
    ax(">=", String, Reflexive),
    ax(">=", String, Antisymmetric),
    ax(">=", String, Transitive),
    ax(">=", String, Total),
    // How `<` and `<=`, and `>` and `>=`, relate, which the compositions of an order chain read
    // (sec:verification). At `int` and `String` they are facts of a total order. They hold at
    // `f64` too: a comparison with a NaN is false, so when the premises hold no operand is a
    // NaN, and on the other floats the comparisons are an order in which `-0.0` and `0.0` are
    // one point.
    ax("<", Int, Implies("<=")),
    ax("<", Int, Composes("<=", "<")),
    ax("<=", Int, Composes("<", "<")),
    ax("<", F64, Implies("<=")),
    ax("<", F64, Composes("<=", "<")),
    ax("<=", F64, Composes("<", "<")),
    ax("<", String, Implies("<=")),
    ax("<", String, Composes("<=", "<")),
    ax("<=", String, Composes("<", "<")),
    ax(">", Int, Implies(">=")),
    ax(">", Int, Composes(">=", ">")),
    ax(">=", Int, Composes(">", ">")),
    ax(">", F64, Implies(">=")),
    ax(">", F64, Composes(">=", ">")),
    ax(">=", F64, Composes(">", ">")),
    ax(">", String, Implies(">=")),
    ax(">", String, Composes(">=", ">")),
    ax(">=", String, Composes(">", ">")),
    // The bit words of step L1.39a, on their domain `int[0..]`. None takes a width, so no law
    // wraps: `shl(x, k)` is the exact `x * 2 ^ k` for every int `x`, `shl(1, 64)` is `2 ^ 64`,
    // and `shr(x, k)` is the Euclidean `x div 2 ^ k`, which rounds toward negative infinity.
    // `bitOr` has identity 0 and `bitAnd` zero 0 on `int[0..]`. Their other constant, -1 (the
    // identity of `bitAnd` and the zero of `bitOr`, DESIGN M0.11), is outside that domain until
    // step L1.39d (plan row INT-twos) reads negative ints by two's complement.
    ax("bitAnd", Int, Associative),
    ax("bitAnd", Int, Commutative),
    ax("bitAnd", Int, Idempotent),
    ax("bitAnd", Int, Zero(Const::Int(0))),
    ax("bitOr", Int, Associative),
    ax("bitOr", Int, Commutative),
    ax("bitOr", Int, Idempotent),
    ax("bitOr", Int, Identity(Const::Int(0))),
    ax("bitXor", Int, Associative),
    ax("bitXor", Int, Commutative),
    ax("bitXor", Int, Identity(Const::Int(0))),
    ax("bitXor", Int, SelfInverse(Const::Int(0))),
    ax("shl", Int, PowerOfTwo("*")),
    ax("shr", Int, PowerOfTwo("div")),
];

/// The axioms of `op` at `carrier`.
pub fn of(op: &str, carrier: Carrier) -> impl Iterator<Item = &'static Law> + '_ {
    AXIOMS
        .iter()
        .filter(move |a| a.op == op && a.carrier == carrier)
        .map(|a| &a.law)
}
