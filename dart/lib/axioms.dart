/// The laws each built-in operator carries by axiom (DESIGN.md sec:property_tracking, the
/// `Axiom` grade; written by step M0.11, read by the obligation record of step L3.8). The
/// prelude's copy is `zed/prelude/axioms.zed`, and the step tests keep the two equal.
///
/// An entry is per arrow: an operator at one carrier. A law that every arrow of a name must
/// have, as every `+` is commutative, is listed at each carrier the kernel has. The carriers
/// are the kernel's values: `int`, `f64`, `bool` and `String`; later layers add the arrows of
/// their own carriers (`rat`, the algebras of sec:linalg) to this table.
library;

import 'kernel.dart';

/// A carrier: the type of an arrow's operands.
enum Carrier {
  int,

  /// 64-bit floats; `==` and the comparisons are IEEE 754 on them.
  f64,
  bool,
  string,
}

/// How a function moves with one argument, in the carrier's order.
enum Tonicity {
  /// Non-decreasing.
  up,

  /// Non-increasing.
  down,
}

/// A law an arrow carries.
sealed class Law {}

/// A law with no argument.
enum Plain implements Law {
  /// `op(op(a, b), c) == op(a, op(b, c))`.
  associative,

  /// `op(a, b) == op(b, a)`.
  commutative,

  /// `op(a, a) == a`.
  idempotent,

  /// For a unary `op`, `op(a) == op(b)` only when `a == b`.
  injective,

  /// For a predicate, `op(a, a)`.
  reflexive,

  /// For a predicate, `!op(a, a)`.
  irreflexive,

  /// For a predicate, `op(a, b)` implies `op(b, a)`.
  symmetric,

  /// For a predicate, `op(a, b)` and `op(b, a)` imply `a == b`.
  antisymmetric,

  /// For a predicate, `op(a, b)` and `op(b, c)` imply `op(a, c)`.
  transitive,

  /// For a predicate, `op(a, b) || op(b, a)`.
  total,
}

/// `op(e, a) == a` and `op(a, e) == a`.
final class Identity implements Law {
  final Value e;
  const Identity(this.e);
}

/// `op(z, a) == z` and `op(a, z) == z`.
final class Zero implements Law {
  final Value z;
  const Zero(this.z);
}

/// For a unary `op`, `g(op(a)) == a` and `op(g(a)) == a`, `g` the named operator.
final class Inverse implements Law {
  final String g;
  const Inverse(this.g);
}

/// `op(a, add(b, c)) == add(op(a, b), op(a, c))`, `add` the named operator.
final class LeftDistributesOver implements Law {
  final String add;
  const LeftDistributesOver(this.add);
}

/// `op(add(b, c), a) == add(op(b, a), op(c, a))`.
final class RightDistributesOver implements Law {
  final String add;
  const RightDistributesOver(this.add);
}

/// The tonicity in each argument.
final class Monotone implements Law {
  final List<Tonicity> signs;
  const Monotone(this.signs);
}

/// One axiom: an operator as written (`+`, `min`, with `neg` for unary minus), the carrier of
/// its arrow, and a law.
typedef Axiom = ({String op, Carrier carrier, Law law});

Axiom _ax(String op, Carrier carrier, Law law) => (op: op, carrier: carrier, law: law);

const _int = Carrier.int, _f64 = Carrier.f64, _bool = Carrier.bool, _string = Carrier.string;
const _up = Tonicity.up, _down = Tonicity.down;

/// The axioms, by operator. An operator with no entry, such as `-` at `f64`, `/`, `div` or
/// `mod`, carries no law by axiom; a law it has is found or proved like any other.
final List<Axiom> axioms = List.unmodifiable([
  // `+`: commutative at every arrow (sec:lexical); associative only where it is exact.
  _ax('+', _int, Plain.associative),
  _ax('+', _int, Plain.commutative),
  _ax('+', _int, const Identity(Int(0))),
  _ax('+', _int, const Monotone([_up, _up])),
  _ax('+', _f64, Plain.commutative),
  // -0.0, not 0.0, which fails at -0.0: -0.0 + 0.0 is 0.0.
  _ax('+', _f64, Identity(Float(-0.0))),
  _ax('-', _int, const Monotone([_up, _down])),
  _ax('*', _int, Plain.associative),
  _ax('*', _int, Plain.commutative),
  _ax('*', _int, const Identity(Int(1))),
  _ax('*', _int, const Zero(Int(0))),
  _ax('*', _int, const LeftDistributesOver('+')),
  _ax('*', _int, const RightDistributesOver('+')),
  _ax('*', _f64, Plain.commutative),
  _ax('*', _f64, Identity(Float(1.0))),
  _ax('neg', _int, const Inverse('neg')),
  _ax('neg', _int, Plain.injective),
  _ax('neg', _int, const Monotone([_down])),
  _ax('neg', _f64, const Inverse('neg')),
  _ax('neg', _f64, Plain.injective),
  // `++`: associative, not commutative.
  _ax('++', _string, Plain.associative),
  _ax('++', _string, Identity(Str(''))),
  // `min` and `max` in the total order of values: no identity on an unbounded carrier.
  _ax('min', _int, Plain.associative),
  _ax('min', _int, Plain.commutative),
  _ax('min', _int, Plain.idempotent),
  _ax('min', _int, const Monotone([_up, _up])),
  _ax('min', _f64, Plain.associative),
  _ax('min', _f64, Plain.commutative),
  _ax('min', _f64, Plain.idempotent),
  _ax('max', _int, Plain.associative),
  _ax('max', _int, Plain.commutative),
  _ax('max', _int, Plain.idempotent),
  _ax('max', _int, const Monotone([_up, _up])),
  _ax('max', _f64, Plain.associative),
  _ax('max', _f64, Plain.commutative),
  _ax('max', _f64, Plain.idempotent),
  _ax('&&', _bool, Plain.associative),
  _ax('&&', _bool, Plain.commutative),
  _ax('&&', _bool, Plain.idempotent),
  _ax('&&', _bool, const Identity(Bool(true))),
  _ax('&&', _bool, const Zero(Bool(false))),
  _ax('&&', _bool, const LeftDistributesOver('||')),
  _ax('||', _bool, Plain.associative),
  _ax('||', _bool, Plain.commutative),
  _ax('||', _bool, Plain.idempotent),
  _ax('||', _bool, const Identity(Bool(false))),
  _ax('||', _bool, const Zero(Bool(true))),
  _ax('||', _bool, const LeftDistributesOver('&&')),
  _ax('!', _bool, const Inverse('!')),
  _ax('!', _bool, Plain.injective),
  _ax('!', _bool, const Monotone([_down])),
  // `==` is an equivalence at every carrier but `f64`, where it is IEEE 754 equality, which a
  // NaN makes irreflexive (step L1.17).
  _ax('==', _int, Plain.reflexive),
  _ax('==', _int, Plain.symmetric),
  _ax('==', _int, Plain.transitive),
  _ax('==', _f64, Plain.symmetric),
  _ax('==', _f64, Plain.transitive),
  _ax('==', _string, Plain.reflexive),
  _ax('==', _string, Plain.symmetric),
  _ax('==', _string, Plain.transitive),
  _ax('!=', _int, Plain.irreflexive),
  _ax('!=', _int, Plain.symmetric),
  // The comparisons are the total order of values at every carrier but `f64`, where they are
  // IEEE 754 comparisons: a strict order, and `<=` only transitive, since a NaN compares false.
  _ax('<', _int, Plain.irreflexive),
  _ax('<', _int, Plain.transitive),
  _ax('<', _f64, Plain.irreflexive),
  _ax('<', _f64, Plain.transitive),
  _ax('<', _string, Plain.irreflexive),
  _ax('<', _string, Plain.transitive),
  _ax('<=', _int, Plain.reflexive),
  _ax('<=', _int, Plain.antisymmetric),
  _ax('<=', _int, Plain.transitive),
  _ax('<=', _int, Plain.total),
  _ax('<=', _f64, Plain.transitive),
  _ax('<=', _string, Plain.reflexive),
  _ax('<=', _string, Plain.antisymmetric),
  _ax('<=', _string, Plain.transitive),
  _ax('<=', _string, Plain.total),
  _ax('>', _int, Plain.irreflexive),
  _ax('>', _int, Plain.transitive),
  _ax('>=', _int, Plain.reflexive),
  _ax('>=', _int, Plain.antisymmetric),
  _ax('>=', _int, Plain.transitive),
  _ax('>=', _int, Plain.total),
]);

/// The axioms of `op` at `carrier`.
Iterable<Law> lawsOf(String op, Carrier carrier) => [
  for (final a in axioms)
    if (a.op == op && a.carrier == carrier) a.law,
];
