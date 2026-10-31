/// Kernel values: scalars, atoms with their payloads, tuples, keypaths and families
/// (step L1.17).
///
/// Values are totally ordered by the natural order of DESIGN.md sec:keys: kinds in the order
/// atoms, `bool`, numbers, strings, tuples, keypaths, families; numbers by value across `int`,
/// `rat` and floats, an `int` before a `rat` before a float of equal value. `==` on values is
/// the ties of that order: the bitwise identity that keys and the law catalog read. The
/// language's `==` is [Value.surfaceEq], which differs only at floats.
library;

import 'dart:collection';
import 'dart:math' as math;
import 'dart:typed_data';

import 'error.dart';
import 'pmap.dart';
import 'text.dart';

part 'family.dart';
part 'num.dart';

/// A kernel value. Values are totally ordered, so any value can be a key; the order of keys is
/// the order a family's entries are visited in.
sealed class Value implements Comparable<Value> {
  const Value();

  /// The integer `n`, as an [Int] when it is in the 64-bit range.
  factory Value.integer(BigInt n) => n.isValidInt ? Int(n.toInt()) : Big(n);

  /// The failure several loose atoms make together (DESIGN.md sec:failure): the set of the
  /// distinct ones as `#errs({…})`, an `#errs` among them giving its members, and a single
  /// failure as itself.
  static Value mergeFailures(Iterable<Value> atoms) {
    final set = SplayTreeSet<Value>();
    for (final a in atoms) {
      final members = a.errs;
      if (members != null) {
        set.addAll(members.keys);
      } else {
        set.add(a);
      }
    }
    if (set.length == 1) return set.first;
    return Atom('errs', [Family.set(set)]);
  }

  /// The set of an `#errs({…})`.
  Family? get errs => switch (this) {
    Atom(name: 'errs', fields: [], args: [Family f]) => f,
    _ => null,
  };

  /// The value as a key (sec:type_resolution, "Equality and order corner rules"): `-0.0`
  /// becomes `0.0` at any depth, since `0.0 == -0.0` makes the two zeros one key, which then
  /// holds the same bits whichever zero arrived first. NaN is already one value.
  Value key() => switch (this) {
    Float(:final x) when x == 0 => Float(0.0),
    Tuple(:final items) => Tuple([for (final v in items) v.key()]),
    Path(:final keys) => Path([for (final v in keys) v.key()]),
    Atom(:final name, :final fields, :final args) when args.isNotEmpty => Atom.raw(name, fields, [
      for (final v in args) v.key(),
    ]),
    _ => this,
  };

  /// Whether the value is its own key: whether it holds no `-0.0`.
  bool get isKey => switch (this) {
    Float(:final x) => !(x == 0 && x.isNegative),
    Tuple(items: final vs) || Path(keys: final vs) => vs.every((v) => v.isKey),
    Atom(:final args) => args.every((v) => v.isKey),
    _ => true,
  };

  /// The language's order on two values of one kind: structural, except that two floats
  /// compare as IEEE 754 does, so `-0.0` and `0.0` are equal and a NaN is unordered, and
  /// tuples compare component by component in that order. Null when they are unordered.
  int? surfaceCmp(Value other) {
    switch ((this, other)) {
      case (Float(x: final a), Float(x: final b)):
        if (a.isNaN || b.isNaN) return null;
        return a < b ? -1 : (a > b ? 1 : 0);
      case (Tuple(items: final a), Tuple(items: final b)):
        for (var i = 0; i < a.length && i < b.length; i++) {
          final c = a[i].surfaceCmp(b[i]);
          if (c == null || c != 0) return c;
        }
        return a.length - b.length;
      default:
        return compareTo(other);
    }
  }

  /// The language's `==` (sec:failure, M0.11): structural, except that two floats compare as
  /// IEEE 754 does, so `NaN != NaN` and `0.0 == -0.0`, at any depth.
  bool surfaceEq(Value other) {
    bool all(List<Value> a, List<Value> b) {
      if (a.length != b.length) return false;
      for (var i = 0; i < a.length; i++) {
        if (!a[i].surfaceEq(b[i])) return false;
      }
      return true;
    }

    switch ((this, other)) {
      case (Float(x: final a), Float(x: final b)):
        return a == b;
      case (Tuple(items: final a), Tuple(items: final b)) ||
          (Path(keys: final a), Path(keys: final b)):
        return all(a, b);
      case (Atom a, Atom b):
        return a.name == b.name &&
            _lex(a.fields, b.fields, compareUtf8) == 0 &&
            all(a.args, b.args);
      case (Family a, Family b):
        if (a.length != b.length) return false;
        final x = a.entries.iterator, y = b.entries.iterator;
        while (x.moveNext() && y.moveNext()) {
          if (x.current.$1 != y.current.$1 || !x.current.$2.surfaceEq(y.current.$2)) return false;
        }
        return true;
      default:
        return this == other;
    }
  }

  /// The kind of a value, by its rank in the natural order; the numbers are one kind.
  int get kind => switch (this) {
    Atom() => 0,
    Bool() => 1,
    Int() || Big() || Rat() || Float() => 2,
    Str() => 3,
    Tuple() => 4,
    Path() => 5,
    Family() => 6,
  };

  /// The numeric kind: `int` (either width) 0, `rat` 1, float 2; null for any other value.
  int? get numberKind => switch (this) {
    Int() || Big() => 0,
    Rat() => 1,
    Float() => 2,
    _ => null,
  };

  /// The number's exact place on the extended line.
  Exact get exact => switch (this) {
    Int(:final value) => Exact.of(Rat.integer(BigInt.from(value))),
    Big(:final value) => Exact.of(Rat.integer(value)),
    Rat r => Exact.of(r),
    Float(:final x) => Exact.float(x),
    _ => throw StateError('only numbers are placed on the line'),
  };

  /// The integer inside, of either width.
  BigInt? get asBigInt => switch (this) {
    Int(:final value) => BigInt.from(value),
    Big(:final value) => value,
    _ => null,
  };

  /// The integer inside, if this is an [Int].
  int? get asInt => switch (this) {
    Int(:final value) => value,
    _ => null,
  };

  /// The family inside, if this is one.
  Family? get asFamily => switch (this) {
    Family f => f,
    _ => null,
  };

  @override
  int compareTo(Value other) {
    switch ((this, other)) {
      case (Int(value: final a), Int(value: final b)):
        return a.compareTo(b);
      case (Bool(value: final a), Bool(value: final b)):
        return a == b ? 0 : (a ? 1 : -1);
      case (Str(:final text), Str(text: final b)):
        return text.compareTo(b);
      case (Atom a, Atom b):
        final c = compareUtf8(a.name, b.name);
        if (c != 0) return c;
        final d = _lex(a.fields, b.fields, compareUtf8);
        return d != 0 ? d : _lex(a.args, b.args, _cmp);
      case (Tuple(items: final a), Tuple(items: final b)) ||
          (Path(keys: final a), Path(keys: final b)):
        return _lex(a, b, _cmp);
      case (Family a, Family b):
        final x = a.entries.iterator, y = b.entries.iterator;
        while (true) {
          final more = x.moveNext();
          if (more != y.moveNext()) return more ? 1 : -1;
          if (!more) return 0;
          final c = x.current.$1.compareTo(y.current.$1);
          if (c != 0) return c;
          final d = x.current.$2.compareTo(y.current.$2);
          if (d != 0) return d;
        }
      default:
        final k = kind, l = other.kind;
        return k == 2 && l == 2 ? _numberCmp(this, other) : k - l;
    }
  }

  /// Equal exactly when [compareTo] says so. Two families are compared by their maps, which
  /// differ at once in size and are equal at once when they are one map, so the test of a
  /// lattice `fix` for its fixpoint does not read the whole iterate when nothing changed.
  @override
  bool operator ==(Object other) {
    if (identical(this, other)) return true;
    if (other is! Value) return false;
    switch ((this, other)) {
      case (Family a, Family b):
        return a._map.sameAs(b._map);
      case (Tuple(items: final a), Tuple(items: final b)) ||
          (Path(keys: final a), Path(keys: final b)):
        if (a.length != b.length) return false;
        for (var i = 0; i < a.length; i++) {
          if (a[i] != b[i]) return false;
        }
        return true;
      default:
        return compareTo(other) == 0;
    }
  }

  @override
  int get hashCode;
}

int _cmp(Value a, Value b) => a.compareTo(b);

int _lex<T>(List<T> a, List<T> b, int Function(T, T) cmp) {
  for (var i = 0; i < a.length && i < b.length; i++) {
    final c = cmp(a[i], b[i]);
    if (c != 0) return c;
  }
  return a.length - b.length;
}

/// The total order on floats: `-0.0` before `0.0`, and NaN after everything.
int _floatCmp(double a, double b) {
  if (a.isNaN) return b.isNaN ? 0 : 1;
  if (b.isNaN) return -1;
  if (a < b) return -1;
  if (a > b) return 1;
  if (a == 0 && a.isNegative != b.isNegative) return a.isNegative ? -1 : 1;
  return 0;
}

/// Two numbers by value; equal values by kind, `int` before `rat` before a float, and two
/// floats by their total order, which puts `-0.0` before `0.0` and NaN last.
int _numberCmp(Value a, Value b) {
  switch ((a, b)) {
    case (Float(x: final x), Float(x: final y)):
      return _floatCmp(x, y);
    case (Rat x, Rat y):
      return x.compareRat(y);
    case (Big(value: final x), Big(value: final y)):
      return x.compareTo(y);
    default:
      final c = a.exact.compareTo(b.exact);
      return c != 0 ? c : a.numberKind! - b.numberKind!;
  }
}

/// `true` or `false`.
final class Bool extends Value {
  final bool value;

  const Bool(this.value);

  @override
  int get hashCode => value.hashCode;

  @override
  String toString() => '$value';
}

/// An integer in the 64-bit range.
final class Int extends Value {
  final int value;

  const Int(this.value);

  @override
  int get hashCode => value.hashCode;

  @override
  String toString() => '$value';
}

/// An integer outside the 64-bit range; never one inside it.
final class Big extends Value {
  final BigInt value;

  const Big(this.value);

  @override
  int get hashCode => value.hashCode;

  @override
  String toString() => '$value';
}

/// A float, compared bitwise after NaN canonicalization, as every kernel equation on a
/// float-bearing value does (sec:kernel, the law catalog): `-0.0` and `0.0` are different
/// values, and every NaN is the one canonical NaN.
final class Float extends Value {
  final double x;

  /// The float `x`, any NaN replaced by the canonical NaN.
  Float(double x) : x = x.isNaN ? double.nan : x;

  @override
  int get hashCode => x == 0 ? (x.isNegative ? 1 : 0) : x.hashCode;

  @override
  String toString() => showF64(x);
}

/// A string.
final class Str extends Value {
  final Text text;

  Str(String s) : text = Text(s);

  const Str.text(this.text);

  @override
  int get hashCode => text.hashCode;

  @override
  String toString() => text.quoted;
}

/// An atom such as `#empty`, `#ioError("disk full")` or `#err(code: 3)`. Failure is data
/// (sec:failure): an atom is an ordinary value that flows through the kernel like any other.
/// A payload is a tuple, by position, or a struct, by name (sec:syntax, the `#name(args)`
/// row); a struct payload keeps its fields in the code point order of their names, so the
/// written order of a construction is not part of the value.
final class Atom extends Value {
  /// The name, without the leading `#`.
  final String name;

  /// The field names of a struct payload, sorted; empty for a tuple payload.
  final List<String> fields;

  /// The payload's values, one per field of a struct payload; empty for a bare atom.
  final List<Value> args;

  const Atom.raw(this.name, this.fields, this.args);

  /// An atom with a tuple payload, such as `#ioError("disk full")`, or a bare atom such as
  /// `#empty`.
  const Atom(this.name, [this.args = const []]) : fields = const [];

  /// An atom with a struct payload, such as `#err(code: 3)`, its fields in any order; null
  /// when a name repeats.
  static Atom? named(String name, List<(String, Value)> fields) {
    final sorted = [...fields]..sort((a, b) => compareUtf8(a.$1, b.$1));
    for (var i = 1; i < sorted.length; i++) {
      if (sorted[i - 1].$1 == sorted[i].$1) return null;
    }
    return Atom.raw(name, [for (final f in sorted) f.$1], [for (final f in sorted) f.$2]);
  }

  @override
  int get hashCode => Object.hash(name, Object.hashAll(fields), Object.hashAll(args));

  @override
  String toString() {
    if (args.isEmpty) return '#$name';
    final parts = [
      for (var i = 0; i < args.length; i++)
        i < fields.length ? '${fields[i]}: ${args[i]}' : '${args[i]}',
    ];
    return '#$name(${parts.join(', ')})';
  }
}

/// A tuple, such as a composite key.
final class Tuple extends Value {
  final List<Value> items;

  const Tuple(this.items);

  @override
  int get hashCode => Object.hashAll(items);

  @override
  String toString() => '(${items.join(', ')})';
}

/// A keypath as a value: what a `reindex` key map reads and returns (sec:keypaths).
final class Path extends Value {
  final List<Value> keys;

  const Path(this.keys);

  @override
  int get hashCode => Object.hash(1, Object.hashAll(keys));

  @override
  String toString() => '[${keys.join(' -> ')}]';
}
