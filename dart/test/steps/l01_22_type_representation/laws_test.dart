/// Step L1.22: the connectives against a direct reading of the type expression: for random
/// expressions over the base types, literals, atoms, tuples and universes, a value is in the
/// type the connectives build exactly when the expression, read as a predicate, holds of it.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/instances.dart';

/// A type expression.
sealed class E {}

final class Base extends E {
  final String name;
  Base(this.name);
}

final class LitE extends E {
  final Value v;
  LitE(this.v);
}

final class AtomE extends E {
  final String name;
  AtomE(this.name);
}

final class AtomWith extends E {
  final String name;
  final E payload;
  AtomWith(this.name, this.payload);
}

final class TupleE extends E {
  final List<E> items;
  TupleE(this.items);
}

final class Univ extends E {
  final Universe u;
  Univ(this.u);
}

enum Op { or, and, diff, not }

final class Conn extends E {
  final Op op;
  final E a;
  final E? b;
  Conn(this.op, this.a, [this.b]);
}

/// Whether `e` holds of `v`; a null `v` is the struct an atom's struct payload is (no struct
/// value exists until L2).
bool holds(E e, Value? v) => switch (e) {
  Conn(op: Op.or, :final a, :final b) => holds(a, v) || holds(b!, v),
  Conn(op: Op.and, :final a, :final b) => holds(a, v) && holds(b!, v),
  Conn(op: Op.diff, :final a, :final b) => holds(a, v) && !holds(b!, v),
  Conn(op: Op.not, :final a) => !holds(a, v),
  Univ(:final u) when v == null => u == Universe.struct,
  _ when v == null => false,
  Base(:final name) => switch ((name, v)) {
    ('int', Int() || Big()) || ('rat', Rat()) || ('f64', Float()) || ('bool', Bool()) => true,
    ('String', Str()) => true,
    _ => false,
  },
  LitE(v: final l) => l == v,
  AtomE(:final name) => v is Atom && v.name == name && v.args.isEmpty,
  AtomWith(:final name, :final payload) => switch (v) {
    Atom(name: final n, :final fields, :final args) when n == name && args.isNotEmpty => holds(
      payload,
      fields.isEmpty ? Tuple(args) : null,
    ),
    _ => false,
  },
  TupleE(:final items) => switch (v) {
    Tuple(items: final xs) || Path(keys: final xs) =>
      items.length == xs.length &&
          [for (var i = 0; i < xs.length; i++) i].every((i) => holds(items[i], xs[i])),
    _ => false,
  },
  Univ(:final u) => Universe.of(v) == u,
};

Type build(E e) => switch (e) {
  Base(name: 'int') => Type.integer,
  Base(name: 'rat') => Type.rational,
  Base(name: 'f64') => Type.f64,
  Base(name: 'bool') => Type.boolean,
  Base() => Type.string,
  LitE(:final v) => Type.lit(v)!,
  AtomE(:final name) => Type.atom(name),
  AtomWith(:final name, :final payload) => Type.atomWith(name, build(payload)),
  TupleE(:final items) => Type.tuple(items.map(build).toList()),
  Univ(:final u) => Type.universe(u),
  Conn(op: Op.or, :final a, :final b) => build(a) | build(b!),
  Conn(op: Op.and, :final a, :final b) => build(a) & build(b!),
  Conn(op: Op.diff, :final a, :final b) => build(a) - build(b!),
  Conn(op: Op.not, :final a) => ~build(a),
};

List<Value> small() => [const Int(0), const Int(1), Str('a'), const Atom('a'), const Bool(true)];

/// Values of every universe: scalars of each base type, bare atoms and atoms with tuple and
/// struct payloads, tuples of length 0 to 2, a keypath and a family.
List<Value> values() => [
  const Int(2),
  Big(BigInt.parse('1208925819614629174706176')),
  Rat.decimal('0.5')!,
  Float(0.5),
  Float(-1.0),
  const Bool(false),
  Str('b'),
  const Atom('b'),
  const Atom('c'),
  const Atom('a', [Int(1)]),
  Atom('a', [const Int(1), Str('a')]),
  const Atom('b', [Int(0)]),
  Atom.named('a', [('x', const Int(1))])!,
  const Path([Int(0), Int(1)]),
  const Family.empty(),
  const Tuple([]),
  const Tuple([
    Tuple([Int(0)]),
  ]),
  ...small(),
  for (final a in small()) ...[
    Tuple([a]),
    for (final b in small()) Tuple([a, b]),
  ],
];

E random(Rng r, int depth) {
  if (depth == 0 || r.below(3) == 0) {
    return switch (r.below(6)) {
      0 => Base(r.pick(['int', 'rat', 'f64', 'bool', 'String'])),
      1 => LitE(r.pick(small())),
      2 => AtomE(r.pick(['a', 'b', 'c'])),
      3 => Univ(r.pick(Universe.values)),
      4 => TupleE([for (var i = r.below(3); i > 0; i--) random(r, 0)]),
      _ => AtomWith(r.pick(['a', 'b']), random(r, 0)),
    };
  }
  E sub() => random(r, depth - 1);
  return switch (r.below(6)) {
    0 => Conn(Op.or, sub(), sub()),
    1 => Conn(Op.and, sub(), sub()),
    2 => Conn(Op.diff, sub(), sub()),
    3 => Conn(Op.not, sub()),
    4 => TupleE([sub(), sub()]),
    _ => AtomWith('a', sub()),
  };
}

void main() {
  test('membership is the expression read as a predicate', () {
    final vs = values();
    final r = Rng(22);
    var (members, nonmembers) = (0, 0);
    for (var i = 0; i < 1500; i++) {
      final e = random(r, 3);
      final t = build(e);
      expect(t.decidable, isTrue);
      for (final v in vs) {
        final want = holds(e, v);
        if (t.contains(v) != want) fail('$v in $t: expected $want');
        want ? members++ : nonmembers++;
      }
    }
    // Both answers occur often, so neither a type that holds everything nor one that holds
    // nothing would pass.
    expect(members > 10000 && nonmembers > 10000, isTrue, reason: '$members $nonmembers');
  });

  test('union and intersection are commutative, idempotent and canonical', () {
    final r = Rng(7);
    for (var i = 0; i < 500; i++) {
      final (a, b) = (build(random(r, 2)), build(random(r, 2)));
      expect(a | b, b | a, reason: '$a | $b');
      expect(a & b, b & a, reason: '$a & $b');
      expect(a | a, a);
      expect(a & a, a);
      expect('${a | b}', '${b | a}');
    }
  });

  test('a type and its complement split every universe', () {
    final r = Rng(11);
    final vs = values();
    for (var i = 0; i < 300; i++) {
      final a = build(random(r, 3));
      final (both, either) = (a & ~a, a | ~a);
      for (final v in vs) {
        if (both.contains(v)) fail('$v in $both');
        if (!either.contains(v)) fail('$v not in $either');
      }
      expect(either.functions && !both.functions, isTrue, reason: '$a');
    }
  });

  test('the scalar part is exact', () {
    // Within the scalars the representation is a normal form: two expressions that hold of
    // the same scalars build one type, so `a | !a` is every scalar exactly.
    final r = Rng(3);
    final scalars = Type.universe(Universe.scalar);
    for (var i = 0; i < 500; i++) {
      final a = build(random(r, 3)).part(Universe.scalar);
      expect(a | (scalars - a), scalars, reason: '$a');
      expect((~~a).part(Universe.scalar), a);
    }
  });
}
