/// Step L1.23: emptiness and subtyping against an exact oracle. The random types are Boolean
/// combinations of scalar leaves, universes, and tuples of length 1 and 2 whose components are
/// Boolean combinations of scalar leaves and universes. Every such type is a union of regions,
/// and `reps` holds one value of each region, so a type is empty exactly when no value of
/// `reps` is in it, and `a <: b` exactly when every value of `reps` in `a` is in `b`.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/instances.dart';

sealed class E {}

final class Base extends E {
  final String name;
  Base(this.name);
  @override
  String toString() => name;
}

final class LitE extends E {
  final Value v;
  LitE(this.v);
  @override
  String toString() => '$v';
}

final class AtomE extends E {
  final String name;
  AtomE(this.name);
  @override
  String toString() => '#$name';
}

final class Univ extends E {
  final Universe u;
  Univ(this.u);
  @override
  String toString() => u.name;
}

final class TupleE extends E {
  final List<E> items;
  TupleE(this.items);
  @override
  String toString() => '(${items.join(', ')})';
}

enum Op { or, and, diff, not }

final class Conn extends E {
  final Op op;
  final E a;
  final E? b;
  Conn(this.op, this.a, [this.b]);
  @override
  String toString() => '${op.name}($a${b == null ? '' : ', $b'})';
}

/// A scalar or morphism value, a tuple of representatives, or the struct, which has no value
/// until L2.
sealed class Rep {}

final class RepValue extends Rep {
  final Value v;
  RepValue(this.v);
}

final class RepTuple extends Rep {
  final List<Rep> items;
  RepTuple(this.items);
}

final class RepStruct extends Rep {}

bool holds(E e, Rep r) => switch ((e, r)) {
  (Conn(op: Op.or, :final a, :final b), _) => holds(a, r) || holds(b!, r),
  (Conn(op: Op.and, :final a, :final b), _) => holds(a, r) && holds(b!, r),
  (Conn(op: Op.diff, :final a, :final b), _) => holds(a, r) && !holds(b!, r),
  (Conn(op: Op.not, :final a), _) => !holds(a, r),
  (Univ(:final u), RepTuple()) => u == Universe.tuple,
  (TupleE(:final items), RepTuple(items: final xs)) =>
    items.length == xs.length &&
        [for (var i = 0; i < xs.length; i++) i].every((i) => holds(items[i], xs[i])),
  (Univ(:final u), RepStruct()) => u == Universe.struct,
  (_, RepTuple() || RepStruct()) => false,
  (Base(:final name), RepValue(:final v)) => switch ((name, v)) {
    ('int', Int()) || ('bool', Bool()) || ('String', Str()) => true,
    _ => false,
  },
  (LitE(v: final l), RepValue(:final v)) => l == v,
  (AtomE(:final name), RepValue(:final v)) => v is Atom && v.name == name,
  (Univ(:final u), RepValue(:final v)) => Universe.of(v) == u,
  (TupleE(), _) => false,
};

Type build(E e) => switch (e) {
  Base(name: 'int') => Type.integer,
  Base(name: 'bool') => Type.boolean,
  Base() => Type.string,
  LitE(:final v) => Type.lit(v)!,
  AtomE(:final name) => Type.atom(name),
  Univ(:final u) => Type.universe(u),
  TupleE(:final items) => Type.tuple(items.map(build).toList()),
  Conn(op: Op.or, :final a, :final b) => build(a) | build(b!),
  Conn(op: Op.and, :final a, :final b) => build(a) & build(b!),
  Conn(op: Op.diff, :final a, :final b) => build(a) - build(b!),
  Conn(op: Op.not, :final a) => ~build(a),
};

List<Value> lits() => [const Int(0), const Int(1), Str('a')];

/// One value of each region a component can tell apart: each literal, another integer and
/// string, a boolean, each named atom and another, another scalar, a tuple, a morphism and
/// the struct.
List<Rep> componentReps() => [
  for (final v in [
    ...lits(),
    const Int(2),
    Str('b'),
    const Bool(true),
    const Atom('a'),
    const Atom('b'),
    const Atom('c'),
    Float(0.5),
    const Family.empty(),
  ])
    RepValue(v),
  RepTuple([]),
  RepStruct(),
];

/// The component regions, and the tuples of length 1 and 2 over them; the empty tuple stands
/// for every other length.
List<Rep> reps() {
  final comps = componentReps();
  return [
    ...comps,
    for (final a in comps) ...[
      RepTuple([a]),
      for (final b in comps) RepTuple([a, b]),
    ],
  ];
}

E leaf(Rng r) => switch (r.below(4)) {
  0 => Base(r.pick(['int', 'bool', 'String'])),
  1 => LitE(r.pick(lits())),
  2 => AtomE(r.pick(['a', 'b'])),
  _ => Univ(r.pick([Universe.scalar, Universe.tuple, Universe.struct, Universe.morphism])),
};

/// A Boolean combination of depth at most `depth`, over `leaf`.
E boolean(Rng r, int depth, E Function(Rng) leaf) {
  if (depth == 0 || r.below(3) == 0) return leaf(r);
  final op = r.below(4);
  final a = boolean(r, depth - 1, leaf);
  final b = boolean(r, depth - 1, leaf);
  return switch (op) {
    0 => Conn(Op.or, a, b),
    1 => Conn(Op.and, a, b),
    2 => Conn(Op.diff, a, b),
    _ => Conn(Op.not, a),
  };
}

E random(Rng r) => boolean(r, 3, (r) {
  final n = r.below(3);
  if (n == 0) return leaf(r);
  return TupleE([for (var i = 0; i < n; i++) boolean(r, 2, leaf)]);
});

/// A deeper combination, mostly of tuples, whose tuple part has diagrams of many nodes.
E deep(Rng r) => boolean(r, 6, (r) {
  final n = r.below(4);
  if (n == 0) return leaf(r);
  return TupleE([for (var i = 0; i < (n < 2 ? n : 2); i++) leaf(r)]);
});

void main() {
  test('emptiness agrees with the oracle', () {
    final rs = reps();
    final r = Rng(23);
    var (empty, inhabited) = (0, 0);
    for (var i = 0; i < 1500; i++) {
      final e = random(r);
      final want = !rs.any((v) => holds(e, v));
      final t = build(e);
      if (t.isEmpty != want) fail('$t, from $e: expected empty $want');
      // The tuple part on its own, where the product split decides.
      final tuples = t.part(Universe.tuple);
      final wantTuples = !rs.any((v) => v is RepTuple && holds(e, v));
      if (tuples.isEmpty != wantTuples) fail('$tuples, from $e: expected empty $wantTuples');
      wantTuples ? empty++ : inhabited++;
    }
    // Both answers occur often, so neither "always empty" nor "never empty" would pass.
    expect(empty > 200 && inhabited > 200, isTrue, reason: '$empty $inhabited');
  });

  test('subtyping agrees with the oracle', () {
    final rs = reps();
    final r = Rng(5);
    var (yes, no) = (0, 0);
    for (var i = 0; i < 1500; i++) {
      var (a, b) = (random(r), random(r));
      // Half the pairs compare a type with a part of itself, so that subtyping holds often.
      if (r.below(2) == 0) a = Conn(Op.and, a, b);
      final want = rs.every((v) => !holds(a, v) || holds(b, v));
      final (ta, tb) = (build(a), build(b));
      if (ta.subtype(tb) != want) fail('$ta <: $tb: expected $want');
      want ? yes++ : no++;
    }
    expect(yes > 400 && no > 400, isTrue, reason: '$yes $no');
  });

  test('deep combinations are decided exactly', () {
    // Deep combinations of tuple types make parts kept as expressions (a union or
    // intersection whose diagram would outgrow its operands); `isEmpty` and subtyping agree
    // with the oracle on every one, with no budget to miss an empty type.
    final rs = reps();
    final r = Rng(23);
    var (empty, inhabited) = (0, 0);
    for (var i = 0; i < 3000; i++) {
      final e = deep(r);
      final t = build(e);
      final tuples = t.part(Universe.tuple);
      for (final (t, tupleOnly) in [(t, false), (tuples, true)]) {
        final want = !rs.any((v) => (!tupleOnly || v is RepTuple) && holds(e, v));
        if (t.isEmpty != want) fail('$t, from $e: expected empty $want');
        want ? empty++ : inhabited++;
      }
      final a = Conn(Op.and, deep(r), e);
      final want = rs.every((v) => !holds(a, v) || holds(e, v));
      if (build(a).subtype(t) != want) fail('$a <: $e: expected $want');
    }
    expect(empty > 300 && inhabited > 300, isTrue, reason: '$empty $inhabited');
  });
}
