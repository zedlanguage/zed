part of 'types.dart';

// Emptiness and subtyping (DESIGN.md sec:type_language): `a <: b` iff `a & !b` is empty,
// decided by a memoized coinductive check.
//
// A type is empty when every part is. The scalar and struct parts are exact, so their
// emptiness is read off. A tuple clause is empty when the meet of its positive tuple types is
// covered by its negated ones, which is decided by splitting the meet into disjoint pieces
// outside each negated type in turn, passing over a negated type disjoint from the piece. A
// morphism clause is empty when its positive types admit no morphism, or one negated type
// contains every morphism they admit, which the variance law decides: contravariant in the
// guarantee, covariant in the permission and the value type. A union of negated morphism types
// is taken one type at a time, so a clause whose positive part is covered by several negated
// types together, and by none alone, counts as inhabited: the check is sound but not complete
// there.
//
// A tuple or morphism part kept as an expression (bdd.dart) is decided by its paths, as a
// diagram is. Apart from the union of negated morphism types above, `isEmpty` is exact: no
// count of nodes, paths or splits stops it. Emptiness of Boolean combinations of tuple types is
// coNP-hard, so its time can be exponential in the tuple types written; its memory is one path
// and one split at a time.
//
// The check is coinductive: a type met again while its own emptiness is being decided is
// assumed empty. Values are finite, so a type whose every value would contain a smaller value
// of the same type is empty, which is the answer the assumption gives; contractive, regular
// and monotone definitions (rec.dart) make the set of types met finite. A result that rests on
// an assumption later found false is dropped. Results are kept for the program's run.

final _memo = <Type, bool>{};

extension Emptiness on Type {
  /// Whether no value is in `this`.
  bool get isEmpty {
    if (_memo[this] case final b?) return b;
    final s = _Search();
    final b = s.decide(this);
    _memo.addAll(s.done);
    return b;
  }

  /// Whether every value of `this` is in `other`: `this <: other`.
  bool subtype(Type other) => (this - other).isEmpty;

  /// Whether `this` and `other` denote one set of values.
  bool equiv(Type other) => subtype(other) && other.subtype(this);
}

/// One query's state: the types being decided, assumed empty, and those decided; and the
/// types decided empty, in the order they were decided.
///
/// Each check is a generator that leaves its answer in [r], and a check calls another with
/// `yield*`, which keeps the suspended checks on the heap: a type nested deeper than the call
/// stack holds is decided as any other.
final class _Search {
  final busy = <Type>{};
  final done = <Type, bool>{};
  final empties = <Type>[];

  /// The answer of the last check to end.
  var r = false;

  bool decide(Type t) {
    for (final _ in empty(t)) {}
    return r;
  }

  Iterable<void> empty(Type t) sync* {
    if (_memo[t] ?? done[t] case final b?) {
      r = b;
      return;
    }
    if (!busy.add(t)) {
      r = true;
      return;
    }
    final mark = empties.length;
    yield* parts(t);
    final b = r;
    busy.remove(t);
    if (b) {
      empties.add(t);
    } else {
      // Every emptiness decided since `t` was assumed empty may rest on that.
      for (final e in empties.sublist(mark)) {
        done.remove(e);
      }
      empties.length = mark;
    }
    done[t] = b;
    r = b;
  }

  Iterable<void> parts(Type p) sync* {
    r = false;
    if (p.bools != 0 ||
        [p.ints, p.rats, p.floats, p.strings].any((l) => l.cofinite || l.values.isNotEmpty) ||
        p.atoms.cofinite) {
      return;
    }
    for (final a in p.atoms.names.values) {
      if (a.bare) {
        r = false;
        return;
      }
      yield* empty(a.payload);
      if (!r) return;
    }
    r = false;
    if (p.structs || p.tuples.rest) return;
    for (final e in p.tuples.lens.entries) {
      yield* all(e.value.paths(), (pos, neg) => tuples(e.key, pos, neg));
      if (!r) return;
    }
    yield* all(p.morphisms.paths(), morphisms);
  }

  /// Whether `test` holds of every path of `q`.
  Iterable<void> all<A extends Literal<A>>(
    Paths<A> q,
    Iterable<void> Function(List<A> pos, List<A> neg) test,
  ) sync* {
    for (final (pos, neg) in q.asked) {
      yield* test(pos, neg);
      q.held = r;
    }
    r = q.result;
  }

  /// The tuples of length `len` in every type of `pos` and in none of `neg`.
  Iterable<void> tuples(int len, List<Components> pos, List<Components> neg) {
    final meet = List.filled(len, Type.top);
    for (final p in pos) {
      for (var i = 0; i < len; i++) {
        meet[i] = meet[i] & p.items[i];
      }
    }
    return product(meet, neg);
  }

  /// Whether the tuples with components in `p` are all in some type of `neg`. A negated type
  /// disjoint from `p` in some component is passed over. Outside a negated type means outside it
  /// first in component `j`, so the pieces are disjoint: the components before `j` inside it,
  /// component `j` outside it, and the rest as in `p`.
  Iterable<void> product(List<Type> p, List<Components> neg, [int from = 0]) sync* {
    for (final t in p) {
      yield* empty(t);
      if (r) return;
    }
    next:
    for (var i = from; i < neg.length; i++) {
      final n = neg[i].items;
      for (var j = 0; j < p.length; j++) {
        yield* empty(p[j] & n[j]);
        if (r) continue next;
      }
      for (var j = 0; j < p.length; j++) {
        yield* product(
          [for (var k = 0; k < j; k++) p[k] & n[k], p[j] - n[j], ...p.skip(j + 1)],
          neg,
          i + 1,
        );
        if (!r) return;
      }
      return;
    }
    r = false;
  }

  Iterable<void> morphisms(List<Morphism> pos, List<Morphism> neg) sync* {
    var (l, u, v) = (Type.empty, Type.top, Type.top);
    for (final p in pos) {
      (l, u, v) = (l | p.guarantee, u & p.permission, v & p.value);
    }
    // No domain lies between the bounds, or a key is promised and no value can be its.
    yield* empty(l - u);
    if (!r) {
      r = true;
      return;
    }
    yield* empty(l);
    if (!r) {
      yield* empty(v);
      if (r) return;
    }
    // With no value, the empty morphism is the only one, and its domain is the guarantee.
    yield* empty(v);
    final noValue = r;
    for (final n in neg) {
      yield* empty(n.guarantee - l);
      if (!r) continue;
      if (!noValue) {
        yield* empty(u - n.permission);
        if (!r) continue;
        yield* empty(u);
        if (!r) {
          yield* empty(v - n.value);
          if (!r) continue;
        }
      }
      r = true;
      return;
    }
    r = false;
  }
}
