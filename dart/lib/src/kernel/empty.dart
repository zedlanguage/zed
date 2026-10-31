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
// of the same type is empty, which is the answer the assumption gives. A result that rests on
// an assumption later found false is dropped. Results are kept for the program's run.

final _memo = <Type, bool>{};

extension Emptiness on Type {
  /// Whether no value is in `this`.
  bool get isEmpty {
    if (_memo[this] case final b?) return b;
    final s = _Search();
    final b = s.empty(this);
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
final class _Search {
  final busy = <Type>{};
  final done = <Type, bool>{};
  final empties = <Type>[];

  bool empty(Type t) {
    if (_memo[t] ?? done[t] case final b?) return b;
    if (!busy.add(t)) return true;
    final mark = empties.length;
    final b = parts(t);
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
    return b;
  }

  bool parts(Type p) =>
      p.bools == 0 &&
      [p.ints, p.rats, p.floats, p.strings].every((l) => !l.cofinite && l.values.isEmpty) &&
      !p.atoms.cofinite &&
      p.atoms.names.values.every((a) => !a.bare && empty(a.payload)) &&
      !p.structs &&
      !p.tuples.rest &&
      p.tuples.lens.entries.every((e) => e.value.paths((pos, neg) => tuples(e.key, pos, neg))) &&
      p.morphisms.paths(morphisms);

  /// The tuples of length `len` in every type of `pos` and in none of `neg`.
  bool tuples(int len, List<Components> pos, List<Components> neg) {
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
  bool product(List<Type> p, List<Components> neg, [int from = 0]) {
    if (p.any(empty)) return true;
    for (var i = from; i < neg.length; i++) {
      final n = neg[i].items;
      if (Iterable<int>.generate(p.length).any((j) => empty(p[j] & n[j]))) continue;
      return Iterable<int>.generate(p.length).every(
        (j) => product(
          [for (var k = 0; k < j; k++) p[k] & n[k], p[j] - n[j], ...p.skip(j + 1)],
          neg,
          i + 1,
        ),
      );
    }
    return false;
  }

  bool morphisms(List<Morphism> pos, List<Morphism> neg) {
    var (l, u, v) = (Type.empty, Type.top, Type.top);
    for (final p in pos) {
      (l, u, v) = (l | p.guarantee, u & p.permission, v & p.value);
    }
    // No domain lies between the bounds, or a key is promised and no value can be its.
    if (!empty(l - u) || (!empty(l) && empty(v))) return true;
    // With no value, the empty morphism is the only one, and its domain is the guarantee.
    final noValue = empty(v);
    return neg.any(
      (n) =>
          empty(n.guarantee - l) &&
          (noValue || empty(u - n.permission)) &&
          (noValue || empty(u) || empty(v - n.value)),
    );
  }
}
