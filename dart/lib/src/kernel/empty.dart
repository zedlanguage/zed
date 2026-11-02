part of 'types.dart';

// Emptiness and subtyping (DESIGN.md sec:type_language): `a <: b` iff `a & !b` is empty,
// decided by a memoized coinductive check.
//
// A type is empty when every part is. The scalar and struct parts are exact, so their
// emptiness is read off. The tuple part of each length, a Boolean combination of tuple types
// (bdd.dart), is decided on a box, one type per component, starting from the whole product:
// each tuple type is known to hold the box, known to miss it, or open on it; the part is
// evaluated in three-valued logic on what is known; a tuple type in every value of the part
// narrows the box to it, and one in no value takes itself out of the one component where it
// does not hold the box. When narrowing stops, a component whose pieces cut by the open tuple
// types are pairwise equal or disjoint is split into those pieces, and each piece decided;
// otherwise each piece on which narrowing alone proves the part empty is taken out of the box;
// otherwise, once on each branch, when the part holds nothing outside the open tuple types,
// the box is split into its meet with each of them. A box none of these steps settles counts
// as inhabited. The morphism part is decided the same way, by the variance law: contravariant
// in the guarantee, covariant in the permission and the value type. A morphism type admits no
// morphism only when a key it promises is shown to exist, by a value found in the key type.
//
// So `isEmpty` is sound, never true of an inhabited type, and its time is polynomial in the
// types written; it is not complete, since emptiness of Boolean combinations of tuple types is
// coNP-hard. A part that only a split of the box in more than one component at once proves
// empty counts as inhabited: a subtyping check then fails, and the error names the types, so
// the program states the case split itself (DESIGN.md L1.23).
//
// The check is coinductive: a type met again while its own emptiness is being decided is
// assumed empty. Values are finite, so a type whose every value would contain a smaller value
// of the same type is empty, which is the answer the assumption gives; contractive, regular
// and monotone definitions (rec.dart) make the set of types met finite. A result, empty or
// inhabited, that rests on an assumption later found false is dropped, and only such a
// result, so no result is decided again unless an assumption it read changed: a tuple type
// wrongly assumed disjoint from the box leaves a clause, so a wrong assumption can make a type
// count as inhabited too. Results are kept until [Emptiness.forget].

final _memo = <Type, bool>{};

extension Emptiness on Type {
  /// Drops the kept results. A unit's checker calls it first: a type equal to a kept one but
  /// built apart from it is compared with it in full, so a result kept from another unit
  /// costs the size of the type at each lookup.
  static void forget() => _memo.clear();

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

/// One query's state: the types being decided, assumed empty, each with its depth among them;
/// those decided; the types decided on assumptions still being made, in the order they were
/// decided, each with the depths of those assumptions; the depths of the assumptions the
/// current decision has used; the representative found for each type, and whether each
/// representative is in each type it was tested against.
///
/// Each check is a generator that leaves its answer in [r], or a representative in [found],
/// and a check calls another with `yield*`, which keeps the suspended checks on the heap: a
/// type nested deeper than the call stack holds is decided as any other.
final class _Search {
  final busy = <Type, int>{};
  final done = <Type, bool>{};
  final pending = <Type>[];
  final rests = <Type, Set<int>>{};
  var reads = <int>{};
  final reps = <Type, _Rep?>{};
  final members = <(Type, Type), bool>{};

  /// The answer of the last check to end.
  var r = false;

  /// The representative the last search for one found.
  _Rep? found;

  bool decide(Type t) {
    for (final _ in empty(t)) {}
    return r;
  }

  Iterable<void> empty(Type t) sync* {
    if (_memo[t] case final b?) {
      r = b;
      return;
    }
    if (done[t] case final b?) {
      if (rests[t] case final s?) reads.addAll(s);
      r = b;
      return;
    }
    if (busy[t] case final d?) {
      reads.add(d);
      r = true;
      return;
    }
    final depth = busy.length;
    busy[t] = depth;
    final mark = pending.length;
    final outer = reads;
    reads = {};
    yield* parts(t);
    final b = r;
    final own = reads..remove(depth);
    reads = outer;
    busy.remove(t);
    // Only results decided since `t` was assumed empty can rest on that. A wrong assumption
    // can make a result wrong either way: an assumed disjointness drops a tuple type from a
    // clause, which can leave the clause inhabited. So when `t` is inhabited, each result
    // that rests on it is dropped; when it is empty, each rests instead on what `t` rests on,
    // and is confirmed when that is nothing.
    final since = pending.sublist(mark);
    pending.length = mark;
    for (final e in since) {
      final s = rests[e]!;
      if (s.remove(depth)) {
        if (!b) {
          done.remove(e);
          rests.remove(e);
          continue;
        }
        s.addAll(own);
      }
      if (s.isEmpty) {
        rests.remove(e);
      } else {
        pending.add(e);
      }
    }
    if (own.isNotEmpty) {
      reads.addAll(own);
      pending.add(t);
      rests[t] = own;
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
      yield* tuples(_Box(List.filled(e.key, Type.top), e.value), true);
      if (!r) return;
    }
    yield* morphisms(Morphism(Type.empty, Type.top, Type.top), p.morphisms, true);
  }

  /// Narrows the box and its part to what the part forces on it: a tuple type in every value
  /// of the part meets the box, and a tuple type in none is taken out of the box when it holds
  /// the box in every component but one. True when the part is proved empty on the box.
  Iterable<void> narrow(_Box b) sync* {
    final items = b.items;
    while (true) {
      for (final t in items) {
        yield* empty(t);
        if (r) return;
      }
      // Where each tuple type stands on the box: false if they are disjoint, true if it
      // holds the box, null if it is open on it.
      final stand = <Components, bool?>{};
      for (final a in _atoms(b.part)) {
        if (stand.containsKey(a)) continue;
        bool? s;
        for (var i = 0; i < items.length && s == null; i++) {
          yield* empty(items[i] & a.items[i]);
          if (r) s = false;
        }
        if (s == null) {
          var holds = true;
          for (var i = 0; i < items.length && holds; i++) {
            yield* empty(items[i] - a.items[i]);
            holds = r;
          }
          if (holds) s = true;
        }
        stand[a] = s;
      }
      b.part = b.part.restrict((a) => stand[a]).settle();
      if (b.part.leaf case final v?) {
        r = !v;
        return;
      }
      final (taken, refused) = b.part.forced();
      var changed = taken.isNotEmpty;
      for (final a in taken) {
        for (var i = 0; i < items.length; i++) {
          items[i] = items[i] & a.items[i];
        }
      }
      for (final a in refused) {
        final open = <int>[];
        for (var j = 0; j < items.length; j++) {
          yield* empty(items[j] - a.items[j]);
          if (!r) open.add(j);
        }
        if (open case [final j]) {
          items[j] = items[j] - a.items[j];
          changed = true;
        }
      }
      if (!changed) {
        r = false;
        return;
      }
    }
  }

  /// Whether no tuple in the box is in its part: the part is narrowed by what it forces; then
  /// a component whose pieces cut by the open tuple types are pairwise equal or disjoint is
  /// split into them; else each such piece on which narrowing alone proves the part empty is
  /// taken out; else, once on each branch (`mayCover`), when the part holds nothing outside
  /// the open tuple types, each of them is decided on its own. What is left counts as
  /// inhabited. A split into disjoint pieces sends each open tuple type to one piece, and a
  /// component split is never split again below, so the nodes are polynomial in the tuple
  /// types.
  Iterable<void> tuples(_Box b, bool mayCover) sync* {
    final items = b.items;
    while (true) {
      yield* narrow(b);
      if (r) return;
      if (b.part.leaf != null) {
        r = false;
        return;
      }
      final open = _atoms(b.part);
      split:
      for (var j = 0; j < items.length; j++) {
        final cells = <Type>[], seen = <Type>{};
        var union = Type.empty;
        for (final a in open) {
          final c = a.items[j] & items[j];
          yield* empty(items[j] - c);
          if (r) continue split;
          if (seen.contains(c)) continue;
          yield* empty(c & union);
          if (!r) continue split;
          union = union | c;
          cells.add(c);
          seen.add(c);
        }
        final rest = items[j] - union;
        yield* empty(rest);
        if (!r) cells.add(rest);
        for (final c in cells) {
          yield* tuples(_Box([...items]..[j] = c, b.part), mayCover);
          if (!r) return;
        }
        r = true;
        return;
      }
      var narrowed = false;
      for (var j = 0; j < items.length; j++) {
        final tried = <Type>{};
        for (final a in open) {
          for (final c in [a.items[j] & items[j], items[j] - a.items[j]]) {
            if (tried.contains(c)) continue;
            yield* empty(c);
            if (r) continue;
            yield* empty(items[j] - c);
            if (r) continue;
            tried.add(c);
            yield* narrow(_Box([...items]..[j] = c, b.part));
            if (r) {
              items[j] = items[j] - c;
              narrowed = true;
            }
          }
        }
      }
      if (narrowed) continue;
      if (mayCover && b.part.eval3((_) => false) == false) {
        for (final a in open) {
          yield* tuples(
            _Box([for (var i = 0; i < items.length; i++) items[i] & a.items[i]], b.part),
            false,
          );
          if (!r) return;
        }
        r = true;
        return;
      }
      r = false;
      return;
    }
  }

  /// Whether `m` admits no morphism: a key is promised and not permitted, or promised and no
  /// value can be its. A key is promised only when a value is shown in the type: a type not
  /// proved empty may still be empty, and then the empty morphism is admitted.
  Iterable<void> noMorphism(Morphism m) sync* {
    yield* rep(m.guarantee - m.permission);
    if (found != null) {
      r = true;
      return;
    }
    yield* rep(m.guarantee);
    if (found == null) {
      r = false;
      return;
    }
    yield* empty(m.value);
  }

  /// A value in `t`, if one is found: a scalar or bare atom of it, or a tuple or atom payload
  /// whose components have representatives and which `t` holds. The tuples tried at each
  /// length are two: the box the tuple types narrow the part to, and its meet with the first
  /// tuple type left open; each is tested against every tuple type of `t`, so a poor choice
  /// costs precision, never soundness. A type met again while its own is sought has none on
  /// that path, since a value is finite; none found means only that, never that `t` is
  /// empty. Each type is tried once and each test of a representative against a type is made
  /// once, so a value nested in shared types is never copied out.
  Iterable<void> rep(Type t) sync* {
    if (reps.containsKey(t)) {
      found = reps[t];
      return;
    }
    reps[t] = null;
    yield* _find(t);
    reps[t] = found;
  }

  Iterable<void> _find(Type t) sync* {
    found = _scalar(t);
    if (found != null) return;
    for (final (name, a) in t.atoms.names.entries) {
      if (a.bare) {
        found = _ValueRep(Atom(name));
        return;
      }
      yield* rep(a.payload);
      if (found is _TupleRep) {
        found = _AtomRep(name, a.payload);
        return;
      }
    }
    if (t.tuples.rest) {
      var len = 0;
      while (t.tuples.lens.containsKey(len)) {
        len++;
      }
      found = _TupleRep(Components(List.filled(len, Type.top)));
      return;
    }
    for (final MapEntry(key: len, value: f) in t.tuples.lens.entries) {
      final box = _Box(List.filled(len, Type.top), f);
      yield* narrow(box);
      if (r) continue;
      final rows = [Components(box.items)];
      if (_first(box.part) case final a?) {
        rows.add(Components([for (var i = 0; i < len; i++) box.items[i] & a.items[i]]));
      }
      for (final row in rows) {
        var all = true;
        for (final x in row.items) {
          yield* rep(x);
          if (found == null) {
            all = false;
            break;
          }
        }
        if (!all) continue;
        yield* holds(row, f);
        if (r) {
          found = _TupleRep(row);
          return;
        }
      }
    }
    found = null;
  }

  /// A Boolean, a literal or an atom in `t`, if it holds one: the first listed in a finite
  /// set, and for a cofinite set of integers, strings or atoms the first not listed.
  static _Rep? _scalar(Type t) {
    if (t.bools != 0) return _ValueRep(Bool(t.bools & 1 == 0));
    for (final (l, make) in <(Lits, Value Function(int)?)>[
      (t.ints, Int.new),
      (t.strings, (i) => Str('$i')),
      (t.rats, null),
      (t.floats, null),
    ]) {
      if (!l.cofinite) {
        if (l.values.isNotEmpty) return _ValueRep(l.values.keys.first);
      } else if (make != null) {
        var i = 0;
        while (l.values.containsKey(make(i))) {
          i++;
        }
        return _ValueRep(make(i));
      }
    }
    if (t.atoms.cofinite) {
      var i = 0;
      while (t.atoms.names[('a$i')] != null) {
        i++;
      }
      return _ValueRep(Atom('a$i'));
    }
    return null;
  }

  /// Whether the tuple of the representatives of `row` is in `f`.
  Iterable<void> holds(Components row, Part<Components> f) sync* {
    final fits = <Components>{};
    for (final a in _atoms(f)) {
      var all = true;
      for (var i = 0; i < row.items.length && all; i++) {
        yield* member(row.items[i], a.items[i]);
        all = r;
      }
      if (all) fits.add(a);
    }
    r = f.eval(fits.contains);
  }

  /// Whether the representative of `t`, which has one, is in `u`.
  Iterable<void> member(Type t, Type u) sync* {
    final key = (t, u);
    if (members[key] case final b?) {
      r = b;
      return;
    }
    yield* rep(t);
    switch (found!) {
      case _ValueRep(:final value):
        r = u.contains(value);
      case _TupleRep(:final row):
        yield* holds(row, u.tuples.get(row.items.length));
      case _AtomRep(:final name, :final payload):
        if (u.atoms.names[name] case final a?) {
          yield* member(payload, a.payload);
        } else {
          r = u.atoms.cofinite;
        }
    }
    members[key] = r;
  }

  /// Whether every morphism `m` admits is in `n`, by the variance law. With no value, the
  /// empty morphism is the only one, and its domain is the guarantee.
  Iterable<void> within(Morphism m, Morphism n) sync* {
    yield* empty(m.value);
    final noValue = r;
    yield* empty(n.guarantee - m.guarantee);
    if (!r || noValue) return;
    yield* empty(m.permission - n.permission);
    if (!r) return;
    yield* empty(m.permission);
    if (r) return;
    yield* empty(m.value - n.value);
  }

  /// Whether no morphism `m` admits is in `f`, decided as for tuples: `m` meets the morphism
  /// types in every value of `f`, and, once on each branch (`mayCover`), when `f` holds
  /// nothing outside the open morphism types, each is decided on its own. Morphism types are
  /// closed under meet but not under difference, so a type in no value of `f` narrows
  /// nothing.
  Iterable<void> morphisms(Morphism m, Part<Morphism> f, bool mayCover) sync* {
    while (true) {
      yield* noMorphism(m);
      if (r) return;
      final stand = <Morphism, bool?>{};
      for (final a in _atoms(f)) {
        if (stand.containsKey(a)) continue;
        yield* noMorphism(_meet(m, a));
        if (r) {
          stand[a] = false;
          continue;
        }
        yield* within(m, a);
        stand[a] = r ? true : null;
      }
      f = f.restrict((a) => stand[a]).settle();
      if (f.leaf case final v?) {
        r = !v;
        return;
      }
      final (taken, _) = f.forced();
      if (taken.isNotEmpty) {
        m = taken.fold(m, _meet);
        continue;
      }
      if (mayCover && f.eval3((_) => false) == false) {
        for (final a in _atoms(f)) {
          yield* morphisms(_meet(m, a), f, false);
          if (!r) return;
        }
        r = true;
        return;
      }
      r = false;
      return;
    }
  }
}

/// The morphisms both `a` and `b` admit.
Morphism _meet(Morphism a, Morphism b) =>
    Morphism(a.guarantee | b.guarantee, a.permission & b.permission, a.value & b.value);

/// The atoms of `p`, each node's in preorder, `hi` first.
List<A> _atoms<A extends Literal<A>>(Part<A> p) {
  final out = <A>[];
  p.atoms((a) {
    out.add(a);
    return true;
  });
  return out;
}

/// The first atom of `p` in preorder, if any.
A? _first<A extends Literal<A>>(Part<A> p) {
  A? first;
  p.atoms((a) {
    first = a;
    return false;
  });
  return first;
}

/// A box of tuples, one type per component, and the part decided on it; both are narrowed in
/// place.
final class _Box {
  final List<Type> items;
  Part<Components> part;

  _Box(this.items, this.part);
}

/// A value known to be in a type, held as the types of its parts, each with a representative
/// of its own.
sealed class _Rep {
  const _Rep();
}

final class _ValueRep extends _Rep {
  final Value value;

  const _ValueRep(this.value);
}

final class _TupleRep extends _Rep {
  final Components row;

  const _TupleRep(this.row);
}

/// An atom of this name, whose payload is the representative tuple of this type.
final class _AtomRep extends _Rep {
  final String name;
  final Type payload;

  const _AtomRep(this.name, this.payload);
}
