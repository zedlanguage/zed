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
// does not hold the box. A tuple type that misses or holds a component still does when the box
// shrinks, so only the components changed since they were last tested are tested again,
// against the tuple types open on them. When narrowing stops, a component whose pieces cut by
// the open tuple types are pairwise equal or disjoint is split into those pieces, and each
// piece decided; otherwise each piece on which narrowing alone proves the part empty is taken
// out of the box; otherwise, once on each branch, when the part holds nothing outside the open
// tuple types, the box is split into its meet with each of them. A box none of these steps
// settles counts as inhabited. The morphism part is decided the same way, by the variance law: contravariant
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
      yield* tuples(_Region(List.filled(e.key, Type.top), e.value), true);
      if (!r) return;
    }
    yield* morphisms(Morphism(Type.empty, Type.top, Type.top), p.morphisms, true);
  }

  /// Tests each changed component of the box against the tuple types of its part open on it,
  /// and closes those it settles. A tuple type that misses one is out of the part, so whether
  /// it holds the others is not tested.
  Iterable<void> retest(_Region g) sync* {
    final changed = [
      for (var j = 0; j < g.items.length; j++)
        if (g.changed[j]) j,
    ];
    if (changed.isEmpty) return;
    for (final j in changed) {
      g.tested(j);
    }
    live:
    for (final a in g.live()) {
      for (final j in changed) {
        if (!g.open[j].contains(a)) continue;
        yield* empty(g.items[j] & a.type.items[j]);
        if (r) {
          g.close(a, j, missed: true);
          continue live;
        }
      }
      for (final j in changed) {
        if (!g.open[j].contains(a)) continue;
        yield* empty(g.items[j] - a.type.items[j]);
        if (r) g.close(a, j, missed: false);
      }
    }
  }

  /// Narrows the box and its part to what the part forces on it: a tuple type in every value
  /// of the part meets the box, and a tuple type in none is taken out of the box when it holds
  /// the box in every component but one. True when the part is proved empty on the box.
  Iterable<void> narrow(_Region g) sync* {
    final items = g.items;
    while (true) {
      for (final t in items) {
        yield* empty(t);
        if (r) return;
      }
      yield* retest(g);
      g.part = g.part.restrict((a) => g.stands[a]!.stand).settle();
      if (g.part.leaf case final v?) {
        r = !v;
        return;
      }
      final (taken, refused) = g.part.forced();
      // The components changed in this pass, against which a refused tuple type's standing is
      // tested before it is used.
      final shrunk = <int>{};
      for (final a in taken) {
        final s = g.stands[a]!;
        for (var j = 0; j < items.length; j++) {
          if (g.open[j].contains(s)) {
            g.shrink(j, items[j] & a.items[j]);
            shrunk.add(j);
          }
        }
      }
      refused:
      for (final a in refused) {
        final s = g.stands[a]!;
        var (loose, at) = (s.loose, s.at);
        for (final j in shrunk) {
          if (!g.open[j].contains(s)) continue;
          yield* empty(items[j] & a.items[j]);
          if (r) continue refused;
          yield* empty(items[j] - a.items[j]);
          if (r) {
            loose--;
            at -= j;
          }
        }
        if (s.missed == 0 && loose == 1) {
          g.shrink(at, items[at] - a.items[at]);
          shrunk.add(at);
        }
      }
      if (shrunk.isEmpty) {
        r = false;
        return;
      }
    }
  }

  /// Whether no tuple in the box is in its part: the part is narrowed by what it forces; then
  /// a component on which every open tuple type is open, and whose pieces cut by them are
  /// pairwise equal or disjoint, is split into them; else each such piece on which narrowing
  /// alone proves the part empty is taken out; else, once on each branch (`mayCover`), when
  /// the part holds nothing outside the open tuple types, each of them is decided on its own.
  /// What is left counts as inhabited. A split into disjoint pieces sends each open tuple type
  /// to one piece, and a component split is never split again below, so the nodes are
  /// polynomial in the tuple types. The components tried for a split are those on which the
  /// open tuple type open on fewest is open, so a box most of whose components the tuple types
  /// hold is not searched. Each piece is tried on the box and the box restored after.
  Iterable<void> tuples(_Region g, bool mayCover) sync* {
    final items = g.items;
    while (true) {
      yield* narrow(g);
      if (r) return;
      if (g.part.leaf != null) {
        r = false;
        return;
      }
      final open = g.live();
      final fewest = open.reduce((a, b) => b.loose < a.loose ? b : a);
      split:
      for (var j = 0; j < items.length; j++) {
        final on = g.open[j];
        if (!on.contains(fewest) || on.length < open.length || !open.every(on.contains)) {
          continue;
        }
        final cells = <Type>{};
        var union = Type.empty;
        for (final a in open) {
          final c = a.type.items[j] & items[j];
          if (cells.contains(c)) continue;
          yield* empty(c & union);
          if (!r) continue split;
          union = union | c;
          cells.add(c);
        }
        final rest = items[j] - union;
        yield* empty(rest);
        if (!r) cells.add(rest);
        for (final c in cells) {
          final mark = g.mark;
          g.shrink(j, c);
          yield* tuples(g, mayCover);
          g.restore(mark);
          if (!r) return;
        }
        r = true;
        return;
      }
      var narrowed = false;
      for (var j = 0; j < items.length; j++) {
        final tried = <Type>{};
        for (final a in open) {
          final t = a.type.items[j];
          for (final c in [t & items[j], items[j] - t]) {
            if (tried.contains(c)) continue;
            yield* empty(c);
            if (r) continue;
            yield* empty(items[j] - c);
            if (r) continue;
            tried.add(c);
            final mark = g.mark;
            g.shrink(j, c);
            yield* narrow(g);
            g.restore(mark);
            if (r) {
              g.shrink(j, items[j] - c);
              narrowed = true;
            }
          }
        }
      }
      if (narrowed) continue;
      if (mayCover && g.part.eval3((_) => false) == false) {
        for (final a in open) {
          final mark = g.mark;
          for (var j = 0; j < items.length; j++) {
            if (g.open[j].contains(a)) g.shrink(j, items[j] & a.type.items[j]);
          }
          yield* tuples(g, false);
          g.restore(mark);
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
      final g = _Region(List.filled(len, Type.top), f);
      yield* narrow(g);
      if (r) continue;
      final rows = [Components(g.items)];
      if (_first(g.part) case final a?) {
        rows.add(Components([for (var i = 0; i < len; i++) g.items[i] & a.items[i]]));
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

/// A box of tuples, one type per component, the part decided on it, and where each tuple type
/// of the part stands on it component by component: missing it, holding it, or open on it. A
/// tuple type that misses a component of the box, or holds it, still does when the box
/// shrinks, so a component that changed is tested again only against the tuple types open on
/// it and still in the part, and only when they are next read. Each tuple type starts open on
/// every component, and each component changed. Each change is logged, so a piece of the box
/// is tried and the box and the part restored after.
final class _Region {
  final List<Type> items;
  Part<Components> _part;

  /// Each tuple type of the part, with where it stands.
  final stands = <Components, _Stand>{};

  /// For each component, the tuple types open on it when it was last tested.
  final List<Set<_Stand>> open;

  /// For each component, whether it changed since it was last tested.
  final List<bool> changed;

  /// How to undo each change, in the order made.
  final _log = <void Function()>[];

  _Region(this.items, this._part)
    : open = [for (final _ in items) <_Stand>{}],
      changed = List.filled(items.length, true) {
    final at = items.length * (items.length - 1) ~/ 2;
    for (final a in _atoms(_part)) {
      stands.putIfAbsent(a, () {
        final s = _Stand(a, items.length, at);
        for (final on in open) {
          on.add(s);
        }
        return s;
      });
    }
  }

  Part<Components> get part => _part;

  set part(Part<Components> p) {
    final before = _part;
    _log.add(() => _part = before);
    _part = p;
  }

  /// The tuple types of the part, each once.
  Set<_Stand> live() => {for (final a in _atoms(_part)) stands[a]!};

  /// The point [restore] goes back to.
  int get mark => _log.length;

  /// Undoes the changes made after `mark`.
  void restore(int mark) {
    while (_log.length > mark) {
      _log.removeLast()();
    }
  }

  /// Sets component `j` of the box to `t`, which is within it.
  void shrink(int j, Type t) {
    final (before, was) = (items[j], changed[j]);
    _log.add(() {
      items[j] = before;
      changed[j] = was;
    });
    items[j] = t;
    changed[j] = true;
  }

  /// Marks component `j` tested.
  void tested(int j) {
    changed[j] = false;
    _log.add(() => changed[j] = true);
  }

  /// Marks `a` no longer open on component `j`: missing it, or holding it.
  void close(_Stand a, int j, {required bool missed}) {
    open[j].remove(a);
    if (missed) {
      a.missed++;
    } else {
      a.loose--;
      a.at -= j;
    }
    _log.add(() {
      open[j].add(a);
      if (missed) {
        a.missed--;
      } else {
        a.loose++;
        a.at += j;
      }
    });
  }
}

/// A tuple type of a part, and where it stands on the box of its region: how many components
/// it misses, and how many it does not hold with the sum of their positions, which is the
/// position when there is one.
final class _Stand {
  final Components type;
  var missed = 0;
  int loose, at;

  _Stand(this.type, this.loose, this.at);

  /// Where it stands on the box, as last tested: false if it misses it, true if it holds it,
  /// null if it is open on it.
  bool? get stand => missed > 0 ? false : (loose == 0 ? true : null);
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
