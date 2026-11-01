/// Types (step L1.22, DESIGN.md sec:type_language): sets of values, closed under union,
/// intersection and complement.
///
/// A type has one part per universe (sec:type_language, the kinding of the connectives): the
/// scalars, which are the literals of each base type and the atoms; the tuples; the structs;
/// and the morphisms. A connective acts on each part on its own, so a complement is taken
/// within each universe. A scalar part is exact: a finite or cofinite set of literals per base
/// type, and per atom name whether the bare atom is in it and which payloads are. The tuple
/// part is, per length, and the morphism part is, a decision diagram over types of the universe
/// (bdd.dart): a Boolean function of tuple or morphism types. Whether one is empty is decided
/// by subtyping (empty.dart), so two of them may denote one set and differ. Structs join at
/// L2: until then the struct part is every struct or none.
///
/// A morphism type bounds its domain from both sides: the keys it guarantees and the keys it
/// permits, with every present key's value in the value type. `K -> V` is exact and
/// `K ->? V` guarantees no key.
///
/// A recursive type (rec.dart) is a node that stands for its definition's body and unfolds to
/// it when a connective needs its parts. A node unfolds one level at a time: a tuple component,
/// atom payload or morphism bound that mentions a recursive type is kept as written rather
/// than met with another, so no connective unfolds a type without end. Whether a type is
/// empty, and so subtyping, is decided in empty.dart.
library;

import 'dart:collection';
import 'dart:convert';

import 'pmap.dart';
import 'text.dart';
import 'value.dart';

part 'bdd.dart';
part 'empty.dart';

/// Combines two hashes; the digests of types, nodes and expressions are built with it from
/// their children's, so that each is computed once, when it is made.
int mix(int a, int b) {
  // splitmix64's finalizer.
  var z = (((a << 29) | (a >>> 35)) ^ b) + 0x9e3779b97f4a7c15;
  z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9;
  z = (z ^ (z >>> 27)) * 0x94d049bb133111eb;
  return z ^ (z >>> 31);
}

/// FNV-1a over `b`.
int _bytes(List<int> b) {
  var h = 0xcbf29ce484222325;
  for (final x in b) {
    h = (h ^ x) * 0x100000001b3;
  }
  return h;
}

/// A hash of a literal: equal literals print alike.
int _scalar(Value v) => switch (v) {
  Int(:final value) => mix(1, value),
  Str(:final text) => mix(2, _bytes(utf8.encode(text.text))),
  _ => mix(3, _bytes(utf8.encode('$v'))),
};

/// Digests are compared as unsigned 64-bit numbers.
int _cmpDigest(int a, int b) => (a ^ _sign).compareTo(b ^ _sign);

const _sign = 0x8000000000000000;

int _cmpBool(bool a, bool b) => a == b ? 0 : (a ? 1 : -1);

/// `a` and `b` in lexicographic order, a prefix first.
int _lex<T>(Iterable<T> a, Iterable<T> b, int Function(T, T) cmp) {
  final x = a.iterator, y = b.iterator;
  while (true) {
    final (p, q) = (x.moveNext(), y.moveNext());
    if (!p || !q) return _cmpBool(p, q);
    final c = cmp(x.current, y.current);
    if (c != 0) return c;
  }
}

int _byValue(Value a, Value b) => a.compareTo(b);

/// The universes of values, within each of which a complement is taken.
enum Universe {
  /// Booleans, numbers, strings and atoms.
  scalar,

  /// Tuples of every length, and keypaths.
  tuple,

  /// Structs, which join at L2.
  struct,

  /// Functions and families.
  morphism;

  /// The universe of `v`. A keypath is a tuple of keys; an atom with its payload is a scalar.
  static Universe of(Value v) => switch (v) {
    Tuple() || Path() => Universe.tuple,
    Family() => Universe.morphism,
    _ => Universe.scalar,
  };
}

/// A type: the set of values it denotes, given by its parts or, for a recursive type, by a
/// node that unfolds to them. Types are ordered by their digests first, so two types are
/// ordered without reading their contents unless their digests are equal.
sealed class Type implements Comparable<Type> {
  /// The hash of the contents, computed when the type is made; a recursive node's is its
  /// identity's, since two such nodes are one type only when they are one node.
  int get digest;

  /// Bit 0 for `false`, bit 1 for `true`.
  int get bools;
  Lits get ints;
  Lits get rats;
  Lits get floats;
  Lits get strings;
  Atoms get atoms;
  Tuples get tuples;
  bool get structs;
  Part<Morphism> get morphisms;

  /// The node named `naming()` whose parts are `make()`'s, each computed when first needed
  /// (rec.dart). `make` must not need this node's parts, which a contractive definition
  /// ensures.
  static Type recursive(String Function() naming, Type Function() make) => _Rec(naming, make);

  /// The type with the given parts, each not given empty.
  static Type _with({
    int bools = 0,
    Lits ints = Lits.none,
    Lits rats = Lits.none,
    Lits floats = Lits.none,
    Lits strings = Lits.none,
    Atoms atoms = Atoms.none,
    Tuples? tuples,
    bool structs = false,
    Part<Morphism>? morphisms,
  }) => _Parts(
    bools,
    ints,
    rats,
    floats,
    strings,
    atoms,
    tuples ?? Tuples.none,
    structs,
    morphisms ?? Leaf<Morphism>(false),
  );

  /// No value.
  static final Type empty = _with();

  /// Every value, `_`.
  static final Type top = ~empty;

  /// The union of `ts`, joined in pairs: `k` tuple or morphism types, each ordered after the
  /// last in the diagrams, cost `O(k log k)` nodes joined this way and `O(k²)` one at a time.
  static Type unionAll(Iterable<Type> ts) => _pairwise(ts, empty, (a, b) => a | b);

  /// The intersection of `ts`, joined in pairs as in [unionAll].
  static Type meetAll(Iterable<Type> ts) => _pairwise(ts, top, (a, b) => a & b);

  static Type _pairwise(Iterable<Type> ts, Type unit, Type Function(Type, Type) op) {
    var level = ts.toList();
    while (level.length > 1) {
      level = [
        for (var i = 0; i < level.length; i += 2)
          i + 1 < level.length ? op(level[i], level[i + 1]) : level[i],
      ];
    }
    return level.isEmpty ? unit : level[0];
  }

  /// `bool`.
  static final Type boolean = _with(bools: 3);

  /// `int`.
  static final Type integer = _with(ints: Lits.all);

  /// `rat`.
  static final Type rational = _with(rats: Lits.all);

  /// `f64`.
  static final Type f64 = _with(floats: Lits.all);

  /// `String`.
  static final Type string = _with(strings: Lits.all);

  /// The type of one scalar literal or bare atom; null for any other value.
  static Type? lit(Value v) => switch (v) {
    Bool(:final value) => _with(bools: value ? 2 : 1),
    Int() || Big() => _with(ints: Lits.none.plus(v)),
    Rat() => _with(rats: Lits.none.plus(v)),
    Float() => _with(floats: Lits.none.plus(v)),
    Str() => _with(strings: Lits.none.plus(v)),
    Atom(:final name, args: []) => atom(name),
    _ => null,
  };

  /// The bare atom `#name`.
  static Type atom(String name) => _atomPart(name, AtomPart(true, empty));

  /// `#name(payload)`: the atoms of that name whose payload, a tuple or struct, is in
  /// `payload`.
  static Type atomWith(String name, Type payload) =>
      _atomPart(name, AtomPart(false, payload & _payloads));

  static Type _atomPart(String name, AtomPart part) => _with(atoms: Atoms.none.set(name, part));

  /// The tuple type `(t1, …, tn)`.
  static Type tuple(List<Type> items) => _with(tuples: Tuples.literal(items));

  /// The morphism type with the given bounds and value type.
  static Type morphism(Type guarantee, Type permission, Type value) =>
      _with(morphisms: Part.literal(Morphism(guarantee, permission, value)));

  /// `K -> V`, exact: every key of `K` is present.
  static Type exact(Type key, Type value) => morphism(key, key, value);

  /// `K ->? V`: the keys are drawn from `K`, none promised.
  static Type partial(Type key, Type value) => morphism(empty, key, value);

  /// Every value of `u`.
  static Type universe(Universe u) => switch (u) {
    Universe.scalar => _with(
      bools: 3,
      ints: Lits.all,
      rats: Lits.all,
      floats: Lits.all,
      strings: Lits.all,
      atoms: Atoms.all,
    ),
    Universe.tuple => _with(tuples: Tuples(true, SplayTreeMap())),
    Universe.struct => _with(structs: true),
    Universe.morphism => _with(morphisms: Leaf<Morphism>(true)),
  };

  /// The values an atom's payload may be: tuples and structs.
  static final Type _payloads = universe(Universe.tuple) | universe(Universe.struct);

  /// The values of `this` in `u`.
  Type part(Universe u) => this & universe(u);

  /// Whether membership in `this` is decidable at run time: no part of it, nor of a tuple
  /// component or atom payload it holds, is a proper subset of the morphisms
  /// (sec:type_notation: run-time type tests are restricted to decidable checks). Each type
  /// is checked once, however often the others hold it.
  bool get decidable {
    final seen = <Type>{};
    bool go(Type t) {
      if (!seen.add(t)) return true;
      return t.morphisms.leaf != null &&
          t.atoms.names.values.every((a) => go(a.payload)) &&
          t.tuples.atoms((c) => c.items.every(go));
    }

    return go(this);
  }

  /// Whether every function is in `this`; for a decidable type, either every function is or
  /// none is.
  bool get functions => morphisms.leaf == true;

  /// Whether `v` is in `this`, for a decidable `this`.
  bool contains(Value v) => switch (v) {
    Bool(:final value) => bools & (value ? 2 : 1) != 0,
    Int() || Big() => ints.contains(v),
    Rat() => rats.contains(v),
    Float() => floats.contains(v),
    Str() => strings.contains(v),
    Atom(:final name, :final fields, :final args) => switch (atoms.names[name]) {
      null => atoms.cofinite,
      final part when args.isEmpty => part.bare,
      final part when fields.isEmpty => part.payload._containsTuple(args),
      final part => part.payload.structs,
    },
    Tuple(:final items) => _containsTuple(items),
    Path(:final keys) => _containsTuple(keys),
    Family() => functions,
  };

  /// Whether the tuple of `xs` is in `this`, read in place: an atom's payload is not copied
  /// into a tuple to be tested.
  bool _containsTuple(List<Value> xs) => tuples.get(xs.length).eval((c) {
    for (var i = 0; i < xs.length; i++) {
      if (!c.items[i].contains(xs[i])) return false;
    }
    return true;
  });

  Type _zip(Type o, bool or) => _Parts(
    or ? bools | o.bools : bools & o.bools,
    ints.zip(o.ints, or),
    rats.zip(o.rats, or),
    floats.zip(o.floats, or),
    strings.zip(o.strings, or),
    atoms.zip(o.atoms, or),
    tuples.zip(o.tuples, or),
    or ? structs || o.structs : structs && o.structs,
    morphisms.zip(o.morphisms, or),
  );

  /// The union.
  Type operator |(Type o) => _zip(o, true);

  /// The intersection.
  Type operator &(Type o) => _zip(o, false);

  /// The difference `a \ b`, which is `a & ~b`.
  Type operator -(Type o) => this & ~o;

  /// The complement, within each universe.
  Type operator ~() => _Parts(
    ~bools & 3,
    ints.not(),
    rats.not(),
    floats.not(),
    strings.not(),
    atoms.not(),
    tuples.not(),
    !structs,
    ~morphisms,
  );

  /// Types given by their parts order before recursive nodes, which order by identity.
  @override
  int compareTo(Type o) {
    if (identical(this, o)) return 0;
    final c = _cmpDigest(digest, o.digest);
    if (c != 0) return c;
    return switch ((this, o)) {
      (final _Parts a, final _Parts b) => a._compare(b),
      (final _Rec a, final _Rec b) => a.id.compareTo(b.id),
      (_Parts(), _Rec()) => -1,
      (_Rec(), _Parts()) => 1,
    };
  }

  @override
  bool operator ==(Object other) => other is Type && compareTo(other) == 0;

  @override
  int get hashCode => digest;

  /// The parts as a prefix expression, the form of the syntax tree's types: `_` is every value
  /// and `(|)` none; `int` every integer, `(\ int 3)` every one but 3; `#_` every atom; `(#a _)`
  /// the atoms `#a` with any payload; `(tuple A B)`, `(! X)`, `(& X Y)`, and `tuple`, `struct`
  /// and `morphism` every value of those universes; `(-> K V)` exact, `(->? K V)` with no
  /// guarantee, `(-> L U V)` otherwise. Made once, when first asked for. A recursive node is
  /// its name.
  @override
  String toString() => switch (this) {
    final _Parts p => p._text ??= _show(),
    final _Rec r => r.name,
  };

  String _show() {
    if (this == top) return '_';
    final items = <String>[];
    switch (bools) {
      case 1:
        items.add('false');
      case 2:
        items.add('true');
      case 3:
        items.add('bool');
    }
    for (final (name, l) in [('int', ints), ('rat', rats), ('f64', floats), ('String', strings)]) {
      switch ((l.cofinite, l.values.isEmpty)) {
        case (true, true):
          items.add(name);
        case (true, false):
          items.add('(\\ $name ${l.values.keys.join(' ')})');
        case (false, _):
          items.addAll(l.values.keys.map((v) => '$v'));
      }
    }
    Iterable<String> atom(String name, AtomPart part) sync* {
      if (part.bare) yield '#$name';
      if (part.payload == _payloads) {
        yield '(#$name _)';
      } else if (part.payload != empty) {
        yield '(#$name ${part.payload})';
      }
    }

    if (atoms.cofinite) {
      final except = [for (final (n, part) in atoms.names.entries) ...atom(n, part.not())];
      items.add(except.isEmpty ? '#_' : '(\\ #_ ${except.join(' ')})');
    } else {
      for (final (n, part) in atoms.names.entries) {
        items.addAll(atom(n, part));
      }
    }
    _showTuples(items, tuples);
    if (structs) items.add('struct');
    _clauses(items, 'morphism', morphisms, (m) {
      if (m.guarantee == m.permission) return '(-> ${m.permission} ${m.value})';
      if (m.guarantee == empty) return '(->? ${m.permission} ${m.value})';
      return '(-> ${m.guarantee} ${m.permission} ${m.value})';
    });
    return _union(items);
  }
}

/// A type given by its parts.
final class _Parts extends Type {
  @override
  final int digest;
  @override
  final int bools;
  @override
  final Lits ints, rats, floats, strings;
  @override
  final Atoms atoms;
  @override
  final Tuples tuples;
  @override
  final bool structs;
  @override
  final Part<Morphism> morphisms;

  String? _text;

  _Parts(
    this.bools,
    this.ints,
    this.rats,
    this.floats,
    this.strings,
    this.atoms,
    this.tuples,
    this.structs,
    this.morphisms,
  ) : digest = _hash(bools, [ints, rats, floats, strings], atoms, tuples, structs, morphisms);

  static int _hash(
    int bools,
    List<Lits> lits,
    Atoms atoms,
    Tuples tuples,
    bool structs,
    Part<Morphism> morphisms,
  ) {
    int bit(bool b) => b ? 1 : 0;
    var h = mix(0, bools);
    for (final l in lits) {
      h = mix(mix(h, bit(l.cofinite)), l.sum);
    }
    h = mix(mix(h, bit(atoms.cofinite)), atoms.sum);
    h = mix(h, bit(tuples.rest));
    for (final MapEntry(key: len, value: part) in tuples.lens.entries) {
      h = mix(mix(h, len), part.digest);
    }
    return mix(mix(h, bit(structs)), morphisms.digest);
  }

  int _compare(_Parts o) {
    var c = bools - o.bools;
    if (c == 0) c = ints.compareTo(o.ints);
    if (c == 0) c = rats.compareTo(o.rats);
    if (c == 0) c = floats.compareTo(o.floats);
    if (c == 0) c = strings.compareTo(o.strings);
    if (c == 0) c = atoms.compareTo(o.atoms);
    if (c == 0) c = tuples.compareTo(o.tuples);
    if (c == 0) c = _cmpBool(structs, o.structs);
    if (c == 0) c = morphisms.compareTo(o.morphisms);
    return c;
  }
}

/// A recursive type, or a part of a recursive definition's body kept unevaluated: its parts
/// are `make()`'s, computed on first use. Two nodes are one type only when they are one node.
final class _Rec extends Type {
  static var _next = 0;

  final int id;
  @override
  final int digest;
  final String Function() _naming;
  final Type Function() _make;

  /// The name, made when first printed: a name spells out its part of the definition, so
  /// making every part's name at once would cost the product of the definition's size and
  /// depth.
  late final String name = _naming();

  /// The parts, made when first needed.
  late final _Parts _body = switch (_make()) {
    final _Parts p => p,
    final _Rec r => r._body,
  };

  _Rec(this._naming, this._make) : id = _next, digest = mix(4, _next++);

  @override
  int get bools => _body.bools;
  @override
  Lits get ints => _body.ints;
  @override
  Lits get rats => _body.rats;
  @override
  Lits get floats => _body.floats;
  @override
  Lits get strings => _body.strings;
  @override
  Atoms get atoms => _body.atoms;
  @override
  Tuples get tuples => _body.tuples;
  @override
  bool get structs => _body.structs;
  @override
  Part<Morphism> get morphisms => _body.morphisms;
}

/// `(| a b …)`, or the one item alone.
String _union(List<String> items) =>
    items.length == 1 ? items[0] : '(|${items.map((i) => ' $i').join()})';

/// The items of a tuple part. With `rest`, it is every tuple outside its complement's items.
void _showTuples(List<String> items, Tuples t) {
  if (t.rest) {
    final except = <String>[];
    _showTuples(except, t.not());
    items.add(switch (except.length) {
      0 => 'tuple',
      1 => '(& tuple (! ${except[0]}))',
      _ => '(& tuple (! ${_union(except)}))',
    });
    return;
  }
  String tuple(Components c) => '(tuple${c.items.map((t) => ' $t').join()})';
  for (final MapEntry(key: len, value: b) in t.lens.entries) {
    _clauses(items, tuple(Components(List.filled(len, Type.top))), b, tuple);
  }
}

/// One item per path of a diagram: the intersection of the atoms it takes, or `all` when it
/// takes none, and the complements of those it refuses. The items, and the atoms within each,
/// are sorted as text, since the diagram's order of atoms is that of their digests. A part
/// kept as an expression is its connective applied to the items of its operands.
void _clauses<A extends Literal<A>>(
  List<String> items,
  String all,
  Part<A> part,
  String Function(A) show,
) {
  if (part case Expr(:final op, :final a, :final b)) {
    String item(Part<A> p) {
      final sub = <String>[];
      _clauses(sub, all, p, show);
      return sub.isEmpty ? '(|)' : _union(sub);
    }

    items.add(switch (op) {
      ExprOp.not => '(& $all (! ${item(a)}))',
      ExprOp.or => '(| ${item(a)} ${item(b!)})',
      ExprOp.and => '(& ${item(a)} ${item(b!)})',
    });
    return;
  }
  final found = <String>[];
  (part as Bdd<A>).walk(false, (pos, neg) {
    final lits = [for (final a in pos) show(a)]..sort(compareUtf8);
    if (lits.isEmpty) lits.add(all);
    lits.addAll([for (final n in neg) '(! ${show(n)})']..sort(compareUtf8));
    found.add(lits.length == 1 ? lits[0] : '(&${lits.map((l) => ' $l').join()})');
    return true;
  });
  items.addAll(found..sort(compareUtf8));
}

/// A morphism type: `(guarantee ⊆ dom ⊆ permission) -> value`.
final class Morphism implements Literal<Morphism> {
  /// The keys certainly present.
  final Type guarantee;

  /// The keys possibly present.
  final Type permission;

  /// The type of every present key's value.
  final Type value;

  @override
  final int digest;

  Morphism(this.guarantee, this.permission, this.value)
    : digest = mix(mix(mix(6, guarantee.digest), permission.digest), value.digest);

  @override
  int compareTo(Morphism o) {
    var c = guarantee.compareTo(o.guarantee);
    if (c == 0) c = permission.compareTo(o.permission);
    if (c == 0) c = value.compareTo(o.value);
    return c;
  }

  @override
  bool operator ==(Object other) => other is Morphism && compareTo(other) == 0;

  @override
  int get hashCode => digest;
}

/// The component types of a tuple type: an atom of a tuple part's diagram.
final class Components implements Literal<Components> {
  final List<Type> items;

  @override
  final int digest;

  Components(this.items) : digest = items.fold(5, (h, t) => mix(h, t.digest));

  @override
  int compareTo(Components o) => _lex(items, o.items, (a, b) => a.compareTo(b));

  @override
  bool operator ==(Object other) => other is Components && compareTo(other) == 0;

  @override
  int get hashCode => digest;
}

/// A finite set of literals, or the complement of one within its base type. The set is
/// persistent, so that a union or difference with a small set copies nothing else, and `sum`,
/// the wrapping sum of its literals' hashes, is kept as it changes.
final class Lits implements Comparable<Lits> {
  final bool cofinite;
  final PMap<Value, bool> values;
  final int sum;

  const Lits(this.cofinite, this.values, this.sum);

  static const none = Lits(false, PMap.empty(_byValue), 0);
  static const all = Lits(true, PMap.empty(_byValue), 0);

  bool contains(Value v) => values.containsKey(v) != cofinite;

  Lits plus(Value v) =>
      values.containsKey(v) ? this : Lits(cofinite, values.put(v, true), sum + _scalar(v));

  Lits minus(Value v) =>
      values.containsKey(v) ? Lits(cofinite, values.remove(v), sum - _scalar(v)) : this;

  /// The sets combined by `or` or `and`, each in `O(s log l)` steps for the smaller set's `s`
  /// literals and the larger's `l`: the result is the larger set changed by the smaller's
  /// literals, or the smaller set's literals filtered.
  Lits zip(Lits b, bool or) {
    final a = this;
    final (cofinite, out) = switch ((or, a.cofinite, b.cofinite)) {
      (true, false, false) => (false, _union(a, b)),
      (true, false, true) => (true, _without(b, a)),
      (true, true, false) => (true, _without(a, b)),
      (true, true, true) => (true, _meet(a, b)),
      (false, false, false) => (false, _meet(a, b)),
      (false, false, true) => (false, _without(a, b)),
      (false, true, false) => (false, _without(b, a)),
      (false, true, true) => (true, _union(a, b)),
    };
    return Lits(cofinite, out.values, out.sum);
  }

  static Lits _union(Lits a, Lits b) {
    final (large, small) = a.values.length >= b.values.length ? (a, b) : (b, a);
    return small.values.keys.fold(large, (out, v) => out.plus(v));
  }

  static Lits _meet(Lits a, Lits b) {
    final (large, small) = a.values.length >= b.values.length ? (a, b) : (b, a);
    return small.values.keys.where(large.values.containsKey).fold(none, (out, v) => out.plus(v));
  }

  /// The literals of `a` not in `b`.
  static Lits _without(Lits a, Lits b) {
    if (a.values.length <= b.values.length) {
      return a.values.keys.where((v) => !b.values.containsKey(v)).fold(none, (o, v) => o.plus(v));
    }
    return b.values.keys.fold(a, (out, v) => out.minus(v));
  }

  Lits not() => Lits(!cofinite, values, sum);

  @override
  int compareTo(Lits o) {
    var c = _cmpBool(cofinite, o.cofinite);
    if (c == 0) c = _lex(values.keys, o.values.keys, _byValue);
    if (c == 0) c = _cmpDigest(sum, o.sum);
    return c;
  }
}

/// The atoms of one name in a type: the bare atom, and those whose payload is in `payload`, a
/// type within the tuples and structs.
final class AtomPart implements Comparable<AtomPart> {
  final bool bare;
  final Type payload;

  const AtomPart(this.bare, this.payload);

  static final all = AtomPart(true, Type._payloads);
  static final none = AtomPart(false, Type.empty);

  AtomPart zip(AtomPart o, bool or) =>
      AtomPart(or ? bare || o.bare : bare && o.bare, payload._zip(o.payload, or));

  AtomPart not() => AtomPart(!bare, Type._payloads - payload);

  @override
  int compareTo(AtomPart o) {
    final c = _cmpBool(bare, o.bare);
    return c != 0 ? c : payload.compareTo(o.payload);
  }

  @override
  bool operator ==(Object other) => other is AtomPart && compareTo(other) == 0;

  @override
  int get hashCode => Object.hash(bare, payload);
}

/// Per atom name, its part; a name not listed has every payload when `cofinite`, else none.
/// The map is persistent, and `sum` is the wrapping sum of its entries' hashes.
final class Atoms implements Comparable<Atoms> {
  final bool cofinite;
  final PMap<String, AtomPart> names;
  final int sum;

  const Atoms(this.cofinite, this.names, this.sum);

  static const none = Atoms(false, PMap.empty(compareUtf8), 0);
  static const all = Atoms(true, PMap.empty(compareUtf8), 0);

  AtomPart get(String name) => names[name] ?? (cofinite ? AtomPart.all : AtomPart.none);

  static int _entry(String name, AtomPart p) =>
      mix(mix(_bytes(utf8.encode(name)), p.bare ? 1 : 0), p.payload.digest);

  /// The atoms with `name` given the part `p`, unlisted when `p` is what an unlisted name has.
  Atoms set(String name, AtomPart p) {
    var (names, sum) = (this.names, this.sum);
    if (names[name] case final old?) {
      names = names.remove(name);
      sum -= _entry(name, old);
    }
    if (p != (cofinite ? AtomPart.all : AtomPart.none)) {
      names = names.put(name, p);
      sum += _entry(name, p);
    }
    return Atoms(cofinite, names, sum);
  }

  /// The parts combined by `or` or `and`, in `O(s log l)` steps for the smaller map's `s`
  /// names and the larger's `l`. A name the smaller map does not list has every payload or
  /// none, and a part combined with all or none is itself, all or none: so the result is the
  /// larger map, or nothing, changed at the smaller map's names.
  Atoms zip(Atoms o, bool or) {
    final cofinite = or ? this.cofinite || o.cofinite : this.cofinite && o.cofinite;
    final (large, small) = names.length >= o.names.length ? (this, o) : (o, this);
    var out = or != small.cofinite
        ? Atoms(cofinite, large.names, large.sum)
        : Atoms(cofinite, none.names, 0);
    for (final (n, p) in small.names.entries) {
      out = out.set(n, large.get(n).zip(p, or));
    }
    return out;
  }

  Atoms not() {
    var out = Atoms(!cofinite, none.names, 0);
    for (final (n, p) in names.entries) {
      out = out.set(n, p.not());
    }
    return out;
  }

  @override
  int compareTo(Atoms o) {
    var c = _cmpBool(cofinite, o.cofinite);
    if (c == 0) {
      c = _lex(names.entries, o.names.entries, (x, y) {
        final c = compareUtf8(x.$1, y.$1);
        return c != 0 ? c : x.$2.compareTo(y.$2);
      });
    }
    if (c == 0) c = _cmpDigest(sum, o.sum);
    return c;
  }
}

/// Per length, the tuples of that length, as a part over tuple types of it; a length not listed
/// has every tuple when `rest`, else none. Tuples of two lengths are disjoint. The map is not
/// changed once made.
final class Tuples implements Comparable<Tuples> {
  final bool rest;
  final SplayTreeMap<int, Part<Components>> lens;

  Tuples(this.rest, this.lens);

  static final none = Tuples(false, SplayTreeMap());

  static Tuples literal(List<Type> items) =>
      Tuples(false, SplayTreeMap()..[items.length] = Part.literal(Components(items)));

  Part<Components> get(int len) => lens[len] ?? Leaf(rest);

  /// Drops the lengths whose part is what an unlisted length has.
  static Tuples _normal(bool rest, Map<int, Part<Components>> lens) => Tuples(
    rest,
    SplayTreeMap.of({
      for (final MapEntry(:key, :value) in lens.entries)
        if (value.leaf != rest) key: value,
    }),
  );

  Tuples zip(Tuples o, bool or) => _normal(or ? rest || o.rest : rest && o.rest, {
    for (final n in {...lens.keys, ...o.lens.keys}) n: get(n).zip(o.get(n), or),
  });

  Tuples not() => _normal(!rest, {for (final MapEntry(:key, :value) in lens.entries) key: ~value});

  /// Whether `f` holds of every tuple type in a part.
  bool atoms(bool Function(Components) f) => lens.values.every((b) => b.atoms(f));

  @override
  int compareTo(Tuples o) {
    final c = _cmpBool(rest, o.rest);
    if (c != 0) return c;
    return _lex(lens.entries, o.lens.entries, (x, y) {
      final c = x.key - y.key;
      return c != 0 ? c : x.value.compareTo(y.value);
    });
  }
}
