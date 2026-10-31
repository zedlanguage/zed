// Families: finite keyed trees, the values the Tier-1 calculus computes over.
//
// A family maps each key of one level to a value; a value that is itself a family is the next
// level down. A *leaf* is a non-family value, and its *keypath* is the sequence of keys that
// reaches it (sec:keypaths). Two rules of (sec:values_morphisms) hold by construction: every
// keypath has exactly one writer, and an outer key over an empty level has no keypath, so it
// is dropped.
part of 'value.dart';

/// The keys from a family's top level down to one of its leaves.
typedef Keypath = List<Value>;

/// A finite family. No level of a family is empty except a whole family that has no entries.
/// Its entries sit in a persistent map: a family one entry larger than another shares all but
/// O(log n) of its nodes with it.
final class Family extends Value {
  final PMap<Value, Value> _map;

  const Family._(this._map);

  /// The family with no entries.
  const Family.empty() : _map = const PMap.empty(_cmp);

  /// A one-level family written out as a literal. A value that is an empty family drops its
  /// key. Throws [ArgumentError] when a key repeats, since a literal with two writers for one
  /// keypath is a mistake in the code that builds it.
  factory Family.of(Iterable<(Value, Value)> entries) {
    try {
      return Family.fromLeaves(entries.map((e) => ([e.$1], e.$2)));
    } on KernelError {
      throw ArgumentError('a family literal repeats a key');
    }
  }

  /// A set: each key maps to itself, as a set leaf does, so a membership lookup yields the
  /// element (sec:kernel, `discard`).
  factory Family.set(Iterable<Value> keys) {
    final sorted = [for (final k in keys) k.key()]..sort();
    final entries = <(Value, Value)>[];
    for (final k in sorted) {
      if (entries.isEmpty || entries.last.$1 != k) entries.add((k, k));
    }
    return Family._(PMap.sorted(entries, _cmp));
  }

  /// Builds a family from its leaves. A leaf whose value is a family contributes that
  /// family's leaves beneath it, sharing the family when nothing else is written there.
  /// Throws [CollisionError] when two leaves share a keypath, or one leaf's keypath is a
  /// prefix of another's, and [EmptyKeypathError] for a leaf with no keys.
  factory Family.fromLeaves(Iterable<(Keypath, Value)> leaves) {
    final root = SplayTreeMap<Value, _Node>();
    for (final (path, value) in leaves) {
      if (path.isEmpty) throw const EmptyKeypathError();
      if (value is Family) {
        if (value.isEmpty || _place(root, path, 0, value)) continue;
        for (final (sub, leaf) in value.leaves()) {
          final whole = [...path, ...sub];
          _insert(root, whole, leaf);
        }
      } else {
        _insert(root, path, value);
      }
    }
    return _freeze(root);
  }

  /// The leaves with their keypaths, in keypath order.
  List<(Keypath, Value)> leaves() {
    final out = <(Keypath, Value)>[];
    final prefix = <Value>[];
    void walk(Family f) {
      for (final (k, v) in f._map.entries) {
        prefix.add(k);
        if (v is Family) {
          walk(v);
        } else {
          out.add((List.of(prefix), v));
        }
        prefix.removeLast();
      }
    }

    walk(this);
    return out;
  }

  /// The value at key `k` of the top level.
  Value? operator [](Value k) => _map[k.isKey ? k : k.key()];

  /// The top-level entries, in key order.
  Iterable<(Value, Value)> get entries => _map.entries;

  /// The top-level keys, in order.
  Iterable<Value> get keys => _map.keys;

  /// The number of top-level entries.
  int get length => _map.length;

  bool get isEmpty => _map.isEmpty;

  /// The union of two families: the leaves of both, where a keypath both write holds the same
  /// leaf in each. Throws [CollisionError], at the first such keypath in order, when the
  /// leaves differ or one family has a leaf above the other's subtree. It costs O(m log n)
  /// for the smaller size m and the larger n: the larger family's entries are shared, not
  /// copied.
  Family union(Family other) => _unionAt(this, other, []);

  @override
  int get hashCode => Object.hashAll(_map.keys);

  @override
  String toString() {
    // A set, each leaf its own key (`k -> k`), is written by its members.
    final set = _map.isNotEmpty && _map.entries.every((e) => e.$1 == e.$2);
    return '{${_map.entries.map((e) => set ? '${e.$1}' : '${e.$1} -> ${e.$2}').join(', ')}}';
  }
}

/// A level being built. A leaf may hold a whole family, shared, until a leaf beneath it is
/// added, when its top level is expanded into an inner node.
sealed class _Node {}

final class _Leaf extends _Node {
  final Value value;

  _Leaf(this.value);
}

final class _Inner extends _Node {
  final SplayTreeMap<Value, _Node> level;

  _Inner(this.level);
}

/// The inner node at `key` of `level`, made or expanded from a leaf holding a family; null
/// when a leaf that is not a family is there.
SplayTreeMap<Value, _Node>? _descend(SplayTreeMap<Value, _Node> level, Value key) {
  final node = level[key];
  switch (node) {
    case null:
      final inner = SplayTreeMap<Value, _Node>();
      level[key] = _Inner(inner);
      return inner;
    case _Inner(:final level):
      return level;
    case _Leaf(value: Family f):
      final inner = SplayTreeMap<Value, _Node>();
      for (final (k, v) in f.entries) {
        inner[k] = _Leaf(v);
      }
      level[key] = _Inner(inner);
      return inner;
    case _Leaf():
      return null;
  }
}

/// Puts the nonempty family `sub` at `path` from index `i` as one shared leaf, and returns
/// true, when no leaf is at that path and none above it. Otherwise returns false, having added
/// only inner nodes that the leaves of `sub` would add.
bool _place(SplayTreeMap<Value, _Node> level, Keypath path, int i, Family sub) {
  for (; ; i++) {
    final key = path[i].key();
    if (i == path.length - 1) {
      if (level.containsKey(key)) return false;
      level[key] = _Leaf(sub);
      return true;
    }
    final inner = _descend(level, key);
    if (inner == null) return false;
    level = inner;
  }
}

void _insert(SplayTreeMap<Value, _Node> level, Keypath path, Value leaf) {
  for (var i = 0; ; i++) {
    final key = path[i].key();
    if (i == path.length - 1) {
      if (level.containsKey(key)) throw CollisionError(path);
      level[key] = _Leaf(leaf);
      return;
    }
    final inner = _descend(level, key);
    if (inner == null) throw CollisionError(path);
    level = inner;
  }
}

Family _freeze(SplayTreeMap<Value, _Node> level) => Family._(
  PMap.sorted([
    for (final MapEntry(:key, :value) in level.entries)
      (
        key,
        switch (value) {
          _Leaf(:final value) => value,
          _Inner(:final level) => _freeze(level),
        },
      ),
  ], _cmp),
);

/// The union of `a` and `b`, the levels beneath `prefix`. A collision is reported as building
/// `a`'s leaves and then `b`'s would report it: at `b`'s leaf, or, where `a` has a leaf above
/// a subtree of `b`, at the subtree's first leaf.
Family _unionAt(Family a, Family b, Keypath prefix) {
  final smallIsB = a.length >= b.length;
  final (big, small) = smallIsB ? (a, b) : (b, a);
  var out = big._map;
  for (final (k, s) in small._map.entries) {
    final g = big._map[k];
    if (g == null) {
      out = out.put(k, s);
      continue;
    }
    final (x, y) = smallIsB ? (g, s) : (s, g);
    prefix.add(k);
    final Value merged;
    switch ((x, y)) {
      case (Family x, Family y):
        merged = _unionAt(x, y, prefix);
      case (Family(), _):
        throw CollisionError(List.of(prefix));
      case (_, Family y):
        var sub = y;
        while (true) {
          final (k, v) = sub._map.first;
          prefix.add(k);
          if (v is! Family) throw CollisionError(List.of(prefix));
          sub = v;
        }
      case _ when x == y:
        merged = g;
      default:
        throw CollisionError(List.of(prefix));
    }
    prefix.removeLast();
    // An entry the union leaves as it was stays the same node, so a union that adds nothing
    // returns the larger family itself.
    if (!identical(merged, g)) out = out.put(k, merged);
  }
  return identical(out, big._map) ? big : Family._(out);
}
