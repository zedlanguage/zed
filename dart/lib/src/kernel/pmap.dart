/// A persistent ordered map: a weight-balanced binary tree (Adams), whose updates return a new
/// map sharing all but O(log n) nodes with the old one.
library;

/// A persistent map from `K` to `V`, ordered by `compare`.
final class PMap<K, V> {
  final _Node<K, V>? _root;

  /// The order on keys.
  final int Function(K, K) compare;

  const PMap._(this._root, this.compare);

  /// The empty map ordered by `compare`.
  const PMap.empty(this.compare) : _root = null;

  /// The map of `entries`, which are sorted by `compare` with no key twice; O(n).
  factory PMap.sorted(List<(K, V)> entries, int Function(K, K) compare) {
    _Node<K, V>? build(int lo, int hi) {
      if (lo >= hi) return null;
      final mid = (lo + hi) >> 1;
      final (k, v) = entries[mid];
      return _Node(k, v, build(lo, mid), build(mid + 1, hi));
    }

    return PMap._(build(0, entries.length), compare);
  }

  /// The number of entries.
  int get length => _size(_root);

  bool get isEmpty => _root == null;

  bool get isNotEmpty => _root != null;

  /// The value at `key`, or null.
  V? operator [](K key) {
    var n = _root;
    while (n != null) {
      final c = compare(key, n.key);
      if (c == 0) return n.value;
      n = c < 0 ? n.left : n.right;
    }
    return null;
  }

  bool containsKey(K key) {
    var n = _root;
    while (n != null) {
      final c = compare(key, n.key);
      if (c == 0) return true;
      n = c < 0 ? n.left : n.right;
    }
    return false;
  }

  /// The map with `key` bound to `value`, replacing any earlier value.
  PMap<K, V> put(K key, V value) => PMap._(_put(_root, key, value), compare);

  _Node<K, V> _put(_Node<K, V>? n, K key, V value) {
    if (n == null) return _Node(key, value, null, null);
    final c = compare(key, n.key);
    if (c == 0) return _Node(key, value, n.left, n.right);
    if (c < 0) return _balance(n.key, n.value, _put(n.left, key, value), n.right);
    return _balance(n.key, n.value, n.left, _put(n.right, key, value));
  }

  /// The entry with the least key; the map must not be empty.
  (K, V) get first {
    var n = _root!;
    while (n.left != null) {
      n = n.left!;
    }
    return (n.key, n.value);
  }

  /// The entries in key order.
  Iterable<(K, V)> get entries => _Entries(_root);

  Iterable<K> get keys => entries.map((e) => e.$1);

  Iterable<V> get values => entries.map((e) => e.$2);

  /// Whether `other` has the same entries, values compared by `==`; O(1) for the same tree.
  bool sameAs(PMap<K, V> other) {
    if (identical(_root, other._root)) return true;
    if (length != other.length) return false;
    final a = entries.iterator, b = other.entries.iterator;
    while (a.moveNext() && b.moveNext()) {
      if (compare(a.current.$1, b.current.$1) != 0 || a.current.$2 != b.current.$2) return false;
    }
    return true;
  }
}

final class _Node<K, V> {
  final K key;
  final V value;
  final _Node<K, V>? left, right;
  final int size;

  _Node(this.key, this.value, this.left, this.right) : size = _size(left) + _size(right) + 1;
}

int _size(_Node<Object?, Object?>? n) => n?.size ?? 0;

// The balance parameters proved correct by Hirai and Yamamoto (2011).
const _delta = 3, _ratio = 2;

_Node<K, V> _balance<K, V>(K k, V v, _Node<K, V>? l, _Node<K, V>? r) {
  final ln = _size(l), rn = _size(r);
  if (ln + rn <= 1) return _Node(k, v, l, r);
  if (rn > _delta * ln) {
    final rl = r!.left, rr = r.right;
    if (_size(rl) < _ratio * _size(rr)) {
      return _Node(r.key, r.value, _Node(k, v, l, rl), rr);
    }
    return _Node(rl!.key, rl.value, _Node(k, v, l, rl.left), _Node(r.key, r.value, rl.right, rr));
  }
  if (ln > _delta * rn) {
    final ll = l!.left, lr = l.right;
    if (_size(lr) < _ratio * _size(ll)) {
      return _Node(l.key, l.value, ll, _Node(k, v, lr, r));
    }
    return _Node(lr!.key, lr.value, _Node(l.key, l.value, ll, lr.left), _Node(k, v, lr.right, r));
  }
  return _Node(k, v, l, r);
}

final class _Entries<K, V> extends Iterable<(K, V)> {
  final _Node<K, V>? root;

  _Entries(this.root);

  @override
  Iterator<(K, V)> get iterator => _InOrder(root);

  @override
  int get length => _size(root);
}

final class _InOrder<K, V> implements Iterator<(K, V)> {
  final _path = <_Node<K, V>>[];
  late (K, V) _current;

  _InOrder(_Node<K, V>? root) {
    _descend(root);
  }

  void _descend(_Node<K, V>? n) {
    while (n != null) {
      _path.add(n);
      n = n.left;
    }
  }

  @override
  (K, V) get current => _current;

  @override
  bool moveNext() {
    if (_path.isEmpty) return false;
    final n = _path.removeLast();
    _current = (n.key, n.value);
    _descend(n.right);
    return true;
  }
}
