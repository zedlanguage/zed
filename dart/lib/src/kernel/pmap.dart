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

  /// The map without `key`; itself when it has no `key`.
  PMap<K, V> remove(K key) {
    final r = _remove(_root, key);
    return identical(r, _root) ? this : PMap._(r, compare);
  }

  _Node<K, V>? _remove(_Node<K, V>? n, K key) {
    if (n == null) return null;
    final c = compare(key, n.key);
    if (c < 0) {
      final l = _remove(n.left, key);
      return identical(l, n.left) ? n : _balance(n.key, n.value, l, n.right);
    }
    if (c > 0) {
      final r = _remove(n.right, key);
      return identical(r, n.right) ? n : _balance(n.key, n.value, n.left, r);
    }
    final (l, r) = (n.left, n.right);
    if (l == null) return r;
    if (r == null) return l;
    // The nearest key of the larger side takes the node's place.
    if (l.size > r.size) {
      final (k, v, rest) = _removeLast(l);
      return _balance(k, v, rest, r);
    }
    final (k, v, rest) = _removeFirst(r);
    return _balance(k, v, l, rest);
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

  /// The entries whose keys are at least `key`, in key order: O(log n) to the first, then O(1)
  /// a step on average.
  Iterable<(K, V)> from(K key) => _Entries(_root, (n) => compare(key, n.key) <= 0);

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

  /// The keys whose entries differ between this map and `other`, in key order: in one map only,
  /// or with values that are not the same object. A subtree the two trees share is skipped
  /// whole, so a map made from the other by d puts and removes is compared in O(d log² n).
  List<K> diff(PMap<K, V> other) {
    final out = <K>[];
    // Each stack holds what is still to be visited, the next on top: a subtree whole, or one
    // node's own entry when `whole` is false.
    final a = <(_Node<K, V>, bool)>[], b = <(_Node<K, V>, bool)>[];
    if (_root case final r?) a.add((r, true));
    if (other._root case final r?) b.add((r, true));
    void open(List<(_Node<K, V>, bool)> s) {
      final (n, _) = s.removeLast();
      if (n.right case final r?) s.add((r, true));
      s.add((n, false));
      if (n.left case final l?) s.add((l, true));
    }

    K least((_Node<K, V>, bool) t) {
      var (n, whole) = t;
      while (whole && n.left != null) {
        n = n.left!;
      }
      return n.key;
    }

    while (a.isNotEmpty && b.isNotEmpty) {
      final (ta, tb) = (a.last, b.last);
      if (ta.$2 && tb.$2 && identical(ta.$1, tb.$1)) {
        a.removeLast();
        b.removeLast();
        continue;
      }
      final c = compare(least(ta), least(tb));
      // The side whose next key comes first: a whole subtree is opened, an entry is in that
      // map alone.
      final first = c < 0 ? a : (c > 0 ? b : null);
      if (first != null) {
        if (first.last.$2) {
          open(first);
        } else {
          out.add(first.removeLast().$1.key);
        }
      } else if (!ta.$2 && !tb.$2) {
        if (!identical(ta.$1.value, tb.$1.value)) out.add(ta.$1.key);
        a.removeLast();
        b.removeLast();
      } else if (ta.$2 && (!tb.$2 || ta.$1.size >= tb.$1.size)) {
        open(a);
      } else {
        open(b);
      }
    }
    // One stack is empty; what the other holds comes after every key already added.
    final rest = a.isEmpty ? b : a;
    while (rest.isNotEmpty) {
      if (rest.last.$2) {
        open(rest);
      } else {
        out.add(rest.removeLast().$1.key);
      }
    }
    return out;
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

(K, V, _Node<K, V>?) _removeFirst<K, V>(_Node<K, V> n) {
  if (n.left == null) return (n.key, n.value, n.right);
  final (k, v, l) = _removeFirst(n.left!);
  return (k, v, _balance(n.key, n.value, l, n.right));
}

(K, V, _Node<K, V>?) _removeLast<K, V>(_Node<K, V> n) {
  if (n.right == null) return (n.key, n.value, n.left);
  final (k, v, r) = _removeLast(n.right!);
  return (k, v, _balance(n.key, n.value, n.left, r));
}

final class _Entries<K, V> extends Iterable<(K, V)> {
  final _Node<K, V>? root;

  /// Whether a node's key is in the range, when the range has a lower bound.
  final bool Function(_Node<K, V>)? inRange;

  _Entries(this.root, [this.inRange]);

  @override
  Iterator<(K, V)> get iterator => _InOrder(root, inRange);

  @override
  int get length => inRange == null ? _size(root) : super.length;
}

final class _InOrder<K, V> implements Iterator<(K, V)> {
  final _path = <_Node<K, V>>[];
  late (K, V) _current;

  _InOrder(_Node<K, V>? root, bool Function(_Node<K, V>)? inRange) {
    if (inRange == null) {
      _descend(root);
      return;
    }
    // The path to the first key in the range holds each node in it whose left subtree may be.
    var n = root;
    while (n != null) {
      if (inRange(n)) {
        _path.add(n);
        n = n.left;
      } else {
        n = n.right;
      }
    }
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
