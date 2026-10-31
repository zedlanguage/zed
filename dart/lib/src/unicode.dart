/// Unicode Normalization Form C (Unicode Standard Annex #15) and the canonical combining class,
/// over code points, from the tables of `unicode_tables.dart`.
library;

import 'unicode_tables.dart';

List<int> _numbers(String hex) => [
  for (final w in hex.split(' '))
    if (w.isNotEmpty) int.parse(w, radix: 16),
];

final _classRuns = _numbers(combiningClasses);

final Map<int, List<int>> _decompositions = () {
  final ns = _numbers(decompositions);
  final out = <int, List<int>>{};
  for (var i = 0; i < ns.length; i += 2 + ns[i + 1]) {
    out[ns[i]] = ns.sublist(i + 2, i + 2 + ns[i + 1]);
  }
  return out;
}();

final Map<int, int> _compositions = () {
  final ns = _numbers(compositions);
  return {for (var i = 0; i < ns.length; i += 3) _pair(ns[i], ns[i + 1]): ns[i + 2]};
}();

int _pair(int a, int b) => a << 21 | b;

// The Hangul syllables, composed and decomposed by arithmetic (Unicode section 3.12).
const _sBase = 0xac00, _lBase = 0x1100, _vBase = 0x1161, _tBase = 0x11a7;
const _lCount = 19, _vCount = 21, _tCount = 28, _nCount = _vCount * _tCount;
const _sCount = _lCount * _nCount;

/// The canonical combining class of code point `c`.
int combiningClass(int c) {
  // The last run starting at or before `c`.
  var (lo, hi) = (0, _classRuns.length ~/ 3);
  while (lo < hi) {
    final mid = (lo + hi) >> 1;
    if (_classRuns[3 * mid] <= c) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return lo > 0 && c <= _classRuns[3 * lo - 2] ? _classRuns[3 * lo - 1] : 0;
}

/// The NFC form of the code points `cs`.
List<int> nfc(List<int> cs) => _compose(_decompose(cs));

/// Whether the code points `cs` are in NFC.
bool isNfc(List<int> cs) {
  final n = nfc(cs);
  if (n.length != cs.length) return false;
  for (var i = 0; i < n.length; i++) {
    if (n[i] != cs[i]) return false;
  }
  return true;
}

/// The canonical decomposition, its marks in canonical order.
List<int> _decompose(List<int> cs) {
  final out = <int>[];
  for (final c in cs) {
    final s = c - _sBase;
    if (s >= 0 && s < _sCount) {
      out
        ..add(_lBase + s ~/ _nCount)
        ..add(_vBase + s % _nCount ~/ _tCount);
      if (s % _tCount != 0) out.add(_tBase + s % _tCount);
    } else {
      out.addAll(_decompositions[c] ?? [c]);
    }
  }
  // Each run of marks sorted by class, keeping their order within a class: the index breaks
  // ties, so any sort is stable, and a run of k marks costs O(k log k).
  for (var i = 0; i < out.length;) {
    if (combiningClass(out[i]) == 0) {
      i++;
      continue;
    }
    var j = i;
    while (j < out.length && combiningClass(out[j]) != 0) {
      j++;
    }
    final run = [for (var k = i; k < j; k++) (combiningClass(out[k]), k, out[k])]
      ..sort((a, b) => a.$1 != b.$1 ? a.$1 - b.$1 : a.$2 - b.$2);
    for (var k = i; k < j; k++) {
      out[k] = run[k - i].$3;
    }
    i = j;
  }
  return out;
}

/// The canonical composition of a decomposition in canonical order.
List<int> _compose(List<int> cs) {
  final out = <int>[];
  // The index in `out` of the last starter, or -1 before the first, and the class of the last
  // code point kept, 0 when that is the starter: a mark is blocked from the starter by a kept
  // mark of the same or a higher class.
  var starter = -1, last = 0;
  for (final c in cs) {
    final cc = combiningClass(c);
    if (starter >= 0 && (last == 0 || last < cc)) {
      final joined = _join(out[starter], c);
      if (joined != null) {
        out[starter] = joined;
        continue;
      }
    }
    if (cc == 0) starter = out.length;
    last = cc;
    out.add(c);
  }
  return out;
}

/// What the starter `a` and the code point `b` compose to, if anything.
int? _join(int a, int b) {
  final (l, v) = (a - _lBase, b - _vBase);
  if (l >= 0 && l < _lCount && v >= 0 && v < _vCount) {
    return _sBase + (l * _vCount + v) * _tCount;
  }
  final (s, t) = (a - _sBase, b - _tBase);
  if (s >= 0 && s < _sCount && s % _tCount == 0 && t > 0 && t < _tCount) return a + t;
  return _compositions[_pair(a, b)];
}
