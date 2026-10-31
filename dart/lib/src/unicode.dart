/// Unicode Normalization Form C (Unicode Standard Annex #15), the canonical combining class,
/// the identifier properties of Unicode Standard Annex #31, and the scripts of Unicode Standard
/// Annex #24, over code points, from the tables of `unicode_tables.dart`.
library;

import 'unicode_tables.dart';

List<int> _numbers(String hex) => [
  for (final w in hex.split(' '))
    if (w.isNotEmpty) int.parse(w, radix: 16),
];

final _classRuns = _numbers(combiningClasses);
final _xidStart = _numbers(xidStart);
final _xidContinue = _numbers(xidContinue);
final _scripts = _numbers(scripts);
final _extensions = _numbers(scriptExtensions);
final _escaped = _numbers(escapedInQuotes);

/// The value of the run of `runs` (first, last, value) holding `c`, or `none`.
int _lookup(List<int> runs, int c, int none) {
  // The last run starting at or before `c`.
  var (lo, hi) = (0, runs.length ~/ 3);
  while (lo < hi) {
    final mid = (lo + hi) >> 1;
    if (runs[3 * mid] <= c) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return lo > 0 && c <= runs[3 * lo - 2] ? runs[3 * lo - 1] : none;
}

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
int combiningClass(int c) => _lookup(_classRuns, c, 0);

/// Whether code point `c` has the XID_Start property.
bool isXidStart(int c) => _lookup(_xidStart, c, 0) == 1;

/// Whether code point `c` has the XID_Continue property.
bool isXidContinue(int c) => _lookup(_xidContinue, c, 0) == 1;

/// Whether a quoted character shows code point `c` as an escape: a control, private use,
/// format or unassigned character, white space, a grapheme extender, or a default-ignorable
/// character.
bool isEscapedInQuotes(int c) => _lookup(_escaped, c, 0) == 1;

/// The script Unknown.
final unknownScript = scriptNames.indexOf('Unknown');

/// The script Common.
final commonScript = scriptNames.indexOf('Common');

/// The script Inherited.
final inheritedScript = scriptNames.indexOf('Inherited');

/// The script of code point `c`, as its index in `scriptNames`.
int script(int c) => _lookup(_scripts, c, unknownScript);

/// The script extensions of code point `c`, as indexes in `scriptNames`, or null for every
/// script: the extension of a character of the Common or Inherited script, which shares every
/// script. A character of the script Unknown has none.
Set<int>? scriptExtension(int c) {
  final k = _lookup(_extensions, c, -1);
  if (k >= 0) return scriptExtensionSets[k].toSet();
  final s = script(c);
  if (s == commonScript || s == inheritedScript) return null;
  return s == unknownScript ? {} : {s};
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

/// `text` between two `quote` characters, written so that every character can be read: `\`,
/// the quote, `\n`, `\t`, `\r` and `\0` escaped with a `\`, and each character
/// `isEscapedInQuotes` holds as `\u{…}` in lowercase hexadecimal.
String quoted(String text, String quote) {
  final out = StringBuffer(quote);
  for (final c in text.runes) {
    out.write(switch (c) {
      0x5c => r'\\',
      0x0a => r'\n',
      0x09 => r'\t',
      0x0d => r'\r',
      0x00 => r'\0',
      _ when String.fromCharCode(c) == quote => '\\$quote',
      >= 0x20 && <= 0x7e || 0xff9e || 0xff9f => String.fromCharCode(c),
      _ when isEscapedInQuotes(c) => '\\u{${c.toRadixString(16)}}',
      _ => String.fromCharCode(c),
    });
  }
  return (out..write(quote)).toString();
}
