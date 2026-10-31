/// Names and the wildcard (step L1.2):
///
/// ```peg
/// Wildcard = '_' !XID_CONTINUE
/// Name     = (XID_START | '_' &XID_CONTINUE) XID_CONTINUE* "'"?
/// ```
///
/// `XID_CONTINUE` holds `_`, so `_x`, `x_1` and `__` are names, and a bare `_` is the
/// wildcard. A name must be of one script, as UTS #39 defines it at its "Highly Restrictive"
/// level: one script is shared by every character (a character of the Common or Inherited
/// script, such as a digit or `_`, shares every script), or every character is of one of three
/// writing systems, each of which Latin may join: Han with Hiragana and Katakana (Japanese), Han
/// with Bopomofo (Chinese), Han with Hangul (Korean). So `größe`, `面積`, `ユーザー名`, `user名`
/// are names, and `pаypal` with a Cyrillic `а` is rejected.
library;

import '../unicode.dart';
import '../unicode_tables.dart';
import 'text.dart';

/// The end of the name starting at byte `pos` of `text`, if one starts there.
int? name(Text text, int pos) {
  final first = text.charAt(pos);
  if (first < 0) return null;
  var end = pos + text.charLength(pos);
  final starts =
      isXidStart(first) || (first == 0x5f && end < text.length && isXidContinue(text.charAt(end)));
  if (!starts) return null;
  while (end < text.length) {
    final c = text.charAt(end);
    if (!isXidContinue(c)) return c == 0x27 ? end + 1 : end;
    end += text.charLength(end);
  }
  return end;
}

/// The end of the wildcard starting at byte `pos` of `text`, if one starts there.
int? wildcard(Text text, int pos) =>
    text.charAt(pos) == 0x5f && !(pos + 1 < text.length && isXidContinue(text.charAt(pos + 1)))
    ? pos + 1
    : null;

/// The writing systems a name may combine with Latin.
final _combined = [
  for (final set in [
    ['Latin', 'Han', 'Hiragana', 'Katakana'],
    ['Latin', 'Han', 'Bopomofo'],
    ['Latin', 'Han', 'Hangul'],
  ])
    set.map(scriptNames.indexOf).toSet(),
];

/// Whether the characters of `name` are of one script, in the sense of the library comment.
bool isSingleScript(String name) {
  // The scripts every character shares so far, null for every script.
  Set<int>? shared;
  for (final c in name.runes) {
    if (scriptExtension(c) case final ext?) {
      shared = shared == null ? ext : shared.intersection(ext);
    }
  }
  if (shared == null || shared.isNotEmpty) return true;
  return _combined.any(
    (set) => name.runes.every((c) => scriptExtension(c)?.any(set.contains) ?? true),
  );
}

/// The scripts of the characters of `name` other than Common and Inherited, in order of first
/// use, as `Latin, Cyrillic`.
String scriptsOf(String name) => {
  for (final c in name.runes)
    if (script(c) case final s when s != commonScript && s != inheritedScript) scriptNames[s],
}.join(', ');
