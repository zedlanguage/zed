/// Unicode Normalization Form C (Unicode Standard Annex #15), the canonical combining class,
/// the identifier properties of Unicode Standard Annex #31, the scripts of Unicode Standard
/// Annex #24, and the full case mappings, over code points, from ICU4X.
library;

import 'package:icu4x/icu4x.dart';

/// The Unicode version of the data, the version of the conformance test the tests run.
const unicodeVersion = '18.0.0';

final _combining = CanonicalCombiningClassMap();
final _xidStart = CodePointSetData.xidStart();
final _xidContinue = CodePointSetData.xidContinue();
final _whiteSpace = CodePointSetData.whiteSpace();
final _graphemeExtend = CodePointSetData.graphemeExtend();
final _defaultIgnorable = CodePointSetData.defaultIgnorableCodePoint();
final _category = CodePointMapData8.generalCategory();
final _scripts = CodePointMapData16.script();
final _extensions = ScriptWithExtensions().asBorrowed;
final _nfc = ComposingNormalizer.nfc();
final _caseMapper = CaseMapper();
final _root = Locale.fromString('und');

/// The general categories whose characters a quoted character shows as an escape.
final _escapedCategories = {
  for (final g in [
    GeneralCategory.control,
    GeneralCategory.privateUse,
    GeneralCategory.format,
    GeneralCategory.unassigned,
  ])
    g.toIntegerValue(),
};

/// Each script by its integer value, which `Script.fromIntegerValue` finds by a scan.
final _byValue = {for (final s in Script.values) s.toIntegerValue(): s};

/// The canonical combining class of code point `c`.
int combiningClass(int c) => _combining[c];

/// Whether code point `c` has the XID_Start property.
bool isXidStart(int c) => _xidStart.contains(c);

/// Whether code point `c` has the XID_Continue property.
bool isXidContinue(int c) => _xidContinue.contains(c);

/// Whether a quoted character shows code point `c` as an escape: a control, private use,
/// format or unassigned character, white space, a grapheme extender, or a default-ignorable
/// character.
bool isEscapedInQuotes(int c) =>
    _escapedCategories.contains(_category[c]) ||
    _whiteSpace.contains(c) ||
    _graphemeExtend.contains(c) ||
    _defaultIgnorable.contains(c);

/// The script of code point `c`.
Script script(int c) => _byValue[_scripts[c]]!;

/// The script extensions of code point `c`, or null for every script: the extension of a
/// character of the Common or Inherited script, which shares every script. A character of the
/// script Unknown has none.
Set<Script>? scriptExtension(int c) {
  // ICU4X gives a character with no extensions listed the set of its script alone.
  final set = _extensions.getScriptExtensionsVal(c);
  if (set.count == 1 && (set.contains(Script.common) || set.contains(Script.inherited))) {
    return null;
  }
  // `scriptAt` scans the list of scripts, whose length is fixed by the data.
  return {for (var i = 0; i < set.count; i++) set.scriptAt(i)!}..remove(Script.unknown);
}

/// The NFC form of the code points `cs`.
List<int> nfc(List<int> cs) => _nfc.normalize(String.fromCharCodes(cs)).runes.toList();

/// Whether the code points `cs` are in NFC.
bool isNfc(List<int> cs) => _nfc.isNormalized(String.fromCharCodes(cs));

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

/// The full lowercase mapping of `s` (the Unicode Standard, section 3.13, "Default Case
/// Conversion"): each character's full mapping, except that a capital sigma becomes the final
/// `ς` when it ends a word (Final_Sigma: a cased character comes before it and none after it,
/// case-ignorable characters between not counting), and `σ` otherwise.
String toLower(String s) => _keepingBom(s, (t) => _caseMapper.lowercase(t, _root));

/// The full uppercase mapping of `s`: each character's full mapping.
String toUpper(String s) => _keepingBom(s, (t) => _caseMapper.uppercase(t, _root));

/// `map(s)`, keeping the U+FEFF characters `s` starts with. ICU4X returns the mapping as
/// UTF-8, which its Dart binding decodes with `utf8.decode`, and that drops a leading U+FEFF
/// as a byte order mark. U+FEFF has no case mapping and is case-ignorable, so mapping the rest
/// and putting them back gives the mapping of `s`.
String _keepingBom(String s, String Function(String) map) {
  var i = 0;
  while (i < s.length && s.codeUnitAt(i) == 0xfeff) {
    i++;
  }
  return s.substring(0, i) + map(s.substring(i));
}
