/// Writes dart/lib/src/unicode_tables.dart, the Unicode tables the Dart source loader and lexer
/// read (steps L1.1 and L1.2), from a copy of the Unicode Character Database: each code point's
/// canonical combining class, its full canonical decomposition, the pairs that canonical
/// composition joins, the XID_Start and XID_Continue properties, each code point's script and
/// script extensions, the code points a quoted character shows as an escape, and the full case
/// mappings with the Cased and Case_Ignorable properties that the final sigma reads.
///
/// Usage: dart tools/bin/unicode_tables.dart [UCD directory, default /usr/share/unicode/ucd]
library;

import 'dart:io';

void main(List<String> args) {
  final ucd = args.firstOrNull ?? '/usr/share/unicode/ucd';
  List<String> lines(String file) => File('$ucd/$file').readAsLinesSync();
  final version = RegExp(r'NormalizationTest-([\d.]+)\.txt')
      .firstMatch(lines('NormalizationTest.txt').first)![1]!;

  final ccc = <int, int>{};
  final mapping = <int, List<int>>{};
  final lower = <int, List<int>>{}, upper = <int, List<int>>{};
  for (final line in lines('UnicodeData.txt')) {
    final f = line.split(';');
    final cp = int.parse(f[0], radix: 16);
    if (int.parse(f[3]) != 0) ccc[cp] = int.parse(f[3]);
    if (f[5].isNotEmpty && !f[5].startsWith('<')) {
      mapping[cp] = [for (final x in f[5].split(' ')) int.parse(x, radix: 16)];
    }
    if (f[12].isNotEmpty) upper[cp] = [int.parse(f[12], radix: 16)];
    if (f[13].isNotEmpty) lower[cp] = [int.parse(f[13], radix: 16)];
  }
  // The full case mappings: SpecialCasing's mappings that hold in every context and every
  // language, else the simple ones of UnicodeData. Of the rest, the final sigma holds in every
  // language, and the code reading the tables applies it.
  for (final line in lines('SpecialCasing.txt')) {
    final f = [for (final x in line.split('#')[0].split(';')) x.trim()];
    if (f.length < 5 || f[4].isNotEmpty) continue;
    final cp = int.parse(f[0], radix: 16);
    List<int> read(String m) => [for (final x in m.split(' ')) int.parse(x, radix: 16)];
    lower[cp] = read(f[1]);
    upper[cp] = read(f[3]);
  }
  for (final m in [lower, upper]) {
    m.removeWhere((cp, to) => to.length == 1 && to[0] == cp);
  }

  /// The code points of each value of a file of `first..last ; value` lines.
  Map<int, String> ranged(String file, [bool Function(String) keep = _all]) {
    final out = <int, String>{};
    for (final line in lines(file)) {
      final body = line.split('#')[0].split(';');
      if (body.length < 2) continue;
      final range = body[0].trim().split('..');
      final v = body[1].trim();
      if (!keep(v)) continue;
      final lo = int.parse(range[0], radix: 16);
      final hi = int.parse(range.last, radix: 16);
      for (var cp = lo; cp <= hi; cp++) {
        out[cp] = v;
      }
    }
    return out;
  }

  final excluded = ranged(
    'DerivedNormalizationProps.txt',
    (v) => v == 'Full_Composition_Exclusion',
  ).keys.toSet();

  List<int> full(int cp) => [
    for (final x in mapping[cp]!) ...(mapping.containsKey(x) ? full(x) : [x]),
  ];

  final decomposed = mapping.keys.toList()..sort();
  final decomp = [
    for (final cp in decomposed) ...[cp, full(cp).length, ...full(cp)],
  ];
  List<int> flat(Map<int, List<int>> m) => [
    for (final cp in m.keys.toList()..sort()) ...[cp, m[cp]!.length, ...m[cp]!],
  ];
  final pairs = [
    for (final cp in decomposed)
      if (!excluded.contains(cp) && mapping[cp]!.length == 2) ...[...mapping[cp]!, cp],
  ];

  // A code point has many properties, so each property is read on its own.
  Set<int> derived(String p) => ranged('DerivedCoreProperties.txt', (v) => v == p).keys.toSet();
  final xidStart = derived('XID_Start');
  final xidContinue = derived('XID_Continue');
  // The characters a quoted character shows as `\u{…}`: a control, private use, format or
  // unassigned character, white space, a grapheme extender, or a default-ignorable character.
  final escaped = {
    for (final MapEntry(:key, :value) in ranged('extracted/DerivedGeneralCategory.txt').entries)
      if (const {'Cc', 'Co', 'Cf', 'Cn'}.contains(value)) key,
    ...ranged('PropList.txt', (v) => v == 'White_Space').keys,
    ...derived('Grapheme_Extend'),
    ...derived('Default_Ignorable_Code_Point'),
  };
  final long = <String, String>{};
  for (final line in lines('PropertyValueAliases.txt')) {
    final f = [for (final x in line.split('#')[0].split(';')) x.trim()];
    if (f.length >= 3 && f[0] == 'sc') long[f[1]] = f[2];
  }
  final scriptNames = long.values.toSet().toList()..sort();
  final index = {for (final (i, n) in scriptNames.indexed) n: i};
  final script = ranged('Scripts.txt').map((cp, v) => MapEntry(cp, index[v]!));
  final extensions = ranged('ScriptExtensions.txt');
  final extSets = extensions.values.toSet().toList()..sort();
  final extIndex = {for (final (i, v) in extSets.indexed) v: i};
  final ext = extensions.map((cp, v) => MapEntry(cp, extIndex[v]!));
  final classRuns = _runs(ccc);

  final out =
      '// Written by tools/bin/unicode_tables.dart from the Unicode $version character database. '
      'Do\n// not edit; run the tool again for a new version of Unicode.\n\n'
      '/// The version of Unicode the tables are of.\n'
      "const unicodeVersion = '$version';\n\n"
      '${[
        _literal('combiningClasses', 'Runs of code points with one nonzero canonical combining '
            'class, in hexadecimal: first, last, class.', classRuns),
        _literal('decompositions', 'Each code point with a canonical decomposition, the length '
            'of its full decomposition, and that decomposition, in hexadecimal.', decomp),
        _literal('compositions', 'The pairs canonical composition joins, and what each pair '
            'becomes, in hexadecimal.', pairs),
        _literal('xidStart', 'Runs of code points with the XID_Start property, in hexadecimal: '
            'first, last, 1.', _runs({for (final cp in xidStart) cp: 1})),
        _literal('xidContinue', 'Runs of code points with the XID_Continue property, in '
            'hexadecimal: first, last, 1.', _runs({for (final cp in xidContinue) cp: 1})),
        _literal('scripts', 'Runs of code points of one script, in hexadecimal: first, last, '
            'and the index of the script in `scriptNames`; a code point in no run is of the '
            'script Unknown.', _runs(script)),
        _literal('scriptExtensions', 'Runs of code points with one Script_Extensions value, in '
            'hexadecimal: first, last, and the index of the value in `scriptExtensionSets`; a '
            'code point in no run has its script as its only extension.', _runs(ext)),
        _literal('escapedInQuotes', 'Runs of code points a quoted character shows as an '
            'escape, in hexadecimal: first, last, 1.', _runs({for (final cp in escaped) cp: 1})),
        _literal('lowercaseMappings', 'Each code point whose full lowercase mapping is not '
            'itself, the length of the mapping, and the mapping, in hexadecimal.', flat(lower)),
        _literal('uppercaseMappings', 'Each code point whose full uppercase mapping is not '
            'itself, the length of the mapping, and the mapping, in hexadecimal.', flat(upper)),
        _literal('cased', 'Runs of code points with the Cased property, in hexadecimal: '
            'first, last, 1.', _runs({for (final cp in derived('Cased')) cp: 1})),
        _literal('caseIgnorable', 'Runs of code points with the Case_Ignorable property, in '
            'hexadecimal: first, last, 1.', _runs({for (final cp in derived('Case_Ignorable')) cp: 1})),
        '/// The names of the scripts.\nconst scriptNames = [\n'
            '${scriptNames.map((n) => "  '$n',\n").join()}];\n',
        '/// The values of the Script_Extensions property, each a list of indexes in '
            '`scriptNames`.\nconst scriptExtensionSets = [\n'
            '${extSets.map((v) => '  [${v.split(' ').map((a) => index[long[a]]).join(', ')}],\n').join()}'
            '];\n',
      ].join('\n')}';
  final path = File.fromUri(Platform.script).parent.parent.parent.path;
  File('$path/dart/lib/src/unicode_tables.dart').writeAsStringSync(out);
  print(
    'Unicode $version: ${classRuns.length ~/ 3} class runs, ${mapping.length} decompositions, '
    '${pairs.length ~/ 3} compositions, ${scriptNames.length} scripts, '
    '${extSets.length} extension sets, ${lower.length} lowercase and ${upper.length} '
    'uppercase mappings',
  );
}

bool _all(String _) => true;

/// Runs of consecutive code points with one value, flattened: first, last, value.
List<int> _runs(Map<int, int> values) {
  final out = <int>[];
  for (final cp in values.keys.toList()..sort()) {
    final n = out.length;
    if (n > 0 && out[n - 2] == cp - 1 && out[n - 1] == values[cp]) {
      out[n - 2] = cp;
    } else {
      out.addAll([cp, cp, values[cp]!]);
    }
  }
  return out;
}

/// A constant `name` holding `numbers` in hexadecimal, as one string literal per line of at
/// most 90 characters, after the doc comment `doc` wrapped at 96.
String _literal(String name, String doc, List<int> numbers) {
  final lines = <String>[];
  var cur = '';
  for (final w in numbers.map((n) => n.toRadixString(16))) {
    if (cur.length + w.length + 1 > 90) {
      lines.add(cur);
      cur = '';
    }
    cur += '$w ';
  }
  lines.add(cur);
  final docLines = <String>[];
  for (final word in doc.split(' ')) {
    if (docLines.isNotEmpty && docLines.last.length + 1 + word.length <= 96) {
      docLines.last += ' $word';
    } else {
      docLines.add(word);
    }
  }
  return '${docLines.map((l) => '/// $l').join('\n')}\nconst $name =\n'
      "${lines.map((l) => "    '$l'").join('\n')};\n";
}
