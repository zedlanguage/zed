/// The M0.8 audit: which grammar alternatives and which defined words a program needs.
///
/// An alternative is needed when the program stops parsing, or parses to a different tree,
/// with that alternative removed from the grammar. Every alternative is tried this way, so the
/// list is exact for the parser of DESIGN.md sec:grammar rather than a guess from token shapes.
/// The defined words come from the spec's layer checker (`layer.dart -v`).
///
/// Usage: audit.dart PROGRAM.zed [--checklist ZED0.md]
///   The grammar is the spec's, through the package zed_grammar. The audit runs by hand, like
///   the corpus layer check (LEDGER.md), since CI does not read the spec repository.
/// Prints one line per needed alternative, `L<layer> <rule>#<index> <grammar text>`, then the
/// words, then the highest layer met. With --checklist, also checks that the checklist names
/// every needed alternative (as `Rule#i`) and every word (in backticks), and exits 1 if not.
library;

import 'dart:io';

import 'package:zed_grammar/check.dart';
import 'package:zed_grammar/layer.dart';
import 'package:zed_grammar/ring.dart';
import 'package:zed_grammar/src/text.dart';

void main(List<String> argv) => runTool(() => _audit(argv));

int _audit(List<String> argv) {
  final main = File(argv[0]).absolute.path;
  final checklist = argv.length > 2 && argv[1] == '--checklist' ? argv[2] : null;
  final spec = Spec.located();
  final (lexRules, synRules) = (spec.lexRules, spec.synRules);
  final lines = [
    for (final l in spec.synText.split('\n'))
      if (strip(l).isNotEmpty) l,
  ];
  final units = programUnits(main);
  final toks = [for (final u in units) lex(lexRules, readText(u).replaceAll('…', 'elided'))];
  final full = [for (final t in toks) parse(synRules, lexRules, t, top, 'Unit').$1];
  if (full.any((t) => t == null)) throw ToolExit('the program does not parse');

  final needed = <(int, String, int)>[];
  for (final MapEntry(key: rule, value: alts) in synRules.entries) {
    for (var i = 0; i < alts.length; i++) {
      final trimmed = {
        ...synRules,
        rule: [...alts.sublist(0, i), ...alts.sublist(i + 1)],
      };
      for (var u = 0; u < toks.length; u++) {
        final t = parse(trimmed, lexRules, toks[u], top, 'Unit').$1;
        if (t == null || !sameTree(t, full[u]!)) {
          needed.add((alts[i].layer, rule, i));
          break;
        }
      }
    }
  }

  // The grammar text of alternative i of a rule: the rule's i-th line, as check.dart reads it.
  final text = <(String?, int), String>{};
  String? cur;
  var n = 0;
  for (final l in lines) {
    final m = grammarLine.firstMatch(l);
    if (m == null) throw ToolExit('grammar line: ${repr(l)}');
    if (m.namedGroup('rule') case final r?) {
      (cur, n) = (r, 0);
    } else {
      n++;
    }
    text[(cur, n)] = m.namedGroup('body')!;
  }
  needed.sort((a, b) {
    if (a.$1 != b.$1) return a.$1 - b.$1;
    final c = compareStrings(a.$2, b.$2);
    return c != 0 ? c : a.$3 - b.$3;
  });
  for (final (lay, rule, i) in needed) {
    print('L$lay $rule#$i ${prefix(text[(rule, i)] ?? '', 110)}');
  }
  // The layer checker's report, as `layer.dart -v PROGRAM` prints it on stdout.
  final buf = StringBuffer();
  try {
    LayerChecker(spec).run(['-v', main], buf);
  } on ToolExit {
    // layer.dart would have written this to stderr, which the audit does not show
  }
  final words = buf.toString();
  print(words);
  print('highest grammar layer: L${needed.map((x) => x.$1).reduce((a, b) => a > b ? a : b)}');

  if (checklist == null) return 0;
  final listed = readText(checklist);
  final found = [
    for (final (_, r, i) in needed) '$r#$i',
    for (final l in words.split('\n'))
      if (l.startsWith('      L')) strip(l).split(RegExp('[$ws]+'))[1],
  ];
  final missing = [
    for (final w in found)
      if (!listed.contains('`$w`')) w,
  ];
  print('checklist: ${found.length} needed, ${missing.length} missing ${missing.join(' ')}');
  return missing.isEmpty ? 0 : 1;
}
