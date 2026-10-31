/// Copy the `zed` fences of the spec's DESIGN.md and EXAMPLES.md into zed/fences/design.md
/// and zed/fences/examples.md, each under a header naming its source line and its layer (step
/// L1.7), and the syntactic grammar and the bracketing cases into zed/grammar (step L1.8).
///
/// CI does not read the spec repository, so the copies are the fixtures; run this by hand
/// after the spec changes. The layer is computed with the spec's grammar tools (the package
/// zed_grammar), as the M0.4 layer checker computes a corpus program's: the lowest ring at
/// which the fence parses (as a Unit, or else under the documentation notation), raised to
/// the layer of any defined word it uses (the table of sec:grammar) and to a `// layer Lk`
/// label.
///
/// Usage: sync.dart [--check] [SPEC_DIR]   (SPEC_DIR defaults to the checkout zed_grammar is
/// in; --check writes nothing and exits 1 if a copy is out of date)
library;

import 'dart:io';

import 'package:zed_grammar/check.dart';
import 'package:zed_grammar/fences.dart';
import 'package:zed_grammar/layer.dart';
import 'package:zed_grammar/ring.dart';
import 'package:zed_grammar/src/text.dart';

final _label = RegExp('^[$ws]*// layer L([0-9]+)(?![\\p{L}\\p{N}_])[^\\n]*\$', unicode: true);

/// The layer a `// layer Lk` line names. A fence's label may be on any line, since its first
/// line is usually its `// [d4]` header; the layer checker reads only a program's first line.
int? labelOf(String line) {
  final m = _label.firstMatch(line);
  return m == null ? null : int.parse(m[1]!);
}

/// The layer of a fence and how it was reached.
typedef FenceLayer = ({int layer, int ring, (int, String?) word, int? label, bool doc});

FenceLayer layerOf(String text, Spec spec, WordTable table) {
  final toks = lex(spec.lexRules, text.replaceAll('…', 'elided'));
  var (rules, start, doc) = (spec.synRules, 'Unit', false);
  if (parse(rules, spec.lexRules, toks, top, start).$1 == null) {
    (rules, start, doc) = (spec.allRules, 'DocFence', true);
  }
  final rng = [for (var k = 1; k <= top; k++) k]
      .firstWhere((k) => parse(rules, spec.lexRules, toks, k, start).$1 != null);
  final tree = Parser.syntactic(rules, top, toks).rule(start, 0, false)!.$2[0] as Node;
  final trees = <Tree>[(tree, toks)];
  addHoles(toks, spec.lexRules, spec.synRules, trees);
  final (hits, _) = analyse(trees, table);
  final (int, String?) word;
  if (hits.isEmpty) {
    word = (1, null);
  } else {
    final (k, w, _) = hits.reduce((a, b) => compareHits(a, b) >= 0 ? a : b);
    word = (k, w);
  }
  final most = text.split('\n').map((l) => labelOf(l) ?? 0).reduce((a, b) => a > b ? a : b);
  final label = most == 0 ? null : most;
  final lay = [rng, word.$1, label ?? 0].reduce((a, b) => a > b ? a : b);
  return (layer: lay, ring: rng, word: word, label: label, doc: doc);
}

String render(String path, Spec spec, WordTable table) {
  final name = path.split('/').last;
  final out = [
    "<!-- The `zed` fences of the spec's $name, copied by tools/bin/sync.dart: do not edit. -->",
  ];
  for (final (file: _, :line, :text) in fences(path)) {
    final f = layerOf(text, spec, table);
    final (k, w) = f.word;
    final why =
        'ring L${f.ring}, word ${w != null && w.isNotEmpty ? 'L$k ($w)' : 'none'}, '
        'label ${f.label != null ? 'L${f.label}' : 'none'}';
    out.addAll([
      '',
      '<!-- $name:$line layer L${f.layer}: $why${f.doc ? ', documentation notation' : ''} -->',
      '```zed',
      text,
      '```',
    ]);
  }
  return '${out.join('\n')}\n';
}

/// (destination, text) of every copy: the fences in zed/fences, and in zed/grammar the
/// syntactic grammar and the documentation notation of sec:grammar and the bracketing cases
/// (step L1.8).
List<(String, String)> copies(String here, Spec spec, WordTable table) {
  final grammar = '$here/../grammar';
  return [
    for (final doc in ['DESIGN.md', 'EXAMPLES.md'])
      ('$here/${doc.split('.')[0].toLowerCase()}.md', render('${spec.root}/$doc', spec, table)),
    ('$grammar/syntax.peg', '${spec.synText}\n'),
    ('$grammar/notation.peg', '${spec.docText}\n'),
    ('$grammar/cases.txt', readText('${spec.root}/tools/grammar/cases.txt')),
  ];
}

void main(List<String> argv) => runTool(() {
  final check = argv.contains('--check');
  final args = argv.where((a) => a != '--check').toList();
  final impl = File.fromUri(Platform.script).parent.parent.parent.path;
  final here = '$impl/zed/fences';
  final spec = args.isNotEmpty ? Spec(Directory(args[0]).absolute.path) : Spec.located();
  final table = WordTable.read(spec.design);
  var stale = 0;
  for (final (dest, want) in copies(here, spec, table)) {
    final file = File(dest);
    final have = file.existsSync() ? readText(dest) : null;
    if (have != want) {
      stale++;
      print('${dest.split('/').last} is ${check ? 'out of date' : 'written'}');
      if (!check) file.writeAsStringSync(want);
    }
  }
  return stale > 0 && check ? 1 : 0;
});
