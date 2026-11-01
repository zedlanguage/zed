/// Step L1.8: the parser runs the grammar of sec:grammar, copied into `zed/grammar/`, and its
/// trees are the trees of the spec's bracketing cases, `tools/grammar/cases.txt`, copied into
/// `zed/grammar/cases.txt`: each line is `Rule[@ring] ::: text ::: tree`, and a tree of `ERROR`
/// means the text must not parse.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';
import 'package:zed/src/parse/peg.dart';

import '../../support/support.dart';
import '../../support/trees.dart';

final grammarDir = Directory('${packageDir.parent.path}/zed/grammar');

/// The tree printed for `text` parsed as `start` at `ring`, or `ERROR` and why.
String show(String text, String start, int ring) {
  try {
    final tokens = lex(text);
    return sx(text, tokens, parse(text, tokens, start, ring));
  } on LexError catch (e) {
    return 'ERROR lexing: $e';
  } on ParseError catch (e) {
    return 'ERROR $e';
  }
}

void main() {
  test('every bracketing case gives its tree', () {
    final cases = File('${grammarDir.path}/cases.txt').readAsLinesSync();
    var n = 0;
    final wrong = <String>[];
    for (final line in cases) {
      if (line.trim().isEmpty || line.startsWith('#')) continue;
      final [start, text, want] = [for (final p in line.split(' ::: ')) p.trim()];
      final (rule, ring) = switch (start.split('@')) {
        [final s, final r] => (s, int.parse(r)),
        _ => (start, top),
      };
      final got = show(text, rule, ring);
      n++;
      if (!(got == want || want == 'ERROR' && got.startsWith('ERROR'))) {
        wrong.add('$rule@$ring | $text\n  got  $got\n  want $want');
      }
    }
    expect(n, 323, reason: 'the number of cases');
    expect(wrong, isEmpty, reason: '${wrong.length} wrong:\n${wrong.join('\n')}');
  });

  test('a later-layer operator parses only at its ring', () {
    // `><` is a reduction, which joins at L3 (sec:grammar, ReduceTail).
    const text = 'total = prices >< (+);';
    final tokens = lex(text);
    expect(() => parse(text, tokens, 'Unit', 2), throwsA(isA<ParseError>()));
    final tree = parse(text, tokens, 'Unit', 3);
    expect(tree.root.all.firstWhere((n) => n.name == 'ReduceTail').layer, 3);
    expect(sx(text, tokens, tree), '((total = (prices (>< (( + )))) ;) )');
  });

  test('a string hole is parsed as an expression', () {
    const text = r'greeting = "Hello, ${name ++ "!"}";';
    final tree = parse(text, lex(text), 'Unit', 1);
    expect(tree.holes, hasLength(1));
    expect(tree.holes[0].root.name, 'Expr');
    const bad = r'greeting = "Hello, ${name ++}";';
    expect(
      () => parse(bad, lex(bad), 'Unit', 1),
      throwsA(isA<ParseError>().having((e) => bad.substring(e.span.start, e.span.end), 'at', '}')),
    );
  });

  test('the embedded grammar is the copy', () {
    expect(syntaxPeg, File('${grammarDir.path}/syntax.peg').readAsStringSync());
    expect(notationPeg, File('${grammarDir.path}/notation.peg').readAsStringSync());
  });

  test('the copies match the spec where it is present', () {
    final spec = Directory('${packageDir.parent.parent.path}/zed');
    if (!File('${spec.path}/DESIGN.md').existsSync()) {
      markTestSkipped('no spec repository at ${spec.path}: drift not checked');
      return;
    }
    final pegs = <String>[];
    final lines = File('${spec.path}/DESIGN.md').readAsLinesSync().iterator;
    while (lines.moveNext()) {
      if (lines.current.trim() != '```peg') continue;
      final body = <String>[];
      while (lines.moveNext() && lines.current.trim() != '```') {
        body.add(lines.current);
      }
      pegs.add('${body.join('\n')}\n');
    }
    String read(String f) => File('${grammarDir.path}/$f').readAsStringSync();
    const stale = 'zed/grammar is out of date: run tools/bin/sync.dart';
    expect(read('syntax.peg'), pegs[1], reason: stale);
    expect(read('notation.peg'), pegs[2], reason: stale);
    expect(
      read('cases.txt'),
      File('${spec.path}/tools/grammar/cases.txt').readAsStringSync(),
      reason: stale,
    );
  });
}
