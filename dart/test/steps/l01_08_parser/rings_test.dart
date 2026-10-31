/// Every fence of the documentation parses, and first parses at the ring
/// `tools/bin/sync.dart` recorded with the spec's grammar tools: as a unit, or under the
/// documentation notation.
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import '../../support/fences.dart' as fences;

bool parses(String text, List<Token> tokens, String start, int ring) {
  try {
    parse(text, tokens, start, ring);
    return true;
  } on ParseError {
    return false;
  }
}

void main() {
  test('every fence parses first at its recorded ring', () {
    final all = fences.all();
    expect(all, hasLength(149));
    final wrong = <String>[];
    for (final f in all) {
      final tokens = lexFence(f.text);
      final unit = parses(f.text, tokens, 'Unit', top);
      if (unit == f.notation) {
        wrong.add('${f.at}: parses as a unit: $unit');
        continue;
      }
      final start = f.notation ? 'DocFence' : 'Unit';
      final lowest = [for (var k = 1; k <= top; k++) k]
          .where((k) => parses(f.text, tokens, start, k))
          .firstOrNull;
      if (lowest != f.ring) wrong.add('${f.at}: ring $lowest, recorded ${f.ring}');
    }
    expect(wrong, isEmpty, reason: wrong.join('\n'));
  });

  test('every variant fixture parses as its fence does', () {
    final all = fences.all();
    for (final v in fences.variants()) {
      final fence = all.firstWhere(
        (f) => f.text.split('\n').any((l) => l.trim() == v.of),
        orElse: () => fail('no fence has the line of ${v.name}'),
      );
      final start = fence.notation ? 'DocFence' : 'Unit';
      final tokens = lexFence(v.text);
      expect(parses(v.text, tokens, start, top), isTrue, reason: '${v.name} does not parse');
    }
  });
}
