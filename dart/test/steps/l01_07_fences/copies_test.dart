/// Step L1.7: every fence of the copies lexes, with its tokens, marks and variants as expected,
/// and the copies match the spec where it is present.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/fence.dart' as fence;
import 'package:zed/lex.dart';

import '../../support/fences.dart' as fences;
import '../../support/support.dart';
import '../../support/tokens.dart';

/// The tokens of each fence of the copy `file`, under its place and layer.
String tokensOf(String file) => [
  for (final f in fences.of(file))
    '== ${f.at} L${f.layer}\n${renderLines(f.text, lexFence(f.text))}',
].join('\n');

void main() {
  test('every DESIGN.md fence lexes', () {
    expectOutput('l01_07_fences', 'design_tokens', tokensOf('design.md'));
  });

  test('every EXAMPLES.md fence lexes', () {
    expectOutput('l01_07_fences', 'examples_tokens', tokensOf('examples.md'));
  });

  test('every fence has a layer no lower than its label', () {
    final all = fences.all();
    expect(all, hasLength(47 + 102));
    for (final f in all) {
      expect(f.layer, inInclusiveRange(1, 29), reason: f.at);
      expect(f.layer, greaterThanOrEqualTo(fence.label(f.text) ?? 1), reason: '${f.at} label');
    }
    final notation = [
      for (final f in all)
        if (f.notation) f.at,
    ];
    expect(notation, hasLength(13), reason: '$notation');
  });

  test('marks', () {
    expectOutput(
      'l01_07_fences',
      'marks',
      [
        for (final f in fences.all())
          if (fence.marks(f.text) case (:final lines, :final variants)
              when lines.isNotEmpty || variants.isNotEmpty)
            '${f.at.padRight(16)} ✗ $lines variants $variants',
      ].join('\n'),
    );
  });

  test('every commented variant has exactly one fixture', () {
    final want = [
      for (final f in fences.all())
        for (final k in fence.marks(f.text).variants) f.text.split('\n')[k - 1].trim(),
    ]..sort();
    final variants = fences.variants();
    expect([for (final v in variants) v.of]..sort(), want);
    for (final v in variants) {
      // The fixture makes its one variant live: one ✗ line outside a comment, and it lexes.
      expect(fence.marks(v.text).lines, hasLength(1), reason: v.name);
      lexFence(v.text);
    }
  });

  test('… is an elision only in a fence', () {
    expect(
      render(lexFence('f(x) = …;\ns = "a … b"; // and …')),
      r'f ( x ) = … ; s = str["a … b"] ;',
    );
    expect(() => lex('f(x) = …;'), throwsA(isA<LexError>()));
  });

  // The copies equal the spec's fences, where the spec repository is beside this one (it is
  // not in CI). Layers are not compared: `tools/bin/sync.dart --check` recomputes them with the
  // spec's tools.
  test('the copies match the spec where it is present', () {
    final spec = Directory('${packageDir.parent.parent.path}/zed');
    if (!File('${spec.path}/DESIGN.md').existsSync()) {
      markTestSkipped('no spec repository at ${spec.path}: drift not checked');
      return;
    }
    for (final (doc, copy) in [('DESIGN.md', 'design.md'), ('EXAMPLES.md', 'examples.md')]) {
      final theirs = [
        for (final f in fence.extract(File('${spec.path}/$doc').readAsStringSync()))
          ('$doc:${f.line}', f.text),
      ];
      final ours = [for (final f in fences.of(copy)) (f.at, f.text)];
      expect(ours, theirs, reason: '$copy is out of date: run tools/bin/sync.dart');
    }
  });
}
