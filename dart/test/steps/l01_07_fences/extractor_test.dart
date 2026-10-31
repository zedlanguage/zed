/// Step L1.7: the fences of DESIGN.md and EXAMPLES.md, copied into `zed/fences/` by
/// `tools/bin/sync.dart`, are lexed, their ✗ marks recorded, and each commented ✗ variant has
/// its own fixture. From here on every step runs the fences of its layer.
library;

import 'package:test/test.dart';
import 'package:zed/fence.dart';

void main() {
  test('only zed fences are extracted, with their lines', () {
    const md =
        '# Notes\n\n```peg\nA = \'a\'\n```\n\nText.\n\n```zed\nx = 1;\n\ny = x;\n```\n\n```\n'
        'plain\n```\n\n1. Step:\n   ```zed\n   z = 2;\n   ```\n';
    expect(extract(md), [
      (line: 9, before: '', text: 'x = 1;\n\ny = x;'),
      (line: 20, before: '1. Step:', text: '   z = 2;'),
    ]);
  });

  test('an unclosed fence runs to the end', () {
    expect(extract('```zed\na = 1;\nb = 2;')[0].text, 'a = 1;\nb = 2;');
    expect(extract('```zed\n```')[0].text, '');
  });

  test('a mark on a comment line is a variant', () {
    const text =
        'q = Point(x:, y:);\n// q = Point(3.0, 4.0);   // ✗ by name\n'
        'z = 7 / 2;   // ✗ `/` is for f64 and rat only\n  // ✗ indented, still a variant';
    expect(
      [marks(text).lines, marks(text).variants],
      [
        [3],
        [2, 4],
      ],
    );
    expect(
      [marks('a = 1; // ✓ fine').lines, marks('a = 1; // ✓ fine').variants],
      [<int>[], <int>[]],
    );
  });

  test('a label is a whole comment line', () {
    expect(label('// [d4] sec:power\n// layer L2\nx = 1;'), 2);
    expect(label('// layer L12 — names a struct of L12'), 12);
    expect(label('// layer L3\n  // layer L5'), 5);
    expect(label('// layer L1x'), isNull);
    expect(label('// layered L3'), isNull);
    expect(label('x = 1; // layer L3'), isNull);
  });
}
