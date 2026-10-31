/// Step M0.8: the Zed₀ checklist (`zed/compiler/ZED0.md`). The audit against corpus program 31
/// needs the spec's grammar tools and runs by hand (`zed/compiler/audit.py`); this test keeps
/// the recorded result consistent: the layer the checklist names as completing Zed₀ is the
/// highest layer of any item in it, and program 31 is labeled at that layer.
library;

import 'dart:io';

import 'package:test/test.dart';

import '../../support/support.dart';

String spec(String path) => File('${packageDir.parent.path}/zed/$path').readAsStringSync();

/// The number at the start of `s`.
int leading(String s) => int.parse(RegExp(r'^\d+').firstMatch(s)![0]!);

/// The layers in the first column of every table row, after the header rows.
List<int> tableLayers(String text) => [
  for (final l in text.split('\n'))
    if (l.startsWith('| L') && RegExp(r'^\d').hasMatch(l.substring(3))) leading(l.substring(3)),
];

/// The layers in the third column of Part B's rows.
List<int> partBLayers(String text) => [
  for (final l in text.split('## Part B')[1].split('\n'))
    if (l.startsWith('| ') && !l.startsWith('| Need') && !l.startsWith('|---'))
      leading(l.split(' | ')[2].replaceFirst(RegExp('^L+'), '')),
];

void main() {
  test('the completing layer is the highest item and program 31 is labeled there', () {
    final checklist = spec('compiler/ZED0.md');
    final stated = int.parse(
      checklist.split('**The layer that completes it is L')[1].split('**')[0],
    );
    final a = tableLayers(checklist);
    final b = partBLayers(checklist);
    expect(a, [1, 2, 3, 4, 5, 6]);
    expect(b.length, 9);
    expect([...a, ...b].reduce((x, y) => x > y ? x : y), stated);
    expect(spec('corpus/31-typechecker.zed').split('\n').first, '// layer L$stated');
  });
}
