/// Step L1.35: the MLIR study, `zed/compiler/MLIR.md`. The record decides how ZIR lowers to
/// MLIR's dialects; this step holds it to the node inventory, so an operation or a region kind
/// added later without a lowering fails here.
library;

import 'dart:collection';
import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart';

import '../../support/support.dart';

String record() => File('${packageDir.parent.path}/zed/compiler/MLIR.md').readAsStringSync();

/// The first cells of the rows of the table under heading `##` `title`, without backticks.
Set<String> rows(String text, String title) {
  final start = text.indexOf('\n## $title\n');
  if (start < 0) throw StateError('no section `$title`');
  final body = text.substring(start + title.length + 5).split('\n## ').first;
  return SplayTreeSet.of([
    for (final l in body.split('\n'))
      if (l.startsWith('| `')) l.substring(2).split(' |').first.replaceAll('`', ''),
  ]);
}

/// The row name of `op`: its text-form name, and `read` or `push` for a port.
// No wildcard: a new operation stops this test from compiling until it is named here.
String row(Op op) => switch (op) {
  ReadOp() => 'port read',
  PushOp() => 'port push',
  ReindexOp() ||
  DiscardOp() ||
  FoldOp() ||
  FixOp() ||
  GenOp() ||
  FamOp() ||
  DerivedOp() ||
  PrimOp() ||
  ApplyOp() ||
  LambdaOp() ||
  IfOp() ||
  MatchOp() ||
  RecOp() ||
  WaveOp() => op.name,
};

List<Op> everyOp() => [
  const ReindexOp(Residue()),
  const DiscardOp(),
  FoldOp(1, false, Evidence()),
  FixOp(true, Evidence()),
  const GenOp(GuardPos.before),
  const ReadOp('out'),
  const PushOp('out'),
  const FamOp(),
  for (final d in Derived.values) DerivedOp(d),
  const PrimOp(Prim.add),
  const ApplyOp(),
  const LambdaOp(),
  const IfOp(),
  const MatchOp([]),
  const RecOp(),
  const WaveOp(),
];

void main() {
  test('every operation has a lowering', () {
    final want = {for (final op in everyOp()) row(op)};
    expect(want.length, 19);
    expect(rows(record(), 'Operations'), want);
  });

  test('every region kind has a form', () {
    expect(rows(record(), 'Region kinds'), {for (final k in RegionKind.values) k.name});
  });

  test('both edge kinds have a form', () {
    expect(rows(record(), 'Edges'), {'state', 'value'});
  });

  test('the record answers the four questions', () {
    // The decisions the plan names: no ZIR dialect in MLIR, the graph regions, the state edges,
    // the content addresses, the certificates, and Cranelift as the compact back end.
    final text = record();
    for (final decision in [
      "**ZIR is lowered into MLIR's existing dialects and is not written as an MLIR dialect.**",
      '**Graph regions are not used.**',
      '**State edges become order, not values.**',
      '**Content addresses travel as locations.**',
      '**Certificates stop at the lowering.**',
      '**The compact back end stays Cranelift.**',
    ]) {
      expect(text, contains(decision), reason: 'the record lacks $decision');
    }
  });
}
