/// Name resolution over the documentation's fences and the corpus.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';
import 'package:zed/resolve.dart';

import '../../support/fences.dart' as fences;
import '../../support/support.dart';
import 'res.dart';

void main() {
  // Every documentation unit that builds resolves, or fails only on what a fragment leaves to
  // the text around it: a name or type it does not bind, or a rebinding the fence marks ✗.
  test('every building fence resolves but for its free names', () {
    var (resolved, built) = (0, 0);
    for (final f in fences.all().where((f) => !f.notation)) {
      final tokens = lexFence(f.text);
      final List<Stmt> stmts;
      try {
        stmts = unit(f.text, tokens, parse(f.text, tokens, 'Unit', top));
      } on BuildError {
        continue;
      }
      built++;
      try {
        resolve(stmts);
        resolved++;
      } on ResolveErrors {
        for (final e in errors(f.text)) {
          final free = e.contains('is not defined [');
          final marked = e.contains('already bound') && f.text.contains('✗');
          expect(free || marked, isTrue, reason: '${f.at}: $e');
        }
      }
    }
    // 23 built and 2 resolved at step L1.14; later steps build more.
    final counts = '$built built, $resolved resolved';
    expect(built, greaterThanOrEqualTo(23), reason: counts);
    expect(resolved, greaterThanOrEqualTo(2), reason: counts);
  });

  test('the corpus program that builds resolves', () {
    final text = File('${packageDir.parent.path}/zed/corpus/09-canonical-equal.zed')
        .readAsStringSync();
    expect(run(text), isA<Resolution>());
  });
}
