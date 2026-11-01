/// The ✗ fence variants of the spec (zed/fences/variants): what each gives at L1. None
/// reaches its documented error yet: the forms it needs come in later layers, so each is
/// pinned to the diagnostic it gives now, and the step that enables it changes the pin.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/testing.dart';

import '../../support/fences.dart' as fences;
import 'diagnostics.dart' as diagnostics;

final dir = '${fences.dir.path}/variants';

String text(String name) => File('$dir/$name.zed').readAsStringSync();

/// The first failure of the variant `name`, or `pass` when every check passes.
String first(String name) {
  for (final o in testUnit(text(name))) {
    if (o.failure case final f?) return '${o.line}: $f';
  }
  return 'pass';
}

void main() {
  test('each variant gives its pinned diagnostic at L1', () {
    const cases = {
      // Passes the mark check because `Point` is not defined: structs are L2.
      'constructor-called-by-position': 'pass',
      'dot-never-mutates': '2: this form (Decl) is built from layer L2',
      'nullable-column-missing-none': '25: the line is marked ✗ and has no diagnostic',
      'numeric-is-not-binary-float': '25: the line is marked ✗ and has no diagnostic',
      'payload-built-by-position': '3: this form (Decl) is built from layer L2',
      // Passes the mark check because its marked line does not parse at L1.
      'taint-reaches-clean-sink': 'pass',
      'taint-through-concatenation': '44: the line is marked ✗ and has no diagnostic',
      'two-writers-of-one-generation': '2: this form (Decl) is built from layer L2',
      'unit-mismatch-force-energy': '49: the line is marked ✗ and has no diagnostic',
      'unit-mismatch-in-sum': '36: the line is marked ✗ and has no diagnostic',
      'value-binding-has-no-next-generation': '2: this form (Decl) is built from layer L2',
    };
    final names = [
      for (final e in Directory(dir).listSync())
        e.uri.pathSegments.last.replaceFirst(RegExp(r'\.zed$'), ''),
    ];
    expect(names, hasLength(cases.length), reason: '$names');
    final wrong = [
      for (final MapEntry(key: name, value: want) in cases.entries)
        if (first(name) case final got when got != want) '$name\n  got  $got\n  want $want',
    ];
    expect(wrong, isEmpty, reason: wrong.join('\n'));
  });

  test('the two passing variants pass for a reason other than their documented error', () {
    expect(
      diagnostics.rejected(text('constructor-called-by-position')),
      '6:5: `Point` is not defined',
    );
    final e = diagnostics.rejected(text('taint-reaches-clean-sink'));
    expect(e, startsWith('39:1: expected '));
  });
}
