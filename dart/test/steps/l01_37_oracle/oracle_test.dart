/// Step L1.37: the differential oracle. The interpreter and the native code of L1.36 run every
/// enabled fence, every corpus program and every step unit, and their outputs are compared
/// byte for byte: a program's port writes, and for a unit with no port the printing of each
/// top-level binding whose type has no function component. The oracle runs in CI from this
/// step on, so every later step keeps the two in agreement.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/fences.dart' as fences;
import '../../support/oracle.dart';

void main() {
  test('every enabled fence agrees', () {
    final r = Report();
    for (final f in fences.all().where((f) => f.layer <= enabled && !f.notation)) {
      r.add(f.at, unit(f.text, natives));
    }
    expect(r.mismatches, isEmpty);
    // The lambda fence's `five` and `seven` under each engine, and the table checks of the
    // four fences: the three rejected ones compare nothing.
    expect(r.compared, 6);
  });

  test('every step unit agrees', () {
    final r = Report();
    for (final f in stepUnits()) {
      r.add(shown(f), unit(f.readAsStringSync(), natives));
    }
    expect(r.mismatches, isEmpty);
    expect(r.compared, 12);
  });

  test('every enabled corpus program agrees and writes its output', () {
    final all = corpus();
    expect(all, hasLength(31));
    final on = [
      for (final (f, layer) in all)
        if (layer <= enabled) f,
    ];
    // The corpus begins at L3; each program joins the oracle when its layer is enabled.
    expect(on, isEmpty);
    for (final f in on) {
      final base = f.path.substring(0, f.path.length - '.zed'.length);
      final (r, want) = program(f.readAsStringSync(), File('$base.in').readAsBytesSync(), natives);
      expect(r.mismatches, isEmpty, reason: shown(f));
      final out = Str(File('$base.out').readAsStringSync());
      expect(want, 'port `stdout` writes $out');
    }
  });

  test('every step program agrees on every corpus input', () {
    final r = Report();
    var runs = 0;
    final inputs = [
      for (final (f, _) in corpus())
        (f, File('${f.path.substring(0, f.path.length - '.zed'.length)}.in').readAsBytesSync()),
    ];
    for (final p in stepUnits()) {
      final text = p.readAsStringSync();
      for (final (c, input) in inputs) {
        final (rep, want) = program(text, input, natives);
        if (want != null) runs++;
        r.add('${shown(p)} on ${shown(c)}', rep);
      }
    }
    expect(r.mismatches, isEmpty);
    // Four programs on 31 inputs, each under two engines.
    expect((runs, r.compared), (124, 248));
  });
}
