/// Soundness on random bodies: for each arrow the checker gives a random function, each value
/// the evaluator computes at arguments of the arrow's parameter types lies in its result.
library;

import 'package:test/test.dart';
import 'package:zed/check.dart';
import 'package:zed/kernel.dart';

import '../../support/instances.dart';
import '../l01_16_elaboration/elab.dart';
import 'support.dart';

/// A random body over `x` and `y`, of depth at most `d`.
String body(Rng rng, int d) {
  if (d == 0 || rng.below(3) == 0) {
    return switch (rng.below(7)) {
      0 || 1 => 'x',
      2 || 3 => 'y',
      4 => '${rng.int_(-3, 3)}',
      5 => '${rng.int_(-2, 2)}.5',
      _ => '"s"',
    };
  }
  final a = body(rng, d - 1);
  final b = body(rng, d - 1);
  return switch (rng.below(9)) {
    0 => '($a + $b)',
    1 => '($a - $b)',
    2 => '($a * $b)',
    3 => '($a / $b)',
    4 => '($a ++ $b)',
    5 => '(-$a)',
    6 => 'if $a < $b { $a } else { $b }',
    7 => 'if $a == $b { $b } else { $a }',
    _ => '(if $a is String { len($a) } else { $b })',
  };
}

/// Argument texts of carrier `c`.
List<String> args(Carrier c) => switch (c) {
  Carrier.integer => ['0', '2', '-3'],
  Carrier.f64 => ['0.0', '1.5', '-2.25'],
  Carrier.rational => ['0r', '3r/2r', '(0r - 2r)'],
  Carrier.string => ['""', '"ab"'],
  Carrier.boolean => ['true', 'false'],
};

void main() {
  test("each computed value is in its arrow's result", () {
    final rng = Rng(26);
    var (fns, checked, failed) = (0, 0, 0);
    for (var i = 0; i < 700; i++) {
      final f = 'f(positional x, positional y) = ${body(rng, 3)};\n';
      final found = info(f);
      if (found.errors.isNotEmpty) continue;
      final s = found.sigs.values.first;
      fns++;
      // One call for each arrow with carrier parameters and each pair of arguments.
      final p = StringBuffer(f);
      final calls = <(String, Ty)>[];
      for (final a in s.expand()) {
        final cs = [
          for (final q in a.params)
            if (q.pieces case [final pc]) pc.carrier,
        ];
        if (cs.length != a.params.length || cs.contains(null)) continue;
        for (final x in args(cs[0]!)) {
          for (final y in args(cs[1]!)) {
            p.write('r${calls.length} = f($x, $y);\n');
            calls.add(('f($x, $y)', a.result));
          }
        }
      }
      final u = elab('$p');
      for (final (k, (call, result)) in calls.indexed) {
        try {
          final v = Evaluator(World()).run(withPrelude(u.get('r$k')!));
          expect(result.contains(v), isTrue, reason: '$f$call: $v is not in $result');
          checked++;
        } on KernelError {
          // A value past the size limit; a division by zero is the atom, a value.
          failed++;
        }
      }
    }
    print('$fns functions, $checked values, $failed failed');
    expect(fns >= 300 && checked >= 650, isTrue, reason: '$fns functions, $checked values');
    expect(failed < checked ~/ 4, isTrue, reason: '$failed failed of $checked');
  });

  test('a wrong claim is caught', () {
    // The check above would reject a result type that missed the value.
    final a = info('f(positional x, positional y) = x + y;\n').sigs.values.first.expand()[0];
    expect(a.result.contains(const Int(3)), isTrue);
    expect(a.result.contains(Float(3.0)), isFalse);
    expect(a.result.contains(Str('3')), isFalse);
  });
}
