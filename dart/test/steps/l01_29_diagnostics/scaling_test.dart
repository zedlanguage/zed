/// Placing diagnostics at the rule of low complexity (DESIGN.md Part G). Placing each
/// diagnostic and each of its steps by decoding the file from its first byte would make a
/// file of `n` lines with an error on each take `O(n²)`.
library;

import 'package:test/test.dart';

import '../../support/scaling.dart';
import 'diagnostics.dart';

/// `n` definitions, each reading a name nothing declares.
String unresolved(int n) => [for (var i = 0; i < n; i++) 'f$i = missing$i;\n'].join();

/// A chain of `n` bindings, each reading the one before twice, ending in an error.
String doubled(int n) {
  final src = StringBuffer('main(stdin: Lines) -> (stdout: Lines) {\n  a0 = 1;\n');
  for (var i = 1; i < n; i++) {
    src.write('  a$i = a${i - 1} + a${i - 1};\n');
  }
  return '$src  stdout <- "x" ++ a${n - 1};\n}\n';
}

/// A function adding `n` untyped parameters and testing the sum as a condition: one class
/// with `n` reasons, shown in one diagnostic. Each parameter and each addition has a line of
/// its own, since each step of a diagnostic shows the whole line it is on.
String summedCondition(int n) {
  final xs = [for (var i = 0; i < n; i++) 'x$i'];
  return 'f(${xs.map((x) => 'positional $x').join(',\n')}) = '
      'if ${xs.join('\n+ ')} { 1 } else { 2 };\n';
}

void main() {
  test('placing a diagnostic on every line scales', () {
    // At 500 lines the rest of loading hides a quadratic placement; at 2000 it does not.
    check('placing a diagnostic on each of n lines', 2000, (n) {
      final out = rejected(unresolved(n));
      // One diagnostic per line, the last at the last line, after `f{n-1} = `.
      final last = n - 1;
      final lines = out.split('\n');
      expect(lines, hasLength(n));
      expect(lines.last, '$n:${'f$last = '.length + 1}: `missing$last` is not defined');
    });
  });

  test('deriving through values read twice scales', () {
    check('the derivation of a chain read twice at each of n bindings', 400, (n) {
      expect(rejected(doubled(n)), contains('`a0` is defined as this expression, 1'));
    });
  });

  test('the reasons of a class narrowed many times scale', () {
    // Each reason was looked for among those shown before it.
    final out = rejected(summedCondition(3));
    expect(out, contains('not bool'));
    expect('gives these values one carrier'.allMatches(out), hasLength(2), reason: out);
    check('the reasons of a class merged n times', 250, (n) {
      final out = rejected(summedCondition(n));
      expect('gives these values one carrier'.allMatches(out), hasLength(n - 1));
    });
  });
}
