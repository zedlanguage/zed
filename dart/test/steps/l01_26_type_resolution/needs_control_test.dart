/// The negative control of the scaling test of needs replayed through calls: calls that grow
/// with the depth are caught.
library;

import 'package:test/test.dart';

import '../../support/scaling.dart' as scaling;
import 'support.dart';

/// `n` functions, each calling the one before twice with its untyped parameter, the first
/// taking a component of it; with `all`, each calls every one before it instead.
String fan(int n, bool all) {
  final src = StringBuffer('g0(positional t) = t[0];\n');
  for (var i = 1; i < n; i++) {
    final calls = all ? [for (var j = 0; j < i; j++) 'g$j(t)'] : ['g${i - 1}(t)', 'g${i - 1}(t)'];
    src.write('g$i(positional t) = ${calls.join(' + ')};\n');
  }
  return '$src';
}

/// The texts of [fan] at `n` and `factor * n`, built before the timing.
Map<int, String> fans(int n, bool all) => {
  for (final m in [n, scaling.factor * n]) m: fan(m, all),
};

void main() {
  test('control: the scaling check catches calls that grow with the depth', () {
    // Each function calls every one before it: n² calls in n functions.
    final texts = fans(10, true);
    expect(
      () => scaling.check('n functions, each calling every one before', 10, (n) {
        expect(info(texts[n]!).errors, isEmpty);
      }),
      throwsStateError,
    );
  });
}
