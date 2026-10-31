/// The two zeros (sec:type_resolution, "Equality and order corner rules"): `==` and the orders
/// read `0.0 == -0.0`, as IEEE 754 does, and key formation makes them one key. Where a value's
/// identity matters (a law's equation, a content address) they stay two values, since
/// `1.0 / x` separates them.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

void main() {
  test('either zero finds the one key', () {
    // A lookup is copied into key form only when it holds a `-0.0`, at any depth.
    final (pos, neg) = (Float(0.0), Float(-0.0));
    Value pair(Value z) => Tuple([const Int(1), z]);
    final f = Family.of([(neg, const Int(1)), (pair(pos), const Int(2))]);
    for (final z in [pos, neg]) {
      expect(f[z], const Int(1), reason: '$z');
      expect(f[pair(z)], const Int(2), reason: '$z');
    }
    expect(f[Float(1.0)], isNull);
  });
}
