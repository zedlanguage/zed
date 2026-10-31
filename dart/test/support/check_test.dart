import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import 'check.dart';
import 'instances.dart';

Matcher failsWith(String text) =>
    throwsA(isA<TestFailure>().having((e) => e.message, 'message', contains(text)));

void main() {
  test('agreement is bitwise on floats and by kind on errors', () {
    expect(agree(const Int(1), const Int(1)), isTrue);
    expect(agree(Float(0.0), Float(-0.0)), isFalse);
    expect(agree(Float(double.nan), Float(-double.nan)), isTrue);
    CollisionError c(int k) => CollisionError([Int(k)]);
    expect(agree(c(1), c(2)), isTrue);
    expect(agree(c(1), const OverflowError()), isFalse);
    expect(agree(c(1), const Int(1)), isFalse);
  });

  test('holds counts and refuted finds the counterexample', () {
    // `x * 2 == x + x` holds; `x * x == x + x` fails first at -8.
    final xs = bmcInts();
    expect(
      holds(xs, (x) => (prim(Prim.mul, [lit(x), lit(2)]), prim(Prim.add, [lit(x), lit(x)]))),
      17,
    );
    final (x, a, b) = refuted(
      xs,
      (x) => (prim(Prim.mul, [lit(x), lit(x)]), prim(Prim.add, [lit(x), lit(x)])),
    );
    expect((x, a, b), (-8, const Int(64), const Int(-16)));
  });

  test('holds names the failing instance', () {
    expect(
      () => holds([1, 2, 3], (x) => (lit(x), lit(x == 3 ? 0 : x))),
      failsWith('the law fails on 3'),
    );
  });

  test('refuted insists on a counterexample', () {
    expect(() => refuted([1, 2], (x) => (lit(x), lit(x))), failsWith('no instance refutes'));
  });

  test('properties', () {
    expect(property([0, 1, 2, 3, 4], (_) => null), 5);
    final (i, why) = propertyRefuted([0, 1, 2, 3, 4], (i) => i == 3 ? 'three' : null);
    expect((i, why), (3, 'three'));
  });
}
