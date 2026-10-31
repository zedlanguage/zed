import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import 'instances.dart';

void main() {
  test('shortlex orders by length, then by the alphabet', () {
    expect(shortlex([1, 2], 2), [
      <int>[],
      [1],
      [2],
      [1, 1],
      [1, 2],
      [2, 1],
      [2, 2],
    ]);
    expect(shortlex(bmcInts(), 2).length, 1 + 17 + 289);
  });

  test('partial maps count absent as a choice', () {
    final m = partialMaps([0, 1], ['a', 'b']);
    expect(m.length, 9);
    expect(m, anyElement(equals([(1, 'b')])));
  });

  test('random draws repeat from one seed', () {
    final (a, b) = (Rng(7), Rng(7));
    final xs = [for (var i = 0; i < 50; i++) a.int_(-8, 8)];
    final ys = [for (var i = 0; i < 50; i++) b.int_(-8, 8)];
    expect(xs, ys);
    expect(xs.every((x) => -8 <= x && x <= 8), isTrue);
    expect(xs.contains(-8) && xs.contains(8), isTrue);
  });

  test('the float instance has nine distinct values', () {
    expect({for (final x in bmcFloats) f64Bits(x)}.length, 9);
    expect(bmcFloats.any((x) => x.isNaN), isTrue);
  });
}
