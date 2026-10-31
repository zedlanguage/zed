import 'dart:typed_data';

import 'package:test/test.dart';
import 'package:zed/address.dart';
import 'package:zed/cost.dart';

void main() {
  test('Brent bounds lie between depth and work', () {
    for (var work = 0; work < 40; work++) {
      for (var depth = 0; depth <= work; depth++) {
        for (var cores = 1; cores < 6; cores++) {
          final t = brent(work, depth, cores);
          expect(depth <= t && t <= work, isTrue, reason: '$work $depth $cores');
          expect(t, greaterThanOrEqualTo((work + cores - 1) ~/ cores));
        }
      }
    }
    // Zero cores are read as one, and a depth above the work as the work.
    expect(brent(10, 3, 0), 10);
    expect(brent(10, 30, 4), 10);
  });

  test('arithmetic saturates', () {
    const max = 0x7fffffffffffffff;
    const r = (device: 0, work: max, depth: max, footprint: 0);
    final plan = Plan(ContentAddress(Uint8List(32)), const [r, r], const []);
    expect(scalarize(plan, const Target.defaultProfile()), max);
  });
}
