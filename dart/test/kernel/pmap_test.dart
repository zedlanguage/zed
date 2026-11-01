import 'package:test/test.dart';
import 'package:zed/src/kernel/pmap.dart';

void main() {
  test('the entries from a key are those at or above it, in order', () {
    var m = PMap<int, String>.empty((a, b) => a - b);
    for (final k in [50, 10, 90, 30, 70, 20, 80, 40, 60]) {
      m = m.put(k, '$k');
    }
    expect(m.from(35).map((e) => e.$1), [40, 50, 60, 70, 80, 90]);
    expect(m.from(40).map((e) => e.$1), [40, 50, 60, 70, 80, 90]);
    expect(m.from(0).map((e) => e.$1), [10, 20, 30, 40, 50, 60, 70, 80, 90]);
    expect(m.from(91), isEmpty);
    expect(PMap<int, String>.empty((a, b) => a - b).from(0), isEmpty);
  });

  test('every lower bound over a large map', () {
    const n = 2000;
    var m = PMap<int, int>.empty((a, b) => a - b);
    for (var i = 0; i < n; i++) {
      m = m.put((i * 7919) % n * 2, i);
    }
    for (var k = -1; k <= 2 * n; k++) {
      final first = m.from(k).firstOrNull?.$1;
      final want = k <= 0 ? 0 : (k.isOdd ? k + 1 : k);
      expect(first, want < 2 * n ? want : null, reason: 'from($k)');
    }
    expect(m.from(1001).length, n - 501);
  });
}
