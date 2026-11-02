import 'dart:math';

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

  diffs();
}

/// The keys whose entries differ, computed from the entries alone.
List<int> differing(PMap<int, Object> a, PMap<int, Object> b) {
  final (x, y) = ({for (final (k, v) in a.entries) k: v}, {for (final (k, v) in b.entries) k: v});
  return ({...x.keys, ...y.keys}.where((k) => !identical(x[k], y[k])).toList()..sort());
}

void diffs() {
  test('diff names each key put, replaced or removed on either side', () {
    final r = Random(7);
    for (var round = 0; round < 200; round++) {
      var base = PMap<int, Object>.empty((a, b) => a - b);
      for (var i = r.nextInt(300); i > 0; i--) {
        base = base.put(r.nextInt(400), Object());
      }
      var (a, b) = (base, base);
      for (var i = r.nextInt(20); i > 0; i--) {
        a = r.nextBool() ? a.put(r.nextInt(400), Object()) : a.remove(r.nextInt(400));
        b = r.nextBool() ? b.put(r.nextInt(400), Object()) : b.remove(r.nextInt(400));
      }
      expect(a.diff(b), differing(a, b), reason: 'round $round');
      expect(b.diff(a), differing(a, b), reason: 'round $round');
      expect(a.diff(a), isEmpty);
    }
  });

  test('diff of two maps that share most of their tree skips what they share', () {
    const n = 1 << 16;
    PMap<int, Object> build() {
      var m = PMap<int, Object>.empty((a, b) => a - b);
      for (var i = 0; i < n; i++) {
        m = m.put(i, i);
      }
      return m;
    }

    final m = build();
    final changed = m.put(n ~/ 3, Object()).put(n + 5, 0).remove(17);
    Duration time(PMap<int, Object> other, List<int> want) {
      final sw = Stopwatch()..start();
      for (var i = 0; i < 100; i++) {
        expect(changed.diff(other), want);
      }
      return sw.elapsed;
    }

    final shared = time(m, [17, n ~/ 3, n + 5]);
    // The control: the same entries in a tree built apart, which shares no node, so each diff
    // walks every entry.
    final apart = time(build(), [17, n ~/ 3, n + 5]);
    expect(shared * 50, lessThan(apart), reason: 'shared $shared, apart $apart');
  });
}
