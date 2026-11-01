import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/src/native/heap.dart';
import 'package:zed/zir.dart' show ZirError;

void main() {
  test('a pair of strings is three cells and frees whole', () {
    final h = Heap();
    final v = Tuple([Str('a'), Str('b')]);
    final w = h.fresh(v);
    expect((h.stats.allocations, h.live), (3, 3));
    expect(h.value(w), v);
    h.dec(w);
    expect((h.stats.frees, h.live), (3, 0));
    expect(() => h.value(w), throwsA(isA<ZirError>()), reason: 'a use after free is caught');
    expect(() => h.dec(w), throwsA(isA<ZirError>()), reason: 'a second drop is caught');
  });

  test('fused release keeps one part with no count write', () {
    final h = Heap();
    final w = h.fresh(Tuple([Str('a'), Str('b')]));
    final out = <(Word, List<int>)>[];
    expect(h.matches(const TupleP([BindP('x'), WildP()]), w, [], out), isTrue);
    expect(out[0].$2, [0]);
    h.release(w, [
      [0],
    ]);
    // The pair is freed without a write, `b` dropped once; `a` is kept, uncounted.
    expect((h.stats.increments, h.stats.decrements, h.live), (0, 1, 1));
    expect(h.value(out[0].$1), Str('a'));
  });

  test('constants match without cells', () {
    final h = Heap();
    final w = h.uncounted(const Atom('some', [Int(3)]));
    final out = <(Word, List<int>)>[];
    expect(h.matches(const AtomP('some', [BindP('n')]), w, [], out), isTrue);
    expect(out[0].$1, const Word.int(3));
    expect(h.matches(const AtomP('none', []), w, [], []), isFalse);
    expect(h.stats.allocations, 0);
  });
}
