import 'package:test/test.dart';
import 'package:zed/native.dart';

void main() {
  test('concatenation copies once', () {
    var r = Rope.leaf('');
    for (var i = 0; i < 1000; i++) {
      r = Rope.cat(r, Rope.leaf('$i,'));
    }
    var copied = 0;
    final s = r.flat((n) => copied += n);
    expect(copied, s.length);
    expect(r.chars, s.runes.length);
    expect(s, allOf(startsWith('0,1,2,'), endsWith('999,')));
    r.flat((n) => copied += n);
    expect(copied, s.length, reason: 'a second flattening copies nothing');
  });

  test('a long chain flattens without overflow', () {
    var r = Rope.leaf('x');
    for (var i = 0; i < 200000; i++) {
      r = Rope.cat(Rope.leaf('y'), r);
    }
    expect(r.bytes, 200001);
    expect(r.flat((_) {}), '${'y' * 200000}x');
  });
}
