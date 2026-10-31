import 'package:test/test.dart';
import 'package:zed/kernel.dart';

/// The length at or above which a join is kept as its two parts.
const short = 64;

Text long(String c) => Text(c * short);

void main() {
  test('a join reads as its parts in order', () {
    final a = long('a'), b = long('b');
    final ab = Text.join(a, b);
    expect(ab.text, '$a$b');
    expect(Text.join(Text(''), a), a);
    expect(Text.join(Text('x'), Text('y')), Text('xy'));
    // Equal text, made two ways, is equal and orders the same.
    final whole = Text('$a$b');
    expect(ab, whole);
    expect(ab.compareTo(whole), 0);
    expect(ab.compareTo(Text.join(a, long('c'))), lessThan(0));
  });

  test('a chain a million deep is written out', () {
    final piece = long('z');
    var t = Text('');
    for (var i = 0; i < 1000000; i++) {
      t = Text.join(t, piece);
    }
    expect(t.length, short * 1000000);
    expect(t.text.codeUnits.every((c) => c == 0x7a), isTrue);
  });
}
