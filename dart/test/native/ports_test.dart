import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/native.dart';
import 'package:zed/run.dart' show RunError;

void main() {
  test('lines split as the interpreter does', () {
    List<Value> f(List<int> b) => [for (final (_, v) in (lines(b) as Family).leaves()) v];
    expect(f([]), <Value>[]);
    expect(f('\n'.codeUnits), [Str('')]);
    expect(f('a\r\nb'.codeUnits), [Str('a'), Str('b')]);
    expect(f('a\n\nb\n'.codeUnits), [Str('a'), Str(''), Str('b')]);
    expect(f([0xff, 0x0a]), [const Atom('ioError')]);
    expect(write('o', Str('x')), 'x\n'.codeUnits);
    expect(() => write('o', const Int(1)), throwsA(isA<RunError>()));
  });
}
