import 'package:test/test.dart';
import 'package:zed/kernel.dart';

void main() {
  test('signed zeros differ and NaNs are one value', () {
    expect(Float(0.0), isNot(Float(-0.0)));
    expect(Float(-0.0).compareTo(Float(0.0)), lessThan(0));
    final otherNan = f64FromBits(f64Bits(double.nan) ^ 1);
    expect(otherNan.isNaN, isTrue);
    expect(Float(otherNan), Float(double.nan));
  });

  test('display forms', () {
    expect(const Atom('empty').toString(), '#empty');
    final io = Atom('ioError', [Str('disk full')]);
    expect(io.toString(), '#ioError("disk full")');
    final t = Tuple([const Int(1), const Bool(true), Float(-0.0)]);
    expect(t.toString(), '(1, true, -0.0)');
    final p = Path([Str('ann'), const Int(2)]);
    expect(p.toString(), '["ann" -> 2]');
  });

  test('accessors', () {
    expect(const Int(3).asInt, 3);
    expect(Str('x').asInt, isNull);
    expect(const Int(3).asFamily, isNull);
    expect(const Family.empty().asFamily, isNotNull);
    expect(valueOf(true), const Bool(true));
    expect(Float(2.5).x, 2.5);
    expect(Float(1.0).compareTo(Float(2.0)), lessThan(0));
  });
}
