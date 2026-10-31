import 'package:test/test.dart';
import 'package:zed/kernel.dart';

void main() {
  test('messages', () {
    expect(
      CollisionError([Str('ann'), const Int(2)]).toString(),
      'collision: two writers for keypath ["ann", 2]',
    );
    expect(const EmptyKeypathError().toString(), 'a key map returned an empty keypath');
    expect(const MixedDepthError().toString(), 'fold over leaves at another depth than its own');
    expect(const KernelTypeError('x').toString(), 'type error: x');
    expect(const UnknownPortError('p').toString(), 'unknown port `p`');
    expect(const OutOfFuelError().toString(), 'out of fuel');
    expect(const TooDeepError().toString(), 'calls nested too deeply');
    expect(const OverflowError().toString(), "a number beyond the evaluator's size limit");
    expect(
      const StalledError([Int(1), Int(2)]).toString(),
      'recursion stalled: entries 1, 2 depend on each other',
    );
  });
}
