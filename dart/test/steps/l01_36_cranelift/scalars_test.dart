/// Integer, float and boolean arithmetic and comparisons run inline: no kernel call, no
/// cell. Every edge case the inline code cannot decide (an overflow, `-` of the least
/// integer, division) goes to the runtime and gives the kernel's value, and every inline
/// result is the kernel's bit for bit, NaN and the signed zeros included.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native;

import '../l01_33_lowering/lowering.dart' show count;
import 'native.dart';

/// [v] printed, with a float's bits, so that equal printing is equal bits.
String bits(Value v) => v is Float ? '$v ${f64Bits(v.x)}' : '$v';

/// [f]'s value, or its error, printed.
String outcome(Value Function() f) {
  try {
    return bits(f());
  } catch (e) {
    return 'error: $e';
  }
}

void main() {
  const min = -0x8000000000000000, max = 0x7fffffffffffffff;

  test('a loop of integer arithmetic calls no kernel', () {
    // The sum of the squares below 10, by a closure applied to each.
    final sq = lam(['x'], prim(Prim.mul, [var_('x'), var_('x')]));
    var sum = lit(0);
    for (var i = 0; i < 10; i++) {
      sum = prim(Prim.add, [
        sum,
        app(var_('sq'), [lit(i)]),
      ]);
    }
    final t = let_('sq', sq, sum);
    final o = run(t);
    expect(o.value, kernel(t));
    expect('${o.value}', '285');
    expect(o.kernelCalls, 0);
    expect(o.stats.allocations, 1, reason: 'the closure is the one cell');
  });

  test('comparisons and branches on scalars call no kernel', () {
    final t = if_(
      prim(Prim.and, [
        prim(Prim.lt, [lit(3), lit(4)]),
        prim(Prim.ge, [lit(2.5), lit(-0.0)]),
      ]),
      prim(Prim.neg, [lit(1.5)]),
      lit(0.0),
    );
    final o = run(t);
    expect(o.value, kernel(t));
    expect('${o.value}', '-1.5');
    expect((o.kernelCalls, o.stats.allocations), (0, 0));
  });

  test('every edge case gives the kernel\'s value', () {
    final cases = [
      prim(Prim.add, [lit(max), lit(1)]),
      prim(Prim.sub, [lit(min), lit(1)]),
      prim(Prim.mul, [lit(max), lit(2)]),
      prim(Prim.neg, [lit(min)]),
      prim(Prim.div, [lit(7), lit(2)]),
      prim(Prim.div, [lit(1), lit(0)]),
      prim(Prim.div, [lit(1.0), lit(0.0)]),
      prim(Prim.div, [lit(0.0), lit(0.0)]),
      prim(Prim.sub, [lit(double.infinity), lit(double.infinity)]),
      prim(Prim.mul, [lit(-0.0), lit(5.0)]),
      prim(Prim.neg, [lit(0.0)]),
      prim(Prim.add, [lit(-0.0), lit(-0.0)]),
      prim(Prim.lt, [lit(double.nan), lit(1.0)]),
      prim(Prim.ge, [lit(double.nan), lit(double.nan)]),
      prim(Prim.eq, [lit(0.0), lit(-0.0)]),
      prim(Prim.eq, [lit(3), lit(3)]),
      prim(Prim.ne, [lit(3), lit(4)]),
      prim(Prim.add, [lit(1), lit(2.0)]),
      prim(Prim.lt, [lit(1), lit(2.0)]),
      prim(Prim.add, [lit(true), lit(1)]),
      prim(Prim.not, [lit(1)]),
      prim(Prim.or, [lit(false), lit(true)]),
      prim(Prim.not, [lit(false)]),
    ];
    for (final t in cases) {
      expect(outcome(() => run(t).value), outcome(() => kernel(t)), reason: '$t');
    }
  });

  test('a canonical NaN and a negative zero survive inline arithmetic', () {
    final nan = run(prim(Prim.mul, [lit(double.infinity), lit(0.0)]));
    expect(nan.kernelCalls, 0);
    // The kernel's canonical NaN is `double.nan`, whose sign bit is set.
    expect(f64Bits((nan.value as Float).x), f64Bits(double.nan));
    final z = run(prim(Prim.neg, [lit(0.0)])).value;
    expect(f64Bits((z as Float).x), f64Bits(-0.0));
  });

  test('an overflow goes to the runtime once', () {
    expect(run(prim(Prim.add, [lit(max), lit(1)])).kernelCalls, 1);
    expect(run(prim(Prim.add, [lit(max - 1), lit(1)])).kernelCalls, 0);
  });

  // A function that pushes and is called twice is one compiled body: each call passes the
  // state words in, and the pushes come out in the order of the calls.
  test('a function that pushes and is called twice runs natively', () {
    final say = lam([
      'm',
    ], let_('_', Push('stdout', var_('m')), prim(Prim.concat, [var_('m'), lit('!')])));
    final t = let_(
      'say',
      say,
      prim(Prim.tuple, [
        app(var_('say'), [lit('a')]),
        app(var_('say'), [lit('b')]),
      ]),
    );
    final (g, p) = planned(t);
    expect(count(g, 'lambda'), 1);
    World world() => World().output('stdout');
    final ev = Evaluator(world());
    final got = native.run(g, p, ev);
    final kev = Evaluator(world());
    expect(got.value, kev.run(t));
    expect(ev.world.log('stdout'), kev.world.log('stdout'));
    expect(ev.world.log('stdout').length, 2);
  });
}
