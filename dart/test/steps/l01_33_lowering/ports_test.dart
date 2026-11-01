/// Ports: each port's state edge enters the root as an argument, passes from node to node in
/// the order of the effects, and leaves as a result; an arm that does not touch a port passes
/// its state through.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' hide print;

import 'lowering.dart';

/// The value of `t` and what it pushed to `stdout`, with `stdin` holding `line`.
(String, List<Value>) run(Term t, String line) {
  final ev = Evaluator(World().input('stdin', s(line)).output('stdout'));
  String v;
  try {
    v = '${ev.run(t)}';
  } on KernelError catch (e) {
    v = '$e';
  }
  return (v, ev.world.log('stdout'));
}

Value s(String x) => Str(x);

void same(Term t, String line) {
  final (v, log) = run(raise(lower(t)), line);
  final (want, wantLog) = run(t, line);
  expect(v, want);
  expect(log, wantLog);
}

/// Matches the edge `Out(node, port)`.
Matcher out(int node, int port) =>
    predicate<Src>((s) => s is Out && s.node == node && s.port == port, 'Out($node, $port)');

/// Matches the edge `Arg(i)`.
Matcher arg(int i) => predicate<Src>((s) => s is Arg && s.i == i, 'Arg($i)');

void main() {
  test('two pushes thread one state edge', () {
    final t = let_(
      'a',
      push('stdout', prim(Prim.concat, [lit('hello, '), const Read('stdin')])),
      let_('b', push('stdout', lit('bye')), prim(Prim.tuple, [var_('a'), var_('b')])),
    );
    final g = lower(t);
    expect(g.kind, RegionKind.port);
    // The value is computed before the push takes the port, so `stdin` comes first.
    expect(g.args, [const StateEdge('stdin'), const StateEdge('stdout')]);
    final push2 = g.nodes.length - 2;
    expect(g.nodes[push2].inputs[0], out(push2 - 1, 1));
    expect(g.results[2], out(push2, 1));
    same(t, 'ada');
  });

  test('an arm that does not push passes the state through', () {
    final t = If(
      prim(Prim.eq, [const Read('stdin'), lit('x')]),
      push('stdout', lit('yes')),
      lit(const Atom('skip')),
    );
    final node = lower(t).nodes.last;
    expect(node.outputs[1], const StateEdge('stdout'));
    expect(node.regions[0].results[1], out(0, 1));
    expect(node.regions[1].results[1], arg(0));
    same(t, 'x');
    same(t, 'y');
  });

  test('a function that pushes and is called twice is one lambda that threads the state', () {
    final t = let_(
      'say',
      lam(['m'], push('stdout', var_('m'))),
      prim(Prim.tuple, [
        App(var_('say'), [lit('a')]),
        App(var_('say'), [lit('b')]),
      ]),
    );
    final g = lower(t);
    expect((count(g, 'port'), count(g, 'lambda'), count(g, 'apply')), (1, 1, 2));
    // The body takes the state after its parameter and returns it after its value.
    final body = g.nodes[0].regions[0];
    expect(body.args.length, 2);
    expect(body.args[1], const StateEdge('stdout'));
    expect(body.results[1], out(0, 1));
    // The second call takes the state the first gives.
    final (first, second) = (g.nodes[1], g.nodes[2]);
    expect(first.inputs[2], arg(0));
    expect(second.inputs[2], out(1, 1));
    expect(first.outputs[1], const StateEdge('stdout'));
    same(t, '');
    expect(run(t, '').$2, [s('a'), s('b')]);
  });

  test('a function that pushes and is called once is inlined', () {
    final t = let_('say', lam(['m'], push('stdout', var_('m'))), App(var_('say'), [lit('a')]));
    final g = lower(t);
    expect((count(g, 'port'), count(g, 'lambda')), (1, 0));
    same(t, '');
  });

  test('each arm passes through the ports it does not touch', () {
    // One arm pushes, the other reads: each arm returns both states, its own and the other's.
    final t = If(prim(Prim.lt, [lit(1), lit(2)]), push('stdout', lit('yes')), const Read('stdin'));
    final node = lower(t).nodes.last;
    expect(node.outputs.sublist(1), [const StateEdge('stdout'), const StateEdge('stdin')]);
    expect(node.regions[0].results.sublist(1), [out(0, 1), arg(1)]);
    expect(node.regions[1].results.sublist(1), [arg(0), out(0, 1)]);
    same(t, 'z');
  });
}
