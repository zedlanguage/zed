/// The reduced product against the interpreter on random bodies of one shape:
///
/// ```text
/// z = <integer term over x, y>;
/// if <test over x, y> { if <test over x, y> { 1 } else { 2 } } else { if z > c { 3 } else { 4 } }
/// ```
///
/// At every point of a window, the interpreter gives the value of `z` and the outcome of each
/// test, so the arms the point reaches; each such arm's scope must hold `x`, `y` and `z` at
/// the point, and so no point reaches an arm found unreachable.
library;

import 'package:zed/kernel.dart' hide Lattice;
import 'package:zed/store.dart';

import '../../support/instances.dart';
import '../l01_38_presburger/checks.dart' show boolTerm, intTerm;
import 'support.dart';

/// The window of `x` and `y`.
const lo = -6;
const hi = 6;

/// One body of the shape.
final class Shape {
  final Term z, outer, inner;
  final int c;

  Shape(this.z, this.outer, this.inner, this.c);

  factory Shape.random(Rng rng) =>
      Shape(intTerm(rng, 2), boolTerm(rng, 2), boolTerm(rng, 2), rng.int_(-6, 6));

  Term get last => prim(Prim.gt, [const Var('z'), lit(c)]);

  Term get body => Let('z', z, If(outer, If(inner, lit(1), lit(2)), If(last, lit(3), lit(4))));

  /// The six arms of the body's own tests, in the walk's order: those of `z`'s term come
  /// first.
  List<Arm> arms() {
    final all = _all(body);
    return all.sublist(all.length - 6);
  }

  @override
  String toString() => 'Shape(z: $z, outer: $outer, inner: $inner, c: $c)';
}

List<Arm> _all(Term body) => arms(body, ints(['x', 'y']));

/// The value of `t` at the state `env`; null when it fails.
Value? at(Term t, Map<String, Value> env) {
  for (final MapEntry(:key, :value) in env.entries) {
    t = Let(key, Lit(value), t);
  }
  try {
    return eval(t);
  } on KernelError {
    return null;
  }
}

/// Checks `arms` against the interpreter over the window: the number of (point, arm) pairs
/// checked; throws a [StateError] naming the first point that reaches an arm whose scope does
/// not hold it.
int check(Shape s, List<Arm> arms) {
  assert(arms.length == 6);
  var checked = 0;
  for (var x = lo; x <= hi; x++) {
    for (var y = lo; y <= hi; y++) {
      final env = <String, Value>{'x': Int(x), 'y': Int(y)};
      final z = at(s.z, env);
      if (z == null) continue;
      final List<int> reached;
      switch (at(s.outer, env)) {
        case Bool(value: true):
          switch (at(s.inner, env)) {
            case Bool(value: true):
              reached = [0, 1];
            case Bool(value: false):
              reached = [0, 2];
            default:
              continue;
          }
        case Bool(value: false):
          env['z'] = z;
          switch (at(s.last, env)) {
            case Bool(value: true):
              reached = [3, 4];
            case Bool(value: false):
              reached = [3, 5];
            default:
              continue;
          }
        default:
          continue;
      }
      env['z'] = z;
      for (final i in reached) {
        checked++;
        if (!arms[i].scope.contains(env)) {
          throw StateError(
            'the point $env reaches arm $i (test ${arms[i].guard}, outcome '
            '${arms[i].outcome}), whose scope does not hold it:\n${arms[i].scope}',
          );
        }
      }
    }
  }
  return checked;
}
