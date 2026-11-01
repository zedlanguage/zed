/// Step L1.36: native code. Each planned graph compiles, by the JIT or to an object file from
/// the same generator, to x86-64 code that runs scalar nodes inline and every other node
/// through the runtime; every corpus row gives the interpreter's value and the counting
/// machine's counts.
library;

import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native show run, Outcome;
import 'package:zed/zir.dart' show Plan, Region, lower, plan;

/// [t] lowered and planned with fusion.
(Region, Plan) planned(Term t) {
  final g = lower(t);
  return (g, plan(g, true));
}

/// [t] run natively with no ports.
native.Outcome run(Term t) {
  final (g, p) = planned(t);
  return native.run(g, p, Evaluator(World()));
}

/// [t] run by the kernel with no ports.
Value kernel(Term t) => Evaluator(World()).run(t);
