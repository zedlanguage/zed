/// Step L1.34: memory. Each graph gets a plan of owned and borrowed edges with a dup before
/// each owned use but the last and a drop at each last use that borrows; the machine runs the
/// graph under the plan and checks, after every node, that each live cell's count is the
/// number of references to it.
library;

import 'package:zed/kernel.dart';
import 'package:zed/zir.dart' as zir show plan, run;
import 'package:zed/zir.dart' show Plan, Region, Src, Out, Arg, Stats, lower;

/// A fresh string: the concatenation of [a] and [b], made when the program runs.
Term cat(String a, String b) => prim(Prim.concat, [lit(a), lit(b)]);

/// [t] lowered and planned, with fusion or not.
(Region, Plan) planned(Term t, bool fuse) {
  final g = lower(t);
  return (g, zir.plan(g, fuse));
}

/// [g] run by the machine under [p], with no ports: its value, printed, and its counts.
(String, Stats) run(Region g, Plan p) {
  final (v, s) = zir.run(g, p, Evaluator(World()));
  return ('$v', s);
}

/// [t] planned with fusion and run.
(String, Stats, Plan) machine(Term t) {
  final (g, p) = planned(t, true);
  final (v, s) = run(g, p);
  return (v, s, p);
}

/// [s] as the machine's errors print it.
String show(Src s) => switch (s) {
  Out(:final node, :final port) => '$node.$port',
  Arg(:final i) => 'argument $i',
  _ => '$s',
};
