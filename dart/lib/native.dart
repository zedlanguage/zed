/// Native code for planned ZIR graphs (step L1.36): each graph compiles to x86-64 machine
/// code, run now by the JIT or written to an object file from the same generator. The code
/// runs integer, float and boolean nodes inline and every other node through the runtime,
/// which allocates and counts as the counting machine does, so a native run gives the
/// interpreter's value and the machine's counts.
library;

import 'kernel.dart';
import 'run.dart' show RunError, Through;
import 'src/native/codegen.dart';
import 'src/native/elf.dart';
import 'src/native/jit.dart' as jit;
import 'src/native/tables.dart';
import 'zir.dart';

export 'src/native/heap.dart' show Heap, Obj, Stats, Tag, Word;
export 'src/native/jit.dart' show Outcome, run;
export 'src/native/ports.dart' show lines, write;
export 'src/native/rope.dart' show Rope;

/// The object file of graph [g] under [plan], for x86-64 Linux: `zed_root` exported, the
/// runtime's hooks imported.
List<int> object(Region g, Plan plan) => elf(generate(Tables(g, plan), g, plan));

/// Lowers, plans with [fuse] and runs a closed term natively: a [Through] for `testThrough`
/// and `Program.runThrough`.
Through through(bool fuse) => (Term t, Evaluator ev) {
  try {
    final g = lower(t);
    return jit.run(g, plan(g, fuse), ev).value;
  } on ZirError catch (e) {
    throw RunError(e.message);
  }
};
