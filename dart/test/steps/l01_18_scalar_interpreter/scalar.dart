/// Step L1.18: the interpreter's scalar tier. Programs run through the L1 prelude words
/// (`String`, the checked casts, `abs`, `sum` and the string words), failures from several
/// operands merge into `#errs`, and floats print in the shortest form that reads back.
library;

import '../l01_16_elaboration/elab.dart';

/// The value of `x = <expr>;`, printed.
String x(String expr) => value('x = $expr;\n', 'x');
