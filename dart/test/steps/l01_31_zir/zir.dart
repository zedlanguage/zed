/// Step L1.31: ZIR, the graph IR. Regions hold nodes in order; edges carry types, domains and
/// facets, or order a port's effects; the text form is flat and sorted, read back in any line
/// order, and the binary form gives back the same graph.
library;

import 'package:test/test.dart';
import 'package:zed/zir.dart' as zir;

/// The graph in `src`, checked, after asserting that it prints back as `src`, that its lines
/// read back in reverse order, and that its binary form decodes to it. Two graphs are compared
/// by their binary forms, which are equal exactly when the graphs are.
zir.Region round(String src) {
  final g = zir.parse(src);
  zir.validate(g);
  expect(zir.print(g), src);
  final lines = src.split('\n');
  if (lines.last.isEmpty) lines.removeLast();
  final reversed = [lines.first, ...lines.skip(1).toList().reversed].join('\n');
  final bytes = zir.encode(g);
  expect(zir.encode(zir.parse(reversed)), bytes);
  expect(zir.encode(zir.decode(bytes)), bytes);
  return g;
}

/// Why the text `src` is rejected, by the reader or the validator.
String rejected(String src) {
  try {
    zir.validate(zir.parse(src));
  } on zir.ZirError catch (e) {
    return e.message;
  }
  fail('the graph is valid');
}
