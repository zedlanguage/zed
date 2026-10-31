/// Step L1.21: the `test { }` runner. From here on a test of what a Zed program computes is
/// written in Zed: each step's `zed/` folder holds units whose tables and ✗ marks `zedc test`
/// checks. The tests here check the runner itself.
library;

import 'package:zed/testing.dart';

/// The checks of `text`, each as `line:col: ok` or `line:col: why`.
List<String> checks(String text) => [
  for (final o in testUnit(text)) '${o.line}:${o.col}: ${o.failure ?? 'ok'}',
];
