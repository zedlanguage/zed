/// Step L1.33: kernel terms lowered to ZIR. Every test row of every corpus unit lowers to a
/// valid graph whose raised term has the original's value; repeated subexpressions are one
/// node; ports thread one state edge each through the regions that touch them; and a term the
/// graph cannot hold is refused with the reason.
library;

import 'package:zed/interp.dart' show prelude;
import 'package:zed/kernel.dart';
import 'package:zed/zir.dart';

import '../l01_16_elaboration/elab.dart';

/// The graph of definition `name` of the unit `text`.
Region graph(String text, String name) =>
    lower(prelude(elab(text).get(name) ?? (throw StateError('no definition `$name`'))));

/// The value of `t` with no ports, printed, or its error.
String evaluate(Term t) {
  try {
    return '${Evaluator(World()).run(t)}';
  } on KernelError catch (e) {
    return '$e';
  }
}

/// The value of `t` lowered and raised back.
String roundTrip(Term t) => evaluate(raise(lower(t)));

/// The number of nodes of `g` and its regions whose operation is named `op`.
int count(Region g, String op) {
  var n = 0;
  final todo = [g];
  while (todo.isNotEmpty) {
    for (final node in todo.removeLast().nodes) {
      if (node.op.name == op) n++;
      todo.addAll(node.regions);
    }
  }
  return n;
}

/// The number of nodes of `g` and its regions.
int nodes(Region g) {
  var n = 0;
  final todo = [g];
  while (todo.isNotEmpty) {
    for (final node in todo.removeLast().nodes) {
      n++;
      todo.addAll(node.regions);
    }
  }
  return n;
}

/// `port <- v`.
Term push(String port, Term v) => Push(port, v);
