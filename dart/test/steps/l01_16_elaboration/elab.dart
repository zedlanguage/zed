/// Step L1.16: elaboration of the L1 surface to kernel terms. Each program is elaborated and
/// its definitions evaluated by the kernel evaluator; where a term's shape is the point, it is
/// printed; and each error elaboration reports has a case.
library;

import 'dart:convert';

import 'package:zed/ast.dart';
import 'package:zed/elab.dart';
import 'package:zed/interp.dart';
import 'package:zed/kernel.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';
import 'package:zed/resolve.dart';

/// The statements of the unit `text`.
List<Stmt> stmtsOf(String text) {
  final tokens = lexFence(text);
  return unit(text, tokens, parse(text, tokens, 'Unit', top));
}

/// The elaboration of the unit `text`; throws [ElabErrors].
Unit elab(String text) {
  final stmts = stmtsOf(text);
  return elaborate(stmts, resolve(stmts));
}

/// `t` under the interpreter's prelude words (step L1.18).
Term withPrelude(Term t) => prelude(t);

/// The value of the definition `name` of `text`, printed.
String value(String text, String name) {
  final t = elab(text).get(name) ?? (throw StateError('no definition `$name`'));
  try {
    return '${Evaluator(World()).run(withPrelude(t))}';
  } on KernelError catch (e) {
    return 'error: $e';
  }
}

/// The term of the definition `name` of `text`, not closed over the others.
String term(String text, String name) =>
    '${elab(text).defs.firstWhere((d) => d.name == name).term}';

/// The errors of `text`, each `message [text]`.
List<String> errors(String text) {
  try {
    elab(text);
  } on ElabErrors catch (e) {
    final bytes = utf8.encode(text);
    return [
      for (final x in e.errors)
        '${x.message} [${utf8.decode(bytes.sublist(x.span.start, x.span.end))}]',
    ];
  }
  throw StateError('$text: elaborated without error');
}

/// The one error of `text`.
String one(String text) {
  final es = errors(text);
  if (es.length != 1) throw StateError('$text: $es');
  return es[0];
}
