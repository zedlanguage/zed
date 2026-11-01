/// Step L1.26: resolution rules 1, 3 and 4. Each declared function gets a signature from its
/// body; a bare numeric literal adopts the carrier an operator or a parameter expects,
/// exactly or not at all; an `is` test narrows the name it tests; a function argument fits
/// the function type its slot expects.
library;

import 'dart:convert';

import 'package:zed/check.dart';
import 'package:zed/resolve.dart';

import '../l01_16_elaboration/elab.dart';

/// The checker's findings on the unit `text`.
Info info(String text) {
  final stmts = stmtsOf(text);
  return check(stmts, resolve(stmts));
}

/// The signature of the declared function `name` in `text`, printed.
String sig(String text, String name) {
  final s = info(text).sigs.entries.where((e) => e.key.name == name).firstOrNull;
  if (s == null) throw StateError('no function `$name`');
  return '${s.value}';
}

/// The type errors of `text`, each `message [text]`.
List<String> typeErrors(String text) {
  final bytes = utf8.encode(text);
  return [
    for (final e in info(text).errors)
      '${e.message} [${utf8.decode(bytes.sublist(e.span.start, e.span.end))}]',
  ];
}
