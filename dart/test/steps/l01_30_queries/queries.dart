/// Step L1.30: the compiler as content-hash-keyed queries. The front end is keyed by the text;
/// a table row by the definitions its check reaches, so an edit recomputes only the rows whose
/// definitions changed, and every answer equals a fresh database's.
library;

import 'package:zed/query.dart';
import 'package:zed/testing.dart';

/// The checks of `text` under `db`, each as `line:col: ok` or `line:col: why`.
List<String> checks(Db db, String text) => [
  for (final o in testIn(db, text)) '${o.line}:${o.col}: ${o.failure ?? 'ok'}',
];

/// A pricing unit: a discount and a tax, each with its table, and a total over both.
const pricing = '''
discount(positional cents: int) = if cents >= 10000 { cents div 10 } else { 0 }
test { 5000 -> 0, 20000 -> 2000 }

tax(positional cents: int) = cents * 8 div 100
test { 10000 -> 800, 2500 -> 200 }

total(positional cents: int) = cents - discount(cents) + tax(cents - discount(cents))
test { 20000 -> 19440 }
''';
