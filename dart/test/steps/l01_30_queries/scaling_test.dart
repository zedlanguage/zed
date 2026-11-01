/// Queries at the rule of low complexity (DESIGN.md Part G). Asking again after an edit to one
/// definition of `n` reruns the front end and one row; finding each kept result by a search of
/// those kept, or keying each row by every definition of the unit, would take `O(n²)`.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/query.dart';

import '../../support/scaling.dart' as scaling;
import 'queries.dart';

/// `n` functions, each with one row, the first scaled by `k`.
String tables(int n, int k) => [
  for (var i = 0; i < n; i++)
    'f$i(positional x) = x * ${i == 0 ? k : 1} + $i test { 1 -> ${i == 0 ? k : i + 1} }\n',
].join();

void main() {
  test('asking again after an edit to one of many definitions scales', () {
    final dbs = <int, Db>{};
    final edits = <int, int>{};
    scaling.check("checking n functions' rows again after one edit", 200, (n) {
      var db = dbs[n];
      if (db == null) {
        db = dbs[n] = Db();
        checks(db, tables(n, 1));
      }
      final before = db.computed(Query.row);
      final k = edits[n] = (edits[n] ?? 1) + 1;
      final got = checks(db, tables(n, k));
      expect(got, hasLength(n));
      expect(got.every((o) => o.endsWith(': ok')), isTrue, reason: got.first);
      expect(db.computed(Query.row), before + 1);
    });
  });

  test('keeping many results and asking for each again scales', () {
    final keys = <int, List<Key>>{};
    scaling.check('keeping n results and asking for each again', 5000, (n) {
      final ks = keys[n] ??= [
        for (var i = 0; i < n; i++) key('row', [utf8.encode('$i')]),
      ];
      final db = Db();
      for (final (i, k) in ks.indexed) {
        db.row(Query.row, k, () => '$i');
      }
      for (final (i, k) in ks.indexed) {
        expect(db.row(Query.row, k, () => 'again'), '$i');
      }
      expect(db.computed(Query.row), n);
    });
  });
}
