/// What an edit recomputes, and that the answers stay those of a fresh database.
library;

import 'package:test/test.dart';
import 'package:zed/query.dart';

import 'queries.dart';

/// The counts of the three queries computed so far.
List<int> counts(Db db) => [for (final q in Query.values) db.computed(q)];

void main() {
  test('asking again recomputes nothing', () {
    final db = Db();
    final first = checks(db, pricing);
    expect(first, ['2:8: ok', '2:19: ok', '5:8: ok', '5:22: ok', '8:8: ok']);
    expect(counts(db), [1, 5, 0]);
    expect(checks(db, pricing), first);
    expect(counts(db), [1, 5, 0]);
  });

  test('a comment reruns the front end and no row', () {
    final db = Db();
    checks(db, pricing);
    final got = checks(db, '// prices in cents\n$pricing');
    // The rows' places move with the text; their results are reused.
    expect(got, ['3:8: ok', '3:19: ok', '6:8: ok', '6:22: ok', '9:8: ok']);
    expect(counts(db), [2, 5, 0]);
  });

  test('an edit reruns the rows that reach the changed definition', () {
    final db = Db();
    checks(db, pricing);
    // The tax rate goes to 10%: `tax`'s two rows and `total`'s row read `tax`; `discount`'s
    // two rows do not.
    final got = checks(db, pricing.replaceFirst('cents * 8 div 100', 'cents * 10 div 100'));
    expect(got, [
      '2:8: ok',
      '2:19: ok',
      '5:8: `10000 -> 800` of `tax`: the result is 1000',
      '5:22: `2500 -> 200` of `tax`: the result is 250',
      '8:8: `20000 -> 19440` of `total`: the result is 19800',
    ]);
    expect(counts(db), [2, 8, 0]);
  });

  test('a new row is the only row computed', () {
    final db = Db();
    checks(db, pricing);
    final got = checks(
      db,
      pricing.replaceFirst('20000 -> 2000 }', '20000 -> 2000, 10000 -> 1000 }'),
    );
    expect(got[2], '2:34: ok');
    expect(counts(db), [2, 6, 0]);
  });

  test('a rejected unit is kept with its diagnostics', () {
    final db = Db();
    const bad = 'tax(positional cents: int) = cents * "8";\n';
    final first = checks(db, bad);
    expect(first, hasLength(1));
    // The outcome carries the diagnostic's derivation, as `zedc test` prints it.
    expect(
      first[0],
      startsWith('1:30: `*` does not take (int, "8")\n  [1] 1:30: `cents` is int here\n'),
    );
    expect(checks(db, bad), first);
    expect(counts(db), [1, 0, 0]);
  });

  test('a wave row is reused until main or what it reads changes', () {
    const src =
        'shout(positional s: String) = upper(s) ++ "!";\n'
        'whisper(positional s: String) = lower(s);\n'
        'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- shout(stdin[1]);\n}\n'
        'test { "hi" -> "HI!\\n" }\n';
    final db = Db();
    expect(checks(db, src), ['6:8: ok']);
    // `whisper` is not read by `main`: the wave is reused.
    expect(checks(db, src.replaceFirst('lower(s)', 'lower(s) ++ "..."')), ['6:8: ok']);
    expect(counts(db), [2, 0, 1]);
    // `shout` is: the wave runs again.
    expect(checks(db, src.replaceFirst('"!"', '"!!"')), [
      '6:8: `"hi" -> "HI!\\n"` of `main`: port `stdout` writes "HI!!\\n"',
    ]);
    expect(counts(db), [3, 0, 2]);
  });

  test("every answer equals a fresh database's", () {
    final edits = [
      pricing,
      pricing.replaceFirst('cents div 10', 'cents div 5'),
      pricing.replaceFirst('cents div 10', 'cents div 5').replaceFirst('19440', '17280'),
      '// v2\n$pricing',
      pricing.replaceFirst('tax(cents - discount(cents))', 'tax(cents)'),
      pricing,
    ];
    final db = Db();
    for (final text in edits) {
      expect(checks(db, text), checks(Db(), text), reason: text);
    }
    // The last text is the first again: nothing is computed for it.
    final before = counts(db);
    checks(db, edits[0]);
    expect(counts(db), before);
  });
}
