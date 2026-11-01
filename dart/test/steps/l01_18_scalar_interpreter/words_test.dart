/// `String`, `abs`, `sum` and the string words.
library;

import 'package:test/test.dart';

import '../l01_16_elaboration/elab.dart';
import 'scalar.dart';

void main() {
  test('`String` writes any value and leaves a string alone', () {
    expect(x('String("ok")'), '"ok"');
    expect(x('String(42)'), '"42"');
    expect(x('String(true)'), '"true"');
    expect(x('String(1r/3r)'), '"1r/3r"');
    expect(x('String((1, "a"))'), r'"(1, \"a\")"');
    expect(x(r'"${3} items at ${2.5}"'), '"3 items at 2.5"');
  });

  test('cleaning a user name', () {
    const src =
        'raw = "  Ada Lovelace \\n";\nname = trim(raw);\nkey = lower(name);\n'
        'shout = upper(name);\nsize = len(name);\n';
    expect(value(src, 'name'), '"Ada Lovelace"');
    expect(value(src, 'key'), '"ada lovelace"');
    expect(value(src, 'shout'), '"ADA LOVELACE"');
    expect(value(src, 'size'), '12');
  });

  test('string words are Unicode', () {
    expect(x('len("héllo")'), '5', reason: 'code points, not bytes');
    expect(x('upper("straße")'), '"STRASSE"');
    expect(x('lower("ÀÉÎ")'), '"àéî"');
    expect(x(r'trim("\u{3000}hi\t")'), '"hi"');
  });

  test('`abs` of each number kind', () {
    expect(x('abs(-7)'), '7');
    expect(x('abs(-2.5)'), '2.5');
    expect(x('abs(-1r/3r)'), '1r/3r');
    expect(x('abs(-9223372036854775807 - 1)'), '9223372036854775808');
  });

  test('summing an order', () {
    expect(x('sum((3, 4, 5))'), '12');
    expect(x('sum((1.5, 2.25))'), '3.75');
    expect(x('sum((1r/2r, 1r/3r))'), '5r/6r');
    expect(x('sum((9, int("x")))'), '#invalid');
    expect(errors('x = sum((1, 2.0));\n'), ['`sum` does not take (1, 2.0) [sum((1, 2.0))]']);
  });
}
