/// Postfix chains read left to right, and bind tighter than every operator.
library;

import 'package:test/test.dart';
import 'package:zed/ast.dart';

import 'ast.dart';

void check(List<(String, String)> cases) {
  final wrong = <String>[];
  for (final (text, want) in cases) {
    String got;
    try {
      got = '${ast(text)}';
    } on BuildError catch (e) {
      got = 'error: $e';
    }
    if (got != want) wrong.add('$text\n  got  $got\n  want $want');
  }
  expect(wrong, isEmpty, reason: wrong.join('\n'));
}

void main() {
  test('a digit then a letter is member access', () {
    check([
      // DESIGN.md: `y = 5.double.clamp(0, 8);  // ≡ clamp(double(5), 0, 8)`
      ('5.double.clamp(0, 8)', '(call (. (. 5 double) clamp) 0 8)'),
      ('2.5.floor', '(. 2.5 floor)'),
      ('0x1F.bits', '(. 0x1F bits)'),
      ('1.0e3.round()', '(call (. 1.0e3 round))'),
    ]);
  });

  test('suffixes apply left to right', () {
    check([
      ('grid[r][c]', '(index (index grid r) c)'),
      ('orders[id].total', '(. (index orders id) total)'),
      ("pos'.x", "(. pos' x)"),
      ('user?.address?.city', '(?. (?. user address) city)'),
      ('make()(3)', '(call (call make) 3)'),
      ('pair[0]', '(index pair 0)'),
      ('add[1]', '(index add 1)'),
      ('lines.map(trim).filter(nonEmpty)', '(call (. (call (. lines map) trim) filter) nonEmpty)'),
      ('#parseError(at: 3)', '(call #parseError (at: 3))'),
    ]);
  });

  test('a chain is an operand of the operators around it', () {
    check([
      // DESIGN.md: `accel(pos[i-1]) * dt ** 2`
      ('accel(pos[i - 1]) * dt ** 2', '(* (call accel (index pos (- i 1))) (** dt 2))'),
      ('-x.abs', '(- (. x abs))'),
      ('-x ** 2', '(- (** x 2))'),
      ('2 ** -1', '(** 2 (- 1))'),
      ('!done && xs.len > 0', '(&& (! done) (> (. xs len) 0))'),
      ('a - b - c', '(- (- a b) c)'),
      ('(a - b).abs', '(. (- a b) abs)'),
      ('total div n mod 7', '(mod (div total n) 7)'),
      ('x == y || p.ok', '(|| (== x y) (. p ok))'),
      (
        r'"${user.name} has ${cart.items.len} items"',
        '(str (. user name) " has " (. (. cart items) len) " items")',
      ),
      (
        r'label("${row.id}", "${row.qty * row.price}")',
        '(call label (str (. row id)) (str (* (. row qty) (. row price))))',
      ),
    ]);
  });
}
