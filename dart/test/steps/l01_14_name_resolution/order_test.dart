/// The resolution order: block scopes, innermost outward; the unit's top level; the prelude.
library;

import 'package:test/test.dart';
import 'package:zed/resolve.dart';

import 'res.dart';

void main() {
  test('the innermost block that binds a name wins', () {
    const text = 'f(x) { y = x + 1; z = { y = 0; y + 1 }; return y + z; }';
    expect(at(text, 'y', 2), ['binding y = 0;']);
    expect(at(text, 'y', 3), ['binding y = x + 1;']);
  });

  test("a name not in a block is found in the unit's top level", () {
    const text = 'rate = 3; total(n) { k = n * rate; return k; }';
    expect(at(text, 'rate', 1), ['binding rate = 3;']);
    expect(at(text, 'n', 1), ['param n']);
  });

  test('a name the unit does not bind is found in the prelude', () {
    expect(at('name = "Ada"; size = len(name);', 'len', 0), ['prelude len']);
  });

  test("a unit's own name shadows a prelude word", () {
    // DESIGN.md: a program's own name shadows it (`scan = 0` declares a variable at any layer)
    const text = 'len(s) = 0; size = len("Ada"); scan = 0; next = scan + 1;';
    expect(at(text, 'len', 1), ['function len(s) = 0;']);
    expect(at(text, 'scan', 1), ['binding scan = 0;']);
  });

  test('a prelude word of a later layer is an error naming the layer', () {
    expect(errors('evens(xs) = where(xs, x -> x mod 2 == 0); best = sort(evens);'), [
      '`where` is a prelude word of layer L3 [where]',
      '`sort` is a prelude word of layer L5 [sort]',
    ]);
  });

  test('statement order does not matter', () {
    const text = 'total = price + tax; tax = price div 10; price = 200;';
    expect(at(text, 'price', 0), ['binding price = 200;']);
    expect(at(text, 'tax', 0), ['binding tax = price div 10;']);
  });

  test('a name bound nowhere is an error', () {
    expect(errors('total = price + 1; shown = total.price;'), ['`price` is not defined [price]']);
  });

  test('a type name resolves to the prelude and a unit declares none at L1', () {
    expect(errors('half(n: int) = n div 2; ok(p: Point) = p;'), [
      'the type `Point` is not defined [Point]',
    ]);
    expect(run('main(stdin: Lines) -> (stdout: Lines) { stdout <- stdin; }'), isA<Resolution>());
  });
}
