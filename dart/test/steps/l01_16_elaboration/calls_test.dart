/// Calls of declared functions: positional and named arguments, defaults, `...`, uniform
/// calls and bracket sections.
library;

import 'package:test/test.dart';

import 'elab.dart';

const tax = 'tax(positional amount, rate = 8) = amount * rate div 100;\n';

void main() {
  test('a default is filled where the call omits it', () {
    const src = '${tax}a = tax(250);\nb = tax(250, rate: 10);\n';
    expect(value(src, 'a'), '20');
    expect(value(src, 'b'), '25');
    expect(term(src, 'a'), '{ amount = 250; rate = 8; tax(amount, rate) }');
    expect(term(src, 'b'), 'tax(250, 10)');
  });

  test('defaults read earlier parameters in dependency order', () {
    const src =
        'box(positional w, d = h, h = w) = w * h * d;\ncube = box(2);\nslab = box(2, d: 1);\n';
    expect(value(src, 'cube'), '8');
    expect(value(src, 'slab'), '4');
    expect(term(src, 'cube'), '{ w = 2; h = w; d = h; box(w, d, h) }');
  });

  test('named arguments go in parameter order whatever the written order', () {
    const src = 'span(lo, hi) = hi - lo;\nn = span(hi: 10, lo: 4);\n';
    expect(value(src, 'n'), '6');
    expect(term(src, 'n'), 'span(4, 10)');
  });

  test('curry is a lambda over the named parameters left out', () {
    const src =
        'greet(positional name, punct = "!", lead = "hi") = "\${lead}, \${name}\${punct}";\n'
        'h = greet("Al", lead: "yo", ...);\nq = h(punct: "?");\n';
    expect(term(src, 'h'), 'punct -> { name = "Al"; lead = "yo"; greet(name, punct, lead) }');
    expect(value(src, 'q'), '"yo, Al?"');
  });

  test('a receiver fills the first parameter of either kind', () {
    const src =
        'clamp(positional v, positional lo, positional hi) = '
        'if v < lo { lo } else if v > hi { hi } else { v };\n'
        'double(x) = x * 2;\n'
        'a = 12.clamp(0, 10);\nb = 5.double;\nc = 3.double.clamp(0, 5);\n';
    expect(value(src, 'a'), '10');
    expect(value(src, 'b'), '10');
    expect(value(src, 'c'), '5');
    expect(term(src, 'b'), 'double(5)');
    expect(term(src, 'c'), 'clamp(double(3), 0, 5)');
  });

  test('a member naming a prelude word is its call', () {
    const src = 'name = " Ada ";\nclean = name.trim;\nn = name.trim.len;\n';
    expect(term(src, 'clean'), 'trim(name)');
    expect(term(src, 'n'), 'len(trim(name))');
  });

  test('brackets index one level and fill no default', () {
    const src =
        'add(positional a, positional b) = a + b;\ninc = add[1];\nr = inc(41);\n'
        'neg(positional x) = 0 - x;\nm = neg[5];\npair = (7, 8);\nsecond = pair[1];\n';
    expect(term(src, 'inc'), r'$1 -> add(1, $1)');
    expect(value(src, 'r'), '42');
    expect(value(src, 'm'), '-5');
    expect(term(src, 'second'), 'tupleGet(pair, 1)');
    expect(value(src, 'second'), '8');
  });
}
