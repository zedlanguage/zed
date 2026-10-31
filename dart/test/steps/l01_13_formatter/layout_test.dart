/// The layout the formatter writes, on small programs written carelessly.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/format.dart';

import 'fmt.dart';

void check(String text, String want) => expect(fmt(text), want);

void main() {
  test('spacing and parentheses are normalized', () {
    check(
      'area(w,h)=w*h;\nmean(a,b)=((a+b))/2;\nf(x)=-(-x)**2;\n',
      'area(w, h) = w * h;\nmean(a, b) = (a + b) / 2;\nf(x) = -(-x) ** 2;\n',
    );
    check(
      'g(x)=(x-1)-(x-2);\nh(x)=x-(1-2);\nok(x)=(x<1)==(x<2);\n',
      'g(x) = x - 1 - (x - 2);\nh(x) = x - (1 - 2);\nok(x) = x < 1 == x < 2;\n',
    );
    // Equality and relations do not associate, so a grouped operand of either side stays
    // grouped.
    check('e(a,b,c)=(a==b)==c;\n', 'e(a, b, c) = (a == b) == c;\n');
  });

  test('a block puts its export last', () {
    check(
      'total(xs){return n+m;n=xs.length;m=1;}\n',
      'total(xs) {\n  n = xs.length;\n  m = 1;\n  n + m\n}\n',
    );
    check('pair(x){a=x;return a,a;}\n', 'pair(x) {\n  a = x;\n  return a, a;\n}\n');
  });

  test('a block of one export stays on one line', () {
    check(
      'sign(x)=if x<0 {-1} else if x==0 {0} else {1};\n',
      'sign(x) = if x < 0 { -1 } else if x == 0 { 0 } else { 1 };\n',
    );
    // As an operand a block opens with a statement at L1, so its export is written `return`.
    check('f(x)={return x;}+1;\n', 'f(x) = { return x; } + 1;\n');
  });

  test('main pushes to its ports', () {
    check(
      'main()->(stdout:Lines){name="Zed";stdout<-"hello, {name}";}\n',
      'main() -> (stdout: Lines) {\n  name = "Zed";\n  stdout <- "hello, {name}";\n}\n',
    );
  });

  test('test tables join into one line under the function', () {
    check('inc(x)=x+1 test{1->2} test{2->3}\n', 'inc(x) = x + 1\n  test { 1 -> 2, 2 -> 3 }\n');
    check(
      'twice(x){y=x+x;y} test{1->2}\n',
      'twice(x) {\n  y = x + x;\n  y\n}\n  test { 1 -> 2 }\n',
    );
  });

  test('lambdas, calls and else are written short', () {
    check(
      'f(xs)=map(xs,(x)->x+1);\ng(a)=h(a:a,b:2,...);\nd(p)=p else #none->0;\n',
      'f(xs) = map(xs, x -> x + 1);\ng(a) = h(a:, b: 2, ...);\nd(p) = p else #none -> 0;\n',
    );
    check(
      'k(t)=t is not (int|#none);\nm()=(1).abs;\n',
      'k(t) = t is not int | #none;\nm() = (1).abs;\n',
    );
  });

  test('comments stay with their statements', () {
    check(
      '// Totals.\ntotal(xs) {\n  return n; // the count\n\n  // xs is a list\n'
          '  n = xs.length;\n  // done\n}\n',
      '// Totals.\ntotal(xs) {\n  // xs is a list\n  n = xs.length;\n  n // the count\n'
          '  // done\n}\n',
    );
    check('f(x) = g(x, /* why */ 1); // after\n', 'f(x) = g(x, 1); /* why */ // after\n');
  });

  test('blank lines collapse to one', () {
    check('a() = 1;\n\n\n\nb() = 2;\nc() = 3;\n', 'a() = 1;\n\nb() = 2;\nc() = 3;\n');
  });

  test('parentheses keep a block from opening a branch', () {
    // An `if` condition's `{` would open the branch, and a default or a lambda body that starts
    // with `{` would be read as a block.
    check(
      'f(a,p)=if (p else {return a;}) {1} else {2};\n',
      'f(a, p) = if (p else { a }) { 1 } else { 2 };\n',
    );
    check(
      'g(p)=p else ({return 1;}+1);\nh(q)=x->({return q;}).k;\n',
      'g(p) = p else ({ return 1; } + 1);\nh(q) = x -> ({ return q; }.k);\n',
    );
  });

  test('a source that does not parse is reported at its line and column', () {
    expect(
      () => formatSource(utf8.encode('f(x) = 1;\ng(x) = ;\n')),
      throwsA(isA<FormatError>().having((e) => e.message, 'message', startsWith('2:8: expected '))),
    );
  });
}
