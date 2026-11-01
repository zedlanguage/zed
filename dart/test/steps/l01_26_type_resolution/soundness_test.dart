/// Type soundness (DESIGN.md rule 4): a program the checker accepts never meets a kernel type
/// error at run time. Each program here once passed the checker and then failed in the kernel;
/// each is now rejected before it runs, and each control, its well-typed twin, still runs.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/run.dart';

/// What one wave of the program `src` writes to `stdout` on `stdin`, or its run error.
String run(String src, String stdin) {
  final Program p;
  try {
    p = load(utf8.encode(src));
  } on RunError catch (e) {
    fail('$src: rejected: $e');
  }
  try {
    final w = p.run({'stdin': utf8.encode(stdin)}, (_) => throw StateError('no `Files` port'));
    return [for (final (_, b) in w.writes) utf8.decode(b, allowMalformed: true)].join();
  } on RunError catch (e) {
    return 'error: $e';
  }
}

/// The program with these definitions and this body of `main`.
String program(String defs, String body) =>
    '$defs\nmain(stdin: Lines) -> (stdout: Lines) {\n  $body\n}\n';

/// Checks that the program `src` is rejected.
void refused(String src) {
  try {
    load(utf8.encode(src));
  } on RunError {
    return;
  }
  fail('accepted, and on input 7 it gives ${jsonEncode(run(src, '7'))}:\n$src');
}

/// Checks that the program with these definitions and this `stdout` expression is rejected.
void rejected(String defs, String out) => refused(program(defs, 'stdout <- $out;'));

/// The program with these definitions and this `stdout` expression, run on `stdin`.
String runs(String defs, String out, String stdin) => run(program(defs, 'stdout <- $out;'), stdin);

const first = 'first(positional p) = p[0];';
const app = 'app(positional f) = f(1);';
const eq = 'eq(positional a, positional b) = a == b;';
const inc = 'inc(positional x) = x + 1;';

void main() {
  test('a tuple index of a non-tuple is rejected', () {
    rejected(first, r'"${first(5)}"');
    expect(runs(first, r'"${first((5, 6))}"', ''), '5\n');
  });

  test('a call of a non-function is rejected', () {
    rejected(app, r'"${app(5)}"');
    expect(runs(app, r'"${app(x -> x + 1)}"', ''), '2\n');
  });

  test('a function argument of the wrong arity is rejected', () {
    rejected(
      'f(positional x: int, positional y: int) = x + y;\ng(positional h) = h(1);',
      r'"${g(f)}"',
    );
    rejected('g(positional h) = h(1, 2);\ninc(positional x: int) = x + 1;', r'"${g(inc)}"');
  });

  test('a lambda parameter must take what it is passed', () {
    rejected('app(positional f) = f("a");', r'"${app((x: int) -> x + 1)}"');
    expect(runs(app, r'"${app((x: int) -> x + 1)}"', ''), '2\n');
  });

  test('functions are not compared with equals', () {
    rejected('$eq\n$inc', r'"${eq(inc, inc)}"');
    rejected(inc, r'"${inc == inc}"');
    expect(runs(eq, r'"${eq(1, 1)}"', ''), 'true\n');
  });

  test('one bounded variable takes one carrier', () {
    const add = 'add(positional a, positional b) = a + b;\nk(positional x: int) = x;';
    rejected(add, r'"${add(k(3), 2.5)}"');
    expect(runs(add, r'"${add(k(3), 4)}"', ''), '7\n');
  });

  test('a comparison of two kinds is rejected', () {
    rejected('lt(positional a, positional b) = a < b;', r'"${lt(1, "b")}"');
    rejected('', r'"${(1, "a") < ("b", 2)}"');
    rejected(inc, r'"${(inc, 1) < (inc, 2)}"');
    expect(runs('', r'"${(1, "a") < (1, "b")}"', ''), 'true\n');
  });

  test('a line of a Lines port is a string or an error', () {
    rejected('', r'"${stdin[1] + 1}"');
    expect(runs('', r'"${len(stdin[1]) else 0}"', 'abc'), '3\n');
  });

  test('an int power needs an exponent of at least zero', () {
    rejected('', r'"${2 ** -1}"');
    rejected('', r'"${(2 ** (int(stdin[1]) else 0)) div 1}"');
    expect(runs('', r'"${2 ** 3}"', ''), '8\n');
  });

  test('a prelude word takes its number of arguments', () {
    rejected('', r'"${len("ab", "c") + 1}"');
  });

  test('a function is not shown and not put in a tuple', () {
    rejected(inc, r'"${inc}"');
    rejected(inc, 'String(inc)');
    rejected(inc, r'"${(inc, 1)[1]}"');
    rejected('pair(positional a, positional b) = (a, b);\n$inc', r'"${pair(inc, 2)[1]}"');
  });

  test('a lambda is checked at each call', () {
    rejected('', r'"${(x -> x + 1)("a")}"');
    expect(runs('', r'"${(x -> x + 1)(2)}"', ''), '3\n');
    const f = 'f = x -> x[0];';
    rejected(f, r'"${f(5)}"');
    expect(runs(f, r'"${f((5, 6))}"', ''), '5\n');
  });

  test('a need passes through a generic call', () {
    const hg = 'h(positional t: (int, int)) = t[0];\ng(positional t) = h(t);';
    rejected(hg, r'"${g(5)}"');
    rejected(hg, r'"${g((1, "x"))}"');
    expect(runs(hg, r'"${g((1, 2))}"', ''), '1\n');
    const ka = '$app\nk(positional g) = app(g);';
    rejected(ka, r'"${k(5)}"');
    expect(runs(ka, r'"${k(x -> x * 2)}"', ''), '2\n');
    const m = 'map2(positional f, positional t) = (f(t[0]), f(t[1]));';
    rejected(m, r'"${map2(x -> x + 1, (1, "a"))}"');
    expect(runs(m, r'"${map2(x -> x + 1, (1, 2))}"', ''), '(2, 3)\n');
  });

  test('the results of two uses under one bound take one carrier', () {
    const h = 'h(positional t) = t[0] + t[1];';
    const k = '$h\nk(positional t) = h(t);\nr(positional x: f64) = x;';
    const cat = 'h(positional t) = t[0] ++ t[1];';
    rejected(h, r'"${h((1, 2.5))}"');
    rejected(k, r'"${k((1, r(2.5)))}"');
    rejected(cat, r'"${h(("a", 2))}"');
    expect(runs(h, r'"${h((1, 2))}"', ''), '3\n');
    expect(runs(k, r'"${k((r(1.5), r(2.5)))}"', ''), '4.0\n');
    expect(runs(cat, r'"${h(("a", "b"))}"', ''), 'ab\n');
    // What a use gives joins a variable an argument binds too.
    const f = 'f(positional c: bool, positional t, positional x) = if c { t[0] } else { x };';
    expect(runs(f, r'"${f(true, (1, 2), "a")}"', ''), '1\n');
  });

  test('a function applied to itself is checked once', () {
    // `w(w)` meets the need of `w` again inside its own check, on the same type: it holds.
    const src =
        'w(positional f) = f(f);\nspin = w(w);\n'
        'main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- "x";\n}\n';
    try {
      load(utf8.encode(src));
    } on RunError catch (e) {
      fail('$src: rejected: $e');
    }
    rejected('w(positional f) = f(f);', r'"${w(5)}"');
  });

  test('a section or a curried call checks what it leaves out when it is called', () {
    const add = 'add(positional a, positional b) = a + b;';
    expect(run(program(add, r'f = add[1]; stdout <- "${f(2)}";'), ''), '3\n');
    refused(program(add, r'f = add[1]; stdout <- "${f("x")}";'));
    const first = 'first(positional t, positional u) = t[0];';
    refused(program(first, r'f = first[5]; stdout <- "${f(1)}";'));
    const pick = 'pick(positional t, positional i) = t[i];';
    refused(program(pick, r'f = pick[(1, 2)]; stdout <- "${f(0)}";'));
    const greet = r'greet(positional name, punct = "!", lead = "hi") = "${lead}, ${name}${punct}";';
    const body = r'h = greet("Al", lead: "yo", ...); stdout <- h(punct: "?");';
    expect(run(program(greet, body), ''), 'yo, Al?\n');
    refused(program(greet, r'h = greet("Al", lead: "yo", ...); stdout <- h(punct: 5);'));
  });

  test('a returned function carries the needs of its parameters', () {
    const defs =
        'inc = x -> x + 1;\n'
        'compose(positional f, positional g) = x -> f(g(x));\n'
        'twice(positional f) = compose(f, f);\n'
        'len2(positional s) = len(s);';
    expect(run(program(defs, r'stdout <- "${twice(inc)(3)}";'), ''), '5\n');
    refused(program(defs, r'stdout <- "${twice(inc)("a")}";'));
    refused(program(defs, r'stdout <- "${twice(len2)("abc")}";'));
    const bang = r'h = twice(x -> x ++ "!"); stdout <- h("a");';
    expect(run(program(defs, bang), ''), 'a!!\n');
    const ok = r'h = compose(x -> x * 2, x -> x + 1); stdout <- "${h(4)}";';
    expect(run(program(defs, ok), ''), '10\n');
    refused(program(defs, r'h = compose(x -> x * 2, x -> x ++ "s"); stdout <- "${h("a")}";'));
  });

  test('a name an else pattern binds has the type of its payload', () {
    const parse =
        r'parse(positional text) = if text == "" { #parseError(line: 1, col: 0) } else { 42 };';
    const both =
        r'both = parse("") else #parseError(line:, col:) -> line * 100 + col; '
        r'stdout <- "${both}" else "?";';
    expect(run(program(parse, both), ''), '100\n');
    const wrap = 'wrap(positional v) = #w(v: v);';
    const five = r'r = wrap(5) else #w(v:) -> v + 1; stdout <- "${r}" else "?";';
    expect(run(program(wrap, five), ''), '6\n');
    refused(program(wrap, r'r = wrap("a") else #w(v:) -> v + 1; stdout <- "${r}";'));
    refused(program('', r'r = #e(x: "a") else #e(x:) -> x + 1; stdout <- "${r}";'));
    // Of two shapes, the name has the union of both.
    var pick = r'pick(positional c: bool) = if c { #e(x: 1) } else { #e(x: "a") };';
    refused(program(pick, r'r = pick(true) else #e(x:) -> x + 1; stdout <- "${r}";'));
    pick = 'pick(positional c: bool) = if c { #e(x: 1) } else { #e(x: 2, y: 3) };';
    const y = r'r = pick(false) else #e(y:) -> y + 1; stdout <- "${r}" else "?";';
    expect(run(program(pick, y), ''), '4\n');
    const nested = r'r = #o(i: #e(x: 2)) else #o(i: #e(x:)) -> x * 3; stdout <- "${r}" else "?";';
    expect(run(program('', nested), ''), '6\n');
    const v = 'v = #e(code: 5) else #e(code:) -> code;';
    expect(run(program(v, r'stdout <- String(v + 1) else "z";'), ''), '6\n');
    refused(program('$first\n$v', r'stdout <- String(first(v)) else "z";'));
    refused(program(v, r'stdout <- String(v ++ "a") else "z";'));
    refused(program('$app\n$v', r'stdout <- String(app(v)) else "z";'));
  });

  test('a generic else pattern binds the payload each call passes', () {
    const g = 'g(positional e) = e else #e(code:) -> code;';
    expect(run(program(g, r'stdout <- String(g(#e(code: 5)) + 1) else "z";'), ''), '6\n');
    expect(run(program(g, r'stdout <- String(g(3) + 1) else "z";'), ''), '4\n');
    refused(program(g, r'stdout <- String(g(#e(code: "a")) + 1) else "z";'));
    refused(program('$g\n$first', r'stdout <- String(first(g(#e(code: 5)))) else "z";'));
    const h = 'h(positional e) = e else #o(i: #e(x:)) -> x;';
    expect(run(program(h, r'stdout <- String(h(#o(i: #e(x: 2))) * 3) else "z";'), ''), '6\n');
    refused(program(h, r'stdout <- String(h(#o(i: #e(x: "s"))) * 3) else "z";'));
  });

  test('a self-application takes the least settled result', () {
    // Inside `w(w)` the inner use first gives nothing; the outer then gives 1, which settles.
    const settles = 'w(positional f) = if true { 1 } else { f(f) + 1 };\nspin = w(w);';
    expect(run(program(settles, r'stdout <- String(spin) else "z";'), ''), '1\n');
    // Here the inner use must give a string, and the outer gives 1 | String: not settled.
    const grows = 'w(positional f) = if true { 1 } else { f(f) ++ "a" };\nspin = w(w);';
    refused(program(grows, 'stdout <- "x";'));
  });
}
