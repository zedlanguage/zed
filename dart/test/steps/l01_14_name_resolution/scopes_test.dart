/// What opens a scope, what one scope may bind, and what each scope sees.
library;

import 'package:test/test.dart';
import 'package:zed/resolve.dart';

import 'res.dart';

void main() {
  test('rebinding in one scope is an error and a nested scope may shadow', () {
    // EXAMPLES.md [d4] sec:lexical — single assignment
    expect(errors('f(x) { y = x + 1; y = y * 2; z = { y = 0; y }; return y + z; }'), [
      '`y` is already bound in this scope [y = y * 2;]; the first binding of `y` [y = x + 1;]',
    ]);
  });

  test("a parameter and the body block's statements share one scope", () {
    expect(errors('clean(s) { s = trim(s); return s; }'), [
      '`s` is already bound in this scope [s = trim(s);]; the first binding of `s` [s]',
    ]);
    expect(at('clean(s) { t = { s = trim(s); s }; return t; }', 's', 3), ['binding s = trim(s);']);
  });

  test('functions of one name with different parameter types form an overload set', () {
    expect(at('show(n: int) = n; show(s: String) = s; out = show(1);', 'show', 2), [
      'function show(n: int) = n;',
      'function show(s: String) = s;',
    ]);
    expect(errors('show(n: int) = n; show(m: int) = m;'), [
      '`show` is already declared in this scope with these parameter types '
          '[show(m: int) = m;]; the first `show` with these parameter types [show(n: int) = n;]',
    ]);
  });

  test("a lambda's parameter shadows an outer name", () {
    const text = 'x = 10; inc = x -> x + 1; y = x;';
    expect(at(text, 'x', 2), ['param x']);
    expect(at(text, 'x', 3), ['binding x = 10;']);
  });

  test("a parameter's type and default see the parameters but not the body", () {
    const text = 'clamp(v: int, lo: int = 0, hi: int = lo + 100) { m = 1; return v; }';
    expect(at(text, 'lo', 1), ['param lo: int = 0']);
    expect(errors('f(a: int = m) { m = 1; return a; }'), ['`m` is not defined [m]']);
  });

  test('test cases are read in the scope around the function', () {
    expect(at('two = 2; double(x) = two * x test { 1 -> two }', 'two', 2), ['binding two = 2;']);
    expect(errors('double(x) = 2 * x test { x -> 2 }'), ['`x` is not defined [x]']);
  });

  test('an else pattern binds its fields in its default', () {
    const text =
        'pos = 1; n = parse(s) else #syntaxError(pos:) -> pos; m = pos; s = "1"; parse(t) = t;';
    expect(at(text, 'pos', 2), ['pattern #syntaxError(pos:)']);
    expect(at(text, 'pos', 3), ['binding pos = 1;']);
  });

  test('a push names an output port of its function', () {
    expect(at('main(stdin: Lines) -> (stdout: Lines) { stdout <- stdin; }', 'stdout', 1), [
      'port stdout: Lines',
    ]);
    expect(errors('main() { stdout <- "hi"; }'), ['`stdout` is not defined [stdout <- "hi";]']);
  });

  test('a member whose name is in scope is recorded for the uniform call', () {
    // DESIGN.md: the uniform call `x.f(a)` is `f(x, a)`; a field is told apart at L1.16
    const text = 'twice(x) = x * 2; p = 3; a = p.twice; b = p.size;';
    final r = run(text);
    Ref? member(String m) {
      final start = text.indexOf(m);
      return r.uses[(start: start, end: start + m.length)];
    }

    expect(member('p.twice'), isA<Bound>().having((b) => b.binders[0].name, 'name', 'twice'));
    expect(member('p.size'), isNull);
  });

  test('a binding that names itself resolves to itself', () {
    // the cycle `x = x + 1` is reported by a later step; resolution ties the name to its binder
    expect(at('x = x + 1;', 'x', 1), ['binding x = x + 1;']);
  });
}
