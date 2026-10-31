/// A block binds names and ends in its export.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/ast.dart';
import 'package:zed/lex.dart';
import 'package:zed/parse.dart';

import 'sx.dart';

void main() {
  test('bindings and the trailing expression', () {
    check([
      (
        'xs -> { n = xs.len; total = xs.sum; total / n }',
        '(fn (xs) (block (= (n) (. xs len)) (= (total) (. xs sum)) (return (/ total n))))',
      ),
      (
        'p -> { lo, hi = p.bounds; hi - lo }',
        '(fn (p) (block (= (lo hi) (. p bounds)) (return (- hi lo))))',
      ),
      ('p -> { _, hi = p.bounds; hi }', '(fn (p) (block (= (_ hi) (. p bounds)) (return hi)))'),
      ('parse(s) else { 0 }', '(else (call parse s) (block (return 0)))'),
      (
        'f(x -> { y = x * 2; y + 1 })',
        '(call f (fn (x) (block (= (y) (* x 2)) (return (+ y 1)))))',
      ),
      // Statement order has no meaning, so a binding may follow the export, which is stored
      // last, where the formatter writes it (step L1.13).
      ('x -> { y + 1; y = x }', 'syntax'),
      ('x -> { return y + 1; y = x * 2; }', '(fn (x) (block (= (y) (* x 2)) (return (+ y 1))))'),
    ]);
  });

  test('the semicolon rule', () {
    check([
      // A statement without its `;` does not parse.
      ('x -> { y = x y }', 'syntax'),
      // The trailing expression takes none; an expression statement is layer L6.
      ('x -> { y = x; y; }', 'error: this form (Decl) is built from layer L6'),
      // A brace holding only an expression is a display (`{ x }` is a set), not a block.
      ('({ x })', 'error: this form (Primary) is built from layer L2'),
    ]);
  });

  test('a block exports exactly once', () {
    check([
      (
        'x -> { return x; x + 1 }',
        "error: a block exports once; the block's first export at byte 7",
      ),
      (
        'x -> { return x; return x + 1; }',
        "error: a block exports once; the block's first export at byte 7",
      ),
      (
        'x -> { y = x * 2; return y; y + 1 }',
        "error: a block exports once; the block's first export at byte 18",
      ),
      (
        'x -> { y = x; }',
        'error: this block exports nothing: end it with an expression or `return e;`',
      ),
    ]);
  });

  test('a statement of a later layer names that layer', () {
    check([
      ('x -> { n: int = x; n }', 'error: this form (Binding) is built from layer L10'),
      ('x -> { y = x with z = 1; y }', 'error: this form (Boundary) is built from layer L6'),
      ('x -> { local y = x; y }', 'error: this form (Decl) is built from layer L2'),
    ]);
  });

  test('a wildcard target binds nothing', () {
    const text = 'p -> { _, hi = p.bounds; hi }';
    final tokens = lex(text);
    final e = build(text, tokens, parse(text, tokens, 'Expr', top));
    final Bind(:targets, :span) = ((e as Lambda).body as Block).stmts.first as Bind;
    expect(targets, [null, 'hi']);
    expect(utf8.decode(utf8.encode(text).sublist(span.start, span.end)), '_, hi = p.bounds;');
  });
}
