// Statements and blocks (step L1.11): bindings with their targets, and `return`.
part of '../../ast.dart';

/// A block `{ … }`: its statements in written order, one of them its `return`.
final class Block extends Expr {
  final List<Stmt> stmts;

  Block(this.stmts, super.span);

  @override
  String toString() => '(block${[for (final s in stmts) ' $s'].join()})';
}

/// A statement and its text, its `;` included.
sealed class Stmt {
  final Span span;

  Stmt(this.span);
}

/// `a = e;`, or `a, b = e;` destructuring a tuple. A target is a name bound, or null for `_`,
/// the component discarded.
final class Bind extends Stmt {
  final List<String?> targets;
  final Expr value;

  Bind(this.targets, this.value, super.span);

  @override
  String toString() => '(= (${[for (final t in targets) t ?? '_'].join(' ')}) $value)';
}

/// `return e;` or `return a, b;`, the block's export; a trailing expression is `return e;`.
final class Return extends Stmt {
  final List<Expr> values;

  Return(this.values, super.span);

  @override
  String toString() => '(return${[for (final e in values) ' $e'].join()})';
}

Stmt get _stmt => _got as Stmt;

/// The builders of blocks and statements, each a generator run as `node` is.
mixin _Stmts {
  Span span(Node n);
  String word(int i);
  BuildError later(Node n);
  _Steps node(Node n);

  /// The block of node `n`, a `Block`: its statements, of which exactly one is a `return`.
  _Steps block(Node n) sync* {
    final stmts = <Stmt>[];
    Span? export;
    for (final k in n.kids) {
      if (k.name == 'Item') {
        yield item(k);
      } else {
        yield node(k);
        _got = Return([_expr], _expr.span);
      }
      final s = _stmt;
      if (s is Return) {
        if (export != null) {
          throw BuildError(s.span, 'a block exports once', [
            (span: export, text: "the block's first export"),
          ]);
        }
        export = s.span;
      }
      stmts.add(s);
    }
    if (export == null) {
      throw BuildError(
        span(n),
        'this block exports nothing: end it with an expression or `return e;`',
      );
    }
    _got = Block(stmts, span(n));
  }

  /// The statement of node `n`, an `Item`.
  _Steps item(Node n) sync* {
    if (n.alt != 3) throw later(n);
    final d = n.kids[0];
    switch ((d.alt, d.kids)) {
      case (7, final kids):
        final values = <Expr>[];
        for (final k in kids) {
          yield node(k);
          values.add(_expr);
        }
        _got = Return(values, span(n));
      case (15, [final b]) when b.alt == 1:
        // Binding = Target % ',' '=' Expr Boundary? ';'
        final targets = [
          for (final t in b.kids.take(b.kids.length - 1)) t.kids.isEmpty ? null : word(t.start),
        ];
        yield node(b.kids.last);
        _got = Bind(targets, _expr, span(n));
      case (11 || 14 || 15, [final k]):
        throw later(k);
      default:
        throw later(d);
    }
  }
}
