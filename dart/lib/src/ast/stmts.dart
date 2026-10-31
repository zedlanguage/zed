// Statements and blocks (step L1.11): bindings with their targets, and `return`; and
// declarations (step L1.12): functions with their `test` tables, and the push `p <- e`.
part of '../../ast.dart';

/// A block `{ … }`: its statements in written order, except that its `return` is last (none in
/// a function's body block that only pushes).
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

/// `p <- e;`, the whole value `e` pushed to the port `p`.
final class Push extends Stmt {
  final String port;
  final Expr value;

  Push(this.port, this.value, super.span);

  @override
  String toString() => '(<- $port $value)';
}

/// A function: `f(params) = e;` or `f(params) { … }`, either followed by `test` tables.
final class FunctionDef extends Stmt {
  final String name;
  final List<Param> params;

  /// Its output ports, `-> (stdout: Lines)`, if declared.
  final List<Port>? ports;

  /// Whether its body is an equation `= e`; otherwise it is a block, which may export
  /// nothing, as a `main` that only pushes does.
  final bool equation;
  final Expr body;

  /// The cases of its `test` tables, `input -> expected`, in written order.
  final List<(Expr, Expr)> tests;

  FunctionDef(this.name, this.params, this.ports, this.equation, this.body, this.tests, super.span);

  /// `(def f (x (y: int)) (-> (stdout: Lines)) = e (test (a b) …))`, the `=` for an equation.
  @override
  String toString() =>
      '(def $name (${params.join(' ')})'
      '${ports == null ? '' : ' (-> ${ports!.join(' ')})'}'
      ' ${equation ? '= ' : ''}$body'
      '${tests.isEmpty ? '' : ' (test${[for (final (a, b) in tests) ' ($a $b)'].join()})'})';
}

/// An output port of a function's header: `stdout: Lines`.
final class Port {
  final String name;
  final TypeExpr type;
  final Span span;

  Port(this.name, this.type, this.span);

  @override
  String toString() => '($name: $type)';
}

Stmt get _stmt => _got as Stmt;

/// The builders of blocks and statements, each a generator run as `node` is.
mixin _Stmts {
  Span span(Node n);
  String word(int i);
  BuildError later(Node n);
  _Steps node(Node n);
  _Steps type(Node n);
  _Steps params(Node n, List<Param> out);

  /// The block of node `n`, a `Block`: its statements, of which at most one is a `return`, and
  /// exactly one when `exportNeeded`, as for a block that is an expression. The export is stored
  /// last, where the formatter writes it (step L1.13); the order of the others is kept.
  _Steps block(Node n, bool exportNeeded) sync* {
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
    final i = stmts.indexWhere((s) => s is Return);
    if (i >= 0) stmts.add(stmts.removeAt(i));
    if (exportNeeded && export == null) {
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
      case (11, [final f]):
        yield* function(f, span(n));
      case (14, [final p]) when p.alt == 1:
        yield node(p.kids[1]);
        _got = Push(word(p.kids[0].start), _expr, span(n));
      case (14 || 15, [final k]):
        throw later(k);
      default:
        throw later(d);
    }
  }

  /// The function of node `n`, a `Function`: `Name '(' Params? ')' Result? Body`.
  _Steps function(Node n, Span whole) sync* {
    final params = <Param>[];
    List<Port>? ports;
    for (final k in n.kids.sublist(1, n.kids.length - 1)) {
      if (k.name == 'Params') {
        yield* this.params(k, params);
      } else if (k.alt == 0) {
        ports = [];
        for (final p in k.kids) {
          yield type(p.kids[1]);
          ports.add(Port(word(p.kids[0].start), _type, span(p)));
        }
      } else {
        throw later(k);
      }
    }
    // Body = '=' Expr (';' | Trailer+) | Block Trailer*
    final body = n.kids.last;
    final equation = word(body.start) == '=';
    if (equation) {
      yield node(body.kids[0]);
    } else {
      yield* block(body.kids[0], false);
    }
    final value = _expr;
    final tests = <(Expr, Expr)>[];
    for (final t in body.kids.skip(1)) {
      if (t.alt != 0) throw later(t);
      for (final c in t.kids) {
        yield node(c.kids[0]);
        final input = _expr;
        yield node(c.kids[1]);
        tests.add((input, _expr));
      }
    }
    _got = FunctionDef(word(n.kids[0].start), params, ports, equation, value, tests, whole);
  }
}
