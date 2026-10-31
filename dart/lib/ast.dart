/// The syntax tree of expressions (steps L1.9 and L1.10), built from a parse tree
/// (`parse.dart`).
///
/// A node of the parse tree records only its rule and tokens; here an expression is one node
/// per operation, with its operands. Parentheses group and leave no node; the grouped
/// expression's span includes them. A postfix chain is built left to right: a call with its
/// positional arguments, then its named ones, and whether it ends in `...`; an index `e[k]`; a
/// member `e.n` or `e?.n`. A uniform call `x.f(a)` stays a call of the member `x.f`, since
/// whether `f` is a field or a function is known only after name resolution (step L1.14). A
/// lambda keeps its parameters as written; an `else` chain is built left to right. A form not
/// built yet is an error naming its layer.
library;

import 'dart:convert';

import 'lex.dart';
import 'parse.dart';
import 'src/unicode.dart';

part 'src/ast/types.dart';

/// An expression and its span.
sealed class Expr {
  /// Its text; a grouping's parentheses widen it.
  Span span;

  Expr(this.span);
}

/// An integer: its base and digits.
final class IntLit extends Expr {
  final int radix;
  final String digits;

  IntLit(this.radix, this.digits, super.span);

  @override
  String toString() {
    final prefix = switch (radix) {
      2 => '0b',
      8 => '0o',
      16 => '0x',
      _ => '',
    };
    return '$prefix$digits';
  }
}

/// A float, as its decimal text.
final class FloatLit extends Expr {
  final String text;

  FloatLit(this.text, super.span);

  @override
  String toString() => text;
}

/// An exact rational, as its decimal text.
final class RatLit extends Expr {
  final String text;

  RatLit(this.text, super.span);

  @override
  String toString() => '${text}r';
}

/// A string: its text and its holes.
final class StrLit extends Expr {
  final List<StrPart> parts;

  StrLit(this.parts, super.span);

  @override
  String toString() {
    final ps = [
      for (final p in parts)
        switch (p) {
          StrText(:final text) => ' ${quoted(text, '"')}',
          StrHole(:final e) => ' $e',
        },
    ];
    return '(str${ps.join()})';
  }
}

/// A part of a string expression.
sealed class StrPart {}

final class StrText extends StrPart {
  final String text;

  StrText(this.text);
}

/// A `${…}` hole.
final class StrHole extends StrPart {
  final Expr e;

  StrHole(this.e);
}

/// `true` or `false`.
final class BoolLit extends Expr {
  final bool value;

  BoolLit(this.value, super.span);

  @override
  String toString() => '$value';
}

/// An atom, without its `#`.
final class AtomLit extends Expr {
  final String name;

  AtomLit(this.name, super.span);

  @override
  String toString() => '#$name';
}

/// A name.
final class NameRef extends Expr {
  final String name;

  NameRef(this.name, super.span);

  @override
  String toString() => name;
}

/// A prefix operator, `-` or `!`, and its operand.
final class Unary extends Expr {
  final String op;
  final Expr e;

  Unary(this.op, this.e, super.span);

  @override
  String toString() => '($op $e)';
}

/// A binary operator and its operands.
final class Binary extends Expr {
  final String op;
  final Expr a;
  final Expr b;

  Binary(this.op, this.a, this.b, super.span);

  @override
  String toString() => '($op $a $b)';
}

/// A call `f(…)`: its positional arguments, then its named ones in written order (`x:` is
/// `x: x`), and whether they end in `...`, currying the named parameters left out.
final class Call extends Expr {
  final Expr callee;
  final List<Expr> positional;
  final List<(String, Expr)> named;
  final bool curry;

  Call(this.callee, this.positional, this.named, this.curry, super.span);

  @override
  String toString() {
    final args = [for (final a in positional) ' $a', for (final (n, a) in named) ' ($n: $a)'];
    return '(call $callee${args.join()}${curry ? ' ...' : ''})';
  }
}

/// An index `e[k]`.
final class Index extends Expr {
  final Expr e;
  final Expr key;

  Index(this.e, this.key, super.span);

  @override
  String toString() => '(index $e $key)';
}

/// A tuple `(a, b, …)`.
final class Tuple extends Expr {
  final List<Expr> items;

  Tuple(this.items, super.span);

  @override
  String toString() => '(tuple ${items.join(' ')})';
}

/// A lambda `x -> e` or `(params) -> e`.
final class Lambda extends Expr {
  final List<Param> params;
  final Expr body;

  Lambda(this.params, this.body, super.span);

  @override
  String toString() => '(fn (${params.join(' ')}) $body)';
}

/// A type test `e is T`, or `e is not T` when `negated`.
final class Is extends Expr {
  final Expr of;
  final TypeExpr type;
  final bool negated;

  Is(this.of, this.type, this.negated, super.span);

  @override
  String toString() => '(is ${negated ? 'not ' : ''}$of $type)';
}

/// `e else d`, or `e else #a -> d` with its atom pattern; with no pattern, every loose atom
/// member is replaced.
final class Else extends Expr {
  final Expr of;
  final Pattern? pattern;
  final Expr fallback;

  Else(this.of, this.pattern, this.fallback, super.span);

  @override
  String toString() => '(else $of ${pattern == null ? '' : '$pattern '}$fallback)';
}

/// A member `e.n`, or `e?.n` when `safe`, which passes an atom member of the value's type
/// through.
final class Member extends Expr {
  final Expr of;
  final String name;
  final bool safe;

  Member(this.of, this.name, this.safe, super.span);

  @override
  String toString() => '(${safe ? '?.' : '.'} $of $name)';
}

/// One step of a derivation: a place in the source and what holds there.
typedef Note = ({Span span, String text});

/// Why an expression could not be built.
final class BuildError implements Exception {
  final Span span;
  final String message;

  /// How the checker reached it: each constraint and step, in the order it met them.
  final List<Note> notes;

  BuildError(this.span, this.message, [this.notes = const []]);

  @override
  String toString() => message;
}

/// The expression of `tree`, parsed as `Expr` from `tokens` of `text`.
Expr build(String text, List<Token> tokens, Tree tree) => expr(text, tokens, tree, tree.root);

/// The expression of node `n` of `tree`, a node of a rule from `Expr` down to `Primary`.
Expr expr(String text, List<Token> tokens, Tree tree, Node n) {
  _run(_Builder(utf8.encode(text), tokens, tree).node(n));
  return _expr;
}

/// Each part of the tree is built by a generator that yields the generators of the parts it
/// needs and reads each one's result from `_got`, then leaves its own there. They run on an
/// explicit stack, so the depth of the text's nesting is bounded by memory alone.
typedef _Steps = Iterable<Iterable<Object?>>;

void _run(_Steps steps) {
  final stack = [steps.iterator];
  while (stack.isNotEmpty) {
    if (stack.last.moveNext()) {
      stack.add((stack.last.current as _Steps).iterator);
    } else {
      stack.removeLast();
    }
  }
}

/// What the last generator to finish built.
Object? _got;

Expr get _expr => _got as Expr;

final class _Builder with _Types {
  final List<int> bytes;
  @override
  final List<Token> tokens;
  final Tree tree;

  /// For each token, the index in `tree.holes` of its first hole.
  final List<int> holes = [];

  _Builder(this.bytes, this.tokens, this.tree) {
    var count = 0;
    for (final t in tokens) {
      holes.add(count);
      if (t.tok case Str(:final parts)) count += parts.whereType<Hole>().length;
    }
  }

  @override
  Span span(Node n) => (start: tokens[n.start].span.start, end: tokens[n.end - 1].span.end);

  @override
  String word(int i) => utf8.decode(bytes.sublist(tokens[i].span.start, tokens[i].span.end));

  /// The error for node `n`, of a form not built yet.
  @override
  BuildError later(Node n) =>
      BuildError(span(n), 'this form (${n.name}) is built from layer L${n.layer}');

  /// The operator token at `i`.
  String op(int i) => switch (tokens[i].tok) {
    Op(:final op) => op,
    Keyword(:final word) => word,
    _ => throw StateError('an operator token'),
  };

  @override
  _Steps node(Node n) sync* {
    final kids = n.kids;
    switch ((n.name, n.alt)) {
      case ('Expr', 2) || ('Prefix', 1) || ('Primary', 0 || 2):
        yield node(kids[0]);
      case ('Expr', 0):
        yield* lambda(n);
      case ('Expr12', _):
        yield node(kids[0]);
        for (final t in kids.skip(1)) {
          yield* elseTail(_expr, t);
        }
      case ('Or' || 'And' || 'Additive' || 'Multiplicative', _) || ('Equality', 1):
        // A left-associative chain; each operator is the token before its right operand.
        yield node(kids[0]);
        for (final k in kids.skip(1)) {
          final a = _expr;
          yield node(k);
          _got = Binary(op(k.start - 1), a, _expr, (start: a.span.start, end: _expr.span.end));
        }
      case ('Relation', 2):
        switch (kids) {
          case [final r]:
            yield node(r);
          case [final l, final tail] when tail.alt == 0:
            yield* binary(op(tail.start), l, tail.kids[0]);
          case [final l, final tail] when tail.alt == 1:
            yield node(l);
            final of = _expr;
            yield type(tail.kids[0]);
            final t = _type;
            _got = Is(of, t, word(tail.start + 1) == 'not', (
              start: of.span.start,
              end: t.span.end,
            ));
          case [_, final tail]:
            throw later(tail);
        }
      case ('Reduce' || 'Range', _):
        if (kids.length > 1) throw later(kids[1]);
        yield node(kids[0]);
      case ('Prefix', 0):
        yield node(kids[0]);
        _got = Unary(op(n.start), _expr, span(n));
      case ('Power', _):
        if (kids case [final l, final r]) {
          yield* binary('**', l, r);
        } else {
          yield node(kids[0]);
        }
      case ('Postfix', _):
        yield node(kids[0]);
        for (final s in kids.skip(1)) {
          yield* suffix(_expr, s);
        }
      case ('Primary', 1):
        _got = AtomLit((tokens[n.start].tok as Atom).name, span(n));
      case ('Primary', 5):
        yield node(kids[0]);
        _expr.span = span(n);
      case ('Primary', 6):
        final items = <Expr>[];
        for (final k in kids) {
          yield node(k);
          items.add(_expr);
        }
        _got = Tuple(items, span(n));
      case ('Name', _):
        _got = NameRef(word(n.start), span(n));
      case ('Literal', _):
        yield* literal(n);
      default:
        throw later(n);
    }
  }

  _Steps binary(String op, Node l, Node r) sync* {
    yield node(l);
    final a = _expr;
    yield node(r);
    _got = Binary(op, a, _expr, (start: a.span.start, end: _expr.span.end));
  }

  /// A lambda: `Name '->' body` or `'(' Params? ')' '->' body`.
  _Steps lambda(Node n) sync* {
    final kids = n.kids[0].kids;
    final params = <Param>[];
    switch (kids) {
      case [final p, _] when p.name == 'Name':
        params.add(Param(word(p.start), false, null, null, span(p)));
      case [final p, _]:
        for (final k in p.kids) {
          yield param(k);
          params.add(_got as Param);
        }
    }
    yield node(kids.last);
    _got = Lambda(params, _expr, span(n));
  }

  /// `of` followed by the `ElseTail` node `t`.
  _Steps elseTail(Expr of, Node t) sync* {
    Pattern? pattern;
    if (t.kids case [final p, _]) {
      yield this.pattern(p);
      pattern = _got as Pattern;
    }
    yield node(t.kids.last);
    _got = Else(of, pattern, _expr, (start: of.span.start, end: _expr.span.end));
  }

  _Steps suffix(Expr of, Node s) sync* {
    final whole = (start: of.span.start, end: tokens[s.end - 1].span.end);
    switch (s.alt) {
      case 0:
        final positional = <Expr>[];
        final named = <(String, Expr)>[];
        var curry = false;
        if (s.kids case [final args]) {
          curry = word(args.end - 1) == '...';
          final seen = <String, Span>{};
          for (final k in args.kids) {
            if (k.name == 'PosArg') {
              if (k.alt == 0) throw later(k);
              yield node(k.kids[0]);
              positional.add(_expr);
              continue;
            }
            final name = NameRef(word(k.kids[0].start), span(k.kids[0]));
            if (seen[name.name] case final first?) {
              throw BuildError(name.span, 'the argument `${name.name}` is named twice', [
                (span: first, text: 'the first argument named `${name.name}`'),
              ]);
            }
            seen[name.name] = name.span;
            if (k.kids case [_, final v]) {
              yield node(v);
              named.add((name.name, _expr));
            } else {
              named.add((name.name, name));
            }
          }
        }
        _got = Call(of, positional, named, curry, whole);
      case 1:
        yield node(s.kids[0]);
        _got = Index(of, _expr, whole);
      case 2 || 3:
        _got = Member(of, word(s.end - 1), s.alt == 3, whole);
      default:
        throw later(s);
    }
  }

  _Steps literal(Node n) sync* {
    final i = n.start;
    switch (tokens[i].tok) {
      case Int(:final radix, :final digits):
        _got = IntLit(radix, digits, span(n));
      case Float(:final text):
        _got = FloatLit(text, span(n));
      case Rat(:final text):
        _got = RatLit(text, span(n));
      case Keyword(:final word):
        _got = BoolLit(word == 'true', span(n));
      case Str(:final parts):
        final out = <StrPart>[];
        var hole = holes[i];
        for (final p in parts) {
          switch (p) {
            case TextPart(:final text):
              out.add(StrText(text));
            case Hole(:final tokens):
              final tree = this.tree.holes[hole++];
              yield _Builder(bytes, tokens, tree).node(tree.root);
              out.add(StrHole(_expr));
          }
        }
        _got = StrLit(out, span(n));
      default:
        throw StateError('Literal = INT | FLOAT | RAT | STRING | true | false');
    }
  }
}
