/// The syntax tree of expressions (step L1.9), built from a parse tree (`parse.dart`).
///
/// A node of the parse tree records only its rule and tokens; here an expression is one node
/// per operation, with its operands. Parentheses group and leave no node; the grouped
/// expression's span includes them. A postfix chain is built left to right: a call with its
/// positional arguments, then its named ones, and whether it ends in `...`; an index `e[k]`; a
/// member `e.n` or `e?.n`. A uniform call `x.f(a)` stays a call of the member `x.f`, since
/// whether `f` is a field or a function is known only after name resolution (step L1.14). A
/// form not built yet is an error naming its layer.
library;

import 'dart:convert';

import 'lex.dart';
import 'parse.dart';
import 'src/unicode.dart';

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
  String toString() =>
      '${switch (radix) {
        2 => '0b',
        8 => '0o',
        16 => '0x',
        _ => '',
      }}$digits';
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
  String toString() =>
      '(str${[for (final p in parts) switch (p) {
          StrText(:final text) => ' ${quoted(text, '"')}',
          StrHole(:final e) => ' $e',
        }].join()})';
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
  String toString() =>
      '(call $callee${[for (final a in positional) ' $a', for (final (n, a) in named) ' ($n: $a)'].join()}'
      '${curry ? ' ...' : ''})';
}

/// An index `e[k]`.
final class Index extends Expr {
  final Expr e;
  final Expr key;

  Index(this.e, this.key, super.span);

  @override
  String toString() => '(index $e $key)';
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
  final b = _Builder(utf8.encode(text), tokens, tree);
  // Each node is built by a generator that yields the nodes it needs built and reads each
  // result from `_built`, so the depth of the text's nesting is bounded by memory alone.
  final stack = [b.node(n).iterator];
  while (stack.isNotEmpty) {
    if (stack.last.moveNext()) {
      final (by, k) = stack.last.current;
      stack.add(by.node(k).iterator);
    } else {
      stack.removeLast();
    }
  }
  return _built!;
}

/// The expression the last generator to finish built.
Expr? _built;

/// A node to build, and the builder of its tree.
typedef _Job = (_Builder, Node);

final class _Builder {
  final List<int> bytes;
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

  Span span(Node n) => (start: tokens[n.start].span.start, end: tokens[n.end - 1].span.end);

  String word(int i) => utf8.decode(bytes.sublist(tokens[i].span.start, tokens[i].span.end));

  /// The error for node `n`, of a form not built yet.
  BuildError later(Node n) =>
      BuildError(span(n), 'this form (${n.name}) is built from layer L${n.layer}');

  /// The operator token at `i`.
  String op(int i) => switch (tokens[i].tok) {
    Op(:final op) => op,
    Keyword(:final word) => word,
    _ => throw StateError('an operator token'),
  };

  Iterable<_Job> node(Node n) sync* {
    final kids = n.kids;
    switch ((n.name, n.alt)) {
      case ('Expr', 2) || ('Prefix', 1) || ('Primary', 0 || 2):
        yield (this, kids[0]);
      case ('Expr12', _) when kids.length == 1:
        yield (this, kids[0]);
      case ('Or' || 'And' || 'Additive' || 'Multiplicative', _) || ('Equality', 1):
        // A left-associative chain; each operator is the token before its right operand.
        yield (this, kids[0]);
        for (final k in kids.skip(1)) {
          final a = _built!;
          yield (this, k);
          _built = Binary(op(k.start - 1), a, _built!, (
            start: a.span.start,
            end: _built!.span.end,
          ));
        }
      case ('Relation', 2):
        switch (kids) {
          case [final r]:
            yield (this, r);
          case [final l, final tail] when tail.alt == 0:
            yield* binary(op(tail.start), l, tail.kids[0]);
          case [_, final tail]:
            throw later(tail);
        }
      case ('Reduce' || 'Range', _):
        if (kids.length > 1) throw later(kids[1]);
        yield (this, kids[0]);
      case ('Prefix', 0):
        yield (this, kids[0]);
        _built = Unary(op(n.start), _built!, span(n));
      case ('Power', _):
        if (kids case [final l, final r]) {
          yield* binary('**', l, r);
        } else {
          yield (this, kids[0]);
        }
      case ('Postfix', _):
        yield (this, kids[0]);
        for (final s in kids.skip(1)) {
          yield* suffix(_built!, s);
        }
      case ('Primary', 1):
        _built = AtomLit((tokens[n.start].tok as Atom).name, span(n));
      case ('Primary', 5):
        yield (this, kids[0]);
        _built!.span = span(n);
      case ('Name', _):
        _built = NameRef(word(n.start), span(n));
      case ('Literal', _):
        yield* literal(n);
      default:
        throw later(n);
    }
  }

  Iterable<_Job> binary(String op, Node l, Node r) sync* {
    yield (this, l);
    final a = _built!;
    yield (this, r);
    _built = Binary(op, a, _built!, (start: a.span.start, end: _built!.span.end));
  }

  Iterable<_Job> suffix(Expr of, Node s) sync* {
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
              yield (this, k.kids[0]);
              positional.add(_built!);
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
              yield (this, v);
              named.add((name.name, _built!));
            } else {
              named.add((name.name, name));
            }
          }
        }
        _built = Call(of, positional, named, curry, whole);
      case 1:
        yield (this, s.kids[0]);
        _built = Index(of, _built!, whole);
      case 2 || 3:
        _built = Member(of, word(s.end - 1), s.alt == 3, whole);
      default:
        throw later(s);
    }
  }

  Iterable<_Job> literal(Node n) sync* {
    final i = n.start;
    switch (tokens[i].tok) {
      case Int(:final radix, :final digits):
        _built = IntLit(radix, digits, span(n));
      case Float(:final text):
        _built = FloatLit(text, span(n));
      case Rat(:final text):
        _built = RatLit(text, span(n));
      case Keyword(:final word):
        _built = BoolLit(word == 'true', span(n));
      case Str(:final parts):
        final out = <StrPart>[];
        var hole = holes[i];
        for (final p in parts) {
          switch (p) {
            case TextPart(:final text):
              out.add(StrText(text));
            case Hole(:final tokens):
              final tree = this.tree.holes[hole++];
              yield (_Builder(bytes, tokens, tree), tree.root);
              out.add(StrHole(_built!));
          }
        }
        _built = StrLit(out, span(n));
      default:
        throw StateError('Literal = INT | FLOAT | RAT | STRING | true | false');
    }
  }
}
