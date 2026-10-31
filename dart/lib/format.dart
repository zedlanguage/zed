/// The source formatter (step L1.13): a unit's statements written back as text, in one layout.
///
/// Two spaces per level of indentation and one statement per line. A block is written on one
/// line, `{ e }`, when it holds only its export and no comment; otherwise it has one statement
/// per line, its export last, so a block reads top-down to its result (DESIGN.md, "Blocks
/// bind; `return` exports"). A function's body block is always on several lines, and its
/// `test` cases are one table on one line, indented under it. An export of one value is the
/// trailing expression, of several `return a, b;`. Binary operators have a space each side,
/// `x: T` has none before the colon, a named argument `x: x` is written `x:`, and parentheses
/// are written only where the grammar needs them. A literal is written as it was spelled.
///
/// Comments are kept. A comment on its own line stays before the statement after it; one after
/// a statement, on its line, stays after it; one inside a statement but in none of its blocks
/// moves to the end of the statement. One blank line is kept where the source had one or more
/// between two statements, or before the comments that end a block.
library;

import 'dart:collection';
import 'dart:convert';
import 'dart:typed_data';

import 'ast.dart';
import 'lex.dart';
import 'parse.dart';
import 'source.dart';

/// The text of `unit`, parsed from `tokens` of `text`, in the formatter's layout, with the
/// comments of `text` kept.
String format(String text, List<Token> tokens, List<Stmt> unit) {
  final f = _Formatter(utf8.encode(text), comments(text, tokens));
  _run(f.stmts(unit, (start: 0, end: f.bytes.length), 0, true));
  return _doc.text;
}

/// Why a source file could not be formatted, at its line and column: `line:col: why`.
final class FormatError implements Exception {
  final String message;

  FormatError(this.message);

  @override
  String toString() => message;
}

/// The source file `bytes` in the formatter's layout; throws a [FormatError].
String formatSource(List<int> bytes) {
  final String text;
  try {
    text = load(bytes);
  } on Reject catch (e) {
    throw FormatError(e.render(bytes));
  }
  final b = utf8.encode(text);
  FormatError at(int offset, String why) {
    final (line, col) = lineCol(b, offset);
    return FormatError('$line:$col: $why');
  }

  try {
    final tokens = lex(text);
    return format(text, tokens, unit(text, tokens, parse(text, tokens, 'Unit', top)));
  } on LexError catch (e) {
    throw at(e.span.start, '$e');
  } on ParseError catch (e) {
    throw at(e.span.start, '$e');
  } on BuildError catch (e) {
    throw at(e.span.start, e.message);
  }
}

/// Precedence levels, from the loosest form of `Expr` to `Primary`, as sec:grammar orders
/// them; an operand written at a lower level than its position needs is parenthesized.
const _lambda = 0;
const _else = 1;
const _or = 2;
const _equality = 4;
const _relation = 5;
const _additive = 6;
const _prefix = 8;
const _power = 9;
const _postfix = 10;
const _primary = 11;

int _level(Expr e) => switch (e) {
  Lambda() => _lambda,
  Else() => _else,
  Binary(:final op) => _binaryLevel(op),
  Is() => _relation,
  Unary() => _prefix,
  Call() || Index() || Member() => _postfix,
  _ => _primary,
};

int _binaryLevel(String op) => switch (op) {
  '||' => _or,
  '&&' => _or + 1,
  '==' || '!=' => _equality,
  '<' || '<=' || '>' || '>=' => _relation,
  '+' || '-' || '++' => _additive,
  '*' || '/' || 'div' || 'mod' => _additive + 1,
  '**' => _power,
  _ => throw StateError('$op is no binary operator of layer L1'),
};

/// Whether `e`'s text starts with a block, which a lambda's body or an `else` default that is
/// not itself a block may not.
bool _startsWithBlock(Expr e) {
  while (true) {
    switch (e) {
      case Block():
        return true;
      case Binary(a: final of) ||
          Call(callee: final of) ||
          Index(e: final of) ||
          Member(:final of) ||
          Is(:final of) ||
          Else(:final of):
        e = of;
      default:
        return false;
    }
  }
}

/// Whether `e`, as an `if` condition, holds a block outside any bracket, which the grammar's
/// `HEAD` forbids there, since the condition's `{` opens the branch.
bool _headUnsafe(Expr e) {
  final todo = [e];
  while (todo.isNotEmpty) {
    switch (todo.removeLast()) {
      case Block():
        return true;
      case Else(:final of, fallback: final b) || Binary(a: final of, :final b):
        todo.addAll([of, b]);
      case Unary(e: final of) ||
          Is(:final of) ||
          Call(callee: final of) ||
          Index(e: final of) ||
          Member(:final of):
        todo.add(of);
      default:
    }
  }
  return false;
}

/// Where a block stands: a block as an operand must open with a statement, a branch (of an
/// `if`, an `else`, a lambda) need not, and a function's body is on several lines.
enum _Place { operand, branch, body }

/// A statement with the comments it keeps, and whether a blank line precedes it.
typedef _Entry = ({Stmt stmt, bool blank, List<Span> leading, List<Span> trailing});

String _indent(int n) => '  ' * n;

/// Each formatting function is a generator of the steps it needs done first, each a generator
/// itself, and leaves its text in [_got]; [_run] runs them on one explicit stack, so the depth
/// of the unit's nesting is bounded by memory alone.
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

/// What the last generator to finish wrote.
Object? _got;

_Doc get _doc => _got as _Doc;

final class _Formatter {
  final Uint8List bytes;

  /// The comments not yet written, by their first byte.
  final SplayTreeMap<int, Span> comments = SplayTreeMap();

  _Formatter(this.bytes, List<Span> all) {
    for (final c in all) {
      comments[c.start] = c;
    }
  }

  String slice(Span s) => utf8.decode(Uint8List.sublistView(bytes, s.start, s.end));

  int newlines(int from, int to) {
    var n = 0;
    for (var i = from; i < to; i++) {
      if (bytes[i] == 0x0a) n++;
    }
    return n;
  }

  /// The comments not yet written that start in `from..to`, now marked written.
  List<Span> take(int from, int to) {
    final out = <Span>[];
    for (
      var k = comments.firstKeyAfter(from - 1);
      k != null && k < to;
      k = comments.firstKeyAfter(k)
    ) {
      out.add(comments.remove(k)!);
    }
    return out;
  }

  /// The comments not yet written that follow byte `from` on its line, before `to`.
  List<Span> takeSameLine(int from, int to) {
    final out = <Span>[];
    var pos = from;
    while (true) {
      final k = comments.firstKeyAfter(pos - 1);
      if (k == null || k >= (to > pos ? to : pos) || newlines(pos, k) > 0) break;
      final c = comments.remove(k)!;
      out.add(c);
      pos = c.end;
    }
    return out;
  }

  bool hasComment(Span s) {
    final k = comments.firstKeyAfter(s.start - 1);
    return s.start < s.end && k != null && k < s.end;
  }

  /// The lines of `stmts`, which stand in `region` of the text, at indentation `ind`, each
  /// line ending in a newline. With `bare`, an export of one value is a trailing expression.
  _Steps stmts(List<Stmt> stmts, Span region, int ind, bool bare) sync* {
    // The comments and blank lines are found in source order, where the export may not be
    // last.
    final inOrder = [...stmts]..sort((a, b) => a.span.start.compareTo(b.span.start));
    final entries = <_Entry>[];
    var prev = region.start;
    for (var i = 0; i < inOrder.length; i++) {
      final s = inOrder[i];
      final leading = take(prev, s.span.start);
      final first = leading.firstOrNull?.start ?? s.span.start;
      final next = i + 1 < inOrder.length ? inOrder[i + 1].span.start : region.end;
      final blank = i > 0 && newlines(prev, first) > 1;
      final trailing = takeSameLine(s.span.end, next);
      prev = trailing.lastOrNull?.end ?? s.span.end;
      entries.add((stmt: s, blank: blank, leading: leading, trailing: trailing));
    }
    final ordered = [
      ...entries.where((e) => e.stmt is! Return),
      ...entries.where((e) => e.stmt is Return),
    ];
    final pad = _indent(ind);
    final out = <Object>[];
    for (final (i, e) in ordered.indexed) {
      if (e.blank && i > 0) out.add('\n');
      for (final c in e.leading) {
        out.add('$pad${slice(c)}\n');
      }
      out.add(pad);
      yield stmt(e.stmt, ind, bare);
      out.add(_doc);
      var afterLineComment = false;
      for (final c in [...take(e.stmt.span.start, e.stmt.span.end), ...e.trailing]) {
        final body = slice(c);
        out.add(afterLineComment ? '\n$pad$body' : ' $body');
        afterLineComment = body.startsWith('//');
      }
      out.add('\n');
    }
    final rest = take(prev, region.end);
    if (rest.isNotEmpty && out.isNotEmpty && newlines(prev, rest.first.start) > 1) out.add('\n');
    for (final c in rest) {
      out.add('$pad${slice(c)}\n');
    }
    _got = _Doc.cat(out);
  }

  /// The text of `s`, which starts at indentation `ind`.
  _Steps stmt(Stmt s, int ind, bool bare) sync* {
    switch (s) {
      case Bind(:final targets, :final value):
        yield expr(value, _lambda, ind);
        _got = _Doc.cat([
          [for (final t in targets) t ?? '_'].join(', '),
          ' = ',
          _doc,
          ';',
        ]);
      case Return(:final values) when bare && values.length == 1:
        yield expr(values[0], _lambda, ind);
      case Return(:final values):
        yield exprs(values, ind);
        _got = _Doc.cat(['return ', _doc, ';']);
      case Push(:final port, :final value):
        yield expr(value, _lambda, ind);
        _got = _Doc.cat(['$port <- ', _doc, ';']);
      case FunctionDef f:
        yield params(f.params, ind);
        final out = <Object>['${f.name}(', _doc, ')'];
        if (f.ports case final ports?) {
          final ps = <Object>[];
          for (final p in ports) {
            yield ty(p.type, 0);
            ps.add(_Doc.cat(['${p.name}: ', _doc]));
          }
          out.add(_Doc.cat([' -> (', _Doc.join(ps, ', '), ')']));
        }
        if (f.equation) {
          yield expr(f.body, _lambda, ind);
          out.add(_Doc.cat([' = ', _doc, if (f.tests.isEmpty) ';']));
        } else {
          yield block(f.body as Block, ind, _Place.body);
          out.add(_Doc.cat([' ', _doc]));
        }
        if (f.tests.isNotEmpty) {
          final cases = <Object>[];
          for (final (a, b) in f.tests) {
            yield expr(a, _else, ind);
            final input = _doc;
            yield expr(b, _else, ind);
            cases.add(_Doc.cat([input, ' -> ', _doc]));
          }
          out.add(_Doc.cat(['\n${_indent(ind + 1)}test { ', _Doc.join(cases, ', '), ' }']));
        }
        _got = _Doc.cat(out);
    }
  }

  /// The expressions `es`, each at the loosest level, joined by commas.
  _Steps exprs(List<Expr> es, int ind) sync* {
    final out = <Object>[];
    for (final e in es) {
      yield expr(e, _lambda, ind);
      out.add(_doc);
    }
    _got = _Doc.join(out, ', ');
  }

  _Steps params(List<Param> ps, int ind) sync* {
    final out = <Object>[];
    for (final p in ps) {
      yield param(p, ind);
      out.add(_doc);
    }
    _got = _Doc.join(out, ', ');
  }

  _Steps param(Param p, int ind) sync* {
    final out = <Object>[if (p.positional) 'positional ', p.name];
    if (p.type case final t?) {
      yield ty(t, 0);
      out.add(_Doc.cat([': ', _doc]));
    }
    if (p.fallback case final d?) {
      yield expr(d, _lambda, ind);
      out.add(_Doc.cat([' = ', _doc]));
    }
    _got = _Doc.cat(out);
  }

  /// The text of `e` in a position that takes forms of level `min` and above.
  _Steps expr(Expr e, int min, int ind) sync* {
    yield raw(e, ind);
    if (_level(e) < min) _got = _Doc.cat(['(', _doc, ')']);
  }

  _Steps raw(Expr e, int ind) sync* {
    switch (e) {
      case IntLit() || FloatLit() || RatLit() || StrLit():
        // A grouped literal's span holds its parentheses; a literal never starts with `(`.
        var t = slice(e.span).trim();
        while (t.length >= 2 && t.startsWith('(') && t.endsWith(')')) {
          t = t.substring(1, t.length - 1).trim();
        }
        _got = _Doc(t);
      case BoolLit(:final value):
        _got = _Doc('$value');
      case AtomLit(:final name):
        _got = _Doc('#$name');
      case NameRef(:final name):
        _got = _Doc(name);
      case Unary(:final op, e: final x):
        if (x is Unary) {
          yield raw(x, ind);
          _got = _Doc.cat(['$op(', _doc, ')']);
        } else {
          yield expr(x, _prefix, ind);
          _got = _Doc.cat([op, _doc]);
        }
      case Binary(:final op, :final a, :final b):
        final l = _binaryLevel(op);
        final (lmin, rmin) = switch (l) {
          _power => (_postfix, _prefix),
          _equality || _relation => (l + 1, l + 1),
          _ => (l, l + 1),
        };
        yield expr(a, lmin, ind);
        final left = _doc;
        yield expr(b, rmin, ind);
        _got = _Doc.cat([left, ' $op ', _doc]);
      case Call(:final callee, :final positional, :final named, :final curry):
        final args = <Object>[];
        for (final a in positional) {
          yield expr(a, _lambda, ind);
          args.add(_doc);
        }
        for (final (n, v) in named) {
          if (v case NameRef(name: final m) when m == n) {
            args.add('$n:');
          } else {
            yield expr(v, _lambda, ind);
            args.add(_Doc.cat(['$n: ', _doc]));
          }
        }
        if (curry) args.add('...');
        yield postfixOf(callee, ind);
        _got = _Doc.cat([_doc, '(', _Doc.join(args, ', '), ')']);
      case Index(e: final of, :final key):
        yield postfixOf(of, ind);
        final o = _doc;
        yield expr(key, _lambda, ind);
        _got = _Doc.cat([o, '[', _doc, ']']);
      case Member(:final of, :final name, :final safe):
        yield postfixOf(of, ind);
        _got = _Doc.cat([_doc, '${safe ? '?.' : '.'}$name']);
      case Tuple(:final items):
        yield exprs(items, ind);
        _got = _Doc.cat(['(', _doc, ')']);
      case Lambda(:final params, :final body):
        final Object head;
        if (params case [Param(positional: false, type: null, fallback: null, :final name)]) {
          head = name;
        } else {
          yield this.params(params, ind);
          head = _Doc.cat(['(', _doc, ')']);
        }
        yield tail(body, _lambda, ind);
        _got = _Doc.cat([head, ' -> ', _doc]);
      case Is(:final of, :final type, :final negated):
        yield expr(of, _additive, ind);
        final o = _doc;
        yield ty(type, 1);
        _got = _Doc.cat([o, ' is ${negated ? 'not ' : ''}', _doc]);
      case Else(:final of, :final pattern, :final fallback):
        yield expr(of, _else, ind);
        final o = _doc;
        yield tail(fallback, _or, ind);
        _got = _Doc.cat([o, ' else ${pattern == null ? '' : '$pattern -> '}', _doc]);
      case Block():
        yield block(e, ind, _Place.operand);
      case If(:final cond, :final then, :final otherwise):
        yield expr(cond, _else, ind);
        final c = _headUnsafe(cond) ? _Doc.cat(['(', _doc, ')']) : _doc;
        yield block(then as Block, ind, _Place.branch);
        final t = _doc;
        yield otherwise is If ? raw(otherwise, ind) : block(otherwise as Block, ind, _Place.branch);
        _got = _Doc.cat(['if ', c, ' ', t, ' else ', _doc]);
    }
  }

  /// The operand of a call, index or member: a number literal is parenthesized, so that its
  /// `.` is not read as a decimal point.
  _Steps postfixOf(Expr of, int ind) sync* {
    if (of is IntLit || of is FloatLit || of is RatLit) {
      yield raw(of, ind);
      _got = _Doc.cat(['(', _doc, ')']);
    } else {
      yield expr(of, _postfix, ind);
    }
  }

  /// A lambda's body or an `else` default: a block, or an expression of level `min` that
  /// does not start with a block.
  _Steps tail(Expr e, int min, int ind) sync* {
    if (e is Block) {
      yield block(e, ind, _Place.branch);
    } else if (_startsWithBlock(e) && _level(e) >= min) {
      yield raw(e, ind);
      _got = _Doc.cat(['(', _doc, ')']);
    } else {
      yield expr(e, min, ind);
    }
  }

  /// The block `e`, standing at `place`, its first line at indentation `ind`.
  _Steps block(Block e, int ind, _Place place) sync* {
    final stmts = e.stmts;
    final bare = !(place == _Place.operand && stmts.length == 1);
    if (stmts case [Return s] when place != _Place.body && !hasComment(e.span)) {
      // With no comment inside, the block is this one statement: on the block's line when its
      // text has no line break, which no indentation then enters, and on a line of its own
      // otherwise. Rendering it once keeps nested blocks linear in their depth.
      yield stmt(s, ind + 1, bare);
      _got = _doc.hasNewline
          ? _Doc.cat(['{\n${_indent(ind + 1)}', _doc, '\n${_indent(ind)}}'])
          : _Doc.cat(['{ ', _doc, ' }']);
    } else if (stmts.isEmpty && !hasComment(e.span)) {
      _got = _Doc('{ }');
    } else {
      yield this.stmts(stmts, (start: e.span.start + 1, end: e.span.end - 1), ind + 1, bare);
      _got = _Doc.cat(['{\n', _doc, '${_indent(ind)}}']);
    }
  }

  /// The text of the type `t` in a position that takes levels `min` and above.
  _Steps ty(TypeExpr t, int min) sync* {
    switch (t) {
      case TypeName(:final name):
        _got = _Doc(name);
      case AtomType(:final name):
        _got = _Doc('#$name');
      case TupleType(:final items):
        yield types(items, 0, ', ');
        _got = _Doc.cat(['(', _doc, ')']);
      case UnionType(:final items):
        yield types(items, 2, ' | ');
      case AndType(:final items):
        yield types(items, 3, ' & ');
      case DiffType(:final a, :final b):
        yield ty(a, a is DiffType ? 1 : 3);
        final l = _doc;
        yield ty(b, 3);
        _got = _Doc.cat([l, ' \\ ', _doc]);
      case ArrowType(:final params, :final partial, :final result):
        final Object ps;
        if (params case [TypeParam(name: null, type: final p)]) {
          yield ty(p, p is TupleType ? 0 : 1);
          ps = p is TupleType ? _Doc.cat(['(', _doc, ')']) : _doc;
        } else {
          final out = <Object>[];
          for (final p in params) {
            yield ty(p.type, 0);
            out.add(switch (p.name) {
              null => _doc,
              final n => _Doc.cat(['${p.positional ? 'positional ' : ''}$n: ', _doc]),
            });
          }
          ps = _Doc.cat(['(', _Doc.join(out, ', '), ')']);
        }
        yield ty(result, 0);
        _got = _Doc.cat([ps, partial ? ' ->? ' : ' -> ', _doc]);
    }
    if (_typeLevel(t) < min) _got = _Doc.cat(['(', _doc, ')']);
  }

  _Steps types(List<TypeExpr> ts, int min, String sep) sync* {
    final out = <Object>[];
    for (final t in ts) {
      yield ty(t, min);
      out.add(_doc);
    }
    _got = _Doc.join(out, sep);
  }
}

/// Type precedence levels: an arrow, a union or difference, an intersection, a primary.
int _typeLevel(TypeExpr t) => switch (t) {
  ArrowType() => 0,
  UnionType() || DiffType() => 1,
  AndType() => 2,
  _ => 5,
};

/// Text built by concatenation without copying: a string, or parts in order with whether any
/// holds a line break. Each level of the tree adds only its own text, so rendering a nest of
/// depth `d` is linear in the output, where joining strings copies each level's text into its
/// parent, `O(n·d)`.
final class _Doc {
  /// A string, or a list of docs.
  final Object _parts;
  final bool hasNewline;

  _Doc(String s) : _parts = s, hasNewline = s.contains('\n');

  _Doc._(List<_Doc> parts) : _parts = parts, hasNewline = parts.any((p) => p.hasNewline);

  /// The concatenation of `parts`, each a string or a doc.
  factory _Doc.cat(List<Object> parts) =>
      _Doc._([for (final p in parts) p is _Doc ? p : _Doc(p as String)]);

  static _Doc join(List<Object> parts, String sep) => _Doc.cat([
    for (final (i, p) in parts.indexed) ...[if (i > 0) sep, p],
  ]);

  /// The text, written without recursion, so the depth of the tree needs no stack.
  String get text {
    final out = StringBuffer();
    final stack = [
      [this].iterator,
    ];
    while (stack.isNotEmpty) {
      if (!stack.last.moveNext()) {
        stack.removeLast();
      } else if (stack.last.current._parts case final List<_Doc> parts) {
        stack.add(parts.iterator);
      } else {
        out.write(stack.last.current._parts);
      }
    }
    return out.toString();
  }
}
