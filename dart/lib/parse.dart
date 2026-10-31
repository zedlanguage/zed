/// The parser (step L1.8): tokens become a tree of the rules of DESIGN.md sec:grammar.
///
/// The parser runs that grammar itself, copied into `zed/grammar/`, as a packrat parser: each
/// rule tries its alternatives in order and memoizes its result at each token. So the
/// precedence ladder is the grammar's, rung for rung, and its trees are the trees
/// `tools/grammar/lib/check.dart` builds. A parse is at a ring: only the alternatives of that
/// layer and below are tried. Each node records its alternative, so a node of a later layer
/// than the program's is found later, by the elaborator, not here.
///
/// A literal in the grammar matches a keyword, an operator or a name with its text, so the
/// positional words `where` and `sep` are names the grammar matches by their text.
library;

import 'dart:collection';
import 'dart:convert';

import 'lex.dart';
import 'src/parse/grammar.dart';
import 'src/parse/peg.dart';

export 'src/parse/grammar.dart' show Grammar, Kind, Rule;

/// The highest layer, and the ring at which every alternative is tried.
const top = 29;

/// The grammar of sec:grammar: its syntactic grammar and its documentation notation.
final Grammar grammar = Grammar.read([syntaxPeg, notationPeg]);

/// A node: the rule it matched, the alternative, counted from 0 among all of the rule's
/// alternatives, the tokens it spans, from `start` to one before `end`, and its children.
final class Node {
  final Rule rule;
  final int alt;
  final int start;
  final int end;
  final List<Node> kids;

  Node(this.rule, this.alt, this.start, this.end, this.kids);

  String get name => rule.name;

  /// The layer of the alternative the node matched.
  int get layer => rule.alts[alt].layer;

  /// This node and every node below it, children before their parent.
  Iterable<Node> get all sync* {
    final stack = [(this, false)];
    while (stack.isNotEmpty) {
      final (n, done) = stack.removeLast();
      if (done) {
        yield n;
        continue;
      }
      stack.add((n, true));
      for (final k in n.kids.reversed) {
        stack.add((k, false));
      }
    }
  }
}

/// A parse tree: its root, and the tree of each `${…}` hole in its tokens, in their order,
/// each parsed as an `Expr`.
final class Tree {
  final Node root;
  final List<Tree> holes;

  Tree(this.root, this.holes);
}

/// Why a parse failed: the span of the furthest token any alternative reached (empty at the
/// end of the text), and the literals (quoted) and token kinds expected there, sorted.
final class ParseError implements Exception {
  final Span span;
  final List<String> expected;

  ParseError(this.span, this.expected);

  @override
  String toString() => 'expected ${expected.join(' or ')}';
}

/// Parses `tokens`, lexed from `text`, as the rule `start` at `ring`, to the end of the tokens.
Tree parse(String text, List<Token> tokens, String start, int ring) {
  final n = utf8.encode(text).length;
  return _parse(tokens, grammar[start], ring, (start: n, end: n));
}

/// Parses as `parse` does; `end` is the span reported for an error at the end of `tokens`.
Tree _parse(List<Token> tokens, Rule start, int ring, Span end) {
  final p = _Parser(ring, [for (final t in tokens) _kind(t.tok)]);
  final kids = <Node>[];
  final at = p.rule(start, 0, false, kids);
  if (at != null && at < p.toks.length - 1) p.fail(at, 'END');
  if (at == null || at < p.toks.length - 1) {
    throw ParseError(p.far < tokens.length ? tokens[p.far].span : end, [...p.expected]);
  }
  return Tree(kids.single, [
    for (final t in tokens)
      if (t.tok case Str(:final parts))
        for (final part in parts)
          if (part case Hole(:final tokens, :final span))
            _parse(tokens, grammar['Expr'], ring, (start: span.end - 1, end: span.end)),
  ]);
}

(Kind, String) _kind(Tok tok) => switch (tok) {
  Name(:final text) => (Kind.ident, text),
  Wildcard() => (Kind.wild, ''),
  Int() => (Kind.int, ''),
  Float() => (Kind.float, ''),
  Rat() => (Kind.rat, ''),
  Str() => (Kind.str, ''),
  Atom() => (Kind.atom, ''),
  Annot() => (Kind.annot, ''),
  Keyword(:final word) => (Kind.keyword, word),
  Op(:final op) => (Kind.op, op),
};

/// The matcher: a packrat parser run on an explicit stack of the expressions being matched,
/// so that the depth of the text's nesting is bounded by memory alone.
final class _Parser {
  final int ring;

  /// The kind and text of each token, and `END` after the last.
  final List<(Kind, String)> toks;

  /// At each token, the end and node of the match of each rule tried there, inside `head(…)`
  /// or not, keyed by `_key`; null for no match.
  final List<Map<int, (int, Node)?>> memo;
  var far = 0;
  var expected = SplayTreeSet<String>();

  _Parser(this.ring, List<(Kind, String)> toks)
    : toks = [...toks, (Kind.end, '')],
      memo = [for (var i = 0; i <= toks.length; i++) {}];

  int _key(Rule r, bool head) => r.id * 2 + (head ? 1 : 0);

  Null fail(int pos, String what) {
    if (pos > far) {
      far = pos;
      expected.clear();
    }
    if (pos == far) expected.add(what);
    return null;
  }

  /// Matches rule `r` at `pos`, adding its node to `kids`: the end of the match, or null.
  int? rule(Rule r, int pos, bool head, List<Node> kids) {
    final stack = <_Frame>[];
    // Either `e` is to be matched at `pos`, adding its nodes to `kids`, or (when `e` is null)
    // `res` is the result of the match the top frame asked for.
    Expr? e = Call(r);
    int? res;
    while (true) {
      if (e != null) {
        switch (e) {
          case Lit(:final text):
            final (k, t) = toks[pos];
            final hit = (k == Kind.keyword || k == Kind.op || k == Kind.ident) && t == text;
            res = hit ? pos + 1 : fail(pos, "'$text'");
            e = null;
          case OfKind(:final kind):
            res = toks[pos].$1 == kind ? pos + 1 : fail(pos, kind.name);
            e = null;
          case Head():
            res = head ? pos : null;
            e = null;
          case SetHead(e: final x, head: final h):
            (e, head) = (x, h);
          case Call(:final rule):
            final key = _key(rule, head);
            final at = memo[pos];
            if (at.containsKey(key)) {
              final hit = at[key];
              if (hit != null) kids.add(hit.$2);
              res = hit?.$1;
              e = null;
            } else {
              // A left-recursive call fails, as in check.dart; the grammar has none.
              at[key] = null;
              final f = _RuleFrame(rule, key, pos, head, kids);
              stack.add(f);
              e = f.next(ring);
              if (e == null) {
                res = null;
              } else {
                kids = f.sub;
              }
            }
          case Seq(:final items):
            stack.add(_SeqFrame(items, head, kids));
            e = items[0];
          case Choice(:final alts):
            stack.add(_ChoiceFrame(alts, pos, head, kids));
            e = alts[0];
          case Repeat(e: final x, :final plus):
            stack.add(_RepeatFrame(x, plus, pos, head, kids));
            e = x;
          case Opt(e: final x):
            stack.add(_OptFrame(pos));
            e = x;
          case Look(e: final x, :final not):
            stack.add(_LookFrame(not, pos, kids, far, expected));
            if (not) expected = SplayTreeSet.of(expected);
            e = x;
        }
        continue;
      }
      if (stack.isEmpty) return res;
      final f = stack.last;
      // Each frame either asks for the next match, setting `e`, `pos`, `head` and `kids`, or
      // is done, setting `res` and popping itself.
      switch (f) {
        case _RuleFrame():
          if (res != null) {
            final node = Node(f.rule, f.alt, f.pos, res, f.sub);
            memo[f.pos][f.key] = (res, node);
            f.kids.add(node);
          } else if (f.next(ring) case final x?) {
            (e, pos, head, kids) = (x, f.pos, f.head, f.sub);
            continue;
          } else {
            memo[f.pos][f.key] = null;
          }
          kids = f.kids;
        case _SeqFrame():
          if (res == null) {
            f.kids.length = f.mark;
          } else if (++f.i < f.items.length) {
            (e, pos, head, kids) = (f.items[f.i], res, f.head, f.kids);
            continue;
          }
          kids = f.kids;
        case _ChoiceFrame():
          if (res == null && ++f.i < f.alts.length) {
            (e, pos, head, kids) = (f.alts[f.i], f.pos, f.head, f.kids);
            continue;
          }
          kids = f.kids;
        case _RepeatFrame():
          // An iteration that matches nothing ends the loop, kept only if it is the first.
          if (res != null && !(res == f.at && f.n > 0)) {
            f.n++;
            if (res != f.at) {
              f.at = res;
              f.mark = f.kids.length;
              (e, pos, head, kids) = (f.e, res, f.head, f.kids);
              continue;
            }
          } else if (res != null) {
            f.kids.length = f.mark;
          }
          res = f.n > 0 || !f.plus ? f.at : null;
          kids = f.kids;
        case _OptFrame():
          res ??= f.pos;
        case _LookFrame():
          f.kids.length = f.mark;
          if (f.not) {
            far = f.far;
            expected = f.expected;
          }
          res = (res != null) != f.not ? f.pos : null;
          kids = f.kids;
      }
      stack.removeLast();
    }
  }
}

sealed class _Frame {}

/// A rule being matched at `pos`: the alternative being tried and the nodes it has matched.
final class _RuleFrame extends _Frame {
  final Rule rule;
  final int key;
  final int pos;
  final bool head;
  final List<Node> kids;
  var alt = -1;
  var sub = <Node>[];

  _RuleFrame(this.rule, this.key, this.pos, this.head, this.kids);

  /// The next alternative of the ring, or null when none is left.
  Expr? next(int ring) {
    while (++alt < rule.alts.length) {
      if (rule.alts[alt].layer <= ring) {
        sub = [];
        return rule.alts[alt].e;
      }
    }
    return null;
  }
}

final class _SeqFrame extends _Frame {
  final List<Expr> items;
  final bool head;
  final List<Node> kids;
  final int mark;
  var i = 0;

  _SeqFrame(this.items, this.head, this.kids) : mark = kids.length;
}

final class _ChoiceFrame extends _Frame {
  final List<Expr> alts;
  final int pos;
  final bool head;
  final List<Node> kids;
  var i = 0;

  _ChoiceFrame(this.alts, this.pos, this.head, this.kids);
}

final class _RepeatFrame extends _Frame {
  final Expr e;
  final bool plus;
  final bool head;
  final List<Node> kids;
  int at;
  var n = 0;
  int mark;

  _RepeatFrame(this.e, this.plus, this.at, this.head, this.kids) : mark = kids.length;
}

final class _OptFrame extends _Frame {
  final int pos;

  _OptFrame(this.pos);
}

final class _LookFrame extends _Frame {
  final bool not;
  final int pos;
  final List<Node> kids;
  final int mark;
  final int far;
  final SplayTreeSet<String> expected;

  _LookFrame(this.not, this.pos, this.kids, this.far, this.expected) : mark = kids.length;
}
