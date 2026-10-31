/// The syntactic grammar of DESIGN.md sec:grammar, read from its copy in `zed/grammar/`.
///
/// Each line is `Rule = body Lk` or `| body Lk`: an alternative and the layer it joins. A body
/// is a parsing expression: ordered choice `|` below sequence, below the prefixes `&` and `!`,
/// below the postfixes `*`, `+`, `?` and `e % sep` (`e (sep e)*`); `head(e)` and `nest(e)` set
/// and clear the flag that `HEAD` tests, and a name in capitals that is no rule is a token kind.
library;

/// A kind of token, by the name the grammar writes for it.
enum Kind {
  ident('IDENT'),
  wild('WILD'),
  int('INT'),
  float('FLOAT'),
  rat('RAT'),
  str('STRING'),
  atom('ATOM'),
  annot('ANNOT'),
  keyword('KW'),
  op('OP'),

  /// After the last token.
  end('END');

  final String name;

  const Kind(this.name);
}

/// A parsing expression.
sealed class Expr {
  const Expr();
}

/// A keyword, operator or name with this text.
final class Lit extends Expr {
  final String text;

  const Lit(this.text);
}

/// A rule.
final class Call extends Expr {
  final Rule rule;

  const Call(this.rule);
}

/// A token of this kind.
final class OfKind extends Expr {
  final Kind kind;

  const OfKind(this.kind);
}

/// `HEAD`: succeeds inside `head(…)` and outside any `nest(…)` within it.
final class Head extends Expr {
  const Head();
}

final class Seq extends Expr {
  final List<Expr> items;

  const Seq(this.items);
}

/// An ordered choice.
final class Choice extends Expr {
  final List<Expr> alts;

  const Choice(this.alts);
}

/// `e*`, or `e+` when `plus`.
final class Repeat extends Expr {
  final Expr e;
  final bool plus;

  const Repeat(this.e, {required this.plus});
}

/// `e?`.
final class Opt extends Expr {
  final Expr e;

  const Opt(this.e);
}

/// `&e`, or `!e` when `not`.
final class Look extends Expr {
  final Expr e;
  final bool not;

  const Look(this.e, {required this.not});
}

/// `head(e)`, or `nest(e)` when not `head`.
final class SetHead extends Expr {
  final Expr e;
  final bool head;

  const SetHead(this.e, {required this.head});
}

/// A rule: its name and its alternatives, in order, each with the layer it joins.
final class Rule {
  final String name;

  /// The rule's place in the grammar, which keys the parser's memo.
  final int id;
  final List<({Expr e, int layer})> alts = [];

  Rule(this.name, this.id);

  @override
  String toString() => name;
}

/// A grammar: its rules, by name, in the order they are written.
final class Grammar {
  final Map<String, Rule> rules;

  Grammar._(this.rules);

  /// Reads the grammar written in `texts`, in order.
  factory Grammar.read(List<String> texts) {
    final lines = [
      for (final t in texts)
        for (final l in t.split('\n'))
          if (l.trim().isNotEmpty) l,
    ];
    final rules = <String, Rule>{};
    for (final l in lines) {
      if (l.startsWith(' ') || !l.contains('=')) continue;
      final name = l.substring(0, l.indexOf('=')).trim();
      if (rules.containsKey(name)) throw FormatException('the rule $name is defined twice');
      rules[name] = Rule(name, rules.length);
    }
    Rule? last;
    for (final l in lines) {
      final String body;
      if (l.startsWith(' ')) {
        final t = l.trimLeft();
        if (!t.startsWith('|')) throw FormatException('no `|` in $l');
        body = t.substring(1);
        if (last == null) throw const FormatException('an alternative before any rule');
      } else {
        final eq = l.indexOf('=');
        last = rules[l.substring(0, eq).trim()];
        body = l.substring(eq + 1);
      }
      final m = RegExp(r'^(.*)\sL(\d+)$', dotAll: true).firstMatch(body.trimRight());
      if (m == null) throw FormatException('no layer at the end of $l');
      final r = _Reader(_tokens(m[1]!), rules);
      final e = r.choice();
      if (r.i != r.toks.length) throw FormatException('trailing text in $l');
      last!.alts.add((e: e, layer: int.parse(m[2]!)));
    }
    return Grammar._(rules);
  }

  /// The rule `name`.
  Rule operator [](String name) => rules[name] ?? (throw ArgumentError('no rule $name'));
}

/// A token of a grammar line: a quoted literal, a name, `head(` or `nest(`, or an operator.
typedef _GTok = ({String kind, String text});

List<_GTok> _tokens(String body) {
  final out = <_GTok>[];
  final cs = body.runes.toList();
  bool word(int c) =>
      c >= 0x61 && c <= 0x7a || c >= 0x41 && c <= 0x5a || c == 0x5f || c >= 0x30 && c <= 0x39;
  for (var i = 0; i < cs.length; i++) {
    final c = String.fromCharCode(cs[i]);
    switch (c) {
      case ' ' || '\t':
        break;
      case "'":
        final lit = StringBuffer();
        for (i++; ; i++) {
          if (i >= cs.length) throw FormatException('an unclosed literal in $body');
          if (cs[i] == 0x27) break;
          if (cs[i] == 0x5c) {
            if (++i >= cs.length) throw FormatException('a `\\` ends the line: $body');
          }
          lit.writeCharCode(cs[i]);
        }
        out.add((kind: 'lit', text: '$lit'));
      case '(' || ')' || '|' || '*' || '+' || '?' || '&' || '!' || '%':
        out.add((kind: 'op', text: c));
      case _ when word(cs[i]) && !(cs[i] >= 0x30 && cs[i] <= 0x39):
        final start = i;
        while (i + 1 < cs.length && word(cs[i + 1])) {
          i++;
        }
        final name = String.fromCharCodes(cs, start, i + 1);
        if ((name == 'head' || name == 'nest') && i + 1 < cs.length && cs[i + 1] == 0x28) {
          i++;
          out.add((kind: 'wrap', text: name));
        } else {
          out.add((kind: 'name', text: name));
        }
      default:
        throw FormatException('`$c` in $body is no grammar token');
    }
  }
  return out;
}

const _kinds = {
  'IDENT': Kind.ident,
  'WILD': Kind.wild,
  'INT': Kind.int,
  'FLOAT': Kind.float,
  'RAT': Kind.rat,
  'STRING': Kind.str,
  'ATOM': Kind.atom,
  'ANNOT': Kind.annot,
  'END': Kind.end,
};

final class _Reader {
  final List<_GTok> toks;
  final Map<String, Rule> rules;
  var i = 0;

  _Reader(this.toks, this.rules);

  bool eat(String op) {
    final hit = i < toks.length && toks[i] == (kind: 'op', text: op);
    if (hit) i++;
    return hit;
  }

  Expr choice() {
    final alts = [seq()];
    while (eat('|')) {
      alts.add(seq());
    }
    return alts.length == 1 ? alts.single : Choice(alts);
  }

  Expr seq() {
    final items = <Expr>[];
    while (i < toks.length &&
        toks[i] != (kind: 'op', text: '|') &&
        toks[i] != (kind: 'op', text: ')')) {
      items.add(prefix());
    }
    return items.length == 1 ? items.single : Seq(items);
  }

  Expr prefix() {
    if (eat('&')) return Look(prefix(), not: false);
    if (eat('!')) return Look(prefix(), not: true);
    return postfix();
  }

  Expr postfix() {
    var e = primary();
    while (true) {
      if (eat('*')) {
        e = Repeat(e, plus: false);
      } else if (eat('+')) {
        e = Repeat(e, plus: true);
      } else if (eat('?')) {
        e = Opt(e);
      } else if (eat('%')) {
        e = Seq([
          e,
          Repeat(Seq([primary(), e]), plus: false),
        ]);
      } else {
        return e;
      }
    }
  }

  Expr primary() {
    if (i >= toks.length) throw const FormatException('an expression is missing');
    final t = toks[i++];
    switch (t.kind) {
      case 'lit':
        return Lit(t.text);
      case 'name':
        if (rules[t.text] case final r?) return Call(r);
        if (t.text == 'HEAD') return const Head();
        if (_kinds[t.text] case final k?) return OfKind(k);
        throw FormatException('the rule ${t.text} is not defined');
      case 'wrap':
        final e = choice();
        if (!eat(')')) throw FormatException('`${t.text}(` is not closed');
        return SetHead(e, head: t.text == 'head');
      case _ when t.text == '(':
        final e = choice();
        if (!eat(')')) throw const FormatException('`(` is not closed');
        return e;
      default:
        throw FormatException('unexpected `${t.text}`');
    }
  }
}
