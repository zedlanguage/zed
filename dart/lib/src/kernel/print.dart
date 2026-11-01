// The printer of kernel terms (step L1.15), in the notation of DESIGN.md sec:kernel:
// `fam(D, i -> e)`, `reindex(F, kf, vf)`, `fold(F, op, ev)` and the rest, with Tier 0 written as
// Zed writes it (`(x, y) -> e`, `f(a)`, `x = e; body`, `if c { a } else { b }`).
//
// `Term.toString` writes a term on one line. [pretty] writes the same text, broken into lines
// of at most a given width where it can: a term that does not fit puts each of its parts on its
// own line, indented two spaces, so the only difference from the one-line form is whitespace.
// Binary primitives are written infix and always parenthesized, so the text needs no
// precedence to be read. Widths count UTF-16 code units, as Dart's strings do.
//
// A subterm's layout is built when a walk first reaches it and kept, and every walk runs on an
// explicit stack, so the depth of a term is bounded by memory alone.
part of 'term.dart';

/// `t` broken into lines of at most `width` columns where its parts allow.
String pretty(Term t, int width) => _Render(width).run(_Lazy(t));

String _patternText(Pattern p) => switch (p) {
  WildP() => '_',
  BindP(:final name) => name,
  LitP(:final value) => '$value',
  AtomP(:final name, args: []) => '#$name',
  AtomP(:final name, :final args) => '#$name(${args.join(', ')})',
  FieldsP(:final name, :final fields) =>
    '#$name(${[for (final (k, p) in fields) '$k: $p'].join(', ')})',
  TupleP(items: [final p]) => '($p,)',
  TupleP(:final items) => '(${items.join(', ')})',
  AnyAtomP() => '#_',
  IsP(:final type) => '(is $type)',
};

/// How a binary primitive is written between its operands, with its spaces.
String? _infix(Prim p) => switch (p) {
  Prim.add => ' + ',
  Prim.sub => ' - ',
  Prim.mul => ' * ',
  Prim.div => ' / ',
  Prim.intDiv => ' div ',
  Prim.mod => ' mod ',
  Prim.eq => ' == ',
  Prim.ne => ' != ',
  Prim.lt => ' < ',
  Prim.le => ' <= ',
  Prim.gt => ' > ',
  Prim.ge => ' >= ',
  Prim.and => ' && ',
  Prim.or => ' || ',
  Prim.concat => ' ++ ',
  Prim.pow => ' ** ',
  _ => null,
};

/// The name of a primitive written as a function, `get(f, k)`.
String _name(Prim p) => switch (p) {
  Prim.neg => 'neg',
  Prim.not => 'not',
  Prim.min => 'min',
  Prim.max => 'max',
  Prim.get => 'get',
  Prim.count => 'count',
  Prim.union => 'union',
  Prim.path => 'path',
  Prim.pathKey => 'pathKey',
  Prim.pathLen => 'pathLen',
  Prim.tuple => 'tuple',
  Prim.tupleGet => 'tupleGet',
  Prim.atom => 'atom',
  Prim.show => 'String',
  Prim.castInt => 'int',
  Prim.castRat => 'rat',
  Prim.castF64 => 'f64',
  Prim.abs => 'abs',
  Prim.len => 'len',
  Prim.lower => 'lower',
  Prim.upper => 'upper',
  Prim.trim => 'trim',
  Prim.sum => 'sum',
  _ => _infix(p)!.trim(),
};

/// A term laid out: text, or parts that are written on one line when they fit and on lines of
/// their own when they do not.
sealed class _Doc {}

final class _Text extends _Doc {
  final String text;

  _Text(this.text);
}

/// A doc always written on one line, as the head of a call.
final class _Flat extends _Doc {
  final _Doc doc;

  _Flat(this.doc);
}

/// Docs written one after another, on the line where they start.
final class _Cat extends _Doc {
  final List<_Doc> docs;

  _Cat(this.docs);
}

/// As [_Cat], but when it does not fit every list in it breaks, so the two branches of an `if`
/// break alike.
final class _Together extends _Doc {
  final List<_Doc> docs;

  _Together(this.docs);
}

/// `open`, the items separated by `sep`, `close`. Broken, each item goes on its own line
/// indented two spaces, `sep` with its trailing spaces removed ending all but the last.
final class _List extends _Doc {
  final String open, sep, close;
  final List<_Doc> items;

  _List(this.open, this.items, this.sep, this.close);

  /// The space inside the braces of a nonempty `{ … }` written on one line.
  String get pad => close == '}' && items.isNotEmpty ? ' ' : '';
}

/// The layout of a subterm, built when it is first read.
final class _Lazy extends _Doc {
  final Term term;

  _Lazy(this.term);

  late final _Doc doc = _layout(term);
}

_Doc _call(String head, List<_Doc> items) => _List('$head(', items, ', ', ')');

/// `key: value`, a named part of a generator such as `depth: 2`.
_Doc _named(String name, _Doc value) => _Cat([_Text('$name: '), value]);

List<_Doc> _lazies(List<Term> ts) => [for (final t in ts) _Lazy(t)];

_Doc _evidence(Evidence ev) => _named(
  'ev',
  _List(
    '{',
    [for (final MapEntry(key: p, value: g) in ev.entries) _Text('$p: ${g.name}')],
    ', ',
    '}',
  ),
);

/// `(x, y) -> body`, or `x -> body` for one parameter.
_Doc _lambda(List<String> params, _Doc body) => _Cat([
  _Text(switch (params) {
    [final p] => '$p -> ',
    _ => '(${params.join(', ')}) -> ',
  }),
  body,
]);

/// `{ e }`, the braces of an `if` branch.
_Doc _block(_Doc d) => _List('{', [d], ' ', '}');

/// The layout of `t`, its subterms left to be laid out when read.
_Doc _layout(Term t) => switch (t) {
  Lit(:final value) => _Text('$value'),
  Var(:final name) => _Text(name),
  Lam(:final params, :final body) => _lambda(params, _Lazy(body)),
  App(f: Var(:final name), :final args) => _call(name, _lazies(args)),
  App(f: final PrimFn f, :final args) => _call(_primFn(f.prim), _lazies(args)),
  // The head is a doc of its own, not a copy of its text, so heads nested in heads stay
  // linear; it is written on one line, as the list after it starts where it ends.
  App(:final f, :final args) => _Cat([
    _Flat(_Cat([_Text('('), _Lazy(f), _Text(')')])),
    _call('', _lazies(args)),
  ]),
  PrimApp(prim: Prim.tuple, args: [final item]) => _Cat([_Text('('), _Lazy(item), _Text(',)')]),
  PrimApp(prim: Prim.tuple, :final args) => _List('(', _lazies(args), ', ', ')'),
  // An atom built from a literal name and field names is written as Zed writes it.
  PrimApp(
    prim: Prim.atom,
    args: [Lit(value: final Str name), Lit(value: Tuple(items: final fs)), ...final rest],
  )
      when fs.isEmpty || fs.length == rest.length =>
    _List(
      '#${name.text}(',
      [
        for (var i = 0; i < rest.length; i++)
          if (i < fs.length)
            _Cat([_Text('${_field(fs[i])}: '), _Lazy(rest[i])])
          else
            _Lazy(rest[i]),
      ],
      ', ',
      ')',
    ),
  PrimApp(:final prim, args: [final a, final b]) when _infix(prim) != null => _List(
    '(',
    [_Lazy(a), _Lazy(b)],
    _infix(prim)!,
    ')',
  ),
  PrimApp(:final prim, :final args) => _call(_name(prim), _lazies(args)),
  PrimFn(:final prim) => _Text(_primFn(prim)),
  Let() => _let(t),
  If(:final cond, :final then, :final orElse) => _Cat([
    _Text('if '),
    _Lazy(cond),
    _Text(' '),
    _Together([_block(_Lazy(then)), _Text(' else '), _block(_Lazy(orElse))]),
  ]),
  Match(:final scrutinee, :final arms) => _Cat([
    _Text('match '),
    _Lazy(scrutinee),
    _Text(' '),
    _List(
      '{',
      [
        for (final (p, t) in arms) _Cat([_Text('$p -> '), _Lazy(t)]),
      ],
      ', ',
      '}',
    ),
  ]),
  Fam(:final domain, :final variable, :final body) => _call('fam', [
    _Lazy(domain),
    _lambda([variable], _Lazy(body)),
  ]),
  Reindex(:final family, :final kf, :final vf, :final witness) => _call('reindex', [
    _Lazy(family),
    _Lazy(kf),
    _Lazy(vf),
    _named(
      'witness',
      _Text(switch (witness) {
        Residue() => 'residue',
        Catalog(:final law) => 'catalog(${quote(law)})',
      }),
    ),
  ]),
  Discard(:final family, :final sel) => _call('discard', [_Lazy(family), _Lazy(sel)]),
  Fold(:final family, :final op, :final identity, :final depth, :final ev) => _call('fold', [
    _Lazy(family),
    _Lazy(op),
    if (identity != null) _named('identity', _Lazy(identity)),
    _named('depth', _Text('$depth')),
    _evidence(ev),
  ]),
  Fix(:final init, :final step, :final self, :final key, :final kind, :final ev) => _call('fix', [
    _Lazy(init),
    ...switch (kind) {
      Lattice(:final join) => [_Lazy(step), _named('join', _Lazy(join))],
      Definedness() => [
        _lambda([self, key], _Lazy(step)),
        _Text('definedness'),
      ],
    },
    _evidence(ev),
  ]),
  Gen(:final init, :final step, :final guard, :final pos) => _call('gen', [
    _Lazy(init),
    _Lazy(step),
    _Lazy(guard),
    _named('guard', _Text(pos.name)),
  ]),
  Read(:final port) => _call('port.read', [_Text(port)]),
  Push(:final port, :final value) => _call('port.push', [_Text(port), _Lazy(value)]),
};

String _primFn(Prim p) => switch (_infix(p)) {
  final op? => '(${op.trim()})',
  null => _name(p),
};

/// A field name stored as a string value, written bare.
String _field(Value v) => v is Str ? '${v.text}' : '$v';

/// A chain of `let`s as one block: `{ x = e; y = f; body }`.
_Doc _let(Term t) {
  final items = <_Doc>[];
  var rest = t;
  for (; rest is Let; rest = rest.body) {
    items.add(_Cat([_Text('${rest.name} = '), _Lazy(rest.value), _Text(';')]));
  }
  items.add(_Lazy(rest));
  return _List('{', items, ' ', '}');
}

/// What a doc writes on one line, in order: each item is text or a doc to expand in its place.
Iterable<Object> _seq(_Doc d) sync* {
  switch (d) {
    case _Text(:final text):
      yield text;
    case _Flat(:final doc) || _Lazy(:final doc):
      yield doc;
    case _Cat(:final docs) || _Together(:final docs):
      yield* docs;
    case _List(:final open, :final items, :final sep, :final close, :final pad):
      yield open;
      yield pad;
      for (var i = 0; i < items.length; i++) {
        if (i > 0) yield sep;
        yield items[i];
      }
      yield pad;
      yield close;
  }
}

/// The one-line text of `d`, piece by piece, read on demand.
Iterable<String> _parts(_Doc d) sync* {
  final stack = [_seq(d).iterator];
  while (stack.isNotEmpty) {
    if (!stack.last.moveNext()) {
      stack.removeLast();
    } else if (stack.last.current case final String s) {
      yield s;
    } else {
      stack.add(_seq(stack.last.current as _Doc).iterator);
    }
  }
}

String _flat(_Doc d) => _parts(d).join();

/// Whether the one-line text of `d` fits in `room` columns. It stops once the room runs out, so
/// it reads at most `room` columns of text.
bool _fits(_Doc d, int room) {
  for (final s in _parts(d)) {
    room -= s.length;
    if (room < 0) return false;
  }
  return true;
}

/// A doc written to a width: each step is text to write, a newline indented so far, a doc to
/// lay out at an indentation, or a list to break at one.
final class _Render {
  final int width;
  final out = StringBuffer();
  int col = 0;

  _Render(this.width);

  String run(_Doc d) {
    final steps = <Object>[(d, 0, false)];
    while (steps.isNotEmpty) {
      switch (steps.removeLast()) {
        case final String s:
          out.write(s);
          col += s.length;
        case final int ind:
          out
            ..write('\n')
            ..write(' ' * ind);
          col = ind;
        case (final _Doc d, final int ind, final bool broken):
          if (broken) {
            _broken(d as _List, ind, steps);
          } else {
            _render(d, ind, steps);
          }
      }
    }
    return out.toString();
  }

  /// Writes `d` at the column reached, on a line indented `ind`, in at most [width] columns
  /// where it can.
  void _render(_Doc d, int ind, List<Object> steps) {
    if (d is _Lazy) return _render(d.doc, ind, steps);
    if (d is _Text || d is _Flat || _fits(d, width - col < 0 ? 0 : width - col)) {
      final s = _flat(d);
      out.write(s);
      col += s.length;
      return;
    }
    switch (d) {
      case _Cat(:final docs):
        for (final c in docs.reversed) {
          steps.add((c, ind, false));
        }
      case _Together(:final docs):
        for (final c in docs.reversed) {
          steps.add((c, ind, c is _List));
        }
      case _List():
        _broken(d, ind, steps);
      case _Text() || _Flat() || _Lazy():
        throw StateError('written above');
    }
  }

  /// Writes the list `d` with each item on its own line.
  void _broken(_List d, int ind, List<Object> steps) {
    out.write(d.open);
    col += d.open.length;
    final inner = ind + 2;
    steps
      ..add(d.close)
      ..add(ind);
    for (var i = d.items.length - 1; i >= 0; i--) {
      if (i + 1 < d.items.length) steps.add(d.sep.trimRight());
      steps
        ..add((d.items[i], inner, false))
        ..add(inner);
    }
  }
}
