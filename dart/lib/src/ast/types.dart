// Type expressions, parameter lists and atom patterns (step L1.10): what an `is` test, a
// lambda's parameters and an `else` pattern are written with.
part of '../../ast.dart';

/// A type expression and its span.
sealed class TypeExpr with _Text {
  /// Its text; a grouping's parentheses widen it.
  Span span;

  TypeExpr(this.span);
}

/// A type name, its unit path included (`geometry.Point`).
final class TypeName extends TypeExpr {
  final String name;

  TypeName(this.name, super.span);

  @override
  List<Object> get _pieces => [name];
}

/// An atom, without its `#`.
final class AtomType extends TypeExpr {
  final String name;

  AtomType(this.name, super.span);

  @override
  List<Object> get _pieces => ['#', name];
}

/// A tuple type `(A, B)`.
final class TupleType extends TypeExpr {
  final List<TypeExpr> items;

  TupleType(this.items, super.span);

  @override
  List<Object> get _pieces => ['(tuple ', ..._spaced(items), ')'];
}

/// A union `A | B | …`.
final class UnionType extends TypeExpr {
  final List<TypeExpr> items;

  UnionType(this.items, super.span);

  @override
  List<Object> get _pieces => ['(| ', ..._spaced(items), ')'];
}

/// An intersection `A & B & …`.
final class AndType extends TypeExpr {
  final List<TypeExpr> items;

  AndType(this.items, super.span);

  @override
  List<Object> get _pieces => ['(& ', ..._spaced(items), ')'];
}

/// A difference `A \ B`.
final class DiffType extends TypeExpr {
  final TypeExpr a;
  final TypeExpr b;

  DiffType(this.a, this.b, super.span);

  @override
  List<Object> get _pieces => [r'(\ ', a, ' ', b, ')'];
}

/// A function type, `->`, or `->?` when `partial`, a partial map.
final class ArrowType extends TypeExpr {
  final List<TypeParam> params;
  final bool partial;
  final TypeExpr result;

  ArrowType(this.params, this.partial, this.result, super.span);

  @override
  List<Object> get _pieces => [partial ? '(->? (' : '(-> (', ..._spaced(params), ') ', result, ')'];
}

/// A parameter of a function type: `int`, `x: int` or `positional x: int`. Its name, if
/// written, documents it.
final class TypeParam with _Text {
  final String? name;
  final bool positional;
  final TypeExpr type;

  TypeParam(this.name, this.positional, this.type);

  @override
  List<Object> get _pieces => switch (name) {
    null => [type],
    final n => ['(', if (positional) 'positional ', n, ': ', type, ')'],
  };
}

/// A parameter of a lambda or a declaration, with its type and default if written.
final class Param with _Text {
  final String name;
  final bool positional;
  final TypeExpr? type;
  final Expr? fallback;
  final Span span;

  Param(this.name, this.positional, this.type, this.fallback, this.span);

  /// `x`, or `(positional x: int = 0)` with what is written.
  @override
  List<Object> get _pieces => !positional && type == null && fallback == null
      ? [name]
      : [
          '(',
          if (positional) 'positional ',
          name,
          if (type case final t?) ...[': ', t],
          if (fallback case final f?) ...[' = ', f],
          ')',
        ];
}

/// A pattern. At L1 the only patterns are atom patterns, which `else` takes.
sealed class Pattern with _Text {
  final Span span;

  Pattern(this.span);
}

/// `#name`, `#name(f: p, g:)` or `#name(p, q)`: fields matched by name, where `g:` (no
/// pattern) binds the field to the name `g`, and payload components matched by position.
final class AtomPattern extends Pattern {
  final String name;
  final List<(String, Pattern?)> fields;
  final List<Pattern> items;

  AtomPattern(this.name, this.fields, this.items, super.span);

  @override
  List<Object> get _pieces {
    if (fields.isEmpty && items.isEmpty) return ['#', name];
    final parts = [
      for (final (f, p) in fields) p == null ? ['$f:'] : ['$f: ', p],
      for (final p in items) [p],
    ];
    return [
      '#',
      name,
      '(',
      for (final (i, p) in parts.indexed) ...[if (i > 0) ', ', ...p],
      ')',
    ];
  }
}

TypeExpr get _type => _got as TypeExpr;

/// The builders of types, parameters and patterns, each a generator run as `node` is.
mixin _Types {
  List<Token> get tokens;
  Span span(Node n);
  String word(int i);
  BuildError later(Node n);
  _Steps node(Node n);

  /// The type of node `n`, of a rule from `Type` down to `TypePrimary`.
  _Steps type(Node n) sync* {
    final kids = n.kids;
    switch ((n.name, n.alt)) {
      case ('Type' || 'TypePostfix' || 'TypeAnd', _) || ('TypeNot' || 'TypeUnion', 1)
          when kids.length == 1:
        yield type(kids[0]);
      case ('Type' || 'TypePostfix', _):
        throw later(kids[1]);
      case ('Arrow', 0):
        final params = <TypeParam>[];
        yield* arrowParams(kids[0], params);
        yield* arrow(params, kids[0], kids[1], span(n));
      case ('Arrow', 1):
        yield type(kids[0]);
        if (kids case [final t, final r]) {
          yield* arrow([TypeParam(null, false, _type)], t, r, span(n));
        }
      case ('TypeUnion', 0):
        yield type(kids[0]);
        for (final k in kids.skip(1)) {
          final a = _type;
          yield type(k);
          _got = DiffType(a, _type, (start: a.span.start, end: _type.span.end));
        }
      case ('TypeUnion', 1):
        final items = <TypeExpr>[];
        yield* types(kids, items);
        _got = UnionType(items, span(n));
      case ('TypeAnd', _):
        final items = <TypeExpr>[];
        yield* types(kids, items);
        _got = AndType(items, span(n));
      case ('TypePrimary', 1):
        _got = TypeName([for (var i = n.start; i < n.end; i += 2) word(i)].join('.'), span(n));
      case ('TypePrimary', 3):
        _got = AtomType((tokens[n.start].tok as Atom).name, span(n));
      case ('TypePrimary', 6):
        final items = <TypeExpr>[];
        yield* types(kids, items);
        _got = TupleType(items, span(n));
      case ('TypePrimary', 8):
        yield type(kids[0]);
        _type.span = span(n);
      default:
        throw later(n);
    }
  }

  _Steps types(List<Node> kids, List<TypeExpr> out) sync* {
    for (final k in kids) {
      yield type(k);
      out.add(_type);
    }
  }

  /// The arrow from `params`, written at node `p`, to the type of node `r`.
  _Steps arrow(List<TypeParam> params, Node p, Node r, Span whole) sync* {
    final partial = word(p.end) == '->?';
    yield type(r);
    _got = ArrowType(params, partial, _type, whole);
  }

  _Steps arrowParams(Node n, List<TypeParam> out) sync* {
    switch (n.alt) {
      case 0:
        break;
      case 1:
        for (final k in n.kids) {
          // TypeParam = 'positional'? Name ':' Type | Type
          yield type(k.kids.last);
          final name = k.kids.length == 2 ? word(k.kids[0].start) : null;
          out.add(TypeParam(name, name != null && word(k.start) == 'positional', _type));
        }
      default:
        yield type(n.kids[1]);
        out.add(TypeParam(word(n.kids[0].start), word(n.start + 1) == 'positional', _type));
    }
  }

  /// The parameters of node `n`, a `Params`, added to `out`.
  _Steps params(Node n, List<Param> out) sync* {
    for (final k in n.kids) {
      yield param(k);
      out.add(_got as Param);
    }
  }

  /// The parameter of node `n`, a `Param` or a `PosParam`.
  _Steps param(Node n) sync* {
    if (n.name == 'PosParam' && n.alt == 0) throw later(n);
    TypeExpr? type;
    Expr? fallback;
    for (final k in n.kids.skip(1)) {
      if (k.name == 'Type') {
        yield this.type(k);
        type = _type;
      } else {
        yield node(k);
        fallback = _expr;
      }
    }
    _got = Param(word(n.kids[0].start), n.name == 'PosParam', type, fallback, span(n));
  }

  /// The pattern of node `n`, a `Pattern` or an `AtomPattern`.
  _Steps pattern(Node n) sync* {
    switch (n.name) {
      case 'Pattern' when n.alt == 1:
        yield pattern(n.kids[0]);
      case 'AtomPattern':
        final fields = <(String, Pattern?)>[];
        final items = <Pattern>[];
        for (final k in n.kids) {
          if (k.name == 'FieldPat') {
            Pattern? p;
            if (k.kids case [_, final q]) {
              yield pattern(q);
              p = _got as Pattern;
            }
            fields.add((word(k.kids[0].start), p));
          } else {
            yield pattern(k);
            items.add(_got as Pattern);
          }
        }
        _got = AtomPattern((tokens[n.start].tok as Atom).name, fields, items, span(n));
      default:
        throw later(n);
    }
  }
}
