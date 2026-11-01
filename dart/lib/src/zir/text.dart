/// The text form of ZIR (DESIGN.md sec:ir, "Dialect descent"): flat, sorted, line-oriented.
///
/// ```text
/// zir 1
/// r region function (int; int)
/// r.0 prim + (r^0, r^1) -> (int)
/// r results (r.0^0)
/// ```
///
/// Every region and node has a path: the root region is `r`, node `k` of region `R` is `R.k`,
/// and region `j` of node `N` is `N/j`. A line is a region's header (its kind and argument
/// edges), a node (its operation, inputs and output edges), or a region's results. `R^i` is
/// argument `i` of region `R`, `N^p` output `p` of node `N`, and any other input is a
/// constant, written as the kernel prints values. A value edge is its type in the kernel's
/// prefix syntax (`(| int String)`), then its facts when it has any: `in [0..=9]`,
/// `class 1 mod 3`, `set {1, 5}`, and each facet as `facet units "m"` or `hint name "x"`. A
/// state edge is `state out`.
///
/// Lines are written sorted by path, a region's header before its nodes, each node followed by
/// its regions, and the results last; the reader accepts the lines in any order, so the form
/// can be sorted, diffed and merged line by line. A pattern is written as the kernel writes
/// one, except that a literal is `=v`, so a literal atom or tuple is not read as a pattern of
/// that shape. A recursive type prints as its name, which this form cannot read back: such
/// types are declared from step L2, and their text form comes with the declarations.
///
/// A column in a message counts UTF-16 code units from 1, and a name is a run of characters
/// of the Unicode property XID_Continue, the characters a Zed name is made of.
library;

import '../canon/canon.dart' show Facet;
import '../canon/domain.dart';
import '../kernel/term.dart';
import '../kernel/types.dart' show Type, Universe;
import '../kernel/value.dart';
import '../store/interval.dart';
import '../store/lattice.dart';
import '../unicode.dart';
import 'graph.dart';

/// The version of the text and binary forms.
const version = 1;

/// How the text form spells a primitive: as the kernel's printer does.
String spell(Prim p) => switch (p) {
  Prim.add => '+',
  Prim.sub => '-',
  Prim.mul => '*',
  Prim.div => '/',
  Prim.intDiv => 'div',
  Prim.mod => 'mod',
  Prim.neg => 'neg',
  Prim.eq => '==',
  Prim.ne => '!=',
  Prim.lt => '<',
  Prim.le => '<=',
  Prim.gt => '>',
  Prim.ge => '>=',
  Prim.and => '&&',
  Prim.or => '||',
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
  Prim.concat => '++',
  Prim.pow => '**',
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
};

final _prims = {for (final p in Prim.values) spell(p): p};

// ---------------------------------------------------------------------------------------------
// Writing

/// The text form of the graph rooted at `root`.
String print(Region root) {
  final out = StringBuffer('zir $version\n');
  _regionLines(root, 'r', out);
  return '$out';
}

/// Writes the lines of `root` and the regions in it, with a stack of the lines still to write.
void _regionLines(Region root, String rootPath, StringBuffer out) {
  final todo = <void Function()>[];
  void region(Region r, String path) {
    out.writeln('$path region ${r.kind.name} (${r.args.join('; ')})');
    todo.add(() => out.writeln('$path results (${_srcs(r.results, path)})'));
    for (final (k, n) in r.nodes.indexed.toList().reversed) {
      final at = '$path.$k';
      todo.add(() {
        out.writeln('$at ${_op(n.op)} (${_srcs(n.inputs, path)}) -> (${n.outputs.join('; ')})');
        for (final (j, sub) in n.regions.indexed.toList().reversed) {
          todo.add(() => region(sub, '$at/$j'));
        }
      });
    }
  }

  region(root, rootPath);
  while (todo.isNotEmpty) {
    todo.removeLast()();
  }
}

String _srcs(List<Src> ss, String path) => ss
    .map(
      (s) => switch (s) {
        Arg(:final i) => '$path^$i',
        Out(:final node, :final port) => '$path.$node^$port',
        Const(:final value) => '$value',
      },
    )
    .join(', ');

/// The text form of an edge type.
String edge(Edge e) {
  final ValueEdge v;
  switch (e) {
    case StateEdge(:final port):
      return 'state $port';
    case final ValueEdge x:
      v = x;
  }
  final s = StringBuffer('${v.type}');
  final d = v.domain;
  if (d.ints != IntervalSet.top()) s.write(' in ${d.ints}');
  if (d.congruence != Congruence.top) s.write(' class ${d.congruence}');
  if (d.finite.members case final vs?) s.write(' set {${vs.join(', ')}}');
  for (final f in v.facets) {
    s.write(' ${f.hint ? 'hint' : 'facet'} ${f.kind} ${f.value}');
  }
  return '$s';
}

String _op(Op op) {
  final name = op.name;
  return switch (op) {
    ReindexOp(witness: Residue()) => '$name residue',
    ReindexOp(witness: Catalog(:final law)) => '$name catalog $law',
    FoldOp(:final depth, :final identity, :final ev) =>
      '$name $depth${identity ? ' identity' : ''} ${_evidence(ev)}',
    FixOp(:final lattice, :final ev) =>
      '$name ${lattice ? 'lattice' : 'definedness'} ${_evidence(ev)}',
    GenOp(:final pos) => '$name ${pos.name}',
    ReadOp(:final port) => '$name read $port',
    PushOp(:final port) => '$name push $port',
    PrimOp(:final prim) => '$name ${spell(prim)}',
    MatchOp(:final patterns) => '$name [${patterns.map(pattern).join(', ')}]',
    _ => name,
  };
}

String _evidence(Evidence ev) =>
    '{${[for (final MapEntry(:key, :value) in ev.entries) '$key: ${value.name}'].join(', ')}}';

/// The text form of a pattern.
String pattern(Pattern p) {
  String list(List<Pattern> ps) => ps.map(pattern).join(', ');
  return switch (p) {
    WildP() => '_',
    BindP(:final name) => name,
    LitP(:final value) => '=$value',
    AtomP(:final name, args: []) => '#$name',
    AtomP(:final name, :final args) => '#$name(${list(args)})',
    FieldsP(:final name, :final fields) =>
      '#$name(${[for (final (k, p) in fields) '$k: ${pattern(p)}'].join(', ')})',
    TupleP(items: [final one]) => '(${pattern(one)},)',
    TupleP(:final items) => '(${list(items)})',
    AnyAtomP() => '#_',
    IsP(:final type) => '(is $type)',
  };
}

// ---------------------------------------------------------------------------------------------
// Reading

/// The graph in `text`, which [validate] has not yet checked; throws a [ZirError] that names
/// the line and column.
Region parse(String text) {
  final lines = <(_Line, int)>[];
  var header = false;
  for (final (i, line) in text.split('\n').indexed) {
    final no = i + 1;
    if (line.trim().isEmpty) continue;
    if (!header) {
      if (line.trim() != 'zir $version') {
        throw ZirError('line $no: the first line is `zir $version`');
      }
      header = true;
      continue;
    }
    final p = _P(line.endsWith('\r') ? line.substring(0, line.length - 1) : line);
    try {
      lines.add((p.line(), no));
    } on _Fail catch (e) {
      throw ZirError('line $no: column ${p.i + 1}: ${e.message}');
    }
  }
  if (!header) throw const ZirError('the text is empty, and starts `zir $version`');
  final keys = [for (final (l, _) in lines) l.key()];
  final order = List.generate(lines.length, (i) => i)
    ..sort((a, b) => _compareKeys(keys[a], keys[b]));
  final sorted = [for (final i in order) lines[i]];
  for (var j = 1; j < order.length; j++) {
    if (_compareKeys(keys[order[j - 1]], keys[order[j]]) == 0) {
      // A stable sort keeps the earlier line first.
      throw ZirError(
        'lines ${sorted[j - 1].$2} and ${sorted[j].$2}: two lines for ${sorted[j].$1.what()}',
      );
    }
  }
  final b = _Builder(sorted);
  final root = b.build(const []);
  if (b.i < sorted.length) {
    final (l, no) = sorted[b.i];
    throw ZirError(
      'line $no: ${l.what()} is not in the graph: its parent or an earlier sibling has no line',
    );
  }
  return root;
}

/// The edge type written `s`, such as `int in [0..=9]`.
Edge parseEdge(String s) => _whole(s, (p) => p.edge());

/// The type written `s` in the kernel's prefix syntax, such as `(| int String)`.
Type parseType(String s) => _whole(s, (p) => p.ty());

/// The value written `s` as the kernel prints values, such as `#err(code: 3)`.
Value parseValue(String s) => _whole(s, (p) => p.value());

/// The pattern written `s`, such as `#some(x)`.
Pattern parsePattern(String s) => _whole(s, (p) => p.pattern());

T _whole<T>(String s, T Function(_P) item) {
  final p = _P(s);
  try {
    final v = item(p);
    p.ws();
    if (p.rest.isNotEmpty) throw _Fail('unexpected ${p.found()} after the item');
    return v;
  } on _Fail catch (e) {
    throw ZirError('column ${p.i + 1}: ${e.message}');
  }
}

/// A message without its position, which the caller adds.
final class _Fail implements Exception {
  final String message;

  const _Fail(this.message);
}

/// `r`, then alternately `.k` for a node and `/j` for a region.
String _show(List<int> path) {
  final s = StringBuffer('r');
  for (final (i, k) in path.indexed) {
    s.write('${i.isEven ? '.' : '/'}$k');
  }
  return '$s';
}

/// The sort key of a region's path: header, nodes in order, results.
List<int> _regionKey(List<int> path) => [
  for (var i = 0; i + 1 < path.length; i += 2) ...[1, path[i], path[i + 1]],
];

int _compareKeys(List<int> a, List<int> b) {
  for (var i = 0; i < a.length && i < b.length; i++) {
    if (a[i] != b[i]) return a[i].compareTo(b[i]);
  }
  return a.length.compareTo(b.length);
}

bool _startsWith(List<int> path, List<int> prefix) {
  if (path.length < prefix.length) return false;
  for (var i = 0; i < prefix.length; i++) {
    if (path[i] != prefix[i]) return false;
  }
  return true;
}

bool _samePath(List<int> a, List<int> b) => a.length == b.length && _startsWith(a, b);

sealed class _Body {}

final class _Header extends _Body {
  final RegionKind kind;
  final List<Edge> args;

  _Header(this.kind, this.args);
}

final class _NodeLine extends _Body {
  final Op op;
  final List<Src> inputs;
  final List<Edge> outputs;

  _NodeLine(this.op, this.inputs, this.outputs);
}

final class _Results extends _Body {
  final List<Src> results;

  _Results(this.results);
}

final class _Line {
  final List<int> path;
  final _Body body;

  _Line(this.path, this.body);

  List<int> key() => switch (body) {
    _Header() => [..._regionKey(path), 0],
    _Results() => [..._regionKey(path), 2],
    _NodeLine() => [..._regionKey(path.sublist(0, path.length - 1)), 1, path.last],
  };

  String what() => switch (body) {
    _Header() => 'region ${_show(path)}',
    _NodeLine() => 'node ${_show(path)}',
    _Results() => 'the results of ${_show(path)}',
  };
}

/// A region whose header is read: its nodes so far, and the node whose regions are being read.
final class _Open {
  final List<int> path;
  final _Header header;
  final nodes = <Node>[];
  _NodeLine? node;
  List<int> nodePath = const [];
  var regions = <Region>[];

  _Open(this.path, this.header);
}

/// Builds the regions from the lines sorted by key, each region's lines in one run. Regions
/// nest as deep as the program does, so the builder keeps a stack of the open regions.
final class _Builder {
  final List<(_Line, int)> lines;
  var i = 0;

  _Builder(this.lines);

  _Line? get _next => i < lines.length ? lines[i].$1 : null;

  _Open open(List<int> path) {
    final h = _next;
    if (h == null || h.body is! _Header || !_samePath(h.path, path)) {
      throw ZirError('region ${_show(path)} has no header line');
    }
    i++;
    return _Open(path, h.body as _Header);
  }

  Region build(List<int> root) {
    final stack = [open(root)];
    while (true) {
      final f = stack.last;
      if (f.node case final n?) {
        final sub = [...f.nodePath, f.regions.length];
        if (_next case _Line(body: _Header(), path: final q) when _samePath(q, sub)) {
          stack.add(open(sub));
          continue;
        }
        f.nodes.add(Node(n.op, n.inputs, n.outputs, f.regions));
        f.node = null;
      }
      if (_next case _Line(body: final _NodeLine n, path: final p)
          when p.length == f.path.length + 1 &&
              _startsWith(p, f.path) &&
              p.last == f.nodes.length) {
        i++;
        f
          ..node = n
          ..nodePath = p
          ..regions = [];
        continue;
      }
      final region = close(f);
      stack.removeLast();
      if (stack.isEmpty) return region;
      stack.last.regions.add(region);
    }
  }

  /// The region `f`, its nodes all read, with its results line.
  Region close(_Open f) {
    final path = f.path;
    final List<Src> results;
    switch (i < lines.length ? lines[i] : null) {
      case (_Line(body: _Results(results: final rs), path: final p), _) when _samePath(p, path):
        results = rs;
      case (final l, final no) when _startsWith(l.path, path):
        final n = f.nodes.length;
        final count = n == 1 ? '1 node' : '$n nodes';
        throw ZirError(
          'line $no: ${l.what()} is not in the graph: region ${_show(path)} has $count before '
          'it, numbered from 0',
        );
      default:
        throw ZirError('region ${_show(path)} has no results line');
    }
    i++;
    return Region(f.header.kind, f.header.args, f.nodes, results);
  }
}

bool _ident(int c) =>
    (c >= 0x61 && c <= 0x7a) ||
    (c >= 0x41 && c <= 0x5a) ||
    (c >= 0x30 && c <= 0x39) ||
    c == 0x5f ||
    (c > 0x7f && isXidContinue(c));

bool _digit(int c) => c >= 0x30 && c <= 0x39;

/// A cursor over one line.
final class _P {
  final String s;
  int i = 0;

  _P(this.s);

  String get rest => s.substring(i);

  /// The code point at `j`, or -1 at the end.
  int _at(int j) => j < s.length ? s.codeUnitAt(j) : -1;

  int get _peek => _at(i);

  /// The code point at `j` and its width in code units.
  (int, int) _cp(int j) {
    final c = s.codeUnitAt(j);
    if (c >= 0xd800 && c < 0xdc00 && j + 1 < s.length) {
      final d = s.codeUnitAt(j + 1);
      if (d >= 0xdc00 && d < 0xe000) return (0x10000 + ((c - 0xd800) << 10) + (d - 0xdc00), 2);
    }
    return (c, 1);
  }

  void ws() {
    while (_peek == 0x20) {
      i++;
    }
  }

  /// Consumes `t`, after spaces, when it comes next.
  bool eat(String t) {
    ws();
    if (s.startsWith(t, i)) {
      i += t.length;
      return true;
    }
    return false;
  }

  /// Consumes the word `w` when it comes next and is not the start of a longer word.
  bool eatWord(String w) {
    ws();
    if (s.startsWith(w, i) && (i + w.length == s.length || !_ident(_cp(i + w.length).$1))) {
      i += w.length;
      return true;
    }
    return false;
  }

  void expect(String t) {
    if (!eat(t)) throw _Fail('expected `$t`, found ${found()}');
  }

  String found() {
    final t = rest.split(' ').first;
    return t.isEmpty ? 'the end of the line' : '`$t`';
  }

  /// A run of name characters.
  String word() {
    ws();
    var j = i;
    while (j < s.length) {
      final (c, w) = _cp(j);
      if (!_ident(c)) break;
      j += w;
    }
    if (j == i) throw _Fail('expected a name, found ${found()}');
    final w = s.substring(i, j);
    i = j;
    return w;
  }

  /// A run of characters up to a space or one of `stop`.
  String token(String stop) {
    ws();
    var j = i;
    while (j < s.length && s[j] != ' ' && !stop.contains(s[j])) {
      j++;
    }
    final t = s.substring(i, j);
    i = j;
    return t;
  }

  /// A run of digits and `-` read as a 64-bit integer, not negative when `!signed`.
  int number({bool signed = true}) {
    ws();
    var j = i;
    while (j < s.length && (_digit(s.codeUnitAt(j)) || s[j] == '-')) {
      j++;
    }
    final t = s.substring(i, j);
    final v = signed || !t.contains('-') ? int.tryParse(t) : null;
    if (v == null) throw _Fail('expected a number, found ${found()}');
    i = j;
    return v;
  }

  List<T> list<T>(String open, String close, String sep, T Function() item) {
    expect(open);
    final out = <T>[];
    if (eat(close)) return out;
    while (true) {
      out.add(item());
      if (eat(close)) return out;
      expect(sep);
    }
  }

  _Line line() {
    final path = this.path();
    final _Body body;
    if (eatWord('region')) {
      if (path.length.isOdd) throw _Fail('${_show(path)} is a node\'s path, not a region\'s');
      final k = word();
      final kind = RegionKind.values.where((x) => x.name == k).firstOrNull;
      if (kind == null) throw _Fail('`$k` is not a region kind');
      body = _Header(kind, list('(', ')', ';', edge));
    } else if (eatWord('results')) {
      if (path.length.isOdd) throw _Fail('${_show(path)} is a node\'s path, not a region\'s');
      body = _Results(list('(', ')', ',', () => src(path)));
    } else {
      if (path.length.isEven) {
        throw _Fail('${_show(path)} is a region\'s path, and its lines are `region` and `results`');
      }
      final op = this.op();
      final region = path.sublist(0, path.length - 1);
      final inputs = list('(', ')', ',', () => src(region));
      expect('->');
      body = _NodeLine(op, inputs, list('(', ')', ';', edge));
    }
    ws();
    if (rest.isNotEmpty) throw _Fail('unexpected ${found()} after the line');
    return _Line(path, body);
  }

  List<int> path() {
    ws();
    if (_peek != 0x72) throw _Fail('expected a path such as `r.0`, found ${found()}');
    i++;
    final path = <int>[];
    while (_peek == (path.length.isEven ? 0x2e : 0x2f)) {
      i++;
      path.add(number(signed: false));
    }
    return path;
  }

  Src src(List<int> region) {
    ws();
    if (_peek != 0x72) return Const(value());
    final start = i;
    final path = this.path();
    expect('^');
    final k = number(signed: false);
    if (_samePath(path, region)) return Arg(k);
    if (path.length == region.length + 1 && _startsWith(path, region)) {
      return Out(path[region.length], k);
    }
    i = start;
    throw _Fail(
      '${_show(path)}^$k is not an edge of region ${_show(region)}, and a region reads only '
      'its own edges',
    );
  }

  Op op() {
    final name = word();
    switch (name) {
      case 'reindex':
        return switch (word()) {
          'residue' => const ReindexOp(Residue()),
          'catalog' => ReindexOp(Catalog(token('('))),
          final w => throw _Fail('`reindex` takes `residue` or `catalog`, not `$w`'),
        };
      case 'discard':
        return const DiscardOp();
      case 'fold':
        final depth = number(signed: false);
        final identity = eatWord('identity');
        return FoldOp(depth, identity, evidence());
      case 'fix':
        final lattice = switch (word()) {
          'lattice' => true,
          'definedness' => false,
          final w => throw _Fail('`fix` is `lattice` or `definedness`, not `$w`'),
        };
        return FixOp(lattice, evidence());
      case 'gen':
        return GenOp(switch (word()) {
          'before' => GuardPos.before,
          'after' => GuardPos.after,
          final w => throw _Fail('`gen` tests its guard `before` or `after`, not `$w`'),
        });
      case 'port':
        return switch (word()) {
          'read' => ReadOp(word()),
          'push' => PushOp(word()),
          final w => throw _Fail('`port` is `read` or `push`, not `$w`'),
        };
      case 'fam':
        return const FamOp();
      case 'group' || 'rank' || 'scan' || 'join':
        return DerivedOp(Derived.values.byName(name));
      case 'prim':
        final t = token('(');
        final p = _prims[t];
        if (p == null) throw _Fail('`$t` is not a primitive');
        return PrimOp(p);
      case 'apply':
        return const ApplyOp();
      case 'lambda':
        return const LambdaOp();
      case 'if':
        return const IfOp();
      case 'match':
        return MatchOp(list('[', ']', ',', pattern));
      case 'rec':
        return const RecOp();
      case 'wave':
        return const WaveOp();
      default:
        throw _Fail('`$name` is not a ZIR operation');
    }
  }

  Evidence evidence() {
    final items = list('{', '}', ',', () {
      final k = word();
      expect(':');
      final g = word();
      final grade = Grade.values.where((x) => x.name == g).firstOrNull;
      if (grade == null) throw _Fail('`$g` is not a grade');
      return (k, grade);
    });
    return Evidence()..addEntries([for (final (k, g) in items) MapEntry(k, g)]);
  }

  Edge edge() {
    if (eatWord('state')) return StateEdge(word());
    final type = ty();
    var (ints, congruence, finite) = (anyDomain.ints, anyDomain.congruence, anyDomain.finite);
    final facets = <Facet>[];
    while (true) {
      if (eatWord('in')) {
        ints = intervals();
      } else if (eatWord('class')) {
        congruence = this.congruence();
      } else if (eatWord('set')) {
        finite = FiniteSet.of(list('{', '}', ',', number));
      } else if (eatWord('facet') || eatWord('hint')) {
        final hint = s.substring(0, i).endsWith('hint');
        final kind = word();
        facets.add(Facet(kind, value(), hint: hint));
      } else {
        return ValueEdge(type, domain: Domain(ints, congruence, finite), facets: facets);
      }
    }
  }

  IntervalSet intervals() => IntervalSet.fromPieces(
    list('[', ']', ',', () {
      ws();
      final End lo = _peek == 0x2e ? negInf : Fin(number());
      expect('..');
      if (_peek == 0x3d) {
        i++;
        return (lo, Fin(number()));
      }
      return (lo, posInf);
    }),
  );

  Congruence congruence() {
    if (eat('{}')) return Congruence.bottom;
    if (eatWord('any')) return Congruence.top;
    final r = number();
    if (eatWord('mod')) return Congruence(number(signed: false), r);
    return Congruence.single(r);
  }

  Type ty() {
    ws();
    if (eat('(')) {
      final head = token('();,');
      final ts = <Type>[];
      while (!eat(')')) {
        if (rest.isEmpty) throw const _Fail('expected `)`, found the end of the line');
        ts.add(ty());
      }
      void arity(int n) {
        if (ts.length != n) throw _Fail('`($head …)` takes $n types, and has ${ts.length}');
      }

      switch (head) {
        case '|':
          return Type.unionAll(ts);
        case '&':
          return Type.meetAll(ts);
        case '!':
          arity(1);
          return ~ts[0];
        case '\\' when ts.isNotEmpty:
          return ts.skip(1).fold(ts[0], (a, t) => a - t);
        case 'tuple':
          return Type.tuple(ts);
        case '->' when ts.length == 2:
          return Type.morphism(ts[0], ts[0], ts[1]);
        case '->':
          arity(3);
          return Type.morphism(ts[0], ts[1], ts[2]);
        case '->?':
          arity(2);
          return Type.morphism(Type.empty, ts[0], ts[1]);
        case final h when h.length > 1 && h.startsWith('#'):
          arity(1);
          return Type.atomWith(h.substring(1), ts[0]);
        case final h:
          throw _Fail('`($h …)` is not a type form');
      }
    }
    final c = _peek;
    if (c == 0x22 || _digit(c) || c == 0x2d) return _lit(value());
    final start = i;
    final w = token('();,[]{}');
    switch (w) {
      case '_':
        return Type.top;
      case 'bool':
        return Type.boolean;
      case 'int':
        return Type.integer;
      case 'rat':
        return Type.rational;
      case 'f64':
        return Type.f64;
      case 'String':
        return Type.string;
      case 'tuple':
        return Type.universe(Universe.tuple);
      case 'struct':
        return Type.universe(Universe.struct);
      case 'morphism':
        return Type.universe(Universe.morphism);
      case '#_':
        return _allAtoms;
      case 'true' || 'false' || 'nan' || 'inf':
        i = start;
        return _lit(value());
      case final w when w.length > 1 && w.startsWith('#') && w.substring(1).runes.every(_ident):
        return Type.atom(w.substring(1));
      default:
        i = start;
        throw _Fail(
          '`$w` is not a type of the text form; a recursive type has none until step L2 '
          'declares types',
        );
    }
  }

  Value value() {
    ws();
    switch (_peek) {
      case 0x22:
        return Str(string());
      case 0x23:
        i++;
        final name = word();
        if (_peek != 0x28) return Atom(name);
        final fields = <String>[];
        final args = list('(', ')', ',', () {
          ws();
          final save = i;
          try {
            final f = word();
            if (s.startsWith(': ', i)) {
              i++;
              fields.add(f);
              return value();
            }
          } on _Fail {
            // Not a field name: a positional value.
          }
          i = save;
          return value();
        });
        if (fields.isEmpty) return Atom(name, args);
        if (fields.length != args.length) {
          throw _Fail('atom `#$name` mixes named and positional payload');
        }
        return Atom.named(name, [for (final (j, f) in fields.indexed) (f, args[j])]) ??
            (throw _Fail('atom `#$name` names a field twice'));
      case 0x28:
        return Tuple(list('(', ')', ',', value));
      case 0x5b:
        return Path(list('[', ']', '->', value));
      case 0x7b:
        expect('{');
        if (eat('}')) return const Family.empty();
        var item = value();
        final map = eat('->');
        final entries = <(Value, Value)>[];
        while (true) {
          entries.add((item, map ? value() : item));
          if (eat('}')) break;
          expect(',');
          item = value();
          if (map) expect('->');
        }
        try {
          return Family.of(entries);
        } on ArgumentError {
          // Each key is written once; the reader names the fault instead of failing.
          throw const _Fail('the family has a key twice');
        }
      default:
        final t = token('()[]{},;^');
        return _number(t) ?? (throw _Fail('expected a value, found `$t`'));
    }
  }

  String string() {
    expect('"');
    final out = StringBuffer();
    var j = i;
    while (j < s.length) {
      final (c, w) = _cp(j);
      j += w;
      if (c == 0x22) {
        i = j;
        return '$out';
      }
      if (c != 0x5c) {
        out.writeCharCode(c);
        continue;
      }
      if (j >= s.length) throw const _Fail('an unfinished escape');
      final (e, ew) = _cp(j);
      j += ew;
      switch (e) {
        case 0x6e:
          out.write('\n');
        case 0x72:
          out.write('\r');
        case 0x74:
          out.write('\t');
        case 0x30:
          out.write('\x00');
        case 0x5c || 0x22 || 0x27:
          out.writeCharCode(e);
        case 0x75:
          if (j >= s.length || s.codeUnitAt(j) != 0x7b) {
            throw const _Fail('`\\u` is followed by `{`');
          }
          j++;
          final hex = StringBuffer();
          while (j < s.length) {
            final (h, hw) = _cp(j);
            j += hw;
            if (h == 0x7d) break;
            hex.writeCharCode(h);
          }
          final v = RegExp(r'^\+?[0-9a-fA-F]+$').hasMatch('$hex')
              ? int.tryParse('$hex'.replaceFirst('+', ''), radix: 16)
              : null;
          if (v == null || v > 0x10ffff || (v >= 0xd800 && v < 0xe000)) {
            throw _Fail('`\\u{$hex}` is not a character');
          }
          out.writeCharCode(v);
        default:
          throw _Fail('`\\${String.fromCharCode(e)}` is not an escape');
      }
    }
    throw const _Fail('the string has no closing `"`');
  }

  Pattern pattern() {
    ws();
    if (eat('=')) return LitP(value());
    if (eatWord('#_')) return const AnyAtomP();
    if (eat('#')) {
      final name = word();
      if (_peek != 0x28) return AtomP(name);
      if (s.startsWith('()', i)) {
        i += 2;
        return FieldsP(name, const []);
      }
      final save = i;
      i++;
      var named = false;
      try {
        word();
        named = s.startsWith(': ', i);
      } on _Fail {
        // Not a field name.
      }
      i = save;
      if (named) {
        return FieldsP(
          name,
          list('(', ')', ',', () {
            final f = word();
            expect(':');
            return (f, pattern());
          }),
        );
      }
      return AtomP(name, list('(', ')', ',', pattern));
    }
    if (eat('(')) {
      if (eatWord('is')) {
        final t = ty();
        expect(')');
        return IsP(t);
      }
      final ps = <Pattern>[];
      while (!eat(')')) {
        ps.add(pattern());
        if (!eat(',')) {
          expect(')');
          break;
        }
      }
      return TupleP(ps);
    }
    final w = word();
    return w == '_' ? const WildP() : BindP(w);
  }
}

/// The type of the one value `v`.
Type _lit(Value v) => Type.lit(v) ?? (throw _Fail('`$v` is not a literal type'));

/// Every atom: the scalars that are not booleans, numbers or strings.
final _allAtoms = [
  Type.boolean,
  Type.integer,
  Type.rational,
  Type.f64,
  Type.string,
].fold(Type.universe(Universe.scalar), (a, t) => a - t);

final _integer = RegExp(r'^-?[0-9]+$');

/// A number, as the kernel prints numbers: `3`, `-2r/3r`, `1.5`, `1.0e300`, `nan`, `-inf`.
Value? _number(String t) {
  switch (t) {
    case 'true':
      return const Bool(true);
    case 'false':
      return const Bool(false);
    case 'nan':
      return Float(double.nan);
    case 'inf':
      return Float(double.infinity);
    case '-inf':
      return Float(double.negativeInfinity);
  }
  if (t.contains('r')) {
    final parts = t.split('/');
    if (parts.length > 2) return null;
    BigInt? big(String s) => s.endsWith('r') && _integer.hasMatch(s.substring(0, s.length - 1))
        ? BigInt.parse(s.substring(0, s.length - 1))
        : null;
    final num = big(parts[0]);
    final den = parts.length == 2 ? big(parts[1]) : BigInt.one;
    return num == null || den == null ? null : Rat.make(num, den);
  }
  if (t.contains('.') || t.contains('e')) {
    if (!RegExp(r'^[-+]?([0-9]+\.?[0-9]*|\.[0-9]+)([eE][-+]?[0-9]+)?$').hasMatch(t)) return null;
    return Float(double.parse(t));
  }
  if (!_integer.hasMatch(t)) return null;
  return Value.integer(BigInt.parse(t));
}
