/// The binary form of ZIR: what a build caches and the backends read.
///
/// It begins with the four bytes `ZIR\0` and the version as a 32-bit little-endian word; the
/// root region follows. Every count, index and integer is a 64-bit little-endian word, every
/// name a count of bytes and then its UTF-8 bytes, and every choice a one-byte tag: the index
/// of the choice in its enum below, or in [RegionKind], [Grade], [GuardPos], [Derived] or
/// [Prim]. A value is written by its structure, a number outside the 64-bit range and a
/// rational by their decimal digits, and a float by its bits, so every value comes back bit
/// for bit. An edge is written as its text form ([edge]): a type's representation is private
/// to the kernel, and its printed form is its exact, canonical description. A decoding error
/// names the byte offset at which it was found. Regions nest as deep as the program does, so
/// the writer and the reader keep their own stacks.
library;

import 'dart:convert';
import 'dart:typed_data';

import '../kernel/term.dart';
import '../kernel/text.dart' show compareUtf8;
import '../kernel/value.dart';
import 'graph.dart';
import 'text.dart';

const _magic = [0x5a, 0x49, 0x52, 0x00];

/// The one NaN word the form writes: the quiet NaN with a zero payload.
const nanBits = 0x7ff8000000000000;

/// The tags of a source.
enum _SrcTag { arg, out, constant }

/// The tags of a value.
enum _ValueTag { boolean, int, big, rat, float, str, atom, tuple, path, family }

/// The tags of an operation.
enum _OpTag {
  reindexResidue,
  reindexCatalog,
  discard,
  fold,
  fix,
  gen,
  read,
  push,
  fam,
  derived,
  prim,
  apply,
  lambda,
  ifElse,
  match,
  rec,
  wave,
}

/// The tags of a pattern.
enum _PatternTag { wild, bind, lit, atom, fields, tuple, anyAtom, isType }

// ---------------------------------------------------------------------------------------------
// Writing

/// The binary form of the graph rooted at `root`.
Uint8List encode(Region root) {
  final w = _W()
    ..bytes.add(_magic)
    ..bytes.add((ByteData(4)..setUint32(0, version, Endian.little)).buffer.asUint8List());
  w.graph(root);
  return w.bytes.takeBytes();
}

final class _W {
  final bytes = BytesBuilder(copy: false);
  final _word = ByteData(8);

  /// What is left to write, the next on top.
  final _todo = <void Function()>[];

  void tag(Enum t) => bytes.addByte(t.index);

  void flag(bool b) => bytes.addByte(b ? 1 : 0);

  void n(int n) {
    _word.setInt64(0, n, Endian.little);
    bytes.add(Uint8List.fromList(_word.buffer.asUint8List()));
  }

  void s(String s) {
    final b = utf8.encode(s);
    n(b.length);
    bytes.add(b);
  }

  void many<T>(List<T> xs, void Function(T) f) {
    n(xs.length);
    xs.forEach(f);
  }

  void graph(Region root) {
    region(root);
    while (_todo.isNotEmpty) {
      _todo.removeLast()();
    }
  }

  /// Writes the region's header and node count, and leaves its nodes and results to do.
  void region(Region r) {
    tag(r.kind);
    many(r.args, edge);
    n(r.nodes.length);
    _todo.add(() => many(r.results, src));
    for (final x in r.nodes.reversed) {
      _todo.add(() => node(x));
    }
  }

  /// Writes the node and its region count, and leaves its regions to do.
  void node(Node x) {
    op(x.op);
    many(x.inputs, src);
    many(x.outputs, edge);
    n(x.regions.length);
    for (final r in x.regions.reversed) {
      _todo.add(() => region(r));
    }
  }

  void edge(Edge e) => s('$e');

  void src(Src x) {
    switch (x) {
      case Arg(:final i):
        tag(_SrcTag.arg);
        n(i);
      case Out(:final node, :final port):
        tag(_SrcTag.out);
        n(node);
        n(port);
      case Const(:final value):
        tag(_SrcTag.constant);
        this.value(value);
    }
  }

  void value(Value v) {
    switch (v) {
      case Bool(:final value):
        tag(_ValueTag.boolean);
        flag(value);
      case Int(:final value):
        tag(_ValueTag.int);
        n(value);
      case Big(:final value):
        tag(_ValueTag.big);
        s('$value');
      case Rat(:final num, :final den):
        tag(_ValueTag.rat);
        s('$num');
        s('$den');
      case Float(:final x):
        tag(_ValueTag.float);
        n(x.isNaN ? nanBits : f64Bits(x));
      case Str(:final text):
        tag(_ValueTag.str);
        s(text.text);
      case Atom(:final name, :final fields, :final args):
        tag(_ValueTag.atom);
        s(name);
        many(fields, s);
        many(args, value);
      case Tuple(:final items):
        tag(_ValueTag.tuple);
        many(items, value);
      case Path(:final keys):
        tag(_ValueTag.path);
        many(keys, value);
      case Family f:
        tag(_ValueTag.family);
        many(f.entries.toList(), (e) {
          value(e.$1);
          value(e.$2);
        });
    }
  }

  void evidence(Evidence ev) => many(ev.entries.toList(), (e) {
    s(e.key);
    tag(e.value);
  });

  void op(Op o) {
    switch (o) {
      case ReindexOp(witness: Residue()):
        tag(_OpTag.reindexResidue);
      case ReindexOp(witness: Catalog(:final law)):
        tag(_OpTag.reindexCatalog);
        s(law);
      case DiscardOp():
        tag(_OpTag.discard);
      case FoldOp(:final depth, :final identity, :final ev):
        tag(_OpTag.fold);
        n(depth);
        flag(identity);
        evidence(ev);
      case FixOp(:final lattice, :final ev):
        tag(_OpTag.fix);
        flag(lattice);
        evidence(ev);
      case GenOp(:final pos):
        tag(_OpTag.gen);
        tag(pos);
      case ReadOp(:final port):
        tag(_OpTag.read);
        s(port);
      case PushOp(:final port):
        tag(_OpTag.push);
        s(port);
      case FamOp():
        tag(_OpTag.fam);
      case DerivedOp(:final derived):
        tag(_OpTag.derived);
        tag(derived);
      case PrimOp(:final prim):
        tag(_OpTag.prim);
        tag(prim);
      case ApplyOp():
        tag(_OpTag.apply);
      case LambdaOp():
        tag(_OpTag.lambda);
      case IfOp():
        tag(_OpTag.ifElse);
      case MatchOp(:final patterns):
        tag(_OpTag.match);
        many(patterns, pattern);
      case RecOp():
        tag(_OpTag.rec);
      case WaveOp():
        tag(_OpTag.wave);
    }
  }

  void pattern(Pattern p) {
    switch (p) {
      case WildP():
        tag(_PatternTag.wild);
      case BindP(:final name):
        tag(_PatternTag.bind);
        s(name);
      case LitP(:final value):
        tag(_PatternTag.lit);
        this.value(value);
      case AtomP(:final name, :final args):
        tag(_PatternTag.atom);
        s(name);
        many(args, pattern);
      case FieldsP(:final name, :final fields):
        tag(_PatternTag.fields);
        s(name);
        many(fields, (f) {
          s(f.$1);
          pattern(f.$2);
        });
      case TupleP(:final items):
        tag(_PatternTag.tuple);
        many(items, pattern);
      case AnyAtomP():
        tag(_PatternTag.anyAtom);
      case IsP(:final type):
        tag(_PatternTag.isType);
        s('$type');
    }
  }
}

// ---------------------------------------------------------------------------------------------
// Reading

/// The graph encoded in `bytes`, which [validate] has not yet checked; throws a [ZirError].
Region decode(Uint8List bytes) {
  final r = _R(bytes);
  final m = r.take(4);
  if (Iterable<int>.generate(4).any((i) => m[i] != _magic[i])) {
    throw const ZirError('byte 0: the data does not start `ZIR\\0`');
  }
  final v = ByteData.sublistView(r.take(4)).getUint32(0, Endian.little);
  if (v != version) {
    throw ZirError('byte 4: version $v, and this compiler reads version $version');
  }
  final root = r.graph();
  if (r.i != bytes.length) {
    final what = bytes.length - r.i == 1 ? '1 byte follows' : 'bytes follow';
    throw ZirError('byte ${r.i}: $what the graph, which ends here');
  }
  return root;
}

/// A region read up to its nodes: `count` nodes, of which `nodes` are read.
final class _OpenRegion {
  final RegionKind kind;
  final List<Edge> args;
  final int count;
  final nodes = <Node>[];

  _OpenRegion(this.kind, this.args, this.count);
}

/// A node read up to its regions: `count` regions, of which `regions` are read.
final class _OpenNode {
  final Op op;
  final List<Src> inputs;
  final List<Edge> outputs;
  final int count;
  final regions = <Region>[];

  _OpenNode(this.op, this.inputs, this.outputs, this.count);
}

final class _R {
  final Uint8List b;
  int i = 0;

  _R(this.b);

  Never err(int at, String e) => throw ZirError('byte $at: $e');

  Uint8List take(int n) {
    if (b.length - i < n) err(i, 'the data ends, and $n more bytes were expected');
    final out = Uint8List.sublistView(b, i, i + n);
    i += n;
    return out;
  }

  /// The choice among `values` that the next tag names; `what` names the choice in a message.
  T tag<T extends Enum>(List<T> values, String what) {
    final at = i;
    final t = take(1)[0];
    if (t >= values.length) err(at, '$t is not a tag of $what');
    return values[t];
  }

  /// A boolean: the tag 0 or 1.
  bool flag() {
    final at = i;
    final t = take(1)[0];
    if (t > 1) err(at, '$t is not a tag of a boolean');
    return t == 1;
  }

  int n() => ByteData.sublistView(take(8)).getInt64(0, Endian.little);

  /// The word read as unsigned, for a message.
  static String _unsigned(int n) => '${BigInt.from(n).toUnsigned(64)}';

  /// A count: no more than the bytes left, since every item takes at least one.
  int len() {
    final at = i;
    final n = this.n();
    if (n < 0 || n > b.length - i) {
      err(at, 'the count ${_unsigned(n)} is more than the bytes left');
    }
    return n;
  }

  /// An index or a depth, which has no bound in the data but must be a non-negative integer.
  int idx() {
    final at = i;
    final n = this.n();
    if (n < 0) err(at, 'the index ${_unsigned(n)} is too large');
    return n;
  }

  String s() {
    final n = len();
    final at = i;
    try {
      return utf8.decode(take(n));
    } on FormatException {
      err(at, 'a name is not UTF-8');
    }
  }

  List<T> many<T>(T Function() f) => [for (var k = len(); k > 0; k--) f()];

  /// The root region, read with a stack of the regions and nodes still open.
  Region graph() {
    final open = <Object>[openRegion()];
    while (true) {
      switch (open.last) {
        case _OpenRegion f when f.nodes.length < f.count:
          open.add(_OpenNode(op(), many(src), many(edge), len()));
        case _OpenRegion f:
          final r = Region(f.kind, f.args, f.nodes, many(src));
          open.removeLast();
          if (open.isEmpty) return r;
          (open.last as _OpenNode).regions.add(r);
        case _OpenNode f when f.regions.length < f.count:
          open.add(openRegion());
        case final _OpenNode f:
          open.removeLast();
          (open.last as _OpenRegion).nodes.add(Node(f.op, f.inputs, f.outputs, f.regions));
      }
    }
  }

  _OpenRegion openRegion() =>
      _OpenRegion(tag(RegionKind.values, 'a region kind'), many(edge), len());

  Edge edge() {
    final at = i;
    final t = s();
    try {
      return parseEdge(t);
    } on ZirError catch (e) {
      err(at, 'the edge `$t`: ${e.message}');
    }
  }

  Src src() => switch (tag(_SrcTag.values, 'a source')) {
    _SrcTag.arg => Arg(idx()),
    _SrcTag.out => Out(idx(), idx()),
    _SrcTag.constant => Const(value()),
  };

  BigInt big() {
    final at = i;
    final t = s();
    return (RegExp(r'^[-+]?[0-9]+$').hasMatch(t) ? BigInt.tryParse(t) : null) ??
        err(at, '`$t` is not an integer');
  }

  Value value() {
    final at = i;
    switch (tag(_ValueTag.values, 'a value')) {
      case _ValueTag.boolean:
        return Bool(flag());
      case _ValueTag.int:
        return Int(n());
      case _ValueTag.big:
        return Value.integer(big());
      case _ValueTag.rat:
        final (num, den) = (big(), big());
        return Rat.make(num, den) ?? err(at, 'a rational with denominator 0');
      case _ValueTag.float:
        return Float(f64FromBits(n()));
      case _ValueTag.str:
        return Str(s());
      case _ValueTag.atom:
        final name = s();
        final fields = many(s);
        final args = many(value);
        for (var k = 1; k < fields.length; k++) {
          if (compareUtf8(fields[k - 1], fields[k]) >= 0) {
            err(at, 'atom `#$name` has its fields out of order or repeated');
          }
        }
        if (fields.isNotEmpty && fields.length != args.length) {
          err(at, 'atom `#$name` has ${fields.length} fields and ${args.length} values');
        }
        return Atom.raw(name, fields, args);
      case _ValueTag.tuple:
        return Tuple(many(value));
      case _ValueTag.path:
        return Path(many(value));
      case _ValueTag.family:
        final entries = many(() => (value(), value()));
        try {
          return Family.of(entries);
        } on ArgumentError {
          err(at, 'the family has a key twice');
        }
    }
  }

  Evidence evidence() {
    final items = many(() => MapEntry(s(), tag(Grade.values, 'a grade')));
    return Evidence()..addEntries(items);
  }

  Op op() => switch (tag(_OpTag.values, 'an operation')) {
    _OpTag.reindexResidue => const ReindexOp(Residue()),
    _OpTag.reindexCatalog => ReindexOp(Catalog(s())),
    _OpTag.discard => const DiscardOp(),
    _OpTag.fold => FoldOp(idx(), flag(), evidence()),
    _OpTag.fix => FixOp(flag(), evidence()),
    _OpTag.gen => GenOp(tag(GuardPos.values, 'a guard position')),
    _OpTag.read => ReadOp(s()),
    _OpTag.push => PushOp(s()),
    _OpTag.fam => const FamOp(),
    _OpTag.derived => DerivedOp(tag(Derived.values, 'a derived node')),
    _OpTag.prim => PrimOp(tag(Prim.values, 'a primitive')),
    _OpTag.apply => const ApplyOp(),
    _OpTag.lambda => const LambdaOp(),
    _OpTag.ifElse => const IfOp(),
    _OpTag.match => MatchOp(many(pattern)),
    _OpTag.rec => const RecOp(),
    _OpTag.wave => const WaveOp(),
  };

  Pattern pattern() {
    switch (tag(_PatternTag.values, 'a pattern')) {
      case _PatternTag.wild:
        return const WildP();
      case _PatternTag.bind:
        return BindP(s());
      case _PatternTag.lit:
        return LitP(value());
      case _PatternTag.atom:
        final name = s();
        return AtomP(name, many(pattern));
      case _PatternTag.fields:
        final name = s();
        return FieldsP(name, many(() => (s(), pattern())));
      case _PatternTag.tuple:
        return TupleP(many(pattern));
      case _PatternTag.anyAtom:
        return const AnyAtomP();
      case _PatternTag.isType:
        final at = i;
        final t = s();
        try {
          return IsP(parseType(t));
        } on ZirError catch (e) {
          err(at, 'the type `$t`: ${e.message}');
        }
    }
  }
}
