/// The compiler as queries (step L1.30): each stage is a query whose result is memoized under
/// a content hash of everything it reads, so asking again after an edit recomputes only the
/// queries whose inputs changed.
///
/// Three queries exist at L1. The front end (lexing through elaboration) is keyed by the
/// unit's text, since every structure before the kernel terms carries byte spans and so
/// changes with any edit. A row of a function's `test` table is keyed by its check and the
/// definitions the check reaches, and a row of `main`'s table by its key, its value, the
/// ports, and the definitions `main` and those terms reach: kernel terms carry no spans, so
/// an edit that leaves those definitions alone (a comment, another function, another row)
/// reuses the row's result. This cutoff is the point of the structure.
///
/// The hashes are syntactic, as step L1.30 allows: a key hashes the terms' structure, so two
/// spellings of one value are two keys, which costs a recomputation and never a wrong answer.
/// Canonical (alpha-invariant) keys are the canonicalizer's addresses, which the queries take
/// over when they move onto the engine (step L7.13). A key is the BLAKE3-256 hash of
/// `zed-query\0`, the query's name, and its parts, each written as its length in bytes and
/// then its bytes, so no two different part lists share a key.
///
/// Where DESIGN.md does not say: results are kept for the life of the [Db] and never evicted,
/// which a long-lived process (the language server, step L25.1) must bound; the interpreter
/// and the prelude are fixed for one build of the compiler, so they are not hashed.
library;

import 'dart:convert';
import 'dart:typed_data';

import 'ast.dart' show Stmt;
import 'canon.dart' show blake3;
import 'elab.dart' show Cones, Unit;
import 'kernel.dart';
import 'run.dart' show Diagnostics, compile;

/// A query's key: a content hash of its inputs.
final class Key {
  final Uint8List bytes;

  Key(this.bytes);

  @override
  bool operator ==(Object other) {
    if (other is! Key) return false;
    for (var i = 0; i < 32; i++) {
      if (bytes[i] != other.bytes[i]) return false;
    }
    return true;
  }

  @override
  int get hashCode => ByteData.sublistView(bytes).getInt64(0);
}

/// The key of query `name` over `parts`.
Key key(String name, List<List<int>> parts) {
  final b = BytesBuilder(copy: false)..add(utf8.encode('zed-query\x00'));
  void put(List<int> p) => b
    ..add(_word(p.length))
    ..add(p);
  put(utf8.encode(name));
  parts.forEach(put);
  return Key(blake3(b.takeBytes()));
}

Uint8List _word(int n) => (ByteData(8)..setUint64(0, n, Endian.little)).buffer.asUint8List();

/// The queries.
enum Query {
  /// Lexing through elaboration, keyed by the text.
  front,

  /// A row of a function's table.
  row,

  /// A row of `main`'s table: one wave.
  wave,
}

/// The memoized results, and how many times each query was computed rather than reused.
final class Db {
  /// Each text's statements and elaboration, or the diagnostics that rejected it.
  final _front = <Key, Object>{};

  /// Each row's failure, or null when it passes.
  final _rows = <(Query, Key), String?>{};

  final _computed = <Query, int>{};

  /// The front end's result for the unit `text`; throws the kept [Diagnostics] when it is
  /// rejected.
  (List<Stmt>, Unit) front(String text) {
    final f = _front.putIfAbsent(key('front', [utf8.encode(text)]), () {
      _count(Query.front);
      try {
        return compile(text);
      } on Diagnostics catch (e) {
        return e;
      }
    });
    if (f is Diagnostics) throw f;
    return f as (List<Stmt>, Unit);
  }

  /// The failure of the table row `q` under `k`, or null when it passes, computing it with
  /// `check` when no result is kept.
  String? row(Query q, Key k, String? Function() check) {
    if (_rows.containsKey((q, k))) return _rows[(q, k)];
    _count(q);
    return _rows[(q, k)] = check();
  }

  /// How many times query `q` has been computed.
  int computed(Query q) => _computed[q] ?? 0;

  void _count(Query q) => _computed[q] = computed(q) + 1;
}

/// The syntactic bytes of the definitions of the unit of `cones` that `roots` reach, in the
/// unit's order, followed by the roots: what a term evaluated under the unit can read.
Uint8List cone(Cones cones, List<Term> roots) {
  final out = _Encoder();
  for (final d in cones.defs(roots)) {
    out
      ..add(d.kernel)
      ..add(d.term);
  }
  roots.forEach(out.add);
  return out.bytes.takeBytes();
}

/// Writes terms by their structure: each node is its kind and then its fields, a string its
/// length and its bytes, a list its length and its items, so two different terms never share
/// bytes. A value or a type is its kind and its printed form, which is exact within a kind.
/// The walk keeps its own stack, since a term may nest deeper than the call stack.
final class _Encoder {
  final bytes = BytesBuilder(copy: false);

  void add(Object root) {
    final todo = <Object?>[root];
    // Pushes `items` so that they are written in order.
    void then(List<Object?> items) => todo.addAll(items.reversed);
    while (todo.isNotEmpty) {
      switch (todo.removeLast()) {
        case null:
          bytes.addByte(0);
        case final int n:
          bytes.add(_word(n));
        case final String s:
          final b = utf8.encode(s);
          bytes
            ..add(_word(b.length))
            ..add(b);
        case final List<Object?> l:
          then([l.length, ...l]);
        case (final Object? a, final Object? b):
          then([a, b]);
        case final Value v:
          then(['value ${v.runtimeType}', '$v']);
        case final Type t:
          then(['type', '$t']);
        case final Enum e:
          then(['${e.runtimeType} ${e.name}']);
        case final Map<String, Grade> ev:
          then([for (final MapEntry(:key, :value) in ev.entries) (key, value)]);
        case final Term t:
          then(switch (t) {
            Lit(:final value) => ['lit', value],
            Var(:final name) => ['var', name],
            Lam(:final params, :final body) => ['lam', params, body],
            App(:final f, :final args) => ['app', f, args],
            PrimApp(:final prim, :final args) => ['primapp', prim, args],
            PrimFn(:final prim) => ['primfn', prim],
            Let(:final name, :final value, :final body) => ['let', name, value, body],
            If(:final cond, :final then, :final orElse) => ['if', cond, then, orElse],
            Match(:final scrutinee, :final arms) => ['match', scrutinee, arms],
            Fam(:final domain, :final variable, :final body) => ['fam', domain, variable, body],
            Reindex(:final family, :final kf, :final vf, :final witness) => [
              'reindex',
              family,
              kf,
              vf,
              witness,
            ],
            Discard(:final family, :final sel) => ['discard', family, sel],
            Fold(:final family, :final op, :final identity, :final depth, :final ev) => [
              'fold',
              family,
              op,
              identity,
              depth,
              ev,
            ],
            Fix(:final init, :final step, :final self, :final key, :final kind, :final ev) => [
              'fix',
              init,
              step,
              self,
              key,
              kind,
              ev,
            ],
            Gen(:final init, :final step, :final guard, :final pos) => [
              'gen',
              init,
              step,
              guard,
              pos,
            ],
            Read(:final port) => ['read', port],
            Push(:final port, :final value) => ['push', port, value],
          });
        case final Pattern p:
          then(switch (p) {
            WildP() => ['_'],
            BindP(:final name) => ['bind', name],
            LitP(:final value) => ['litp', value],
            AtomP(:final name, :final args) => ['atomp', name, args],
            FieldsP(:final name, :final fields) => ['fieldsp', name, fields],
            TupleP(:final items) => ['tuplep', items],
            AnyAtomP() => ['anyatom'],
            IsP(:final type) => ['is', type],
          });
        case Residue():
          then(['residue']);
        case Catalog(:final law):
          then(['catalog', law]);
        case Lattice(:final join):
          then(['lattice', join]);
        case Definedness():
          then(['definedness']);
        case final other:
          throw ArgumentError('not part of a term: ${other.runtimeType}');
      }
    }
  }
}
