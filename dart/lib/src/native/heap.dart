/// Value words and the counted heap (step L1.36).
///
/// **Words.** Native code passes every value as a [Word], a pair of 64-bit integers: a tag
/// and its payload. An integer in 64 bits, a float (its bits) and a boolean are unboxed, so
/// the arithmetic on them runs inline; a primitive as a function, a lookup port and a port's
/// state are unboxed too. Every other value is a cell of the heap, counted, or an entry of
/// the heap's table of uncounted values: a constant, the empty tuple and a bare atom, which
/// the memory plan of step L1.34 never counts either.
///
/// **Cells.** The heap mirrors the cells of step L1.34 one for one, so a native run makes the
/// same allocations and count writes as the counting machine: a non-empty tuple and an atom
/// with a payload are a cell whose parts are words, a closure a cell holding its captures, a
/// string a cell holding a [Rope], and a big integer, a rational, a keypath and a family a
/// cell holding the kernel value. A cell's count is the number of references to it; at 0 it
/// is freed, its parts dropped, and a later use of it is an error.
library;

import '../kernel/term.dart';
import '../kernel/text.dart' show compareUtf8;
import '../kernel/value.dart';
import '../zir/binary.dart' show nanBits;
import '../zir/graph.dart' show ZirError;
import 'rope.dart';

/// What a word's payload is.
abstract final class Tag {
  /// An integer in 64 bits; the payload is the integer.
  static const integer = 0;

  /// A float; the payload is its bits, a NaN always the one canonical NaN.
  static const float = 1;

  /// A boolean; the payload is 0 or 1.
  static const boolean = 2;

  /// A heap cell; the payload is its index.
  static const cell = 3;

  /// An uncounted value; the payload is its index in the heap's table.
  static const val = 4;

  /// A primitive as a function; the payload is its index in the program's table.
  static const prim = 5;

  /// A lookup port; the payload is its index in the program's table.
  static const source = 6;

  /// A port's state, which carries nothing.
  static const state = 7;

  /// An error: the run stops, and the runtime holds the error.
  static const err = 8;
}

/// A value as native code holds it: a tag and its payload.
final class Word {
  final int tag, bits;

  const Word(this.tag, this.bits);

  /// The integer [n].
  const Word.int(int n) : this(Tag.integer, n);

  /// A port's state.
  static const state = Word(Tag.state, 0);

  /// The error word.
  static const err = Word(Tag.err, 0);

  /// The word of a scalar value, when [v] is one.
  static Word? scalar(Value v) => switch (v) {
    Int(:final value) => Word.int(value),
    Float(:final x) => Word(Tag.float, x.isNaN ? nanBits : f64Bits(x)),
    Bool(:final value) => Word(Tag.boolean, value ? 1 : 0),
    _ => null,
  };

  @override
  bool operator ==(Object other) => other is Word && tag == other.tag && bits == other.bits;

  @override
  int get hashCode => Object.hash(tag, bits);

  @override
  String toString() => 'Word($tag, $bits)';
}

/// What a cell holds.
sealed class Obj {
  const Obj();

  /// The words the cell holds a reference to.
  List<Word> get parts => const [];
}

/// A string.
final class StrObj extends Obj {
  final Rope rope;

  const StrObj(this.rope);
}

/// A non-empty tuple.
final class TupleObj extends Obj {
  final List<Word> items;

  const TupleObj(this.items);

  @override
  List<Word> get parts => items;
}

/// An atom with a payload, its parts in the order of [Atom.args]; [fields] are the sorted
/// field names of a struct payload, empty for a tuple payload.
final class AtomObj extends Obj {
  final String name;
  final List<String> fields;
  final List<Word> args;

  const AtomObj(this.name, this.fields, this.args);

  @override
  List<Word> get parts => args;
}

/// A big integer, a rational, a keypath or a family, as the kernel holds it.
final class DataObj extends Obj {
  final Value value;

  const DataObj(this.value);
}

/// A closure: the index of its lambda in the program's table, and its captures in the
/// lambda node's input order.
final class CloObj extends Obj {
  final int lambda;
  final List<Word> caps;

  const CloObj(this.lambda, this.caps);

  @override
  List<Word> get parts => caps;
}

/// A heap cell: its count, its contents until it is freed, and whether it was ever shared.
final class _Cell {
  var count = 1;
  Obj? obj;
  var shared = false;

  _Cell(this.obj);
}

/// The counts of one run, the same measures as the counting machine of step L1.34 keeps,
/// and the bytes ropes copied.
final class Stats {
  /// Count increments.
  var increments = 0;

  /// Count decrements.
  var decrements = 0;

  /// Cells allocated.
  var allocations = 0;

  /// Cells freed.
  var frees = 0;

  /// The most cells live at once.
  var peak = 0;

  /// The cells whose count ever exceeded 1.
  var shared = 0;

  /// The bytes copied flattening ropes.
  var copied = 0;
}

/// The heap of one run.
final class Heap {
  final _cells = <_Cell>[];
  final _vals = <Value>[];

  /// The counts so far.
  final stats = Stats();

  /// The cells live now.
  var live = 0;

  /// The word of [v], uncounted: a scalar, or an entry of the table.
  Word uncounted(Value v) {
    if (Word.scalar(v) case final w?) return w;
    _vals.add(v);
    return Word(Tag.val, _vals.length - 1);
  }

  /// The uncounted value of word [w], tagged [Tag.val].
  Value valueAt(Word w) => _vals[w.bits];

  /// A new cell holding [obj], with count 1.
  Word alloc(Obj obj) {
    _cells.add(_Cell(obj));
    stats.allocations++;
    live++;
    if (live > stats.peak) stats.peak = live;
    return Word(Tag.cell, _cells.length - 1);
  }

  /// A fresh word for [v], owned: its cells allocated, each part of a tuple or an atom its
  /// own, as the counting machine allocates a value the kernel returns.
  Word fresh(Value v) {
    if (Word.scalar(v) case final w?) return w;
    return switch (v) {
      Tuple(:final items) when items.isEmpty => uncounted(v),
      Atom(:final args) when args.isEmpty => uncounted(v),
      Tuple(:final items) => alloc(TupleObj([for (final x in items) fresh(x)])),
      Atom(:final name, :final fields, :final args) => alloc(
        AtomObj(name, fields, [for (final x in args) fresh(x)]),
      ),
      Str(:final text) => alloc(StrObj(Rope.leaf(text.text))),
      _ => alloc(DataObj(v)),
    };
  }

  /// What live cell [w] holds; null for a word that is not a cell.
  Obj? obj(Word w) {
    if (w.tag != Tag.cell) return null;
    return _cells[w.bits].obj ??
        (throw ZirError('runtime: cell ${w.bits} is used after it was freed'));
  }

  /// Whether [w] is a function: a closure, a primitive or a lookup port.
  bool isFunction(Word w) => switch (w.tag) {
    Tag.prim || Tag.source => true,
    Tag.cell => obj(w) is CloObj,
    _ => false,
  };

  /// The kernel value of data word [w]; a string's rope is flattened.
  Value value(Word w) => switch (w.tag) {
    Tag.integer => Int(w.bits),
    Tag.float => Float(f64FromBits(w.bits)),
    Tag.boolean => Bool(w.bits != 0),
    Tag.val => _vals[w.bits],
    Tag.cell => switch (obj(w)!) {
      StrObj(:final rope) => Str(rope.flat((n) => stats.copied += n)),
      TupleObj(:final items) => Tuple([for (final x in items) value(x)]),
      AtomObj(:final name, :final fields, :final args) => Atom.raw(name, fields, [
        for (final x in args) value(x),
      ]),
      DataObj(:final value) => value,
      CloObj() => throw const ZirError('runtime: a closure is not data'),
    },
    final t => throw ZirError('runtime: a word tagged $t is not data'),
  };

  /// Adds a reference to [w], when it is a cell.
  void inc(Word w) {
    if (w.tag != Tag.cell) return;
    stats.increments++;
    final c = _cells[w.bits];
    c.count++;
    if (c.count == 2 && !c.shared) {
      c.shared = true;
      stats.shared++;
    }
  }

  /// Drops a reference to [w], when it is a cell, freeing it and dropping its parts at 0.
  void dec(Word w) {
    final todo = [w];
    while (todo.isNotEmpty) {
      final w = todo.removeLast();
      if (w.tag != Tag.cell) continue;
      stats.decrements++;
      final c = _cells[w.bits];
      if (c.count == 0) throw ZirError('runtime: cell ${w.bits} is dropped after it was freed');
      c.count--;
      if (c.count == 0) {
        final parts = c.obj!.parts;
        c.obj = null;
        stats.frees++;
        live--;
        // In reverse, so the parts are dropped first to last.
        todo.addAll(parts.reversed);
      }
    }
  }

  /// The fused release of step L1.34 of scrutinee [w], keeping the parts at the paths
  /// [kept]: a cell with count 1 is freed without a count write, the kept parts' references
  /// moving out of it and the others dropped; a shared cell gives each kept part a
  /// reference and loses one.
  void release(Word w, List<List<int>> kept) => _release(w, kept, 0);

  /// [release], each path in [kept] read from its step [d] on.
  void _release(Word w, List<List<int>> kept, int d) {
    if (w.tag != Tag.cell || kept.any((p) => p.length == d)) return;
    final o = obj(w)!;
    final c = _cells[w.bits];
    if (c.count == 1) {
      c.count = 0;
      c.obj = null;
      stats.frees++;
      live--;
      final byPart = <int, List<List<int>>>{};
      for (final p in kept) {
        (byPart[p[d]] ??= []).add(p);
      }
      final parts = o.parts;
      for (var i = 0; i < parts.length; i++) {
        if (byPart[i] case final sub?) {
          _release(parts[i], sub, d + 1);
        } else {
          dec(parts[i]);
        }
      }
    } else {
      for (final p in kept) {
        inc(_at(w, p, d));
      }
      dec(w);
    }
  }

  /// The part of [w] at [path], from its step [d] on.
  Word _at(Word w, List<int> path, int d) {
    for (var x = d; x < path.length; x++) {
      final o = obj(w) ?? (throw ZirError('runtime: a word tagged ${w.tag} has no parts'));
      w = o.parts[path[x]];
    }
    return w;
  }

  /// Part [i] of closure [w], borrowed: a capture.
  Word capture(Word w, int i) => switch (obj(w)) {
    CloObj(:final caps) => caps[i],
    _ => throw ZirError('runtime: a word tagged ${w.tag} is not a closure'),
  };

  /// The structure of data word [w], for matching: a tuple's items, or an atom's name,
  /// fields and payload; null for anything else.
  (String?, List<String>, List<Word>)? _parts(Word w) => switch (w.tag) {
    Tag.cell => switch (obj(w)) {
      TupleObj(:final items) => (null, const [], items),
      AtomObj(:final name, :final fields, :final args) => (name, fields, args),
      _ => null,
    },
    Tag.val => switch (_vals[w.bits]) {
      Tuple(:final items) => (null, const [], [for (final x in items) uncounted(x)]),
      Atom(:final name, :final fields, :final args) => (
        name,
        fields,
        [for (final x in args) uncounted(x)],
      ),
      _ => null,
    },
    _ => null,
  };

  /// Whether [w] matches [p], as the kernel matches a value: on success, [out] holds each
  /// binder's word and its path of part indices inside [w], in preorder; [at] is the path to
  /// [w]. A function matches only `_`, a name, and `is T` for a type `T` of functions.
  bool matches(Pattern p, Word w, List<int> at, List<(Word, List<int>)> out) {
    if (isFunction(w)) {
      return switch (p) {
        WildP() => true,
        BindP() => () {
          out.add((w, [...at]));
          return true;
        }(),
        IsP(:final type) => type.functions,
        _ => false,
      };
    }
    bool sub(int i, Pattern q, Word x) {
      at.add(i);
      final m = matches(q, x, at, out);
      at.removeLast();
      return m;
    }

    bool all(List<Pattern> ps, List<Word> xs) {
      for (var i = 0; i < ps.length; i++) {
        if (!sub(i, ps[i], xs[i])) return false;
      }
      return true;
    }

    switch (p) {
      case WildP():
        return true;
      case BindP():
        out.add((w, [...at]));
        return true;
      case LitP(value: final l):
        return value(w) == l;
      case AnyAtomP():
        return _parts(w)?.$1 != null;
      case IsP(:final type):
        return type.contains(value(w));
      case AtomP(:final name, args: final ps):
        return switch (_parts(w)) {
          (final n?, final fields, final args)
              when n == name && fields.isEmpty && ps.length == args.length =>
            all(ps, args),
          _ => false,
        };
      case FieldsP(:final name, fields: final fs):
        final (n, fields, args) = _parts(w) ?? (null, const <String>[], const <Word>[]);
        if (n != name || fields.isEmpty) return false;
        for (final (f, q) in fs) {
          final i = fieldIndex(fields, f);
          if (i == null || !sub(i, q, args[i])) return false;
        }
        return true;
      case TupleP(:final items):
        return switch (_parts(w)) {
          (null, _, final xs) when xs.length == items.length => all(items, xs),
          _ => false,
        };
    }
  }
}

/// The index of field [f] in the sorted [fields], found by binary search.
int? fieldIndex(List<String> fields, String f) {
  var (lo, hi) = (0, fields.length);
  while (lo < hi) {
    final mid = (lo + hi) >> 1;
    final c = compareUtf8(fields[mid], f);
    if (c == 0) return mid;
    if (c < 0) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return null;
}
