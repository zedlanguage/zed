/// The runtime the generated code calls: every node it does not run inline, every count
/// write, and the decisions of `if` and `match` it cannot make from a tag. Each hook does
/// what the counting machine of step L1.34 does for the same node, on words, so a native run
/// makes the machine's allocations and count writes one for one.
library;

import '../kernel/error.dart';
import '../kernel/eval.dart';
import '../kernel/term.dart';
import '../kernel/value.dart';
import '../zir/graph.dart';
import '../zir/lower.dart' show raiseWith;
import '../zir/memory.dart' show Mode;
import 'heap.dart';
import 'rope.dart';
import 'tables.dart';

/// The state of one native run.
final class State {
  final heap = Heap();
  final Evaluator ev;
  final Tables t;

  /// The inputs of the next node a hook runs, pushed one at a time.
  final args = <Word>[];

  /// The binders of the arm a `match` picked.
  var outs = <Word>[];

  /// The failure value of the last `if` or `match` that failed, owned.
  var pending = Word.err;

  /// The first error, which stops the run.
  Object? err;
  StackTrace? trace;

  /// Each lambda's entry address, once registered.
  final List<int> entries;

  /// The kernel runs so far.
  var kernelCalls = 0;

  State(this.t, this.ev) : entries = List.filled(t.lambdas.length, 0) {
    for (final v in t.consts) {
      heap.uncounted(v);
    }
  }

  /// Runs [f]; an error it throws is recorded, the first one kept, and [fallback] returned.
  T guard<T>(T fallback, T Function() f) {
    try {
      return f();
    } catch (e, st) {
      if (err == null) {
        err = e;
        trace = st;
      }
      return fallback;
    }
  }

  /// `rt_node`: runs node [id] on the pushed inputs as the counting machine does; returns its
  /// first output, owned.
  Word node(int id) {
    final ins = _take();
    final ni = t.nodes[id];
    final allData = ins.every(_data);
    switch (ni.node.op) {
      case PrimOp(prim: Prim.tuple) when allData && ins.isNotEmpty:
        return heap.alloc(TupleObj(ins));
      case PrimOp(prim: Prim.atom) when allData:
        final v = _kernel(ni, ins);
        if (v case Atom(:final name, :final fields, :final args)
            when args.isNotEmpty && args.length + 2 == ins.length) {
          final names = switch (heap.value(ins[1])) {
            Tuple(:final items) => items,
            _ => const <Value>[],
          };
          final at = {
            for (var i = 0; i < names.length; i++)
              if (names[i] case Str(:final text)) text.text: i,
          };
          return heap.alloc(
            AtomObj(name, fields, [
              for (var i = 0; i < args.length; i++) ins[2 + (names.isEmpty ? i : at[fields[i]]!)],
            ]),
          );
        }
        _consume(ni, ins);
        return heap.fresh(v);
      case PrimOp(prim: Prim.tupleGet):
        if ((heap.obj(ins[0]), ins[1])
            case (TupleObj(:final items), Word(tag: Tag.integer, :final bits))
            when bits >= 0 && bits < items.length) {
          final kid = items[bits];
          heap.inc(kid);
          return kid;
        }
        return heap.fresh(_kernel(ni, ins));
      case PrimOp(prim: Prim.concat) when ins.length == 2:
        if ((_rope(ins[0]), _rope(ins[1])) case (final a?, final b?)) {
          _consume(ni, ins);
          return heap.alloc(StrObj(Rope.cat(a, b)));
        }
        return _slow(ni, ins);
      case PrimOp(prim: Prim.len) when ins.length == 1:
        if (_rope(ins[0]) case final r?) {
          _consume(ni, ins);
          return Word.int(r.chars);
        }
        return _slow(ni, ins);
      case LambdaOp():
        return heap.alloc(CloObj(ni.lambda!, ins));
      case ReadOp(:final port):
        if (ev.world.inputs[port] case final v?) return heap.fresh(v);
        if (ev.world.sources.containsKey(port)) return Word(Tag.source, t.portAt[port]!);
        ev.run(Read(port));
        throw const ZirError('a read');
      default:
        return _slow(ni, ins);
    }
  }

  /// `rt_callable`: the number of lambda of closure [w] plus 1 when it takes [nargs]
  /// arguments; else 0.
  int callable(Word w, int nargs) => switch (heap.obj(w)) {
    CloObj(:final lambda) when t.lambdas[lambda].params == nargs => lambda + 1,
    _ => 0,
  };

  /// `rt_error`: the error node [id] raises when it runs.
  Never error(int id) =>
      throw t.nodes[id].error ?? const ZirError('native: an error with no message');

  /// `rt_branch`: an `if` whose condition is not a boolean word; the kernel decides. Returns
  /// the arm, or 2 for a failure.
  int branch(int id) {
    final ins = _take();
    if (ins[0].tag == Tag.boolean) return ins[0].bits == 0 ? 1 : 0;
    final c = _term(ins[0], _Lets());
    switch (_run(If(c, const Lit(Int(0)), const Lit(Int(1))))) {
      case Int(:final value):
        return value;
      case final v:
        _failed(t.nodes[id], ins, v);
        return 2;
    }
  }

  /// `rt_match`: the arm whose pattern the scrutinee matches first, its binders in [outs],
  /// the scrutinee released as the plan says; or the number of arms for a failure.
  int matched(int id) {
    final ins = _take();
    final ni = t.nodes[id];
    final ps = (ni.node.op as MatchOp).patterns;
    final scrut = ins[0];
    final function = heap.isFunction(scrut);
    int? found;
    var binders = <(Word, List<int>?)>[];
    if (!function) {
      for (var i = 0; i < ps.length; i++) {
        final out = <(Word, List<int>)>[];
        if (heap.matches(ps[i], scrut, [], out)) {
          (found, binders) = (i, out);
          break;
        }
      }
    }
    if (found == null) {
      final picked = _kernelMatch(ps, scrut);
      if (picked is! (int, List<Value>)) {
        _failed(ni, ins, picked as Value);
        return ps.length;
      }
      final (i, vals) = picked;
      if (!function) {
        throw ZirError(
          'native: ${ni.path}: no pattern matches natively, and the kernel picks arm $i',
        );
      }
      found = i;
      binders = [for (final v in vals) (heap.uncounted(v), null)];
    }
    final i = found;
    final arm = ni.arms[i];
    final words = <Word>[];
    if (ni.modes[0] == Mode.owned) {
      final kept = [
        for (var b = 0; b < binders.length; b++)
          if (arm[b] == Mode.owned) b,
      ];
      // A binder the arm borrows holds no reference once the scrutinee is released, so it is
      // detached first: the machine gives it no cell.
      for (var b = 0; b < binders.length; b++) {
        final w = binders[b].$1;
        words.add(arm[b] == Mode.owned || w.tag != Tag.cell ? w : heap.uncounted(heap.value(w)));
      }
      if (t.fuse) {
        heap.release(scrut, [for (final b in kept) ?binders[b].$2]);
      } else {
        for (final b in kept) {
          heap.inc(binders[b].$1);
        }
        heap.dec(scrut);
      }
    } else {
      for (var b = 0; b < binders.length; b++) {
        if (arm[b] == Mode.owned) {
          throw ZirError(
            'memory: ${ni.path}: the scrutinee is borrowed, and arm $i owns binder $b',
          );
        }
        words.add(binders[b].$1);
      }
    }
    outs = words;
    return i;
  }

  /// The program's result [w]: its value, after the result is dropped and no cell is left
  /// live. Throws the run's first error.
  Value finish(Word w) {
    if (err case final e?) Error.throwWithStackTrace(e, trace!);
    if (w.tag == Tag.err) throw const ZirError('native: the run failed and recorded no message');
    final v = heap.isFunction(w) ? null : heap.value(w);
    heap.dec(w);
    if (heap.live != 0) {
      final n = heap.live;
      throw ZirError('memory: $n cell${n == 1 ? '' : 's'} live after the result is dropped');
    }
    return v ?? (throw const KernelTypeError("the program's result is a function"));
  }

  List<Word> _take() {
    final ins = [...args];
    args.clear();
    return ins;
  }

  /// Whether [w] is data: not a function and not a port's state.
  bool _data(Word w) => w.tag != Tag.state && !heap.isFunction(w);

  /// The rope of string word [w], when it is one.
  Rope? _rope(Word w) => switch (w.tag) {
    Tag.cell => switch (heap.obj(w)) {
      StrObj(:final rope) => rope,
      _ => null,
    },
    Tag.val => switch (heap.valueAt(w)) {
      Str(:final text) => Rope.leaf(text.text),
      _ => null,
    },
    _ => null,
  };

  /// The kernel runs the node, the owned inputs are dropped, and the value is allocated.
  Word _slow(NodeInfo ni, List<Word> ins) {
    final v = _kernel(ni, ins);
    _consume(ni, ins);
    return heap.fresh(v);
  }

  /// Drops each input the node takes owned.
  void _consume(NodeInfo ni, List<Word> ins) {
    for (var j = 0; j < ins.length; j++) {
      if (ni.modes[j] == Mode.owned) heap.dec(ins[j]);
    }
  }

  /// The value the kernel gives node [ni] run alone on [ins].
  Value _kernel(NodeInfo ni, List<Word> ins) {
    final lets = _Lets();
    final terms = [for (final w in ins) _term(w, lets)];
    return _run(_wrap(lets, raiseWith(ni.alone, terms)));
  }

  Value _run(Term term) {
    kernelCalls++;
    return ev.run(term);
  }

  /// The kernel term for word [w]; a lookup port is read once, by a `let` in [lets].
  Term _term(Word w, _Lets lets) {
    switch (w.tag) {
      case Tag.prim:
        return PrimFn(t.prims[w.bits]);
      case Tag.state:
        return const Lit(Tuple([]));
      case Tag.source:
        final p = t.ports[w.bits];
        if (lets.seen.add(p)) lets.order.add(p);
        return Var(_portVar(p));
    }
    if (heap.obj(w) case CloObj(:final lambda, :final caps)) {
      return raiseWith(t.nodes[t.lambdas[lambda].node].alone, [
        for (final c in caps) _term(c, lets),
      ]);
    }
    return Lit(heap.value(w));
  }

  /// An `if` or `match` whose decision is failure value [v]: the owned inputs are dropped
  /// and the value is pending as the node's result.
  void _failed(NodeInfo ni, List<Word> ins, Value v) {
    _consume(ni, ins);
    pending = heap.fresh(v);
  }

  /// The kernel's decision on a scrutinee native matching does not decide: the arm and its
  /// binders' values, or the failure value.
  Object _kernelMatch(List<Pattern> ps, Word scrut) {
    final lets = _Lets();
    final s = _term(scrut, lets);
    final arms = <(Pattern, Term)>[];
    var n = 0;
    for (var i = 0; i < ps.length; i++) {
      final xs = <Term>[Lit(Int(i))];
      final p = _rename(ps[i], () {
        final x = '\u0000bind${++n}';
        xs.add(Var(x));
        return x;
      });
      arms.add((p, PrimApp(Prim.tuple, xs)));
    }
    final picked = _run(_wrap(lets, Match(s, arms)));
    if (picked case Tuple(items: [Int(value: final i), ...final rest])
        when i >= 0 && i < ps.length) {
      return (i, rest);
    }
    return picked;
  }
}

/// The lookup ports a kernel term reads, each once, in the order first met.
final class _Lets {
  final seen = <String>{};
  final order = <String>[];
}

String _portVar(String p) => '\u0000port $p';

/// [t] with each lookup port in [ports] read first.
Term _wrap(_Lets ports, Term t) {
  for (final p in ports.order.reversed) {
    t = Let(_portVar(p), Read(p), t);
  }
  return t;
}

/// [p] with each binder renamed, in preorder, to what [f] gives.
Pattern _rename(Pattern p, String Function() f) => switch (p) {
  BindP() => BindP(f()),
  AtomP(:final name, :final args) => AtomP(name, [for (final q in args) _rename(q, f)]),
  TupleP(:final items) => TupleP([for (final q in items) _rename(q, f)]),
  FieldsP(:final name, :final fields) => FieldsP(name, [
    for (final (x, q) in fields) (x, _rename(q, f)),
  ]),
  WildP() || LitP() || AnyAtomP() || IsP() => p,
};
