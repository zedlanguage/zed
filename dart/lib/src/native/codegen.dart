/// The code generator (step L1.36): x86-64 machine code for one planned graph, shared by
/// the JIT and the object writer.
///
/// Every value is a word, two 64-bit integers, kept in a 16-byte slot of its function's
/// frame and loaded just before each use, so code size and generation time are linear in
/// the graph. The root region is the function `zed_root`, with no parameters, returning its
/// result's word in `rax:rdx`. Each lambda body is a function `zed_body_<i>` taking, in
/// `rdi`, the address of the closure's word followed by the parameters' words, held as the
/// body's plan holds them, and reading its captures from the closure; `zed_entry_<i>` takes
/// every parameter owned and drops the ones the body borrows, for calls whose callee is
/// known only when they run. The arms of `if` and `match` are emitted inline. Each node's
/// dups and drops are calls of `rt_inc` and `rt_dec`. Integer, float and boolean arithmetic
/// and comparisons run inline when the tags say the operands are scalars; overflow and every
/// other case call the runtime, which runs the node as the counting machine does. After each
/// call that returns a word, an error word leaves the function, returning the error word.
library;

import 'dart:typed_data';

import '../kernel/term.dart' show Prim;
import '../zir/binary.dart' show nanBits;
import '../zir/graph.dart';
import '../zir/memory.dart';
import 'heap.dart' show Tag, Word;
import 'tables.dart';
import 'x64.dart';

/// Every hook the code calls, in the order of their numbers.
enum Hook {
  arg,
  node,
  inc,
  dec,
  cap,
  callable,
  entry,
  register,
  branch,
  match,
  out,
  pending,
  error;

  /// Its symbol.
  String get symbol => 'rt_$name';
}

/// A function of the code: its name, where it starts, its length, and whether it is
/// exported.
typedef Symbol = ({String name, int offset, int size, bool global});

/// The machine code of one graph.
final class Code {
  final Uint8List bytes;

  /// Each hook address in [bytes].
  final List<HookUse> hooks;

  /// The functions, `zed_root` last.
  final List<Symbol> symbols;

  const Code(this.bytes, this.hooks, this.symbols);

  /// Where `zed_root` starts.
  int get root => symbols.last.offset;
}

/// Where a word is kept: a slot of the frame, or a constant.
sealed class _Loc {
  const _Loc();
}

final class _Slot extends _Loc {
  /// The slot's offset from `rbp`: the tag there, the payload 8 bytes on.
  final int disp;

  const _Slot(this.disp);
}

final class _Const extends _Loc {
  final Word word;

  const _Const(this.word);
}

const _state = _Const(Word.state);

/// The code of graph [g] under [plan], whose tables are [t].
Code generate(Tables t, Region g, Plan plan) => _Gen(t).run(g, plan);

final class _Gen {
  final Tables t;
  final a = Asm();
  final List<Label> bodies, entries;
  final _symbols = <Symbol>[];

  /// The frame offset of the last slot the current function took.
  var _next = 0;

  /// The current function's exit for an error word.
  var _err = Label();

  _Gen(this.t)
    : bodies = [for (final _ in t.lambdas) Label()],
      entries = [for (final _ in t.lambdas) Label()];

  Code run(Region g, Plan plan) {
    for (var i = 0; i < t.lambdas.length; i++) {
      _body(i);
      _entry(i);
    }
    _function('zed_root', Label(), true, () {
      for (var i = 0; i < t.lambdas.length; i++) {
        a
          ..movImm(Reg.rdi, i)
          ..leaLabel(Reg.rsi, entries[i])
          ..callHook(Hook.register.index);
      }
      return _region(g, plan.root, [for (final _ in g.args) _state])[0];
    });
    return Code(a.finish(), a.hooks, _symbols);
  }

  /// Emits a function named [name] at [start]; [body] emits its code and gives the word it
  /// returns.
  void _function(String name, Label start, bool global, _Loc Function() body) {
    a.bind(start);
    final frame = a.enter();
    _next = 0;
    _err = Label();
    final out = body();
    _tag(Reg.rax, out);
    _bits(Reg.rdx, out);
    a
      ..leave()
      ..bind(_err)
      ..movImm(Reg.rax, Tag.err)
      ..movImm(Reg.rdx, 0)
      ..leave()
      ..frame(frame, -_next);
    _symbols.add((name: name, offset: start.at!, size: a.here - start.at!, global: global));
  }

  void _body(int i) {
    final l = t.lambdas[i];
    final node = t.nodes[l.node].node;
    final region = node.regions[0];
    // A body that uses ports takes their states after its parameters, as state words like
    // any other, and returns them after its value; the states order nothing here, since the
    // code runs the effects in the order of the nodes.
    final states = region.args.take(l.params).where((e) => e.isState).length;
    if (region.results.length != 1 + states) {
      throw ZirError(
        'native: lambda body `${l.body.path}` has ${region.results.length} results; a body '
        'returns one value and the states of the ${states == 1 ? '1 port' : '$states ports'} '
        'it takes',
      );
    }
    _function('zed_body_$i', bodies[i], false, () {
      // The words go to the frame before any call takes `rdi`.
      final ws = [for (var j = 0; j <= l.params; j++) _copy(Reg.rdi, 16 * j)];
      final args = ws.sublist(1);
      for (var c = 0; c < node.inputs.length; c++) {
        _hookArgs([ws[0]]);
        a
          ..movImm(Reg.rdx, c)
          ..callHook(Hook.cap.index);
        args.add(_put());
      }
      return _region(region, l.body, args)[0];
    });
  }

  void _entry(int i) {
    final l = t.lambdas[i];
    _function('zed_entry_$i', entries[i], false, () {
      final at = _slot();
      a
        ..store(Reg.rbp, at, Reg.rdi)
        ..call(bodies[i]);
      final out = _slot();
      _storeOut(out);
      final modes = l.modes;
      for (var j = 0; j < modes.length; j++) {
        if (modes[j] == Mode.borrowed) {
          a
            ..load(Reg.rax, Reg.rbp, at)
            ..load(Reg.rdi, Reg.rax, 16 * (j + 1))
            ..load(Reg.rsi, Reg.rax, 16 * (j + 1) + 8)
            ..callHook(Hook.dec.index);
        }
      }
      return _Slot(out);
    });
  }

  /// A new slot.
  int _slot() => _next -= 16;

  /// [n] new slots in a row, the first at the lowest address; returns its offset.
  int _block(int n) => _next -= 16 * n;

  /// Loads the tag of [l] into [r].
  void _tag(Reg r, _Loc l) => switch (l) {
    _Slot(:final disp) => a.load(r, Reg.rbp, disp),
    _Const(:final word) => a.movImm(r, word.tag),
  };

  /// Loads the payload of [l] into [r].
  void _bits(Reg r, _Loc l) => switch (l) {
    _Slot(:final disp) => a.load(r, Reg.rbp, disp + 8),
    _Const(:final word) => a.movImm(r, word.bits),
  };

  /// Stores the word `rax:rdx` in slot [at].
  void _storeOut(int at) {
    a
      ..store(Reg.rbp, at, Reg.rax)
      ..store(Reg.rbp, at + 8, Reg.rdx);
  }

  /// The word `rax:rdx` in a new slot.
  _Slot _put() {
    final at = _slot();
    _storeOut(at);
    return _Slot(at);
  }

  /// The word at `[base + disp]` in a new slot.
  _Slot _copy(Reg base, int disp) {
    final at = _slot();
    a
      ..load(Reg.rax, base, disp)
      ..store(Reg.rbp, at, Reg.rax)
      ..load(Reg.rax, base, disp + 8)
      ..store(Reg.rbp, at + 8, Reg.rax);
    return _Slot(at);
  }

  /// Stores the word at [l] in slot [at].
  void _move(_Loc l, int at) {
    _tag(Reg.rax, l);
    a.store(Reg.rbp, at, Reg.rax);
    _bits(Reg.rax, l);
    a.store(Reg.rbp, at + 8, Reg.rax);
  }

  /// The words at [ins] in a row; returns the first one's offset.
  int _row(List<_Loc> ins) {
    final at = _block(ins.length);
    for (var j = 0; j < ins.length; j++) {
      _move(ins[j], at + 16 * j);
    }
    return at;
  }

  /// Puts the words at [ws] in the argument registers of a hook.
  void _hookArgs(List<_Loc> ws) {
    const regs = [Reg.rdi, Reg.rsi, Reg.rdx, Reg.rcx];
    for (var j = 0; j < ws.length; j++) {
      _tag(regs[2 * j], ws[j]);
      _bits(regs[2 * j + 1], ws[j]);
    }
  }

  /// Leaves the function when `rax:rdx` is the error word.
  void _checked() {
    a
      ..cmpImm(Reg.rax, Tag.err)
      ..jcc(Cond.e, _err);
  }

  void _inc(_Loc l) {
    _hookArgs([l]);
    a.callHook(Hook.inc.index);
  }

  void _dec(_Loc l) {
    _hookArgs([l]);
    a.callHook(Hook.dec.index);
  }

  _Loc _src(Src s, List<_Loc> args, List<List<_Loc>> outs) => switch (s) {
    Arg(:final i) => args[i],
    Out(:final node, :final port) => outs[node][port],
    Const(:final value) => _Const(t.constant(value)),
  };

  List<_Loc> _region(Region r, RegionPlan rp, List<_Loc> args) {
    final ids = t.ids[rp]!;
    for (final i in rp.entryDrops) {
      _dec(args[i]);
    }
    final outs = <List<_Loc>>[];
    for (var k = 0; k < r.nodes.length; k++) {
      final np = rp.nodes[k];
      final ins = [for (final s in r.nodes[k].inputs) _src(s, args, outs)];
      for (final j in np.dups) {
        _inc(ins[j]);
      }
      outs.add(_node(ids[k], ins));
      for (final s in np.drops) {
        _dec(_src(s, args, outs));
      }
    }
    for (final i in rp.resultDups) {
      _inc(_src(r.results[i], args, outs));
    }
    return [for (final s in r.results) _src(s, args, outs)];
  }

  /// [first] and the outputs after it, which are states.
  List<_Loc> _states(_Loc first, int n) => [first, for (var i = 1; i < n; i++) _state];

  List<_Loc> _node(int id, List<_Loc> ins) {
    final node = t.nodes[id].node;
    final n = node.outputs.length;
    return switch (node.op) {
      PrimOp(:final prim) when ins.isEmpty && prim.arity != null => _states(
        _Const(Word(Tag.prim, t.prims.indexOf(prim))),
        n,
      ),
      PrimOp(:final prim) when _inline(prim, ins.length) => _states(_inlined(prim, id, ins), n),
      ApplyOp() => _states(_apply(id, ins), n),
      IfOp() => _branch(id, ins),
      MatchOp(:final patterns) => _matched(id, [for (final p in patterns) binds(p)], ins),
      _ => _states(_slow(id, ins), n),
    };
  }

  /// Node [id] run by the runtime on [ins], its word in a new slot.
  _Slot _slow(int id, List<_Loc> ins) {
    _runtime(id, ins);
    return _put();
  }

  /// Node [id] run by the runtime on [ins], its word in `rax:rdx`, checked.
  void _runtime(int id, List<_Loc> ins) {
    _push(ins);
    a
      ..movImm(Reg.rdi, id)
      ..callHook(Hook.node.index);
    _checked();
  }

  /// Pushes each word at [ins] to the runtime's inputs.
  void _push(List<_Loc> ins) {
    for (final l in ins) {
      _hookArgs([l]);
      a.callHook(Hook.arg.index);
    }
  }

  /// Stores tag [tag] and the payload in `rax` in slot [at], then jumps to [done].
  void _result(int at, int tag, Label done) {
    a
      ..storeImm(Reg.rbp, at, tag)
      ..store(Reg.rbp, at + 8, Reg.rax)
      ..jmp(done);
  }

  /// Replaces a NaN in `rax` by the canonical NaN, as the kernel does.
  void _canonical() {
    final ok = Label();
    a
      ..toXmm(0, Reg.rax)
      ..ucomisd(0, 0)
      ..jcc(Cond.np, ok)
      ..movImm(Reg.rax, nanBits)
      ..bind(ok);
  }

  /// Jumps to [no] unless the tags of [x] and [y] are both [tag].
  void _both(_Loc x, _Loc y, int tag, Label no) {
    _tag(Reg.rax, x);
    a
      ..cmpImm(Reg.rax, tag)
      ..jcc(Cond.ne, no);
    _tag(Reg.rax, y);
    a
      ..cmpImm(Reg.rax, tag)
      ..jcc(Cond.ne, no);
    _bits(Reg.rax, x);
    _bits(Reg.rcx, y);
  }

  /// Primitive [p] on scalar words inline, the runtime running every other case.
  _Slot _inlined(Prim p, int id, List<_Loc> ins) {
    final out = _slot();
    final done = Label(), slow = Label();
    final x = ins[0];
    if (ins.length == 1) {
      final next = Label();
      _tag(Reg.rax, x);
      if (p == Prim.neg) {
        a
          ..cmpImm(Reg.rax, Tag.integer)
          ..jcc(Cond.ne, next);
        _bits(Reg.rax, x);
        a
          ..neg(Reg.rax)
          ..jcc(Cond.o, slow);
        _result(out, Tag.integer, done);
        a.bind(next);
        _tag(Reg.rax, x);
        a
          ..cmpImm(Reg.rax, Tag.float)
          ..jcc(Cond.ne, slow);
        _bits(Reg.rax, x);
        a
          ..movImm(Reg.rcx, 1 << 63)
          ..xor(Reg.rax, Reg.rcx);
        _canonical();
        _result(out, Tag.float, done);
      } else {
        a
          ..cmpImm(Reg.rax, Tag.boolean)
          ..jcc(Cond.ne, slow);
        _bits(Reg.rax, x);
        a.xorImm8(Reg.rax, 1);
        _result(out, Tag.boolean, done);
        a.bind(next);
      }
    } else {
      final y = ins[1];
      final intOp = _intOps.contains(p), intCmp = _intCmp[p];
      if (intOp || intCmp != null) {
        final next = Label();
        _both(x, y, Tag.integer, next);
        if (intCmp != null) {
          a
            ..cmp(Reg.rax, Reg.rcx)
            ..setAl(intCmp);
          _result(out, Tag.boolean, done);
        } else {
          switch (p) {
            case Prim.add:
              a.add(Reg.rax, Reg.rcx);
            case Prim.sub:
              a.sub(Reg.rax, Reg.rcx);
            default:
              a.imul(Reg.rax, Reg.rcx);
          }
          a.jcc(Cond.o, slow);
          _result(out, Tag.integer, done);
        }
        a.bind(next);
      }
      final floatOp = _floatOps[p], floatCmp = _floatCmp[p];
      if (floatOp != null || floatCmp != null) {
        final next = Label();
        _both(x, y, Tag.float, next);
        a
          ..toXmm(0, Reg.rax)
          ..toXmm(1, Reg.rcx);
        if (floatCmp case (final swap, final c)) {
          a
            ..ucomisd(swap ? 1 : 0, swap ? 0 : 1)
            ..setAl(c);
          _result(out, Tag.boolean, done);
        } else {
          a
            ..sd(floatOp!, 0, 1)
            ..fromXmm(Reg.rax, 0);
          _canonical();
          _result(out, Tag.float, done);
        }
        a.bind(next);
      }
      if (p == Prim.and || p == Prim.or) {
        final next = Label();
        _both(x, y, Tag.boolean, next);
        p == Prim.and ? a.and(Reg.rax, Reg.rcx) : a.or(Reg.rax, Reg.rcx);
        _result(out, Tag.boolean, done);
        a.bind(next);
      }
    }
    a.bind(slow);
    _runtime(id, ins);
    _storeOut(out);
    a.bind(done);
    return _Slot(out);
  }

  /// A call: directly when the plan resolves the callee and the closure is it, through the
  /// closure's entry when its arity fits, else by the runtime.
  _Slot _apply(int id, List<_Loc> ins) {
    final ni = t.nodes[id];
    final out = _slot(), lam = _slot();
    final generic = Label(), kernel = Label(), done = Label();
    _hookArgs([ins[0]]);
    a
      ..movImm(Reg.rdx, ins.length - 1)
      ..callHook(Hook.callable.index)
      ..store(Reg.rbp, lam, Reg.rax);
    if (ni.callee case final li?) {
      a
        ..cmpImm(Reg.rax, li + 1)
        ..jcc(Cond.ne, generic);
      if (ni.error != null) {
        a
          ..movImm(Reg.rdi, id)
          ..callHook(Hook.error.index)
          ..jmp(_err);
      } else {
        final row = _row(ins);
        a
          ..lea(Reg.rdi, Reg.rbp, row)
          ..call(bodies[li]);
        _checked();
        _storeOut(out);
        final modes = t.lambdas[li].modes;
        for (var i = 0; i < modes.length; i++) {
          if (ni.modes[1 + i] == Mode.owned && modes[i] == Mode.borrowed) _dec(ins[1 + i]);
        }
        a.jmp(done);
      }
    }
    a
      ..bind(generic)
      ..load(Reg.rdi, Reg.rbp, lam)
      ..test(Reg.rdi)
      ..jcc(Cond.e, kernel)
      ..movImm(Reg.rcx, 1)
      ..sub(Reg.rdi, Reg.rcx)
      ..callHook(Hook.entry.index)
      ..mov(Reg.r11, Reg.rax);
    // The row is written with `rax` and `rcx` only, so `r11` keeps the entry.
    final row = _row(ins);
    a
      ..lea(Reg.rdi, Reg.rbp, row)
      ..callReg(Reg.r11);
    _checked();
    _storeOut(out);
    a
      ..jmp(done)
      ..bind(kernel);
    _runtime(id, ins);
    _storeOut(out);
    a.bind(done);
    return _Slot(out);
  }

  /// Emits arm [i] of node [id] inline on [args], its results stored in the slots from
  /// [outs] on, then jumps to [done].
  void _arm(int id, int i, List<_Loc> args, int outs, Label done) {
    final ni = t.nodes[id];
    final res = _region(ni.node.regions[i], ni.plan.regions[i], args);
    for (var j = 0; j < res.length; j++) {
      _move(res[j], outs + 16 * j);
    }
    a.jmp(done);
  }

  /// The runtime's failure word as the node's result, the other outputs states.
  void _fail(int n, int outs, Label done) {
    a.callHook(Hook.pending.index);
    _checked();
    _storeOut(outs);
    for (var j = 1; j < n; j++) {
      _move(_state, outs + 16 * j);
    }
    a.jmp(done);
  }

  /// Dispatches on the code in `rax`: `labels[i]` for `i`, else the error exit.
  void _dispatch(List<Label> labels) {
    for (var i = 0; i < labels.length; i++) {
      a
        ..cmpImm(Reg.rax, i)
        ..jcc(Cond.e, labels[i]);
    }
    a.jmp(_err);
  }

  List<_Loc> _outs(int outs, int n) => [for (var j = 0; j < n; j++) _Slot(outs + 16 * j)];

  List<_Loc> _branch(int id, List<_Loc> ins) {
    final n = t.nodes[id].node.outputs.length;
    final outs = _block(n);
    final arms = [Label(), Label()];
    final fail = Label(), slow = Label(), done = Label();
    final c = ins[0];
    _tag(Reg.rax, c);
    a
      ..cmpImm(Reg.rax, Tag.boolean)
      ..jcc(Cond.ne, slow);
    _bits(Reg.rax, c);
    a
      ..test(Reg.rax)
      ..jcc(Cond.ne, arms[0])
      ..jmp(arms[1])
      ..bind(slow);
    _push(ins);
    a
      ..movImm(Reg.rdi, id)
      ..callHook(Hook.branch.index);
    _dispatch([...arms, fail]);
    for (var i = 0; i < 2; i++) {
      a.bind(arms[i]);
      _arm(id, i, ins.sublist(1), outs, done);
    }
    a.bind(fail);
    _fail(n, outs, done);
    a.bind(done);
    return _outs(outs, n);
  }

  List<_Loc> _matched(int id, List<int> binders, List<_Loc> ins) {
    final n = t.nodes[id].node.outputs.length;
    final outs = _block(n);
    final done = Label(), fail = Label();
    final arms = [for (final _ in binders) Label()];
    _push(ins);
    a
      ..movImm(Reg.rdi, id)
      ..callHook(Hook.match.index);
    _dispatch([...arms, fail]);
    for (var i = 0; i < binders.length; i++) {
      a.bind(arms[i]);
      final args = <_Loc>[];
      for (var b = 0; b < binders[i]; b++) {
        a
          ..movImm(Reg.rdi, b)
          ..callHook(Hook.out.index);
        args.add(_put());
      }
      _arm(id, i, [...args, ...ins.skip(1)], outs, done);
    }
    a.bind(fail);
    _fail(n, outs, done);
    a.bind(done);
    return _outs(outs, n);
  }
}

/// Whether primitive [p] on [n] inputs has an inline path.
bool _inline(Prim p, int n) => switch (n) {
  1 => p == Prim.neg || p == Prim.not,
  2 =>
    _intOps.contains(p) ||
        _intCmp.containsKey(p) ||
        _floatOps.containsKey(p) ||
        p == Prim.and ||
        p == Prim.or,
  _ => false,
};

const _intOps = {Prim.add, Prim.sub, Prim.mul};

const _intCmp = {
  Prim.lt: Cond.l,
  Prim.le: Cond.le,
  Prim.gt: Cond.g,
  Prim.ge: Cond.ge,
  Prim.eq: Cond.e,
  Prim.ne: Cond.ne,
};

/// The float operations, by their opcode.
const _floatOps = {Prim.add: 0x58, Prim.sub: 0x5c, Prim.mul: 0x59, Prim.div: 0x5e};

/// The float comparisons, ordered, so a NaN compares false as the kernel's do: whether the
/// operands are swapped for `ucomisd`, and the condition. `==` and `!=` on floats are the
/// kernel's surface equality and are not inline.
const _floatCmp = {
  Prim.lt: (true, Cond.a),
  Prim.le: (true, Cond.ae),
  Prim.gt: (false, Cond.a),
  Prim.ge: (false, Cond.ae),
};
