/// The JIT (step L1.36): the generated code is copied to memory the process maps executable
/// and called through the foreign function interface; each hook it calls is a Dart function
/// made callable from native code, which runs on the current [State].
library;

import 'dart:ffi';
import 'dart:typed_data';

import '../kernel/eval.dart';
import '../kernel/value.dart';
import '../zir/graph.dart';
import '../zir/memory.dart' show Plan;
import 'codegen.dart';
import 'heap.dart';
import 'hooks.dart';
import 'tables.dart';

/// What one native run gives.
final class Outcome {
  /// The program's value.
  final Value value;

  /// The heap's counts.
  final Stats stats;

  /// How many nodes the kernel ran for the runtime.
  final int kernelCalls;

  const Outcome(this.value, this.stats, this.kernelCalls);
}

/// Compiles graph [g] under [plan] and runs it, the kernel in [ev] running the nodes the
/// runtime does not. Only on x86-64 Linux.
Outcome run(Region g, Plan plan, Evaluator ev) {
  if (Abi.current() != Abi.linuxX64) {
    throw ZirError('native: code is generated for x86-64 Linux, not ${Abi.current()}');
  }
  final t = Tables(g, plan);
  final code = generate(t, g, plan);
  final s = State(t, ev);
  final size = (code.bytes.length + 4095) & ~4095;
  final p = _mmap(nullptr, size, 3, 0x22, -1, 0);
  if (p.address == -1) throw const ZirError('native: the code could not be mapped');
  final previous = _current;
  try {
    final mem = p.cast<Uint8>().asTypedList(size)..setAll(0, code.bytes);
    final addresses = _addresses();
    final view = mem.buffer.asByteData(mem.offsetInBytes, size);
    for (final (:offset, :hook) in code.hooks) {
      view.setInt64(offset, addresses[hook], Endian.little);
    }
    if (_mprotect(p, size, 5) != 0) throw const ZirError('native: the code could not be mapped');
    final root = Pointer<NativeFunction<_Pair Function()>>.fromAddress(p.address + code.root)
        .asFunction<_Pair Function()>();
    _current = s;
    final w = root();
    _current = previous;
    return Outcome(s.finish(Word(w.tag, w.bits)), s.heap.stats, s.kernelCalls);
  } finally {
    _current = previous;
    _munmap(p, size);
  }
}

/// The run in progress.
State? _current;

State get _s => _current!;

/// A word as native code returns it, in `rax:rdx`.
final class _Pair extends Struct {
  @Int64()
  external int tag;
  @Int64()
  external int bits;
}

_Pair _pair(Word w) => Struct.create<_Pair>()
  ..tag = w.tag
  ..bits = w.bits;

final _libc = DynamicLibrary.process();
final _mmap = _libc
    .lookupFunction<
      Pointer<Void> Function(Pointer<Void>, IntPtr, Int32, Int32, Int32, IntPtr),
      Pointer<Void> Function(Pointer<Void>, int, int, int, int, int)
    >('mmap');
final _mprotect = _libc
    .lookupFunction<
      Int32 Function(Pointer<Void>, IntPtr, Int32),
      int Function(Pointer<Void>, int, int)
    >('mprotect');
final _munmap = _libc
    .lookupFunction<Int32 Function(Pointer<Void>, IntPtr), int Function(Pointer<Void>, int)>(
      'munmap',
    );

typedef _W1 = _Pair Function(Int64);
typedef _V2 = Void Function(Int64, Int64);
typedef _I1 = Int64 Function(Int64);

/// The callable hooks, made once and kept: each catches every error, records it on the run,
/// and returns the error word or -1.
final List<NativeCallable<Function>> _hooks = [
  NativeCallable<_V2>.isolateLocal((int tag, int bits) {
    _s.guard(null, () => _s.args.add(Word(tag, bits)));
  }),
  NativeCallable<_W1>.isolateLocal((int id) => _pair(_s.guard(Word.err, () => _s.node(id)))),
  NativeCallable<_V2>.isolateLocal((int tag, int bits) {
    _s.guard(null, () => _s.heap.inc(Word(tag, bits)));
  }),
  NativeCallable<_V2>.isolateLocal((int tag, int bits) {
    _s.guard(null, () => _s.heap.dec(Word(tag, bits)));
  }),
  NativeCallable<_Pair Function(Int64, Int64, Int64)>.isolateLocal(
    (int tag, int bits, int i) =>
        _pair(_s.guard(Word.err, () => _s.heap.capture(Word(tag, bits), i))),
  ),
  NativeCallable<Int64 Function(Int64, Int64, Int64)>.isolateLocal(
    (int tag, int bits, int nargs) => _s.guard(0, () => _s.callable(Word(tag, bits), nargs)),
    exceptionalReturn: 0,
  ),
  NativeCallable<_I1>.isolateLocal((int lambda) => _s.entries[lambda], exceptionalReturn: 0),
  NativeCallable<_V2>.isolateLocal((int lambda, int address) {
    _s.entries[lambda] = address;
  }),
  NativeCallable<_I1>.isolateLocal(
    (int id) => _s.guard(-1, () => _s.branch(id)),
    exceptionalReturn: -1,
  ),
  NativeCallable<_I1>.isolateLocal(
    (int id) => _s.guard(-1, () => _s.matched(id)),
    exceptionalReturn: -1,
  ),
  NativeCallable<_W1>.isolateLocal((int k) => _pair(_s.outs[k])),
  NativeCallable<_Pair Function()>.isolateLocal(() => _pair(_s.pending)),
  NativeCallable<_W1>.isolateLocal((int id) => _pair(_s.guard(Word.err, () => _s.error(id)))),
];

/// Each hook's address, in the order of [Hook].
List<int> _addresses() => [for (final h in _hooks) h.nativeFunction.address];
