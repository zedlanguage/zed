/// The ways a kernel evaluation stops without a value.
///
/// Failure atoms such as `#empty` are values, not errors (sec:failure). These errors are the
/// cases the checker rejects statically, which the reference evaluator detects when it meets
/// them, plus the divergence that fuel bounds.
library;

import 'value.dart';

/// Why a kernel evaluation stopped without a value.
sealed class KernelError implements Exception {
  const KernelError();

  /// What tells two errors of one kind apart.
  List<Object> get _fields => const [];

  @override
  bool operator ==(Object other) {
    if (other is! KernelError || other.runtimeType != runtimeType) return false;
    final a = _fields, b = other._fields;
    if (a.length != b.length) return false;
    for (var i = 0; i < a.length; i++) {
      if (a[i] != b[i]) return false;
    }
    return true;
  }

  @override
  int get hashCode => Object.hash(runtimeType, Object.hashAll(_fields));
}

/// Two entries were written to one keypath, or one entry's keypath is a prefix of another's:
/// the collision rule (sec:grouping), the premise of T-Reindex.
final class CollisionError extends KernelError {
  /// The keypath written twice.
  final Keypath keypath;

  const CollisionError(this.keypath);

  @override
  List<Object> get _fields => keypath;

  @override
  String toString() => 'collision: two writers for keypath [${keypath.join(', ')}]';
}

/// A leaf with no keys, which only a key map that returns an empty keypath can make.
final class EmptyKeypathError extends KernelError {
  const EmptyKeypathError();

  @override
  String toString() => 'a key map returned an empty keypath';
}

/// A fold met a family with a leaf at another depth than the fold's, so it has no one level
/// to collapse.
final class MixedDepthError extends KernelError {
  const MixedDepthError();

  @override
  String toString() => 'fold over leaves at another depth than its own';
}

/// A value had the wrong shape for the construct reading it, which a well-typed term never
/// does.
final class KernelTypeError extends KernelError {
  final String message;

  const KernelTypeError(this.message);

  @override
  List<Object> get _fields => [message];

  @override
  String toString() => 'type error: $message';
}

/// The term named a port the world does not have.
final class UnknownPortError extends KernelError {
  final String port;

  const UnknownPortError(this.port);

  @override
  List<Object> get _fields => [port];

  @override
  String toString() => 'unknown port `$port`';
}

/// A lookup port could not answer a read: the port and why.
final class PortError extends KernelError {
  final String port, why;

  const PortError(this.port, this.why);

  @override
  List<Object> get _fields => [port, why];

  @override
  String toString() => 'port `$port`: $why';
}

/// The evaluation used up its fuel: a `fix` whose ascent or a `gen` that did not stop within
/// the step budget (sec:generations, divergence).
final class OutOfFuelError extends KernelError {
  const OutOfFuelError();

  @override
  String toString() => 'out of fuel';
}

/// Calls nested deeper than the reference evaluator follows (`maxDepth`).
final class TooDeepError extends KernelError {
  const TooDeepError();

  @override
  String toString() => 'calls nested too deeply';
}

/// A number beyond the size the reference evaluator builds ([maxBits]): a limit of its memory,
/// since `int` and `rat` are unbounded.
final class OverflowError extends KernelError {
  const OverflowError();

  @override
  String toString() => "a number beyond the evaluator's size limit";
}

/// A definedness `fix` stopped with these entries undefined: each reads an entry of the
/// cycle, which is divergence (T-Fix), never `#notFound`.
final class StalledError extends KernelError {
  /// The undefined keys, in order.
  final List<Value> keys;

  const StalledError(this.keys);

  @override
  List<Object> get _fields => keys;

  @override
  String toString() => 'recursion stalled: entries ${keys.join(', ')} depend on each other';
}
