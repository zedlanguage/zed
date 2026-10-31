/// Checking an equation of kernel terms on finite models: run both sides on each instance and
/// compare what they compute (step M0.10).
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

/// What a closed term computes: a [Value], or the [KernelError] that stopped it.
Object outcome(Term t) {
  try {
    return eval(t);
  } on KernelError catch (e) {
    return e;
  }
}

/// Whether two outcomes agree: equal values, compared as the law catalog compares them
/// (bitwise on floats after NaN canonicalization), or errors of one kind. Errors are compared
/// by kind because a law whose two sides are both rejected, such as a reindex that collides
/// on either side (law 5), may report the collision at different keypaths.
bool agree(Object a, Object b) => switch ((a, b)) {
  (Value x, Value y) => x == y,
  (KernelError x, KernelError y) => x.runtimeType == y.runtimeType,
  _ => false,
};

/// Checks that the two terms `sides` builds agree on every instance, and returns how many
/// instances were run. Fails at the first disagreement, naming the instance and both
/// outcomes.
int holds<I>(Iterable<I> instances, (Term, Term) Function(I) sides) {
  var n = 0;
  for (final inst in instances) {
    final (lhs, rhs) = sides(inst);
    final (a, b) = (outcome(lhs), outcome(rhs));
    if (!agree(a, b)) fail('the law fails on $inst:\n  left  $a\n  right $b');
    n++;
  }
  return n;
}

/// The first instance on which the two terms disagree, with both outcomes. Fails when they
/// agree on every instance, since the counterexample was expected.
(I, Object, Object) refuted<I>(Iterable<I> instances, (Term, Term) Function(I) sides) {
  for (final inst in instances) {
    final (lhs, rhs) = sides(inst);
    final (a, b) = (outcome(lhs), outcome(rhs));
    if (!agree(a, b)) return (inst, a, b);
  }
  fail('no instance refutes the equation');
}

/// Checks a property that is not an equation of two terms on every instance, and returns how
/// many were run. `prop` returns why an instance fails, or null when it holds.
int property<I>(Iterable<I> instances, String? Function(I) prop) {
  var n = 0;
  for (final inst in instances) {
    final why = prop(inst);
    if (why != null) fail('the property fails on $inst: $why');
    n++;
  }
  return n;
}

/// The first instance on which `prop` fails, with the reason. Fails when it holds on every
/// instance.
(I, String) propertyRefuted<I>(Iterable<I> instances, String? Function(I) prop) {
  for (final inst in instances) {
    final why = prop(inst);
    if (why != null) return (inst, why);
  }
  fail('no instance refutes the property');
}
