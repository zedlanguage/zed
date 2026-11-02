/// Step L1.39: the reduced product (DESIGN.md sec:domains and sec:constraints).
///
/// Each name in scope holds a product of its cell, its type and its binding time, and the
/// scope holds the linear relation and the written constraints. `spec` checks the design's
/// examples: an arm whose test fixes `n mod 4 == 1` within `0..=10` holds `n` in `1..=9`, an
/// arm whose test no value meets is unreachable and the program is accepted, and a binding
/// read from a static `if` is static. `random` checks against the interpreter that each arm's
/// scope holds every value that reaches it and that no value reaches an unreachable arm,
/// `controls` checks each reduction and that each check of `random` rejects a wrong answer,
/// `exact` checks scopes under `@exact`, and `scaling` checks the time against the size.
library;

import 'package:zed/kernel.dart' hide Lattice;
import 'package:zed/store.dart';

import '../l01_16_elaboration/elab.dart';
import '../l01_25_preimage_catalog/support.dart';

/// No premises.
const none = Premises.empty;

/// The scope of integer parameters `ps`, known only when the program runs.
Scope ints(List<String> ps) => Scope([for (final p in ps) (p, Product.ofType(Type.integer))]);

/// The arms of the function `ok` that `src` defines, its parameters integers.
(List<String>, Term, List<Arm>) armsOf(String src) {
  final (ps, body) = function(src);
  return (ps, body, arms(body, ints(ps)));
}

/// The arm of `arms` whose test prints as containing `guard`, taken by `outcome`.
Arm arm(List<Arm> arms, String guard, bool outcome) =>
    arms.where((a) => a.guard.contains(guard) && a.outcome == outcome).firstOrNull ??
    (throw StateError(
      'no arm with test `$guard` and outcome $outcome among ${[for (final a in arms) a.guard]}',
    ));

/// The top-level binding `name` of the unit `src`, as a chain of `let` bindings.
Term binding(String src, String name) =>
    elab(src).get(name) ?? (throw StateError('$src: no binding `$name`'));
