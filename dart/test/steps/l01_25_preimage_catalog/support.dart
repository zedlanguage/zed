/// Step L1.25: the scalar entries of the preimage catalog, and the tonicity of the scalar
/// primitives (DESIGN.md sec:domains, "Backward transfer, and `@ensure`").
///
/// A preimage is taken of a function's body, elaborated from Zed source, from a demand on its
/// value, over a box of parameter domains. The interpreter is the oracle: `entries` checks
/// the preimages of ordinary preconditions and guards against the points that meet them,
/// `random` checks soundness, and exactness where it is claimed, on random terms and domains,
/// `stops` checks that each term the scalar catalog does not cover is reported, `tonicity`
/// checks each claimed tonicity by running the primitive, and `scaling` checks that the
/// transfer's time grows no faster than the rule of low complexity allows.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

import '../l01_16_elaboration/elab.dart';

/// The parameters and the body of the function `ok` that `src` defines, under the
/// interpreter's prelude and the unit's other definitions.
(List<String>, Term) function(String src) {
  var t = elab(src).get('ok') ?? (throw StateError('$src: no definition `ok`'));
  final lets = <(String, Term)>[];
  while (t is Let) {
    lets.add((t.name, t.value));
    t = t.body;
  }
  if (t is! Var) throw StateError('$src: not a closed definition: $t');
  final k = t.name;
  final f = lets.where((l) => l.$1 == k).firstOrNull?.$2;
  if (f is! Lam) throw StateError('$src: `$k` is not a function');
  var body = f.body;
  for (final (n, e) in lets.reversed) {
    body = Let(n, e, body);
  }
  return (f.params, withPrelude(body));
}

/// A bound of a domain; null for an unbounded end.
typedef Dom = (String, int?, int?);

/// The domains `name: [lo..=hi]`, null for an unbounded end.
Domains doms(List<Dom> ds) => Domains()
  ..addAll({
    for (final (n, lo, hi) in ds)
      n: IntervalSet.range(lo == null ? negInf : Fin(lo), hi == null ? posInf : Fin(hi)),
  });

/// Each name's set of the listed integers `vs`, as the source would list them.
Domains listed(List<(String, List<int>)> ds) => Domains()
  ..addAll({
    for (final (n, vs) in ds) n: IntervalSet.fromPieces([for (final v in vs) (Fin(v), Fin(v))]),
  });

/// The preimage of `demand` under the function `src`, over `ds`.
Preimage pre(String src, List<Dom> ds, Demand demand) =>
    preimage(function(src).$2, doms(ds), demand);

/// The preimage of `true`, printed: each parameter's set, then `exact` or `necessary`, then
/// `enumerated` when it was.
String shown(Preimage p) => [
  for (final MapEntry(:key, :value) in p.domains.entries) '$key $value',
  p.exact ? 'exact' : 'necessary',
  if (p.enumerated) 'enumerated',
  for (final s in p.stops) 'stop: $s',
].join('; ');

/// Whether `body` meets `demand` with the inputs `names` at `point`; a failure does not.
bool meets(Term body, List<String> names, List<int> point, Demand demand) {
  var t = body;
  for (var i = names.length - 1; i >= 0; i--) {
    t = Let(names[i], Lit(Int(point[i])), t);
  }
  try {
    return demand.holds(eval(t));
  } on KernelError {
    return false;
  }
}

/// The points of the box `ds` within `window` on each axis, as values in the order of
/// `names`.
List<List<int>> points(Domains ds, List<String> names, (int, int) window) {
  var out = <List<int>>[[]];
  for (final n in names) {
    final vs = [
      for (var v = window.$1; v <= window.$2; v++)
        if (ds[n]!.contains(v)) v,
    ];
    out = [
      for (final p in out)
        for (final v in vs) [...p, v],
    ];
  }
  return out;
}

/// Checks `p` against the interpreter on the points of `ds` within `window`: every point that
/// meets the demand is in the preimage, and when it is exact, every point in it meets the
/// demand. Returns how many points met it.
int check(Term body, Domains ds, Demand demand, Preimage p, (int, int) window) {
  final names = ds.keys.toList();
  var met = 0;
  for (final pt in points(ds, names, window)) {
    final inside = [for (var i = 0; i < names.length; i++) p.domains[names[i]]!.contains(pt[i])]
        .every((b) => b);
    if (meets(body, names, pt, demand)) {
      met++;
      expect(
        inside,
        isTrue,
        reason: '$body over $ds: $pt meets $demand but is outside ${shown(p)}',
      );
    } else if (p.exact) {
      expect(inside, isFalse, reason: '$body: $pt fails $demand but is inside exact ${shown(p)}');
    }
  }
  return met;
}
