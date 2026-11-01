/// The tonicity of the scalar primitives and the scalar entries of the preimage catalog
/// (DESIGN.md sec:domains, "Backward transfer, and `@ensure`", and sec:constraints, "Both
/// directions, one rule"; step L1.25).
///
/// A preimage is computed over a kernel term whose free names are the inputs, each with an
/// interval domain, from a demand on the term's value: an interval for an integer term, `true`
/// or `false` for a test. The result is a box, one interval per input, that contains every
/// point of the inputs' domains at which the term meets the demand: a necessary condition,
/// which narrowing needs. When the box contains no other point it is marked exact, and it is
/// then also sufficient, which a precondition needs.
///
/// The catalog, applied from the term's root down:
///
/// - an input meets the demand exactly where its value lies in it;
/// - a term with no input is evaluated, and keeps the whole box or none of it;
/// - `+`, `-` and `*` with one constant operand, and Euclidean `div` and `mod` by a constant,
///   invert exactly, `mod` within the operand's forward interval, its first and last periods
///   exactly and the periods between them as one piece;
/// - `-x`, `abs` and `**` by a constant invert exactly at their endpoints, by the tonicity of
///   each sign part (the M0.5 revision table); a product of one value `k` times is read as its
///   `k`th power first (sec:constraints);
/// - `min` and `max` invert exactly with a constant operand, and with two operands when the
///   demand is a ray in the direction both must meet, or the other direction, where either may;
/// - a comparison with a constant operand is a demand on the other operand, and between two
///   terms a demand on their difference;
/// - `&&`, `||` and `!` meet, join and swap the preimages of their operands;
/// - a branch's preimage is the union of each arm's preimage met with its guard's;
/// - a `let` is read through, as the evaluator reads it; a call to a lambda is read through
///   once for each argument abstraction: each argument that reads an input and is an integer
///   is a parameter over its forward interval with its ends moved out to the landmarks (the
///   term's literals and the domains' ends, each with its neighbors), and the call's preimage
///   is the summary's box over the inputs met with each argument's preimage of the box over its
///   parameter; a call whose arguments are not of that kind is read through in place; and a
///   call of a lambda already being read stops the transfer, so the calls followed nest no
///   deeper than the number of lambdas;
/// - other integer operations take the HC4 projection of the M0.5 table, which is necessary and
///   not exact;
/// - string operations other than `len`, and calls to names that are not lambdas (foreign
///   calls), stop the transfer, and the stop is reported, as is any other term the scalar
///   catalog does not cover.
///
/// A union of two boxes is a box, and so exact, only when one contains the other or they differ
/// in one input. After the catalog, a result not marked exact is checked by forward transfer
/// over it: when every point it holds must meet the demand, it is exact. A result still not
/// exact over a listed box (every piece of every input's set holding no more members than its
/// endpoints, at most one input with more than one member), of a term whose form shows that it
/// ends, is enumerated: the term is run at each point, and the result is the projection of the
/// points that meet the demand, exact when they form a box. An enumeration that meets a term
/// the evaluator cannot run removes nothing.
///
/// Under `@exact` ([exactPreimage]) a result still not exact over a bounded box is found by
/// branch and prune (docs/thresholds.md, "`@exact`"): each sub-box is narrowed by the steps
/// above, and dropped when nothing in it meets the demand, kept whole when every point does,
/// and otherwise halved on its widest input; a single point is evaluated. A sub-box whose
/// values on every input are already known to meet the demand at some point is skipped, since
/// only each input's projection is sought. A scope under `@exact` does not list the projection,
/// which can have as many pieces as the box has points; it asks [witness] for one point that
/// meets the demand, and the same search stops at the first.
library;

import 'dart:collection';
import 'dart:math' as math;

import '../../stage.dart';
import '../canon/canon.dart' show sameTerm;
import '../kernel/error.dart';
import '../kernel/eval.dart';
import '../kernel/term.dart';
import '../kernel/value.dart';
import 'interval.dart';
import 'lattice.dart';
import 'presburger.dart' as pb;
import 'revision.dart';

/// An interval per input name, in name order.
typedef Domains = SplayTreeMap<String, IntervalSet>;

/// The congruence class of each input that has one, under `@exact`; an input not listed may be
/// any integer.
typedef Classes = Map<String, Congruence>;

/// A point of the inputs, each input within its class, at which the term meets the demand.
typedef Point = SplayTreeMap<String, int>;

/// What the term's value must be.
sealed class Demand {
  const Demand();

  /// Whether `v` meets the demand. An integer outside the 64-bit range lies in the set when
  /// the set is unbounded on its side.
  bool holds(Value v);
}

/// An integer in the set.
final class IntsDemand extends Demand {
  final IntervalSet z;

  const IntsDemand(this.z);

  @override
  bool holds(Value v) => switch (v) {
    Int(:final value) => z.contains(value),
    Big(:final value) => switch (z.bounds) {
      (final lo, final hi) => value.isNegative ? lo is NegInf : hi is PosInf,
      null => false,
    },
    _ => false,
  };

  @override
  bool operator ==(Object other) => other is IntsDemand && other.z == z;

  @override
  int get hashCode => z.hashCode;

  @override
  String toString() => 'Ints($z)';
}

/// The boolean.
final class BoolDemand extends Demand {
  final bool w;

  const BoolDemand(this.w);

  @override
  bool holds(Value v) => v is Bool && v.value == w;

  @override
  bool operator ==(Object other) => other is BoolDemand && other.w == w;

  @override
  int get hashCode => w.hashCode;

  @override
  String toString() => 'Bool($w)';
}

/// Why the transfer stopped.
sealed class StopKind {
  const StopKind();
}

/// A string operation other than `len`.
final class StringStop extends StopKind {
  final Prim prim;

  const StringStop(this.prim);

  @override
  bool operator ==(Object other) => other is StringStop && other.prim == prim;

  @override
  int get hashCode => prim.hashCode;
}

/// A call to a name that is not a lambda, or a free name that is not an input.
final class ForeignStop extends StopKind {
  final String name;

  const ForeignStop(this.name);

  @override
  bool operator ==(Object other) => other is ForeignStop && other.name == name;

  @override
  int get hashCode => name.hashCode;
}

/// A term the scalar catalog does not cover: families, folds, `fix`, patterns or ports.
final class OutsideStop extends StopKind {
  const OutsideStop();
}

/// A call of a lambda whose call is already being read.
final class RecursionStop extends StopKind {
  const RecursionStop();
}

/// A reported stop: its kind and the term it stopped at.
final class Stop {
  /// Why.
  final StopKind kind;

  /// The term, as the kernel prints it.
  final String term;

  const Stop(this.kind, this.term);

  @override
  bool operator ==(Object other) => other is Stop && other.kind == kind && other.term == term;

  @override
  int get hashCode => Object.hash(kind, term);

  @override
  String toString() {
    final why = switch (kind) {
      StringStop(:final prim) => 'string operation ${prim.label} stops the transfer at',
      ForeignStop(:final name) => 'foreign name `$name` stops the transfer at',
      OutsideStop() => 'no scalar catalog entry for',
      RecursionStop() => 'a call of a function already being read at',
    };
    return '$why $term';
  }
}

/// A preimage.
final class Preimage {
  /// The box: every point at which the term meets the demand lies in it.
  final Domains domains;

  /// Whether every point of the box meets the demand.
  final bool exact;

  /// Whether the box came from enumeration.
  final bool enumerated;

  /// Where the transfer stopped.
  final List<Stop> stops;

  /// The relation the inputs must meet, when the box is not exact and the linear-relation
  /// domain states the demand: every point meeting the demand meets it, and every point of the
  /// box meeting it meets the demand.
  final pb.Relation? relation;

  const Preimage(this.domains, this.exact, this.enumerated, this.stops, [this.relation]);
}

/// The most factors read as one power: an integer power past 64 of anything but -1, 0 and 1
/// leaves the 64-bit integers.
const _powerFactors = 64;

/// The preimage of `demand` under `term`, whose free names in `inputs` range over their
/// domains.
Preimage preimage(Term term, Map<String, IntervalSet> inputs, Demand demand) =>
    _preimageIn(term, Domains.of(inputs), demand);

Preimage _preimageIn(Term term, Domains inputs, Demand demand) {
  final root = _Scope.empty();
  final marks = _landmarks(term, inputs, demand);
  final cx = _Cx(inputs, _Shared(marks));
  rounded();
  var r = cx._back(term, root, demand);
  // An exact backward transfer through a rounded end may keep points that fail.
  if (rounded()) r = _Res(r.dom, false);
  final stops = cx.shared.stops;
  var enumerated = false;
  if (!r.exact && !_isEmpty(r.dom)) {
    final over = _Cx(r.dom, _Shared(marks));
    if (over._fwd(term, root).meets(demand)) r = _Res(r.dom, true);
  }
  pb.Relation? relation;
  rounded();
  if (!r.exact && !_isEmpty(r.dom)) {
    if (_linear(term, r.dom, demand) case (final dom, final exact, final rel)) {
      r = _Res(dom, exact && !rounded());
      relation = r.exact ? null : rel;
    }
  }
  if (!r.exact) {
    if (_enumerate(term, r.dom, demand) case final e?) {
      r = e;
      enumerated = true;
      if (r.exact) relation = null;
    }
  }
  // Adjacent repeats are dropped.
  final kept = <Stop>[
    for (var i = 0; i < stops.length; i++)
      if (i == 0 || stops[i] != stops[i - 1]) stops[i],
  ];
  return Preimage(r.dom, r.exact, enumerated, kept, relation);
}

/// The relations the linear-relation domain states for `terms`, tests over the free names
/// `inputs`, with one numbering of auxiliary variables; products of two symbols are atoms when
/// `products` holds. Null when a term is outside the domain.
List<pb.Relation>? relations(List<Term> terms, List<String> inputs, bool products) {
  final doms = Domains()..addAll({for (final n in inputs) n: IntervalSet.top()});
  final cx = _Cx(doms, _Shared(Landmarks.none()));
  final tr = _Tr(products);
  final root = _Scope.empty();
  final out = <pb.Relation>[];
  for (final t in terms) {
    // An auxiliary variable belongs to the relation of the term that made it.
    cx.memo
      ..lin.clear()
      ..formula.clear()
      ..linCalls.clear()
      ..formulaCalls.clear()
      ..log.clear();
    final first = tr.defs.length;
    final body = cx._formula(tr, t, root);
    if (body == null) return null;
    out.add(pb.Relation(body, tr.defs.sublist(first)));
  }
  return out;
}

/// The linear stage: the relation of the demand over the box `dom`, the box narrowed to its
/// projections, whether the box entails the relation, and the relation. Null when the term is
/// outside the domain or a question is undecided.
(Domains, bool, pb.Relation)? _linear(Term term, Domains dom, Demand demand) {
  final cx = _Cx(dom, _Shared(Landmarks.none()));
  final tr = _Tr(false);
  final root = _Scope.empty();
  final pb.Formula body;
  switch (demand) {
    case BoolDemand(:final w):
      final f = cx._formula(tr, term, root);
      if (f == null) return null;
      body = w ? f : pb.Formula.negate(f);
    case IntsDemand(:final z):
      final l = cx._lin(tr, term, root);
      if (l == null) return null;
      body = pb.within(l, z);
  }
  final rel = pb.Relation(body, tr.defs);
  pb.Formula within(Domains d) => pb.Formula.and([
    for (final MapEntry(:key, :value) in d.entries) pb.member(pb.Sym(key), value),
  ]);
  try {
    final whole = pb.Formula.and([rel.defined, within(dom), body]);
    final mentioned = body.atoms;
    for (final (_, _, f) in rel.defs) {
      mentioned.addAll(f.atoms);
    }
    final syms = [
      for (final k in dom.keys)
        if (mentioned.contains(pb.Sym(k))) pb.Sym(k),
    ];
    final each = pb.projectEach(whole, syms).iterator;
    final out = Domains();
    dom.forEach((k, v) {
      if (mentioned.contains(pb.Sym(k))) {
        each.moveNext();
        out[k] = (each.current ?? (throw const pb.Over())).meet(v);
      } else {
        out[k] = v;
      }
    });
    if (_isEmpty(out)) return (_empty(out), true, rel);
    final outside = pb.Formula.and([rel.defined, within(out), pb.Formula.negate(body)]);
    final bool exact;
    try {
      exact = pb.satisfiable(outside) == null;
    } on pb.Over {
      return (out, false, rel);
    }
    return (out, exact, rel);
  } on pb.Over {
    return null;
  }
}

/// The translation of terms into the linear-relation domain: the definitions of the auxiliary
/// variables made so far.
final class _Tr {
  final defs = <(int, String, pb.Formula)>[];
  final bool products;

  _Tr(this.products);

  pb.Atom aux(String what, pb.Formula def) {
    final n = defs.length;
    defs.add((n, what, def));
    return pb.Aux(n);
  }
}

/// A call to translate: the lambda, by its body and scope, and its arguments' linear terms.
final class _CallKey {
  final _Key key;
  final List<pb.Lin> args;

  _CallKey(this.key, this.args);

  @override
  bool operator ==(Object other) {
    if (other is! _CallKey || other.key != key || other.args.length != args.length) return false;
    for (var i = 0; i < args.length; i++) {
      if (other.args[i] != args[i]) return false;
    }
    return true;
  }

  @override
  int get hashCode => Object.hash(key, Object.hashAll(args));
}

/// The tonicity of a scalar primitive in argument `arg`, the others fixed, with `false` below
/// `true` for the tests (sec:domains, rule (1)); null where the primitive is not of one
/// tonicity on each part of one sign, or not a scalar operator.
Tonicity? primTonicity(Prim p, int arg) {
  final Tonicity t;
  switch ((p, arg)) {
    case (Prim.add || Prim.sub || Prim.mul || Prim.min || Prim.max, _) ||
        (Prim.intDiv || Prim.mod, _) ||
        (Prim.neg || Prim.abs, 0):
      t = tonicity(_op(p)!, arg);
    case (Prim.lt || Prim.le, 0) || (Prim.gt || Prim.ge, 1) || (Prim.not, 0):
      t = Tonicity.down;
    case (Prim.lt || Prim.le, 1) || (Prim.gt || Prim.ge, 0) || (Prim.and || Prim.or, _):
      t = Tonicity.up;
    default:
      return null;
  }
  return t == Tonicity.none ? null : t;
}

/// The revision table's operator for a primitive, with the constant exponent of `**`.
Op? _op(Prim p, [int? exponent]) => switch (p) {
  Prim.add => Op.add,
  Prim.sub => Op.sub,
  Prim.mul => Op.mul,
  Prim.intDiv => Op.div,
  Prim.mod => Op.mod,
  Prim.neg => Op.neg,
  Prim.abs => Op.abs,
  Prim.min => Op.min,
  Prim.max => Op.max,
  Prim.pow when exponent != null => Op.pow(exponent),
  _ => null,
};

/// The landmarks a summary's parameters and demands move out to: the term's integer literals,
/// the ends of the input domains and of the demand, each with its neighbors. A finite set, so
/// a lambda has finitely many summaries.
Landmarks _landmarks(Term term, Domains inputs, Demand demand) {
  final ints = <int>[];
  final seen = HashSet<Term>.identity();
  final todo = [term];
  while (todo.isNotEmpty) {
    final t = todo.removeLast();
    if (!seen.add(t)) continue;
    switch (t) {
      case Lit(value: Int(:final value)):
        ints.add(value);
      case Lam(:final body):
        todo.add(body);
      case App(:final f, :final args):
        todo.addAll([...args.reversed, f]);
      case PrimApp(:final args):
        todo.addAll(args.reversed);
      case Let(:final value, :final body):
        todo.addAll([body, value]);
      case If(:final cond, :final then, :final orElse):
        todo.addAll([orElse, then, cond]);
      default:
    }
  }
  Iterable<int> ends(IntervalSet s) => [
    for (final (a, b) in s.pieces) ...[if (a case Fin(:final v)) v, if (b case Fin(:final v)) v],
  ];
  ints.addAll(inputs.values.expand(ends));
  if (demand case IntsDemand(:final z)) ints.addAll(ends(z));
  return Landmarks.of(ints);
}

/// A term and the scope it is read in, by identity: neither has a structural equality.
typedef _Key = (Term, _Scope);

/// A summarized call: the lambda, by its body and scope, and its arguments, each a parameter
/// over an interval ([IntervalSet]), a constant (`int` or `bool`), or a term that reads no
/// input, by the term and scope it resolves to ([_Key]).
final class _Summary {
  final _Key key;
  final List<Object> args;

  _Summary(this.key, this.args);

  @override
  bool operator ==(Object other) {
    if (other is! _Summary || other.key != key || other.args.length != args.length) return false;
    for (var i = 0; i < args.length; i++) {
      if (other.args[i] != args[i]) return false;
    }
    return true;
  }

  @override
  int get hashCode => Object.hash(key, Object.hashAll(args));
}

/// A call to summarize: its summary, each parameter's binding (a name, its term and the scope
/// it is read in), and the parameters over intervals (the argument's place, the input that
/// stands for it, the interval).
final class _Call {
  final _Summary key;
  final List<(String, Term, _Scope)> binds;
  final List<(int, String, IntervalSet)> params;

  _Call(this.key, this.binds, this.params);
}

/// What every context of one transfer shares.
final class _Shared {
  final stops = <Stop>[];
  final seen = <String>{};

  /// The bodies of the lambdas whose calls are being read, each with its place on the stack.
  final active = HashMap<Term, int>.identity();
  final Landmarks marks;
  final fwds = <_Summary, _Fwd>{};
  final backs = <(_Summary, Demand), _Res>{};
  final scanned = <_Summary>{};

  /// A number for each lambda body, which names the inputs that stand for its parameters.
  final ids = HashMap<Term, int>.identity();

  _Shared(this.marks);
}

bool _isEmpty(Domains d) => d.values.any((s) => s.isEmpty);

/// A scope: the names bound by `let` and by calls, each to a term and the scope it is read
/// in.
final class _Scope {
  final String? name;
  final Term? term;
  final _Scope? at, parent;

  _Scope.empty() : name = null, term = null, at = null, parent = null;

  _Scope.bind(_Scope this.parent, String this.name, Term this.term, _Scope this.at);

  /// The term `x` is bound to, with the scope it is read in.
  (Term, _Scope)? lookup(String x) {
    for (var s = this; s.name != null; s = s.parent!) {
      if (s.name == x) return (s.term!, s.at!);
    }
    return null;
  }
}

/// What a call reaches.
sealed class _Callee {}

/// A lambda's parameters and body, with the scope the body is read in.
final class _LamCallee extends _Callee {
  final List<String> params;
  final Term body;
  final _Scope lam;

  _LamCallee(this.params, this.body, this.lam);
}

/// A primitive, as a prelude word binds it (the interpreter's prelude, step L1.18).
final class _PrimCallee extends _Callee {
  final Prim prim;

  _PrimCallee(this.prim);
}

/// A free name that is not a lambda.
final class _ForeignCallee extends _Callee {
  final String name;

  _ForeignCallee(this.name);
}

/// Anything else.
final class _NoCallee extends _Callee {}

/// A result before the final checks: the box and whether it is exact. Neither is changed once
/// made, since results are shared through the memo tables.
final class _Res {
  final Domains dom;
  final bool exact;

  _Res(this.dom, this.exact);
}

/// What forward transfer knows of a term's value.
final class _Fwd {
  /// The integers it may be.
  final IntervalSet ints;

  /// Whether it may be `true`, and `false`.
  final bool t, f;

  /// Whether it may be a failure: an atom such as `#divByZero`, which every primitive but
  /// `==` and `!=` passes through.
  final bool fails;

  /// Whether it may be a value of another kind: a string, a float, a function.
  final bool other;

  const _Fwd({
    this.ints = const IntervalSet.empty(),
    this.t = false,
    this.f = false,
    this.fails = false,
    this.other = false,
  });

  _Fwd.int(IntervalSet ints) : this(ints: ints);

  static final top = _Fwd(ints: IntervalSet.top(), t: true, f: true, fails: true, other: true);

  bool get hasBools => t || f;

  /// Whether it is certainly an integer.
  bool get isInt => !fails && !other && !hasBools;

  /// Whether it is certainly a boolean.
  bool get isBool => !fails && !other && ints.isEmpty;

  /// Whether every value it may be meets `d`.
  bool meets(Demand d) => switch (d) {
    IntsDemand(:final z) => isInt && ints.isSubset(z),
    BoolDemand(:final w) => isBool && !(w ? f : t),
  };
}

/// What the transfer has computed, for each pair of a term and a scope, so that a name bound
/// once is followed once however often it is read (the rule of low complexity, Part G).
final class _Memo {
  /// The scopes of `let` bodies, call bodies and lambda bodies, by the term that makes them.
  final envs = <_Key, _Scope>{};

  /// The primitive applications that calls of prelude words stand for.
  final calls = <_Key, Term>{};

  /// The differences that comparisons of two terms stand for, by the two terms.
  final diffs = <(Term, Term), Term>{};
  final mentions = <_Key, bool?>{};
  final constant = <_Key, Value?>{};
  final fwd = <_Key, _Fwd>{};
  final back = <(Term, _Scope, Demand), _Res>{};
  final scan = <_Key>{};
  final lin = <_Key, pb.Lin?>{};
  final formula = <_Key, pb.Formula?>{};

  /// The translations of calls, by the lambda and the translations of the arguments: a body's
  /// value depends on its parameters only through their values, so calls whose arguments
  /// translate alike translate alike, however they are reached.
  final linCalls = <_CallKey, pb.Lin?>{};
  final formulaCalls = <_CallKey, pb.Formula?>{};

  /// The translation entries in the order they were made, each with its table, which a
  /// translation that is undone removes.
  final log = <(Map<Object, Object?>, Object)>[];
}

/// No place on the stack of lambdas being read.
const _nowhere = maxInt;

final class _Cx {
  final Domains inputs;
  final _Shared shared;

  /// The lowest place on the stack of lambdas being read whose lambda a call stopped at,
  /// since the result being computed began. A result is remembered only when that place is
  /// not below the stack's height when it began: otherwise it depends on where it was
  /// reached.
  int cut = _nowhere;
  final memo = _Memo();

  _Cx(this.inputs, this.shared);

  /// `f(place)` with the lambda whose body is `body` on the stack of lambdas being read, at
  /// `place`; or `stopped`, with the stop reported, when it is already there, since that call
  /// would make the same call again. The stack holds distinct lambdas, so it is no higher
  /// than the number of lambdas in the term.
  V _through<V>(Term t, Term body, V stopped, V Function(int place) f) {
    if (shared.active[body] case final at?) {
      cut = math.min(cut, at);
      _stop(const RecursionStop(), t);
      return stopped;
    }
    final place = shared.active.length;
    shared.active[body] = place;
    final v = f(place);
    shared.active.remove(body);
    return v;
  }

  /// The summary of a call of `\ps. body` in scope `lam` with `args` read in `env`, or null
  /// when an argument that reads an input may be other than an integer, or reads a term the
  /// catalog does not follow.
  _Call? _summon(List<String> ps, Term body, _Scope lam, List<Term> args, _Scope env) {
    final empty = _Scope.empty();
    final sig = <Object>[];
    final binds = <(String, Term, _Scope)>[];
    final params = <(int, String, IntervalSet)>[];
    for (var i = 0; i < ps.length; i++) {
      final (p, a) = (ps[i], args[i]);
      final m = _mentions(a, env);
      if (m == null) return null;
      if (m) {
        final f = _fwd(a, env);
        if (!f.isInt) return null;
        final dom = f.ints.snap(shared.marks);
        // A name no source name can be; the lambda is read once at a time.
        final id = shared.ids.putIfAbsent(body, () => shared.ids.length);
        final name = '\u0001$i.$id';
        binds.add((p, Var(name), empty));
        params.add((i, name, dom));
        sig.add(dom);
        continue;
      }
      switch (_constant(a, env)) {
        case Int(:final value):
          binds.add((p, Lit(Int(value)), empty));
          sig.add(value);
        case Bool(:final value):
          binds.add((p, Lit(Bool(value)), empty));
          sig.add(value);
        default:
          var (t, e) = (a, env);
          while (t is Var) {
            final b = e.lookup(t.name);
            if (b == null) break;
            (t, e) = b;
          }
          sig.add((t, e));
          binds.add((p, t, e));
      }
    }
    return _Call(_Summary((body, lam), sig), binds, params);
  }

  /// The context a summary is computed in: the inputs and the call's parameters, and the
  /// lambda's scope with its parameters bound.
  (_Cx, _Scope) _open(_Call call, _Scope lam) {
    final inputs = Domains.of(this.inputs);
    for (final (_, n, d) in call.params) {
      inputs[n] = d;
    }
    var e = lam;
    for (final (p, t, at) in call.binds) {
      e = _Scope.bind(e, p, t, at);
    }
    return (_Cx(inputs, shared), e);
  }

  /// Whether a summary computed in `sub` for the lambda at `place` holds wherever it is
  /// reached; the stops below it are passed on.
  bool _closes(_Cx sub, int place) {
    final c = sub.cut;
    cut = math.min(cut, c);
    return c >= place;
  }

  /// The forward value of a summarized call.
  _Fwd _callFwd(_Call call, Term body, _Scope lam, int place) {
    if (shared.fwds[call.key] case final f?) return f;
    final (sub, e) = _open(call, lam);
    final f = sub._fwd(body, e);
    if (_closes(sub, place)) shared.fwds[call.key] = f;
    return f;
  }

  /// The preimage of a summarized call: the summary's box over the inputs, met with each
  /// argument's preimage of the summary's interval for its parameter. Exact when the summary
  /// is, the demand's ends are landmarks, and each argument's preimage is exact.
  ///
  /// A summary keeps only the inputs it narrows. Its context holds every input of the
  /// context that first reached it, the parameters of enclosing summaries among them, and
  /// another context reaching the same summary may give those other intervals. An input
  /// the body reads has the same interval wherever the summary is reached: an input of the
  /// transfer is the same in every context, and an enclosing parameter is read through the
  /// lambda's scope, which the summary's key holds.
  _Res _callBack(
    _Call call,
    Term body,
    _Scope lam,
    List<Term> args,
    _Scope env,
    Demand d,
    int place,
  ) {
    var same = true;
    if (d case IntsDemand(:final z)) {
      final s = z.snap(shared.marks);
      same = s == z;
      d = IntsDemand(s);
    }
    final k = (call.key, d);
    var r = shared.backs[k];
    if (r == null) {
      final (sub, e) = _open(call, lam);
      final full = sub._backAt(body, e, d);
      final narrowed = Domains();
      full.dom.forEach((k, z) {
        if (z != sub.inputs[k]) narrowed[k] = z;
      });
      r = _Res(narrowed, full.exact);
      if (_closes(sub, place)) shared.backs[k] = r;
    }
    if (_isEmpty(r.dom)) return _none();
    final dom = Domains();
    inputs.forEach((k, z) => dom[k] = r!.dom[k] ?? z);
    var out = _Res(dom, r.exact && same);
    for (final (i, n, dom) in call.params) {
      if (r.dom[n] case final z? when !dom.isSubset(z)) {
        out = _meet(out, _backAt(args[i], env, IntsDemand(z)));
      }
    }
    return out;
  }

  /// `f()`, remembered under `k` in `map` unless a call it reads stopped at a lambda that was
  /// being read before it began.
  V _cached<K, V>(Map<K, V> map, K k, V Function() f) {
    if (map.containsKey(k)) return map[k] as V;
    final base = shared.active.length;
    final outer = cut;
    cut = _nowhere;
    final v = f();
    final c = cut;
    if (c >= base) map[k] = v;
    cut = math.min(outer, c);
    return v;
  }

  /// [_cached] for the translation into the linear-relation domain, whose entries a translation
  /// that is undone removes.
  V _translated<K extends Object, V>(Map<K, V> map, K k, V Function() f) {
    final known = map.containsKey(k);
    final v = _cached(map, k, f);
    if (!known && map.containsKey(k)) memo.log.add((map, k));
    return v;
  }

  /// Removes the translation's entries made after the first `mark`.
  void _forget(int mark) {
    for (final (map, k) in memo.log.sublist(mark)) {
      map.remove(k);
    }
    memo.log.length = mark;
  }

  /// The key a call of the lambda `body` in scope `lam` is translated under: null, with what
  /// the attempt made undone, when an argument has no linear term.
  _CallKey? _callKey(_Tr tr, Term body, _Scope lam, List<Term> args, _Scope env) {
    final (mark, logged) = (tr.defs.length, memo.log.length);
    final lins = <pb.Lin>[];
    for (final a in args) {
      final l = _lin(tr, a, env);
      if (l == null) {
        tr.defs.length = mark;
        _forget(logged);
        return null;
      }
      lins.add(l);
    }
    return _CallKey((body, lam), lins);
  }

  /// The scope of a `let` body, made once for each `let` and scope.
  _Scope _letEnv(Let t, _Scope env) =>
      memo.envs.putIfAbsent((t, env), () => _Scope.bind(env, t.name, t.value, env));

  /// The primitive application a call `t` of a prelude word stands for.
  Term _callPrim(Term t, _Scope env, Prim p, List<Term> args) =>
      memo.calls.putIfAbsent((t, env), () => PrimApp(p, args));

  _Res _all() => _Res(inputs, true);

  _Res _none() =>
      _Res(Domains()..addAll({for (final k in inputs.keys) k: IntervalSet.empty()}), true);

  _Res _stop(StopKind kind, Term t) {
    final s = Stop(kind, t.toString());
    if (shared.seen.add(s.toString())) shared.stops.add(s);
    return _Res(inputs, false);
  }

  _Res _meet(_Res a, _Res b) {
    final dom = Domains();
    a.dom.forEach((k, v) => dom[k] = v.meet(b.dom[k]!));
    if (_isEmpty(dom)) return _none();
    return _Res(dom, a.exact && b.exact);
  }

  /// The union, as the per-input join of the two boxes: exact when both are and the union is
  /// itself a box.
  _Res _union(_Res a, _Res b) {
    if (_isEmpty(a.dom)) return b;
    if (_isEmpty(b.dom)) return a;
    final differ = a.dom.entries.where((e) => e.value != b.dom[e.key]).length;
    bool within(Domains x, Domains y) => x.entries.every((e) => e.value.isSubset(y[e.key]!));
    final boxed = differ <= 1 || within(a.dom, b.dom) || within(b.dom, a.dom);
    final dom = Domains();
    a.dom.forEach((k, v) => dom[k] = v.join(b.dom[k]!));
    return _Res(dom, a.exact && b.exact && boxed);
  }

  /// Whether the term reads an input, or null when it reads a term the catalog does not
  /// follow.
  bool? _mentions(Term t, _Scope env) =>
      _cached(memo.mentions, (t, env), () => _mentionsAt(t, env));

  bool? _mentionsAt(Term t, _Scope env) {
    bool? any(Iterable<(Term, _Scope)> ts) {
      var m = false;
      for (final (t, e) in ts) {
        final x = _mentions(t, e);
        if (x == null) return null;
        m |= x;
      }
      return m;
    }

    switch (t) {
      case Lit() || PrimFn():
        return false;
      case Var(:final name):
        if (env.lookup(name) case (final bt, final benv)) return _mentions(bt, benv);
        return inputs.containsKey(name);
      case Let(:final value, :final body):
        return any([(value, env), (body, _letEnv(t, env))]);
      case Lam(:final params, :final body):
        // A parameter is not an input, even where it shadows one.
        final inner = memo.envs.putIfAbsent((t, env), () {
          var inner = env;
          for (final p in params) {
            inner = _Scope.bind(inner, p, const Lit(Bool(false)), inner);
          }
          return inner;
        });
        return _mentions(body, inner);
      case App(:final f, :final args):
        return any([(f, env), for (final a in args) (a, env)]);
      case PrimApp(:final args):
        return any([for (final a in args) (a, env)]);
      case If(:final cond, :final then, :final orElse):
        return any([(cond, env), (then, env), (orElse, env)]);
      default:
        return null;
    }
  }

  /// The term with every bound name replaced by the closed term it is bound to, for a term
  /// that reads no input.
  Term? _close(Term t, _Scope env) {
    List<Term>? all(List<Term> ts) {
      final out = <Term>[];
      for (final a in ts) {
        final c = _close(a, env);
        if (c == null) return null;
        out.add(c);
      }
      return out;
    }

    switch (t) {
      case Var(:final name):
        if (env.lookup(name) case (final bt, final benv)) return _close(bt, benv);
        return t;
      case Lit() || PrimFn():
        return t;
      case Let(:final name, :final value, :final body):
        // The body reads `name` as the closed bound term.
        final e = _close(value, env);
        if (e == null) return null;
        return _close(body, _Scope.bind(env, name, e, _Scope.empty()));
      case Lam(:final params, :final body):
        var inner = env;
        for (final p in params) {
          inner = _Scope.bind(inner, p, Var(p), _Scope.empty());
        }
        final b = _close(body, inner);
        return b == null ? null : Lam(params, b);
      case App(:final f, :final args):
        final (g, xs) = (_close(f, env), all(args));
        return g == null || xs == null ? null : App(g, xs);
      case PrimApp(:final prim, :final args):
        final xs = all(args);
        return xs == null ? null : PrimApp(prim, xs);
      case If(:final cond, :final then, :final orElse):
        final (g, a, b) = (_close(cond, env), _close(then, env), _close(orElse, env));
        return g == null || a == null || b == null ? null : If(g, a, b);
      default:
        return null;
    }
  }

  /// The value of a term that reads no input, when the evaluator can compute it.
  Value? _constant(Term t, _Scope env) => _cached(memo.constant, (t, env), () {
    if (_mentions(t, env) != false) return null;
    // From the values of the parts where the catalog reads them, so that a part is run once;
    // otherwise the closed term.
    switch (t) {
      case Lit(:final value):
        return value;
      case Var(:final name) when env.lookup(name) != null:
        final (bt, benv) = env.lookup(name)!;
        return _constant(bt, benv);
      case Let(:final body):
        return _constant(body, _letEnv(t, env));
      case PrimApp(:final prim, :final args):
        final vs = <Term>[];
        for (final a in args) {
          final v = _constant(a, env);
          if (v == null) return null;
          vs.add(Lit(v));
        }
        return _run(PrimApp(prim, vs));
      case If(:final cond, :final then, :final orElse):
        switch (_constant(cond, env)) {
          case null:
            return null;
          case Bool(value: true):
            return _constant(then, env);
          case Bool(value: false):
            return _constant(orElse, env);
          default:
        }
      default:
    }
    final c = _close(t, env);
    return c == null ? null : _run(c);
  });

  int? _constantInt(Term t, _Scope env) => switch (_constant(t, env)) {
    Int(:final value) => value,
    _ => null,
  };

  /// The function a call reaches, with the scope its body is read in. Each name is looked up
  /// in the scope its binding was made in, which was built before that binding, so the walk
  /// ends.
  _Callee _callee(Term f, _Scope env) {
    while (true) {
      switch (f) {
        case Lam(:final params, :final body):
          return _LamCallee(params, body, env);
        case PrimFn(:final prim):
          return _PrimCallee(prim);
        case Var(:final name):
          final b = env.lookup(name);
          if (b == null) return _ForeignCallee(name);
          (f, env) = b;
        default:
          return _NoCallee();
      }
    }
  }

  /// The scope of a call's body: the lambda's scope with each parameter bound to its
  /// argument, read in the caller's scope.
  _Scope _callEnv(Term t, List<String> ps, List<Term> args, _Scope lam, _Scope caller) =>
      memo.envs.putIfAbsent((t, caller), () {
        var e = lam;
        for (var i = 0; i < ps.length; i++) {
          e = _Scope.bind(e, ps[i], args[i], caller);
        }
        return e;
      });

  /// The factors of a product of one value read `k` times, as that value and `k`.
  (Term, _Scope, int)? _power(Term t, _Scope env) {
    final fs = <(Term, _Scope)>[];
    void factors(Term t, _Scope env) {
      while (t is Var) {
        final b = env.lookup(t.name);
        if (b == null) break;
        (t, env) = b;
      }
      if (fs.length > _powerFactors) return;
      if (t case PrimApp(prim: Prim.mul, :final args) when args.length == 2) {
        factors(args[0], env);
        factors(args[1], env);
      } else {
        fs.add((t, env));
      }
    }

    factors(t, env);
    final (first, fenv) = fs[0];
    bool one((Term, _Scope) f) => switch ((f.$1, first)) {
      (Var(name: final x), Var(name: final y)) when x == y => true,
      _ => (identical(f.$1, first) || sameTerm(f.$1, first)) && identical(f.$2, fenv),
    };
    return fs.length >= 2 && fs.length <= _powerFactors && fs.every(one)
        ? (first, fenv, fs.length)
        : null;
  }

  // ---- Into the linear-relation domain ----------------------------------------------------

  /// The linear term an integer term states over the inputs.
  pb.Lin? _lin(_Tr tr, Term t, _Scope env) =>
      _translated(memo.lin, (t, env), () => _linAt(tr, t, env));

  pb.Lin? _linAt(_Tr tr, Term t, _Scope env) {
    if (_constant(t, env) case final v?) {
      return v is Int ? pb.Lin.constant(BigInt.from(v.value)) : null;
    }
    switch (t) {
      case Var(:final name):
        if (env.lookup(name) case (final bt, final benv)) return _lin(tr, bt, benv);
        return inputs.containsKey(name) ? pb.Lin.atom(pb.Sym(name)) : null;
      case Let(:final body):
        return _lin(tr, body, _letEnv(t, env));
      case App(:final f, :final args):
        switch (_callee(f, env)) {
          case _LamCallee(:final params, :final body, :final lam) when params.length == args.length:
            pb.Lin? read() => _through(t, body, null, (_) {
              return _lin(tr, body, _callEnv(t, params, args, lam, env));
            });
            final k = _callKey(tr, body, lam, args, env);
            return k == null ? read() : _translated(memo.linCalls, k, read);
          case _PrimCallee(:final prim):
            return _lin(tr, _callPrim(t, env, prim, args), env);
          default:
            return null;
        }
      case If(:final cond, :final then, :final orElse):
        final g = _formula(tr, cond, env);
        if (g == null) return null;
        final la = _lin(tr, then, env);
        if (la == null) return null;
        final lb = _lin(tr, orElse, env);
        if (lb == null) return null;
        final x = pb.Lin.atom(pb.Aux(tr.defs.length));
        tr.aux(
          t.toString(),
          pb.Formula.or([
            pb.Formula.and([g, pb.Con.eq(x, la)]),
            pb.Formula.and([pb.Formula.negate(g), pb.Con.eq(x, lb)]),
          ]),
        );
        return x;
      case PrimApp(:final prim, :final args) when prim.arity == null || prim.arity == args.length:
        pb.Lin? arg(int i) => _lin(tr, args[i], env);
        switch (prim) {
          case Prim.add:
            if (arg(0) case final a?) if (arg(1) case final b?) return a.plus(b);
            return null;
          case Prim.sub:
            if (arg(0) case final a?) if (arg(1) case final b?) return a.minus(b);
            return null;
          case Prim.neg:
            return arg(0)?.times(BigInt.from(-1));
          case Prim.mul:
            final a = arg(0);
            if (a == null) return null;
            final b = arg(1);
            if (b == null) return null;
            if (!tr.products && a.terms.isNotEmpty && b.terms.isNotEmpty) return null;
            return a.product(b);
          case Prim.pow:
            switch (_constantInt(args[1], env)) {
              case 0:
                return pb.Lin.constant(BigInt.one);
              case 1:
                return arg(0);
              case 2 when tr.products:
                final a = arg(0);
                return a?.product(a);
              default:
                return null;
            }
          case Prim.intDiv || Prim.mod:
            final c = _constantInt(args[1], env);
            if (c == null || c == 0) return null;
            final a = arg(0);
            if (a == null) return null;
            // `a == c·q + r` and `0 <= r < |c|`: Euclidean.
            final n = tr.defs.length;
            final (q, r) = (pb.Lin.atom(pb.Aux(n)), pb.Lin.atom(pb.Aux(n + 1)));
            final def = pb.Formula.and([
              pb.Con.eq(a, q.times(BigInt.from(c)).plus(r)),
              pb.Con.ge(r, pb.Lin.zero),
              pb.Con.ge(pb.Lin.constant(BigInt.from(c.abs() - 1)), r),
            ]);
            String shown(String op) => '${args[0]} $op $c';
            tr.defs
              ..add((n, shown('div'), def))
              ..add((n + 1, shown('mod'), pb.Formula.top));
            return prim == Prim.intDiv ? q : r;
          case Prim.min || Prim.max || Prim.abs:
            final a = arg(0);
            if (a == null) return null;
            final b = prim == Prim.abs ? a.times(BigInt.from(-1)) : arg(1);
            if (b == null) return null;
            final x = pb.Lin.atom(pb.Aux(tr.defs.length));
            // `min` takes `a` where `a <= b`, `max` and `abs` where `a >= b`.
            final first = prim == Prim.min ? pb.Con.ge(b, a) : pb.Con.ge(a, b);
            tr.aux(
              t.toString(),
              pb.Formula.or([
                pb.Formula.and([first, pb.Con.eq(x, a)]),
                pb.Formula.and([pb.Formula.negate(first), pb.Con.eq(x, b)]),
              ]),
            );
            return x;
          default:
            return null;
        }
      default:
        return null;
    }
  }

  /// The formula a test states over the inputs.
  pb.Formula? _formula(_Tr tr, Term t, _Scope env) =>
      _translated(memo.formula, (t, env), () => _formulaAt(tr, t, env));

  pb.Formula? _formulaAt(_Tr tr, Term t, _Scope env) {
    if (_constant(t, env) case final v?) {
      return switch (v) {
        Bool(value: true) => pb.Formula.top,
        Bool(value: false) => pb.Formula.bottom,
        _ => null,
      };
    }
    switch (t) {
      case Var(:final name):
        if (env.lookup(name) case (final bt, final benv)) return _formula(tr, bt, benv);
        return null;
      case Let(:final body):
        return _formula(tr, body, _letEnv(t, env));
      case App(:final f, :final args):
        switch (_callee(f, env)) {
          case _LamCallee(:final params, :final body, :final lam) when params.length == args.length:
            pb.Formula? read() => _through(t, body, null, (_) {
              return _formula(tr, body, _callEnv(t, params, args, lam, env));
            });
            final k = _callKey(tr, body, lam, args, env);
            return k == null ? read() : _translated(memo.formulaCalls, k, read);
          case _PrimCallee(:final prim):
            return _formula(tr, _callPrim(t, env, prim, args), env);
          default:
            return null;
        }
      case If(:final cond, :final then, :final orElse):
        final g = _formula(tr, cond, env);
        if (g == null) return null;
        final fa = _formula(tr, then, env);
        if (fa == null) return null;
        final fb = _formula(tr, orElse, env);
        if (fb == null) return null;
        return pb.Formula.or([
          pb.Formula.and([g, fa]),
          pb.Formula.and([pb.Formula.negate(g), fb]),
        ]);
      case PrimApp(:final prim, :final args) when prim.arity == null || prim.arity == args.length:
        switch (prim) {
          case Prim.not:
            final a = _formula(tr, args[0], env);
            return a == null ? null : pb.Formula.negate(a);
          case Prim.and || Prim.or:
            final a = _formula(tr, args[0], env);
            if (a == null) return null;
            final b = _formula(tr, args[1], env);
            if (b == null) return null;
            return prim == Prim.and ? pb.Formula.and([a, b]) : pb.Formula.or([a, b]);
          case Prim.lt || Prim.le || Prim.gt || Prim.ge || Prim.eq || Prim.ne:
            final (mark, logged) = (tr.defs.length, memo.log.length);
            if (_lin(tr, args[0], env) case final a?) {
              if (_lin(tr, args[1], env) case final b?) {
                final one = pb.Lin.constant(BigInt.one);
                final c = switch (prim) {
                  Prim.lt => pb.Con.ge(b, a.plus(one)),
                  Prim.le => pb.Con.ge(b, a),
                  Prim.gt => pb.Con.ge(a, b.plus(one)),
                  Prim.ge => pb.Con.ge(a, b),
                  _ => pb.Con.eq(a, b),
                };
                return prim == Prim.ne ? pb.Formula.negate(c) : c;
              }
            }
            tr.defs.length = mark;
            _forget(logged);
            if (prim != Prim.eq && prim != Prim.ne) return null;
            // Two tests are equal where both hold or neither does.
            final a = _formula(tr, args[0], env);
            if (a == null) return null;
            final b = _formula(tr, args[1], env);
            if (b == null) return null;
            final same = pb.Formula.or([
              pb.Formula.and([a, b]),
              pb.Formula.and([pb.Formula.negate(a), pb.Formula.negate(b)]),
            ]);
            return prim == Prim.ne ? pb.Formula.negate(same) : same;
          default:
            return null;
        }
      default:
        return null;
    }
  }

  _Fwd _fwd(Term t, _Scope env) => _cached(memo.fwd, (t, env), () => _fwdAt(t, env));

  _Fwd _fwdAt(Term t, _Scope env) {
    switch (t) {
      case Lit(value: Int(:final value)):
        return _Fwd.int(IntervalSet.single(value));
      case Lit(value: Bool(:final value)):
        return _Fwd(t: value, f: !value);
      case Lit(value: Atom()):
        return const _Fwd(fails: true);
      case Lit():
        return const _Fwd(other: true);
      case Var(:final name):
        if (env.lookup(name) case (final bt, final benv)) return _fwd(bt, benv);
        final dom = inputs[name];
        return dom != null ? _Fwd.int(dom) : _Fwd.top;
      case Let(:final body):
        return _fwd(body, _letEnv(t, env));
      case If(:final cond, :final then, :final orElse):
        final g = _fwd(cond, env);
        // A guard that is not a test is a failure.
        var (ints, yes, no, fails, other) = (
          const IntervalSet.empty(),
          false,
          false,
          !g.isBool,
          false,
        );
        for (final (arm, live) in [(then, g.t), (orElse, g.f)]) {
          if (!live) continue;
          final f = _fwd(arm, env);
          ints = ints.join(f.ints);
          yes |= f.t;
          no |= f.f;
          fails |= f.fails;
          other |= f.other;
        }
        return _Fwd(ints: ints, t: yes, f: no, fails: fails, other: other);
      case App(:final f, :final args):
        switch (_callee(f, env)) {
          case _LamCallee(:final params, :final body, :final lam) when params.length == args.length:
            return _through(t, body, _Fwd.top, (place) {
              final call = _summon(params, body, lam, args, env);
              return call != null
                  ? _callFwd(call, body, lam, place)
                  : _fwd(body, _callEnv(t, params, args, lam, env));
            });
          case _PrimCallee(:final prim):
            return _fwd(_callPrim(t, env, prim, args), env);
          default:
            return _Fwd.top;
        }
      case PrimApp(:final prim, :final args):
        return _fwdPrim(t, prim, args, env);
      default:
        return _Fwd.top;
    }
  }

  _Fwd _fwdPrim(Term t, Prim p, List<Term> args, _Scope env) {
    if (p.arity != null && p.arity != args.length) return _Fwd.top;
    if (p == Prim.mul) {
      if (_power(t, env) case (final base, final benv, final k)) {
        final b = _fwd(base, benv);
        return _arith(Op.pow(k), b, b, false);
      }
    }
    switch (p) {
      case Prim.neg || Prim.abs:
        final a = _fwd(args[0], env);
        return _arith(_op(p)!, a, a, false);
      case Prim.pow:
        final k = _constantInt(args[1], env);
        if (k == null || k < 0 || k > 0xffffffff) return _Fwd.top;
        final a = _fwd(args[0], env);
        return _arith(Op.pow(k), a, a, false);
      case Prim.add || Prim.sub || Prim.mul || Prim.intDiv || Prim.mod || Prim.min || Prim.max:
        final a = _fwd(args[0], env);
        final b = _fwd(args[1], env);
        final byZero = (p == Prim.intDiv || p == Prim.mod) && b.ints.contains(0);
        return _arith(_op(p)!, a, b, byZero);
      case Prim.lt || Prim.le || Prim.gt || Prim.ge || Prim.eq || Prim.ne:
        final a = _fwd(args[0], env);
        final b = _fwd(args[1], env);
        if (a.isInt && b.isInt) return _compare(p, a.ints, b.ints);
        // Values of other kinds compare as data under `==` and `!=`, and otherwise fail or
        // compare in an order this transfer does not follow.
        return _Fwd(t: true, f: true, fails: p != Prim.eq && p != Prim.ne);
      case Prim.not:
        final a = _fwd(args[0], env);
        return _Fwd(t: a.f, f: a.t, fails: !a.isBool);
      case Prim.and || Prim.or:
        final a = _fwd(args[0], env);
        final b = _fwd(args[1], env);
        final (yes, no) = p == Prim.and ? (a.t && b.t, a.f || b.f) : (a.t || b.t, a.f && b.f);
        return _Fwd(t: yes, f: no, fails: !a.isBool || !b.isBool);
      default:
        return _Fwd.top;
    }
  }

  /// An integer operator over its operands' forward values.
  _Fwd _arith(Op o, _Fwd a, _Fwd b, bool byZero) =>
      _Fwd(ints: forward(o, a.ints, b.ints), fails: !a.isInt || !b.isInt || byZero);

  // ---- Backward transfer --------------------------------------------------------------

  _Res _back(Term t, _Scope env, Demand d) => _backAt(t, env, d);

  _Res _backAt(Term t, _Scope env, Demand d) =>
      _cached(memo.back, (t, env, d), () => _backIn(t, env, d));

  _Res _backIn(Term t, _Scope env, Demand d) {
    if (d case IntsDemand(:final z) when z.isEmpty) return _none();
    // A term that reads no input is decided by running it.
    if (t is! Var) {
      if (_constant(t, env) case final v?) return d.holds(v) ? _all() : _none();
    }
    switch (t) {
      case Var(:final name):
        if (env.lookup(name) case (final bt, final benv)) return _backAt(bt, benv, d);
        final dom = inputs[name];
        if (dom == null) return _stop(ForeignStop(name), t);
        switch (d) {
          case IntsDemand(:final z):
            final r = Domains.of(inputs)..[name] = dom.meet(z);
            return _isEmpty(r) ? _none() : _Res(r, true);
          case BoolDemand():
            return _none();
        }
      case Lit(:final value):
        return d.holds(value) ? _all() : _none();
      case Let(:final body):
        return _backAt(body, _letEnv(t, env), d);
      case If(:final cond, :final then, :final orElse):
        final gt = _backAt(cond, env, const BoolDemand(true));
        final at = _backAt(then, env, d);
        final gf = _backAt(cond, env, const BoolDemand(false));
        final bf = _backAt(orElse, env, d);
        return _union(_meet(gt, at), _meet(gf, bf));
      case App(:final f, :final args):
        switch (_callee(f, env)) {
          case _LamCallee(:final params, :final body, :final lam) when params.length == args.length:
            return _through(t, body, _Res(inputs, false), (place) {
              final call = _summon(params, body, lam, args, env);
              return call != null
                  ? _callBack(call, body, lam, args, env, d, place)
                  : _backAt(body, _callEnv(t, params, args, lam, env), d);
            });
          case _PrimCallee(:final prim):
            return _backAt(_callPrim(t, env, prim, args), env, d);
          case _ForeignCallee(:final name):
            return _stop(ForeignStop(name), t);
          default:
            return _stop(const OutsideStop(), t);
        }
      case PrimApp(:final prim, :final args):
        if (prim.arity != null && prim.arity != args.length) return _stop(const OutsideStop(), t);
        return _backPrim(t, prim, args, env, d);
      default:
        return _stop(const OutsideStop(), t);
    }
  }

  _Res _backPrim(Term t, Prim p, List<Term> args, _Scope env, Demand d) {
    switch (p) {
      case Prim.show || Prim.lower || Prim.upper || Prim.trim || Prim.concat:
        return _stop(StringStop(p), t);
      // `len` moves the demand to the length facet, which is not an input here; the terms
      // below it may still stop.
      case Prim.len:
        _scan(args[0], env);
        return _Res(inputs, false);
      case Prim.not || Prim.and || Prim.or:
        switch (d) {
          case IntsDemand():
            return _none();
          case BoolDemand(:final w) when p == Prim.not:
            return _backAt(args[0], env, BoolDemand(!w));
          case BoolDemand(:final w):
            final a = _backAt(args[0], env, d);
            final b = _backAt(args[1], env, d);
            if ((p == Prim.and) == w) return _meet(a, b);
            // `&&` and `||` here are strict: one side meeting the demand is enough only when
            // the other cannot fail.
            final strict = _fwd(args[0], env).isBool && _fwd(args[1], env).isBool;
            final r = _union(a, b);
            return _Res(r.dom, r.exact && strict);
        }
      case Prim.lt || Prim.le || Prim.gt || Prim.ge || Prim.eq || Prim.ne:
        return switch (d) {
          IntsDemand() => _none(),
          BoolDemand(:final w) => _backCompare(w ? p : _negate(p), args[0], args[1], env),
        };
      case Prim.add || Prim.sub || Prim.mul || Prim.intDiv || Prim.mod || Prim.neg || Prim.abs:
      case Prim.pow:
        return switch (d) {
          IntsDemand(:final z) => _backArith(t, p, args, env, z),
          BoolDemand() => _none(),
        };
      case Prim.min || Prim.max:
        return switch (d) {
          IntsDemand(:final z) => _backArith(t, p, args, env, z),
          // `min` and `max` of two tests are tests.
          BoolDemand() => _stop(const OutsideStop(), t),
        };
      default:
        return _stop(const OutsideStop(), t);
    }
  }

  _Res _backCompare(Prim p, Term a, Term b, _Scope env) {
    final (fa, fb) = (_fwd(a, env), _fwd(b, env));
    // Two tests are equal where both are true or both false.
    if ((p == Prim.eq || p == Prim.ne) && fa.isBool && fb.isBool) {
      _Res arm(bool w) =>
          _meet(_backAt(a, env, BoolDemand(w)), _backAt(b, env, BoolDemand(w == (p == Prim.eq))));
      final yes = arm(true);
      final no = arm(false);
      return _union(yes, no);
    }
    // An operand that may fail meets an ordered comparison nowhere, since the comparison fails
    // too, and `==` with an integer nowhere; it meets `!=` everywhere.
    final ints = fa.isInt && fb.isInt;
    bool orderedOrEq(_Fwd f) => !f.other && !f.hasBools && p != Prim.ne;
    if (_constantInt(b, env) case final c? when ints || orderedOrEq(fa)) {
      return _backAt(a, env, IntsDemand(_ray(p, c)));
    }
    if (_constantInt(a, env) case final c? when ints || orderedOrEq(fb)) {
      return _backAt(b, env, IntsDemand(_ray(_mirror(p), c)));
    }
    final oneInt = fa.isInt || fb.isInt;
    if (ints || (orderedOrEq(fa) && orderedOrEq(fb) && (p != Prim.eq || oneInt))) {
      // Between two integers, `a op b` is `a - b op 0`.
      final diff = memo.diffs.putIfAbsent((a, b), () => PrimApp(Prim.sub, [a, b]));
      return _backAt(diff, env, IntsDemand(_ray(p, 0)));
    }
    // Operands of other kinds, or two that may both fail, which `==` finds equal.
    _scan(a, env);
    _scan(b, env);
    return _Res(inputs, false);
  }

  /// Reports the stops in a term whose value the transfer does not follow.
  void _scan(Term t, _Scope env) {
    // A term is scanned once in each scope: its stops are reported the first time.
    if (!memo.scan.add((t, env))) return;
    if (_mentions(t, env) == false) return;
    switch (t) {
      case Var(:final name):
        if (env.lookup(name) case (final bt, final benv)) _scan(bt, benv);
      case Let(:final body):
        _scan(body, _letEnv(t, env));
      case If(:final cond, :final then, :final orElse):
        for (final u in [cond, then, orElse]) {
          _scan(u, env);
        }
      case App(:final f, :final args):
        switch (_callee(f, env)) {
          case _LamCallee(:final params, :final body, :final lam) when params.length == args.length:
            _through<void>(t, body, null, (place) {
              final call = _summon(params, body, lam, args, env);
              if (call == null) {
                _scan(body, _callEnv(t, params, args, lam, env));
              } else if (shared.scanned.add(call.key)) {
                final (sub, e) = _open(call, lam);
                sub._scan(body, e);
                _closes(sub, place);
              }
            });
          case _PrimCallee(:final prim):
            _scan(_callPrim(t, env, prim, args), env);
          case _ForeignCallee(:final name):
            _stop(ForeignStop(name), t);
          default:
            _stop(const OutsideStop(), t);
        }
      case PrimApp(:final prim)
          when const {Prim.show, Prim.lower, Prim.upper, Prim.trim, Prim.concat}.contains(prim):
        _stop(StringStop(prim), t);
      case PrimApp(:final prim, :final args) when _scalar(prim):
        for (final a in args) {
          _scan(a, env);
        }
      default:
        _stop(const OutsideStop(), t);
    }
  }

  _Res _backArith(Term t, Prim p, List<Term> args, _Scope env, IntervalSet z) {
    if (p == Prim.mul) {
      if (_power(t, env) case (final base, final benv, final k)) {
        return _backUnary(Op.pow(k), base, benv, z);
      }
    }
    switch (p) {
      case Prim.neg || Prim.abs:
        return _backUnary(_op(p)!, args[0], env, z);
      case Prim.pow:
        final k = _constantInt(args[1], env);
        // A variable exponent: only the points where both operands are integers.
        if (k == null || k < 0 || k > 0xffffffff) return _bothInts(args[0], args[1], env);
        return _backUnary(Op.pow(k), args[0], env, z);
      default:
    }
    final (a, b) = (args[0], args[1]);
    final ca = _constantInt(a, env);
    final cb = _constantInt(b, env);
    switch ((p, ca, cb)) {
      case (Prim.add, final int c, _):
        return _backAt(b, env, IntsDemand(_shift(z, -BigInt.from(c))));
      case (Prim.add, _, final int c):
        return _backAt(a, env, IntsDemand(_shift(z, -BigInt.from(c))));
      case (Prim.sub, _, final int c):
        return _backAt(a, env, IntsDemand(_shift(z, BigInt.from(c))));
      case (Prim.sub, final int c, _):
        return _backAt(b, env, IntsDemand(forward(Op.sub, IntervalSet.single(c), z)));
      case (Prim.mul, final int c, _):
        return _backAt(b, env, IntsDemand(_timesPre(z, c)));
      case (Prim.mul, _, final int c):
        return _backAt(a, env, IntsDemand(_timesPre(z, c)));
      case (Prim.intDiv, _, final int c):
        return _backAt(a, env, IntsDemand(_divPre(z, c)));
      case (Prim.mod, _, final int c):
        final (s, exact) = _modPre(z, c, _fwd(a, env).ints);
        final r = _backAt(a, env, IntsDemand(s));
        return _Res(r.dom, r.exact && exact);
      case (Prim.min || Prim.max, final int c, _):
        return _backAt(b, env, IntsDemand(_minmaxPre(p, z, c)));
      case (Prim.min || Prim.max, _, final int c):
        return _backAt(a, env, IntsDemand(_minmaxPre(p, z, c)));
      case (Prim.min || Prim.max, null, null):
        final f = _fwd(t, env).ints;
        final zf = z.meet(f);
        final (fb, zb) = (f.bounds, zf.bounds);
        if (fb == null || zb == null) return _none();
        final (flo, fhi) = fb;
        final (lo, hi) = zb;
        final up = IntervalSet.range(lo, fhi).isSubset(z);
        final down = IntervalSet.range(flo, hi).isSubset(z);
        // min ≥ lo: both are; max ≤ hi: both are. The other rays: either is. When the demand
        // holds the whole forward range, both rays apply; the upward one is taken.
        final both = (p == Prim.min && up) || (p == Prim.max && down && !up);
        final either = (p == Prim.min && down && !up) || (p == Prim.max && up);
        if (both || either) {
          final r = up ? IntervalSet.range(lo, posInf) : IntervalSet.range(negInf, hi);
          final ra = _backAt(a, env, IntsDemand(r));
          final rb = _backAt(b, env, IntsDemand(r));
          return both ? _meet(ra, rb) : _union(ra, rb);
        }
        return _project(p, a, b, env, z);
      default:
        return _project(p, a, b, env, z);
    }
  }

  /// `op(c)` in `z`, for an operator the revision table inverts exactly within the forward
  /// interval of `c`.
  _Res _backUnary(Op o, Term c, _Scope env, IntervalSet z) {
    if (o == const Op.pow(0)) {
      // `c ** 0` is 1 wherever `c` is an integer.
      return z.contains(1) ? _backAt(c, env, IntsDemand(IntervalSet.top())) : _none();
    }
    final fc = _fwd(c, env).ints;
    return _backAt(c, env, IntsDemand(backward(o, 0, fc, fc, z)));
  }

  /// The HC4 projection onto each operand: necessary, not exact.
  _Res _project(Prim p, Term a, Term b, _Scope env, IntervalSet z) {
    final o = _op(p)!;
    final fa = _fwd(a, env).ints;
    final fb = _fwd(b, env).ints;
    final za = backward(o, 0, fa, fb, z);
    final zb = backward(o, 1, fa, fb, z);
    final r = _meet(_backAt(a, env, IntsDemand(za)), _backAt(b, env, IntsDemand(zb)));
    return _Res(r.dom, _isEmpty(r.dom));
  }

  _Res _bothInts(Term a, Term b, _Scope env) {
    final top = IntsDemand(IntervalSet.top());
    final r = _meet(_backAt(a, env, top), _backAt(b, env, top));
    return _Res(r.dom, _isEmpty(r.dom));
  }
}

/// The value of a closed term, or null when the evaluator cannot run it.
Value? _run(Term t) {
  try {
    return eval(t);
  } on KernelError {
    return null;
  }
}

/// Whether the scalar catalog has an entry for the primitive, or reads through it (`len`).
bool _scalar(Prim p) => const {
  Prim.add,
  Prim.sub,
  Prim.mul,
  Prim.intDiv,
  Prim.mod,
  Prim.neg,
  Prim.abs,
  Prim.pow,
  Prim.min,
  Prim.max,
  Prim.lt,
  Prim.le,
  Prim.gt,
  Prim.ge,
  Prim.eq,
  Prim.ne,
  Prim.not,
  Prim.and,
  Prim.or,
  Prim.len,
}.contains(p);

/// Forward transfer of a comparison over two integer sets.
_Fwd _compare(Prim p, IntervalSet a, IntervalSet b) {
  final (ab, bb) = (a.bounds, b.bounds);
  if (ab == null || bb == null) return const _Fwd();
  final (alo, ahi) = ab;
  final (blo, bhi) = bb;
  Piece? one(IntervalSet x) => x.bounds != null && x.bounds!.$1 == x.bounds!.$2 ? x.bounds : null;
  final (bool, bool) tf;
  switch (p) {
    case Prim.lt:
      tf = (alo < bhi, ahi >= blo);
    case Prim.le:
      tf = (alo <= bhi, ahi > blo);
    case Prim.gt:
      tf = (ahi > blo, alo <= bhi);
    case Prim.ge:
      tf = (ahi >= blo, alo < bhi);
    default:
      final eq = !a.meet(b).isEmpty;
      final ne = !(one(a) != null && one(a) == one(b));
      tf = p == Prim.eq ? (eq, ne) : (ne, eq);
  }
  return _Fwd(t: tf.$1, f: tf.$2);
}

/// The comparison that holds exactly when `p` is false, between two integers.
Prim _negate(Prim p) => switch (p) {
  Prim.lt => Prim.ge,
  Prim.le => Prim.gt,
  Prim.gt => Prim.le,
  Prim.ge => Prim.lt,
  Prim.eq => Prim.ne,
  _ => Prim.eq,
};

/// The comparison `p` with its operands swapped.
Prim _mirror(Prim p) => switch (p) {
  Prim.lt => Prim.gt,
  Prim.le => Prim.ge,
  Prim.gt => Prim.lt,
  Prim.ge => Prim.le,
  _ => p,
};

/// The integers `x` with `x p c`.
IntervalSet _ray(Prim p, int c) {
  final v = BigInt.from(c);
  return switch (p) {
    Prim.lt => IntervalSet.range(negInf, End.upper(v - BigInt.one)),
    Prim.le => IntervalSet.range(negInf, End.upper(v)),
    Prim.gt => IntervalSet.range(End.lower(v + BigInt.one), posInf),
    Prim.ge => IntervalSet.range(End.lower(v), posInf),
    Prim.eq => IntervalSet.range(End.lower(v), End.upper(v)),
    _ => IntervalSet.single(c).complementIn(IntervalSet.top()),
  };
}

/// Each piece of `z` moved up by `c`.
IntervalSet _shift(IntervalSet z, BigInt c) {
  End m(End e, End Function(BigInt) end) => e is Fin ? end(BigInt.from(e.v) + c) : e;
  return IntervalSet.fromPieces([
    for (final (lo, hi) in z.pieces) (m(lo, End.lower), m(hi, End.upper)),
  ]);
}

/// The floor of `v / d`, for `d > 0`.
BigInt _floorDiv(BigInt v, BigInt d) => (v - v % d) ~/ d;

/// The integers `x` with `x * c` in `z`.
IntervalSet _timesPre(IntervalSet z, int c) {
  if (c == 0) return z.contains(0) ? IntervalSet.top() : const IntervalSet.empty();
  final cb = BigInt.from(c);
  // ceil and floor of v / c, at an endpoint.
  End q(End e, bool up) {
    if (e case Fin(:final v)) {
      final (n, d) = c < 0 ? (-BigInt.from(v), -cb) : (BigInt.from(v), cb);
      var f = _floorDiv(n, d);
      if (up && f * d != n) f += BigInt.one;
      return up ? End.lower(f) : End.upper(f);
    }
    return c < 0 ? -e : e;
  }

  return IntervalSet.fromPieces([
    for (final (lo, hi) in z.pieces)
      c > 0 ? (q(lo, true), q(hi, false)) : (q(hi, true), q(lo, false)),
  ]);
}

/// The integers `x` with `x div c` in `z`, Euclidean: `x = q * c + r` with `r` in
/// `0..abs(c)`.
IntervalSet _divPre(IntervalSet z, int c) {
  if (c == 0) return const IntervalSet.empty();
  final cb = BigInt.from(c);
  final m = cb.abs();
  End lower(End e) => switch (e) {
    Fin(:final v) => End.lower(BigInt.from(v) * cb),
    _ => c < 0 ? -e : e,
  };
  End upper(End e) => switch (e) {
    Fin(:final v) => End.upper(BigInt.from(v) * cb + m - BigInt.one),
    _ => c < 0 ? -e : e,
  };
  return IntervalSet.fromPieces([
    for (final (lo, hi) in z.pieces) c > 0 ? (lower(lo), upper(hi)) : (lower(hi), upper(lo)),
  ]);
}

/// The members of `within` with `x mod c` in `z`, Euclidean, and whether that is all of them
/// and no more. The first and last periods `within` meets are listed exactly and the periods
/// between them are one piece, so the set has at most `2 * p + 1` pieces for `p` pieces of
/// remainders, and it is exact when there is no period between them. An unbounded `within`
/// is kept whole unless every remainder is demanded.
(IntervalSet, bool) _modPre(IntervalSet z, int c, IntervalSet within) {
  if (c == 0) return (const IntervalSet.empty(), true);
  final m = BigInt.from(c).abs();
  final all = IntervalSet.range(const Fin(0), End.exact(m - BigInt.one));
  final rem = z.meet(all);
  if (rem.isEmpty) return (const IntervalSet.empty(), true);
  if (rem == all) return (within, true);
  if (within.bounds case (Fin(v: final lo), Fin(v: final hi))) {
    final (k0, k1) = (_floorDiv(BigInt.from(lo), m), _floorDiv(BigInt.from(hi), m));
    List<Piece> period(BigInt k) => [
      for (final (a, b) in rem.pieces)
        if ((a, b) case (Fin(v: final a), Fin(v: final b)))
          (End.exact(k * m + BigInt.from(a)), End.exact(k * m + BigInt.from(b))),
    ];
    final pieces = period(k0);
    if (k1 > k0 + BigInt.one) {
      final (Fin(v: a), Fin(v: b)) = rem.bounds! as (Fin, Fin);
      pieces.add((
        End.exact((k0 + BigInt.one) * m + BigInt.from(a)),
        End.exact((k1 - BigInt.one) * m + BigInt.from(b)),
      ));
    }
    if (k1 > k0) pieces.addAll(period(k1));
    return (IntervalSet.fromPieces(pieces).meet(within), k1 <= k0 + BigInt.one);
  }
  return (within, false);
}

/// The integers `x` with `min(x, c)` (or `max`) in `z`.
IntervalSet _minmaxPre(Prim p, IntervalSet z, int c) {
  final atC = p == Prim.min ? IntervalSet.range(Fin(c), posInf) : IntervalSet.range(negInf, Fin(c));
  final below = p == Prim.min
      ? IntervalSet.range(negInf, Fin(c))
      : IntervalSet.range(Fin(c), posInf);
  final own = z.meet(below);
  return z.contains(c) ? own.join(atC) : own;
}

/// `term` with each input of `point` bound to its value by a `let`, in name order.
Term _at(Term term, Iterable<(String, int)> point) {
  var t = term;
  for (final (k, v) in point.toList().reversed) {
    t = Let(k, Lit(Int(v)), t);
  }
  return t;
}

/// The projection of the points of a listed box at which the term meets the demand: every
/// input's set is listed, each piece holding no more members than its two endpoints (the rule
/// by which a type lists an interval), and at most one input has more than one member, so the
/// points number no more than the endpoints written (docs/thresholds.md, replacement 8). The
/// term's form must show that it ends ([ends]). A range is left to the catalog.
_Res? _enumerate(Term term, Domains dom, Demand demand) {
  if (!ends(term)) return null;
  final axes = <(String, List<int>)>[];
  for (final MapEntry(:key, :value) in dom.entries) {
    final vs = <int>[];
    for (final (lo, hi) in value.pieces) {
      if ((lo, hi) case (Fin(v: final lo), Fin(v: final hi)) when hi == lo || hi - 1 == lo) {
        vs.addAll([for (var v = lo; v <= hi; v++) v]);
      } else {
        return null;
      }
    }
    axes.add((key, vs));
  }
  if (axes.where((a) => a.$2.length > 1).length > 1) return null;
  if (axes.any((a) => a.$2.isEmpty)) return _Res(dom, true);
  return _enumerateOn(term, axes, demand);
}

/// The enumeration of [_enumerate] over `axes`.
_Res? _enumerateOn(Term term, List<(String, List<int>)> axes, Demand demand) {
  final met = [for (final _ in axes) <int>[]];
  var count = 0;
  final point = List.filled(axes.length, 0);
  while (true) {
    final t = _at(term, [for (var j = 0; j < axes.length; j++) (axes[j].$1, axes[j].$2[point[j]])]);
    final v = _run(t);
    if (v == null) return null;
    if (demand.holds(v)) {
      count++;
      for (var j = 0; j < axes.length; j++) {
        met[j].add(axes[j].$2[point[j]]);
      }
    }
    // The next point, the last axis fastest.
    var j = axes.length;
    while (true) {
      if (j == 0) {
        final dom = Domains();
        for (var i = 0; i < axes.length; i++) {
          dom[axes[i].$1] = IntervalSet.fromPieces([for (final v in met[i]) (Fin(v), Fin(v))]);
        }
        final product = met.fold(1, (n, vs) => n * vs.toSet().length);
        return _Res(dom, product == count);
      }
      j--;
      point[j]++;
      if (point[j] < axes[j].$2.length) break;
      point[j] = 0;
    }
  }
}

/// The preimage of `demand` under `term` when its declaration is annotated `@exact`
/// (DESIGN.md sec:constraints): [preimage], and where that is not exact, every input is
/// bounded and the term's form shows that it ends, the projection of the points of the box, in
/// their inputs' `classes`, that meet the demand. Its cost is that of the points the analysis
/// cannot decide in bulk, which the annotation accepts; there is no limit on them. The result
/// is exact when the projections' product holds no point that fails the demand, which a second
/// search, for such a point, decides. A point the evaluator cannot run leaves the result of
/// [preimage].
Preimage exactPreimage(Term term, Map<String, IntervalSet> inputs, Classes classes, Demand demand) {
  final p = _preimageIn(term, Domains.of(inputs), demand);
  if (p.exact) {
    // Every point of the box meets the demand, so the classes alone narrow it.
    final dom = _withinClasses(p.domains, classes) ?? _empty(p.domains);
    return Preimage(dom, true, p.enumerated, p.stops);
  }
  if (!ends(term)) return p;
  final found = _exactSearch(term, p.domains, classes, demand);
  if (found == null) return p;
  return Preimage(found.$1, found.$2, true, p.stops, found.$2 ? null : p.relation);
}

/// Every input of `d` with the empty set.
Domains _empty(Domains d) =>
    Domains()..addAll({for (final k in d.keys) k: const IntervalSet.empty()});

/// A point of `inputs`, each input within its class, at which `term` meets `demand`: a
/// record holding the point, or holding null when there is none. The search of
/// [exactPreimage] stops at the first point found, and a box on which the preimage is exact
/// gives its lowest point, so it holds only the boxes on its stack, two for each halving. Null
/// when an input is unbounded, a point cannot be run, or the term's form does not show that it
/// ends and the preimage alone does not decide.
({Point? point})? witness(
  Term term,
  Map<String, IntervalSet> inputs,
  Classes classes,
  Demand demand,
) {
  Point lowest(Domains b) => Point()
    ..addAll({for (final MapEntry(:key, :value) in b.entries) key: (value.bounds!.$1 as Fin).v});
  if (inputs.values.any((s) => !s.isEmpty && !_bounded(s))) return null;
  final dom = _withinClasses(Domains.of(inputs), classes);
  if (dom == null) return (point: null);
  if (!ends(term)) {
    final r = _preimageIn(term, dom, demand);
    final narrowed = Domains();
    dom.forEach((k, s) => narrowed[k] = s.meet(r.domains[k]!));
    final n = _withinClasses(narrowed, classes);
    if (n == null) return (point: null);
    return r.exact ? (point: lowest(n)) : null;
  }
  Point? found;
  final stopped = _branch(term, dom, classes, demand, (_) => false, (b) {
    found = lowest(b);
    return true;
  });
  if (stopped == null) return null;
  return (point: found);
}

/// Whether both ends of `s` are finite.
bool _bounded(IntervalSet s) => s.bounds is (Fin, Fin);

/// The projection of the points of `dom` in `classes` meeting `demand`, and whether their box
/// holds no point that fails it; null when an input is unbounded or a point cannot be run.
(Domains, bool)? _exactSearch(Term term, Domains dom, Classes classes, Demand demand) {
  final within = _withinClasses(dom, classes);
  if (within == null) return (_empty(dom), true);
  if (within.values.any((s) => !_bounded(s))) return null;
  final met = _empty(within);
  final ran = _branch(
    term,
    within,
    classes,
    demand,
    (b) => b.entries.every((e) => e.value.isSubset(met[e.key]!)),
    (b) {
      b.forEach((k, s) => met[k] = met[k]!.join(s));
      return false;
    },
  );
  if (ran == null) return null;
  final several = met.values.where((s) => !_isPoint(s)).length;
  if (met.values.any((s) => s.isEmpty) || several <= 1) return (met, true);
  final fails = switch (demand) {
    BoolDemand(:final w) => BoolDemand(!w),
    IntsDemand(:final z) => IntsDemand(z.complementIn(IntervalSet.top())),
  };
  final found = _branch(term, Domains.of(met), classes, fails, (_) => false, (_) => true);
  if (found == null) return null;
  return (met, !found);
}

/// Branch and prune over `root`: each box not `skip`ped is narrowed by [preimage] and its
/// inputs' classes, and dropped when empty, given to `all` when every point meets `demand`,
/// and otherwise halved on its widest input; a single point is evaluated. Every box is smaller
/// than the one it was split from, so the search ends. True when `all` stopped it, null when a
/// point cannot be run.
bool? _branch(
  Term term,
  Domains root,
  Classes classes,
  Demand demand,
  bool Function(Domains) skip,
  bool Function(Domains) all,
) {
  // The classes hold for the whole search, so their arithmetic is read once: it can decide the
  // term on every point of the box, as `x * x mod 10 == 9` with `x` in `5 mod 10`.
  switch (_classesDecide(term, classes, demand)) {
    case false:
      return false;
    case true:
      return all(root);
    case null:
  }
  final boxes = [root];
  while (boxes.isNotEmpty) {
    var b = boxes.removeLast();
    if (skip(b)) continue;
    if (!b.values.every(_isPoint)) {
      final r = _preimageIn(term, b, demand);
      final narrowed = Domains();
      b.forEach((k, s) => narrowed[k] = s.meet(r.domains[k]!));
      final n = _withinClasses(narrowed, classes);
      if (n == null) continue;
      if (r.exact) {
        if (all(n)) return true;
        continue;
      }
      b = n;
    }
    if (b.values.every(_isPoint)) {
      final v = _run(
        _at(term, [for (final e in b.entries) (e.key, (e.value.bounds!.$1 as Fin).v)]),
      );
      if (v == null) return null;
      if (demand.holds(v) && all(b)) return true;
      continue;
    }
    // The widest input, the last of those equally wide.
    String? k;
    var (lo, hi, width) = (0, 0, BigInt.from(-1));
    for (final MapEntry(:key, :value) in b.entries) {
      if (value.bounds case (Fin(v: final l), Fin(v: final h)) when l < h) {
        final w = BigInt.from(h) - BigInt.from(l);
        if (w >= width) (k, lo, hi, width) = (key, l, h, w);
      }
    }
    final mid = (BigInt.from(lo) + (BigInt.from(hi) - BigInt.from(lo)) ~/ BigInt.two).toInt();
    for (final half in [
      IntervalSet.range(Fin(mid + 1), posInf),
      IntervalSet.range(negInf, Fin(mid)),
    ]) {
      final h = Domains.of(b)..[k!] = b[k]!.meet(half);
      if (_withinClasses(h, classes) case final h?) boxes.add(h);
    }
  }
  return false;
}

/// Whether every integer point with each input in its class meets `demand` under `term`
/// (true), none does (false), or the classes do not decide (null).
bool? _classesDecide(Term term, Classes classes, Demand demand) {
  switch (demand) {
    case BoolDemand(:final w):
      final b = _classTest(term, classes);
      return b == null ? null : b == w;
    case IntsDemand(:final z):
      final c = _classOf(term, classes);
      if (c == null) return null;
      if (c.isBottom) return false;
      if (c.modulus == 0) return z.contains(c.residue);
      return null;
  }
}

/// The value of the test `term` at every point with each input in its class, if one value.
bool? _classTest(Term term, Classes classes) {
  switch (term) {
    case Lit(value: Bool(:final value)):
      return value;
    case Let(:final name, :final body):
      return _classTest(body, _unbound(classes, name));
    case PrimApp(prim: Prim.not, args: [final a]):
      final x = _classTest(a, classes);
      return x == null ? null : !x;
    case PrimApp(prim: Prim.and, args: [final a, final b]):
      return switch ((_classTest(a, classes), _classTest(b, classes))) {
        (false, _) || (_, false) => false,
        (true, true) => true,
        _ => null,
      };
    case PrimApp(prim: Prim.or, args: [final a, final b]):
      return switch ((_classTest(a, classes), _classTest(b, classes))) {
        (true, _) || (_, true) => true,
        (false, false) => false,
        _ => null,
      };
    case PrimApp(prim: final p && (Prim.eq || Prim.ne), args: [final a, final b]):
      final x = _classOf(a, classes);
      if (x == null) return null;
      final y = _classOf(b, classes);
      if (y == null) return null;
      final bool eq;
      if (x.modulus == 0 && y.modulus == 0) {
        eq = x.residue == y.residue;
      } else if (x.meet(y).isBottom) {
        eq = false;
      } else {
        return null;
      }
      return eq == (p == Prim.eq);
    default:
      return null;
  }
}

/// The class of the integer `term` at every point with each input in its class, by Granger's
/// arithmetic of congruences; null for a form it does not cover or a class too fine to hold.
Congruence? _classOf(Term term, Classes classes) {
  // A class as (modulus, residue), and back, null when it leaves the 64-bit integers.
  (BigInt, BigInt)? parts(Congruence? c) =>
      c == null || c.isBottom ? null : (BigInt.from(c.modulus!), BigInt.from(c.residue));
  Congruence? cls(BigInt m, BigInt r) {
    final res = m == BigInt.zero ? r : r % m;
    if (!m.isValidInt || !res.isValidInt) return null;
    return Congruence(m.toInt(), res.toInt());
  }

  switch (term) {
    case Lit(value: Int(:final value)):
      return Congruence.single(value);
    case Var(:final name):
      return classes[name] ?? Congruence.top;
    case Let(:final name, :final body):
      return _classOf(body, _unbound(classes, name));
    case PrimApp(prim: Prim.neg, args: [final a]):
      final x = parts(_classOf(a, classes));
      return x == null ? null : cls(x.$1, -x.$2);
    case PrimApp(prim: final p && (Prim.add || Prim.sub), args: [final a, final b]):
      final x = parts(_classOf(a, classes));
      final y = parts(_classOf(b, classes));
      if (x == null || y == null) return null;
      return cls(x.$1.gcd(y.$1), p == Prim.add ? x.$2 + y.$2 : x.$2 - y.$2);
    case PrimApp(prim: Prim.mul, args: [final a, final b]):
      // (r mod m)(s mod n) is rs mod gcd(mn, rn, sm).
      final x = parts(_classOf(a, classes));
      final y = parts(_classOf(b, classes));
      if (x == null || y == null) return null;
      final ((m, r), (n, s)) = (x, y);
      return cls((m * n).gcd(r * n).gcd(s * m), r * s);
    case PrimApp(prim: Prim.mod, args: [final a, Lit(value: Int(value: final k))]) when k > 0:
      // `x mod k` is Euclidean, so in 0..k; when k divides the modulus it is one value, and
      // otherwise it is x's residue modulo gcd(m, k).
      final x = parts(_classOf(a, classes));
      if (x == null) return null;
      final (m, r) = x;
      final kb = BigInt.from(k);
      return m % kb == BigInt.zero ? cls(BigInt.zero, r % kb) : cls(m.gcd(kb), r);
    default:
      return null;
  }
}

/// `classes` without `x`, which a `let` has bound to a value the classes do not hold.
Classes _unbound(Classes classes, String x) => Map.of(classes)..remove(x);

/// `dom` with each input's set tightened to its class, or null when one is then empty.
Domains? _withinClasses(Domains dom, Classes classes) {
  final d = Domains();
  dom.forEach((k, s) => d[k] = classes[k] == null ? s : reduceCongruence(s, classes[k]!).$1);
  return _isEmpty(d) ? null : d;
}

/// Whether `s` is one value.
bool _isPoint(IntervalSet s) => switch (s.bounds) {
  (Fin(v: final a), Fin(v: final b)) => a == b,
  _ => false,
};
