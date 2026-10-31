/// Kernel terms: the calculus of DESIGN.md sec:kernel, which the reference evaluator runs.
library;

import 'value.dart';

/// A primitive operation. Its label is how messages name it.
enum Prim {
  add('Add', 2),
  sub('Sub', 2),
  mul('Mul', 2),
  div('Div', 2),
  intDiv('IntDiv', 2),
  mod('Mod', 2),
  neg('Neg', 1),
  eq('Eq', 2),
  ne('Ne', 2),
  lt('Lt', 2),
  le('Le', 2),
  gt('Gt', 2),
  ge('Ge', 2),
  and('And', 2),
  or('Or', 2),
  not('Not', 1),
  min('Min', 2),
  max('Max', 2),
  get('Get', 2),
  count('Count', 1),
  union('Union', 2),
  path('Path', null),
  pathKey('PathKey', 2),
  pathLen('PathLen', 1),
  tuple('Tuple', null),
  tupleGet('TupleGet', 2),
  concat('Concat', 2),
  pow('Pow', 2),
  atom('Atom', null),
  show('Show', 1),
  castInt('CastInt', 1),
  castRat('CastRat', 1),
  castF64('CastF64', 1),
  abs('Abs', 1),
  len('Len', 1),
  lower('Lower', 1),
  upper('Upper', 1),
  trim('Trim', 1),
  sum('Sum', 1);

  final String label;

  /// The number of arguments; null for one that takes any number.
  final int? arity;

  const Prim(this.label, this.arity);

  @override
  String toString() => label;
}

/// A `match` arm's pattern.
sealed class Pattern {
  const Pattern();
}

/// `_`: matches anything.
final class WildP extends Pattern {
  const WildP();
}

/// A name: matches anything and binds it.
final class BindP extends Pattern {
  final String name;

  const BindP(this.name);
}

/// A literal: matches a value equal to it.
final class LitP extends Pattern {
  final Value value;

  const LitP(this.value);
}

/// `#name(p, …)`: an atom of that name with a tuple payload whose values match.
final class AtomP extends Pattern {
  final String name;
  final List<Pattern> args;

  const AtomP(this.name, [this.args = const []]);
}

/// `#name(f: p, …)`: an atom of that name with a struct payload holding these fields.
final class FieldsP extends Pattern {
  final String name;
  final List<(String, Pattern)> fields;

  const FieldsP(this.name, this.fields);
}

/// `(p, …)`: a tuple of that length whose items match.
final class TupleP extends Pattern {
  final List<Pattern> items;

  const TupleP(this.items);
}

/// Any atom.
final class AnyAtomP extends Pattern {
  const AnyAtomP();
}

/// Where a `gen` reads its guard: before each step or after it.
enum GuardPos { before, after }

/// What justifies a `reindex`: the residue check, or a law of the catalog.
sealed class Witness {
  const Witness();
}

final class Residue extends Witness {
  const Residue();
}

final class Catalog extends Witness {
  final String law;

  const Catalog(this.law);
}

/// How strongly a law is established (sec:law_catalog).
enum Grade {
  axiom,
  checkedExhaustive,
  proved,
  bounded,
  obligated,
  assumed;

  bool get isProofGrade => index <= proved.index;
}

/// The laws a construct relies on, each with its grade.
typedef Evidence = Map<String, Grade>;

/// What a `fix` iterates to: the least fixpoint of a lattice under `join`, or the entries a
/// definedness recursion defines.
sealed class FixKind {
  const FixKind();
}

final class Lattice extends FixKind {
  final Term join;

  const Lattice(this.join);
}

final class Definedness extends FixKind {
  const Definedness();
}

/// A kernel term.
sealed class Term {
  const Term();
}

final class Lit extends Term {
  final Value value;

  const Lit(this.value);
}

final class Var extends Term {
  final String name;

  const Var(this.name);
}

final class Lam extends Term {
  final List<String> params;
  final Term body;

  const Lam(this.params, this.body);
}

final class App extends Term {
  final Term f;
  final List<Term> args;

  const App(this.f, this.args);
}

final class PrimApp extends Term {
  final Prim prim;
  final List<Term> args;

  const PrimApp(this.prim, this.args);
}

/// A primitive as a function value, such as the `+` a fold takes.
final class PrimFn extends Term {
  final Prim prim;

  const PrimFn(this.prim);
}

final class Let extends Term {
  final String name;
  final Term value, body;

  const Let(this.name, this.value, this.body);
}

final class If extends Term {
  final Term cond, then, orElse;

  const If(this.cond, this.then, this.orElse);
}

final class Match extends Term {
  final Term scrutinee;
  final List<(Pattern, Term)> arms;

  const Match(this.scrutinee, this.arms);
}

/// `fam var in domain => body`: the family with the domain's keys and the body's values.
final class Fam extends Term {
  final Term domain;
  final String variable;
  final Term body;

  const Fam(this.domain, this.variable, this.body);
}

final class Reindex extends Term {
  final Term family, kf, vf;
  final Witness witness;

  const Reindex(this.family, this.kf, this.vf, this.witness);
}

final class Discard extends Term {
  final Term family, sel;

  const Discard(this.family, this.sel);
}

final class Fold extends Term {
  final Term family, op;
  final Term? identity;
  final int depth;
  final Evidence ev;

  const Fold(this.family, this.op, this.identity, this.depth, this.ev);
}

final class Fix extends Term {
  final Term init, step;
  final String self, key;
  final FixKind kind;
  final Evidence ev;

  const Fix(this.init, this.step, this.self, this.key, this.kind, this.ev);
}

final class Gen extends Term {
  final Term init, step, guard;
  final GuardPos pos;

  const Gen(this.init, this.step, this.guard, this.pos);
}

final class Read extends Term {
  final String port;

  const Read(this.port);
}

final class Push extends Term {
  final String port;
  final Term value;

  const Push(this.port, this.value);
}

/// The value of a Dart `int`, `bool`, `double`, `String` or [Value].
Value valueOf(Object v) => switch (v) {
  Value v => v,
  int n => Int(n),
  bool b => Bool(b),
  double x => Float(x),
  String s => Str(s),
  _ => throw ArgumentError('not a value: $v'),
};

Term var_(String name) => Var(name);

Term lit(Object v) => Lit(valueOf(v));

Term lam(List<String> params, Term body) => Lam(params, body);

Term app(Term f, List<Term> args) => App(f, args);

Term prim(Prim p, List<Term> args) => PrimApp(p, args);

Term let_(String name, Term e, Term body) => Let(name, e, body);

Term if_(Term c, Term a, Term b) => If(c, a, b);
