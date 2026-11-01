/// Cells and the premises their elements rest on.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/store.dart';

/// The fact at node `n` with no keypath.
FactAddress addr(int n) => FactAddress.of(NodeAddress.of([0, n]));

Premises because(int n) => Premises.one(Premise.constraint(addr(n)));

void main() {
  test('a meet adds its premises only when it narrows', () {
    // `let i: int[0..<n] = ...`, then a test `i < 10`, then a test `i < n + 5`.
    final n = Affine.sym('n');
    final e = Entry(Bounds.top);
    expect(e.meet(Bounds.range(const Affine.constant(0), n.plus(-1)), because(1)), isTrue);
    expect(e.meet(Bounds.range(null, const Affine.constant(9)), because(2)), isTrue);
    // `n + 4` with the same terms is looser than `n - 1`, so the test changes nothing and the
    // element does not rest on it.
    expect(e.meet(Bounds.range(null, n.plus(4)), because(3)), isFalse);
    expect(e.element.toString(), '[0..=min(9, n - 1)]');
    expect(e.premises.set, {Premise.constraint(addr(1)), Premise.constraint(addr(2))});
    expect(e.proofGrade, isTrue);
  });

  test('a join rests on both sides', () {
    // `if c { x = 1 } else { x = y }` with `y: int[3..=5]` declared at node 4.
    final then = Entry(Bounds.ints(IntervalSet.single(1)));
    final other = Entry(Bounds.top)..meet(Bounds.ints(IntervalSet.of(3, 5)), because(4));
    expect(then.join(other), isTrue);
    expect(then.element.toString(), '[1..=1, 3..=5]');
    expect(then.premises, because(4));
    // Joining a side already below adds its premises, and changes nothing else.
    final lit = Entry(Bounds.ints(IntervalSet.single(3)), because(5));
    expect(then.join(lit), isFalse);
    expect(then.premises.contains(Premise.constraint(addr(5))), isTrue);
  });

  test('a widening past the join is a premise and not proof-grade', () {
    final head = addr(7);
    // A counter at a loop head: 0, then 0 or 1, then widened.
    final e = Entry(Bounds.ints(IntervalSet.single(0)));
    final step = Entry(Bounds.ints(IntervalSet.of(0, 1)));
    expect(e.widen(step, head, Landmarks.none()), isTrue);
    expect(e.element.toString(), '[0..]');
    expect(e.premises.set, {Premise.widened(head)});
    expect(e.proofGrade, isFalse);
    // A widening that gives only the join, as in a lattice of finite height, adds nothing.
    final f = Entry(FloatClass([Kind.finite], Width.f32));
    final g = Entry(FloatClass([Kind.nan], Width.f64));
    expect(f.widen(g, head, Landmarks.none()), isTrue);
    expect(f.proofGrade, isTrue);
    // A finite set keeps a new member that the program writes, and gives the top for one it
    // does not.
    final b = Entry(FiniteSet.of([Str('b')]));
    final s = Entry(FiniteSet.of([Str('a')]));
    expect(s.widen(b, head, Landmarks.of([], [Str('b')])), isTrue);
    expect(s.element, FiniteSet.of([Str('a'), Str('b')]));
    expect(s.proofGrade, isTrue);
    final t = Entry(FiniteSet.of([Str('a')]));
    expect(t.widen(b, head, Landmarks.none()), isTrue);
    expect(t.element, const FiniteSet<Value>.top());
    expect(t.proofGrade, isFalse);
  });

  test('a literal fills the domains that read its kind', () {
    expect(Cell.literal(const Int(6)).toString(), 'ints [6..=6]\ncongruence 6\nfinite {6}\n');
    expect(Cell.literal(Str('héllo')).toString(), 'finite {"héllo"}\nlength [5..=5]\n');
    final x = Cell.literal(Float(0.5));
    expect(x.toString(), 'finite {0.5}\nfloat f16{finite}\n');
    expect(x.premises.isEmpty, isTrue);
    expect(Cell.top().toString(), '');
  });

  test('a length is never negative', () {
    // `s::len <= n` for a string `s`: the length is `[0..=n]`, and a length below zero leaves
    // the cell empty.
    final c = Cell.top();
    expect(c.length.meet(Bounds.range(null, Affine.sym('n')), because(1)), isTrue);
    expect(c.length.element.toString(), '[0..=n]');
    expect(Cell.top().length.element.toString(), '[0..]');
    final d = Cell.top()..length.meet(Bounds.ints(IntervalSet.of(-3, -1)), because(2));
    expect(d.length.element, Bounds.bottom);
    // A widening whose lower end moves goes to minus infinity, and the cell keeps the length
    // at zero or more.
    final e = Cell.literal(Str('abc'));
    expect(e.widen(Cell.literal(Str('ab')), addr(8), Landmarks.none()), isTrue);
    expect(e.length.element.toString(), '[0..=3]');
  });

  test('a cell joins and widens entry by entry', () {
    final head = addr(9);
    final store = Store();
    final a = addr(1);
    expect(store.cell(a), Cell.top());
    store[a] = Cell.literal(const Int(0));
    expect(store.cellMut(a).join(Cell.literal(const Int(1))), isTrue);
    expect(store.cell(a).toString(), 'ints [0..=1]\nfinite {0, 1}\n');
    final two = Cell.literal(const Int(2));
    // The program writes 1 (so 0, 1 and 2 are landmarks) and 3: the interval stops at 2, and
    // the finite set keeps 2.
    final b = store.cell(a);
    expect(b.widen(two, head, Landmarks.of([1])), isTrue);
    expect(b.toString(), 'ints [0..=2]\nfinite {0, 1, 2}\n');
    expect(b.ints.proofGrade && b.finite.proofGrade, isTrue);
    // With no landmarks, the interval goes to infinity and the finite set to the top.
    expect(store.cellMut(a).widen(two, head, Landmarks.none()), isTrue);
    final c = store.cell(a);
    expect(c.toString(), 'ints [0..]\n');
    expect(c.ints.proofGrade, isFalse);
    expect(c.finite.proofGrade, isFalse);
    expect(c.premises.set, {Premise.widened(head)});
    expect(store.cells.length, 1);
  });
}
