use super::*;
use crate::seed::Rng;
use crate::types::{AtomPart, Morphism, Node, Row, Type};
use crate::value::Value;

/// The tuple type of one integer, an atom independent of the others.
pub(super) fn atom(i: u64) -> Row {
    Row::new(vec![Type::lit(&Value::Int(i as i64)).unwrap()])
}

fn random(rng: &mut Rng, depth: u32) -> Part<Row> {
    let pick = rng.next_u64();
    if depth == 0 || pick.is_multiple_of(5) {
        return Part::literal(atom(pick % 6));
    }
    let (a, b) = (random(rng, depth - 1), random(rng, depth - 1));
    match pick % 3 {
        0 => a.zip(&b, Op::Or),
        1 => a.zip(&b, Op::And),
        _ => a.not(),
    }
}

/// The part built from `random`'s connectives as expressions, so that every form is met;
/// an operand is at times one built before, kept in `pool`, so that expressions are shared.
fn random_expr(rng: &mut Rng, depth: u32, pool: &mut Vec<Part<Row>>) -> Part<Row> {
    let pick = rng.next_u64();
    if !pool.is_empty() && pick % 7 == 3 {
        return pool[(pick / 7) as usize % pool.len()].clone();
    }
    if depth == 0 || pick.is_multiple_of(5) {
        return random(rng, 2);
    }
    let (a, b) = (
        random_expr(rng, depth - 1, pool),
        random_expr(rng, depth - 1, pool),
    );
    let p = match pick % 3 {
        0 => Part::connect(Op::Or, a, b),
        1 => Part::connect(Op::And, a, b),
        _ => Part::not_expr(a),
    };
    pool.push(p.clone());
    p
}

#[test]
fn three_valued_operations_keep_the_assignments() {
    // Each set of the six atoms is one assignment, and a partial assignment fixes the
    // atoms of `known` to their membership in `fixed`. A three-valued value is the value
    // of every assignment that agrees with it; restricting keeps the value of every
    // assignment agreeing with what it fixes; settling keeps every assignment in the
    // part, and makes it empty only when the part is; an atom forced taken is in every assignment
    // in the part, and one forced refused in none.
    let (mut rng, _) = Rng::fresh("three_valued_operations_keep_the_assignments");
    let mut met = [0usize; 4];
    for _ in 0..600 {
        let p = if rng.coin() {
            random(&mut rng, 6)
        } else {
            random_expr(&mut rng, 5, &mut Vec::new())
        };
        let (known, fixed) = (rng.below(64) as u32, rng.below(64) as u32);
        for (n, k) in met.iter_mut().zip(three_valued_holds(&p, known, fixed)) {
            *n += usize::from(k);
        }
    }
    eprintln!("expressions, decided, forced, settled to empty: {met:?}");
    // Each kind on a part built to give it, whatever the draws met (PROOF-test-count-thresholds;
    // until 2026-11-15 the test asserted that 600 drawn parts gave more than 250 expressions,
    // 200 decided, 400 forced atoms and 5 settled to empty). The literal of atom 0 with atom 0
    // known and taken: its value is decided, true, and atom 0 is in its every assignment, so
    // forced taken. `e & !e` with `e = a0 | a1` one shared expression: no assignment is in it,
    // and `e` used twice is pinned by settling (with `e` false the meet is false by three-valued
    // logic, so `e` becomes true, and `true & !true` is false), so it settles to empty.
    let lit = Part::literal(atom(0));
    assert_eq!(three_valued_holds(&lit, 1, 1), [false, true, true, false]);
    let e = Part::connect(Op::Or, Part::literal(atom(0)), Part::literal(atom(1)));
    let none = Part::connect(Op::And, e.clone(), Part::not_expr(e));
    let [expr, _, _, settled] = three_valued_holds(&none, 0, 0);
    assert!(expr && settled, "{none:?}");
}

/// Checks [`three_valued_operations_keep_the_assignments`]'s properties on `p` with the atoms
/// of `known` fixed to their membership in `fixed`. Gives whether `p` is an expression,
/// whether its value is decided by what is fixed, whether it forces some atom, and whether it
/// holds no assignment and settles to the empty leaf.
fn three_valued_holds(p: &Part<Row>, known: u32, fixed: u32) -> [bool; 4] {
    let mut met = [matches!(p, Part::Expr(_)), false, false, false];
    {
        let holds = |set: u32| move |t: &Row| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i));
        assert!(p.settle() == p.settle_by_scans(), "settling changed");
        assert!(
            p.settle() == p.settle_by(Pins::Carried),
            "the cut changed the pins"
        );
        let inside: Vec<u32> = (0..64).filter(|&set| p.eval(&holds(set))).collect();
        let fix = |t: &Row| {
            (0..6)
                .find(|&i| *t == atom(i) && known & (1 << i) != 0)
                .map(|i| fixed & (1 << i) != 0)
        };
        let agree = |set: u32| (set ^ fixed) & known == 0;
        if let Some(v) = p.eval3(&fix) {
            met[1] = true;
            assert!(
                (0..64)
                    .filter(|&s| agree(s))
                    .all(|s| p.eval(&holds(s)) == v),
                "{p:?}"
            );
        }
        let r = p.restrict(&fix);
        let t = p.settle();
        met[3] = inside.is_empty() && t.is_leaf() == Some(false);
        for set in 0..64 {
            if agree(set) {
                assert_eq!(r.eval(&holds(set)), p.eval(&holds(set)), "{p:?} at {set:b}");
            }
            assert!(
                !p.eval(&holds(set)) || t.eval(&holds(set)),
                "{p:?} at {set:b}"
            );
        }
        let (taken, refused) = p.forced();
        met[2] = !taken.is_empty() || !refused.is_empty();
        // The one pass finds what trying each atom alone by three-valued logic finds.
        let (mut on, mut off) = (Vec::new(), Vec::new());
        for a in p.distinct_atoms() {
            if p.eval3(&|x| (*x == a).then_some(false)) == Some(false) {
                on.push(a);
            } else if p.eval3(&|x| (*x == a).then_some(true)) == Some(false) {
                off.push(a);
            }
        }
        assert_eq!((&taken, &refused), (&on, &off), "{p:?}");
        for a in &taken {
            let i = (0..6).find(|&i| *a == atom(i)).unwrap();
            assert!(inside.iter().all(|s| s & (1 << i) != 0), "{p:?} takes {i}");
        }
        for a in &refused {
            let i = (0..6).find(|&i| *a == atom(i)).unwrap();
            assert!(
                inside.iter().all(|s| s & (1 << i) == 0),
                "{p:?} refuses {i}"
            );
        }
        // On a diagram every atom in all assignments, or in none, is found.
        if matches!(p, Part::Bdd(_)) && !inside.is_empty() {
            for i in 0..6 {
                let at = |set: &u32| set & (1 << i) != 0;
                assert_eq!(
                    taken.contains(&atom(i)),
                    inside.iter().all(at),
                    "{p:?} at {i}"
                );
                assert_eq!(
                    refused.contains(&atom(i)),
                    !inside.iter().any(at),
                    "{p:?} at {i}"
                );
            }
        }
    }
    met
}
#[test]
fn two_exclusive_ors_on_disjoint_atoms_meet_in_an_expression() {
    // With the atoms in the order `a < b < c < d`, the diagrams of `a xor c` and `b xor d`
    // have three nodes each and no atom in common, and their meet has nine: disjoint atoms
    // bound a meet by the sum of the sizes only when one diagram's atoms all come before
    // the other's (cross-review XR3, R3_CODEX.md Q1). An exclusive or is no decision list,
    // so `Part::zip` keeps each, and their meet, as expressions.
    let oxor =
        |p: &Old, q: &Old| (p.apply(&q.not(), Op::And)).apply(&p.not().apply(q, Op::And), Op::Or);
    let (a, b) = (
        oxor(&Old::literal(0), &Old::literal(2)),
        oxor(&Old::literal(1), &Old::literal(3)),
    );
    assert_eq!(
        (a.nodes(), b.nodes(), a.apply(&b, Op::And).nodes()),
        (3, 3, 9)
    );
    let lit = |i: u64| Part::literal(atom(i));
    let xor = |p: Part<Row>, q: Part<Row>| {
        p.zip(&q.not(), Op::And)
            .zip(&p.not().zip(&q, Op::And), Op::Or)
    };
    let (pa, pb) = (xor(lit(0), lit(2)), xor(lit(1), lit(3)));
    let kept = pa.zip(&pb, Op::And);
    assert!(matches!(kept, Part::Expr(_)), "{kept:?}");
    for set in 0..16u32 {
        let holds = |t: &Row| (0..4).any(|i| set >> i & 1 == 1 && *t == atom(i));
        let bit = |i: u32| set >> i & 1 == 1;
        assert_eq!(kept.eval(&holds), (bit(0) != bit(2)) && (bit(1) != bit(3)));
    }
}

/// A decision list's blocks with each block's literals sorted, and its default.
type Blocks = (Vec<(bool, Vec<(Row, bool)>)>, bool);

fn sorted(l: super::list::List<Row>) -> Blocks {
    let blocks = l
        .blocks
        .into_iter()
        .map(|(v, mut lits)| {
            lits.sort();
            (v, lits)
        })
        .collect();
    (blocks, l.tail)
}

/// The one form of the decision list of `f`, a function of the atoms `atom(0..6)` given
/// by its value on each set of them, found from the values alone: the literals under which
/// the function is constant, a block, then those once the block's literals are false, and
/// so on (module `list`). `None` when the function is no decision list.
fn list_of_values(f: impl Fn(u32) -> bool) -> Option<Blocks> {
    // The value when the atoms of `fixed` are fixed to theirs, if one.
    let constant = |fixed: &[Option<bool>; 6]| {
        let mut seen = [false; 2];
        for set in 0..64u32 {
            let agrees = (0..6).all(|i| fixed[i].is_none_or(|b| b == (set >> i & 1 == 1)));
            if agrees {
                seen[usize::from(f(set))] = true;
            }
        }
        match seen {
            [true, false] => Some(false),
            [false, true] => Some(true),
            _ => None,
        }
    };
    let mut fixed = [None; 6];
    let mut blocks = Vec::new();
    loop {
        if let Some(v) = constant(&fixed) {
            return Some((blocks, v));
        }
        let mut lits = Vec::new();
        for i in 0..6 {
            for taken in [true, false] {
                if fixed[i].is_some() {
                    continue;
                }
                let mut f = fixed;
                f[i] = Some(taken);
                if let Some(c) = constant(&f) {
                    lits.push((i, taken, c));
                }
            }
        }
        if lits.is_empty() {
            return None;
        }
        // Literals of both values are one atom's two: the list of one literal, `true`.
        let v = lits.iter().any(|l| l.2);
        let mut block: Vec<(Row, bool)> = Vec::new();
        for &(i, taken, c) in &lits {
            if c == v {
                fixed[i] = Some(!taken);
                block.push((atom(i as u64), taken));
            }
        }
        block.sort();
        blocks.push((v, block));
    }
}

/// The construction the lists replaced, kept to check them against: a reduced ordered
/// diagram on the atoms `atom(0..6)` in the order of their indices, two diagrams joined
/// by `apply`, which builds `O(n²)` nodes for a decision list of `n` literals in the worst
/// atom order. Small sizes only: the walks recurse and share no node.
mod old {
    use super::Op;
    use std::rc::Rc;

    #[derive(Clone, PartialEq, Eq, Hash, Debug)]
    pub(super) enum Old {
        Leaf(bool),
        Node(Rc<(usize, Old, Old)>),
    }

    impl Old {
        pub(super) fn node(i: usize, hi: Old, lo: Old) -> Old {
            if hi == lo {
                hi
            } else {
                Old::Node(Rc::new((i, hi, lo)))
            }
        }

        pub(super) fn literal(i: usize) -> Old {
            Old::node(i, Old::Leaf(true), Old::Leaf(false))
        }

        fn top(&self) -> usize {
            match self {
                Old::Leaf(_) => usize::MAX,
                Old::Node(n) => n.0,
            }
        }

        /// The diagram with atom `i` fixed to `true`, and to `false`; `i` is at or above
        /// the root's atom.
        fn cofactors(&self, i: usize) -> (Old, Old) {
            match self {
                Old::Node(n) if n.0 == i => (n.1.clone(), n.2.clone()),
                _ => (self.clone(), self.clone()),
            }
        }

        pub(super) fn apply(&self, other: &Old, op: Op) -> Old {
            if let (Old::Leaf(a), Old::Leaf(b)) = (self, other) {
                return Old::Leaf(match op {
                    Op::Or => a | b,
                    Op::And => a & b,
                });
            }
            let i = self.top().min(other.top());
            let ((a1, a0), (b1, b0)) = (self.cofactors(i), other.cofactors(i));
            Old::node(i, a1.apply(&b1, op), a0.apply(&b0, op))
        }

        pub(super) fn not(&self) -> Old {
            match self {
                Old::Leaf(b) => Old::Leaf(!b),
                Old::Node(n) => Old::node(n.0, n.1.not(), n.2.not()),
            }
        }

        pub(super) fn restrict(&self, fixed: &[Option<bool>; 6]) -> Old {
            match self {
                Old::Leaf(_) => self.clone(),
                Old::Node(n) => match fixed[n.0] {
                    Some(true) => n.1.restrict(fixed),
                    Some(false) => n.2.restrict(fixed),
                    None => Old::node(n.0, n.1.restrict(fixed), n.2.restrict(fixed)),
                },
            }
        }

        /// The value on the set of atoms whose indices are the bits of `set`.
        pub(super) fn eval(&self, set: u32) -> bool {
            match self {
                Old::Leaf(b) => *b,
                Old::Node(n) if set >> n.0 & 1 == 1 => n.1.eval(set),
                Old::Node(n) => n.2.eval(set),
            }
        }

        /// The number of distinct nodes.
        pub(super) fn nodes(&self) -> usize {
            let mut seen = std::collections::HashSet::new();
            zed_graph::reach(
                [self],
                |&d| matches!(d, Old::Node(_)) && seen.insert(d.clone()),
                |&d| match d {
                    Old::Node(n) => Some([&n.1, &n.2]).into_iter().flatten(),
                    Old::Leaf(_) => None.into_iter().flatten(),
                },
            );
            seen.len()
        }
    }
}
use old::Old;

#[test]
fn lists_agree_with_the_diagrams_apply_built() {
    // Random lists built by the connectives on lists (complement, a chain joined, a
    // restriction) and, beside each, the diagram the old construction builds. They agree
    // on every set of atoms; the list is the one form of its function, found from its
    // values; two lists of one function are one list, however they were built; and the
    // three-valued value, the forced atoms and the first node each agree with the values.
    let mut pool: Vec<(Bdd<Row>, Old)> = (0..6)
        .map(|i| (Bdd::literal(atom(i as u64)), Old::literal(i)))
        .chain([false, true].map(|b| (Bdd::Leaf(b), Old::Leaf(b))))
        .collect();
    // The id of the one list of each function, by its values.
    let mut ids: HashMap<u64, u64> = HashMap::new();
    let (mut rng, _) = Rng::fresh("lists_agree_with_the_diagrams_apply_built");
    let mut next = || rng.next_u64();
    let (mut joined, mut found_again) = (0usize, 0usize);
    for _ in 0..4_000 {
        let r = next() as usize;
        let (a, x) = pool[r % pool.len()].clone();
        let (b, y) = pool[next() as usize % pool.len()].clone();
        let op = if (r / pool.len()).is_multiple_of(2) {
            Op::Or
        } else {
            Op::And
        };
        let made = match r / pool.len() / 2 % 4 {
            0 => (a.not(), x.not()),
            3 => {
                let mut fixed = [None; 6];
                for f in &mut fixed {
                    *f = [None, None, Some(false), Some(true)][next() as usize % 4];
                }
                let fix = |t: &Row| {
                    (0..6)
                        .find(|&i| *t == atom(i as u64))
                        .and_then(|i| fixed[i])
                };
                (
                    a.restrict(&fix, &mut Default::default()),
                    x.restrict(&fixed),
                )
            }
            _ => match a.zip_chain(&b, op) {
                Some(z) => {
                    joined += 1;
                    (z, x.apply(&y, op))
                }
                None => continue,
            },
        };
        let (z, d) = made;
        found_again += usize::from(list_agrees(&z, &d, &mut ids, &pool, &mut next));
        pool.push((z, d));
    }
    eprintln!("{joined} joined, {found_again} found again");
    // Both kinds on lists built to give them, whatever the draws met (PROOF-test-count-
    // thresholds; until 2026-11-15 the test asserted that 4,000 rounds joined more than 1000
    // chains and found more than 2500 lists again). A literal is a chain of one literal under
    // either connective, so `zip_chain` joins `a0` and `a1` under `|` (`Bdd::zip_chain`: `None`
    // only when neither operand is a chain). Joined in the other order while the first lives,
    // the same function is the same list, found again by its values in `ids`.
    let (a0, a1) = (Bdd::literal(atom(0)), Bdd::literal(atom(1)));
    let (x0, x1) = (Old::literal(0), Old::literal(1));
    let first = (a0.zip_chain(&a1, Op::Or)).expect("two literals joined");
    let mut ids: HashMap<u64, u64> = HashMap::new();
    list_agrees(&first, &x0.apply(&x1, Op::Or), &mut ids, &[], &mut next);
    let again = (a1.zip_chain(&a0, Op::Or)).expect("two literals joined");
    let live = [(first, x0.apply(&x1, Op::Or))];
    assert!(list_agrees(
        &again,
        &x1.apply(&x0, Op::Or),
        &mut ids,
        &live,
        &mut next
    ));
}

/// Checks [`lists_agree_with_the_diagrams_apply_built`]'s properties on the list `z` beside the
/// diagram `d` the old construction built, drawing the partial assignments from `next`. `ids`
/// holds the id of the list of each function met, by its values; gives whether `z` is the list
/// of a function met before, whose list `pool` still holds.
fn list_agrees(
    z: &Bdd<Row>,
    d: &Old,
    ids: &mut HashMap<u64, u64>,
    pool: &[(Bdd<Row>, Old)],
    next: &mut impl FnMut() -> u64,
) -> bool {
    let holds = |set: u32| move |t: &Row| (0..6).any(|i| set >> i & 1 == 1 && *t == atom(i));
    {
        let values: u64 = (0..64).filter(|&s| d.eval(s)).fold(0, |m, s| m | 1 << s);
        for set in 0..64u32 {
            assert_eq!(z.eval(holds(set)), d.eval(set), "{z:?} at {set:b}");
        }
        let id = *ids.entry(values).or_insert_with(|| z.id());
        let found_again = id == z.id() && pool.iter().any(|(p, _)| p.id() == id);
        assert_eq!(id, z.id(), "two lists of one function: {z:?}");
        assert_eq!(
            Some(sorted(z.list())),
            list_of_values(|s| d.eval(s)),
            "the list of {z:?}"
        );
        // Three-valued: known when every set agreeing with what is known has one value.
        for _ in 0..8 {
            let (known, fixed) = (next() as u32 % 64, next() as u32 % 64);
            let fix = |t: &Row| {
                (0..6)
                    .find(|&i| *t == atom(i as u64) && known >> i & 1 == 1)
                    .map(|i| fixed >> i & 1 == 1)
            };
            let agreeing: Vec<bool> = (0..64u32)
                .filter(|s| (s ^ fixed) & known == 0)
                .map(|s| d.eval(s))
                .collect();
            let expected = (agreeing.iter().all(|&v| v == agreeing[0])).then_some(agreeing[0]);
            assert_eq!(z.eval3(&fix), expected, "{z:?}");
        }
        // Forced: the atoms in every set of value `true`, and those in none; none when
        // there is no such set, as the diagram's walk found.
        let inside: Vec<u32> = (0..64).filter(|&s| d.eval(s)).collect();
        let (mut taken, mut refused) = (Vec::new(), Vec::new());
        if !inside.is_empty() {
            for i in 0..6 {
                if inside.iter().all(|s| s >> i & 1 == 1) {
                    taken.push(atom(i as u64));
                } else if inside.iter().all(|s| s >> i & 1 == 0) {
                    refused.push(atom(i as u64));
                }
            }
        }
        taken.sort();
        refused.sort();
        assert_eq!(z.forced(), (taken.clone(), refused.clone()), "{z:?}");
        let (mut t, mut f) = Part::Bdd(z.clone()).forced();
        t.sort();
        f.sort();
        assert_eq!((t, f), (taken, refused), "{z:?}");
        // The first node: the list is its `hi` where its atom holds, its `lo` elsewhere.
        if let Ok((_, a, hi, lo)) = z.branch() {
            for set in 0..64u32 {
                let h = holds(set);
                let by_node = if h(a) { hi.eval(h) } else { lo.eval(h) };
                assert_eq!(by_node, z.eval(h), "{z:?} at {set:b}");
            }
        }
        found_again
    }
}

/// [`random`] beside the diagram [`Old`] builds from the same draws, by its recursive `apply`
/// and `not`.
fn random_beside_old(rng: &mut Rng, depth: u32) -> (Part<Row>, Old) {
    let pick = rng.next_u64();
    if depth == 0 || pick.is_multiple_of(5) {
        let i = (pick % 6) as usize;
        return (Part::literal(atom(i as u64)), Old::literal(i));
    }
    let (a, x) = random_beside_old(rng, depth - 1);
    let (b, y) = random_beside_old(rng, depth - 1);
    match pick % 3 {
        0 => (a.zip(&b, Op::Or), x.apply(&y, Op::Or)),
        1 => (a.zip(&b, Op::And), x.apply(&y, Op::And)),
        _ => (a.not(), x.not()),
    }
}

/// The parts of [`random_parts_agree_with_the_recursive_diagrams`], made `groups` groups of
/// `rounds` at a time from the seed of `rng`, each group from the six literals: a part is a
/// fresh [`random_beside_old`], or `zip`, `not`, [`Part::connect`] or [`Part::not_expr`] of
/// parts of the group made before it, so that expressions are shared, met again and negated.
/// Each part has, on every set of the atoms, the value of the diagram the recursive `apply` and
/// `not` of [`Old`] build from the same draws; its complement has the opposite values; and it
/// met with its complement is the leaf, as the old `zip` gave it through `same_as_not`.
pub(super) fn random_parts_agree(rng: &mut Rng, groups: usize, rounds: usize) {
    let mut kinds = [0usize; 4];
    for _ in 0..groups {
        let mut pool: Vec<(Part<Row>, Old)> = (0..6)
            .map(|i| (Part::literal(atom(i as u64)), Old::literal(i)))
            .collect();
        for _ in 0..rounds {
            let r = rng.next_u64();
            let (a, x) = pool[rng.below(pool.len())].clone();
            let (b, y) = pool[rng.below(pool.len())].clone();
            let op = if r >> 8 & 1 == 0 { Op::Or } else { Op::And };
            let kind = (r % 4) as usize;
            kinds[kind] += 1;
            let (p, d) = match kind {
                0 => random_beside_old(rng, 5),
                1 => (a.zip(&b, op), x.apply(&y, op)),
                2 => (a.not(), x.not()),
                _ if r >> 9 & 1 == 0 => (Part::connect(op, a, b), x.apply(&y, op)),
                // `Part::not_expr` is called only on an expression (`negate`), never on a leaf:
                // `Not` of a leaf is a constant that is not the leaf, which `Form` excludes.
                _ if a.is_leaf().is_some() => (a.not(), x.not()),
                _ => (Part::not_expr(a), x.not()),
            };
            let got = values(&p);
            let want: Vec<bool> = (0..64u32).map(|set| d.eval(set)).collect();
            assert_eq!(got, want, "{p:?} beside {d:?}");
            let n = p.not();
            let opposite: Vec<bool> = want.iter().map(|v| !v).collect();
            assert_eq!(values(&n), opposite, "the complement {n:?} of {p:?}");
            assert_eq!(p.zip(&n, Op::And), Part::leaf(false), "{p:?} & !{p:?}");
            assert_eq!(p.zip(&n, Op::Or), Part::leaf(true), "{p:?} | !{p:?}");
            pool.push((p, d));
        }
    }
    eprintln!("fresh, zip, not, kept as expressions: {kinds:?}");
}

/// T2-types-rest-4 (a34629bf) moved `Part::not` and `Part::zip` (with `choose`, `choice`,
/// `choice_of`, `same_as_not`) and `Bdd::apply` from recursion to frames on the heap; its
/// probe, not committed, built 3,000 random parts with both and found byte-identical ids,
/// digests, Debug texts and paths (TESTS-T2-types-rest-4-random-vs-recursive, test audit
/// 2026-11-08 row 8). Those cannot be compared now: an id counts parts made on any thread, and
/// the forms of parts have changed since (lists in place of diagrams, exclusive ors in their
/// one form, the `_at_once` shortcuts), so the recursive code of `a34629bf^` would build other
/// forms of the same functions. What the old code fixed and the new must keep is the function:
/// each seeded random part, here 300 in 10 groups of 30, has the values of the diagram the
/// recursive `apply` and `not` of [`Old`] build from the same draws. The probe's 3,000 are
/// `bench::three_thousand_random_parts_agree_with_the_recursive_diagrams`.
#[test]
fn random_parts_agree_with_the_recursive_diagrams() {
    let (mut rng, _) = Rng::fresh("random_parts_agree_with_the_recursive_diagrams");
    random_parts_agree(&mut rng, 10, 30);
}

#[test]
fn list_matches_the_one_form_found_from_its_values() {
    let (mut rng, _) = Rng::fresh("list_matches_the_one_form_found_from_its_values");
    let mut lists = 0;
    for _ in 0..800 {
        let Part::Bdd(b) = random(&mut rng, 6) else {
            continue;
        };
        list_matches(&b);
        lists += 1;
    }
    eprintln!("{lists} lists");
    // Lists built as lists, whatever the draws met (PROOF-test-count-thresholds; until
    // 2026-11-15 the test asserted that 800 draws gave more than 400): each literal, its
    // complement, and the chain `a0 | a1 | a2` with `!a3` met, all `Bdd`s by their types.
    let lits: Vec<Bdd<Row>> = (0..6).map(|i| Bdd::literal(atom(i))).collect();
    for l in &lits {
        list_matches(l);
        list_matches(&l.not());
    }
    let chain = (lits[1..3].iter()).fold(lits[0].clone(), |c, l| {
        c.zip_chain(l, Op::Or).expect("a chain joined")
    });
    list_matches(&chain);
    list_matches(
        &chain
            .zip_chain(&lits[3].not(), Op::And)
            .expect("a chain met"),
    );
}

/// Checks that the list of `b` is the one form found from its values.
fn list_matches(b: &Bdd<Row>) {
    let holds = |set: u32| move |t: &Row| (0..6).any(|i| set >> i & 1 == 1 && *t == atom(i));
    let expected = list_of_values(|s| b.eval(holds(s)));
    assert_eq!(Some(sorted(b.list())), expected, "the list of {b:?}");
}

#[test]
fn list_of_a_literal_and_its_complement() {
    let y = Bdd::literal(atom(1));
    assert_eq!(y.list().blocks, vec![(true, vec![(atom(1), true)])]);
    assert!(!y.list().tail);
    assert_eq!(y.not().list().blocks, vec![(true, vec![(atom(1), false)])]);
    assert!(!y.not().list().tail);
    assert_eq!(y.not().not(), y);
}

/// `p ^ q` as the type operations build it: `p&!q | !p&q`.
pub(super) fn xor_by_or(p: &Part<Row>, q: &Part<Row>) -> Part<Row> {
    let left = p.zip(&q.not(), Op::And);
    left.zip(&p.not().zip(q, Op::And), Op::Or)
}

/// `p ^ q` as `(p|q) & (!p|!q)`.
pub(super) fn xor_by_and(p: &Part<Row>, q: &Part<Row>) -> Part<Row> {
    let left = p.zip(q, Op::Or);
    left.zip(&p.not().zip(&q.not(), Op::Or), Op::And)
}

/// Whether the set `bits` has an odd number of the atoms `0..k`.
fn odd(bits: u32, k: u32) -> bool {
    (bits & ((1 << k) - 1)).count_ones() % 2 == 1
}

/// `(a ^ b) & w | (a ^ b) & !w`, each meet built with `a ^ b` spread over `a` and `!a`, is
/// merged as a choice on `w`, whose branches meet to `a&!b` and `!a&b`: the exclusive or of
/// `a` and `b` in its one form, not a union of the two meets (cross-review of
/// PERF-xor-shape-free, Gemini F1). And a branch that meets to `false` leaves the other.
#[test]
fn a_choice_whose_branches_are_the_halves_of_an_exclusive_or_is_that_exclusive_or() {
    let [a, b, c, d] = [0, 1, 2, 3].map(|i| Part::literal(atom(i)));
    let w = xor_by_or(&c, &d);
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let some = or(&a.not(), &b.not());
    let any = or(&a, &b);
    let half = |w: &Part<Row>| or(&and(&a, &and(&some, w)), &and(&a.not(), &and(&any, w)));
    let merged = or(&half(&w), &half(&w.not()));
    let x = xor_by_or(&a, &b);
    assert!(x.xor_tag().is_some());
    assert_eq!(
        merged.id(),
        x.id(),
        "{merged:?} is not the exclusive or {x:?}"
    );
    // `a&!a&w | !a&b&w`, and the same under `!w`: the union of the second meets, `!a&b`.
    let half = |w: &Part<Row>| or(&and(&a, &and(&a.not(), w)), &and(&a.not(), &and(&b, w)));
    let merged = or(&half(&w), &half(&w.not()));
    assert_eq!(merged.id(), and(&a.not(), &b).id(), "{merged:?}");
}

/// A choice whose meets are lists that `zip` joins as lists is that list, not a union kept as an
/// expression: `a&(a|b) | !a&b` is `a|b` (cross-review of PERF-xor-shape-free, round 2, Sol
/// X2-F4). And a choice with one branch `true`, `c | !c&y`, is `c|y` when `!c&y` is a list (Opus
/// N1); when it is not, plan row CANON-choose-true-branch.
#[test]
fn a_choice_whose_meets_are_lists_is_their_list() {
    let [a, b, c, d] = [0, 1, 2, 3].map(|i| Part::literal(atom(i)));
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let any = or(&a, &b);
    let half = |w: &Part<Row>| or(&and(&a, &and(&any, w)), &and(&a.not(), &and(&b, w)));
    let merged = or(&half(&c), &half(&c.not()));
    assert_eq!(merged.id(), any.id(), "{merged:?} is not the list {any:?}");
    // `c?a:b | c?!a:d`: the branches join to `true` and `b|d`.
    let pick = |c: &Part<Row>, x: &Part<Row>, y: &Part<Row>| or(&and(c, x), &and(&c.not(), y));
    let merged = or(&pick(&c, &a, &b), &pick(&c, &a.not(), &d));
    let direct = or(&c, &or(&b, &d));
    assert_eq!(
        merged.id(),
        direct.id(),
        "{merged:?} is not the list {direct:?}"
    );
}

#[test]
fn exclusive_ors_built_in_any_order_are_one_node() {
    let lits: Vec<Part<Row>> = (0..6).map(|i| Part::literal(atom(i))).collect();
    let fold = |order: &[usize], by: fn(&Part<Row>, &Part<Row>) -> Part<Row>| {
        (order.iter()).fold(Part::leaf(false), |f, &i| by(&f, &lits[i]))
    };
    let holds = |bits: u32| move |a: &Row| (0..6).any(|i| bits >> i & 1 == 1 && *a == atom(i));
    let forward = fold(&[0, 1, 2, 3, 4, 5], xor_by_or);
    assert!(forward.xor_tag().is_some(), "{forward:?}");
    for bits in 0..64 {
        assert_eq!(forward.eval(&holds(bits)), odd(bits, 6), "{bits:b}");
    }
    for order in [[5, 4, 3, 2, 1, 0], [2, 0, 5, 1, 3, 4], [3, 5, 1, 0, 4, 2]] {
        assert_eq!(fold(&order, xor_by_or).id(), forward.id(), "{order:?}");
        assert_eq!(fold(&order, xor_by_and).id(), forward.id(), "{order:?}");
    }
    // Two halves joined, and a literal's complement taken in.
    let halves = xor_by_or(&fold(&[0, 2, 4], xor_by_or), &fold(&[5, 3, 1], xor_by_and));
    assert_eq!(halves.id(), forward.id());
    let flipped = (1..6).fold(lits[0].not(), |f, i| xor_by_or(&f, &lits[i]));
    assert_eq!(flipped.id(), forward.not().id());
    for bits in 0..64 {
        assert_eq!(flipped.eval(&holds(bits)), !odd(bits, 6), "{bits:b}");
    }
    // An atom taken twice leaves; all taken twice leave nothing.
    let twice = xor_by_or(&forward, &lits[3]);
    assert_eq!(twice.id(), fold(&[0, 1, 2, 4, 5], xor_by_or).id());
    assert_eq!(xor_by_and(&forward, &forward.not()).is_leaf(), Some(true));
    // The choice `c&x | !c&!x`, `!(c ^ x)`.
    let (c, x) = (fold(&[0, 1], xor_by_or), fold(&[2, 3, 4, 5], xor_by_or));
    let choice = xor::xor_choice(&c, &x, &x.not()).expect("an exclusive or of two");
    assert_eq!(choice.id(), forward.not().id());
    // Restricted to one atom's value, an exclusive or is the one of the others.
    let fixed = forward.restrict(&|a: &Row| (*a == atom(2)).then_some(true));
    assert_eq!(fixed.id(), fold(&[0, 1, 3, 4, 5], xor_by_or).not().id());
}

/// Two choices on one condition `c`, `c?x:(!x&e)` and `c?x:(!x&!e)`, neither an exclusive or,
/// join branch by branch (`zipped`) to `c?x:!x`, which `choose` takes to the exclusive or
/// `!(c ^ x)` in its one form (`xor::xor_choice`) before making a node of it. Built directly,
/// `c&x | !c&!x` is found as an exclusive or before `choose`, so this is the way there
/// (TEST-kernel-unreached-paths-4).
#[test]
fn choices_whose_branches_join_to_opposite_exclusive_ors_are_one() {
    let lits: Vec<Part<Row>> = (0..4).map(|i| Part::literal(atom(i))).collect();
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let pick = |c: &Part<Row>, x: &Part<Row>, y: &Part<Row>| or(&and(c, x), &and(&c.not(), y));
    let (c, e) = (&lits[0], &lits[3]);
    let x = xor_by_or(&lits[1], &lits[2]);
    let left = pick(c, &x, &and(&x.not(), e));
    let right = pick(c, &x, &and(&x.not(), &e.not()));
    assert!(left.xor_tag().is_none() && right.xor_tag().is_none());
    let joined = or(&left, &right);
    let all = xor_by_or(c, &x);
    assert_eq!(joined.id(), all.not().id());
}

/// The values of `p` on the 64 sets of the atoms 0 to 5.
fn values(p: &Part<Row>) -> Vec<bool> {
    (0..64u32)
        .map(|set| p.eval(&|t: &Row| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i))))
        .collect()
}

/// `k&x | !k&y` with `k`, `x` and `y` choices on one condition `c`: `Connect::choose` meets `k`
/// with `x` and `!k` with `y`, each meet a choice on `c` again, and joins the two by the rule for
/// two choices on one condition. Here the union of the branches on each side of `c` is `l1`, so
/// the choice is `l1`. With `k = c&!l2 | !c&l3` the two meets choose on `c` as kept (the arm
/// `c == d` of `choose`, not reached by any other test, TEST-kernel-unreached-paths-4); with
/// `k = c&l2 | !c&l3` one meet chooses on `c` and the other on `!c` (the arm of opposite
/// conditions).
#[test]
fn a_choice_whose_meets_choose_on_one_condition_with_equal_unions_is_that_union() {
    let l: Vec<Part<Row>> = (0..4).map(|i| Part::literal(atom(i))).collect();
    let pick = |c: &Part<Row>, x: &Part<Row>, y: &Part<Row>| {
        c.zip(x, Op::And).zip(&c.not().zip(y, Op::And), Op::Or)
    };
    let (c, l1, l2, l3) = (&l[0], &l[1], &l[2], &l[3]);
    let x = pick(c, l1, &l1.zip(l3, Op::And));
    let y = pick(c, l1, &l1.zip(&l3.not(), Op::And));
    for k in [pick(c, &l2.not(), l3), pick(c, l2, l3)] {
        let joined = Part::connect(Op::And, k.clone(), x.clone())
            .zip(&Part::connect(Op::And, k.not(), y.clone()), Op::Or);
        assert_eq!(joined, *l1, "{k:?}");
    }
}

/// The rule for two choices on one condition of `Connect::choose`, met with two choices on two
/// conditions that are neither equal nor complements (the arm `None`, not reached by any other
/// test, TEST-kernel-unreached-paths-4): the union is kept as an expression, and it holds the
/// assignments of `k&x | !k&y`. The input, the complement of a choice of choices, was found by a
/// random search over the connectives and reduced by hand.
#[test]
fn a_choice_whose_meets_choose_on_two_conditions_keeps_their_union() {
    let l: Vec<Part<Row>> = (0..6).map(|i| Part::literal(atom(i))).collect();
    let pick = |c: &Part<Row>, x: &Part<Row>, y: &Part<Row>| {
        c.zip(x, Op::And).zip(&c.not().zip(y, Op::And), Op::Or)
    };
    let kept = |c: &Part<Row>, x: &Part<Row>, y: &Part<Row>| {
        Part::connect(
            Op::Or,
            Part::connect(Op::And, c.clone(), x.clone()),
            Part::connect(Op::And, c.not(), y.clone()),
        )
    };
    let (l1, l3, l4, l5) = (&l[1], &l[3], &l[4], &l[5]);
    let inner = pick(l4, &l1.not(), l3);
    let outer = pick(l3, &inner, l5);
    let both = kept(l4, &outer, &outer);
    let p = kept(&outer, &inner, &both);
    let complement = p.not();
    let want: Vec<bool> = values(&p).into_iter().map(|v| !v).collect();
    assert_eq!(values(&complement), want);
    assert!(complement.is_leaf().is_none());
}

/// An exclusive or built from two others holds its complement, so taking the complement next
/// costs a lookup, not a frame of `Connect` and a node made again. `xor_of` made the exclusive or
/// with the other constant and returned its complement, dropping the node that held that
/// complement (cross-review of PERF-xor-shape-free, round 2, Sol X2-F3: 296 nodes made and 98
/// complements made again for parity of 100 atoms, against 198 and none).
#[test]
fn an_exclusive_or_built_from_two_holds_its_complement() {
    let lits: Vec<Part<Row>> = (0..6).map(|i| Part::literal(atom(i))).collect();
    let holds = |p: &Part<Row>| {
        assert!(p.xor_tag().is_some(), "not an exclusive or: {p:?}");
        matches!(p, Part::Expr(e) if e.known().is_some())
    };
    for k in 3..=6 {
        let by_or = (1..k).fold(lits[0].clone(), |f, i| xor_by_or(&f, &lits[i]));
        assert!(holds(&by_or), "by `|`, {k} atoms: {by_or:?}");
        let by_and = (1..k).fold(lits[0].clone(), |f, i| xor_by_and(&f, &lits[i]));
        assert!(holds(&by_and), "by `&`, {k} atoms: {by_and:?}");
        let x = (2..k).fold(lits[1].clone(), |f, i| xor_by_or(&f, &lits[i]));
        let choice = xor::xor_choice(&lits[0], &x, &x.not()).expect("an exclusive or of two");
        assert!(holds(&choice), "a choice, {k} atoms: {choice:?}");
    }
}

/// An exclusive or asked for while only its complement lives holds that complement, as one made
/// fresh does: once the caller drops the complement, the next `not` finds it, not a node made
/// again. `Part::xor` returned `n.not()`, which holds `n` only weakly (cross-review of
/// PERF-xor-shape-free, round 3, Claude R3-C1).
#[test]
fn an_exclusive_or_found_through_its_complement_holds_it() {
    let lits: Vec<Part<Row>> = (20..24).map(|i| Part::literal(atom(i))).collect();
    let holds = |p: &Part<Row>| matches!(p, Part::Expr(e) if e.known().is_some());
    let y = (1..4).fold(lits[0].clone(), |f, i| xor_by_or(&f, &lits[i]));
    let (s, constant) = y.xor_tag().expect("an exclusive or of four");
    let n = y.not();
    let n_id = n.id();
    drop(y);
    let again = Part::xor(Some(s), constant);
    assert_eq!(again.not().id(), n_id);
    drop(n);
    assert!(holds(&again), "its complement is not held: {again:?}");
    assert_eq!(again.not().id(), n_id, "its complement was made again");
}

#[test]
fn an_exclusive_or_is_found_again_when_only_its_complement_lives() {
    // The steps leave live only one of the two exclusive ors of a set, its two constants; the
    // other one asked for again is the complement of the live one, not a second node of the same
    // function. `exclusive_ors_agree_with_their_values`, run with new seeds, found the case:
    // `a ^ !b` made by `xor_by_and` and then by `xor_by_or` were two nodes.
    let lits: Vec<Part<Row>> = (0..6).map(|i| Part::literal(atom(i))).collect();
    let not_b = lits[1].not();
    let by_and = xor_by_and(&lits[0], &not_b);
    assert_eq!(xor_by_or(&lits[0], &not_b).id(), by_and.id());
    for k in 2..=6 {
        let flipped = (1..k).fold(lits[0].not(), |f, i| xor_by_and(&f, &lits[i]));
        let again = (1..k).fold(lits[0].not(), |f, i| xor_by_or(&f, &lits[i]));
        assert_eq!(again.id(), flipped.id(), "{k}");
        let plain = (1..k).fold(lits[0].clone(), |f, i| xor_by_or(&f, &lits[i]));
        assert_eq!(plain.not().id(), flipped.id(), "{k}");
    }
}

/// Row KERNEL-xor-complement-dedup (audit P266-3) said that after an exclusive or is built
/// again, equal complement nodes are built more than once. The table of a thread keeps one
/// node per set id and constant, so a second node of one function could only be one left
/// live outside the table. This test holds every node built for `a ^ b ^ c ^ d ^ e` and its
/// complement, built in several orders, by both helpers, after an atom is added and taken out
/// again, with each complement first taken by `not` and then dropped and asked for again, and
/// counts the distinct nodes: two, one per constant. It passed on main at 7b58d316e with no
/// change to `xor` (b22-misc, 2026-11-22), so the claim was not reproduced: `Part::xor` finds
/// the live node and the live complement (`found`) before it makes either.
#[test]
fn an_exclusive_or_built_again_shares_its_two_nodes() {
    let lits: Vec<Part<Row>> = (0..6).map(|i| Part::literal(atom(i))).collect();
    let chain = |order: &[usize], by_or: bool| {
        let first = lits[order[0]].clone();
        order[1..].iter().fold(first, |f, &i| {
            if by_or {
                xor_by_or(&f, &lits[i])
            } else {
                xor_by_and(&f, &lits[i])
            }
        })
    };
    let mut held = vec![chain(&[0, 1, 2, 3, 4], false)];
    held.push(held[0].not());
    for (order, by_or) in [
        (&[4, 3, 2, 1, 0][..], true),
        (&[2, 0, 4, 1, 3][..], false),
        (&[1, 3, 0, 4, 2][..], true),
    ] {
        let x = chain(order, by_or);
        held.push(x.not());
        held.push(x);
    }
    // An atom added and taken out again: the set is made anew and must find the live nodes.
    let back = xor_by_and(&xor_by_or(&held[0], &lits[5]), &lits[5]);
    held.push(back.not());
    held.push(back);
    let ids: std::collections::BTreeSet<u64> = held.iter().map(Part::id).collect();
    assert_eq!(ids.len(), 2, "one node per constant");
    // The caller's handles on the complement dropped and the complement asked for again, while
    // the node lives (it holds its complement, so the same node comes back).
    let x = chain(&[3, 1, 4, 0, 2], true);
    held.retain(|p| p.id() == x.id());
    assert_eq!(held.len(), 5, "the held nodes of one constant");
    let again: std::collections::BTreeSet<u64> = [x.not().id(), x.id()].into();
    assert_eq!(again, ids, "the same two nodes");
}

#[test]
fn exclusive_ors_agree_with_their_values() {
    let firsts = exclusive_or_rounds(
        crate::seed::seed("exclusive_ors_agree_with_their_values"),
        XOR_ROUNDS,
    );
    every_exclusive_or_built_is_the_one_reached(&firsts);
}

/// The rounds of [`exclusive_or_rounds`] in a run. 4000 rounds reached 117 to 126 of the 126
/// exclusive ors on 5,600 seeds, in about 0.3 s a run; the ones a run misses are built by
/// [`every_exclusive_or_built_is_the_one_reached`] (PROOF-test-count-thresholds; until
/// 2026-11-15 the run asserted that at least 100 were reached, which 2000 rounds missed on
/// about 1 seed in 200).
const XOR_ROUNDS: usize = 4000;

/// The seeds on which 2000 rounds reached fewer than 100 exclusive ors (77 on seed 81, 85 on
/// seed 3601000514119134698); 4000 rounds reach 125 of the 126 on each, measured 2026-11-15.
#[test]
fn exclusive_ors_reach_their_count_on_the_seeds_that_failed() {
    for (seed, count) in [(3601000514119134698, 125), (81, 125)] {
        let firsts = exclusive_or_rounds(seed, XOR_ROUNDS);
        assert_eq!(firsts.len(), count, "seed {seed}");
        every_exclusive_or_built_is_the_one_reached(&firsts);
    }
}

/// Each of the 2 · 63 exclusive ors of a nonempty set of the six atoms, and their complements
/// (2 · 64 - 2 functions, every exclusive or that is no leaf), built from the literals in two
/// ways: by [`xor_by_or`] in increasing order of the atoms, and by [`xor_by_and`] in
/// decreasing order with the complement taken on the first literal. Both are exclusive ors in
/// their one form, have the values of the function, and are one node, the node `firsts`
/// holds for the function when the random rounds reached it. So every exclusive or is checked
/// whatever the rounds reached, and no count of them is relied on.
fn every_exclusive_or_built_is_the_one_reached(firsts: &HashMap<u64, Part<Row>>) {
    let lits: Vec<Part<Row>> = (0..6).map(|i| Part::literal(atom(i))).collect();
    let holds = |bits: u32| move |a: &Row| (0..6).any(|i| bits >> i & 1 == 1 && *a == atom(i));
    for set in 1u32..64 {
        let members: Vec<usize> = (0..6).filter(|i| set >> i & 1 == 1).collect();
        let mask = (0..64u32)
            .filter(|b| (b & set).count_ones() % 2 == 1)
            .fold(0u64, |m, b| m | 1 << b);
        for complement in [false, true] {
            let first = |i: usize| match complement {
                true => lits[i].not(),
                false => lits[i].clone(),
            };
            let up = (members[1..].iter()).fold(first(members[0]), |f, &i| xor_by_or(&f, &lits[i]));
            let last = members.len() - 1;
            let down = (members[..last].iter().rev())
                .fold(first(members[last]), |f, &i| xor_by_and(&f, &lits[i]));
            let mask = if complement { !mask } else { mask };
            assert!(up.xor_tag().is_some(), "{set:b} {complement}: {up:?}");
            for bits in 0..64 {
                assert_eq!(
                    up.eval(&holds(bits)),
                    mask >> bits & 1 == 1,
                    "{set:b} {bits:b}"
                );
            }
            assert_eq!(down.id(), up.id(), "{set:b} {complement}");
            if let Some(reached) = firsts.get(&mask) {
                assert_eq!(reached.id(), up.id(), "{set:b} {complement}");
            }
        }
    }
}

/// Random parts over six atoms, each built with its set of values beside it as a mask of
/// the 64 assignments; exclusive ors in their one form of one function are one node while
/// they live. The first part of each function is held, so that a later one is compared with
/// a live node: a node freed and made again takes a new id. Returns the first part made of
/// each exclusive-or function the `rounds` rounds from `seed` reached, by its mask of values.
fn exclusive_or_rounds(seed: u64, rounds: usize) -> HashMap<u64, Part<Row>> {
    // The MMIX linear congruential sequence (zed-hash's `Lcg64`, where its source is).
    let mut rng = zed_hash::Lcg64::new(seed);
    const POOL: usize = 50;
    let lits: Vec<(Part<Row>, u64)> = (0..6)
        .map(|i| {
            let mask = (0..64u32).filter(|b| b >> i & 1 == 1);
            (Part::literal(atom(i)), mask.fold(0u64, |m, b| m | 1 << b))
        })
        .collect();
    let atoms: Vec<Row> = (0..6).map(atom).collect();
    let holds = |bits: u32| {
        let atoms = &atoms;
        move |a: &Row| (0..6).any(|i| bits >> i & 1 == 1 && *a == atoms[i])
    };
    // Two pools: every part made, and the exclusive ors in their one form, from which the
    // operands of the two exclusive ors are drawn (any two parts drawn from the first would be
    // exclusive ors in their one form in about one round in a hundred). The literals stay in
    // both, so that every round can join exclusive ors of them; a leaf makes nothing new and
    // is not kept.
    let put = |pool: &mut Vec<(Part<Row>, u64)>, made: &(Part<Row>, u64), pick: usize| {
        if pool.len() < POOL {
            pool.push(made.clone());
        } else {
            pool[lits.len() + pick % (POOL - lits.len())] = made.clone();
        }
    };
    let (mut pool, mut xors) = (lits.clone(), lits.clone());
    let mut firsts: HashMap<u64, Part<Row>> = HashMap::new();
    for _ in 0..rounds {
        let pick = rng.next_high() as usize;
        let from = if pick % 5 < 2 { &xors } else { &pool };
        let (p, pm) = from[pick % from.len()].clone();
        let (q, qm) = from[(pick / 7) % from.len()].clone();
        let made = match pick % 5 {
            0 => (xor_by_or(&p, &q), pm ^ qm),
            1 => (xor_by_and(&p, &q), pm ^ qm),
            2 => (p.not(), !pm),
            3 => (p.zip(&q, Op::And), pm & qm),
            _ => (p.zip(&q, Op::Or), pm | qm),
        };
        for bits in 0..64 {
            assert_eq!(made.0.eval(&holds(bits)), made.1 >> bits & 1 == 1);
        }
        if made.0.is_leaf().is_some() {
            continue;
        }
        if made.0.xor_tag().is_some() {
            let first = firsts.entry(made.1).or_insert_with(|| made.0.clone());
            assert_eq!(first.id(), made.0.id(), "{:x}", made.1);
            put(&mut xors, &made, pick);
        }
        put(&mut pool, &made, pick);
    }
    firsts
}

#[test]
fn the_halves_of_exclusive_ors_meet_as_zip_meets_them() {
    // `xor::meet` builds the meets of an exclusive or's halves without the search of `zip`,
    // for literals and exclusive ors over disjoint atoms; it must make the part `zip` makes.
    // Random sets of 1 to 7 atoms, each built in a random order, are met with each other and
    // their complements, both ways round.
    let (mut rng, _) = Rng::fresh("the_halves_of_exclusive_ors_meet_as_zip_meets_them");
    let mut next = |below: u64| rng.below_u64(below);
    let mut first = 0u64;
    let mut parts = Vec::new();
    for _ in 0..60 {
        let k = 1 + next(7);
        let mut atoms: Vec<u64> = (first..first + k).collect();
        first += k;
        for i in (1..atoms.len()).rev() {
            atoms.swap(i, next(i as u64 + 1) as usize);
        }
        let x = (atoms.iter()).fold(Part::leaf(false), |f, &a| {
            xor_by_or(&f, &Part::literal(atom(a)))
        });
        assert!(x.xor_tag().is_some(), "{atoms:?}");
        parts.push(x.not());
        parts.push(x);
    }
    let mut exprs = 0;
    for i in (0..parts.len()).step_by(2) {
        for j in (i + 2..parts.len()).step_by(2) {
            for (a, b) in [(i, j), (i + 1, j), (i, j + 1), (i + 1, j + 1)] {
                for (p, q) in [(&parts[a], &parts[b]), (&parts[b], &parts[a])] {
                    exprs += usize::from(meets_as_zip(p, q));
                }
            }
        }
    }
    eprintln!("{exprs} meets kept as expressions");
    // A meet kept as an expression, built, whatever the draws met (PROOF-test-count-
    // thresholds; until 2026-11-15 the test asserted more than 10,000 among the draws): an
    // exclusive or is no decision list, so the meet of `a0 ^ a2` and `a1 ^ a3`, on disjoint
    // atoms, is kept as an expression, as
    // `two_exclusive_ors_on_disjoint_atoms_meet_in_an_expression` finds.
    let lit = |i: u64| Part::literal(atom(first + i));
    let (p, q) = (xor_by_or(&lit(0), &lit(2)), xor_by_or(&lit(1), &lit(3)));
    assert!(meets_as_zip(&p, &q), "{p:?} & {q:?}");
}

/// Checks that `xor::meet` makes the part `zip` makes of `p & q`; gives whether it is an
/// expression.
fn meets_as_zip(p: &Part<Row>, q: &Part<Row>) -> bool {
    let made = xor::meet(p, q);
    assert!(made == p.zip(q, Op::And), "{p:?} & {q:?}");
    made.expr_id().is_some()
}

/// `depth` levels of the atom `#a` with a payload of the level below, over `bottom`, every
/// digest 0: comparing two of them reads every level, as two types whose digests tie at
/// every depth are read in the short-addresses build (SHORT-stack-l01_22).
pub(super) fn tied(bottom: &str, depth: usize) -> Type {
    let zeroed = |t: Type| {
        let Node::Parts(p, _) = &*t.0 else {
            unreachable!("an atom type is no recursive node")
        };
        let mut p = p.clone();
        p.digest = 0;
        p.name_digest = 0;
        Type(Arc::new(Node::Parts(p, super::super::Shown::default())))
    };
    let mut t = zeroed(Type::atom(bottom));
    for _ in 0..depth {
        let Node::Parts(p, _) = &*Type::atom("a").0 else {
            unreachable!("an atom type is no recursive node")
        };
        let mut p = p.clone();
        p.digest = 0;
        p.name_digest = 0;
        p.atoms.set(
            &"a".into(),
            AtomPart {
                bare: false,
                payload: t,
            },
        );
        t = Type(Arc::new(Node::Parts(p, super::super::Shown::default())));
    }
    t
}

/// The order of chains of [`tied`] `depth` levels deep: equal chains are equal, chains whose
/// bottoms differ are ordered by them, read `depth` levels down, and a chain a level shorter is
/// ordered one way, the same both ways round.
pub(super) fn tied_chains_are_ordered(depth: usize) {
    let (a, b, c) = (tied("z", depth), tied("z", depth), tied("y", depth));
    assert_eq!(a.digest(), c.digest());
    assert_eq!(a.cmp(&b), Ordering::Equal);
    assert_eq!(a, b);
    // The bottoms differ: `#y` before `#z`.
    assert_eq!(a.cmp(&c), Ordering::Greater);
    assert_eq!(c.cmp(&a), Ordering::Less);
    // A chain that stops a level short has no payload where the other has one.
    let d = tied("z", depth - 1);
    assert_eq!(d.cmp(&a), a.cmp(&d).reverse());
    assert_ne!(d.cmp(&a), Ordering::Equal);
}

#[test]
fn types_whose_digests_tie_at_every_depth_are_ordered() {
    // From one level, where the shorter chain is the bare bottom, up. The depth at which the
    // old recursion overflowed a small stack is in `bench.rs` (author P178).
    for depth in [1, 2, 5] {
        tied_chains_are_ordered(depth);
    }
}

/// `x_0 | x_1 | … | x_{m-1}` as expressions nested `m - 1` deep, the first operand the
/// deeper, each `x_k` the part `leaf` makes of the atom `base + k`.
pub(super) fn ors(base: u64, m: usize, leaf: impl Fn(Row) -> Part<Row>) -> Part<Row> {
    (1..m as u64).fold(leaf(atom(base)), |e, k| {
        Part::connect(Op::Or, e, leaf(atom(base + k)))
    })
}

/// The expressions `e_k = e_{k-1} | e_{k-2}` for `k` from 2 to `m - 1`, the last returned, on
/// `e_0` the atom `base` and `e_1` the atom `base + 1`: each expression is the second operand
/// of the one two above it, so an evaluation that reaches it first through the first operand
/// finds it in its memo the second time. In [`ors`] every lookup comes before the first entry.
pub(super) fn ladder(base: u64, m: usize) -> Part<Row> {
    let (mut below, mut top) = (Part::literal(atom(base)), Part::literal(atom(base + 1)));
    for _ in 2..m {
        let next = Part::connect(Op::Or, top.clone(), below);
        (below, top) = (top, next);
    }
    top
}

/// `t | y_1 | … | y_{m-1}` as expressions nested `m - 1` deep, and `!t`: `t` is the
/// complement of the atom `base` kept as an expression, and `y_k` the list of the
/// atoms `base + 2k - 1` and `base + 2k`, which is no chain under `|`, so that no union
/// rebuilt from them merges into a list. [`Part::settle`] pins `t` to `false` and
/// rebuilds the `m - 1` expressions above it.
pub(super) fn settled_by_one_pin(base: u64, m: usize) -> Part<Row> {
    let t = Part::not_expr(Part::literal(atom(base)));
    let p = (1..m as u64).fold(t.clone(), |e, k| {
        let x = Bdd::literal(atom(base + 2 * k - 1));
        Part::connect(
            Op::Or,
            e,
            Part::Bdd(x.and_literal((atom(base + 2 * k), true))),
        )
    });
    Part::connect(Op::And, p, Part::not_expr(t))
}

/// `T_1 & (T_2 & (… & T_m))` with `T_k = s_k | !s_{k+1}` for `k < m` and `T_m = s_m`, each `s_k`
/// the union of two meets of two atoms of its own, which is no chain under `|`, so that it stays
/// an expression when a round rebuilds the part ([`settled_by_one_pin`]). `s_k`'s trial `false`
/// makes the part `false` only once `s_{k+1}` is pinned `true` (then `!s_{k+1}` is `false` and
/// `T_k` is `s_k`), so a round pins `s_k` only where the walk of [`Part::pins`] reaches it after
/// `s_{k+1}`. The first walk finds `s_2, …, s_m` in that order and pins `s_m` alone; the walks
/// of the rebuilt parts find them in other orders, and pin 1 to 17 at a time. Measured (VM):
/// 14 rounds at m 64, 38 at 128 and 75 at 256, so the rounds grow with `m` (COMPLEXITY K144).
pub(super) fn pinned_one_a_round(base: u64, m: usize) -> Part<Row> {
    // One expression per `s_k`, so that its two uses are one expression.
    let s: Vec<Part<Row>> = (0..=m as u64)
        .map(|k| {
            let at = base + 4 * k;
            Part::connect(Op::Or, Part::Bdd(meet(at, 2)), Part::Bdd(meet(at + 2, 2)))
        })
        .collect();
    let terms: Vec<Part<Row>> = (1..=m)
        .map(|k| match k < m {
            true => Part::connect(Op::Or, s[k].clone(), Part::not_expr(s[k + 1].clone())),
            false => s[m].clone(),
        })
        .collect();
    terms
        .into_iter()
        .rev()
        .reduce(|rest, t| Part::connect(Op::And, t, rest))
        .expect("m is at least 1")
}

#[test]
fn a_chain_pinned_one_a_round_settles_as_the_scans_do() {
    for m in [1, 2, 3, 5, 9] {
        let p = pinned_one_a_round(900, m);
        let settled = p.settle();
        assert!(settled == p.settle_by_scans(), "m = {m}");
        // Every `s_k` with `k >= 2` is pinned `true`, which leaves `T_1 = s_1`, four atoms.
        assert_eq!(settled.distinct_atoms().len(), 4, "m = {m}");
        // The rounds of `settle`: each `s_k` with `k >= 2` pinned once, in more than one round
        // from m 3 on.
        let (mut q, mut rounds) = (p, Vec::new());
        loop {
            let pins = q.pins();
            if pins.is_empty() {
                break;
            }
            rounds.push(pins.len());
            q = q.substitute_all(&pins);
        }
        assert_eq!(rounds.iter().sum::<usize>(), m - 1, "m = {m}: {rounds:?}");
        assert_eq!(m >= 3, rounds.len() > 1, "m = {m}: {rounds:?}");
    }
}

/// The list `x_0 & x_1 & … & x_{m-1}`, one block of `m` literals, the atoms from `base`.
pub(super) fn meet(base: u64, m: usize) -> Bdd<Row> {
    (0..m as u64).fold(Bdd::Leaf(true), |b, k| {
        b.and_literal((atom(base + k), true))
    })
}

/// [`meet`] built as its one block at once: the block of the literals `x_k` not taken, of value
/// `false`, before `true`. `O(m)` after the sort, against `O(m log m)` literal by literal; for
/// the inputs of benchmarks (TIME-pieces-under-cap-high-load).
pub(super) fn meet_at_once(base: u64, m: usize) -> Bdd<Row> {
    let mut keys: Vec<_> = (0..m as u64).map(|k| (atom(base + k), false)).collect();
    keys.sort();
    Bdd::assemble(vec![(false, set::from_sorted(keys))], &Bdd::Leaf(true))
}

#[test]
fn a_meet_built_at_once_is_the_meet_built_literal_by_literal() {
    for m in 0..40 {
        assert_eq!(meet_at_once(700, m).id(), meet(700, m).id(), "m = {m}");
    }
}

/// `Bdd::zip_chain` of two chains, each under either connective, is the list the other's
/// literals give joined to the first one at a time (`or_literal`, `and_literal`), the path
/// it replaces (PROOF-union-all-expr-parts): the same node, and the connective's value at
/// every set of the atoms. Every chain on four atoms is met, each atom absent, taken or
/// refused, so every case of `zip_chain` is: two chains under `op` (`set::union_if_agree`,
/// agreeing or with an atom taken by one and refused by the other), a chain under `op` met
/// with one under the other connective (`set::difference_if_agree`: atoms apart, shared with
/// one polarity, shared with the other, and the other's block emptied), and a short chain.
#[test]
fn a_chain_joined_at_once_is_the_chain_joined_literal_by_literal() {
    let chains = |op: Op| -> Vec<Bdd<Row>> {
        (0..81u32)
            .map(|code| {
                let (unit, mut code) = (Bdd::Leaf(op == Op::And), code);
                (0..4).fold(unit, |c, i| {
                    let digit = code % 3;
                    code /= 3;
                    let key = (atom(i), digit == 1);
                    match (digit, op) {
                        (0, _) => c,
                        (_, Op::Or) => c.or_literal(key),
                        (_, Op::And) => c.and_literal(key),
                    }
                })
            })
            .collect()
    };
    let (ors, ands) = (chains(Op::Or), chains(Op::And));
    let holds = |set: u32| move |t: &Row| (0..4).any(|i| set >> i & 1 == 1 && *t == atom(i));
    let (mut long, mut met) = (0, 0);
    for op in [Op::Or, Op::And] {
        for x in ors.iter().chain(&ands) {
            for j in ors.iter().chain(&ands) {
                let Some(at_once) = x.zip_chain(j, op) else {
                    continue;
                };
                let (base, keys) = match j.chain_keys(op) {
                    Some(k) => (x, k),
                    None => (
                        j,
                        x.chain_keys(op)
                            .expect("one of the two is a chain under op"),
                    ),
                };
                let one_by_one = keys.into_iter().fold(base.clone(), |f, k| match op {
                    Op::Or => f.or_literal(k),
                    Op::And => f.and_literal(k),
                });
                let op_name = if op == Op::Or { "or" } else { "and" };
                assert_eq!(at_once.id(), one_by_one.id(), "{x:?} {op_name} {j:?}");
                for set in 0..16 {
                    let (a, b) = (x.eval(holds(set)), j.eval(holds(set)));
                    let want = match op {
                        Op::Or => a || b,
                        Op::And => a && b,
                    };
                    let got = at_once.eval(holds(set));
                    assert_eq!(got, want, "{x:?} {op_name} {j:?} at {set}");
                }
                let other = match op {
                    Op::Or => Op::And,
                    Op::And => Op::Or,
                };
                long += usize::from(x.is_long_chain(op) && j.is_long_chain(op));
                met += usize::from(
                    (x.is_long_chain(other) && j.is_long_chain(op))
                        || (j.is_long_chain(other) && x.is_long_chain(op)),
                );
            }
        }
    }
    // Each case was reached: of the 81 chains under a connective, 72 have two or more
    // literals; two of them under `op`, for each `op`, are 2 * 72^2 pairs, and one under each
    // connective, in either order, 2 * 2 * 72^2.
    assert_eq!((long, met), (2 * 72 * 72, 4 * 72 * 72));
}

/// The walks on expressions and diagrams nested `depth` deep: union rows, eval, eval3, the
/// atoms, the forced atoms, restrict and settle, each on the input whose answer is known.
pub(super) fn the_walks_over_parts_hold(depth: usize) {
    let p = ors(0, depth, Part::literal);
    assert_eq!(p.union_rows().map(|r| r.len()), Some(depth));
    assert!(!p.eval(&|_| false));
    assert!(p.eval(&|a| *a == atom(0)));
    assert_eq!(p.eval3(&|_| None), None);
    assert_eq!(p.eval3(&|a| Some(*a == atom(0))), Some(true));
    assert_eq!(p.distinct_atoms().len(), depth);
    assert_eq!(p.forced(), (Vec::new(), Vec::new()));
    let only = |x: Row| move |a: &Row| (*a != x).then_some(false);
    assert_eq!(p.restrict(&only(atom(0))), Part::literal(atom(0)));
    let q = settled_by_one_pin(0, depth);
    assert_eq!(q.settle().distinct_atoms().len(), 2 * (depth - 1));
    let b = Part::Bdd(meet(0, depth));
    assert_eq!(b.eval3(&|_| None), None);
    assert_eq!(b.eval3(&|_| Some(true)), Some(true));
    assert_eq!(b.distinct_atoms().len(), depth);
    assert_eq!(b.restrict(&|_| None), b);
    let all_but = |x: Row| move |a: &Row| (*a != x).then_some(true);
    assert_eq!(b.restrict(&all_but(atom(0))), Part::literal(atom(0)));
}

#[test]
fn an_expression_read_twice_has_one_value() {
    // The ladder's top is the union of its two atoms, and each expression below it is read
    // once through each of two expressions above it.
    let p = ladder(0, 12);
    assert!(!p.eval(&|_| false));
    assert!(p.eval(&|_| true));
    assert!(p.eval(&|a| *a == atom(0)));
    assert!(p.eval(&|a| *a == atom(1)));
    assert!(!p.eval(&|a| *a == atom(2)));
}

/// The list `x_0 & … & x_{m-2} & !x_{m-1}`, on the atoms of [`meet`]`(base, m)`, which
/// meets it in no value: the meet of the two joins each literal of one to the other.
pub(super) fn meet_but_last(base: u64, m: usize) -> Bdd<Row> {
    let last = atom(base + m as u64 - 1);
    meet(base, m - 1).and_literal((last, false))
}

/// The choice `c_{m-1} & (… (c_1 & x_0 | !c_1 & y_1) …) | !c_{m-1} & y_{m-1}`, kept as
/// expressions nested `m - 1` deep, each `c_k` the atom `base + k`, `x_0` the atom
/// `base + m`, and `y_k` the atom `leaves + k`. Its complement, and its union with another
/// such chain on the same conditions, are each built a level at a time, through the choice
/// each level is.
pub(super) fn choices(base: u64, leaves: u64, m: usize) -> Part<Row> {
    (1..m as u64).fold(Part::literal(atom(base + m as u64)), |p, k| {
        let c = Part::literal(atom(base + k));
        Part::connect(
            Op::Or,
            Part::connect(Op::And, c.clone(), p),
            Part::connect(Op::And, c.not(), Part::literal(atom(leaves + k))),
        )
    })
}

/// The connectives on lists `lists` literals long and on choices nested `choice` deep: the
/// meet of a list with one that differs in its last literal, the complement and its
/// complement, the union with the complement, and the union of two chains of choices on the
/// same conditions, each against the answer known.
pub(super) fn the_connectives_on_parts_hold(lists: usize, choice: usize) {
    let (a, b) = (meet(0, lists), meet_but_last(0, lists));
    assert_eq!(a.zip_chain(&b, Op::And), Some(Bdd::Leaf(false)));
    let not_a = a.not();
    assert_eq!(not_a.not(), a);
    assert_eq!(a.zip_chain(&not_a, Op::Or), Some(Bdd::Leaf(true)));
    let l = b.list();
    assert_eq!(l.blocks.len(), 1);
    assert_eq!(l.blocks[0].1.len(), lists);
    let base = 10 * lists as u64;
    let p = choices(base, base + 2 * choice as u64, choice);
    let q = choices(base, base + 4 * choice as u64, choice);
    let not_p = p.not();
    assert_eq!(not_p.not(), p);
    assert_eq!(p.zip(&not_p, Op::And), Part::leaf(false));
    let both = p.zip(&q, Op::Or);
    // Every condition and `x_0` held: both chains take the deepest branch, `x_0`.
    let deepest: BTreeSet<Row> = (1..=choice as u64).map(|k| atom(base + k)).collect();
    assert!(p.eval(&|a| deepest.contains(a)));
    assert!(both.eval(&|a| deepest.contains(a)));
    // No condition held, and the top leaf of `q`: only `q` takes it.
    let top_of_q = atom(base + 4 * choice as u64 + choice as u64 - 1);
    assert!(both.eval(&|a| *a == top_of_q));
    assert!(!p.eval(&|a| *a == top_of_q));
}

#[test]
fn the_connectives_on_parts_hold_at_small_depths() {
    // The depths at which the old recursions overflowed the default stack are in `bench.rs`
    // (author P178).
    for (lists, choice) in [(2, 2), (3, 3), (9, 9)] {
        the_connectives_on_parts_hold(lists, choice);
    }
}

/// The entries of this thread's tables of tuple nodes, in all: sets, cells and exclusive ors.
fn entries() -> usize {
    Row::table(|t| t.sets.values().map(|b| b.len()).sum::<usize>() + t.cells.len() + t.xors.len())
}

/// The exclusive or of the atoms `base..base + k`.
fn parity(base: u64, k: u64) -> Part<Row> {
    (base..base + k).fold(Part::leaf(false), |f, i| {
        xor_by_or(&f, &Part::literal(atom(i)))
    })
}

#[test]
fn the_tables_keep_a_node_only_while_it_lives() {
    // Each table holds its nodes weakly, and a node leaves it when it is dropped (step
    // TABLE-life): the lists, sets, exclusive ors and complements of a unit leave no entry.
    let before = entries();
    {
        let x = parity(7000, 8);
        assert!(x.xor_tag().is_some());
        let parts = [x.not(), Part::Bdd(meet(7100, 64)), choices(7200, 7300, 16)];
        let nots: Vec<Part<Row>> = parts.iter().map(Part::not).collect();
        assert!(entries() > before);
        assert_eq!(nots[2].not().id(), parts[2].id());
    }
    assert_eq!(entries(), before);
}

#[test]
fn a_node_rebuilt_after_its_drop_equals_the_first() {
    // While a node lives, building it again finds it; once dropped, it is built anew with
    // another id and the same contents.
    let first = meet(7400, 32);
    let (id, digest) = (first.id(), first.digest());
    assert_eq!(meet(7400, 32).id(), id);
    drop(first);
    let again = meet(7400, 32);
    assert_eq!(again.digest(), digest);
    assert_eq!(meet(7400, 32).id(), again.id());
    let holds = |a: &Row| *a != atom(7400 + 31);
    assert!(!again.eval(holds));
    assert!(again.eval(|_| true));
}

#[test]
fn a_complement_is_found_while_it_lives_and_rebuilt_alike_after() {
    // The complement of an expression: found again while it lives, rebuilt with the same
    // contents once dropped, and its own complement the expression in both cases.
    let e = choices(7500, 7600, 8);
    let n = e.not();
    assert_eq!(e.not().id(), n.id());
    assert_eq!(n.not().id(), e.id());
    let n_digest = n.digest();
    drop(n);
    let n = e.not();
    assert_eq!((n.digest(), n.not().id()), (n_digest, e.id()));
    // The expression dropped while its complement lives: made again as written, with the
    // same digest (so no order or text depends on whether it was freed), the same values,
    // and negating back to the complement.
    let (e_id, e_digest) = (e.id(), e.digest());
    drop(e);
    let again = n.not();
    assert_ne!(again.id(), e_id);
    assert_eq!(again.digest(), e_digest);
    assert_eq!(again.not().id(), n.id());
    let written = choices(7500, 7600, 8);
    let atoms: Vec<Row> = (7501..=7508).chain(7601..7608).map(atom).collect();
    for bits in 0..1u32 << atoms.len() {
        let holds = |a: &Row| (0..atoms.len()).any(|i| bits >> i & 1 == 1 && *a == atoms[i]);
        assert_eq!(again.eval(&holds), written.eval(&holds), "{bits:b}");
    }
    // An exclusive or's complement, its mate, rebuilt after its drop: the same contents, an
    // exclusive or again, and the one node a literal's complement taken in reaches.
    let x = parity(7700, 6);
    let mate = x.not();
    let mate_digest = mate.digest();
    assert_eq!(mate.not().id(), x.id());
    drop(mate);
    let mate = x.not();
    assert_eq!(mate.digest(), mate_digest);
    assert!(mate.xor_tag().is_some());
    assert_eq!(mate.not().id(), x.id());
    let flipped = (7701..7706).fold(Part::literal(atom(7700)).not(), |f, i| {
        xor_by_or(&f, &Part::literal(atom(i)))
    });
    assert_eq!(flipped.id(), mate.id());
    let holds = |bits: u32| {
        move |a: &Row| (0..6).any(|i| bits >> i & 1 == 1 && *a == atom(7700 + i as u64))
    };
    for bits in 0..64 {
        assert_eq!(mate.eval(&holds(bits)), !odd(bits, 6), "{bits:b}");
    }
    // The exclusive or dropped while its mate lives: rebuilt from the mate, the same node
    // the literals give.
    let x_digest = x.digest();
    drop(x);
    let x = mate.not();
    assert_eq!(x.digest(), x_digest);
    assert_eq!(x.id(), parity(7700, 6).id());
}

#[test]
fn equal_rows_alive_together_are_one_node_and_leave_the_table_when_freed() {
    // Step TABLE-life: two equal rows built apart while both live are one node, so a meet
    // compares them by pointer; a freed row leaves the table.
    let (a, b) = (atom(7900), atom(7900));
    assert!(std::ptr::eq(a.as_ptr(), b.as_ptr()));
    assert!(!std::ptr::eq(a.as_ptr(), atom(7901).as_ptr()));
    let digest = a.digest();
    let live = || super::super::ROWS.with(|t| t.borrow().get(&digest).map_or(0, |b| b.len()));
    assert_eq!(live(), 1);
    drop((a, b));
    assert_eq!(live(), 0);
}

#[test]
fn equal_morphism_types_alive_together_are_one_node_and_leave_the_table_when_freed() {
    // Step ATOM-intern: as rows, two equal morphism types built apart while both live are one
    // node, so they compare by pointer; a freed one leaves the table.
    let lit = |i| Type::lit(&Value::Int(i)).unwrap();
    let arrow = |i| Morphism::new(Type::empty(), lit(7990), lit(i));
    let (a, b) = (arrow(7991), arrow(7991));
    assert!(std::ptr::eq(&*a, &*b));
    assert!(!std::ptr::eq(&*a, &*arrow(7992)));
    let digest = a.digest();
    let live = || super::super::ARROWS.with(|t| t.borrow().get(&digest).map_or(0, |b| b.len()));
    assert_eq!(live(), 1);
    drop((a, b));
    assert_eq!(live(), 0);
}

/// The text of `!n` and whether it equals the type `n` is the complement of, where `n` is
/// the complement of a type whose tuple part is a choice, found through a row of `n`. In
/// batch mode an earlier unit built the same row and dropped the type, keeping the row (as
/// a recursive instance that outlives its unit keeps its members, item REC-cycle), so the
/// row found is that unit's and `!n` is made again from a complement whose holder was freed;
/// alone, the complement's holder lives and `!n` is it.
fn complement_of_a_kept_complement(batch: bool) -> (String, String, bool) {
    std::thread::spawn(move || {
        let ty = || {
            Type::with(|p| {
                p.tuples.lens.insert(1, choices(7950, 7980, 8));
            })
        };
        let kept = batch.then(|| {
            let t = ty();
            Row::new(vec![!&t])
        });
        let t = ty();
        let row = Row::new(vec![!&t]);
        assert_eq!(
            kept.as_ref()
                .map(|k| std::ptr::eq(k.as_ptr(), row.as_ptr())),
            batch.then_some(true),
            "the earlier unit's row is found",
        );
        let back = !&row[0];
        (back.to_string(), back.surface().to_string(), back == t)
    })
    .join()
    .expect("the thread runs without panicking")
}

#[test]
fn batch_and_single_file_agree_on_a_complement_whose_holder_was_freed() {
    // Step TABLE-life: a complement made again after its holder was freed is made from the
    // holder's written form, so the text and order are those of a check run alone.
    let alone = complement_of_a_kept_complement(false);
    assert!(alone.2);
    assert_eq!(complement_of_a_kept_complement(true), alone);
}

/// The offsets of the atoms a scaling test runs at each size when its work follows the
/// path or spine of one treap: a priority is a hash of a literal, so each offset gives the
/// treaps another random shape, and the work summed over the offsets measures the expected
/// path rather than one sample of it. Every size runs all of them.
pub(super) const SHAPES: u64 = 8;

/// The distance between the atoms of two offsets, above the atoms any one offset uses.
pub(super) const SHAPE_STRIDE: u64 = 1 << 32;

/// The block of the two literals on the atoms `a` and `a + 1`, each taken.
pub(super) fn pair_block(a: u64) -> Arc<Set<Row>> {
    set::insert(Some(&set::single((atom(a), true))), (atom(a + 1), true))
}

/// The list of `m` blocks of two literals, the atoms from `base`, the values alternating
/// from `true`: no block is merged or moved, so the list has `m` cells.
pub(super) fn blocks(base: u64, m: usize) -> Bdd<Row> {
    let prefix = (0..m as u64)
        .map(|i| (i % 2 == 0, Some(pair_block(base + 2 * i))))
        .collect();
    Bdd::assemble(prefix, &Bdd::Leaf(m.is_multiple_of(2)))
}

/// The atoms a list's paths to a value take are given in the list's order, the blocks first to
/// last and the literals of a block in order, whatever the draw that shapes the cells and sets
/// (PERF-xor-shape-free): the callers keep the first atom found or build unions in the order
/// given. A walk that took a node before its sides gives another order but at a draw in about
/// `1/8!` for each block of 8.
#[test]
fn the_atoms_taken_toward_a_value_come_in_the_lists_order() {
    let k = 8u64;
    let m = 16u64;
    let block = |i: u64| {
        // Every third literal is not taken, so both kinds of call are met.
        let keys = (0..k).map(|j| (atom(1000 + i * k + j), j % 3 != 1));
        let mut keys: Vec<_> = keys.collect();
        keys.sort();
        set::from_sorted(keys).expect("non-empty")
    };
    let blocks: Vec<_> = (0..m).map(block).collect();
    let prefix = (0..m as usize)
        .map(|i| (i % 2 == 0, Some(blocks[i].clone())))
        .collect();
    let list = Bdd::assemble(prefix, &Bdd::Leaf(m.is_multiple_of(2)));
    assert_eq!(list.list().blocks.len(), m as usize);
    for to in [false, true] {
        let mut expected = Vec::new();
        for (i, b) in blocks.iter().enumerate() {
            for (a, taken) in set::iter(Some(b)) {
                if (i % 2 == 0) == to || !taken {
                    expected.push(a.clone());
                }
            }
        }
        let mut got = Vec::new();
        let mut seen = crate::digest::DigestSet::default();
        list.taken_toward(to, &mut seen, &mut |a| got.push(a.clone()));
        assert!(expected.len() > k as usize, "{to}");
        assert_eq!(got, expected, "{to}");
    }
}

#[test]
fn restricting_with_a_shared_memo_gives_the_lists_restricted_alone() {
    // Item CHAIN-restrict-memo: a memo kept across lists that share cells gives each list
    // what a fresh memo gives it, on every atom fixed either way.
    let tail = blocks(8500, 6);
    let mut lists = vec![tail.clone(), tail.not()];
    for i in 0..3u64 {
        let head = (i % 2 == 0, Some(pair_block(8600 + 2 * i)));
        lists.push(Bdd::assemble(vec![head], &tail));
        let one = (i % 2 == 1, Some(set::single((atom(8700 + i), true))));
        lists.push(Bdd::assemble(vec![one], &tail));
    }
    let atoms: Vec<Row> = (8500..8512)
        .chain(8600..8606)
        .chain(8700..8703)
        .map(atom)
        .collect();
    for a in &atoms {
        for x in [false, true] {
            let fix = |b: &Row| (b == a).then_some(x);
            let mut memo = list::Memo::default();
            for l in &lists {
                let shared = l.restrict(&fix, &mut memo);
                let alone = l.restrict(&fix, &mut Default::default());
                assert_eq!(shared, alone, "{a:?} {x}");
                for bits in [0u64, 0x15555, 0xaaaaa, 0x1fffff, 0x12345] {
                    let holds = |b: &Row| {
                        if b == a {
                            return x;
                        }
                        let i = atoms.iter().position(|y| y == b).expect("an atom listed");
                        bits >> i & 1 == 1
                    };
                    assert_eq!(shared.eval(holds), l.eval(holds), "{a:?} {x} {bits:x}");
                }
            }
        }
    }
}

#[test]
fn a_choice_between_chains_is_the_one_found_by_listing_both() {
    // Item CHOICE-both-chains: the union of two meets with one literal each the other's
    // complement, found by looking the shorter's literals up in the longer, has the values
    // of the union; with two such literals it is kept as written.
    let x = meet(8800, 5);
    let y = meet(8810, 2).and_literal((atom(8802), false));
    let z = meet(8810, 1)
        .and_literal((atom(8802), false))
        .and_literal((atom(8803), false));
    let atoms: Vec<Row> = (8800..8805).chain(8810..8812).map(atom).collect();
    for other in [y, z] {
        let u = Part::Bdd(x.clone()).zip(&Part::Bdd(other.clone()), Op::Or);
        assert!(
            matches!(&u, Part::Expr(e) if matches!(e.form(), Form::Or(..))),
            "{u:?}"
        );
        for bits in 0..1u32 << atoms.len() {
            let holds = |a: &Row| (0..atoms.len()).any(|i| bits >> i & 1 == 1 && *a == atoms[i]);
            assert_eq!(
                u.eval(&holds),
                x.eval(holds) || other.eval(holds),
                "{bits:b}"
            );
        }
    }
}

#[test]
fn an_expression_and_its_complement_are_freed_together() {
    // Item CHOICE-both-chains: an expression and its complement point at each other, and
    // were a cycle of `Arc`s that no drop freed; since step TABLE-life the complement
    // holds its expression weakly. A choice, a choice of chains and an exclusive or, each
    // with its complement made, are freed when dropped.
    let weak = |p: &Part<Row>| match p {
        Part::Expr(e) => Arc::downgrade(e),
        Part::Bdd(_) => unreachable!("an expression"),
    };
    let held = {
        let chains = Part::Bdd(meet(8900, 4)).zip(
            &Part::Bdd(meet(8910, 1).and_literal((atom(8901), false))),
            Op::Or,
        );
        let parts = [choices(8920, 8940, 6), chains, parity(8960, 5)];
        let nots: Vec<Part<Row>> = parts.iter().map(Part::not).collect();
        for (p, n) in parts.iter().zip(&nots) {
            assert_eq!(n.not().id(), p.id());
        }
        (parts.iter().chain(&nots)).map(weak).collect::<Vec<_>>()
    };
    for (i, w) in held.iter().enumerate() {
        assert!(w.upgrade().is_none(), "part {i} lives on");
    }
}

#[test]
fn an_exclusive_or_built_on_another_thread_is_recognized() {
    // Item XOR-cross-thread: an exclusive or built on another thread, joined to the
    // complement of the same one built here, is the exclusive or that the two built here
    // give: the atoms' sets of the two threads are equal but not one node.
    let k = 6;
    let there = std::thread::spawn(move || parity(9000, k))
        .join()
        .expect("the thread runs without panicking");
    let here = parity(9000, k);
    let l = Part::literal(atom(9000 + k));
    let mixed = (there.zip(&l, Op::Or)).zip(&here.not().zip(&l.not(), Op::Or), Op::And);
    let alone = (here.zip(&l, Op::Or)).zip(&here.not().zip(&l.not(), Op::Or), Op::And);
    assert!(alone.xor_tag().is_some());
    assert_eq!(mixed, alone);
    assert!(mixed.xor_tag().is_some(), "{mixed:?}");
    // The choice `l&x | !l&!x`, `x` built there and `!x` here: `!(l ^ x)`.
    let c = l
        .zip(&there, Op::And)
        .zip(&l.not().zip(&here.not(), Op::And), Op::Or);
    let d = l
        .zip(&here, Op::And)
        .zip(&l.not().zip(&here.not(), Op::And), Op::Or);
    assert!(d.xor_tag().is_some());
    assert_eq!(c, d);
    assert!(c.xor_tag().is_some(), "{c:?}");
}

/// Whether `p` is an expression whose form is not made yet (`Expr::form`).
fn unmade(p: &Part<Row>) -> bool {
    matches!(p, Part::Expr(e) if e.form.get().is_none())
}

/// The expression of `p`.
fn expr_of(p: &Part<Row>) -> &Arc<Expr<Row>> {
    match p {
        Part::Expr(e) => e,
        Part::Bdd(_) => unreachable!("an expression"),
    }
}

#[test]
fn the_halves_of_an_exclusive_or_are_made_on_first_read() {
    // Items KERNEL-parity-lazy-halves and PERF-xor-shape-free: an exclusive or is made with its
    // digests alone, its set's and its constant's, and its two meets when its form is first
    // read. The form made on first read is the one `zip` makes of `p&!q | !p&q` or
    // `p&q | !p&!q`, for `p` the literal of the smallest atom and `q` the exclusive or of the
    // others, its operands in their order.
    for k in 2..12 {
        let x = parity(9600 + 20 * k, k);
        // Ordering two exclusive ors of distinct digests reads no form.
        let y = parity(9601 + 20 * k, k);
        assert!(x.digest() != y.digest() && x != y);
        for p in [&x, &x.not(), &y] {
            assert!(unmade(p), "{k}");
        }
        for p in [x.clone(), x.not()] {
            let e = expr_of(&p);
            let (s, constant) = e.xor.as_ref().expect("an exclusive or");
            let first = set::min(s);
            let q = Part::literal(first.0.clone());
            let r = Part::xor(set::remove(s, first), false);
            let (a, b) = match constant {
                true => (q.zip(&r, Op::And), q.not().zip(&r.not(), Op::And)),
                false => (q.zip(&r.not(), Op::And), q.not().zip(&r, Op::And)),
            };
            let (a, b) = if a.before(&b) { (a, b) } else { (b, a) };
            let Form::Or(u, v) = e.form() else {
                panic!("an exclusive or is a union: {p:?}")
            };
            assert!(*u == a && *v == b, "{k} {constant}");
            let digest = |d: u64| mix(mix(11, d), u64::from(*constant));
            assert_eq!(
                (e.digest, e.name_digest),
                (digest(s.digest), digest(s.name_digest))
            );
            assert!(!unmade(&p));
        }
        for bits in 0..1u32 << k {
            let holds =
                |a: &Row| (0..k).any(|i| bits >> i & 1 == 1 && *a == atom(9600 + 20 * k + i));
            assert_eq!(x.eval(&holds), odd(bits, k as u32), "{k} {bits:b}");
        }
    }
}

#[test]
fn an_exclusive_or_made_again_from_its_pair_is_made_on_first_read() {
    // The complement of an exclusive or whose own complement was dropped is made again from
    // their set (`xor::mate`), with its digest alone, equal to the one dropped.
    let first = parity(9900, 9);
    let (digest, text) = (first.digest(), format!("{first:?}"));
    let n = first.not();
    assert!(expr_of(&n).known().is_some());
    drop(first);
    assert!(expr_of(&n).known().is_none());
    let again = n.not();
    assert!(unmade(&again));
    assert_eq!(again.digest(), digest);
    assert_eq!(format!("{again:?}"), text);
    assert_eq!(again.not().id(), n.id());
}

#[test]
fn the_complement_of_an_exclusive_or_is_its_live_mate() {
    // An exclusive or dropped while its complement lives, and built again from the same set of
    // its atoms, is the complement's complement, taken from the table (`xor::mate`), not made
    // a third time (TEST-bench-move-l0123, author P188: before, only a benchmark of l01_23
    // reached it, 2 times in 15,000 complements), as in
    // `an_exclusive_or_made_again_from_its_pair_is_made_on_first_read`.
    for k in [2, 3, 9] {
        let base = 9970 + 10 * k;
        let first = parity(base, k);
        let (atoms, constant) = first.xor_tag().expect("an exclusive or in its one form");
        let n = first.not();
        drop(first);
        let x = Part::xor(Some(atoms), constant);
        let again = n.not();
        assert!(
            matches!((&again, &x), (Part::Expr(a), Part::Expr(b)) if Arc::ptr_eq(a, b)),
            "{k}"
        );
        // `x` was made as `n`'s complement, so its own complement is `n`.
        assert_eq!(x.not().id(), n.id(), "{k}");
        for bits in 0..1u32 << k {
            let holds = |a: &Row| (0..k).any(|i| bits >> i & 1 == 1 && *a == atom(base + i));
            assert_eq!(x.eval(&holds), odd(bits, k as u32), "{k} {bits:b}");
            assert_eq!(n.eval(&holds), !odd(bits, k as u32), "{k} {bits:b}");
        }
    }
}

#[test]
fn the_halves_of_an_exclusive_or_read_on_many_threads_are_made_once() {
    // An exclusive or shared by threads that read its form at once: each reads the one form,
    // made by one of them (`OnceLock`).
    const THREADS: usize = 8;
    let x = parity(9950, 10);
    assert!(unmade(&x));
    let barrier = std::sync::Barrier::new(THREADS);
    let seen: Vec<usize> = std::thread::scope(|s| {
        let threads: Vec<_> = (0..THREADS)
            .map(|_| {
                let (x, barrier) = (&x, &barrier);
                s.spawn(move || {
                    barrier.wait();
                    std::ptr::from_ref(expr_of(x).form()).addr()
                })
            })
            .collect();
        (threads.into_iter())
            .map(|h| h.join().expect("the thread runs without panicking"))
            .collect()
    });
    assert!(seen.iter().all(|&a| a == seen[0]), "{seen:?}");
    // The form is the exclusive or's one form: the union of its halves is the node itself.
    let Form::Or(u, v) = expr_of(&x).form() else {
        panic!("an exclusive or is a union")
    };
    assert_eq!(u.zip(v, Op::Or).id(), x.id());
}

/// What `exclusive_ors_shared_by_threads_are_the_ones_built_on_one` records of a part: its
/// digest, its complement's, whether it is an exclusive or in its one form, and its text.
type Record = (u64, u64, bool, String);

/// The record of `p`; see `Record`.
fn record(p: &Part<Row>) -> Record {
    (
        p.digest(),
        p.not().digest(),
        p.xor_tag().is_some(),
        format!("{p:?}"),
    )
}

/// One round of `exclusive_ors_shared_by_threads_are_the_ones_built_on_one` for thread `t`:
/// three literals each joined to the part `p` another thread built, so that the sets made share
/// nodes of `p`'s set, then all three in turn. Returns the records and the last part.
fn extend(p: Part<Row>, round: u64, t: u64) -> (Vec<Record>, Part<Row>) {
    let lits: Vec<_> = (0..3)
        .map(|i| Part::literal(atom(60_000 + round * 100 + t * 10 + i)))
        .collect();
    let mut out: Vec<_> = lits.iter().map(|l| record(&xor_by_or(&p, l))).collect();
    let last = lits.iter().fold(p, |f, l| xor_by_or(&f, l));
    out.push(record(&last));
    (out, last)
}

#[test]
fn exclusive_ors_shared_by_threads_are_the_ones_built_on_one() {
    // Each thread keeps its own tables (`TUPLES` in `types.rs`), and parts are shared between
    // threads. Eight threads each start from an exclusive or of 40 atoms; in each round a
    // thread takes the part another thread built in the round before, joins literals to it,
    // and hands its result on, so that a thread makes sets over nodes another thread made, and
    // a part is dropped on a thread other than the one that built it. Every part built is
    // recorded, and the records equal those of the same rounds run on one thread.
    const THREADS: u64 = 8;
    const ROUNDS: u64 = 6;
    let start = |t: u64| parity(50_000 + t * 1_000, 40);
    let alone = std::thread::spawn(move || {
        let mut slots: Vec<_> = (0..THREADS).map(start).collect();
        let mut out = Vec::new();
        for r in 0..ROUNDS {
            let taken: Vec<_> = (0..THREADS)
                .map(|t| slots[((t + r + 1) % THREADS) as usize].clone())
                .collect();
            for (t, p) in (0..THREADS).zip(taken) {
                let (rec, last) = extend(p, r, t);
                out.push(rec);
                slots[t as usize] = last;
            }
        }
        out
    })
    .join()
    .expect("the thread runs without panicking");
    let slots: std::sync::Mutex<Vec<Option<Part<Row>>>> =
        std::sync::Mutex::new((0..THREADS).map(|_| None).collect());
    let barrier = std::sync::Barrier::new(THREADS as usize);
    let shared: Vec<Vec<_>> = std::thread::scope(|s| {
        let threads: Vec<_> = (0..THREADS)
            .map(|t| {
                let (slots, barrier) = (&slots, &barrier);
                s.spawn(move || {
                    let mut out = Vec::new();
                    slots.lock().expect("no thread panics")[t as usize] = Some(start(t));
                    for r in 0..ROUNDS {
                        barrier.wait();
                        let p = slots.lock().expect("no thread panics")
                            [((t + r + 1) % THREADS) as usize]
                            .clone()
                            .expect("each slot is filled");
                        barrier.wait();
                        let (rec, last) = extend(p, r, t);
                        out.push(rec);
                        // The part replaced was built on another thread and is dropped here.
                        let old = slots.lock().expect("no thread panics")[t as usize].replace(last);
                        drop(old);
                    }
                    out
                })
            })
            .collect();
        threads
            .into_iter()
            .map(|h| h.join().expect("the thread runs without panicking"))
            .collect()
    });
    for r in 0..ROUNDS {
        for t in 0..THREADS {
            let (a, b) = (
                &alone[(r * THREADS + t) as usize],
                &shared[t as usize][r as usize],
            );
            assert!(a == b, "round {r}, thread {t}");
        }
    }
}

/// The list of `m` blocks of two literals on the atoms from `base`, built by joining one
/// literal at a time, each new block first: the values alternate from `false` at the
/// block built first. Built from `or_literal` and `and_literal` alone.
pub(super) fn joined_blocks(base: u64, m: usize) -> Bdd<Row> {
    let mut f = Bdd::Leaf(false);
    for i in 0..m as u64 {
        for a in [base + 2 * i, base + 2 * i + 1] {
            f = match i % 2 {
                0 => f.or_literal((atom(a), true)),
                _ => f.and_literal((atom(a), true)),
            };
        }
    }
    f
}

#[test]
fn rejoined_blocks_give_the_function_and_the_one_form() {
    // Item CHAIN-deep-atom: the list after the rejoins of the scaling test
    // `bench::rejoining_one_atom_of_each_block_scales`, on 6
    // blocks, against the truth table of the same joins.
    let (base, m) = (70500, 6);
    let mut f = joined_blocks(base, m);
    let atoms: Vec<Row> = (0..2 * m as u64).map(|i| atom(base + i)).collect();
    let at = |a: &Row| atoms.iter().position(|b| b == a).expect("an atom listed");
    let mut table: Vec<bool> = (0..1u32 << (2 * m))
        .map(|s| joined_blocks(base, m).eval(|a| s >> at(a) & 1 == 1))
        .collect();
    for i in 0..m {
        f = match i % 2 {
            0 => f.or_literal((atoms[2 * i].clone(), true)),
            _ => f.and_literal((atoms[2 * i].clone(), true)),
        };
        for (s, t) in table.iter_mut().enumerate() {
            let x = s >> (2 * i) & 1 == 1;
            *t = if i % 2 == 0 { *t || x } else { *t && x };
        }
    }
    for (s, t) in table.iter().enumerate() {
        assert_eq!(f.eval(|a| s >> at(a) & 1 == 1), *t, "{s:b}");
    }
    assert!(f.cells_are_sound());
}

/// A decision list as plain vectors, its operations by the rules of the one form, the
/// reference for the treap of cells (item CHAIN-deep-atom).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Plain {
    blocks: Vec<(bool, BTreeMap<u64, bool>)>,
    tail: bool,
}

impl Plain {
    /// The list of `blocks` and `tail` in its one form: empty blocks dropped, neighbors of
    /// one value joined, then the end as `list::finish` puts it.
    fn normal(blocks: Vec<(bool, BTreeMap<u64, bool>)>, mut tail: bool) -> Plain {
        let mut out: Vec<(bool, BTreeMap<u64, bool>)> = Vec::new();
        for (v, b) in blocks {
            if b.is_empty() {
                continue;
            }
            match out.last_mut() {
                Some((w, c)) if *w == v => c.extend(b),
                _ => out.push((v, b)),
            }
        }
        if out.last().is_some_and(|(v, _)| *v == tail) {
            out.pop();
        }
        if out.len() >= 2 && out[out.len() - 1].1.len() == 1 {
            let (u, last) = out.pop().expect("two or more blocks");
            let (&m, &t) = last.iter().next().expect("one literal");
            out.last_mut().expect("a block before").1.insert(m, !t);
            tail = u;
        }
        if out.len() == 1 && !out[0].0 && out[0].1.len() == 1 {
            let (&m, &t) = out[0].1.iter().next().expect("one literal");
            out[0] = (true, BTreeMap::from([(m, !t)]));
            tail = false;
        }
        Plain { blocks: out, tail }
    }

    fn or(&self, a: u64, t: bool) -> Plain {
        let found = (self.blocks.iter()).position(|(_, b)| b.contains_key(&a));
        let Some(p) = found else {
            let mut blocks = self.blocks.clone();
            match blocks.first_mut() {
                _ if self.blocks.is_empty() && self.tail => return self.clone(),
                Some((true, b)) => {
                    b.insert(a, t);
                }
                _ => blocks.insert(0, (true, BTreeMap::from([(a, t)]))),
            }
            return Plain {
                blocks,
                tail: self.tail,
            };
        };
        let (w, taken) = (self.blocks[p].0, self.blocks[p].1[&a]);
        if taken == t && p == 0 && w {
            return self.clone();
        }
        let rest = if taken == t {
            let mut blocks = self.blocks.clone();
            blocks[p].1.remove(&a);
            Plain::normal(blocks, self.tail)
        } else {
            Plain::normal(self.blocks[..p].to_vec(), w)
        };
        rest.or(a, t)
    }

    fn not(&self) -> Plain {
        let blocks = self.blocks.iter().map(|(v, b)| (!v, b.clone())).collect();
        Plain::normal(blocks, !self.tail)
    }

    fn and(&self, a: u64, t: bool) -> Plain {
        self.not().or(a, !t).not()
    }

    fn restrict(&self, fix: &BTreeMap<u64, bool>) -> Plain {
        let mut blocks = Vec::new();
        for (v, b) in &self.blocks {
            if b.iter().any(|(a, t)| fix.get(a) == Some(t)) {
                return Plain::normal(blocks, *v);
            }
            let left = b.iter().filter(|(a, _)| !fix.contains_key(a));
            blocks.push((*v, left.map(|(a, t)| (*a, *t)).collect()));
        }
        Plain::normal(blocks, self.tail)
    }

    fn eval(&self, holds: impl Fn(u64) -> bool) -> bool {
        for (v, b) in &self.blocks {
            if b.iter().any(|(a, t)| holds(*a) == *t) {
                return *v;
            }
        }
        self.tail
    }
}

#[test]
fn list_operations_agree_with_plain_lists() {
    // Item CHAIN-deep-atom: random joins, complements, restrictions and blocks put before
    // lists, on 40 atoms, give the list the plain vectors give, one id for one list, and
    // cells of a treap whose atoms are those of their blocks. The first list of each value is
    // kept, since ids are compared only between lists alive at once.
    const ATOMS: u64 = 40;
    let base = 71000;
    let (mut rng, _) = Rng::fresh("list_operations_agree_with_plain_lists");
    let mut next = move || rng.next_u64();
    let atoms: Vec<Row> = (0..ATOMS).map(|i| atom(base + i)).collect();
    let index = |a: &Row| atoms.iter().position(|b| b == a).expect("an atom listed") as u64;
    let plain = |b: &Bdd<Row>| Plain {
        blocks: (b.list().blocks.into_iter())
            .map(|(v, l)| (v, l.iter().map(|(a, t)| (index(a), *t)).collect()))
            .collect(),
        tail: b.default(),
    };
    // The cells are sound, one list has one id, and the values agree on the sets of `bits`.
    let agrees = |g: &Bdd<Row>, q: &Plain, kept: &mut BTreeMap<Plain, Bdd<Row>>, bits: [u64; 4]| {
        assert!(g.cells_are_sound(), "{g:?}");
        let id = kept.entry(q.clone()).or_insert_with(|| g.clone()).id();
        assert_eq!(id, g.id(), "two cells of one list: {q:?}");
        for bits in bits {
            let holds = |x: u64| bits >> x & 1 == 1;
            assert_eq!(g.eval(|b| holds(index(b))), q.eval(holds), "{q:?}");
        }
    };
    let mut pool: Vec<(Bdd<Row>, Plain)> = vec![(Bdd::Leaf(false), plain(&Bdd::Leaf(false)))];
    let mut kept: BTreeMap<Plain, Bdd<Row>> = BTreeMap::new();
    let mut longest = 0;
    for _ in 0..8_000 {
        let r = next();
        let (f, p) = pool[(r % pool.len() as u64) as usize].clone();
        let (a, t) = (next() % ATOMS, next() % 2 == 0);
        let op = (r >> 32) % 10;
        let made = match op {
            0..=4 => match matches!(f, Bdd::List(_, true)) {
                // A new block first, most of the time, so that the lists grow long.
                true => (f.and_literal((atoms[a as usize].clone(), t)), p.and(a, t)),
                false => (f.or_literal((atoms[a as usize].clone(), t)), p.or(a, t)),
            },
            5 => (f.or_literal((atoms[a as usize].clone(), t)), p.or(a, t)),
            6 => (f.and_literal((atoms[a as usize].clone(), t)), p.and(a, t)),
            7 => (f.not(), p.not()),
            8 => {
                let fix: BTreeMap<u64, bool> = (0..1 + next() % 3)
                    .map(|_| (next() % ATOMS, next() % 2 == 0))
                    .collect();
                let by_row = |b: &Row| fix.get(&index(b)).copied();
                (
                    f.restrict(&by_row, &mut Default::default()),
                    p.restrict(&fix),
                )
            }
            _ => {
                let free: Vec<u64> = (0..ATOMS)
                    .filter(|x| !p.blocks.iter().any(|(_, b)| b.contains_key(x)))
                    .collect();
                if free.len() < 2 {
                    continue;
                }
                let (x, y) = (
                    free[a as usize % free.len()],
                    free[(a as usize + 1) % free.len()],
                );
                let block = set::insert(
                    Some(&set::single((atoms[x as usize].clone(), t))),
                    (atoms[y as usize].clone(), !t),
                );
                let mut blocks = vec![(t, BTreeMap::from([(x, t), (y, !t)]))];
                blocks.extend(p.blocks.iter().cloned());
                let tail = p.tail;
                (
                    Bdd::assemble(vec![(t, Some(block))], &f),
                    Plain::normal(blocks, tail),
                )
            }
        };
        let (g, q) = made;
        assert_eq!(plain(&g), q, "op {op} on {p:?}, atom {a} {t}: {g:?}");
        agrees(&g, &q, &mut kept, [next(), next(), next(), next()]);
        longest = longest.max(q.blocks.len());
        pool.push((g, q));
        if pool.len() > 400 {
            pool.swap_remove((next() % 400) as usize);
        }
    }
    eprintln!("the longest list drawn has {longest} blocks");
    // A long list built, whatever the draws reached (PROOF-test-count-thresholds; until
    // 2026-11-15 the test asserted that the longest list drawn had 12 blocks or more). From
    // the empty list, atoms 0, 1, 2, … joined alternately by `|` and `&`, each taken: by
    // `Plain::or`, `Plain::not` and `Plain::normal`, `a0 | …` is one block, `(a0) & a1` one
    // block `!a0 | !a1` of value false, and each later literal, on an atom not in the list, is
    // put first as a block of its own, its value the opposite of the block after it. So 20
    // literals give 19 blocks, as `a_list_of_alternating_literals_has_a_block_per_literal`
    // finds for literals joined at the other end.
    let (mut g, mut q) = (Bdd::Leaf(false), plain(&Bdd::Leaf(false)));
    for i in 0..20u64 {
        let key = (atoms[i as usize].clone(), true);
        (g, q) = match i % 2 {
            0 => (g.or_literal(key), q.or(i, true)),
            _ => (g.and_literal(key), q.and(i, true)),
        };
        assert_eq!(plain(&g), q, "{i}: {g:?}");
        agrees(&g, &q, &mut kept, [i, !i, i << 7 | 5, u64::MAX]);
    }
    assert_eq!(q.blocks.len(), 19, "{q:?}");
}

#[test]
fn a_set_less_some_literals_is_the_set_they_leave_one_at_a_time() {
    // `set::retain` against removing the literals one at a time (`set::remove`): sets have one
    // shape and are found again in the table, so the two must give one node. Random sets of up
    // to 200 literals, with none, some or all removed.
    let mut rng = Rng::new(7);
    let mut next = || rng.next_u64();
    for round in 0..300 {
        let m = next() % 200 + 1;
        let mut t = set::single((atom(round * 1000), next() % 2 == 0));
        for i in 1..m {
            t = set::insert(Some(&t), (atom(round * 1000 + i), next() % 2 == 0));
        }
        let every = [1, 2, 3, 7, 1000][(next() % 5) as usize];
        let gone: Vec<_> = set::iter(Some(&t))
            .filter(|_| next() % every == 0)
            .cloned()
            .collect();
        let mut one_at_a_time = Some(t.clone());
        for k in &gone {
            one_at_a_time = set::remove(one_at_a_time.as_ref().expect("k is in it"), k);
        }
        let mut order = Vec::new();
        let retained = set::retain(&t, |k| {
            order.push(k.clone());
            !gone.contains(k)
        });
        assert_eq!(
            order,
            set::iter(Some(&t)).cloned().collect::<Vec<_>>(),
            "keep is asked in order"
        );
        assert_eq!(
            retained.as_ref().map(|s| s.id),
            one_at_a_time.as_ref().map(|s| s.id),
            "round {round}: {} of {m} removed",
            gone.len()
        );
        if gone.is_empty() {
            assert_eq!(
                retained.map(|s| s.id),
                Some(t.id),
                "nothing removed keeps the node"
            );
        }
    }
}

// Small instances of the benchmarks in `bench.rs`: each checks at a few small sizes what the
// benchmark of the same input checks besides its ratio (TEST-bench-move-crates).

/// `w ∧ ((x_1 ∧ … ∧ x_m) ∨ z)`, built from its literals by the connectives, `w` the atom 0
/// and `z` the atom `m + 1`; and `w`, the one atom it forces.
pub(super) fn forced_chain(m: usize) -> (Part<Row>, Row) {
    let xs: Vec<Row> = (0..m as u64 + 2).map(atom).collect();
    let lit = |k: usize| Part::literal(xs[k].clone());
    let meet = (2..=m).fold(lit(1), |g, k| g.zip(&lit(k), Op::And));
    let g = meet.zip(&lit(m + 1), Op::Or);
    (lit(0).zip(&g, Op::And), xs[0].clone())
}

/// [`forced_chain`] kept as an expression (`Part::connect`), as [`conjunction`] keeps its
/// conjunction: `Part::forced` walks every link of it, where on the decision list that `zip`
/// makes it reads the first block only (`Bdd::forced_to`).
pub(super) fn forced_chain_expr(m: usize) -> Part<Row> {
    let lit = |k: usize| Part::literal(atom(k as u64));
    let and = |a, b| Part::connect(Op::And, a, b);
    let meet = (2..=m).fold(lit(1), |g, k| and(g, lit(k)));
    and(lit(0), Part::connect(Op::Or, meet, lit(m + 1)))
}

#[test]
fn the_one_atom_a_chain_forces_is_its_first() {
    for m in [1, 2, 3, 8, 33] {
        let (p, w) = forced_chain(m);
        let want = (vec![w], Vec::new());
        assert_eq!(p.forced(), want, "{m}");
        assert_eq!(forced_chain_expr(m).forced(), want, "{m}, as an expression");
    }
}

/// The literal `x_i` of [`conjunction`]: the atom `i`, refused at every third.
fn conjunction_literal(i: usize) -> Part<Row> {
    let l = Part::literal(atom(i as u64));
    if i % 3 == 2 { l.not() } else { l }
}

/// `x_0 ∧ x_1 ∧ … ∧ x_{m-1}`, every third literal refused, kept as expressions: built one
/// literal at a time, or as a balanced tree (`balanced`).
pub(super) fn conjunction(m: usize, balanced: bool) -> Part<Row> {
    let and = |a: Part<Row>, b: Part<Row>| Part::connect(Op::And, a, b);
    if !balanced {
        return (1..m).fold(conjunction_literal(0), |p, i| {
            and(p, conjunction_literal(i))
        });
    }
    let mut level: Vec<Part<Row>> = (0..m).map(conjunction_literal).collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut it = level.into_iter();
        while let Some(a) = it.next() {
            next.push(match it.next() {
                Some(b) => and(a, b),
                None => a,
            });
        }
        level = next;
    }
    level.pop().expect("one literal at least")
}

/// The atoms [`conjunction`]`(m, _)` forces taken and refused, each sorted.
pub(super) fn conjunction_forced(m: usize) -> (Vec<Row>, Vec<Row>) {
    let (mut taken, mut refused): (Vec<Row>, Vec<Row>) = (Vec::new(), Vec::new());
    for i in 0..m {
        if i % 3 == 2 { &mut refused } else { &mut taken }.push(atom(i as u64));
    }
    taken.sort();
    refused.sort();
    (taken, refused)
}

/// Forced atoms with each list sorted.
pub(super) fn sorted_forced((mut t, mut r): (Vec<Row>, Vec<Row>)) -> (Vec<Row>, Vec<Row>) {
    t.sort();
    r.sort();
    (t, r)
}

#[test]
fn a_conjunction_forces_each_of_its_literals() {
    assert_eq!(
        sorted_forced(conjunction_literal(0).forced()),
        conjunction_forced(1),
        "one literal"
    );
    for m in [2, 3, 7, 64] {
        for balanced in [false, true] {
            let p = conjunction(m, balanced);
            assert_eq!(
                sorted_forced(p.forced()),
                conjunction_forced(m),
                "{m}, balanced {balanced}"
            );
        }
    }
    // A conjunction holding an atom both ways holds nowhere: every atom is then forced.
    let empty = Part::connect(Op::And, conjunction(5, false), Part::literal(atom(0)).not());
    let (t, r) = empty.forced();
    assert_eq!(t.len() + r.len(), 5, "{empty:?}");
}

/// `x_{k+1} = x_k & !x_k` to `depth` levels over the atom 0: both operands of each level
/// lead to the level below.
pub(super) fn self_meets(depth: usize) -> Part<Row> {
    let mut x = Part::literal(atom(0));
    for _ in 0..depth {
        x = Part::connect(Op::And, x.clone(), x.not());
    }
    x
}

#[test]
fn equal_expressions_built_apart_compare_equal() {
    for depth in [0, 1, 2, 5, 16] {
        assert_eq!(self_meets(depth).cmp(&self_meets(depth)), Ordering::Equal);
    }
    assert_ne!(self_meets(4).cmp(&self_meets(5)), Ordering::Equal);
}

/// A list of `m` literals on the atoms from 0, in blocks of two of alternating values.
pub(super) fn paired_literals(m: usize) -> Part<Row> {
    let mut b = Bdd::Leaf(false);
    for i in 0..m {
        let k = (atom(i as u64), true);
        b = if (i / 2) % 2 == 0 {
            b.or_literal(k)
        } else {
            b.and_literal(k)
        };
    }
    Part::Bdd(b)
}

#[test]
fn equal_lists_built_on_two_threads_compare_equal() {
    let on_a_thread = |m: usize| {
        std::thread::spawn(move || paired_literals(m))
            .join()
            .unwrap()
    };
    for m in [1, 2, 3, 4, 9, 64] {
        let (a, b) = (on_a_thread(m), on_a_thread(m));
        assert_eq!(a.cmp(&b), Ordering::Equal, "{m}");
        assert_ne!(a.cmp(&on_a_thread(m + 1)), Ordering::Equal, "{m}");
    }
}

/// `((x0 | x1) & !x2 | x3) & !x4 …` on `m` atoms, each new literal first in the order, so
/// that every literal is a block of its own.
pub(super) fn alternating_literals(m: usize) -> Bdd<Row> {
    let mut xs: Vec<Row> = (0..m as u64).map(atom).collect();
    xs.sort();
    let mut f = Part::literal(xs[m - 1].clone());
    for (i, x) in xs[..m - 1].iter().rev().enumerate() {
        f = match i % 2 {
            0 => f.zip(&Part::literal(x.clone()), Op::Or),
            _ => f.zip(&Part::literal(x.clone()).not(), Op::And),
        };
    }
    let Part::Bdd(b) = f else {
        unreachable!("a literal joined to a list is a list")
    };
    b
}

#[test]
fn a_list_of_alternating_literals_has_a_block_per_literal() {
    for m in [2, 3, 4, 9, 64] {
        let l = alternating_literals(m).list();
        assert_eq!(l.blocks.len(), m - 1, "{m}");
        assert!(!l.tail, "{m}");
    }
}

#[test]
fn chains_built_a_literal_at_a_time_stay_lists() {
    for m in [2, 3, 8, 65] {
        let mut xs: Vec<Row> = (0..m as u64).map(|i| atom(60000 + i)).collect();
        xs.sort();
        let lits: Vec<Part<Row>> = xs.into_iter().map(Part::literal).collect();
        // Literals taken in alternately and as complements: a list.
        let f = (lits[1..].iter().enumerate()).fold(lits[0].clone(), |f, (i, x)| match i % 2 {
            0 => f.zip(x, Op::Or),
            _ => f.zip(&x.not(), Op::And),
        });
        assert!(matches!(f, Part::Bdd(_)), "{m}: {f:?}");
        // One connective all along: a chain of all `m`.
        for op in [Op::Or, Op::And] {
            let f = (lits[1..].iter()).fold(lits[0].clone(), |f, x| f.zip(x, op));
            assert!(
                matches!(&f, Part::Bdd(b) if b.chain_len(op) == Some(m)),
                "{m}: {f:?}"
            );
        }
        // Two chains with half their atoms in common: the union is neither.
        let chain = |from: u64| {
            (from..from + m as u64).fold(Part::leaf(false), |f, k| {
                f.zip(&Part::literal(atom(61000 + k)), Op::Or)
            })
        };
        let (a, b) = (chain(0), chain(m as u64 / 2 + 1));
        let both = a.zip(&b, Op::Or);
        assert!(both != a && both != b, "{m}");
    }
}

/// The exclusive ors of the first half and of the last three quarters of `m` atoms from
/// `16 m`, which share a quarter, each built a literal at a time.
pub(super) fn overlapping_xors(m: usize) -> (Part<Row>, Part<Row>) {
    let ls: Vec<_> = (0..m as u64)
        .map(|i| Part::literal(atom(16 * m as u64 + i)))
        .collect();
    let half = |r: std::ops::Range<usize>| {
        ls[r]
            .iter()
            .fold(Part::leaf(false), |f, l| xor_by_or(&f, l))
    };
    (half(0..m / 2), half(m / 4..m))
}

#[test]
fn exclusive_ors_with_atoms_in_common_join_in_an_exclusive_or() {
    for m in [4, 8, 12, 64] {
        let (a, b) = overlapping_xors(m);
        let joined = xor_by_and(&a, &b);
        assert!(joined.xor_tag().is_some(), "{m}");
        // The shared quarter leaves: the first quarter and the last half remain.
        let rest = (0..m / 4)
            .chain(m / 2..m)
            .map(|i| Part::literal(atom(16 * m as u64 + i as u64)))
            .fold(Part::leaf(false), |f, l| xor_by_or(&f, &l));
        assert_eq!(joined.id(), rest.id(), "{m}");
    }
}

#[test]
fn the_walks_over_parts_hold_at_small_depths() {
    for m in [2, 3, 9] {
        let (or, pin, meet, ladder) = (
            ors(10 * m as u64, m, Part::literal),
            settled_by_one_pin(20 * m as u64, m),
            Part::Bdd(meet(30 * m as u64, m)),
            ladder(40 * m as u64, m),
        );
        assert!(!or.eval(&|_| false));
        assert!(!ladder.eval(&|_| false));
        assert_eq!(or.eval3(&|_| None), None);
        assert_eq!(meet.eval3(&|_| None), None);
        assert_eq!(or.distinct_atoms().len(), m);
        assert_eq!(meet.distinct_atoms().len(), m);
        assert_eq!(or.union_rows().map(|r| r.len()), Some(m));
        assert_eq!(or.forced(), (Vec::new(), Vec::new()));
        assert_eq!(or.restrict(&|_| Some(false)), Part::leaf(false));
        assert_eq!(meet.restrict(&|_| None), meet);
        assert_eq!(pin.settle().distinct_atoms().len(), 2 * (m - 1));
        // The depths at which the old recursions overflowed a small stack are in `bench.rs`
        // (author P178).
        the_walks_over_parts_hold(m);
    }
}

#[test]
fn a_long_meet_joined_to_short_meets_is_kept_as_an_expression() {
    // The input of `a_long_meet_joined_to_short_meets_scales` at 8 literals: a meet of two on
    // atoms of its own, and a meet of one with the complement of a literal of the long meet.
    let m = 8;
    let long = meet(40000, m);
    let atoms: Vec<Row> = (40000..40000 + m as u64)
        .chain(50000..50000 + 2 * m as u64)
        .map(atom)
        .collect();
    for i in 0..m as u64 {
        let short = match i % 2 {
            0 => meet(50000 + 2 * i, 2),
            _ => meet(50000 + 2 * i, 1).and_literal((atom(40000 + i), false)),
        };
        let u = Part::Bdd(long.clone()).zip(&Part::Bdd(short.clone()), Op::Or);
        assert!(matches!(u, Part::Expr(_)), "{i}: {u:?}");
        for seed in 0..64u64 {
            let bits = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let holds = |a: &Row| {
                let k = atoms.iter().position(|b| b == a).expect("an atom listed");
                // Every literal of the long meet taken at seed 0, so that it holds there.
                seed == 0 && k < m || bits >> (k % 64) & 1 == 1
            };
            assert_eq!(
                u.eval(&holds),
                long.eval(holds) || short.eval(holds),
                "{i} {seed}"
            );
        }
    }
}

/// `a&(a|b)&w | !a&(!a|d)&w`, joined with the same over `!w` for an exclusive or `w`, is
/// everything: the meets of the choice on `w` are Bdds that `zip_chain` joins to the leaf `true`
/// (round 2 cross-review, Gemini R2-F3 Case I). On base e48f7567d the union stayed an expression,
/// and a morphism set of that shape was not `decidable()`.
#[test]
fn a_choice_on_an_exclusive_or_whose_branches_cover_everything_is_the_leaf() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let [a, b, d, p, q] = [0, 1, 2, 3, 4].map(|i| Part::literal(atom(i)));
    let w = xor_by_or(&p, &q);
    let (x, y) = (or(&a, &b), or(&a.not(), &d));
    let half = |w: &Part<Row>| or(&and(&a, &and(&x, w)), &and(&a.not(), &and(&y, w)));
    assert_eq!(or(&half(&w), &half(&w.not())).is_leaf(), Some(true));
    // The same shape over morphisms.
    let m = |i: i64| {
        let l = Type::lit(&Value::Int(i)).unwrap();
        Type::morphism(l.clone(), l, Type::int())
    };
    let (ma, mb, md, mp, mq) = (m(0), m(1), m(2), m(3), m(4));
    let all = Type::universe(crate::types::Universe::Morphism);
    let not = |t: &Type| &all - t;
    let mw = &(&mp & &not(&mq)) | &(&not(&mp) & &mq);
    let (mx, my) = (&ma | &mb, &not(&ma) | &md);
    let mhalf = |w: &Type| &(&ma & &(&mx & w)) | &(&not(&ma) & &(&my & w));
    let merged = &mhalf(&mw) | &mhalf(&not(&mw));
    assert!(merged.subtype(&all) && all.subtype(&merged));
    assert!(merged.decidable(), "{}", merged.surface());
}

// CANON-choose-true-branch (Opus, round 2 of the xor-shape cross-review, N1): the choice
// `c&x | !c&y` with the branch `x` the leaf `true` was kept as `c | !c&y`, another node than
// `c | y` built by `zip`. A union kept as an expression is not hash-consed (`Part::expr` takes a
// new id at each call), so `or(&c, &y)` made twice has two ids; the two are compared by contents
// and digest, which differed before the repair (cross-review round 3, Gemini Q2).
#[test]
fn a_choice_with_a_true_branch_is_the_union_in_its_one_form() {
    let [a, b, c, d, e] = [0, 1, 2, 3, 4].map(|i| Part::literal(atom(i)));
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let y = xor_by_or(&xor_by_or(&b, &d), &e);
    assert!(y.xor_tag().is_some());
    let pick = |c: &Part<Row>, x: &Part<Row>, y: &Part<Row>| or(&and(c, x), &and(&c.not(), y));
    // `c?a:y | c?!a:y`: the branches join to `true` and `y`.
    let merged = or(&pick(&c, &a, &y), &pick(&c, &a.not(), &y));
    let direct = or(&c, &y);
    let holds = |bits: u32| move |r: &Row| (0..5).any(|i| bits >> i & 1 == 1 && *r == atom(i));
    for bits in 0..32 {
        assert_eq!(
            merged.eval(&holds(bits)),
            direct.eval(&holds(bits)),
            "{bits:b}"
        );
    }
    assert!(merged == direct, "{merged:?} is not {direct:?}");
    assert_eq!(merged.digest(), direct.digest());
}

/// The other branch `true`: `c?y:a | c?y:!a` is `!c | y`.
#[test]
fn a_choice_with_a_true_second_branch_is_the_union_in_its_one_form() {
    let [a, b, c, d, e] = [0, 1, 2, 3, 4].map(|i| Part::literal(atom(i)));
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let y = xor_by_or(&xor_by_or(&b, &d), &e);
    let pick = |c: &Part<Row>, x: &Part<Row>, y: &Part<Row>| or(&and(c, x), &and(&c.not(), y));
    let merged = or(&pick(&c, &y, &a), &pick(&c, &y, &a.not()));
    let direct = or(&c.not(), &y);
    let holds = |bits: u32| move |r: &Row| (0..5).any(|i| bits >> i & 1 == 1 && *r == atom(i));
    for bits in 0..32 {
        assert_eq!(
            merged.eval(&holds(bits)),
            direct.eval(&holds(bits)),
            "{bits:b}"
        );
    }
    assert!(merged == direct, "{merged:?} is not {direct:?}");
    assert_eq!(merged.digest(), direct.digest());
}

// Widened by the round 2 review (Gemini R2-F3, Cases III and IV).

/// Case III: the condition is itself a choice; both branches meet `w` and `!w` to `a ^ e`.
#[test]
fn a_choice_on_a_compound_condition_whose_meets_agree_is_that_meet() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let [a, b, e, p, q, r, s] = [0, 1, 3, 4, 5, 6, 7].map(|i| Part::literal(atom(i)));
    let w = xor_by_or(&p, &q);
    let dx = xor_by_or(&r, &s);
    let c = or(&and(&dx, &a), &and(&dx.not(), &b));
    let ae = xor_by_or(&a, &e);
    let x = or(&and(&dx, &or(&a.not(), &e.not())), &and(&dx.not(), &ae));
    let y = or(&and(&dx, &or(&a, &e)), &and(&dx.not(), &ae));
    let half = |w: &Part<Row>| or(&and(&c, &and(&x, w)), &and(&c.not(), &and(&y, w)));
    let merged = or(&half(&w), &half(&w.not()));
    let holds = |bits: u32| move |row: &Row| (0..8).any(|i| bits >> i & 1 == 1 && *row == atom(i));
    for bits in 0..256 {
        assert_eq!(merged.eval(&holds(bits)), ae.eval(&holds(bits)), "{bits:b}");
    }
    assert_eq!(merged.id(), ae.id(), "{merged:?} is not {ae:?}");
}

/// Case IV: the meets of the two choices on `a` are `a&d` and `!a&d`, which is `d`.
#[test]
fn a_meet_of_choices_whose_branches_meet_to_one_set_is_that_set() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let [a, d, r, s, t, u] = [0, 2, 6, 7, 8, 9].map(|i| Part::literal(atom(i)));
    let (w, z) = (xor_by_or(&r, &s), xor_by_or(&t, &u));
    let ad = and(&a, &d);
    let nad = and(&a.not(), &d);
    let left = or(&and(&a, &or(&ad, &w)), &and(&a.not(), &or(&nad, &z)));
    let right = or(
        &and(&a, &or(&ad, &w.not())),
        &and(&a.not(), &or(&nad, &z.not())),
    );
    let merged = and(&left, &right);
    let holds = |bits: u32| move |row: &Row| (0..10).any(|i| bits >> i & 1 == 1 && *row == atom(i));
    for bits in 0..1024 {
        assert_eq!(merged.eval(&holds(bits)), d.eval(&holds(bits)), "{bits:b}");
    }
    assert_eq!(merged.id(), d.id(), "{merged:?} is not {d:?}");
}

/// Case IV with `d` a meet of `m` literals, so that the meets are chains of `m + 1` literals:
/// the small instances of `the_union_of_a_choices_meets_scales`.
#[test]
fn a_meet_of_choices_whose_branches_meet_to_a_meet_of_literals_is_that_meet() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    for m in [1, 2, 3, 6] {
        let lit = |i: usize| Part::literal(atom(i as u64));
        let a = lit(0);
        let d = (1..=m).fold(Part::leaf(true), |f, i| and(&f, &lit(i)));
        let [r, s, t, u] = [m + 1, m + 2, m + 3, m + 4].map(lit);
        let (w, z) = (xor_by_or(&r, &s), xor_by_or(&t, &u));
        let (ad, nad) = (and(&a, &d), and(&a.not(), &d));
        let left = or(&and(&a, &or(&ad, &w)), &and(&a.not(), &or(&nad, &z)));
        let right = or(
            &and(&a, &or(&ad, &w.not())),
            &and(&a.not(), &or(&nad, &z.not())),
        );
        let merged = and(&left, &right);
        let holds = |bits: u32| {
            move |row: &Row| (0..m + 5).any(|i| bits >> i & 1 == 1 && *row == atom(i as u64))
        };
        for bits in 0..1u32 << (m + 5) {
            assert_eq!(
                merged.eval(&holds(bits)),
                d.eval(&holds(bits)),
                "{m} {bits:b}"
            );
        }
        assert!(merged == d, "{m}: {merged:?} is not {d:?}");
    }
}

/// The union of two choices with one branch `true` and the other an exclusive or of `m`
/// atoms: the small instances of `the_union_of_a_choices_meets_scales`.
#[test]
fn a_choice_with_a_true_branch_and_a_long_exclusive_or_is_the_union() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    for m in [2, 3, 5, 8] {
        let [a, c] = [0, 1].map(|i| Part::literal(atom(i)));
        let y = (2..2 + m as u64).fold(Part::leaf(false), |f, i| {
            xor_by_or(&f, &Part::literal(atom(i)))
        });
        let pick = |x: &Part<Row>| or(&and(&c, x), &and(&c.not(), &y));
        let merged = or(&pick(&a), &pick(&a.not()));
        let direct = or(&c, &y);
        let holds = |bits: u32| {
            move |row: &Row| (0..m + 2).any(|i| bits >> i & 1 == 1 && *row == atom(i as u64))
        };
        for bits in 0..1u32 << (m + 2) {
            assert_eq!(
                merged.eval(&holds(bits)),
                direct.eval(&holds(bits)),
                "{m} {bits:b}"
            );
        }
        assert!(merged == direct, "{m}: {merged:?} is not {direct:?}");
    }
}

/// One list built on one thread by several routes is one cell (PROOF-lists-opposite-one-cell):
/// the literals of its blocks added in two orders, a literal or a whole block dropped by a
/// restriction (so that the blocks on either side join, `list::finish`), and the branch of a
/// list's first node (`Bdd::view`). Each route makes its cells through `list::cell`, whose table
/// holds the one live cell of a block and two children, and gives the treap of its blocks its
/// one shape; so the lists compare by ids in `Part::lists_opposite`, never by contents.
#[test]
fn one_list_built_by_several_routes_on_one_thread_is_one_cell() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let a: [Part<Row>; 10] = std::array::from_fn(|i| Part::literal(atom(i as u64)));
    let x = atom(8);
    // Blocks {a0, a1} true, {!a2, !a3} false, {a4, a5} true, {!a6, !a7} false, otherwise true.
    let tail = |p: &Part<Row>| and(&a[2], &and(&a[3], &or(&a[4], &or(&a[5], p))));
    let list = or(&a[0], &or(&a[1], &tail(&and(&a[6], &a[7]))));
    let reversed = or(
        &or(&a[1], &a[0]),
        &and(
            &and(&a[3], &a[2]),
            &or(&or(&a[5], &a[4]), &and(&a[7], &a[6])),
        ),
    );
    let not_x = |b: &Row| (*b == x).then_some(false);
    let x_taken = |b: &Row| (*b == x).then_some(true);
    let routes = [
        reversed,
        // `a8` dropped from the first block and from the last.
        or(&a[8], &list).restrict(&not_x),
        or(&a[0], &or(&a[1], &tail(&and(&a[6], &and(&a[7], &a[8]))))).restrict(&x_taken),
        // The block {!a8} dropped, so that {a0} and {a1} join, then {!a2} and {!a3}.
        or(&a[0], &and(&a[8], &or(&a[1], &tail(&and(&a[6], &a[7]))))).restrict(&x_taken),
        or(
            &a[0],
            &or(
                &a[1],
                &and(
                    &a[2],
                    &or(
                        &a[8],
                        &and(&a[3], &or(&a[4], &or(&a[5], &and(&a[6], &a[7])))),
                    ),
                ),
            ),
        )
        .restrict(&not_x),
        // The list after the first node `a9`, whose block of one literal is first.
        {
            let Part::Bdd(b) = and(&a[9], &list) else {
                panic!("a list")
            };
            let (_, hi, lo) = b.view().expect("a list has a first node");
            assert!(matches!(lo, Bdd::Leaf(false)), "{lo:?}");
            Part::Bdd(hi.clone())
        },
        list.not().not(),
    ];
    let Part::Bdd(Bdd::List(c, v)) = &list else {
        panic!("a list: {list:?}")
    };
    assert_eq!(c.len, 4, "{list:?}");
    for (i, r) in routes.iter().enumerate() {
        let Part::Bdd(b @ Bdd::List(d, w)) = r else {
            panic!("route {i}: a list: {r:?}")
        };
        assert!(r == &list, "route {i}: {r:?} is not {list:?}");
        assert!(b.cells_are_sound(), "route {i}: {r:?}");
        assert!(
            Arc::ptr_eq(c, d) && v == w,
            "route {i}: one list in two cells, {} and {}",
            c.id,
            d.id
        );
    }
}

/// Parts built on one thread and met on another: each thread has its own tables of cells, so
/// the complement of a literal taken there is a cell of that thread, and a list rebuilt there
/// is a second cell of the same contents. Both are still found complements of what was built
/// here (`Part::lists_opposite`). Before, the choice on `a` below, built here, was kept as an
/// expression when met on another thread, as the scaling checks meet their inputs.
#[test]
fn parts_built_on_one_thread_meet_on_another_in_their_one_form() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let [a, d, p, q, r, s, t, u, v] = [0, 1, 2, 3, 4, 5, 6, 7, 8].map(|i| Part::literal(atom(i)));
    // Case IV of `a_meet_of_choices_whose_branches_meet_to_one_set_is_that_set`.
    let (w, z) = (xor_by_or(&r, &s), xor_by_or(&t, &u));
    let (ad, nad) = (and(&a, &d), and(&a.not(), &d));
    let left = or(&and(&a, &or(&ad, &w)), &and(&a.not(), &or(&nad, &z)));
    let right = or(
        &and(&a, &or(&ad, &w.not())),
        &and(&a.not(), &or(&nad, &z.not())),
    );
    // A list that is no literal and no chain, and its complement, made here.
    let l = or(&and(&p, &q), &v);
    assert!(
        matches!(&l, Part::Bdd(b) if b.as_literal().is_none()),
        "{l:?}"
    );
    let not_l = l.not();
    let na = a.not();
    std::thread::scope(|scope| {
        scope
            .spawn(|| {
                let Part::Bdd(x) = &a else {
                    panic!("a literal is a list")
                };
                let Part::Bdd(y) = &na else {
                    panic!("a literal is a list")
                };
                assert!(Part::lists_opposite(x, y) && Part::lists_opposite(y, x));
                assert!(!Part::lists_opposite(x, x));
                let again = or(&and(&p, &q), &v);
                let (Part::Bdd(x), Part::Bdd(y)) = (&again, &not_l) else {
                    panic!("lists")
                };
                assert!(Part::lists_opposite(x, y) && Part::lists_opposite(y, x));
                let Part::Bdd(l) = &l else { panic!("a list") };
                assert!(!Part::lists_opposite(x, l));
                assert_eq!(or(&again, &not_l).is_leaf(), Some(true));
                let merged = and(&left, &right);
                assert!(merged == d, "{merged:?} is not {d:?}");
            })
            .join()
            .unwrap()
    });
}

/// Case I with a list condition that is no literal (CANON-list-absorb).
#[test]
fn a_choice_on_a_list_condition_whose_branches_cover_everything_is_the_leaf() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let [p, q, r, b, d, s, t] = [0, 1, 2, 3, 4, 5, 6].map(|i| Part::literal(atom(i)));
    let l = or(&and(&p, &q), &r);
    assert!(matches!(l, Part::Bdd(_)));
    let w = xor_by_or(&s, &t);
    let (x, y) = (or(&l, &b), or(&l.not(), &d));
    let half = |w: &Part<Row>| or(&and(&l, &and(&x, w)), &and(&l.not(), &and(&y, w)));
    let merged = or(&half(&w), &half(&w.not()));
    let holds = |bits: u32| move |row: &Row| (0..7).any(|i| bits >> i & 1 == 1 && *row == atom(i));
    assert!((0..128).all(|bits| merged.eval(&holds(bits))));
    assert_eq!(merged.is_leaf(), Some(true), "{merged:?}");
}

/// The cases of `Bdd::absorbed` (CANON-list-absorb): `f` implies `g`, so `f & g` is `f` and
/// `f | g` is `g`, in either order of the operands, where neither is a chain. Case A, a literal
/// added to the first block (first value `true`, and its complement, first value `false`), and
/// case B, a block put first (both values). Each result is checked on every setting, and the
/// lists built on another thread, compared there by contents, give the same.
#[test]
fn a_list_that_implies_another_as_their_blocks_show_absorbs_it() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let [p, q, r, b] = [0, 1, 2, 3].map(|i| Part::literal(atom(i)));
    let lists = |p: &Part<Row>, q: &Part<Row>, r: &Part<Row>, b: &Part<Row>| {
        let l = or(&and(p, q), r);
        let not_l = l.not();
        // `l` has the first value `true`: `l|b` adds `b` to its first block (case A); `!l`
        // has `false`: `!l|b` puts `{b}` first (case B), and `l & !b` is its complement.
        let pairs = [
            (l.clone(), or(&l, b)),
            (not_l.clone(), or(&not_l, b)),
            (and(&l, &b.not()), l.clone()),
            (and(&not_l, &b.not()), not_l.clone()),
        ];
        for (f, g) in &pairs {
            for part in [f, g] {
                let Part::Bdd(x) = part else {
                    panic!("{part:?} is a list")
                };
                assert!(!x.is_chain(Op::And) && !x.is_chain(Op::Or), "{x:?}");
            }
        }
        pairs
    };
    let pairs = lists(&p, &q, &r, &b);
    let holds = |bits: u32| move |row: &Row| (0..4).any(|i| bits >> i & 1 == 1 && *row == atom(i));
    for (f, g) in &pairs {
        for bits in 0..16 {
            assert!(
                !f.eval(&holds(bits)) || g.eval(&holds(bits)),
                "{f:?} implies {g:?}"
            );
        }
        assert!(and(f, g) == *f && and(g, f) == *f, "{f:?} & {g:?}");
        assert!(or(f, g) == *g && or(g, f) == *g, "{f:?} | {g:?}");
    }
    std::thread::scope(|scope| {
        scope
            .spawn(|| {
                let [p2, q2, r2, b2] = [0, 1, 2, 3].map(|i| Part::literal(atom(i)));
                for ((f, g), (f2, g2)) in pairs.iter().zip(lists(&p2, &q2, &r2, &b2)) {
                    assert!(and(f, &g2) == *f && or(&f2, g) == *g, "{f:?}, {g:?}");
                }
            })
            .join()
            .unwrap()
    });
}

/// A list that implies another where the blocks show it in no case of `Bdd::absorbed`: a
/// literal added to the last block, not the first. The meet and union are kept as made, and
/// still take the right value at every setting.
#[test]
fn a_list_implied_through_a_later_block_is_kept_and_right() {
    let and = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::And);
    let or = |p: &Part<Row>, q: &Part<Row>| p.zip(q, Op::Or);
    let [p, q, r, s] = [0, 1, 2, 3].map(|i| Part::literal(atom(i)));
    let l = or(&and(&p, &q), &r);
    let f = or(&and(&and(&p, &q), &s), &r);
    let holds = |bits: u32| move |row: &Row| (0..4).any(|i| bits >> i & 1 == 1 && *row == atom(i));
    for (u, v) in [(and(&f, &l), &f), (or(&f, &l), &l)] {
        assert!(
            (0..16).all(|bits| u.eval(&holds(bits)) == v.eval(&holds(bits))),
            "{u:?}"
        );
    }
}

/// A meet of `m` literals and a meet of two of them: the long meet implies the short (case A,
/// first value `false`), so their union is the short meet and their meet the long.
#[test]
fn a_long_meet_and_a_meet_of_two_of_its_literals_absorb() {
    let long = Part::Bdd(meet(40000, 8));
    let short = Part::Bdd(meet(40003, 2));
    assert!(long.zip(&short, Op::Or) == short && short.zip(&long, Op::Or) == short);
    assert!(long.zip(&short, Op::And) == long && short.zip(&long, Op::And) == long);
}

/// The same over morphisms: a set equal to all morphisms is `decidable()` (CANON-list-absorb).
#[test]
fn a_morphism_choice_on_a_list_condition_covering_everything_is_decidable() {
    let m = |i: i64| {
        let l = Type::lit(&Value::Int(i)).unwrap();
        Type::morphism(l.clone(), l, Type::int())
    };
    let (mp, mq, mr, mb, md, ms, mt) = (m(0), m(1), m(2), m(3), m(4), m(5), m(6));
    let all = Type::universe(crate::types::Universe::Morphism);
    let not = |t: &Type| &all - t;
    let ml = &(&mp & &mq) | &mr;
    let mw = &(&ms & &not(&mt)) | &(&not(&ms) & &mt);
    let (mx, my) = (&ml | &mb, &not(&ml) | &md);
    let mhalf = |w: &Type| &(&ml & &(&mx & w)) | &(&not(&ml) & &(&my & w));
    let merged = &mhalf(&mw) | &mhalf(&not(&mw));
    assert!(merged.subtype(&all) && all.subtype(&merged));
    assert!(merged.decidable());
}

/// The members of the order and `Debug` families of parts, expressions and diagrams that only
/// delegate, which no caller in the workspace calls directly (llvm-cov over the whole local
/// suite, TEST-types-unreached-paths-2): `partial_cmp` is `Some` of `cmp` and `==` is `cmp`
/// giving `Equal`, as `Ord` requires; and the text `{:?}` writes for each is the text the part
/// holding it writes for it, which `debug_samples` holds to the derived `Debug`s.
#[test]
fn the_delegating_orders_and_texts_of_parts_agree_with_what_they_delegate_to() {
    let lit = |i: u64| Part::literal(atom(i));
    let xor = |p: Part<Row>, q: Part<Row>| {
        p.zip(&q.not(), Op::And)
            .zip(&p.not().zip(&q, Op::And), Op::Or)
    };
    let kept = xor(lit(0), lit(2)).zip(&xor(lit(1), lit(3)), Op::And);
    let Part::Expr(e) = &kept else {
        panic!("{kept:?} is kept as an expression")
    };
    let parts = [lit(0), lit(1), lit(0).zip(&lit(1), Op::Or), kept.clone()];
    for p in &parts {
        for q in &parts {
            assert_eq!(p.partial_cmp(q), Some(p.cmp(q)), "{p:?}, {q:?}");
            assert_eq!(p == q, p.cmp(q) == Ordering::Equal, "{p:?}, {q:?}");
        }
    }
    let bdds: Vec<Bdd<Row>> = (0..3).map(|i| Bdd::literal(atom(i))).collect();
    for b in &bdds {
        for c in &bdds {
            assert_eq!(b.partial_cmp(c), Some(b.cmp(c)), "{b:?}, {c:?}");
        }
    }
    let other = xor(lit(4), lit(5));
    let Part::Expr(f) = &other else {
        panic!("{other:?} is kept as an expression")
    };
    for (x, y) in [(e, e), (e, f), (f, e)] {
        let (px, py) = (Part::Expr(x.clone()), Part::Expr(y.clone()));
        assert_eq!(x.partial_cmp(y), Some(x.cmp(y)), "{px:?}, {py:?}");
    }
    // The diagram of one literal is its node with the leaves `true` and `false` below it.
    assert_eq!(
        format!("{:?}", lit(0)),
        format!("Bdd(Node({:?}, true, false))", atom(0))
    );
    // The diagram alone, without the part around it.
    let Part::Bdd(b) = lit(0) else {
        panic!("one literal is a diagram")
    };
    assert_eq!(
        format!("{b:?}"),
        format!("Node({:?}, true, false)", atom(0))
    );
}

/// `Part::connect` keeps the value of the unfolded expression `a | b` or `a & b` (that is, of
/// its operands joined by `||` or `&&`), on random parts with leaves mixed in, at every
/// assignment of the six atoms.
#[test]
fn connecting_keeps_the_value_of_the_unfolded_expression() {
    let (mut rng, _) = Rng::fresh("connecting_keeps_the_value_of_the_unfolded_expression");
    let operand = |rng: &mut Rng| match rng.below(4) {
        0 => Part::Bdd(Bdd::Leaf(true)),
        1 => Part::Bdd(Bdd::Leaf(false)),
        _ => random(rng, 2),
    };
    let mut folded = 0;
    for _ in 0..2000 {
        let (a, b) = (operand(&mut rng), operand(&mut rng));
        for op in [Op::Or, Op::And] {
            let or = matches!(op, Op::Or);
            let new = Part::connect(op, a.clone(), b.clone());
            if !matches!(new, Part::Expr(_)) {
                folded += 1;
            }
            for set in 0..64u32 {
                let holds = |t: &Row| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i));
                let old = if or {
                    a.eval(&holds) || b.eval(&holds)
                } else {
                    a.eval(&holds) && b.eval(&holds)
                };
                assert_eq!(new.eval(&holds), old, "{a:?} or {or} {b:?}");
            }
        }
    }
    assert!(folded > 1000, "{folded} folded");
}

/// The set of the literals `x_{base + k}`, `k < m`, each with value `true`.
fn literals(base: u64, m: u64) -> Arc<set::Set<Row>> {
    let mut keys: Vec<_> = (0..m).map(|k| (atom(base + k), true)).collect();
    keys.sort();
    set::from_sorted(keys).expect("non-empty")
}

#[test]
fn the_rest_of_two_sequences_orders_the_shorter_first() {
    // On disjoint atoms, so that no subtree of one is a node of the other: the table keeps one
    // node for each set, and a shared subtree is passed over whole, reading no key.
    let (long, short) = (literals(0, 3), literals(10, 2));
    let ends = |a: &set::Set<Row>, b: &set::Set<Row>| {
        let mut rest = Rest::new(a, b);
        let mut keys = 0;
        loop {
            match rest.next(|_, _| false) {
                Ok(_) => keys += 1,
                Err(o) => return (keys, o),
            }
        }
    };
    assert_eq!(ends(&long, &short), (2, Ordering::Greater));
    assert_eq!(ends(&short, &long), (2, Ordering::Less));
    // One node on both sides is passed over whole.
    assert_eq!(ends(&short, &short), (0, Ordering::Equal));
}

#[test]
fn leaves_are_opposite_only_to_the_other_leaf() {
    let (t, f, l) = (Bdd::<Row>::Leaf(true), Bdd::Leaf(false), meet(0, 2));
    assert!(Part::lists_opposite(&t, &f));
    assert!(!Part::lists_opposite(&t, &t));
    assert!(!Part::lists_opposite(&l, &f));
    assert!(!Part::lists_opposite(&t, &l));
}

#[test]
fn expressions_are_equal_exactly_when_they_compare_equal() {
    let (a, b) = (Part::literal(atom(0)), Part::literal(atom(1)));
    let (Part::Expr(e), Part::Expr(f)) = (
        Part::connect(Op::Or, a.clone(), Part::not_expr(b.clone())),
        Part::connect(Op::And, a, b),
    ) else {
        panic!("connect makes expressions")
    };
    assert!(*e == *e.clone());
    assert!(*e != *f);
}

#[test]
fn atoms_mapped_keep_the_value_at_the_mapped_assignment() {
    // Every part of `random_expr` over `x_0 … x_5`, leaves and expressions among them, mapped
    // by `x_i ↦ x_{(i + 2) mod 6}`, against the part read at the assignment moved back.
    let atoms: Vec<Row> = (0..6).map(atom).collect();
    let index = |a: &Row| atoms.iter().position(|b| b == a).expect("one of x_0 … x_5");
    let map = |a: &Row| atoms[(index(a) + 2) % 6].clone();
    let mut rng = Rng::new(7);
    let mut pool = Vec::new();
    let mut parts = vec![Part::leaf(true), Part::leaf(false)];
    parts.extend((0..300).map(|_| random_expr(&mut rng, 4, &mut pool)));
    for p in &parts {
        let q = p.map_atoms(&map);
        for bits in 0u32..64 {
            let at = |a: &Row| bits & (1 << index(a)) != 0;
            let moved = |a: &Row| at(&map(a));
            assert_eq!(q.eval(&at), p.eval(&moved), "bits {bits:06b}");
        }
    }
}

#[test]
fn a_clause_reads_a_shared_operand_once() {
    let (l0, l1, l2) = (
        Part::literal(atom(0)),
        Part::literal(atom(1)),
        Part::literal(atom(2)),
    );
    assert_eq!(Part::<Row>::leaf(false).clause(), None);
    let e = Part::not_expr(l1);
    let p = Part::connect(Op::And, e.clone(), Part::connect(Op::And, e, l2));
    assert_eq!(p.clause(), Some((vec![atom(2)], vec![atom(1)])));
    let q = Part::connect(Op::And, Part::not_expr(l0), Part::literal(atom(3)));
    assert_eq!(q.clause(), Some((vec![atom(3)], vec![atom(0)])));
    // Item TEST-kernel-unreached-paths-4: the complement, kept as an expression, of a refused
    // literal takes its atom. Product code makes `Form::Not` only of an expression (`negate`),
    // so only a test reaches this arm.
    let r = Part::connect(
        Op::And,
        Part::not_expr(Part::literal(atom(4)).not()),
        Part::literal(atom(5)),
    );
    assert_eq!(r.clause(), Some((vec![atom(4), atom(5)], vec![])));
}

/// Item TEST-kernel-unreached-paths-13: the complement of `!x_0` kept as an expression of the
/// literal `x_0`, a form only tests make (product code makes `Form::Not` only of an expression,
/// `Connect::negate`), is `x_0`, kept as a complement that is no expression (`Expr::link`), the
/// same when asked again; made from the form as written (`Part::of_form`), it is `x_0` too.
#[test]
fn the_complement_of_the_complement_of_a_literal_kept_as_an_expression_is_the_literal() {
    let l0 = Part::literal(atom(0));
    let e = Part::not_expr(l0.clone());
    assert_eq!(e.not(), l0);
    let Part::Expr(x) = &e else {
        unreachable!("`Part::not_expr` makes an expression")
    };
    assert_eq!(x.complement.get(), Some(&l0), "the complement kept");
    assert_eq!(e.not(), l0, "the complement kept, read again");
    assert_eq!(Part::of_form(Form::Not(l0.clone())).not(), l0);
}

/// Item TEST-kernel-unreached-paths-13: the operand of a form `Not` is held by it, and nothing
/// else is (`Form::holds`, whose one caller asks it only of an `Or` or an `And`).
#[test]
fn a_form_not_holds_its_operand_alone() {
    let e = Part::not_expr(Part::literal(atom(0)));
    let n = Part::not_expr(e.clone());
    let (Part::Expr(x), Part::Expr(y)) = (&e, &n) else {
        unreachable!("`not_expr` makes an expression");
    };
    assert!(y.form().holds(x));
    assert!(!y.form().holds(y));
    assert!(!x.form().holds(x), "the operand of `x` is a literal");
}

#[test]
fn disjoint_disjuncts_read_a_shared_union_once() {
    let n = |i| Part::not_expr(Part::literal(atom(i)));
    let e = Part::connect(Op::Or, n(0), n(1));
    let p = Part::connect(
        Op::Or,
        e.clone(),
        Part::connect(Op::Or, e, Part::literal(atom(2))),
    );
    assert_eq!(p.disjoint_disjuncts().map(|v| v.len()), Some(3));
}

#[test]
fn the_complement_of_an_expression_flips_the_value_taken_toward() {
    // `!(x_0 | !x_1)` is `!x_0 & x_1`: toward `true` only `x_1` is given.
    let p = Part::not_expr(Part::connect(
        Op::Or,
        Part::literal(atom(0)),
        Part::not_expr(Part::literal(atom(1))),
    ));
    let mut seen = DigestSet::default();
    let mut given = Vec::new();
    p.taken_toward(true, &mut seen, &mut |a| given.push(a.clone()));
    assert_eq!(given, vec![atom(1)]);
}

#[test]
fn the_exclusive_or_of_no_atoms_is_its_constant() {
    for c in [false, true] {
        assert_eq!(Part::<Row>::xor(None, c), Part::leaf(c));
    }
}

#[test]
fn a_union_of_no_literals_is_false_and_of_an_atom_both_ways_is_left_to_zip() {
    assert_eq!(Part::<Row>::union_of_literals(&[]), Some(Part::leaf(false)));
    let (x, nx) = (Part::literal(atom(0)), Part::literal(atom(0)).not());
    let y = Part::literal(atom(1));
    assert_eq!(Part::union_of_literals(&[&x, &y, &nx]), None);
}

/// The calls `Bdd::reaching` makes, found by walking every path of `b` ([`Bdd::branch`]): each
/// node from whose `hi` a chain of `lo` edges reaches `true`, with the atoms taken on the path
/// to it. The walk is over paths, not nodes, so it holds for any diagram.
fn reaching_by_paths(b: &Bdd<Row>, taken: &mut Vec<Row>, out: &mut Vec<String>) {
    let Ok((_, a, hi, lo)) = b.branch() else {
        return;
    };
    let mut end = hi;
    while let Ok((_, _, _, l)) = end.branch() {
        end = l;
    }
    if *end == Bdd::Leaf(true) {
        out.push(format!("{a:?} after {taken:?}"));
    }
    taken.push(a.clone());
    reaching_by_paths(hi, taken, out);
    taken.pop();
    reaching_by_paths(lo, taken, out);
}

/// `reaching` passes `f` each node that is the last `hi` taken on a path to `true`, with the
/// atoms taken before it, as a walk of every path finds; it stops at the first `false` of `f`
/// and gives `false`; and on a leaf it calls nothing and gives `true`. Its `seen` and joined
/// states are unreachable (proof at `Bdd::reaching`); the leaf and a stop by `f` were never
/// reached by the kernel's tests before (cover8): its one caller's `f` always holds.
#[test]
fn reaching_visits_the_nodes_a_walk_of_every_path_finds() {
    for v in [false, true] {
        let mut calls = 0;
        assert!(Bdd::<Row>::Leaf(v).reaching(
            (),
            |_, _| (),
            |_, _| {
                calls += 1;
                false
            }
        ));
        assert_eq!(calls, 0);
    }
    let (mut rng, _) = Rng::fresh("reaching_visits_the_nodes_a_walk_of_every_path_finds");
    let (mut lists, mut stopped) = (0, 0);
    for _ in 0..800 {
        let Part::Bdd(b) = random(&mut rng, 6) else {
            continue;
        };
        let mut expected = Vec::new();
        reaching_by_paths(&b, &mut Vec::new(), &mut expected);
        let mut got = Vec::new();
        let take = |s: &Vec<Row>, a: &Row| {
            let mut s = s.clone();
            s.push(a.clone());
            s
        };
        assert!(b.reaching(Vec::new(), take, |a, s| {
            got.push(format!("{a:?} after {s:?}"));
            true
        }));
        expected.sort();
        got.sort();
        assert_eq!(got, expected, "{b:?}");
        lists += 1;
        // Stopped at its `k`-th call, `reaching` gives `false` after exactly `k` calls.
        for k in 1..=expected.len() {
            let mut calls = 0;
            let all = b.reaching(Vec::new(), take, |_, _| {
                calls += 1;
                calls < k
            });
            assert!(!all && calls == k, "{b:?} stopped at call {k}");
            stopped += 1;
        }
    }
    eprintln!("{lists} lists, {stopped} stops");
    // Each kind on a list built to give it, whatever the draws met: `a0 | a1` reaches `true`
    // from both nodes, so `f` is called twice and can stop at either.
    let (a0, a1) = (Bdd::literal(atom(0)), Bdd::literal(atom(1)));
    let b = a0.zip_chain(&a1, Op::Or).expect("a chain joined");
    let mut calls = 0;
    assert!(b.reaching(
        (),
        |_, _| (),
        |_, _| {
            calls += 1;
            true
        }
    ));
    assert_eq!(calls, 2);
}

/// `x_i | x_(i+1)`, kept as an expression.
fn or_expr(i: u64) -> Part<Row> {
    Part::connect(Op::Or, Part::literal(atom(i)), Part::literal(atom(i + 1)))
}

/// The complement as kept of `!q` made as an expression, whose own complement is not yet
/// made, is `q`, read from its form (cover8; not reached by the kernel's tests before).
#[test]
fn the_complement_as_kept_of_a_not_is_its_operand() {
    let q = or_expr(0);
    let n = Part::not_expr(q.clone());
    let Part::Expr(e) = &n else {
        panic!("`!q` is an expression")
    };
    assert!(
        e.known().is_none(),
        "the complement of `!q` is not yet made"
    );
    assert_eq!(Part::not_as_kept(&n), Some(q));
}

/// `a | b` is a choice as kept only when exactly one condition fits (`choice_of_as_kept`): two
/// chains with two literals taken opposite ways, and two meets of expressions each with its
/// complement in the other, give `None`, as do two meets with no complement between them;
/// one condition gives the choice. The cases with two conditions or none were not reached by
/// the kernel's tests before (cover8).
#[test]
fn a_union_with_two_conditions_or_none_is_no_choice_as_kept() {
    let lit = |i: u64, t: bool| {
        let l = Bdd::literal(atom(i));
        if t { l } else { l.not() }
    };
    let chain =
        |x: Bdd<Row>, y: Bdd<Row>| Part::Bdd(x.zip_chain(&y, Op::And).expect("a chain met"));
    // Chains: `x0&x1 | !x0&x1` chooses on `x0`; `x0&x1 | !x0&!x1` on two atoms.
    let one = Part::choice_of_as_kept(
        &chain(lit(0, true), lit(1, true)),
        &chain(lit(0, false), lit(1, true)),
    );
    let x0 = Part::Bdd(lit(0, true));
    let x1 = Part::Bdd(lit(1, true));
    assert_eq!(one, Some((x0, x1.clone(), x1)));
    let two = Part::choice_of_as_kept(
        &chain(lit(0, true), lit(1, true)),
        &chain(lit(0, false), lit(1, false)),
    );
    assert_eq!(two, None);
    // Meets of expressions.
    let (p, q) = (or_expr(0), or_expr(2));
    let meet = |a: &Part<Row>, b: &Part<Row>| Part::connect(Op::And, a.clone(), b.clone());
    let (np, nq) = (Part::not_expr(p.clone()), Part::not_expr(q.clone()));
    assert_eq!(
        Part::choice_of_as_kept(&meet(&p, &q), &meet(&np, &q)),
        Some((p.clone(), q.clone(), q.clone()))
    );
    assert_eq!(
        Part::choice_of_as_kept(&meet(&p, &q), &meet(&np, &nq)),
        None
    );
    let (r, s) = (or_expr(4), or_expr(6));
    assert_eq!(Part::choice_of_as_kept(&meet(&p, &q), &meet(&r, &s)), None);
}

/// The walks that keep a `seen` set pass over what they met before, and stop when `f` fails
/// (cover8; none of these steps was reached by the kernel's tests before): a union whose two
/// operands are one expression gives that expression's atoms once; a list walked a second time
/// toward `true` with the same set gives nothing; and the walk of atoms over shared set nodes
/// gives `false` at the first atom `f` refuses.
#[test]
fn walks_pass_over_what_they_met_and_stop_when_f_fails() {
    let e = or_expr(0);
    let twice = Part::connect(Op::Or, e.clone(), e);
    assert_eq!(twice.union_rows(), Some(vec![atom(0), atom(1)]));
    let x: Vec<Bdd<Row>> = (0..3).map(|i| Bdd::literal(atom(i))).collect();
    let chain = x[0].zip_chain(&x[1], Op::Or).expect("a chain joined");
    let chain = chain.zip_chain(&x[2], Op::Or).expect("a chain joined");
    let mut seen = DigestSet::default();
    let mut given = Vec::new();
    chain.taken_toward(true, &mut seen, &mut |a| given.push(a.clone()));
    assert_eq!(given.len(), 3, "{given:?}");
    chain.taken_toward(true, &mut seen, &mut |a| given.push(a.clone()));
    assert_eq!(
        given.len(),
        3,
        "a second walk with the same set gives nothing"
    );
    let mut calls = 0;
    let all = chain.atoms_unseen(
        &mut DigestSet::default(),
        &mut |_| {
            calls += 1;
            false
        },
        true,
    );
    assert!(!all && calls == 1);
}

/// A part goes before itself: of equal digests the order of contents decides, and a part is
/// equal to itself (cover8: the tie was reached only in the short-addresses build).
#[test]
fn a_part_goes_before_itself() {
    let (mut rng, _) = Rng::fresh("a_part_goes_before_itself");
    for _ in 0..50 {
        let p = random_expr(&mut rng, 4, &mut Vec::new());
        assert!(p.before(&p), "{p:?}");
    }
}

/// Item TEST-kernel-unreached-paths-15 (`Connect::negate`, a choice whose complement is no
/// expression): `c&x | !c&x` built with `Part::connect` is kept as an expression, a choice on
/// `c` whose branches are equal, so its complement `choose(c, !x, !x)` is `!x`, a diagram, and
/// no source is set on it. 40,000 drawn expressions (`random_expr`, depth 5, seeds 1 to 400,
/// 100 draws each) met no such case. Control: the choice `c&x | !c&y` has an expression as its
/// complement.
#[test]
fn a_choice_with_equal_branches_has_a_diagram_as_complement() {
    let l = |i: u64| Part::literal(atom(i));
    let choice = |x: Part<Row>, y: Part<Row>| {
        Part::connect(
            Op::Or,
            Part::connect(Op::And, l(0), x),
            Part::connect(Op::And, l(0).not(), y),
        )
    };
    let p = choice(l(1), l(1));
    assert!(matches!(p, Part::Expr(_)), "{p:?}");
    let n = p.not();
    assert!(matches!(n, Part::Bdd(_)), "{n:?}");
    let flipped: Vec<bool> = values(&p).into_iter().map(|v| !v).collect();
    assert_eq!(values(&n), flipped);
    assert_eq!(values(&n), values(&l(1).not()));
    let control = choice(l(1), l(2));
    let m = control.not();
    assert!(matches!(m, Part::Expr(_)), "{m:?}");
    let flipped: Vec<bool> = values(&control).into_iter().map(|v| !v).collect();
    assert_eq!(values(&m), flipped);
}

/// An expression that stays one when a round rebuilds the part: the union of two meets of two
/// atoms each, which is no chain under `|` ([`pinned_one_a_round`]), the atoms from `at`.
fn opaque(at: u64) -> Part<Row> {
    Part::connect(Op::Or, Part::Bdd(meet(at, 2)), Part::Bdd(meet(at + 2, 2)))
}

/// [`Part::settle_by`] round by round: the part settled, the steps of [`Part::pins_by`] in all
/// (`SETTLE_WORK`) and the pins of each round. For [`Pins::Cut`] and [`Pins::Carried`] it
/// checks that no round costs more than the first, as a round rebuilds the part with constants
/// put in, which leaves no more expressions: the work is at most the rounds, plus the last
/// round that finds no pin, times the first round's.
fn settled_by(p: &Part<Row>, how: Pins) -> (Part<Row>, u64, Vec<usize>) {
    SETTLE_WORK.with(|w| w.set(0));
    let (mut q, mut rounds, mut first) = (p.clone(), Vec::new(), None);
    loop {
        let pins = q.pins_by(how);
        first.get_or_insert_with(|| SETTLE_WORK.with(|w| w.get()));
        if pins.is_empty() {
            break;
        }
        rounds.push(pins.len());
        q = q.substitute_all(&pins);
    }
    let work = SETTLE_WORK.with(|w| w.get());
    let first = first.expect("one round at least");
    if how != Pins::Required {
        assert!(
            work <= (rounds.len() as u64 + 1) * first,
            "{how:?}: work {work} over {} rounds of {first}",
            rounds.len() + 1
        );
    }
    (q, work, rounds)
}

/// [`settled_by`] with [`Pins::Cut`], checked against [`Pins::Carried`] (the same part and
/// rounds, and no more work) and, when `scans`, against [`Part::settle_by_scans`]. Checks
/// that [`Pins::Required`] (Claude's A+B) gives the same part exactly when `a_plus_b_alike`
/// (asserted since cross-review XR-lazy-and-kernel-batch-1 round 2, Codex B3; it was printed).
/// Gives the cut's part, the cut's work, the carried work and the rounds.
fn settled_alike(
    p: &Part<Row>,
    scans: bool,
    a_plus_b_alike: bool,
    what: &str,
) -> (Part<Row>, u64, u64, Vec<usize>) {
    let (cut, cut_work, rounds) = settled_by(p, Pins::Cut);
    let (carried, carried_work, carried_rounds) = settled_by(p, Pins::Carried);
    assert!(cut == carried, "{what}: the cut changed the part");
    assert_eq!(rounds, carried_rounds, "{what}");
    assert!(
        cut_work <= carried_work,
        "{what}: {cut_work} > {carried_work}"
    );
    if scans {
        assert!(cut == p.settle_by_scans(), "{what}: not the scans' part");
    }
    let (required, _, _) = settled_by(p, Pins::Required);
    assert_eq!(required == cut, a_plus_b_alike, "{what}: A+B's part");
    (cut, cut_work, carried_work, rounds)
}

/// Codex's witness (cross-review XR-lazy-and-kernel-batch-1, round 1): `p = x | y`,
/// `u = p & A`, `root = ((u | B) & (u | !p)) & p`. The walk finds `u` shared, then `p`. A round
/// cannot pin `u`: neither trial value makes the root `false` while `p` is unknown. It pins
/// `p = true`, and the rebuild turns `u` into the diagram `A`, so the part settles to `A`. A
/// worklist that tried `u` again after the pin of `p` would pin `u = true` and settle to
/// `true`, another superset, and so does Claude's A+B ([`Pins::Required`]: `root = true`
/// requires `p`, and then `u | !p` requires `u`). So both change what `settle` gives, and are
/// not used.
#[test]
fn worklist_cannot_pin_an_expression_the_round_turns_into_a_bdd() {
    let lit = |i| Part::literal(atom(i));
    let p = Part::connect(Op::Or, lit(9500), lit(9501));
    let u = Part::connect(Op::And, p.clone(), lit(9502));
    let r = Part::connect(Op::Or, u.clone(), lit(9503));
    let s = Part::connect(Op::Or, u.clone(), Part::not_expr(p.clone()));
    let root = Part::connect(Op::And, Part::connect(Op::And, r, s), p.clone());
    let pins = root.pins();
    assert_eq!(pins.len(), 1, "{pins:?}");
    assert_eq!(pins.get(&p.id()), Some(&true));
    let (settled, _, _, rounds) = settled_alike(&root, true, false, "witness");
    assert!(settled == lit(9502), "{settled:?}");
    assert_eq!(rounds, vec![1]);
    let required = root.pins_by(Pins::Required);
    assert_eq!(required.get(&u.id()), Some(&true), "{required:?}");
    assert_eq!(root.settle_by(Pins::Required).is_leaf(), Some(true));
}

/// The And-path certificate of [`Pins::Cut`] fires only along unfixed `And`s: `e` is under `f`
/// (an `And`) and under an `Or`; `f`, found shared first, is pinned `true`, which leaves `e` no
/// unfixed `And` path to the root, and neither trial of `e` makes the root `false`. A cut that
/// took every upward path, or kept `f` as a path once fixed, would pin `e` too.
#[test]
fn the_and_path_certificate_stops_at_a_fixed_and_and_at_an_or() {
    let lit = |i| Part::literal(atom(i));
    let e = opaque(9600);
    let f = Part::connect(Op::And, lit(9610), e.clone());
    let left = Part::connect(Op::Or, f.clone(), lit(9611));
    let right = Part::connect(
        Op::And,
        f.clone(),
        Part::connect(Op::Or, e.clone(), lit(9612)),
    );
    let root = Part::connect(Op::And, left, right);
    let pins = root.pins();
    assert_eq!(pins.len(), 1, "{pins:?}");
    assert_eq!(pins.get(&f.id()), Some(&true));
    assert!(!pins.contains_key(&e.id()));
    // Phase A of [`Pins::Required`] stops at a fixed node as the round does (cross-review
    // XR-lazy-and-kernel-batch-1 round 2, Gemini B.4): before, it pinned `f` and then passed
    // `f = true`'s requirement on to `e` through the pin, and pinned `e` too.
    assert_eq!(root.pins_by(Pins::Required), pins);
    settled_alike(&root, true, true, "certificate");
}

/// The reduction from orthogonal vectors behind the conditional lower bound at
/// [`Part::settle`] (Gemini, cross-review XR-lazy-and-kernel-batch-1 rounds 1 and 2, with
/// Codex's round 2 correction), on raw parts: for lists `a` and `b` of vectors in `{0,1}^d`, no
/// vector of `b` zero, the part has a pin exactly when some `a_i . b_j = 0`, and then `settle`
/// does not return it. Every instance with `d = 2` and lists of 1 or 2 vectors, and with `d = 3`
/// and 2 and 2: this covers a coordinate node used by more than one `B_j` on NO instances, a
/// one-bit change from NO to YES, equal vectors, and a `b_j` with one coordinate (before the
/// coordinates are doubled, the case where sharing the double would be wrong).
#[test]
fn pins_exist_iff_the_two_vector_sets_have_an_orthogonal_pair() {
    let lit = |i| Part::literal(atom(i));
    let and = |a, b| Part::connect(Op::And, a, b);
    let or = |a, b| Part::connect(Op::Or, a, b);
    let part = |a: &[Vec<bool>], b: &[Vec<bool>], d: usize| {
        let s: Vec<Part<Row>> = (0..a.len() as u64)
            .map(|i| opaque(30_000 + 4 * i))
            .collect();
        // Each coordinate twice, at `k` and `k + d`, with its own guard `z_k`.
        let c: Vec<Part<Row>> = (0..2 * d)
            .map(|k| {
                let zero = (0..a.len()).filter(|&i| !a[i][k % d]);
                zero.fold(lit(31_000 + k as u64), |x, i| and(x, s[i].clone()))
            })
            .collect();
        let rows = b.iter().map(|v| {
            let ones = (0..2 * d).filter(|&k| v[k % d]).map(|k| c[k].clone());
            ones.reduce(or).expect("no vector of b is zero")
        });
        let guards = (0..a.len() as u64).map(|i| {
            let g = |e| or(s[i as usize].clone(), lit(32_000 + 2 * i + e));
            and(g(0), g(1))
        });
        (rows.chain(guards)).fold(lit(33_000), and)
    };
    let vectors = |d: usize, n: usize, bits: u32| -> Vec<Vec<bool>> {
        (0..n)
            .map(|i| (0..d).map(|k| (bits >> (i * d + k)) & 1 == 1).collect())
            .collect()
    };
    let mut cases = [0, 0];
    for (d, na, nb) in [(2, 1, 1), (2, 1, 2), (2, 2, 1), (2, 2, 2), (3, 2, 2)] {
        for x in 0..1u32 << (d * na) {
            for y in 0..1u32 << (d * nb) {
                let (a, b) = (vectors(d, na, x), vectors(d, nb, y));
                if b.iter().any(|v| v.iter().all(|&t| !t)) {
                    continue;
                }
                let yes = (a.iter()).any(|u| b.iter().any(|v| (0..d).all(|k| !(u[k] && v[k]))));
                let root = part(&a, &b, d);
                let pins = root.pins();
                let what = format!("a {a:?}, b {b:?}");
                assert_eq!(!pins.is_empty(), yes, "{what}: {pins:?}");
                assert_eq!(root.pins_by(Pins::Carried), pins, "{what}");
                assert_eq!(root.settle() != root, yes, "{what}");
                cases[yes as usize] += 1;
            }
        }
    }
    assert!(cases[0] > 0 && cases[1] > 0, "{cases:?}");
}

/// Codex's spine (cross-review XR-lazy-and-kernel-batch-1, round 1): `m` shared expressions,
/// each as `s_i | s_i` under one tree of unions, then `m` unions with atoms up to the root. No
/// trial pins anything. Carried, each trial `s_i = true` turns the spine above it `true` up to
/// the root, `Θ(m^2)` in all on `O(m)` nodes; with the polarity cut of [`Pins::Cut`], a
/// value that cannot make the root `false` (`true` under unions) is carried no higher and the
/// round is linear.
#[test]
fn a_spine_of_unions_is_tried_in_linear_work() {
    let spine = |m: usize| {
        let s = (0..m as u64).map(|j| {
            let x = opaque(20_000 + 4 * j);
            Part::connect(Op::Or, x.clone(), x)
        });
        let tree = s
            .reduce(|a, b| Part::connect(Op::Or, a, b))
            .expect("m is at least 1");
        (0..m as u64).fold(tree, |r, j| {
            Part::connect(Op::Or, r, Part::literal(atom(40_000 + j)))
        })
    };
    let mut last: Option<(u64, u64)> = None;
    for m in [64, 128, 256] {
        let (_, cut, carried, rounds) = settled_alike(&spine(m), m <= 64, true, "spine");
        assert!(rounds.is_empty(), "m = {m}: {rounds:?}");
        eprintln!("spine m = {m}: cut work {cut}, carried work {carried}");
        if let Some((c0, k0)) = last {
            assert!(cut as f64 <= 2.2 * c0 as f64, "m = {m}: cut {c0} to {cut}");
            assert!(
                carried as f64 >= 3.5 * k0 as f64,
                "m = {m}: carried {k0} to {carried}"
            );
        }
        last = Some((cut, carried));
    }
}

/// Gemini's `G_k` (cross-review XR-lazy-and-kernel-batch-1, round 1): `!s_0`, and for `k` from
/// 1 `!s_k | ((s_(k-1) | b_k) & !b_k)` with `b_k` an atom, and `s_k | d_k` beside each so that
/// every `s_k` is shared. `s_(k-1)` pinned `false` leaves `(s_(k-1) | b_k) & !b_k` unknown
/// until the rebuild makes it `b_k & !b_k = false`; only then does the trial `s_k = true` make
/// the root `false`. So `m` rounds of one pin each, each round `Θ(N)`: `Θ(N^2)` in all.
#[test]
fn gated_by_the_one_before_takes_a_round_a_pin() {
    let gated = |m: usize| {
        let s: Vec<Part<Row>> = (0..m as u64).map(|k| opaque(50_000 + 4 * k)).collect();
        let mut conj = vec![Part::not_expr(s[0].clone())];
        for k in 1..m {
            let b = 60_000 + k as u64;
            let or = Part::connect(Op::Or, s[k - 1].clone(), Part::literal(atom(b)));
            let g = Part::connect(Op::And, or, Part::Bdd(Bdd::literal(atom(b)).not()));
            conj.push(Part::connect(Op::Or, Part::not_expr(s[k].clone()), g));
        }
        for (k, sk) in s.iter().enumerate() {
            let d = Part::literal(atom(70_000 + k as u64));
            conj.push(Part::connect(Op::Or, sk.clone(), d));
        }
        conj.into_iter()
            .reduce(|a, b| Part::connect(Op::And, a, b))
            .expect("m is at least 1")
    };
    for m in [4, 16, 64] {
        let (_, cut, carried, rounds) = settled_alike(&gated(m), m <= 16, true, "G_k");
        assert_eq!(rounds, vec![1; m], "m = {m}");
        eprintln!("G_k m = {m}: cut work {cut}, carried work {carried}");
    }
}

/// Gemini's family against a worklist, at `K = S = n` (cross-review XR-lazy-and-kernel-batch-1,
/// round 1): `S` shared expressions under both `e_1 & … & e_S` and `e_1 | … | e_S`, the first
/// below a spine of `K` `And`s with `u_1, …, u_K`, and the `u_j` pinned one by one by the chain
/// of [`pinned_one_a_round`]. A worklist tries each `e_i` again after each pin of a `u_j`, each
/// time across the spine: `Θ(n^3)`. The rounds try each `e_i` once a round.
///
/// Measured with `Pins::Cut` (`SETTLE_WORK`, round 2 of that cross-review), for `n` = 8, 16, 32
/// and 64: the first round costs 432, 1136, 3312 and 10736, a ratio per doubling of 2.63, 2.92
/// and 3.24, rising toward 4, so `Θ(n^2)` a round, the `Θ(S · N)` of `Part::settle` with `S` and
/// `N` both `Θ(n)`; all rounds cost 1984, 7632, 26515 and 178679 over 6, 10, 13 and 26 rounds,
/// each round at most the first (the ratio of the whole to rounds times the first is 0.77, 0.67,
/// 0.62 and 0.64). The test asserts both: the first round within `7 · n^2`, and the whole within
/// rounds times the first.
#[test]
fn cubic_for_a_worklist() {
    let family = |n: usize| {
        let es: Vec<Part<Row>> = (0..n as u64).map(|i| opaque(80_000 + 4 * i)).collect();
        let us: Vec<Part<Row>> = (0..=n as u64).map(|j| opaque(90_000 + 4 * j)).collect();
        let and = |a, b| Part::connect(Op::And, a, b);
        let or = |a, b| Part::connect(Op::Or, a, b);
        let c = es.iter().cloned().reduce(and).expect("n is at least 1");
        let c2 = es.iter().cloned().reduce(or).expect("n is at least 1");
        let spine = (1..=n).fold(c, |r, j| and(r, us[j].clone()));
        let dead = or(spine, Part::literal(atom(99_000)));
        let dead2 = or(c2, Part::literal(atom(99_001)));
        let chain = (1..n).rev().fold(us[n].clone(), |rest, j| {
            and(or(us[j].clone(), Part::not_expr(us[j + 1].clone())), rest)
        });
        and(and(dead, dead2), chain)
    };
    for n in [8, 16, 32, 64] {
        let p = family(n);
        SETTLE_WORK.with(|w| w.set(0));
        p.pins();
        let first = SETTLE_WORK.with(|w| w.get());
        let (_, cut, carried, rounds) = settled_alike(&p, n <= 16, true, "K = S = n");
        eprintln!(
            "K = S = n = {n}: first round {first}, cut work {cut}, carried work {carried}, {} \
             rounds {rounds:?}",
            rounds.len()
        );
        assert!(first <= 7 * (n * n) as u64, "n = {n}: first round {first}");
        assert!(
            cut <= rounds.len() as u64 * first,
            "n = {n}: {cut} over {} rounds",
            rounds.len()
        );
    }
}

/// Codex's gated parities (cross-review XR-lazy-and-kernel-batch-1, round 1) on the diagrams
/// `pair(i) = (L_i, H_i)`: `E_i = L_i | H_i`, an expression, `F_i = L_i | (H_i & E_(i-1))`, and
/// the part `E_0 & F_1 & … & F_m & (E_m | g)`, `g` the atom `last`, each `E_i` built once (an
/// expression's id is new at each build, [`Part::made`], and sharing is by id), with the id of
/// `E_0`. Where `share_e0` is false, `F_1` takes an `E_0` built again, of another id, the
/// negative control of Codex's B5 (round 2): then no expression is shared.
fn gated_parities(
    pair: &dyn Fn(usize) -> (Part<Row>, Part<Row>),
    last: u64,
    m: usize,
    share_e0: bool,
) -> (Part<Row>, u64) {
    let e = |i: usize| {
        let (l, h) = pair(i);
        Part::connect(Op::Or, l, h)
    };
    let es: Vec<Part<Row>> = (0..=m).map(e).collect();
    let mut conj = vec![es[0].clone()];
    for i in 1..=m {
        let (l, h) = pair(i);
        let before = match (i, share_e0) {
            (1, false) => e(0),
            _ => es[i - 1].clone(),
        };
        conj.push(Part::connect(Op::Or, l, Part::connect(Op::And, h, before)));
    }
    conj.push(Part::connect(
        Op::Or,
        es[m].clone(),
        Part::literal(atom(last)),
    ));
    let part = conj
        .into_iter()
        .reduce(|a, b| Part::connect(Op::And, a, b))
        .expect("at least two conjuncts");
    (part, es[0].id())
}

/// The first round's pins of [`gated_parities`] on `pair`: `E_0 = true` by its id, and none
/// where `E_0` is built twice (Codex's B5 of round 2: the pin is checked by id, not counted).
fn first_pin_is_e0(pair: &dyn Fn(usize) -> (Part<Row>, Part<Row>), last: u64, m: usize) {
    let (p, e0) = gated_parities(pair, last, m, true);
    let pins = p.pins();
    assert_eq!(pins.len(), 1, "m = {m}: {pins:?}");
    assert_eq!(pins.get(&e0), Some(&true), "m = {m}: {pins:?}");
    let (p, _) = gated_parities(pair, last, m, false);
    assert!(p.pins().is_empty(), "m = {m}, E_0 built twice");
}

/// [`gated_parities`] as Codex gave them, `L_i = a_i & !b_i` and `H_i = !a_i & b_i` on two atoms
/// `a_i, b_i`. Only `E_0` is shared at first; each round pins one expression and its rebuild
/// exposes the next shared (how the rebuild does so is not inspected): `m + 1` rounds of one
/// pin each, and the rounds' work about `m^2`, each round over the whole part (measured
/// 2026-11-27: cut work 73, 541 and 6,733 at m 2, 8 and 32). A+B finds the same part in the
/// same rounds. Before 2026-11-27 this test built each `E_i` twice, so no `E_i` was shared and
/// the family pinned nothing; that 0 was the test's fault. The first round pins `E_0` by its
/// id, and with `E_0` built twice nothing ([`first_pin_is_e0`]).
#[test]
fn gated_parities_expose_one_pin_per_rebuild() {
    let pair = |i: usize| {
        let (a, b) = (atom(120_000 + 2 * i as u64), atom(120_001 + 2 * i as u64));
        let low = Bdd::literal(a.clone()).and_literal((b.clone(), false));
        let high = Bdd::literal(a).not().and_literal((b, true));
        (Part::Bdd(low), Part::Bdd(high))
    };
    let mut all = Vec::new();
    for m in [2, 8, 32] {
        first_pin_is_e0(&pair, 129_999, m);
        let (p, _) = gated_parities(&pair, 129_999, m, true);
        let (_, cut, carried, rounds) = settled_alike(&p, m <= 8, true, "gated parities");
        eprintln!("gated parities m = {m}: cut {cut}, carried {carried}, rounds {rounds:?}");
        all.push((m, rounds));
    }
    for (m, rounds) in all {
        assert_eq!(rounds, vec![1; m + 1], "m = {m}");
    }
}

/// [`gated_parities`] with `L_i` and `H_i` meets of two atoms of their own, as in [`opaque`]:
/// one round, which pins `E_0`. The rebuilt `F_1`, `L_1 | H_1`, is an expression of its own,
/// not `E_1`, so nothing more is shared (measured 2026-11-27 at m 2, 8 and 32). The one pin is
/// `E_0`'s by id, and with `E_0` built twice there is none ([`first_pin_is_e0`]).
#[test]
fn gated_parities_on_meets_pin_once() {
    let pair = |i: usize| {
        let at = 110_000 + 4 * i as u64;
        (Part::Bdd(meet(at, 2)), Part::Bdd(meet(at + 2, 2)))
    };
    let mut all = Vec::new();
    for m in [2, 8, 32] {
        first_pin_is_e0(&pair, 119_999, m);
        let (p, _) = gated_parities(&pair, 119_999, m, true);
        let (_, cut, carried, rounds) = settled_alike(&p, m <= 8, true, "gated parities on meets");
        eprintln!(
            "gated parities on meets m = {m}: cut {cut}, carried {carried}, rounds {rounds:?}"
        );
        all.push((m, rounds));
    }
    for (m, rounds) in all {
        assert_eq!(rounds, vec![1], "m = {m}");
    }
}

/// [`pinned_one_a_round`]'s work under each way of finding pins. [`Pins::Cut`] and
/// [`Pins::Carried`] (the rounds) take the same rounds, which grow faster than `m` (measured
/// 2026-11-27: 8 rounds at m 32 and 20 at 64, cut work 5.1 times a doubling);
/// [`settled_by`] holds their work to the rounds plus 1 times the first round. The cross-review
/// (XR-lazy-and-kernel-batch-1, round 1) holds [`Pins::Required`] (A+B), the change meant to
/// make this family linear, to at most 2.2 times its total work a doubling of `m`, to the same
/// part as the rounds, and to one run of its phase A a call of [`Part::pins_by`] (before phase A
/// was one propagation, measured 2026-11-27: 1 round, but work 4,547 at m 32 and 17,299 at 64,
/// 3.8 times). Every count is printed before any is checked.
#[test]
fn settling_a_chain_pinned_one_a_round_takes_rounds_times_the_part() {
    let mut last: Option<u64> = None;
    let mut over = Vec::new();
    for m in [16, 32, 64, 128] {
        let p = pinned_one_a_round(130_000, m);
        SETTLE_WORK.with(|w| w.set(0));
        p.pins();
        let one = SETTLE_WORK.with(|w| w.get());
        let (settled, cut, carried, rounds) = settled_alike(&p, false, true, "pinned one a round");
        REQUIRED_PASSES.with(|n| n.set(0));
        let (by_required, required, required_rounds) = settled_by(&p, Pins::Required);
        let passes = REQUIRED_PASSES.with(|n| n.get());
        eprintln!(
            "pinned one a round m = {m}: first round {one}, rounds {}, cut work {cut}, carried \
             work {carried}; A+B rounds {}, passes {passes}, work {required}",
            rounds.len(),
            required_rounds.len()
        );
        assert!(by_required == settled, "m = {m}: A+B gave another part");
        // Phase A once a call of `pins_by`: the rounds that pin, and the last that finds none.
        assert_eq!(passes, required_rounds.len() as u64 + 1, "m = {m}");
        if let Some(r0) = last
            && required as f64 > 2.2 * r0 as f64
        {
            over.push(format!("m = {m}: A+B work {r0} to {required}"));
        }
        last = Some(required);
    }
    assert!(over.is_empty(), "{over:#?}");
}
