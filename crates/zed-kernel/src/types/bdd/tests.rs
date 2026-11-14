use super::*;
use crate::types::{AtomPart, Morphism, Node, Row, Type};
use crate::value::Value;

/// The tuple type of one integer, an atom independent of the others.
pub(super) fn atom(i: u64) -> Row {
    Row::new(vec![Type::lit(&Value::Int(i as i64)).unwrap()])
}

fn random(seed: &mut u64, depth: u32) -> Part<Row> {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let pick = *seed >> 33;
    if depth == 0 || pick.is_multiple_of(5) {
        return Part::literal(atom(pick % 6));
    }
    let (a, b) = (random(seed, depth - 1), random(seed, depth - 1));
    match pick % 3 {
        0 => a.zip(&b, Op::Or),
        1 => a.zip(&b, Op::And),
        _ => a.not(),
    }
}

/// The part built from `random`'s connectives as expressions, so that every form is met;
/// an operand is at times one built before, kept in `pool`, so that expressions are shared.
fn random_expr(seed: &mut u64, depth: u32, pool: &mut Vec<Part<Row>>) -> Part<Row> {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let pick = *seed >> 33;
    if !pool.is_empty() && pick % 7 == 3 {
        return pool[(pick / 7) as usize % pool.len()].clone();
    }
    if depth == 0 || pick.is_multiple_of(5) {
        return random(seed, 2);
    }
    let (a, b) = (
        random_expr(seed, depth - 1, pool),
        random_expr(seed, depth - 1, pool),
    );
    let p = Part::expr(match pick % 3 {
        0 => Form::Or(a, b),
        1 => Form::And(a, b),
        _ => Form::Not(a),
    });
    pool.push(p.clone());
    p
}

#[test]
fn three_valued_operations_keep_the_assignments() {
    // Each set of the six atoms is one assignment, and a partial assignment fixes the
    // atoms of `known` to their membership in `fixed`. A three-valued value is the value
    // of every assignment that agrees with it; restricting keeps the value of every
    // assignment agreeing with what it fixes; settling keeps every assignment in the
    // part, and makes it empty only when the part is; an atom forced taken is in every assignment in the part, and one
    // forced refused in none.
    let mut seed = crate::seed::seed("three_valued_operations_keep_the_assignments");
    let (mut exprs, mut decided, mut forced, mut settled) = (0, 0, 0, 0);
    for _ in 0..600 {
        let p = if seed.is_multiple_of(2) {
            random(&mut seed, 6)
        } else {
            random_expr(&mut seed, 5, &mut Vec::new())
        };
        exprs += usize::from(matches!(p, Part::Expr(_)));
        let holds = |set: u32| move |t: &Row| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i));
        assert!(p.settle() == p.settle_by_scans(), "settling changed");
        let inside: Vec<u32> = (0..64).filter(|&set| p.eval(&holds(set))).collect();
        let (known, fixed) = ((seed >> 7) as u32 % 64, (seed >> 13) as u32 % 64);
        let fix = |t: &Row| {
            (0..6)
                .find(|&i| *t == atom(i) && known & (1 << i) != 0)
                .map(|i| fixed & (1 << i) != 0)
        };
        let agree = |set: u32| (set ^ fixed) & known == 0;
        if let Some(v) = p.eval3(&fix) {
            decided += 1;
            assert!(
                (0..64)
                    .filter(|&s| agree(s))
                    .all(|s| p.eval(&holds(s)) == v),
                "{p:?}"
            );
        }
        let r = p.restrict(&fix);
        let t = p.settle();
        settled += usize::from(inside.is_empty() && t.is_leaf() == Some(false));
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
        forced += taken.len() + refused.len();
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
    // 30 runs of 600 parts: 376 to 413 expressions, 287 to 337 decided, 516 to 608 forced
    // atoms, 14 to 38 settled to empty.
    assert!(
        exprs > 250 && decided > 200 && forced > 400 && settled > 5,
        "{exprs} {decided} {forced} {settled}"
    );
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
            let mut stack = vec![self];
            while let Some(d) = stack.pop() {
                if let Old::Node(n) = d
                    && seen.insert(d.clone())
                {
                    stack.extend([&n.1, &n.2]);
                }
            }
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
    let holds = |set: u32| move |t: &Row| (0..6).any(|i| set >> i & 1 == 1 && *t == atom(i));
    let mut pool: Vec<(Bdd<Row>, Old)> = (0..6)
        .map(|i| (Bdd::literal(atom(i as u64)), Old::literal(i)))
        .chain([false, true].map(|b| (Bdd::Leaf(b), Old::Leaf(b))))
        .collect();
    // The id of the one list of each function, by its values.
    let mut ids: HashMap<u64, u64> = HashMap::new();
    let mut seed = crate::seed::seed("lists_agree_with_the_diagrams_apply_built");
    let mut next = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        seed >> 33
    };
    let (mut joined, mut found_again) = (0, 0);
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
        let values: u64 = (0..64).filter(|&s| d.eval(s)).fold(0, |m, s| m | 1 << s);
        for set in 0..64u32 {
            assert_eq!(z.eval(holds(set)), d.eval(set), "{z:?} at {set:b}");
        }
        let id = *ids.entry(values).or_insert_with(|| z.id());
        found_again += usize::from(id == z.id() && pool.iter().any(|(p, _)| p.id() == id));
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
        pool.push((z, d));
    }
    // 30 runs of 4,000: 1,534 to 1,715 joined, 3,193 to 3,592 found again.
    assert!(
        joined > 1000 && found_again > 2500,
        "{joined} {found_again}"
    );
}

#[test]
fn list_matches_the_one_form_found_from_its_values() {
    let mut seed = crate::seed::seed("list_matches_the_one_form_found_from_its_values");
    let mut lists = 0;
    for _ in 0..800 {
        let Part::Bdd(b) = random(&mut seed, 6) else {
            continue;
        };
        let holds = |set: u32| move |t: &Row| (0..6).any(|i| set >> i & 1 == 1 && *t == atom(i));
        let expected = list_of_values(|s| b.eval(holds(s)));
        assert_eq!(Some(sorted(b.list())), expected, "the list of {b:?}");
        lists += 1;
    }
    // 30 runs of 800: 524 to 576 lists.
    assert!(lists > 400, "{lists} lists");
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

#[test]
fn exclusive_ors_agree_with_their_values() {
    let reached = exclusive_or_rounds(
        crate::seed::seed("exclusive_ors_agree_with_their_values"),
        XOR_ROUNDS,
    );
    // 2 · 64 - 2 functions are exclusive ors and no leaf.
    assert!(reached >= 100, "{reached}");
}

/// The rounds of [`exclusive_or_rounds`] in a run. 2000 rounds reached 77 exclusive ors on
/// seed 81 and 85 on seed 3601000514119134698, about 1 run in 200 below 100; 4000 rounds
/// reached 117 to 126 on 5,600 seeds, all but 4 at 123 or more, in about 0.3 s a run.
const XOR_ROUNDS: usize = 4000;

/// The seeds on which 2000 rounds reached too few exclusive ors.
#[test]
fn exclusive_ors_reach_their_count_on_the_seeds_that_failed() {
    for seed in [3601000514119134698, 81] {
        let reached = exclusive_or_rounds(seed, XOR_ROUNDS);
        assert!(reached >= 100, "seed {seed}: {reached}");
    }
}

/// Random parts over six atoms, each built with its set of values beside it as a mask of
/// the 64 assignments; exclusive ors in their one form of one function are one node while
/// they live. The first part of each function is held, so that a later one is compared with
/// a live node: a node freed and made again takes a new id. Returns the number of distinct
/// exclusive-or functions the `rounds` rounds from `seed` reached.
fn exclusive_or_rounds(mut seed: u64, rounds: usize) -> usize {
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
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let pick = (seed >> 33) as usize;
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
    firsts.len()
}

#[test]
fn the_halves_of_exclusive_ors_meet_as_zip_meets_them() {
    // `xor::meet` builds the meets of an exclusive or's halves without the search of `zip`,
    // for literals and exclusive ors over disjoint atoms; it must make the part `zip` makes.
    // Random sets of 1 to 7 atoms, each built in a random order, are met with each other and
    // their complements, both ways round.
    let mut seed = crate::seed::seed("the_halves_of_exclusive_ors_meet_as_zip_meets_them");
    let mut next = |below: u64| {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) % below
    };
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
                    let made = xor::meet(p, q);
                    assert!(made == p.zip(q, Op::And), "{p:?} & {q:?}");
                    exprs += usize::from(made.expr_id().is_some());
                }
            }
        }
    }
    assert!(exprs > 10_000, "{exprs}");
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
        p.atoms.names = p.atoms.names.update(
            "a".into(),
            AtomPart {
                bare: false,
                payload: t,
            },
        );
        p.atoms.payloads = imbl::OrdSet::unit("a".into());
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
        Part::expr(Form::Or(e, leaf(atom(base + k))))
    })
}

/// The expressions `e_k = e_{k-1} | e_{k-2}` for `k` from 2 to `m - 1`, the last returned, on
/// `e_0` the atom `base` and `e_1` the atom `base + 1`: each expression is the second operand
/// of the one two above it, so an evaluation that reaches it first through the first operand
/// finds it in its memo the second time. In [`ors`] every lookup comes before the first entry.
pub(super) fn ladder(base: u64, m: usize) -> Part<Row> {
    let (mut below, mut top) = (Part::literal(atom(base)), Part::literal(atom(base + 1)));
    for _ in 2..m {
        let next = Part::expr(Form::Or(top.clone(), below));
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
    let t = Part::expr(Form::Not(Part::literal(atom(base))));
    let p = (1..m as u64).fold(t.clone(), |e, k| {
        let x = Bdd::literal(atom(base + 2 * k - 1));
        Part::expr(Form::Or(
            e,
            Part::Bdd(x.and_literal((atom(base + 2 * k), true))),
        ))
    });
    Part::expr(Form::And(p, Part::expr(Form::Not(t))))
}

/// The list `x_0 & x_1 & … & x_{m-1}`, one block of `m` literals, the atoms from `base`.
pub(super) fn meet(base: u64, m: usize) -> Bdd<Row> {
    (0..m as u64).fold(Bdd::Leaf(true), |b, k| {
        b.and_literal((atom(base + k), true))
    })
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
        Part::expr(Form::Or(
            Part::expr(Form::And(c.clone(), p)),
            Part::expr(Form::And(c.not(), Part::literal(atom(leaves + k)))),
        ))
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

/// The entries of this thread's tables of tuple nodes, in all: sets, cells, exclusive ors and
/// the exclusive ors of inner nodes.
fn entries() -> usize {
    Row::table(|t| {
        t.sets.values().map(|b| b.len()).sum::<usize>()
            + t.cells.len()
            + t.xors.len()
            + t.inners.len()
    })
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
    // Item KERNEL-parity-lazy-halves: an exclusive or with an operand that is an expression is
    // made with its digest alone, and its two meets when its form is first read; one of two
    // literals, whose meets are lists, is made whole at once. The form made on first read is
    // the one `zip` makes from the same pair, `p&!q | !p&q` or `p&q | !p&!q`, its operands in
    // their order, and its digest is the one the expression was made with.
    let two = parity(9500, 2);
    assert!(!unmade(&two) && !unmade(&two.not()));
    for k in 3..12 {
        let x = parity(9600 + 20 * k, k);
        // Ordering two exclusive ors of distinct digests reads no form.
        let y = parity(9601 + 20 * k, k);
        assert!(x.digest() != y.digest() && x != y);
        for p in [&x, &x.not(), &y] {
            assert!(unmade(p), "{k}");
        }
        for p in [x.clone(), x.not()] {
            let e = expr_of(&p);
            let (pair, constant) = e.xor.as_ref().expect("an exclusive or");
            let (q, r) = (&pair.p, &pair.q);
            let (a, b) = match constant {
                true => (q.zip(r, Op::And), q.not().zip(&r.not(), Op::And)),
                false => (q.zip(&r.not(), Op::And), q.not().zip(r, Op::And)),
            };
            let (a, b) = if a.before(&b) { (a, b) } else { (b, a) };
            let Form::Or(u, v) = e.form() else {
                panic!("an exclusive or is a union: {p:?}")
            };
            assert!(*u == a && *v == b, "{k} {constant}");
            assert_eq!(joined_digest(Op::Or, a.digest(), b.digest()), e.digest);
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
    // their pair (`xor::mate`), with its digest alone, equal to the one dropped.
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
    // An exclusive or dropped while its complement lives, and built again from the same tree
    // node of its atoms, is the complement's complement, taken from the table (`xor::mate`),
    // not made a third time (TEST-bench-move-l0123, author P188: before, only a benchmark of
    // l01_23 reached it, 2 times in 15,000 complements). Built again by `parity`, the tree node
    // is a new one, and the complement is made again from its pair, as in
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
        // `x` was made with a complement of its own beside it (`xor::xor2`): equal to `n`, not
        // the same node.
        assert_eq!(x.not(), n, "{k}");
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
    assert_eq!(expr_of(&x).form().digest(), x.digest());
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
/// three literals each joined to the part `p` another thread built, so that the tree nodes
/// rebuilt keep `p`'s left subtrees and atoms, then all three in turn. Returns the records and
/// the last part.
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
    // and hands its result on, so that a thread rebuilds tree nodes whose left subtree and atom
    // another thread made (`xor::inner`), and a part is dropped on a thread other than the one
    // that built it. Every part built is recorded, and the records equal those of the same
    // rounds run on one thread.
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
fn joined_blocks(base: u64, m: usize) -> Bdd<Row> {
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
    // Item CHAIN-deep-atom: the list after the rejoins of the scaling test above, on 6
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
    let mut seed = crate::seed::seed("list_operations_agree_with_plain_lists") | 1;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let atoms: Vec<Row> = (0..ATOMS).map(|i| atom(base + i)).collect();
    let index = |a: &Row| atoms.iter().position(|b| b == a).expect("an atom listed") as u64;
    let plain = |b: &Bdd<Row>| Plain {
        blocks: (b.list().blocks.into_iter())
            .map(|(v, l)| (v, l.iter().map(|(a, t)| (index(a), *t)).collect()))
            .collect(),
        tail: b.default(),
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
        assert!(g.cells_are_sound(), "{g:?}");
        let id = kept.entry(q.clone()).or_insert_with(|| g.clone()).id();
        assert_eq!(id, g.id(), "two cells of one list: {q:?}");
        for _ in 0..4 {
            let bits = next();
            let holds = |x: u64| bits >> x & 1 == 1;
            assert_eq!(g.eval(|b| holds(index(b))), q.eval(holds), "{q:?}");
        }
        longest = longest.max(q.blocks.len());
        pool.push((g, q));
        if pool.len() > 400 {
            pool.swap_remove((next() % 400) as usize);
        }
    }
    // 30 runs of 8,000: the longest list had 14 to 20 blocks.
    assert!(longest >= 12, "the longest list has {longest} blocks");
}

#[test]
fn a_set_less_some_literals_is_the_set_they_leave_one_at_a_time() {
    // `set::retain` against removing the literals one at a time (`set::remove`): sets have one
    // shape and are found again in the table, so the two must give one node. Random sets of up
    // to 200 literals, with none, some or all removed.
    let mut seed = 7u64;
    let mut next = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        seed >> 33
    };
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

#[test]
fn the_one_atom_a_chain_forces_is_its_first() {
    for m in [1, 2, 3, 8, 33] {
        let (p, w) = forced_chain(m);
        assert_eq!(p.forced(), (vec![w], Vec::new()), "{m}");
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
    let and = |a: Part<Row>, b: Part<Row>| Part::expr(Form::And(a, b));
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
    let empty = Part::expr(Form::And(
        conjunction(5, false),
        Part::literal(atom(0)).not(),
    ));
    let (t, r) = empty.forced();
    assert_eq!(t.len() + r.len(), 5, "{empty:?}");
}

/// `x_{k+1} = x_k & !x_k` to `depth` levels over the atom 0: both operands of each level
/// lead to the level below.
pub(super) fn self_meets(depth: usize) -> Part<Row> {
    let mut x = Part::literal(atom(0));
    for _ in 0..depth {
        x = Part::expr(Form::And(x.clone(), x.not()));
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
