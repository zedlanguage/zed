use super::*;
use crate::types::{AtomPart, Morphism, Node, Row, Type};
use crate::value::Value;

use crate::scaling;

/// The tuple type of one integer, an atom independent of the others.
fn atom(i: u64) -> Row {
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
    let (mut seed, mut exprs, mut decided, mut forced, mut settled) = (7, 0, 0, 0, 0);
    for k in 0..3000u32 {
        let p = if seed % 2 == 0 {
            random(&mut seed, 6)
        } else {
            random_expr(&mut seed, 5, &mut Vec::new())
        };
        exprs += usize::from(matches!(p, Part::Expr(_)));
        let holds = |set: u32| move |t: &Row| (0..6).any(|i| set & (1 << i) != 0 && *t == atom(i));
        assert!(p.settle() == p.settle_by_scans(), "settling changed");
        let inside: Vec<u32> = (0..64).filter(|&set| p.eval(&holds(set))).collect();
        let (known, fixed) = (k % 64, (k / 64) % 64);
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
    assert!(
        exprs > 500 && decided > 300 && forced > 1000 && settled > 100,
        "{exprs} {decided} {forced} {settled}"
    );
}
#[test]
fn forced_atoms_of_a_long_chain_scale() {
    // `w ∧ ((x_1 ∧ … ∧ x_m) ∨ z)`: `true` is reached past `z` from every `x_k`. Finding the
    // branches that dominate `true` took the nearest common dominator of `m` branches at
    // growing depths, walking up one step at a time: `O(m²)`.
    std::thread::Builder::new()
        .spawn(|| {
            // Built from its literals by the connectives: `w` is atom 0, `z` atom `m + 1`.
            let chain = |m: usize| {
                let xs: Vec<Row> = (0..m as u64 + 2).map(atom).collect();
                let lit = |k: usize| Part::literal(xs[k].clone());
                let meet = (2..=m).fold(lit(1), |g, k| g.zip(&lit(k), Op::And));
                let g = meet.zip(&lit(m + 1), Op::Or);
                (lit(0).zip(&g, Op::And), xs[0].clone())
            };
            let n = 1 << 12;
            let built = scaling::inputs(n, chain);
            scaling::check("the forced atoms of a chain, by its length", n, |m| {
                let (p, w) = &built[&m];
                assert_eq!(p.forced(), (vec![w.clone()], Vec::new()));
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn forced_atoms_of_a_long_conjunction_scale() {
    // `x_0 ∧ x_1 ∧ … ∧ x_{m-1}`, every third literal refused, kept as expressions: built one
    // literal at a time, and as a balanced tree, whose meets join two large sets. A pass that
    // copied the settings found so far at each conjunction took 12.5 ms at 512 literals and
    // 760 ms at 4096 (cross-review XR3, R3_CODEX.md Q7).
    let lit = |i: usize| {
        let l = Part::literal(atom(i as u64));
        if i % 3 == 2 { l.not() } else { l }
    };
    let and = |a: Part<Row>, b: Part<Row>| Part::expr(Form::And(a, b));
    let deep = |m: usize| (1..m).fold(lit(0), |p, i| and(p, lit(i)));
    let balanced = |m: usize| {
        let mut level: Vec<Part<Row>> = (0..m).map(lit).collect();
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
    };
    let expected = |m: usize| {
        let (mut taken, mut refused): (Vec<Row>, Vec<Row>) = (Vec::new(), Vec::new());
        for i in 0..m {
            if i % 3 == 2 { &mut refused } else { &mut taken }.push(atom(i as u64));
        }
        taken.sort();
        refused.sort();
        (taken, refused)
    };
    let sorted = |(mut t, mut r): (Vec<Row>, Vec<Row>)| {
        t.sort();
        r.sort();
        (t, r)
    };
    assert_eq!(sorted(lit(0).forced()), expected(1), "one literal");
    assert_eq!(
        sorted(deep(7).forced()),
        expected(7),
        "seven, one at a time"
    );
    assert_eq!(sorted(balanced(7).forced()), expected(7), "seven, balanced");
    // A conjunction holding an atom both ways holds nowhere: every atom is then forced.
    let empty = and(deep(5), Part::literal(atom(0)).not());
    let (t, r) = empty.forced();
    assert_eq!(t.len() + r.len(), 5, "{empty:?}");
    let n = 1 << 11;
    let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, (deep(m), balanced(m))))
        .collect();
    for (&m, (deep, balanced)) in &built {
        assert_eq!(sorted(deep.forced()), expected(m), "{m}, one at a time");
        assert_eq!(sorted(balanced.forced()), expected(m), "{m}, balanced");
    }
    scaling::check(
        "the forced atoms of a conjunction, by its literals",
        n,
        |m| {
            let (deep, balanced) = &built[&m];
            std::hint::black_box((deep.forced(), balanced.forced()));
        },
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

#[test]
fn comparing_equal_expressions_built_apart_scales() {
    // `x_{k+1} = x_k & !x_k`, built twice: both operands of each level lead to the level
    // below, so comparing operand by operand met the bottom `2^depth` times.
    std::thread::Builder::new()
        .spawn(|| {
            let build = |depth: usize| {
                let mut x = Part::literal(atom(0));
                for _ in 0..depth {
                    x = Part::expr(Form::And(x.clone(), x.not()));
                }
                x
            };
            let n = 1 << 12;
            let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
                .into_iter()
                .map(|m| (m, (build(m), build(m))))
                .collect();
            scaling::check(
                "comparing equal expressions built apart, by depth",
                n,
                |m| {
                    let (a, b) = &built[&m];
                    assert_eq!(a.cmp(b), Ordering::Equal);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn comparing_equal_lists_built_on_two_threads_scales() {
    // A list of `m` literals in blocks of two of alternating values. Each thread has its
    // own tables of cells and sets, so the two lists share no node, and comparing them
    // reads each pair of cells and of set nodes once. (The parity of `m` atoms, a diagram
    // the lists no longer build, met its last atom `2^m` times when compared `hi` then
    // `lo`.)
    let blocks = |m: usize| {
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
    };
    let n = 1 << 10;
    let on_a_thread = |m: usize| std::thread::spawn(move || blocks(m)).join().unwrap();
    let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, (on_a_thread(m), on_a_thread(m))))
        .collect();
    scaling::check(
        "comparing equal lists built on two threads, by literals",
        n,
        |m| {
            let (a, b) = &built[&m];
            assert_eq!(a.cmp(b), Ordering::Equal);
        },
    );
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
    let mut seed = 5u64;
    let mut next = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        seed >> 33
    };
    let (mut joined, mut found_again) = (0, 0);
    for _ in 0..20_000 {
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
    assert!(
        joined > 5000 && found_again > 5000,
        "{joined} {found_again}"
    );
}

#[test]
fn list_matches_the_one_form_found_from_its_values() {
    let mut seed = 11;
    let mut lists = 0;
    for _ in 0..4000 {
        let Part::Bdd(b) = random(&mut seed, 6) else {
            continue;
        };
        let holds = |set: u32| move |t: &Row| (0..6).any(|i| set >> i & 1 == 1 && *t == atom(i));
        let expected = list_of_values(|s| b.eval(holds(s)));
        assert_eq!(Some(sorted(b.list())), expected, "the list of {b:?}");
        lists += 1;
    }
    assert!(lists > 1000, "{lists} lists");
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

#[test]
fn list_of_alternating_literals_scales() {
    // `((x0 | x1) & !x2 | x3) & !x4 …`, each new literal first in the order, so every
    // literal is a block of its own: finding the blocks one by one took a pass over the
    // diagram's nodes per block.
    let build = |m: usize| {
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
    };
    let n = 1 << 12;
    let built: BTreeMap<usize, Bdd<Row>> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, build(m)))
        .collect();
    scaling::check(
        "the decision list of alternating literals, by atoms",
        n,
        |m| {
            let l = built[&m].list();
            assert_eq!(l.blocks.len(), m - 1);
            assert!(!l.tail);
        },
    );
}

#[test]
fn joining_chains_to_lists_scales() {
    // `((x_0 | x_1) & !x_2 | x_3) & !x_4 …` built a literal at a time, each new literal last
    // in the order of the atoms: the diagram the chain rule built had up to `k` nodes on
    // the `k`-th atom, `O(m²)` in all, and built them all again at each literal (the
    // negative control in STATUS.md, CHAIN-zip-size). A list takes each literal into its
    // first block, or a block of its own, in `O(log m)`. Two chains with half their atoms
    // in common are joined a literal of the shorter at a time.
    let n = 1 << 11;
    let lits = scaling::inputs(n, |m| {
        let mut xs: Vec<Row> = (0..m as u64).map(atom).collect();
        xs.sort();
        let lits: Vec<(Part<Row>, Part<Row>)> = xs
            .into_iter()
            .map(|x| (Part::literal(x.clone()), Part::literal(x).not()))
            .collect();
        lits
    });
    let chains = scaling::inputs(n, |m| {
        let chain = |from: u64| {
            (from..from + m as u64).fold(Part::leaf(false), |f, k| {
                f.zip(&Part::literal(atom(k)), Op::Or)
            })
        };
        (chain(0), chain(m as u64 / 2))
    });
    scaling::check("a list built a literal at a time, by literals", n, |m| {
        let xs = &lits[&m];
        let f =
            (xs[1..].iter().enumerate()).fold(xs[0].0.clone(), |f, (i, (x, not_x))| match i % 2 {
                0 => f.zip(x, Op::Or),
                _ => f.zip(not_x, Op::And),
            });
        assert!(matches!(f, Part::Bdd(_)), "{f:?}");
    });
    // A chain grown a literal at a time stays a chain, so both operands of each step are
    // chains; listing the long one too at each step took `O(m²)` (59 s for the forced atoms
    // of a chain of 32768 literals).
    // Each literal goes into the chain's one block, so the work follows the right spine of
    // the block's treap; it is summed over `SHAPES` offsets of the atoms.
    let shapes = scaling::inputs(n, |m| {
        (0..SHAPES)
            .map(|j| {
                let mut xs: Vec<Row> = (0..m as u64).map(|i| atom(j * SHAPE_STRIDE + i)).collect();
                xs.sort();
                xs.into_iter().map(Part::literal).collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    });
    for op in [Op::Or, Op::And] {
        scaling::check("a chain built a literal at a time, by literals", n, |m| {
            for xs in &shapes[&m] {
                let f = (xs[1..].iter()).fold(xs[0].clone(), |f, x| f.zip(x, op));
                assert!(
                    matches!(&f, Part::Bdd(b) if b.chain_len(op) == Some(m)),
                    "{f:?}"
                );
            }
        });
    }
    scaling::check(
        "the union of two chains with half their atoms in common, by literals",
        n,
        |m| {
            let (a, b) = &chains[&m];
            assert!(a.zip(b, Op::Or) != *a);
        },
    );
}

/// `p ^ q` as the type operations build it: `p&!q | !p&q`.
fn xor_by_or(p: &Part<Row>, q: &Part<Row>) -> Part<Row> {
    let left = p.zip(&q.not(), Op::And);
    left.zip(&p.not().zip(q, Op::And), Op::Or)
}

/// `p ^ q` as `(p|q) & (!p|!q)`.
fn xor_by_and(p: &Part<Row>, q: &Part<Row>) -> Part<Row> {
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
fn exclusive_ors_agree_with_their_values() {
    // Random parts over six atoms, each built with its set of values beside it as a mask of
    // the 64 assignments; exclusive ors in their one form of one function are one node.
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
    let mut pool: Vec<(Part<Row>, u64)> = lits.clone();
    let mut ids: HashMap<u64, u64> = HashMap::new();
    let mut seed = 7u64;
    for _ in 0..4000 {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let pick = (seed >> 33) as usize;
        let (p, pm) = pool[pick % pool.len()].clone();
        let (q, qm) = pool[(pick / 7) % pool.len()].clone();
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
        if made.0.xor_tag().is_some() {
            assert_eq!(*ids.entry(made.1).or_insert(made.0.id()), made.0.id());
        }
        if pool.len() < 200 {
            pool.push(made);
        } else {
            pool[pick % 200] = made;
        }
    }
    assert!(ids.len() >= 10, "{}", ids.len());
}

#[test]
fn the_halves_of_exclusive_ors_meet_as_zip_meets_them() {
    // `xor::meet` builds the meets of an exclusive or's halves without the search of `zip`,
    // for literals and exclusive ors over disjoint atoms; it must make the part `zip` makes.
    // Random sets of 1 to 7 atoms, each built in a random order, are met with each other and
    // their complements, both ways round.
    let mut seed = 11u64;
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

#[test]
fn parity_built_a_literal_at_a_time_scales() {
    // Parity built a literal at a time, as the type operations build it: each step takes a
    // literal into the set of the one form in `O(log n)`, and makes the expressions of the
    // `O(log n)` new tree nodes. Each size has atoms of its own. Each literal rebuilds the
    // nodes on its path in the set's treap, so the work follows that path; parity is built
    // over `SHAPES` offsets of the atoms.
    //
    // Measured (16 offsets, 2026-11-09): the tree nodes built per literal at 128 to 8,192
    // literals are 6.30, 7.99, 9.25, 10.48, 11.98, 13.18, 14.84, that is `2 H_n - 4.45`
    // within 0.15, the depth of a treap built by random insertion. So the work is `n log n`
    // with a negative constant term, and its ratio at `n` and `8n` approaches the limit's
    // `ln(8n)/ln(n) × 1.1` from above as `n` falls; at 2,048 and 16,384 the limit is 11.20.
    // With the atoms in sorted order the nodes per literal are `H_n - 1.5`.
    //
    // Each node cost about 147,000 instructions while `xor::half` met its operands by `zip`,
    // whose search for a simpler form (`choice_of`, `same_as_not`, `choice`, `negate`) never
    // finds one for the halves of an exclusive or (see `xor::meet`). With `xor::meet` a node
    // costs about 34,000: 6.51G and 66.12G instructions at 2,048 and 16,384 (10.2 times),
    // 696M and 6.96G bytes (10.0 times), 25 s at load 6 (SCALE-log-offset). Releasing a
    // shared handle in place, one table probe per freed node, the inner nodes' exclusive ors
    // kept in a table, two literals met at once and the exclusive or tested before `zip`'s
    // frames bring it to 4.99G and 50.09G (10.0 times), 489M and 4.97G bytes (10.2 times),
    // 28 s at load 31 where the code before took 54 s at load 30, and 51 s inside a run of
    // 508 tests (KERNEL-parity-cost). So the sizes are now 1,024 and 8,192 literals, where the
    // limit is 11.44: 2.26G and 23.36G instructions (10.3 times), 221M and 2.31G bytes (10.4
    // times), 11 s at load 30. Rebuilding every tree node on each literal fails the check at
    // 128 and 1,024 literals, by 58.6 times the bytes. Making each exclusive or's two meets
    // only when its form is read (KERNEL-parity-lazy-halves) takes 1.96G and 20.45G
    // instructions to 1.48G and 15.31G (10.3 times), 221M and 2.31G bytes to 138M and 1.39G
    // (10.1 times), and 10.4 s to 7.0 s at load 11 to 22.
    let n = 1 << 10;
    let lits = scaling::inputs(n, |m| {
        (0..SHAPES)
            .map(|j| {
                (0..m as u64)
                    .map(|i| Part::literal(atom(j * SHAPE_STRIDE + 16 * m as u64 + i)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    });
    scaling::check("parity built a literal at a time, by literals", n, |m| {
        for ls in &lits[&m] {
            let x = ls.iter().fold(Part::leaf(false), |f, l| xor_by_or(&f, l));
            assert!(x.xor_tag().is_some());
        }
    });
}

#[test]
fn exclusive_ors_scale() {
    // The exclusive ors of the first half and of the last three quarters of `n` atoms, which
    // share a quarter, are joined in `O(n log n)`. Each size has atoms of its own.
    let n = 1 << 10;
    let halves = scaling::inputs(n, |m| {
        let ls: Vec<_> = (0..m as u64)
            .map(|i| Part::literal(atom(16 * m as u64 + i)))
            .collect();
        let half = |r: std::ops::Range<usize>| {
            ls[r]
                .iter()
                .fold(Part::leaf(false), |f, l| xor_by_or(&f, l))
        };
        (half(0..m / 2), half(m / 4..m))
    });
    scaling::check(
        "two exclusive ors with half their atoms in common joined, by literals",
        n,
        |m| {
            let (a, b) = &halves[&m];
            assert!(xor_by_and(a, b).xor_tag().is_some());
        },
    );
}

/// `depth` levels of the atom `#a` with a payload of the level below, over `bottom`, every
/// digest 0: comparing two of them reads every level, as two types whose digests tie at
/// every depth are read in the short-addresses build (SHORT-stack-l01_22).
fn tied(bottom: &str, depth: usize) -> Type {
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

#[test]
fn types_whose_digests_tie_at_every_depth_are_ordered_on_a_small_stack() {
    // The order reads such types n levels down. It was a recursion, which overflowed this
    // 2 MiB stack a few thousand levels down; it is a loop with a stack of its own.
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            let depth = 100_000;
            let (a, b, c) = (tied("z", depth), tied("z", depth), tied("y", depth));
            assert_eq!(a.digest(), c.digest());
            assert_eq!(a.cmp(&b), Ordering::Equal);
            assert_eq!(a, b);
            // The bottoms differ: `#y` before `#z`, read 100,000 levels down.
            assert_eq!(a.cmp(&c), Ordering::Greater);
            assert_eq!(c.cmp(&a), Ordering::Less);
            // A chain that stops a level short has no payload where the other has one.
            let d = tied("z", depth - 1);
            assert_eq!(d.cmp(&a), a.cmp(&d).reverse());
            assert_ne!(d.cmp(&a), Ordering::Equal);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn ordering_types_whose_digests_tie_at_every_depth_scales() {
    // One step per level: the two chains are equal, so every level is read.
    let n = 10_000;
    let built: BTreeMap<usize, (Type, Type)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, (tied("z", m), tied("z", m))))
        .collect();
    scaling::check(
        "ordering two equal chains of tied digests, by depth",
        n,
        |m| {
            let (a, b) = &built[&m];
            assert_eq!(a.cmp(b), Ordering::Equal);
        },
    );
}

/// `x_0 | x_1 | … | x_{m-1}` as expressions nested `m - 1` deep, the first operand the
/// deeper, each `x_k` the part `leaf` makes of the atom `base + k`.
fn ors(base: u64, m: usize, leaf: impl Fn(Row) -> Part<Row>) -> Part<Row> {
    (1..m as u64).fold(leaf(atom(base)), |e, k| {
        Part::expr(Form::Or(e, leaf(atom(base + k))))
    })
}

/// The expressions `e_k = e_{k-1} | e_{k-2}` for `k` from 2 to `m - 1`, the last returned, on
/// `e_0` the atom `base` and `e_1` the atom `base + 1`: each expression is the second operand
/// of the one two above it, so an evaluation that reaches it first through the first operand
/// finds it in its memo the second time. In [`ors`] every lookup comes before the first entry.
fn ladder(base: u64, m: usize) -> Part<Row> {
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
fn settled_by_one_pin(base: u64, m: usize) -> Part<Row> {
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
fn meet(base: u64, m: usize) -> Bdd<Row> {
    (0..m as u64).fold(Bdd::Leaf(true), |b, k| {
        b.and_literal((atom(base + k), true))
    })
}

/// The walks on expressions and diagrams nested this deep, on a 2 MiB stack.
const DEEP: usize = 100_000;

#[test]
fn the_walks_over_parts_nested_deep_run_on_a_small_stack() {
    // Each walk was a recursion, which overflowed this stack (see the negative control in
    // STATUS.md, T2-types-rest part 3); each is now a loop with a stack of its own.
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            let p = ors(0, DEEP, Part::literal);
            assert_eq!(p.union_rows().map(|r| r.len()), Some(DEEP));
            assert!(!p.eval(&|_| false));
            assert!(p.eval(&|a| *a == atom(0)));
            assert_eq!(p.eval3(&|_| None), None);
            assert_eq!(p.eval3(&|a| Some(*a == atom(0))), Some(true));
            assert_eq!(p.distinct_atoms().len(), DEEP);
            assert_eq!(p.forced(), (Vec::new(), Vec::new()));
            let only = |x: Row| move |a: &Row| (*a != x).then_some(false);
            assert_eq!(p.restrict(&only(atom(0))), Part::literal(atom(0)));
            let q = settled_by_one_pin(0, DEEP);
            assert_eq!(q.settle().distinct_atoms().len(), 2 * (DEEP - 1));
            let b = Part::Bdd(meet(0, DEEP));
            assert_eq!(b.eval3(&|_| None), None);
            assert_eq!(b.eval3(&|_| Some(true)), Some(true));
            assert_eq!(b.distinct_atoms().len(), DEEP);
            assert_eq!(b.restrict(&|_| None), b);
            let all_but = |x: Row| move |a: &Row| (*a != x).then_some(true);
            assert_eq!(b.restrict(&all_but(atom(0))), Part::literal(atom(0)));
        })
        .unwrap()
        .join()
        .unwrap();
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

#[test]
fn the_walks_over_parts_scale() {
    let n = 1 << 12;
    let sizes = [n, scaling::FACTOR * n];
    let ors: BTreeMap<usize, Part<Row>> = sizes
        .map(|m| (m, ors(10 * m as u64, m, Part::literal)))
        .into();
    let pins: BTreeMap<usize, Part<Row>> = sizes
        .map(|m| (m, settled_by_one_pin(20 * m as u64, m)))
        .into();
    let meets: BTreeMap<usize, Part<Row>> =
        sizes.map(|m| (m, Part::Bdd(meet(30 * m as u64, m)))).into();
    let ladders: BTreeMap<usize, Part<Row>> = sizes.map(|m| (m, ladder(40 * m as u64, m))).into();
    scaling::check("eval of an expression, by depth", n, |m| {
        assert!(!ors[&m].eval(&|_| false));
    });
    // Every expression but the top one is read twice, the second time from the memo.
    scaling::check(
        "eval of an expression whose operands are shared, by depth",
        n,
        |m| {
            assert!(!ladders[&m].eval(&|_| false));
        },
    );
    scaling::check("eval3 of an expression and a diagram, by depth", n, |m| {
        assert_eq!(ors[&m].eval3(&|_| None), None);
        assert_eq!(meets[&m].eval3(&|_| None), None);
    });
    scaling::check(
        "the atoms of an expression and a diagram, by depth",
        n,
        |m| {
            assert_eq!(ors[&m].distinct_atoms().len(), m);
            assert_eq!(meets[&m].distinct_atoms().len(), m);
        },
    );
    scaling::check("the union's rows, by depth", n, |m| {
        assert_eq!(ors[&m].union_rows().map(|r| r.len()), Some(m));
    });
    scaling::check("the forced atoms of an expression, by depth", n, |m| {
        assert_eq!(ors[&m].forced(), (Vec::new(), Vec::new()));
    });
    scaling::check(
        "restricting an expression and a diagram, by depth",
        n,
        |m| {
            assert_eq!(ors[&m].restrict(&|_| Some(false)), Part::leaf(false));
            assert_eq!(meets[&m].restrict(&|_| None), meets[&m]);
        },
    );
    scaling::check("settling on one pin, by depth", n, |m| {
        assert_eq!(pins[&m].settle().distinct_atoms().len(), 2 * (m - 1));
    });
}

/// The list `x_0 & … & x_{m-2} & !x_{m-1}`, on the atoms of [`meet`]`(base, m)`, which
/// meets it in no value: the meet of the two joins each literal of one to the other.
fn meet_but_last(base: u64, m: usize) -> Bdd<Row> {
    let last = atom(base + m as u64 - 1);
    meet(base, m - 1).and_literal((last, false))
}

/// The choice `c_{m-1} & (… (c_1 & x_0 | !c_1 & y_1) …) | !c_{m-1} & y_{m-1}`, kept as
/// expressions nested `m - 1` deep, each `c_k` the atom `base + k`, `x_0` the atom
/// `base + m`, and `y_k` the atom `leaves + k`. Its complement, and its union with another
/// such chain on the same conditions, are each built a level at a time, through the choice
/// each level is.
fn choices(base: u64, leaves: u64, m: usize) -> Part<Row> {
    (1..m as u64).fold(Part::literal(atom(base + m as u64)), |p, k| {
        let c = Part::literal(atom(base + k));
        Part::expr(Form::Or(
            Part::expr(Form::And(c.clone(), p)),
            Part::expr(Form::And(c.not(), Part::literal(atom(leaves + k)))),
        ))
    })
}

/// How deep the lists of the depth test go: the diagrams' `apply` and `flip`, as
/// recursions, overflowed the 8 MiB stack of a main thread at 60,000 (and ran at 30,000).
const DIAGRAM_DEPTH: usize = 100_000;

/// How deep the choices of the depth test go: `Part::not` and `Part::zip`, as a mutual
/// recursion through `choice`, `choice_of`, `same_as_not` and `choose`, overflowed the
/// 8 MiB stack at 10,000 (and ran at 6,000).
const CHOICE_DEPTH: usize = 20_000;

#[test]
fn the_connectives_on_parts_nested_deep_run_on_the_default_stack() {
    // On the test thread's own stack (2 MiB unless RUST_MIN_STACK says otherwise), a
    // quarter of the 8 MiB the depths above overflowed.
    let (a, b) = (meet(0, DIAGRAM_DEPTH), meet_but_last(0, DIAGRAM_DEPTH));
    assert_eq!(a.zip_chain(&b, Op::And), Some(Bdd::Leaf(false)));
    let not_a = a.not();
    assert_eq!(not_a.not(), a);
    assert_eq!(a.zip_chain(&not_a, Op::Or), Some(Bdd::Leaf(true)));
    let l = b.list();
    assert_eq!(l.blocks.len(), 1);
    assert_eq!(l.blocks[0].1.len(), DIAGRAM_DEPTH);
    let base = 10 * DIAGRAM_DEPTH as u64;
    let p = choices(base, base + 2 * CHOICE_DEPTH as u64, CHOICE_DEPTH);
    let q = choices(base, base + 4 * CHOICE_DEPTH as u64, CHOICE_DEPTH);
    let not_p = p.not();
    assert_eq!(not_p.not(), p);
    assert_eq!(p.zip(&not_p, Op::And), Part::leaf(false));
    let both = p.zip(&q, Op::Or);
    // Every condition and `x_0` held: both chains take the deepest branch, `x_0`.
    let deepest: BTreeSet<Row> = (1..=CHOICE_DEPTH as u64).map(|k| atom(base + k)).collect();
    assert!(p.eval(&|a| deepest.contains(a)));
    assert!(both.eval(&|a| deepest.contains(a)));
    // No condition held, and the top leaf of `q`: only `q` takes it.
    let top_of_q = atom(base + 4 * CHOICE_DEPTH as u64 + CHOICE_DEPTH as u64 - 1);
    assert!(both.eval(&|a| *a == top_of_q));
    assert!(!p.eval(&|a| *a == top_of_q));
}

#[test]
fn the_connectives_on_parts_scale_by_depth() {
    // Inputs Θ(m) deep, built before any run is timed; each connective meets each node or
    // expression a constant number of times.
    let n = 1 << 12;
    let meets = scaling::inputs(n, |m| {
        let base = 100 * m as u64;
        (meet(base, m), meet_but_last(base, m))
    });
    // A union keeps the complements it makes with the expressions, so each run of it takes
    // chains of its own, on atoms of their own.
    let (small, large) = scaling::Meter::new().runs();
    type Pairs = std::sync::Mutex<Vec<(Part<Row>, Part<Row>)>>;
    let chains: BTreeMap<usize, Pairs> = [(n, small), (scaling::FACTOR * n, large)]
        .map(|(m, runs)| {
            let pairs = (0..runs as u64)
                .map(|i| {
                    let base = (1000 + 10 * i) * m as u64;
                    (
                        choices(base, base + 2 * m as u64, m),
                        choices(base, base + 4 * m as u64, m),
                    )
                })
                .collect();
            (m, std::sync::Mutex::new(pairs))
        })
        .into();
    scaling::check("the meet of two lists, by depth", n, |m| {
        let (a, b) = &meets[&m];
        assert_eq!(a.zip_chain(b, Op::And), Some(Bdd::Leaf(false)));
    });
    // The complement flips the value of the first block and allocates nothing.
    scaling::check_instructions_only("the complement of a list, by depth", n, 1, |m| {
        assert!(meets[&m].0.not() != meets[&m].0);
    });
    scaling::check("the union of two chains of choices, by depth", n, |m| {
        let (p, q) = chains[&m]
            .lock()
            .expect("the chains of a size")
            .pop()
            .expect("a pair of chains per run");
        assert!(p.zip(&q, Op::Or) != p);
    });
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
const SHAPES: u64 = 8;

/// The distance between the atoms of two offsets, above the atoms any one offset uses.
const SHAPE_STRIDE: u64 = 1 << 32;

/// The block of the two literals on the atoms `a` and `a + 1`, each taken.
fn pair_block(a: u64) -> Arc<Set<Row>> {
    set::insert(Some(&set::single((atom(a), true))), (atom(a + 1), true))
}

/// The list of `m` blocks of two literals, the atoms from `base`, the values alternating
/// from `true`: no block is merged or moved, so the list has `m` cells.
fn blocks(base: u64, m: usize) -> Bdd<Row> {
    let prefix = (0..m as u64)
        .map(|i| (i % 2 == 0, Some(pair_block(base + 2 * i))))
        .collect();
    Bdd::assemble(prefix, &Bdd::Leaf(m.is_multiple_of(2)))
}

#[test]
fn restricting_lists_that_share_a_tail_scales() {
    // Item CHAIN-restrict-memo: `m` lists, each a block of its own before one tail of `m`
    // blocks, restricted on an atom of the tail's last block with one memo. Memoized by
    // list, each walked and rebuilt the whole tail again, `O(m²)` in all; memoized by cell,
    // the cells of the tail are restricted once.
    let n = 1 << 9;
    // Each list rebuilds the tail's right spine where its last block shrinks, so the work
    // follows that spine; it is summed over the tails of `SHAPES` offsets of the atoms.
    let lists = scaling::inputs(n, |m| {
        (0..SHAPES)
            .map(|j| {
                let o = j * SHAPE_STRIDE;
                let tail = blocks(o + 8000, m);
                let Bdd::List(_, v) = &tail else {
                    unreachable!("a list of blocks has a cell")
                };
                let heads: Vec<Bdd<Row>> = (0..m as u64)
                    .map(|i| {
                        let head = (!*v, Some(pair_block(o + 30000 + 2 * i)));
                        Bdd::assemble(vec![head], &tail)
                    })
                    .collect();
                (atom(o + 8000 + 2 * (m as u64 - 1)), heads)
            })
            .collect::<Vec<_>>()
    });
    scaling::check("lists sharing a tail of m blocks, restricted", n, |m| {
        for (last, heads) in &lists[&m] {
            let fix = |a: &Row| (a == last).then_some(false);
            let mut memo = list::Memo::default();
            for l in heads {
                assert_ne!(l.restrict(&fix, &mut memo).id(), l.id());
            }
        }
    });
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
fn a_long_meet_joined_to_short_meets_scales() {
    // Item CHOICE-both-chains: a meet of `m` literals joined under `|` to `m` meets of two,
    // half of them with the complement of one of its literals, each a choice then. Listing
    // both chains at each join took `O(m)` a join; the longer is now only looked up.
    let n = 1 << 10;
    let parts = scaling::inputs(n, |m| {
        let long = Part::Bdd(meet(40000, m));
        let short: Vec<Part<Row>> = (0..m as u64)
            .map(|i| match i % 2 {
                0 => Part::Bdd(meet(50000 + 2 * i, 2)),
                _ => Part::Bdd(meet(50000 + 2 * i, 1).and_literal((atom(40000 + i), false))),
            })
            .collect();
        (long, short)
    });
    scaling::check("a meet of m literals joined to m meets of two", n, |m| {
        let (long, short) = &parts[&m];
        for s in short {
            assert!(matches!(long.zip(s, Op::Or), Part::Expr(_)));
        }
    });
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
fn rejoining_one_atom_of_each_block_scales() {
    // Item CHAIN-deep-atom: a list of `m` blocks, one atom of each joined again, the
    // deepest block first. The literal set false leaves a block at depth `d`; a list of
    // cells each before the next rebuilt the `d` cells above it, `O(m²)` in all. The
    // blocks in a treap by position rebuild `O(log m)` cells for each.
    let n = 1 << 9;
    let lists = scaling::inputs(n, |m| (joined_blocks(70000, m), m));
    scaling::check(
        "one atom of each of m blocks joined again, deepest first",
        n,
        |m| {
            let (f, m) = &lists[&m];
            let mut f = f.clone();
            for i in 0..*m as u64 {
                f = match i % 2 {
                    0 => f.or_literal((atom(70000 + 2 * i), true)),
                    _ => f.and_literal((atom(70000 + 2 * i), true)),
                };
            }
            assert!(f.cells().count() > 1);
        },
    );
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
    let mut seed = 0x2545_f491_4f6c_dd1du64;
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
    for _ in 0..30_000 {
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
