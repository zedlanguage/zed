//! The kernel primitives of plan row FP-ops-run, each on its own: the four entry steps that
//! walk a level in key order (`firstEntry`, `lastEntry`, `entryAfter`, `entryBefore`), and
//! `first` and `last`, the leaf at the least and greatest keypath.

use zed_kernel::term::build::lit;
use zed_kernel::{Family, Prim, Term, Value, eval};
use zed_tests::kernel::s;

/// `p` applied to `args`, evaluated.
fn run(p: Prim, args: Vec<Value>) -> Value {
    eval(&Term::Prim(p, args.into_iter().map(lit).collect())).unwrap()
}

fn fam(entries: Vec<(Value, Value)>) -> Value {
    Value::Family(Family::of(entries))
}

fn int(i: i64) -> Value {
    Value::Int(i)
}

fn pair(k: Value, v: Value) -> Value {
    Value::tuple(vec![k, v])
}

fn end() -> Value {
    Value::tuple(Vec::new())
}

/// `{"b" -> 20, "a" -> 10, "c" -> 30}`, whose keys are not in the order written.
fn abc() -> Value {
    fam(vec![
        (s("b"), int(20)),
        (s("a"), int(10)),
        (s("c"), int(30)),
    ])
}

#[test]
fn first_and_last_entry_are_the_ends_in_key_order() {
    assert_eq!(run(Prim::FirstEntry, vec![abc()]), pair(s("a"), int(10)));
    assert_eq!(run(Prim::LastEntry, vec![abc()]), pair(s("c"), int(30)));
    let empty = fam(Vec::new());
    assert_eq!(run(Prim::FirstEntry, vec![empty.clone()]), end());
    assert_eq!(run(Prim::LastEntry, vec![empty]), end());
}

#[test]
fn entry_after_and_before_step_through_the_keys() {
    let after = |k: &str| run(Prim::EntryAfter, vec![abc(), pair(s(k), int(0))]);
    let before = |k: &str| run(Prim::EntryBefore, vec![abc(), pair(s(k), int(0))]);
    assert_eq!(after("a"), pair(s("b"), int(20)));
    assert_eq!(after("b"), pair(s("c"), int(30)));
    assert_eq!(after("c"), end());
    assert_eq!(before("c"), pair(s("b"), int(20)));
    assert_eq!(before("a"), end());
    // A key the family does not hold: the nearest held key on that side.
    assert_eq!(after("ab"), pair(s("b"), int(20)));
    assert_eq!(before("ab"), pair(s("a"), int(10)));
    assert_eq!(after(""), pair(s("a"), int(10)));
    assert_eq!(before("z"), pair(s("c"), int(30)));
}

/// Every key of a family big enough to have inner nodes is reached once, in order, from both
/// ends, against the keys sorted by Rust.
#[test]
fn a_walk_visits_every_key_once_in_order() {
    let n = 1000_i64;
    // The keys 0, 7, 14, … in a scrambled order.
    let keys: Vec<i64> = (0..n).map(|i| (i * 389) % n * 7).collect();
    let f = fam(keys.iter().map(|&k| (int(k), int(-k))).collect());
    let mut sorted = keys.clone();
    sorted.sort();
    let walk = |start: Prim, step: Prim| {
        let mut seen = Vec::new();
        let mut e = run(start, vec![f.clone()]);
        while e != end() {
            let Value::Tuple(items) = &e else {
                panic!("an entry step gave {e:?}")
            };
            let Value::Int(k) = items[0] else {
                panic!("a key {:?}", items[0])
            };
            assert_eq!(items[1], int(-k));
            seen.push(k);
            e = run(step, vec![f.clone(), e.clone()]);
        }
        seen
    };
    assert_eq!(walk(Prim::FirstEntry, Prim::EntryAfter), sorted);
    let mut down = sorted.clone();
    down.reverse();
    assert_eq!(walk(Prim::LastEntry, Prim::EntryBefore), down);
}

/// A key that is an atom is data in the entry tuple, and the end is `()`, not an atom.
#[test]
fn an_atom_key_is_an_entry_not_the_end() {
    let f = fam(vec![(Value::atom("none"), int(1)), (int(5), int(2))]);
    let first = run(Prim::FirstEntry, vec![f.clone()]);
    let last = run(Prim::LastEntry, vec![f.clone()]);
    assert_ne!(first, end());
    assert_ne!(last, end());
    assert_ne!(run(Prim::EntryAfter, vec![f.clone(), first.clone()]), end());
    assert_eq!(run(Prim::EntryAfter, vec![f.clone(), last.clone()]), end());
    assert_eq!(run(Prim::EntryBefore, vec![f, first]), end());
}

/// A loose atom given for the family is the result, as at every primitive that computes.
#[test]
fn a_loose_atom_family_passes_through() {
    let a = Value::atom("bad");
    for p in [Prim::FirstEntry, Prim::LastEntry, Prim::First, Prim::Last] {
        assert_eq!(run(p, vec![a.clone()]), a, "{p:?}");
    }
    for p in [Prim::EntryAfter, Prim::EntryBefore] {
        assert_eq!(run(p, vec![a.clone(), pair(int(0), int(0))]), a, "{p:?}");
    }
}

#[test]
fn first_and_last_descend_to_the_ends_of_the_keypaths() {
    // {1 -> {"y" -> 3, "x" -> 4}, 0 -> {"q" -> 5}, 2 -> {"a" -> 6, "b" -> 7}}
    let f = fam(vec![
        (int(1), fam(vec![(s("y"), int(3)), (s("x"), int(4))])),
        (int(0), fam(vec![(s("q"), int(5))])),
        (int(2), fam(vec![(s("a"), int(6)), (s("b"), int(7))])),
    ]);
    assert_eq!(run(Prim::First, vec![f.clone()]), int(5));
    assert_eq!(run(Prim::Last, vec![f]), int(7));
    let flat = fam(vec![(int(2), int(9)), (int(1), int(8))]);
    assert_eq!(run(Prim::First, vec![flat.clone()]), int(8));
    assert_eq!(run(Prim::Last, vec![flat]), int(9));
}

/// An empty level on the way, at the top or below it, gives `#none`.
#[test]
fn an_empty_level_gives_none() {
    let none = Value::atom("none");
    assert_eq!(run(Prim::First, vec![fam(Vec::new())]), none);
    let inner_empty = fam(vec![(int(0), fam(Vec::new())), (int(1), int(4))]);
    assert_eq!(run(Prim::First, vec![inner_empty.clone()]), none);
    assert_eq!(run(Prim::Last, vec![inner_empty]), int(4));
}

#[test]
fn a_tuple_entry_is_a_leaf() {
    let f = fam(vec![(int(0), pair(int(1), int(2)))]);
    assert_eq!(run(Prim::First, vec![f]), pair(int(1), int(2)));
}
