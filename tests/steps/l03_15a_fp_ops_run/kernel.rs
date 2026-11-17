//! The kernel primitives of plan row FP-ops-run, each on its own: the four entry steps that
//! walk a level in key order (`firstEntry`, `lastEntry`, `entryAfter`, `entryBefore`), and
//! `first` and `last`, the leaf at the least and greatest keypath; and the string functions of
//! plan row FP-ops-strings, `split`, `lines` and `concat`; and the reads of a list made by `++`
//! that build no map of it (plan row TEST-list-concat-no-map-build).

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

/// `[s0, s1, …]`: strings keyed by position from 0, as `split` and `lines` give them.
fn strings(xs: &[&str]) -> Value {
    fam((xs.iter().enumerate())
        .map(|(k, x)| (int(k as i64), s(x)))
        .collect())
}

/// `split` (plan row FP-ops-strings): every piece, empty ones included, and `""` split by a
/// nonempty separator is `[""]`, so the join law holds there too. An empty separator has no
/// answer: it is the failure `#emptySeparator`, for every text, `""` included (DESIGN L3.2,
/// author decision P314, plan row FP-ops-split-empty-separator).
#[test]
fn split_keeps_every_piece() {
    let split = |x: &str, sep: &str| run(Prim::Split, vec![s(x), s(sep)]);
    assert_eq!(split("", " "), strings(&[""]));
    assert_eq!(split("a  b", " "), strings(&["a", "", "b"]));
    assert_eq!(split("a,b,", ","), strings(&["a", "b", ""]));
    assert_eq!(split(",", ","), strings(&["", ""]));
    assert_eq!(split("a::b", "::"), strings(&["a", "b"]));
    assert_eq!(split("abc", "x"), strings(&["abc"]));
    assert_eq!(split("aaa", "aa"), strings(&["", "a"]));
    assert_eq!(split("hé€", "é"), strings(&["h", "€"]));
    assert_eq!(split("hé€", ""), Value::atom("emptySeparator"));
    assert_eq!(split("", ""), Value::atom("emptySeparator"));
}

/// `lines`: a line ends at `\n`, `\r\n` and a lone `\r`, and no empty line follows a line end
/// at the end of the text (step L3.2's cases, and a `\r\n` that is the last two bytes).
#[test]
fn lines_ends_a_line_at_each_line_end() {
    let lines = |x: &str| run(Prim::Lines, vec![s(x)]);
    assert_eq!(lines("a\rb"), strings(&["a", "b"]));
    assert_eq!(lines("a\r\nb"), strings(&["a", "b"]));
    assert_eq!(lines("a\n\rb"), strings(&["a", "", "b"]));
    assert_eq!(lines("a\r\r\n"), strings(&["a", ""]));
    assert_eq!(lines(""), strings(&[]));
    assert_eq!(lines("\n"), strings(&[""]));
    assert_eq!(lines("a\n"), strings(&["a"]));
    assert_eq!(lines("a\r\n"), strings(&["a"]));
    assert_eq!(lines("a\r"), strings(&["a"]));
    assert_eq!(lines("\n\n"), strings(&["", ""]));
}

/// `concat(pieces, sep: s)`: the pieces in key order with `s` between each two, and the join
/// law over `split` on a set of texts with the separator in every place.
#[test]
fn concat_joins_in_key_order_and_undoes_split() {
    let join = |f: Value, sep: &str| run(Prim::Join, vec![f, s(sep)]);
    assert_eq!(join(strings(&["a", "", "b"]), ","), s("a,,b"));
    assert_eq!(join(strings(&["a", "b"]), ""), s("ab"));
    assert_eq!(join(strings(&[]), ","), s(""));
    assert_eq!(join(strings(&["x"]), ","), s("x"));
    // Key order, not the order written.
    let backward = fam(vec![(int(1), s("b")), (int(0), s("a"))]);
    assert_eq!(join(backward, "-"), s("a-b"));
    for text in ["", ",", ",,", "a", "a,", ",a", "a,,b,", "é,€,"] {
        for sep in [",", ",,", "a"] {
            let pieces = run(Prim::Split, vec![s(text), s(sep)]);
            assert_eq!(join(pieces, sep), s(text), "{text:?} by {sep:?}");
        }
    }
}

/// A loose atom operand is the result; `concat` of a family with an entry that is not a
/// string is refused, as a primitive given the wrong kind of value is.
#[test]
fn string_functions_pass_atoms_and_refuse_other_entries() {
    let a = Value::atom("bad");
    assert_eq!(run(Prim::Split, vec![a.clone(), s(",")]), a);
    assert_eq!(run(Prim::Split, vec![s("x"), a.clone()]), a);
    assert_eq!(run(Prim::Lines, vec![a.clone()]), a);
    assert_eq!(run(Prim::Join, vec![a.clone(), s(",")]), a);
    let ints = fam(vec![(int(0), int(1))]);
    let t = Term::Prim(Prim::Join, vec![lit(ints), lit(s(","))]);
    assert!(eval(&t).is_err(), "concat of ints");
}

/// The list `[0, 10, …, 10(n-1)]` made by `n - 1` concatenations of one-entry lists nested to the
/// right, `[0] ++ ([10] ++ (… ++ [10(n-1)]))`: a list made by `++` whose ordered map is not built
/// (plan row TEST-list-concat-no-map-build). Each call makes a new list, so a map built by one read
/// is not found built by the next.
fn joined(n: i64) -> Value {
    let one = |i: i64| Family::of([(int(0), int(10 * i))]);
    let list = (0..n - 1)
        .rev()
        .fold(one(n - 1), |acc, i| one(i).concat(&acc).unwrap());
    Value::Family(list)
}

/// The same list as [`joined`], built as one map.
fn flat(n: i64) -> Value {
    fam((0..n).map(|i| (int(i), int(10 * i))).collect())
}

/// `p` on `args`, asserting that no list made by `++` had its map built while it ran.
fn unflattened(p: Prim, args: Vec<Value>) -> Value {
    let before = zed_kernel::value::lists_flattened();
    let out = run(p, args);
    let built = zed_kernel::value::lists_flattened() - before;
    assert_eq!(
        built, 0,
        "{p:?} built the map of {built} list(s) made by `++`"
    );
    out
}

/// The reads by key, `in`, the count, the four entry steps, `first`, `last` and `++` itself on a
/// list made by `++` give what they give on the same list built as one map, and build no map
/// (COMPLEXITY.md F223: each is O(log n) or O(1) on the joined list).
#[test]
fn reads_of_a_joined_list_build_no_map() {
    let n = 50;
    let none = Value::atom("notFound");
    let oob = Value::atom("outOfBounds");
    for (k, want_get, want_at) in [
        (int(0), int(0), int(0)),
        (int(25), int(250), int(250)),
        (int(49), int(490), int(490)),
        (int(50), none.clone(), oob.clone()),
        (int(-1), none.clone(), oob.clone()),
        (s("a"), none.clone(), oob.clone()),
    ] {
        for (p, want) in [
            (Prim::Get, &want_get),
            (Prim::TupleGet, &want_get),
            (Prim::At, &want_at),
        ] {
            assert_eq!(
                unflattened(p, vec![joined(n), k.clone()]),
                *want,
                "{p:?} at {k}"
            );
            assert_eq!(
                run(p, vec![flat(n), k.clone()]),
                *want,
                "{p:?} at {k}, one map"
            );
        }
        let held = want_at != oob;
        assert_eq!(
            unflattened(Prim::Has, vec![k, joined(n)]),
            Value::Bool(held)
        );
    }
    assert_eq!(unflattened(Prim::Count, vec![joined(n)]), int(n));
    let first = pair(int(0), int(0));
    let last = pair(int(49), int(490));
    assert_eq!(unflattened(Prim::FirstEntry, vec![joined(n)]), first);
    assert_eq!(unflattened(Prim::LastEntry, vec![joined(n)]), last);
    let step = |p: Prim, k: i64| unflattened(p, vec![joined(n), pair(int(k), int(0))]);
    assert_eq!(step(Prim::EntryAfter, 25), pair(int(26), int(260)));
    assert_eq!(step(Prim::EntryBefore, 25), pair(int(24), int(240)));
    assert_eq!(step(Prim::EntryAfter, 49), end());
    assert_eq!(step(Prim::EntryBefore, 0), end());
    assert_eq!(step(Prim::EntryAfter, -5), first);
    assert_eq!(step(Prim::EntryBefore, 99), last);
    assert_eq!(unflattened(Prim::First, vec![joined(n)]), int(0));
    assert_eq!(unflattened(Prim::Last, vec![joined(n)]), int(490));
    let both = unflattened(Prim::ListConcat, vec![joined(n), joined(n)]);
    assert_eq!(unflattened(Prim::Count, vec![both.clone()]), int(2 * n));
    assert_eq!(unflattened(Prim::Get, vec![both, int(75)]), int(250));
}

/// `first` and `last` descend through a list of lists, each made by `++`, building no map.
#[test]
fn first_and_last_descend_through_joined_lists() {
    let outer = |a: Value, b: Value| {
        let one = |v: Value| Family::of([(int(0), v)]);
        Value::Family(one(a).concat(&one(b)).unwrap())
    };
    let f = outer(joined(3), joined(4));
    assert_eq!(unflattened(Prim::First, vec![f.clone()]), int(0));
    assert_eq!(unflattened(Prim::Last, vec![f]), int(30));
}

/// `==`, `!=`, the order and `min`/`max` of a list made by `++` against lists of other sizes,
/// against itself, against an equal list built as one map, and against lists that differ at an
/// entry, give what the same lists built as one map give, and build no map.
#[test]
fn comparisons_of_a_joined_list_build_no_map() {
    let n = 50;
    let differs = |at: i64| {
        fam((0..n)
            .map(|i| (int(i), int(10 * i + i64::from(i == at))))
            .collect())
    };
    let others = [
        flat(1),
        flat(n - 1),
        flat(n + 1),
        flat(n),
        differs(0),
        differs(n / 2),
        differs(n - 1),
        fam(Vec::new()),
        fam(vec![(s("a"), int(0))]),
    ];
    for other in &others {
        for p in [Prim::Eq, Prim::Ne, Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge] {
            let want = run(p, vec![flat(n), other.clone()]);
            let got = unflattened(p, vec![joined(n), other.clone()]);
            assert_eq!(got, want, "{p:?} against {other}");
            let want = run(p, vec![other.clone(), flat(n)]);
            let got = unflattened(p, vec![other.clone(), joined(n)]);
            assert_eq!(got, want, "{p:?} from {other}");
            let got = unflattened(p, vec![joined(n), joined(n)]);
            assert_eq!(
                got,
                run(p, vec![flat(n), flat(n)]),
                "{p:?} of two joined lists"
            );
        }
        for p in [Prim::Min, Prim::Max] {
            let want = run(p, vec![flat(n), other.clone()]);
            let got = unflattened(p, vec![joined(n), other.clone()]);
            // The two are equal under `==`; which one is given is read by its count.
            assert_eq!(
                unflattened(Prim::Count, vec![got]),
                run(Prim::Count, vec![want]),
                "{p:?} against {other}"
            );
        }
    }
    let x = joined(n);
    for (p, want) in [
        (Prim::Eq, true),
        (Prim::Ne, false),
        (Prim::Le, true),
        (Prim::Lt, false),
    ] {
        assert_eq!(
            unflattened(p, vec![x.clone(), x.clone()]),
            Value::Bool(want),
            "{p:?} self"
        );
    }
    // Rust's `==`, the identity the kernel's maps and memo tables use: by the count, the
    // sharing, or the entries read in order.
    let before = zed_kernel::value::lists_flattened();
    assert!(x == x.clone() && x == joined(n) && x == flat(n) && flat(n) == x);
    assert!(x != joined(n - 1) && x != differs(n / 2) && differs(0) != x);
    assert_eq!(zed_kernel::value::lists_flattened(), before, "Rust's `==`");
}

/// A list made by `++` hashes as the same list built as one map, and as a key of a family it is
/// found by an equal list either way, building no map: the hash reads the count, and the key
/// order reads the entries to the first difference.
#[test]
fn a_joined_list_as_a_key_builds_no_map() {
    use std::hash::{BuildHasher, RandomState};
    let n = 50;
    let hasher = RandomState::new();
    let before = zed_kernel::value::lists_flattened();
    assert_eq!(hasher.hash_one(joined(n)), hasher.hash_one(flat(n)));
    assert_eq!(zed_kernel::value::lists_flattened(), before, "the hash");
    let keyed = fam(vec![
        (flat(n), int(1)),
        (flat(n - 1), int(2)),
        (joined(3), int(3)),
    ]);
    assert_eq!(
        unflattened(Prim::Has, vec![joined(n), keyed.clone()]),
        Value::Bool(true)
    );
    assert_eq!(
        unflattened(Prim::Get, vec![keyed.clone(), joined(n)]),
        int(1)
    );
    assert_eq!(
        unflattened(Prim::Get, vec![keyed.clone(), joined(n - 1)]),
        int(2)
    );
    assert_eq!(unflattened(Prim::Get, vec![keyed, flat(3)]), int(3));
}

/// A union that holds a list made by `++` beneath a key builds no map of that list when it does
/// not read the list's entries: beside a key the other side lacks, the list is shared whole; under
/// a leaf of the other side, the collision is at the list's first keypath, read in O(log n) (plan
/// row TEST-list-map-build-callers-complete). An open range there is read by its first entry too,
/// not walked.
#[test]
fn a_union_holding_a_joined_list_builds_no_map() {
    use zed_kernel::KernelError;
    let n = 50;
    let at = |k: i64, v: Value| Family::of([(int(k), v)]);
    let unbuilt = |a: &Family, b: &Family| {
        let before = zed_kernel::value::lists_flattened();
        let out = a.union(b);
        assert_eq!(
            zed_kernel::value::lists_flattened(),
            before,
            "{a} ∪ {b} built a map"
        );
        out
    };
    let both = unbuilt(&at(0, joined(n)), &at(1, int(5))).unwrap();
    assert_eq!(
        unflattened(Prim::Count, vec![Value::Family(both.clone())]),
        int(2)
    );
    assert_eq!(
        unflattened(Prim::Get, vec![Value::Family(both), int(0)]),
        joined(n)
    );
    let collision = |keypath: Vec<Value>| KernelError::Collision { keypath };
    assert_eq!(
        unbuilt(&at(0, int(1)), &at(0, joined(n))).unwrap_err(),
        collision(vec![int(0), int(0)])
    );
    let nested = |v: Value| {
        let one = |v: Value| Family::of([(int(0), v)]);
        Value::Family(one(v).concat(&one(int(7))).unwrap())
    };
    assert_eq!(
        unbuilt(&at(0, int(1)), &at(0, nested(joined(n)))).unwrap_err(),
        collision(vec![int(0), int(0), int(0)])
    );
    let open = Value::Family(Family::range_from(int(3)));
    assert_eq!(
        unbuilt(&at(0, int(1)), &at(0, open)).unwrap_err(),
        collision(vec![int(0), int(3)])
    );
}

/// A walk over every entry builds the map of a list made by `++` once, O(n), which the copies of
/// the list share: printing it twice builds one map, and its text is the one map's.
#[test]
fn a_walk_builds_the_map_once() {
    let x = joined(5);
    let before = zed_kernel::value::lists_flattened();
    let shown = run(Prim::Show, vec![x.clone()]);
    assert_eq!(zed_kernel::value::lists_flattened() - before, 1);
    assert_eq!(run(Prim::Show, vec![x]), shown);
    assert_eq!(zed_kernel::value::lists_flattened() - before, 1);
    assert_eq!(shown, run(Prim::Show, vec![flat(5)]));
}
