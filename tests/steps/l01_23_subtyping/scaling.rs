//! The tuple and morphism parts at the rule of low complexity (DESIGN.md Part G). The union of
//! `C` differences `m(i) - m(i + 1000)` has a decision diagram of `2^C` nodes, since every
//! `m(i)` is ordered before every `m(i + 1000)`. A connective whose diagram would have more
//! nodes than its operands keeps its operands instead, so building the union and its
//! complement stay linear in `C`, and the queries on them are decided exactly: `b <: b | a` by
//! expanding on `b`, which both sides share, and `!b & a` by passing over paths whose taken
//! types are disjoint. A product of tuple types covered by many negated ones is split into disjoint pieces, and
//! a negated type disjoint from a piece is passed over.

use std::sync::Mutex;
use std::sync::atomic::Ordering::Relaxed;
use zed_kernel::Value;
use zed_kernel::types::{Type, Universe, Verdict};
use zed_tests::scaling;

fn lit(i: usize) -> Type {
    Type::lit(&Value::Int(i as i64)).unwrap()
}

fn morphism(i: usize) -> Type {
    Type::morphism(Type::empty(), Type::top(), lit(i))
}

fn pair(i: usize) -> Type {
    Type::tuple(vec![lit(i), Type::top()])
}

/// The union of `c` differences of the atoms `atom` makes.
fn union(c: usize, atom: fn(usize) -> Type) -> Type {
    (0..c).fold(Type::empty(), |u, i| &u | &(&atom(i) - &atom(i + 1000)))
}

fn run(c: usize, atom: fn(usize) -> Type) {
    let b = union(c, atom);
    let n = !&b;
    assert!(!(&n & &atom(5000)).is_empty());
    assert!(b.subtype(&(&b | &atom(5000))));
}

#[test]
fn small_unions_are_still_decided() {
    // The answers `the_parts_scale` times, at a count small enough that unions of diagrams
    // stay diagrams.
    for atom in [morphism as fn(usize) -> Type, pair] {
        let b = union(6, atom);
        assert!(b.subtype(&(&b | &atom(5000))), "{b}");
        assert!(!b.subtype(&atom(0)), "{b}");
        assert!((&b - &b).is_empty(), "{b}");
    }
}

/// The tuples `(i, b + j)` for `i, j < n`, as a product and as the union of its `n²` cells.
fn grid(n: usize, b: usize) -> (Type, Type) {
    let set = |b: usize| Type::union_all((0..n).map(|i| lit(b + i)));
    let cells = Type::union_all((0..n * n).map(|k| Type::tuple(vec![lit(k / n), lit(b + k % n)])));
    (Type::tuple(vec![set(0), set(b)]), cells)
}

#[test]
fn a_cell_left_out_is_found() {
    for n in [2, 3, 5, 8] {
        let (p, cells) = grid(n, 0);
        let hole = Type::tuple(vec![lit(n / 2), lit(n - 1)]);
        let rest = &(&p - &cells) | &hole;
        assert!(!(&p - &(&cells - &hole)).is_empty(), "n = {n}");
        assert!((&rest - &hole).is_empty(), "n = {n}");
    }
}

#[test]
fn negated_types_disjoint_from_the_product_are_passed_over() {
    // The decoy `(bits(i), 1000 + i)`, with `bits(i)` the numbers below 8192 with bit `i` set,
    // misses `(0..8192, 0)` in the second component, and splitting on it would cut every piece
    // in two in the first: `2^13` pieces for the 13 decoys, unless a disjoint one is passed
    // over. The pieces are all met only when the answer is `true`, here once the two halves
    // of the product are reached.
    let set = |r: std::ops::Range<usize>| Type::union_all(r.map(lit));
    let bits = |i: usize| Type::union_all((0..8192).filter(|x| x >> i & 1 == 1).map(lit));
    let p = Type::tuple(vec![set(0..8192), lit(0)]);
    let halves =
        &Type::tuple(vec![set(0..4096), lit(0)]) | &Type::tuple(vec![set(4096..8192), lit(0)]);
    let decoys = Type::union_all((0..13).map(|i| Type::tuple(vec![bits(i), lit(1000 + i)])));
    assert!(!(&p - &decoys).is_empty());
    assert!((&p - &(&decoys | &halves)).is_empty());
}

/// The tuple `(… ((b, b), b + 1) …, b + d - 1)`, nested `d` deep.
fn nested(d: usize, b: usize) -> Type {
    (0..d).fold(lit(b), |t, i| Type::tuple(vec![t, lit(b + i)]))
}

#[test]
fn a_type_built_on_another_thread_is_the_same_type() {
    // Each thread keeps its own table of nodes, so the two copies are distinct nodes, and are
    // equal by their contents.
    let here = &nested(20, 7) | &Type::morphism(Type::empty(), Type::top(), nested(5, 3));
    let there = std::thread::spawn(|| {
        &nested(20, 7) | &Type::morphism(Type::empty(), Type::top(), nested(5, 3))
    })
    .join()
    .unwrap();
    assert_eq!(here, there);
    assert_eq!(here.to_string(), there.to_string());
    assert!(here.subtype(&there) && there.subtype(&here));
    assert!(!here.subtype(&nested(20, 8)));
}

#[test]
fn literal_and_atom_sets_combine_exactly() {
    // Every pair of signs and both connectives, with sets of unequal sizes in either order.
    let atom = |i: usize| Type::atom(&format!("a{i}"));
    let set = |r: std::ops::Range<usize>| {
        &Type::union_all(r.clone().map(lit)) | &Type::union_all(r.map(atom))
    };
    let (a, b) = (set(0..6), set(4..5));
    let both = &lit(4) | &atom(4);
    for (x, y) in [(&a, &b), (&b, &a)] {
        for (nx, ny) in [(false, false), (false, true), (true, false), (true, true)] {
            let x = if nx { !x } else { x.clone() };
            let y = if ny { !y } else { y.clone() };
            let (or, and) = (&x | &y, &x & &y);
            for v in (0..8).flat_map(|i| [lit(i), atom(i)]) {
                let (in_x, in_y) = (v.subtype(&x), v.subtype(&y));
                assert_eq!(v.subtype(&or), in_x || in_y, "{v} in {x} | {y}");
                assert_eq!(v.subtype(&and), in_x && in_y, "{v} in {x} & {y}");
            }
            assert_eq!(&(&or - &and) | &and, or);
        }
    }
    assert_eq!(&a & &b, both);
    assert_eq!(&(&a - &b) | &both, a);
}

/// The exclusive or of `types`, taken in order as `x = (x - t) | (t - x)`: the values in an odd
/// number of them.
fn parity(types: impl IntoIterator<Item = Type>) -> Type {
    types
        .into_iter()
        .fold(Type::empty(), |x, t| &(&x - &t) | &(&t - &x))
}

/// The exclusive or of the `c` tuple types `(b + i, b + i)`: a diagram of about `2c` nodes with
/// `2^(c - 1)` paths to `true`, holding `c` values.
fn odd_tuples(c: usize, b: usize) -> Type {
    parity((0..c).map(|i| Type::tuple(vec![lit(b + i), lit(b + i)])))
}

/// [`odd_tuples`] with its tuple types taken in the reverse order: the same set, built apart.
fn odd_tuples_reversed(c: usize, b: usize) -> Type {
    parity(
        (0..c)
            .rev()
            .map(|i| Type::tuple(vec![lit(b + i), lit(b + i)])),
    )
}

#[test]
fn exclusive_ors_of_none_one_and_more_tuple_types_are_compared_exactly() {
    // A set of switches, each a tuple type: a value is on when an odd number of the types
    // hold it. The parity of no type is empty and that of one is the type itself.
    let one = Type::tuple(vec![lit(0), lit(0)]);
    assert!(odd_tuples(0, 0).is_empty());
    assert!(odd_tuples(1, 0).equiv(&one));
    for c in [0, 1, 2, 7] {
        let (x, y) = (odd_tuples(c, 0), odd_tuples(c + 1, 0));
        // One more tuple type adds its one value: `x <: y` holds and `y <: x` does not.
        assert!(x.subtype(&y), "c = {c}");
        assert!(!y.subtype(&x), "c = {c}");
        assert!(!x.equiv(&y), "c = {c}");
        assert!(x.equiv(&odd_tuples_reversed(c, 0)), "c = {c}");
        assert_eq!(x.each_value().map(|v| v.count()), Some(c), "c = {c}");
    }
    // Tuple types of one column, overlapping: `(0 | 1)` and `(1 | 2)` share `(1)`, which is in
    // both and so in neither's parity; `(0 | 1) ^ (1 | 2) ^ (1)` holds all three values.
    let row = |vs: &[usize]| Type::tuple(vec![Type::union_all(vs.iter().map(|&v| lit(v)))]);
    let two = parity([row(&[0, 1]), row(&[1, 2])]);
    assert!(two.equiv(&(&row(&[0]) | &row(&[2]))));
    assert!(!two.equiv(&row(&[0, 1, 2])));
    assert!(parity([row(&[0, 1]), row(&[1, 2]), row(&[1])]).equiv(&row(&[0, 1, 2])));
    assert!(parity([row(&[0, 1]), row(&[0, 1])]).is_empty());
}

/// The `runs` inputs `make` builds for count `c` in case `k` of a test, each at a base no other
/// input uses, so that no run reads a result another kept.
fn pool<T>(c: usize, runs: usize, k: usize, make: impl Fn(usize, usize) -> T) -> Mutex<Vec<T>> {
    let base = |i: usize| 100_000_000 * k + 1_000_000 * (i + 1) + 1_000 * c;
    Mutex::new((0..runs).map(|i| make(c, base(i))).collect())
}

/// The rows of a decision tree on `c` columns of `{b, b + 1, b + 2}`: on column `i`, after
/// `b + 2` in every column before it, `b` and `b + 1` each end a row and `b + 2` goes on; on
/// the last column `b + 2` ends a row too. The rows cover the product of the columns.
fn decision_tree(c: usize, b: usize) -> (Type, Vec<Type>) {
    let column = Type::union_all((b..b + 3).map(lit));
    let row = |i: usize, v: usize| {
        Type::tuple(
            (0..c)
                .map(|j| match j.cmp(&i) {
                    std::cmp::Ordering::Less => lit(b + 2),
                    std::cmp::Ordering::Equal => lit(v),
                    std::cmp::Ordering::Greater => column.clone(),
                })
                .collect(),
        )
    };
    let mut rows: Vec<Type> = (0..c).flat_map(|i| [row(i, b), row(i, b + 1)]).collect();
    rows.push(row(c - 1, b + 2));
    (Type::tuple(vec![column.clone(); c]), rows)
}

#[test]
fn a_row_left_out_of_a_decision_tree_is_found() {
    for c in [1, 2, 5, 16] {
        let (p, rows) = decision_tree(c, 0);
        assert!(
            (&p - &Type::union_all(rows.iter().cloned())).is_empty(),
            "c = {c}"
        );
        for i in 0..rows.len() {
            let mut less = rows.clone();
            less.remove(i);
            assert!(
                !(&p - &Type::union_all(less)).is_empty(),
                "c = {c}, row {i} left out"
            );
        }
    }
}

/// A type the check does not prove empty may still be empty, so it promises no key: here
/// four pigeons in three holes, a Boolean tuple type that no valuation of its 4096 is in.
#[test]
fn a_type_not_proved_empty_promises_no_key() {
    let (pigeons, holes) = (4, 3);
    let d = pigeons * holes;
    let bit = Type::bool();
    let mut forbidden = Vec::new();
    let row = |hit: &dyn Fn(usize) -> bool, b: bool| {
        let lit = Type::lit(&Value::Bool(b)).unwrap();
        Type::tuple(
            (0..d)
                .map(|j| if hit(j) { lit.clone() } else { bit.clone() })
                .collect(),
        )
    };
    for p in 0..pigeons {
        forbidden.push(row(&|j| j / holes == p, false));
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                forbidden.push(row(&|j| j == p * holes + h || j == q * holes + h, true));
            }
        }
    }
    let unknown = &Type::tuple(vec![bit; d]) - &Type::union_all(forbidden);
    for mask in 0..1usize << d {
        let v = Value::Tuple((0..d).map(|j| Value::Bool(mask >> j & 1 != 0)).collect());
        assert!(
            !unknown.contains(&v),
            "a valuation is in the pigeonhole type"
        );
    }
    assert!(
        !unknown.is_empty(),
        "the check proves the pigeonhole type empty"
    );
    let m = Type::morphism(unknown, Type::empty(), Type::int());
    assert!(!m.is_empty(), "the empty morphism is in it");
    // A key shown in the type is promised: a scalar, a tuple, an atom's payload.
    let pair = Type::tuple(vec![Type::int(), Type::string()]);
    let tagged = Type::atom_with("p", &pair);
    for key in [Type::bool(), pair, tagged] {
        assert!(Type::morphism(key.clone(), Type::empty(), Type::int()).is_empty());
        assert!(Type::exact(key, Type::empty()).is_empty());
    }
}

/// The one-tuples of `ints` but `0` to `c - 1`, each taken out as its own tuple type.
fn past_excluded(c: usize, ints: Type) -> Type {
    &Type::tuple(vec![ints]) - &Type::union_all((0..c).map(|i| Type::tuple(vec![lit(i)])))
}

/// The pinwheel on `ends`: the square of them less four boxes around its middle
/// `(ends[1], ends[1])`, and less the middle too when `full`, which makes it empty.
fn pinwheel(full: bool, ends: [Type; 3]) -> Type {
    let set = |m: u8| Type::union_all((0..3).filter(|i| m >> i & 1 == 1).map(|i| ends[i].clone()));
    let boxes: &[[u8; 2]] = match full {
        false => &[[3, 1], [4, 3], [6, 4], [1, 6]],
        true => &[[3, 1], [4, 3], [6, 4], [1, 6], [2, 2]],
    };
    let square = Type::tuple(vec![set(7); 2]);
    &square
        - &Type::union_all(
            boxes
                .iter()
                .map(|b| Type::tuple(b.iter().map(|&m| set(m)).collect())),
        )
}

fn lit_i(i: i64) -> Type {
    Type::lit(&Value::Int(i)).unwrap()
}

/// What the ends of a pinwheel are: the integer `i` itself, the atom `#e((i,))` or the
/// one-tuple `(i,)`.
#[derive(Clone, Copy, Debug)]
enum End {
    Plain,
    Payload,
    OneTuple,
}

impl End {
    const ALL: [End; 3] = [End::Plain, End::Payload, End::OneTuple];

    /// The end made of `t`, a type of integers.
    fn of(self, t: Type) -> Type {
        match self {
            End::Plain => t,
            End::Payload => Type::atom_with("e", &Type::tuple(vec![t])),
            End::OneTuple => Type::tuple(vec![t]),
        }
    }

    fn ends(self, b: i64) -> [Type; 3] {
        [1, 2, 3].map(|j| self.of(lit_i(b + j)))
    }
}

/// The union of `k` pinwheels on disjoint integers, with ends of kind `end`.
fn pinwheels(k: usize, full: bool, end: End) -> Type {
    Type::union_all((0..k as i64).map(|i| pinwheel(full, end.ends(10 * i))))
}

/// [`pinwheels`] with the third end of the last pinwheel cofinite: made of its own integer and
/// every integer no pinwheel uses.
fn cofinite_pinwheels(k: usize, full: bool, end: End) -> Type {
    let k = k as i64;
    let used = Type::union_all((0..k).flat_map(|i| (1..=3).map(move |j| lit_i(10 * i + j))));
    let [a, b, _] = end.ends(10 * (k - 1));
    let third = end.of(&(&Type::int() - &used) | &lit_i(10 * (k - 1) + 3));
    let others = (0..k - 1).map(|i| pinwheel(full, end.ends(10 * i)));
    Type::union_all(others.chain([pinwheel(full, [a, b, third])]))
}

/// The pinwheel on `ends` as the model writes it: the union of the pairs of ends that no box
/// holds. The ends are disjoint, so this is the pinwheel exactly.
fn pinwheel_model(full: bool, ends: &[Type; 3]) -> Type {
    let boxes: &[[u8; 2]] = match full {
        false => &[[3, 1], [4, 3], [6, 4], [1, 6]],
        true => &[[3, 1], [4, 3], [6, 4], [1, 6], [2, 2]],
    };
    let pairs = (0..3).flat_map(|a| (0..3).map(move |b| (a, b)));
    let kept = pairs.filter(|&(a, b)| {
        !boxes
            .iter()
            .any(|m| m[0] >> a & 1 == 1 && m[1] >> b & 1 == 1)
    });
    Type::union_all(kept.map(|(a, b)| Type::tuple(vec![ends[a].clone(), ends[b].clone()])))
}

/// The value of the end of kind `end` made of the integer `i`.
fn end_value(end: End, i: i64) -> Value {
    let one = Value::Tuple(vec![Value::Int(i)].into_iter().collect());
    match end {
        End::Plain => Value::Int(i),
        End::OneTuple => one,
        End::Payload => Value::atom_with("e", vec![Value::Int(i)]),
    }
}

/// Checks the union of the pinwheels on `ends` against the model, `full` and not.
fn check_against_model(what: &str, ends: &[[Type; 3]]) {
    for full in [true, false] {
        let t = Type::union_all(ends.iter().map(|e| pinwheel(full, e.clone())));
        let model = Type::union_all(ends.iter().map(|e| pinwheel_model(full, e)));
        let want = match full || ends.is_empty() {
            true => Verdict::Empty,
            false => Verdict::Inhabited,
        };
        assert_eq!(t.verdict(), want, "{what}, full = {full}");
        assert_eq!(
            t.is_empty(),
            want == Verdict::Empty,
            "{what}, full = {full}"
        );
        assert!(t.equiv(&model), "{what}, full = {full}");
    }
}

#[test]
fn pinwheels_of_payload_and_one_tuple_ends_agree_with_the_model() {
    // An empty union of pinwheels whose ends are atom payloads or one-tuples was refused: the
    // settled form of a tuple part, which may hold more than the part, was read as showing a
    // tuple in it, and all atoms of one name and all tuples of one length fell in one class.
    for end in End::ALL {
        for k in [0, 1, 2, 3, 5] {
            let ends: Vec<[Type; 3]> = (0..k).map(|i| end.ends(10 * i)).collect();
            check_against_model(&format!("{end:?}, k = {k}"), &ends);
            let middles = Type::union_all((0..k).map(|i| {
                let m = end.of(lit_i(10 * i + 2));
                Type::tuple(vec![m.clone(), m])
            }));
            let (full, open) = (
                pinwheels(k as usize, true, end),
                pinwheels(k as usize, false, end),
            );
            assert!((&open - &full).equiv(&middles), "{end:?}, k = {k}");
            // Each pair of ends, of any two pinwheels, is in the open union exactly when the
            // model keeps it: only the middles of the full union are taken out.
            let ints = (0..k).flat_map(|i| (1..=3).map(move |j| 10 * i + j));
            for a in ints.clone() {
                for b in ints.clone() {
                    let v =
                        Value::Tuple([end_value(end, a), end_value(end, b)].into_iter().collect());
                    let same = a / 10 == b / 10;
                    let (x, y) = ((a % 10 - 1) as u8, (b % 10 - 1) as u8);
                    let boxed = [[3u8, 1], [4, 3], [6, 4], [1, 6]]
                        .iter()
                        .any(|m| m[0] >> x & 1 == 1 && m[1] >> y & 1 == 1);
                    let want = same && !boxed;
                    assert_eq!(open.contains(&v), want, "{end:?}, k = {k}, ({a}, {b})");
                    assert!(!full.contains(&v), "{end:?}, k = {k}, ({a}, {b})");
                }
            }
        }
    }
}

#[test]
fn pinwheels_of_nested_payloads_and_cofinite_ends_are_decided() {
    // A payload of a payload: `#e((#e((i,)),))`.
    let nested = |b: i64| [1, 2, 3].map(|j| End::Payload.of(End::Payload.of(lit_i(b + j))));
    for k in [0, 1, 3] {
        let ends: Vec<[Type; 3]> = (0..k).map(|i| nested(10 * i)).collect();
        check_against_model(&format!("nested payloads, k = {k}"), &ends);
    }
    // Ends of different kinds in one union, each pinwheel of one kind.
    let mixed: Vec<[Type; 3]> = (0..6)
        .map(|i| End::ALL[i % 3].ends(10 * i as i64))
        .collect();
    check_against_model("mixed kinds", &mixed);
    // One pinwheel whose ends are of different kinds.
    check_against_model(
        "kinds within a pinwheel",
        &[[
            End::Plain.of(lit_i(1)),
            End::Payload.of(lit_i(2)),
            End::OneTuple.of(lit_i(3)),
        ]],
    );
    // The cofinite end with payload and one-tuple ends.
    for end in End::ALL {
        for k in [1, 2, 4] {
            let full = cofinite_pinwheels(k, true, end);
            let open = cofinite_pinwheels(k, false, end);
            assert_eq!(full.verdict(), Verdict::Empty, "{end:?}, k = {k}");
            assert_eq!(open.verdict(), Verdict::Inhabited, "{end:?}, k = {k}");
            let middles = Type::union_all((0..k as i64).map(|i| {
                let m = end.of(lit_i(10 * i + 2));
                Type::tuple(vec![m.clone(), m])
            }));
            assert!((&open - &full).equiv(&middles), "{end:?}, k = {k}");
        }
    }
}

/// The ends of `k` pinwheels whose first two ends are the atoms `#e((b + 1,))` and
/// `#f((b + 2,))` and whose third end is the integer `b + 3`, with the third end of the last
/// pinwheel cofinite: its own integer and every integer no pinwheel uses.
fn cofinite_scalar_ends(k: usize) -> Vec<[Type; 3]> {
    let k = k as i64;
    let scalar = |i: i64| lit_i(10 * i + 3);
    let used = Type::union_all((0..k).map(scalar));
    (0..k)
        .map(|i| {
            let b = 10 * i;
            let third = match i == k - 1 {
                true => &(&Type::int() - &used) | &scalar(i),
                false => scalar(i),
            };
            [
                Type::atom_with("e", &Type::tuple(vec![lit_i(b + 1)])),
                Type::atom_with("f", &Type::tuple(vec![lit_i(b + 2)])),
                third,
            ]
        })
        .collect()
}

/// The union of the pinwheels on [`cofinite_scalar_ends`].
fn cofinite_scalar_pinwheels(k: usize, full: bool) -> Type {
    Type::union_all(
        cofinite_scalar_ends(k)
            .into_iter()
            .map(|e| pinwheel(full, e)),
    )
}

#[test]
fn pinwheels_with_a_cofinite_scalar_end_beside_payload_ends_agree_with_the_model() {
    for k in [1, 2, 3, 5] {
        check_against_model(
            &format!("a cofinite scalar end beside payload ends, k = {k}"),
            &cofinite_scalar_ends(k),
        );
    }
    // The open union holds each middle `(#f((b + 2,)), #f((b + 2,)))` and no pair of the
    // cofinite end, whose integers no box leaves out.
    let open = cofinite_scalar_pinwheels(3, false);
    let pair = |x: Value, y: Value| Value::Tuple([x, y].into_iter().collect());
    let f = |i: i64| Value::atom_with("f", vec![Value::Int(i)]);
    for b in [0, 10, 20] {
        assert!(open.contains(&pair(f(b + 2), f(b + 2))), "b = {b}");
    }
    assert!(!open.contains(&pair(Value::Int(1000), Value::Int(1000))));
    assert!(!open.contains(&pair(Value::Int(23), f(22))));
}

/// Ends that repeat the integer `b + 1` under a one-tuple and an atom payload: `(b + 1,)`, then
/// `#e((b + 1, b + 5))` when `pair` and `#e((b + 1,))` when not, then `(b + 3,)`. When `shared`
/// the two `b + 1` are one type, and when not two equal ones built apart.
fn repeating_ends(b: i64, pair: bool, shared: bool) -> [Type; 3] {
    let first = lit_i(b + 1);
    let again = match shared {
        true => first.clone(),
        false => lit_i(b + 1),
    };
    let payload = match pair {
        true => vec![again, lit_i(b + 5)],
        false => vec![again],
    };
    [
        Type::tuple(vec![first]),
        Type::atom_with("e", &Type::tuple(payload)),
        End::OneTuple.of(lit_i(b + 3)),
    ]
}

/// The union of `k` pinwheels on [`repeating_ends`].
fn repeating_pinwheels(k: usize, full: bool, pair: bool, shared: bool) -> Type {
    Type::union_all((0..k as i64).map(|i| pinwheel(full, repeating_ends(10 * i, pair, shared))))
}

#[test]
fn pinwheels_whose_ends_repeat_an_integer_agree_with_the_model() {
    // A type met twice inside a cell, the `b + 1` of `(b + 1,)` and of `#e((b + 1,))`, held
    // every value under the node of the second meeting when the two were one shared type, so
    // all pinwheels fell in one class; two equal types built apart were walked apart. The two
    // nodes are now merged, whichever way the type was built.
    for pair in [false, true] {
        for shared in [false, true] {
            for k in [0, 1, 2, 3, 5] {
                let ends: Vec<[Type; 3]> = (0..k)
                    .map(|i| repeating_ends(10 * i, pair, shared))
                    .collect();
                check_against_model(&format!("pair {pair}, shared {shared}, k = {k}"), &ends);
            }
        }
    }
}

/// The ends of `k` pinwheels of one-tuple ends, with the third end of the last one every tuple
/// but the other ends: a tuple type outside any other, which holds every one-tuple outside them.
fn negated_ends(k: usize) -> Vec<[Type; 3]> {
    let mut ends: Vec<[Type; 3]> = (0..k as i64).map(|i| End::OneTuple.ends(10 * i)).collect();
    let n = ends.len() * 3;
    let others = Type::union_all(ends.iter().flatten().take(n.saturating_sub(1)).cloned());
    if let Some(last) = ends.last_mut() {
        last[2] = &Type::universe(Universe::Tuple) - &others;
    }
    ends
}

/// The ends of `k` pinwheels whose ends are pairs with one first component, `(0, b + j)`.
fn first_component_ends(k: usize) -> Vec<[Type; 3]> {
    let end = |b: i64| [1, 2, 3].map(|j| Type::tuple(vec![lit_i(0), lit_i(b + j)]));
    (0..k as i64).map(|i| end(10 * i)).collect()
}

/// The union of the pinwheels on `ends`, full or with their middles.
fn pinwheels_on(ends: Vec<[Type; 3]>, full: bool) -> Type {
    Type::union_all(ends.into_iter().map(|e| pinwheel(full, e)))
}

/// A box of pairs disjoint from every end of [`negated_ends`] (`outside`) or of
/// [`first_component_ends`], whose ends it is shaped like.
fn far_box(outside: bool) -> Type {
    let end = match outside {
        true => Type::tuple(vec![lit_i(-5)]),
        false => Type::tuple(vec![lit_i(0), lit_i(-5)]),
    };
    Type::tuple(vec![end; 2])
}

/// [`check_against_model`], and the union full and not compared as subtypes, and less a box
/// it does not meet. The box is a tuple type, so the top of the union less it is a meet, and
/// the union is not split into its pinwheels at its top.
fn check_pinwheels(what: &str, ends: Vec<[Type; 3]>, outside: bool) {
    check_against_model(what, &ends);
    let (full, open) = (
        pinwheels_on(ends.clone(), true),
        pinwheels_on(ends.clone(), false),
    );
    assert!(full.subtype(&open) && !open.subtype(&full), "{what}");
    let model = Type::union_all(ends.iter().map(|e| pinwheel_model(false, e)));
    let less = &open - &far_box(outside);
    assert_eq!(less.verdict(), Verdict::Inhabited, "{what}");
    assert!(less.equiv(&model), "{what}");
    let less = &full - &far_box(outside);
    assert_eq!(less.verdict(), Verdict::Empty, "{what}");
}

#[test]
fn pinwheels_whose_ends_share_a_first_component_are_decided() {
    // The ends `(0, b + j)` share their first component, and the pinwheels are told apart on
    // the second (`overlaps`).
    for k in [1, 2, 4, 7] {
        check_pinwheels(
            &format!("one first component, k = {k}"),
            first_component_ends(k),
            false,
        );
    }
}

#[test]
fn pinwheels_with_an_end_outside_every_tuple_type_are_decided() {
    // The end outside every other is a tuple type less a union of one-tuples, which meets
    // only the last pinwheel's ends (`overlaps`).
    for k in [1, 2, 4, 7] {
        check_pinwheels(&format!("an end outside, k = {k}"), negated_ends(k), true);
    }
}

/// The checks of [`check_pinwheels`] as scaling checks on `k` pinwheels on `ends(k)`: the
/// verdict of the full union at k = 32 and 256, the two subtype checks at 64 and 512, and the
/// union less a box, empty and not, at 16 and 128.
fn pinwheels_scale(what: &str, ends: fn(usize) -> Vec<[Type; 3]>, outside: bool) {
    scaling::check(&format!("k pinwheels, {what}, empty, by k"), 32, |k| {
        Type::forget_emptiness();
        assert_eq!(pinwheels_on(ends(k), true).verdict(), Verdict::Empty);
    });
    scaling::check(&format!("k pinwheels, {what}, subtypes, by k"), 64, |k| {
        Type::forget_emptiness();
        let (full, open) = (pinwheels_on(ends(k), true), pinwheels_on(ends(k), false));
        assert!(full.subtype(&open) && !open.subtype(&full));
    });
    for full in [true, false] {
        let name = format!("k pinwheels, {what}, full = {full}, less a box, by k");
        scaling::check(&name, 16, |k| {
            Type::forget_emptiness();
            let want = match full {
                true => Verdict::Empty,
                false => Verdict::Inhabited,
            };
            assert_eq!(
                (&pinwheels_on(ends(k), full) - &far_box(outside)).verdict(),
                want
            );
        });
    }
}

/// The integer ends of `k` pinwheels, `10 i + 1` to `10 i + 3`, with the third end of the last
/// one cofinite when `cofinite`: its own integer and every integer no pinwheel uses.
fn plain_ends(k: usize, cofinite: bool) -> Vec<[Type; 3]> {
    let mut ends: Vec<[Type; 3]> = (0..k as i64).map(|i| End::Plain.ends(10 * i)).collect();
    if cofinite && let Some(last) = ends.last_mut() {
        let used =
            Type::union_all((0..k as i64).flat_map(|i| (1..=3).map(move |j| lit_i(10 * i + j))));
        last[2] = &(&Type::int() - &used) | &last[2];
    }
    ends
}

/// The pinwheels on `ends` written as one difference: the union of their squares less the
/// union of all their boxes. Each box lies in the square of its own pinwheel and the squares
/// share no value, so this is the union of the pinwheels. But its part is a meet, not a union
/// of parts that share no tuple type, so the rule that decides such a union one part at a
/// time (COMPLEXITY.md K80) does not apply, and only the split into classes on a component
/// (K36) decides it one pinwheel at a time.
fn squares_less_boxes(full: bool, ends: &[[Type; 3]]) -> Type {
    let boxes: &[[u8; 2]] = match full {
        false => &[[3, 1], [4, 3], [6, 4], [1, 6]],
        true => &[[3, 1], [4, 3], [6, 4], [1, 6], [2, 2]],
    };
    let set = |e: &[Type; 3], m: u8| {
        Type::union_all((0..3).filter(|i| m >> i & 1 == 1).map(|i| e[i].clone()))
    };
    let squares = Type::union_all(ends.iter().map(|e| Type::tuple(vec![set(e, 7); 2])));
    let all = Type::union_all(ends.iter().flat_map(|e| {
        boxes
            .iter()
            .map(|b| Type::tuple(b.iter().map(|&m| set(e, m)).collect()))
    }));
    &squares - &all
}

#[test]
fn a_union_of_disjoint_pinwheels_is_decided() {
    for k in [1, 2, 3, 5] {
        let (full, open) = (
            pinwheels(k, true, End::Plain),
            pinwheels(k, false, End::Plain),
        );
        assert_eq!(full.verdict(), zed_kernel::types::Verdict::Empty, "k = {k}");
        assert_eq!(
            open.verdict(),
            zed_kernel::types::Verdict::Inhabited,
            "k = {k}"
        );
        // The middles are the values of the union outside the full one.
        let middles =
            Type::union_all((0..k).map(|i| Type::tuple(vec![lit_i(10 * i as i64 + 2); 2])));
        assert!((&open - &full).equiv(&middles), "k = {k}");
        assert!(
            middles.subtype(&open) && (&middles & &full).is_empty(),
            "k = {k}"
        );
        assert!(full.subtype(&open) && !open.subtype(&full), "k = {k}");
        // The squares less all the boxes are the same pinwheels, with or without a cofinite
        // end, and are decided the same way.
        for cofinite in [false, true] {
            let ends = plain_ends(k, cofinite);
            let (full_d, open_d) = (
                squares_less_boxes(true, &ends),
                squares_less_boxes(false, &ends),
            );
            assert_eq!(full_d.verdict(), Verdict::Empty, "k = {k}, {cofinite}");
            assert_eq!(open_d.verdict(), Verdict::Inhabited, "k = {k}, {cofinite}");
            assert!((&open_d - &full_d).equiv(&middles), "k = {k}, {cofinite}");
            let unions = (
                Type::union_all(ends.iter().map(|e| pinwheel(true, e.clone()))),
                Type::union_all(ends.iter().map(|e| pinwheel(false, e.clone()))),
            );
            assert!(
                full_d.equiv(&unions.0) && open_d.equiv(&unions.1),
                "k = {k}, {cofinite}"
            );
        }
    }
}

/// The lists of integers whose length is `k` modulo `p`.
fn period(p: usize, k: usize) -> Type {
    use zed_kernel::types::rec::{Def, Expr, Group};
    let defs = (0..p)
        .map(|i| {
            let cons = Expr::Atom(
                "cons".into(),
                vec![Expr::Type(Type::int()), Expr::Ref((i + 1) % p, vec![])],
            );
            let body = match i == k {
                true => Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
                false => cons,
            };
            Def {
                name: format!("P{i}"),
                params: vec![],
                body,
            }
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![]).remove(0)
}

/// Every member of the group of [`period`]: member `i` holds the lists whose length is
/// `k - i` modulo `p`.
fn periods(p: usize, k: usize) -> Vec<Type> {
    use zed_kernel::types::rec::{Def, Expr, Group};
    let defs = (0..p)
        .map(|i| {
            let cons = Expr::Atom(
                "cons".into(),
                vec![Expr::Type(Type::int()), Expr::Ref((i + 1) % p, vec![])],
            );
            let body = match i == k {
                true => Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]),
                false => cons,
            };
            Def {
                name: format!("P{i}"),
                params: vec![],
                body,
            }
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![])
}

#[test]
fn a_cycle_kept_for_each_type_on_it_gives_each_its_own_lengths() {
    // In one search, the meet `P_0 & Q_0` walks both cycles and keeps them for every type on
    // them; the meet `P_i & Q_j` beside it then reads the kept cycles of the types after
    // `P_i` and `Q_j`, whose stops are nearer. A meet is inhabited exactly when some length is
    // `k - i` modulo `p` and `r - j` modulo `q`.
    let meets = |p: usize, k: usize, i: usize, q: usize, r: usize, j: usize| {
        (0..p * q).any(|l| (l + i) % p == k && (l + j) % q == r)
    };
    for p in 2..=5 {
        for q in 2..=5 {
            for (k, r) in (0..p).flat_map(|k| (0..q).map(move |r| (k, r))) {
                let (ps, qs) = (periods(p, k), periods(q, r));
                for (i, j) in (0..p).flat_map(|i| (0..q).map(move |j| (i, j))) {
                    Type::forget_emptiness();
                    let t = Type::tuple(vec![&ps[0] & &qs[0], &ps[i] & &qs[j]]);
                    let want = match meets(p, k, 0, q, r, 0) && meets(p, k, i, q, r, j) {
                        true => Verdict::Inhabited,
                        false => Verdict::Empty,
                    };
                    assert_eq!(t.verdict(), want, "p {p} k {k} i {i}, q {q} r {r} j {j}");
                }
            }
        }
    }
}

mod bench;
