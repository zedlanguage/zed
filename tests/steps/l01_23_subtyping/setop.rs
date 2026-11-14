//! Members of recursive groups under `&` and `\` (plan item GROUP-setop). The group's decider
//! reads `A & B` as a node that needs both operands and `A \ B` as `A`: a set of values that
//! holds the member's, so a member it proves empty is empty, and the search is skipped
//! (`Type::members_searched` counts the members sent to it). A member it shows inhabited
//! through such a node may still be empty (`#a & #b` below), so that answer goes to the search.

use zed_kernel::Value;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::instances::Rng;
use zed_tests::scaling;

fn def(name: &str, body: Expr) -> Def {
    Def {
        name: name.into(),
        params: vec![],
        body,
    }
}

fn cons(head: Type, tail: Expr) -> Expr {
    Expr::Atom("cons".into(), vec![Expr::Type(head), tail])
}

fn nil() -> Expr {
    Expr::Type(Type::atom("nil"))
}

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn diff(a: Expr, b: Expr) -> Expr {
    Expr::Diff(Box::new(a), Box::new(b))
}

/// The verdict on `t`, from no kept answer, and how many members it sent to the search.
fn verdict_and_searched(t: &Type) -> (Verdict, usize) {
    Type::forget_emptiness();
    let before = Type::members_searched();
    let v = t.verdict();
    (v, Type::members_searched() - before)
}

/// `List = nil | cons(int, List)`, `Endless = cons(int, Endless)` and `M = List & Endless`:
/// one operand inhabited, the other empty. The decider proves `M` empty, and nothing is
/// searched.
#[test]
fn a_meet_with_an_empty_operand_is_empty_with_no_search() {
    let g = Group::new(vec![
        def("List", Expr::Union(vec![nil(), cons(Type::int(), r(0))])),
        def("Endless", cons(Type::int(), r(1))),
        def("M", Expr::And(vec![r(0), r(1)])),
    ])
    .unwrap()
    .instance(vec![]);
    assert_eq!(verdict_and_searched(&g[2]), (Verdict::Empty, 0));
    Type::forget_emptiness();
    assert!(g[2].is_empty());
}

/// `D = List \ nil` is read as `List`, which is inhabited, so its answer comes from the search;
/// `E = Endless \ nil`, in a group of its own, is read as `Endless`, which the decider proves
/// empty with no search. The count is of the group, whose verdicts are decided together.
#[test]
fn a_difference_is_read_as_its_left_operand() {
    let d = Group::new(vec![
        def("List", Expr::Union(vec![nil(), cons(Type::int(), r(0))])),
        def("D", diff(r(0), nil())),
    ])
    .unwrap()
    .instance(vec![]);
    let e = Group::new(vec![
        def("Endless", cons(Type::int(), r(0))),
        def("E", diff(r(0), nil())),
    ])
    .unwrap()
    .instance(vec![]);
    assert_eq!(verdict_and_searched(&d[1]), (Verdict::Inhabited, 1));
    assert_eq!(verdict_and_searched(&e[1]), (Verdict::Empty, 0));
}

/// Members the decider would call inhabited through a meet or a difference though they are
/// empty: `A = #a | cons(int, A)` and `B = #b | cons(int, B)` share no value, since each list
/// ends in its own atom; `L \ (nil | cons(int, _))` holds no list. The decider leaves both to
/// the search, which proves them empty. `A`, `B` and `L` are not searched: the group sends two
/// members to the search.
#[test]
fn what_the_decider_shows_inhabited_through_a_meet_is_searched() {
    let any_list = Expr::Union(vec![nil(), cons(Type::int(), Expr::Type(Type::top()))]);
    let g = Group::new(vec![
        def(
            "A",
            Expr::Union(vec![Expr::Type(Type::atom("a")), cons(Type::int(), r(0))]),
        ),
        def(
            "B",
            Expr::Union(vec![Expr::Type(Type::atom("b")), cons(Type::int(), r(1))]),
        ),
        def("M", Expr::And(vec![r(0), r(1)])),
        def("L", Expr::Union(vec![nil(), cons(Type::int(), r(3))])),
        def("N", diff(r(3), any_list)),
    ])
    .unwrap()
    .instance(vec![]);
    for i in [2, 4] {
        assert_eq!(
            verdict_and_searched(&g[i]),
            (Verdict::Empty, 2),
            "member {i}"
        );
    }
    assert_eq!(verdict_and_searched(&g[0]), (Verdict::Inhabited, 2));
}

/// A group of `k` cycles of period 2 holding the lists of even length, with `Endless =
/// cons(int, Endless)` when `endless`, and last `M`, the meet of the first member of each cycle
/// (and `Endless`).
fn meet_of_k(k: usize, endless: bool) -> Type {
    let mut defs = Vec::new();
    let mut starts = Vec::new();
    for c in 0..k {
        let (even, odd) = (2 * c, 2 * c + 1);
        starts.push(even);
        defs.push(def(
            &format!("Even{c}"),
            Expr::Union(vec![nil(), cons(Type::int(), r(odd))]),
        ));
        defs.push(def(&format!("Odd{c}"), cons(Type::int(), r(even))));
    }
    if endless {
        let e = defs.len();
        starts.push(e);
        defs.push(def("Endless", cons(Type::int(), r(e))));
    }
    defs.push(def("M", Expr::And(starts.into_iter().map(r).collect())));
    Group::new(defs).unwrap().instance(vec![]).pop().unwrap()
}

fn lit(i: usize) -> Type {
    Type::lit(&Value::Int(i as i64)).unwrap()
}

/// The lists of integers of odd length holding an even count of each of `0..k`, as the meet of
/// `k + 1` two-state lists in one group: their product has `2^(k+1)` states.
fn parity_meet(k: usize) -> Type {
    let mut defs = Vec::new();
    for j in 0..k {
        let (even, odd) = (2 * j, 2 * j + 1);
        let other = || &Type::int() - &lit(j);
        defs.push(def(
            &format!("Even{j}"),
            Expr::Union(vec![nil(), cons(lit(j), r(odd)), cons(other(), r(even))]),
        ));
        defs.push(def(
            &format!("Odd{j}"),
            Expr::Union(vec![cons(lit(j), r(even)), cons(other(), r(odd))]),
        ));
    }
    let (odd_len, even_len) = (2 * k, 2 * k + 1);
    defs.push(def("OddLen", cons(Type::int(), r(even_len))));
    defs.push(def(
        "EvenLen",
        Expr::Union(vec![nil(), cons(Type::int(), r(odd_len))]),
    ));
    let mut parts: Vec<Expr> = (0..k).map(|j| r(2 * j)).collect();
    parts.push(r(odd_len));
    defs.push(def("M", Expr::And(parts)));
    Group::new(defs).unwrap().instance(vec![]).pop().unwrap()
}

/// The meet of `k` parity lists and the odd-length lists, written in form `form`: bit 0
/// renames each definition, bit 1 lists the definitions in the opposite order, bit 2 writes
/// the meet's operands in the opposite order; references are remapped as the definitions are
/// built. [`parity_variant`] also takes a name prefix and reverses the arms of each union.
fn parity_form(k: usize, form: usize) -> Type {
    parity_variant(k, form, None, false)
}

fn parity_variant(k: usize, form: usize, prefix: Option<&str>, reverse_unions: bool) -> Type {
    let at = |i: usize| {
        if form & 2 != 0 && i < 2 * k + 2 {
            2 * k + 1 - i
        } else {
            i
        }
    };
    let refer = |i: usize| r(at(i));
    let name = |old: String| {
        if let Some(prefix) = prefix {
            format!("{prefix}{old}")
        } else if form & 1 != 0 {
            format!("Renamed_{old}")
        } else {
            old
        }
    };
    let mut defs = Vec::new();
    for j in 0..k {
        let (even, odd) = (2 * j, 2 * j + 1);
        let other = || &Type::int() - &lit(j);
        defs.push((
            even,
            def(
                &name(format!("Even{j}")),
                Expr::Union(vec![
                    nil(),
                    cons(lit(j), refer(odd)),
                    cons(other(), refer(even)),
                ]),
            ),
        ));
        defs.push((
            odd,
            def(
                &name(format!("Odd{j}")),
                Expr::Union(vec![cons(lit(j), refer(even)), cons(other(), refer(odd))]),
            ),
        ));
    }
    let (odd_len, even_len) = (2 * k, 2 * k + 1);
    defs.push((
        odd_len,
        def(&name("OddLen".into()), cons(Type::int(), refer(even_len))),
    ));
    defs.push((
        even_len,
        def(
            &name("EvenLen".into()),
            Expr::Union(vec![nil(), cons(Type::int(), refer(odd_len))]),
        ),
    ));
    let mut parts: Vec<Expr> = (0..k).map(|j| refer(2 * j)).collect();
    parts.push(refer(odd_len));
    if form & 4 != 0 {
        parts.reverse();
    }
    defs.push((2 * k + 2, def(&name("M".into()), Expr::And(parts))));
    defs.sort_by_key(|(i, _)| at(*i));
    let types = Group::new(
        defs.into_iter()
            .map(|(_, mut d)| {
                if reverse_unions && let Expr::Union(kids) = &mut d.body {
                    kids.reverse();
                }
                d
            })
            .collect(),
    )
    .unwrap()
    .instance(vec![]);
    types[at(2 * k + 2)].clone()
}

fn canonical_blame_chain(m: usize) -> Vec<Type> {
    let mut defs = Vec::with_capacity(m + 2);
    let end = m + 1;
    let split_arm = || {
        let a = Expr::exact(
            Expr::Type(Type::atom("x") | Type::atom("y")),
            Expr::Type(Type::int()),
        );
        let b1 = Expr::exact(Expr::Type(Type::atom("x")), Expr::Type(Type::int()));
        let b2 = Expr::exact(Expr::Type(Type::atom("y")), Expr::Type(Type::int()));
        diff(a, Expr::Union(vec![b1, b2]))
    };
    for i in 0..m {
        let clean = Expr::Tuple(vec![Expr::Type(Type::atom(&format!("k{i}"))), r(i + 1)]);
        defs.push(def(&format!("C{i}"), Expr::Union(vec![split_arm(), clean])));
    }
    defs.push(def(
        "Tail",
        Expr::Tuple(vec![Expr::Type(Type::atom("tail")), r(end)]),
    ));
    defs.push(def(
        " sink",
        diff(
            Expr::exact(Expr::Type(Type::int()), r(end)),
            Expr::exact(Expr::Type(Type::int()), Expr::Type(Type::top())),
        ),
    ));
    defs[end].name = "Sink".into();
    Group::new(defs).unwrap().instance(vec![])
}

#[test]
fn the_parity_singleton_is_found_across_names_and_operand_orders() {
    for k in [2usize, 3, 4] {
        for form in 0..8 {
            let t = parity_form(k, form);
            let yes = Value::atom_with("cons", vec![Value::Int(k as i64), Value::atom("nil")]);
            assert!(t.contains(&yes));
            assert_eq!(
                verdict_and_searched(&t).0,
                Verdict::Inhabited,
                "k={k} form={form}"
            );
        }
    }
    for salt in 0..24 {
        for reverse in [false, true] {
            let t = parity_variant(3, 0, Some(&format!("S{salt}_")), reverse);
            assert_eq!(
                verdict_and_searched(&t).0,
                Verdict::Inhabited,
                "salt={salt} reverse={reverse}"
            );
        }
    }
}

/// A finite bound is a further constraint on the column used by the singleton witness.
#[test]
fn bounded_parity_singletons_obey_further_integer_constraints() {
    for k in [2usize, 3, 4, 8, 32] {
        for hi in [k, k + 1, 2 * k] {
            let t = bounded_parity(k, hi, None);
            assert!(t.contains(&Value::atom_with(
                "cons",
                vec![Value::Int(k as i64), Value::atom("nil")]
            )));
            assert_eq!(verdict_and_searched(&t).0, Verdict::Inhabited);
        }
        let t = bounded_parity(k, 2 * k, Some(k));
        assert!(t.contains(&Value::atom_with(
            "cons",
            vec![Value::Int((k + 1) as i64), Value::atom("nil")]
        )));
        assert_eq!(verdict_and_searched(&t).0, Verdict::Inhabited);
        // Removing k from 0..=k leaves only the k monitored symbols. Each
        // occurs evenly often, so an odd-length list cannot inhabit the meet.
        let no = bounded_parity(k, k, Some(k));
        assert!(!no.contains(&Value::atom_with(
            "cons",
            vec![Value::Int(k as i64), Value::atom("nil")]
        )));
        assert_ne!(verdict_and_searched(&no).0, Verdict::Inhabited);
    }
}

/// Random meets of two-state lists, each swapping its two states on a set of integers and
/// keeping them on the others, with the stop atom in a random set of states, and the items
/// bounded to `0..a` or not: a meet answered `Empty` holds no list of length at most 4 over
/// `0..a` and one integer outside it, by `Type::contains`. Some meets are proved empty by the
/// reading as a linear system over GF(2), and some fall outside it; the count of each is
/// printed with `--nocapture`.
///
/// Until TEST-bench-move-l0123 (author P169) this ran 400 meets from one fixed seed of its own
/// generator, 1.1 to 1.4 s alone under load; it now runs 100 from a fresh seed each run,
/// 0.23 to 0.70 s alone under the same load, the time varying with the meets drawn. Every kind of meet is still drawn: each draw picks among
/// 1 to 4 integers, 1 to 8 lists, bounded or not, swaps by pairs or by any subset, and stop
/// sets of none, one or both states. At 400 meets 309 were answered `Empty` with no short
/// list (77 percent), so at 100 about 77 are, with a standard deviation of about 4.2: the one
/// count checked, at least one such meet, holds by far more than three of them.
#[test]
fn random_parity_meets_answered_empty_hold_no_short_list() {
    let (mut g, seed) = Rng::fresh("random parity meets");
    let set = |xs: &[usize]| (xs.iter().map(|&x| lit(x))).fold(Type::empty(), |u, x| &u | &x);
    let mut tally = std::collections::BTreeMap::new();
    for _ in 0..100 {
        let a = 1 + g.below(4);
        let k = 1 + g.below(8);
        let bounded = g.below(2) == 0;
        // In half the meets each integer swaps at most two lists, the class read over GF(2).
        let mut swaps: Vec<Vec<usize>> = vec![vec![]; k];
        let pairs = g.below(2) == 0;
        for x in 0..a {
            match pairs {
                true => {
                    for _ in 0..g.below(3) {
                        let i = g.below(k);
                        if swaps[i].last() != Some(&x) {
                            swaps[i].push(x);
                        }
                    }
                }
                false => (0..k)
                    .filter(|_| g.below(2) == 0)
                    .for_each(|i| swaps[i].push(x)),
            }
        }
        let mut defs = Vec::new();
        for (i, swaps) in swaps.iter().enumerate() {
            let stops = g.below(4);
            for (state, other_state) in [(2 * i, 2 * i + 1), (2 * i + 1, 2 * i)] {
                let mut arms = Vec::new();
                if (stops >> (state % 2)) & 1 == 1 {
                    arms.push(nil());
                }
                if !swaps.is_empty() {
                    arms.push(cons(set(swaps), r(other_state)));
                }
                arms.push(cons(&Type::int() - &set(swaps), r(state)));
                defs.push(def(&format!("S{state}"), Expr::Union(arms)));
            }
        }
        let small = 2 * k;
        let all: Vec<usize> = (0..a).collect();
        defs.push(def(
            "Small",
            Expr::Union(vec![nil(), cons(set(&all), r(small))]),
        ));
        let mut parts: Vec<Expr> = (0..k).map(|i| r(2 * i)).collect();
        if bounded {
            parts.push(r(small));
        }
        defs.push(def("M", Expr::And(parts)));
        let t = Group::new(defs).unwrap().instance(vec![]).pop().unwrap();
        let letters: Vec<i64> = (0..a as i64).chain([a as i64 + 3]).collect();
        let mut words: Vec<Vec<i64>> = vec![vec![]];
        let mut found = None;
        for _ in 0..4 {
            words = (words.iter())
                .flat_map(|w| letters.iter().map(move |&x| [w.clone(), vec![x]].concat()))
                .collect();
            for w in &words {
                let list = (w.iter().rev()).fold(Value::atom("nil"), |tail, &x| {
                    Value::atom_with("cons", vec![Value::Int(x), tail])
                });
                if t.contains(&list) {
                    found = Some(w.clone());
                }
            }
        }
        let v = verdict_and_searched(&t).0;
        if v == Verdict::Empty {
            assert_eq!(
                found, None,
                "a list of a meet answered empty (ZED_TEST_SEED={seed})"
            );
        }
        *tally
            .entry((format!("{v:?}"), found.is_some()))
            .or_insert(0) += 1;
    }
    eprintln!("random parity meets, by verdict and whether a short list was found: {tally:?}");
    assert!(
        tally.contains_key(&("Empty".to_owned(), false)),
        "no meet answered empty (ZED_TEST_SEED={seed}): {tally:?}"
    );
}

fn bounded_parity(k: usize, hi: usize, exclude: Option<usize>) -> Type {
    bounded_parity_variant(k, hi, exclude, None)
}

fn bounded_parity_variant(
    k: usize,
    hi: usize,
    exclude: Option<usize>,
    repeated: Option<usize>,
) -> Type {
    Group::new(bounded_parity_definitions(k, hi, exclude, repeated))
        .unwrap()
        .instance(vec![])
        .pop()
        .unwrap()
}

fn bounded_parity_definitions(
    k: usize,
    hi: usize,
    exclude: Option<usize>,
    repeated: Option<usize>,
) -> Vec<Def> {
    let mut defs = Vec::new();
    for j in 0..k {
        let (even, odd) = (2 * j, 2 * j + 1);
        let other = || &Type::int() - &lit(j);
        defs.push(def(
            &format!("Even{j}"),
            Expr::Union(vec![nil(), cons(lit(j), r(odd)), cons(other(), r(even))]),
        ));
        defs.push(def(
            &format!("Odd{j}"),
            Expr::Union(vec![cons(lit(j), r(even)), cons(other(), r(odd))]),
        ));
    }
    let (odd_len, even_len, small) = (2 * k, 2 * k + 1, 2 * k + 2);
    defs.push(def("OddLen", cons(Type::int(), r(even_len))));
    defs.push(def(
        "EvenLen",
        Expr::Union(vec![nil(), cons(Type::int(), r(odd_len))]),
    ));
    let mut elem = (1..=hi).fold(lit(0), |u, i| &u | &lit(i));
    if let Some(i) = exclude {
        elem = &elem - &lit(i);
    }
    let name = repeated.map_or("Small".to_owned(), |salt| format!("Small{salt}"));
    defs.push(def(
        &name,
        Expr::Union(vec![nil(), cons(elem.clone(), r(small))]),
    ));
    let mut parts: Vec<Expr> = (0..k).map(|j| r(2 * j)).collect();
    parts.push(r(odd_len));
    parts.push(r(small));
    if repeated.is_some() {
        // The first arm already holds every nonempty Small list. Its scalar
        // field also occurs in the mandatory Small row, with a different tail.
        parts.push(Expr::Union(vec![
            cons(elem, Expr::Type(Type::top())),
            cons(lit(0), Expr::Type(Type::bool())),
        ]));
    }
    defs.push(def("M", Expr::And(parts)));
    defs
}

#[test]
fn diagonal_parity_proofs_require_every_allowed_symbol_to_be_counted() {
    for k in [2, 3, 4, 8, 32] {
        for hi in [0, k - 1, k, k + 1] {
            let t = bounded_parity(k, hi, None);
            Type::forget_emptiness();
            assert_eq!(
                t.verdict(),
                if hi < k {
                    Verdict::Empty
                } else {
                    Verdict::Inhabited
                }
            );
        }
    }
}

/// Repeating an alphabet reference or adding an equal alphabet definition
/// preserves the same diagonal proof, in both meet operand orders.
#[test]
fn diagonal_empty_proofs_reuse_equal_alphabet_classes() {
    for k in [2usize, 8, 32] {
        for hi in [k - 1, k] {
            for reverse in [false, true] {
                let mut defs = bounded_parity_definitions(k, hi, None, None);
                let mut root = defs.pop().unwrap();
                let second = defs.len();
                let elements = Type::union_all((0..=hi).rev().map(lit));
                defs.push(def(
                    "AnotherAlphabet",
                    Expr::Union(vec![nil(), cons(elements, r(second))]),
                ));
                let Expr::And(parts) = &mut root.body else {
                    unreachable!()
                };
                parts.extend([r(2 * k + 2), r(second)]);
                if reverse {
                    parts.reverse();
                }
                defs.push(root);
                let t = Group::new(defs).unwrap().instance(vec![]).pop().unwrap();
                Type::forget_emptiness();
                assert_eq!(
                    t.verdict(),
                    if hi < k {
                        Verdict::Empty
                    } else {
                        Verdict::Inhabited
                    }
                );
                Type::forget_emptiness();
                assert_eq!(t.is_empty(), hi < k);
            }
        }
    }
}

/// All small diagonal systems, checked against their Boolean equations rather
/// than against the search. A positive system has an explicit checked word.
#[test]
fn diagonal_parity_agrees_with_boolean_equations() {
    let mut checked = 0;
    for k in 1..=3 {
        for alphabet in 1usize..1 << (k + 1) {
            for wanted in 0usize..1 << k {
                for odd in [false, true] {
                    let mut defs = bounded_parity_definitions(k, k, None, None);
                    let elements =
                        Type::union_all((0..=k).filter(|j| alphabet >> j & 1 != 0).map(lit));
                    defs[2 * k + 2].body = Expr::Union(vec![nil(), cons(elements, r(2 * k + 2))]);
                    let mut parts: Vec<Expr> =
                        (0..k).map(|j| r(2 * j + (wanted >> j & 1))).collect();
                    parts.push(r(2 * k + usize::from(!odd)));
                    parts.push(r(2 * k + 2));
                    defs.last_mut().unwrap().body = Expr::And(parts);
                    let t = Group::new(defs).unwrap().instance(vec![]).pop().unwrap();
                    let outside = wanted & !alphabet != 0;
                    let extra = alphabet >> k & 1 != 0;
                    let parity = wanted.count_ones() % 2 != 0;
                    let exists = !outside && (extra || parity == odd);
                    Type::forget_emptiness();
                    let v = t.verdict();
                    if exists {
                        assert_ne!(
                            v,
                            Verdict::Empty,
                            "k={k} alphabet={alphabet} wanted={wanted} odd={odd}"
                        );
                        let mut word = Value::atom("nil");
                        if parity != odd {
                            word = Value::atom_with("cons", vec![Value::Int(k as i64), word]);
                        }
                        for j in 0..k {
                            if wanted >> j & 1 != 0 {
                                word = Value::atom_with("cons", vec![Value::Int(j as i64), word]);
                            }
                        }
                        assert!(t.contains(&word));
                    } else {
                        assert_eq!(
                            v,
                            Verdict::Empty,
                            "k={k} alphabet={alphabet} wanted={wanted} odd={odd}"
                        );
                    }
                    checked += 1;
                }
            }
        }
    }
    eprintln!("DIAGONAL Boolean systems checked {checked}");
}

#[test]
fn diagonal_empty_proofs_ignore_names_and_written_orders() {
    for k in [2, 3, 8] {
        for hi in [k - 1, k] {
            for form in 0..16 {
                let mut defs = bounded_parity_definitions(k, hi, None, None);
                let n = defs.len();
                for d in &mut defs {
                    if form & 1 != 0 {
                        d.name = format!("Renamed_{}", d.name);
                    }
                    let mut todo = vec![&mut d.body];
                    while let Some(e) = todo.pop() {
                        match e {
                            Expr::Ref(i, _) if form & 2 != 0 => *i = n - 1 - *i,
                            Expr::Union(xs) => {
                                if form & 8 != 0 {
                                    xs.reverse();
                                }
                                todo.extend(xs);
                            }
                            Expr::And(xs) => {
                                if form & 4 != 0 {
                                    xs.reverse();
                                }
                                todo.extend(xs);
                            }
                            Expr::Atom(_, xs) => todo.extend(xs),
                            _ => {}
                        }
                    }
                }
                if form & 2 != 0 {
                    defs.reverse();
                }
                let g = Group::new(defs).unwrap().instance(vec![]);
                let t = &g[if form & 2 != 0 { 0 } else { n - 1 }];
                Type::forget_emptiness();
                assert_eq!(
                    t.verdict(),
                    if hi < k {
                        Verdict::Empty
                    } else {
                        Verdict::Inhabited
                    },
                    "k={k} hi={hi} form={form}"
                );
            }
        }
    }
}

#[test]
fn a_mandatory_integer_field_is_classified_before_its_alternative_rows() {
    for k in [2usize, 3, 4, 8, 32] {
        for salt in 0..24 {
            let t = bounded_parity_variant(k, k, None, Some(salt));
            assert_eq!(
                verdict_and_searched(&t).0,
                Verdict::Inhabited,
                "k={k} salt={salt}"
            );
        }
    }
}

fn repeated_integer_field_scale(n: usize) {
    let inputs = scaling::inputs(n, |k| bounded_parity_variant(k, k, None, Some(4)));
    scaling::check_order("bounded parity with a repeated scalar field", n, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
    });
}

/// Two literal sets and two rows are shared by all columns. Written DAG size
/// is linear in k; a checked witness has k integer fields, not k squared.
fn shared_integer_columns(k: usize, distinct: bool) -> Type {
    let evens = (0..k).fold(Type::empty(), |t, j| &t | &lit(2 * j));
    let odds = (0..k).fold(Type::empty(), |t, j| &t | &lit(2 * j + 1));
    let a = &Type::int() - &evens;
    let b = &Type::int() - &odds;
    let right = if distinct {
        (0..k).map(|j| &b - &lit(4 * k + j)).collect()
    } else {
        vec![b; k]
    };
    &Type::tuple(vec![a; k]) & &Type::tuple(right)
}

fn shared_integer_columns_check(n: usize, distinct: bool) {
    let inputs = scaling::inputs(n, |k| shared_integer_columns(k, distinct));
    scaling::check_order("shared scalar boundaries across tuple columns", n, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
    });
}

fn cofinite_rows(k: usize) -> Type {
    let excluded = Type::union_all((0..k).map(lit));
    let common = &Type::int() - &excluded;
    Type::meet_all((0..k).map(|j| Type::tuple(vec![&common - &lit(4 * k + j)])))
}

fn cofinite_rows_scale(n: usize) {
    let inputs = scaling::inputs(n, cofinite_rows);
    scaling::check_order("shared integer boundaries across rows", n, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].verdict(), Verdict::Inhabited);
    });
}

/// `A & B`, where `A` holds the lists of integers linked by `more` with an even count of 0 and
/// `B` those with an odd count, both ending in `nil`; with `cons_too`, every state of both also
/// holds `cons(int, nil)`, a second link atom that continues a list in any state.
fn opposite_parities(cons_too: bool) -> Type {
    let more = |head: Type, tail: Expr| Expr::Atom("more".into(), vec![Expr::Type(head), tail]);
    let state = |accepts: bool, zero: usize, same: usize| {
        let mut arms = Vec::new();
        if accepts {
            arms.push(nil());
        }
        if cons_too {
            arms.push(cons(Type::int(), nil()));
        }
        arms.extend([more(lit(0), r(zero)), more(&Type::int() - &lit(0), r(same))]);
        def(&format!("S{same}"), Expr::Union(arms))
    };
    // 0: A even (accepts), 1: A odd, 2: B even (accepts), 3: B odd.
    let defs = vec![
        state(true, 1, 0),
        state(false, 0, 1),
        state(true, 3, 2),
        state(false, 2, 3),
        def("M", Expr::And(vec![r(0), r(3)])),
    ];
    Group::new(defs).unwrap().instance(vec![]).pop().unwrap()
}

/// A meet of parity lists is proved empty by the count of each integer only when its link atom
/// is the one way a list goes on: with `cons(int, nil)` in every state, `cons(1, nil)` is in both
/// operands, so the meet is inhabited. Without it the counts of 0 contradict, and the meet is
/// empty. Before REGRESS-l01_26-overload the parity proof read only the rows of the last link
/// atom by name, `more`, and answered `Empty` here.
#[test]
fn a_parity_meet_with_a_second_link_atom_is_inhabited() {
    Type::forget_emptiness();
    assert_eq!(opposite_parities(false).verdict(), Verdict::Empty);
    let t = opposite_parities(true);
    let witness = Value::atom_with("cons", vec![Value::Int(1), Value::atom("nil")]);
    assert!(t.contains(&witness));
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Inhabited);
    assert!(!t.is_empty());
}

/// Small instance of `bench::meets_of_k_members_scale`: the meet of a few even-length lists is
/// settled with no search when an endless list is among them, and searched once otherwise.
#[test]
fn meets_of_a_few_members_are_decided() {
    for k in [1, 2, 3] {
        assert_eq!(
            verdict_and_searched(&meet_of_k(k, true)),
            (Verdict::Empty, 0),
            "k = {k}"
        );
        assert_eq!(
            verdict_and_searched(&meet_of_k(k, false)),
            (Verdict::Inhabited, 1),
            "k = {k}"
        );
    }
}

/// Small instance of `bench::the_product_of_k_parity_lists_has_a_checked_singleton`: the
/// product of two parity lists is found inhabited with one search (the check at `k = 2` was in
/// the benchmark until TEST-bench-move-l0123, author P169), and the product of a few is not
/// empty.
#[test]
fn the_product_of_a_few_parity_lists_has_a_singleton() {
    assert_eq!(
        verdict_and_searched(&parity_meet(2)),
        (Verdict::Inhabited, 1)
    );
    for k in [1, 2, 3] {
        Type::forget_emptiness();
        assert!(!parity_meet(k).is_empty(), "k = {k}");
    }
}

/// Small instance of `bench::canonical_blame_settlement_scales`: the first member of a short
/// chain of members with a split arm is refused for want of a witness.
#[test]
fn a_short_chain_with_split_arms_is_refused_for_want_of_a_witness() {
    for m in [1, 2, 5] {
        let types = canonical_blame_chain(m);
        Type::forget_emptiness();
        assert_eq!(
            types[0].verdict(),
            Verdict::Refused(Refusal::NoWitness),
            "m = {m}"
        );
    }
}

/// Small instance of `bench::bounded_empty_parity_decided_on_another_thread_costs_the_same_here`:
/// a bounded parity decided empty on another thread, and kept alive, is decided empty here
/// too. The benchmark measures that the work here is not less; this checks the answer.
#[test]
fn bounded_empty_parity_decided_on_another_thread_is_empty_here() {
    let k = 3;
    let _decided = std::thread::spawn(move || {
        let t = bounded_parity(k, k - 1, None);
        assert_eq!(t.verdict(), Verdict::Empty);
        t
    })
    .join()
    .unwrap();
    Type::forget_emptiness();
    assert_eq!(bounded_parity(k, k - 1, None).verdict(), Verdict::Empty);
}

/// Small instance of `bench::bounded_empty_parity_is_decided_in_the_size_of_the_constraints`: a
/// bounded parity whose bound is below its count is empty by its verdict and by `is_empty`,
/// asked in the benchmark's order and by `is_empty` alone.
#[test]
fn small_bounded_empty_parities_are_empty() {
    for k in [2, 3, 5] {
        let t = bounded_parity(k, k - 1, None);
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Empty, "k = {k}");
        assert!(t.is_empty(), "k = {k}");
        Type::forget_emptiness();
        assert!(bounded_parity(k, k - 1, None).is_empty(), "k = {k}");
    }
}

/// Small instance of `bench::shared_integer_columns_scale_with_their_written_dag` and
/// `bench::distinct_integer_columns_reuse_a_checked_point`: a few columns sharing their
/// boundaries, alike or distinct, are inhabited; and a further finite field keeps the point
/// the first search checked. That last check was in the benchmark until TEST-bench-move-l0123
/// (author P169) moved it here.
#[test]
fn a_few_shared_integer_columns_are_inhabited() {
    for k in [1, 2, 5] {
        for distinct in [false, true] {
            Type::forget_emptiness();
            assert_eq!(
                shared_integer_columns(k, distinct).verdict(),
                Verdict::Inhabited,
                "k = {k}, distinct = {distinct}"
            );
        }
    }
    // Every column contributes its exclusions. A further finite field leaves
    // this class and must retain the original search's checked point.
    let t = &Type::tuple(vec![&Type::int() - &lit(0), &Type::int() - &lit(1)])
        & &Type::tuple(vec![&Type::int() - &lit(2), &Type::int() - &lit(3)]);
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Inhabited);
    let v = Value::tuple(vec![Value::Int(1), Value::Int(0)]);
    assert!(t.contains(&v));
    let constrained = &t & &Type::tuple(vec![Type::int(), lit(0)]);
    Type::forget_emptiness();
    assert_eq!(constrained.verdict(), Verdict::Inhabited);
    assert!(constrained.contains(&v));
}

/// Small instance of `bench::shared_cofinite_boundaries_are_not_enumerated_per_row`: the meet
/// of a few one-tuples of integers outside shared and own exclusions is inhabited.
#[test]
fn a_few_shared_cofinite_boundaries_are_inhabited() {
    for k in [1, 2, 5] {
        Type::forget_emptiness();
        assert_eq!(cofinite_rows(k).verdict(), Verdict::Inhabited, "k = {k}");
    }
}

/// The one-tuples of integers other than `10^(10^k)` and other than 0, measured by
/// `bench::cofinite_integer_points_keep_large_powers_symbolic`.
fn beside_a_large_power(k: usize) -> Type {
    let text = format!("1e1{}", "0".repeat(k));
    let huge = Value::integer(zed_kernel::Rat::decimal(&text).unwrap().unwrap());
    Type::meet_all([
        Type::tuple(vec![&Type::int() - &Type::lit(&huge).unwrap()]),
        Type::tuple(vec![&Type::int() - &lit(0)]),
    ])
}

/// Small instance of `bench::cofinite_integer_points_keep_large_powers_symbolic`: one-tuples of
/// integers other than `10^10`, `10^100` or `10^1000` and other than 0 are inhabited, and hold
/// `(1,)`. The `contains` check was in the benchmark, after its runs, until
/// TEST-bench-move-l0123 (author P169) moved it here.
#[test]
fn cofinite_integer_points_beside_a_few_large_powers() {
    for k in [1, 2, 3] {
        let t = beside_a_large_power(k);
        Type::forget_emptiness();
        assert_eq!(t.verdict(), Verdict::Inhabited, "k = {k}");
        assert!(t.contains(&Value::tuple(vec![Value::Int(1)])), "k = {k}");
    }
}

mod bench;
