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

/// `D = List \ nil` is read as `List`, which is inhabited; the exact decision of flat differences
/// (`exact_flat_diff_decide`) settles it and the shared Horn search builds its value, so it is not
/// sent to the search (it was, as one member, before GROUP-order-cpoly-merge);
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
    assert_eq!(verdict_and_searched(&d[1]), (Verdict::Inhabited, 0));
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

/// A group built before timing, and the index of the member a scaling check decides. Each run
/// makes its own instance ([`Fresh::member`]): an instance keeps its members' unfoldings and
/// its group's judgment while it lives (`Env::members`, `Env::judged`), so on one instance kept
/// in the inputs every run after the first did about half the work of the first (parity
/// verdicts at 8n: 28.4 G instructions on the first run, 13.3 G after), and the check, which
/// then compared the first run at 8n with the second at n, found the ratio over and ran 8n again on
/// every check: about 18 times the time at n where 10 passes (FAIL-setop-parity-bench-time).
/// A fresh instance on each run's thread (instances are kept per thread) does the whole work
/// each time, so the runs compared are alike and the first runs are those the check holds.
///
/// What a run on a fresh instance shares with earlier runs (PROOF-bench-fresh-instance). The
/// group path reaches zed-kernel and, of the workspace, zed-graph, zed-collections and
/// zed-numtheory; their `static`, `thread_local!`, `OnceLock` and `LazyLock` items fall in four
/// kinds (searched 2026-11-22):
///
/// 1. The group itself, built before the timing: its definitions, its trees, whose leaves are
///    the written types (`int`, the literals, `int - j`, the atoms), and two `OnceLock`s. Its
///    canonical form (`Checked::canon`) is built by [`Fresh::new`], so no run builds it. Its
///    order of definitions by name (`Checked::by_name`) is filled only when two groups of one
///    canonical form are ordered (`Checked::names_order`), and a run reads one group, so no run
///    fills it. The leaf types are shared, and a lazily filled part of one (a printed text, a
///    diagram's complement or index) filled by one run is read by the next; each such part is of
///    one leaf, of a size that does not grow with `k`, so at most O(k) work a run is saved by
///    them, inside work that grows with `k` (8.2 to 8.3 times from 4096 to 32768).
/// 2. Tables the process keeps for all threads: `GROUPS`, by the definitions, which only
///    `Group::new` reads, before the timing; `INSTANCES`, by the thread first, so a run's new
///    thread finds no instance an earlier run made, and its own table leaves when its last
///    instance is dropped, at the run's end; the outer map holds an entry for each thread with a
///    live instance, a number that does not grow with `k`. The id counters (`IdSource`: groups,
///    instances, threads, units, nodes) give other numbers in a later run, and their atomic
///    increments cost the same.
/// 3. Values fixed for the process on first use: the digest seed (`digest::SEED`, `TEXT`) and
///    the treap priorities (`Priorities` statics). Building the inputs reads them first.
/// 4. Everything else is `thread_local!`: the emptiness memos (`empty::MEMO`, `VERDICTS` and the
///    rest), the diagram tables (`TUPLES`, `MORPHISMS`), the unit of `rec::unfold` and the
///    printer's tables. Each run is on a new thread (`scaling::alone`), so they start empty,
///    and `Type::forget_emptiness` empties this thread's emptiness memos besides.
///
/// Proof that the runs compared are comparable: on a count of instructions each size runs once
/// (author A160), the run at 8n in a new process of the test (TEST-scaling-cold-shared-memo), so
/// each run measured is the first on its own `Fresh`, built the same way, and starts with kinds 1
/// and 3 in the same state at its own size, kind 4 empty and kind 2 differing only in the counters'
/// values and the outer map's size, neither of which grows with `k`. So nothing a run finds
/// filled was filled by a run at the other size, and the work measured is the unfolding, the
/// judging and the search on the written definitions. A meter of processor time takes the least
/// of several runs of each size; for it,
/// `bench::a_second_run_on_a_fresh_instance_does_the_work_of_the_first` checks that a second run
/// at `n` does the counted work of the first, within 1%, so that what
/// a first run leaves in kinds 1 and 2 does not lower the least.
struct Fresh {
    group: Group,
    member: usize,
}

impl Fresh {
    /// Makes one instance and drops it, so that the group's canonical form, built at its first
    /// instance and kept by the group, is built here, before timing, as it was when the inputs
    /// were instances.
    fn new(group: Group, member: usize) -> Fresh {
        drop(group.instance(vec![]));
        Fresh { group, member }
    }

    /// The member, in an instance made on this thread.
    fn member(&self) -> Type {
        self.group.instance(vec![]).swap_remove(self.member)
    }
}

/// The lists of integers of odd length holding an even count of each of `0..k`, as the meet of
/// `k + 1` two-state lists in one group: their product has `2^(k+1)` states.
fn parity_meet(k: usize) -> Type {
    parity_meet_group(k).instance(vec![]).pop().unwrap()
}

/// The group of [`parity_meet`], whose last member is the meet.
fn parity_meet_group(k: usize) -> Group {
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
    Group::new(defs).unwrap()
}

/// The meet of `k` parity lists and the odd-length lists, written in form `form`: bit 0
/// renames each definition, bit 1 lists the definitions in the opposite order, bit 2 writes
/// the meet's operands in the opposite order; references are remapped as the definitions are
/// built. [`parity_variant`] also takes a name prefix and reverses the arms of each union.
fn parity_form(k: usize, form: usize) -> Type {
    parity_variant(k, form, None, false)
}

fn parity_variant(k: usize, form: usize, prefix: Option<&str>, reverse_unions: bool) -> Type {
    let (group, meet) = parity_variant_group(k, form, prefix, reverse_unions);
    group.instance(vec![]).swap_remove(meet)
}

/// The group of [`parity_variant`] and the index of its meet.
fn parity_variant_group(
    k: usize,
    form: usize,
    prefix: Option<&str>,
    reverse_unions: bool,
) -> (Group, usize) {
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
    let group = Group::new(
        defs.into_iter()
            .map(|(_, mut d)| {
                if reverse_unions && let Expr::Union(kids) = &mut d.body {
                    kids.reverse();
                }
                d
            })
            .collect(),
    )
    .unwrap();
    (group, at(2 * k + 2))
}

/// A chain of `m` members, each a union of an arm the search refuses and a tagged tuple of the
/// next member, ending in an empty member: each member is inhabited by the arm alone, and the
/// search shows no value of it, so the whole group is refused with
/// [`Refusal::NoWitness`]. The arm is a pair of a list whose length is 5 modulo 6 and an
/// integer, less the pairs of a list of length 3 modulo 4 or 0 modulo 3: the pairs of a list of
/// length 1 modulo 4 are left, but the walk of a list through the union of the two list types
/// would follow both rests, so no value is shown (`witnesses.rs`,
/// `a_meet_of_cycles_is_shown_by_its_length`; the tradeoff in `Search::list_member`).
///
/// Until 2026-11-23 the arm was `{x | y: int} - ({x: int} | {y: int})`, also refused for want
/// of a witness. REP-refusals-rest point (1) (b22-ref3) decides that arm: the two sides are
/// apart, since a closure of the first has both keys and one of the second has one, so the
/// difference is the first type and has a closure. With it the chain is inhabited
/// ([`morphism_split_chain`]) and no longer measures the settlement of a refused group.
fn canonical_blame_chain(m: usize) -> Vec<Type> {
    use super::witnesses::period;
    let pair = Type::tuple(vec![&period(2, 1) & &period(3, 2), Type::int()]);
    let held = &period(4, 3) | &period(3, 0);
    let arm = &pair - &Type::tuple(vec![held, Type::int()]);
    blame_chain(m, || Expr::Type(arm.clone()))
}

/// The chain of [`canonical_blame_chain`] with the arm it had until 2026-11-23,
/// `{x | y: int} - ({x: int} | {y: int})`, which has a closure.
fn morphism_split_chain(m: usize) -> Vec<Type> {
    blame_chain(m, || {
        let a = Expr::exact(
            Expr::Type(Type::atom("x") | Type::atom("y")),
            Expr::Type(Type::int()),
        );
        let b1 = Expr::exact(Expr::Type(Type::atom("x")), Expr::Type(Type::int()));
        let b2 = Expr::exact(Expr::Type(Type::atom("y")), Expr::Type(Type::int()));
        diff(a, Expr::Union(vec![b1, b2]))
    })
}

/// `m` members `C_i = arm | (k_i, C_{i+1})`, then `Tail = (tail, Sink)` with `Sink` the empty
/// difference `{int: Tail} - {int: top}`.
fn blame_chain(m: usize, split_arm: impl Fn() -> Expr) -> Vec<Type> {
    let mut defs = Vec::with_capacity(m + 2);
    let end = m + 1;
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
/// 0.23 to 0.70 s alone under the same load, the time varying with the meets drawn. Every kind of
/// meet is still drawn: each draw picks among 1 to 4 integers, 1 to 8 lists, bounded or not, swaps
/// by pairs or by any subset, and stop sets of none, one or both states. At 400 meets 309 were
/// answered `Empty` with no short list (77 percent), so at 100 about 77 are, with a standard
/// deviation of about 4.2. A meet built to be answered `Empty` is checked on every run, so no draw
/// need hold one.
#[test]
fn random_parity_meets_answered_empty_hold_no_short_list() {
    let (mut g, seed) = Rng::fresh("random parity meets");
    let set = |xs: &[usize]| (xs.iter().map(|&x| lit(x))).fold(Type::empty(), |u, x| &u | &x);
    // The meet of `k` two-state lists over the integers `0..a`, list `i` swapping its states on
    // `swaps[i]` and stopping in the states of the bits of `stops[i]`, and bounded to `0..a` when
    // `bounded`; returns its verdict and whether a list of length at most 4 is in it, and checks
    // that a meet answered `Empty` holds none.
    let check = |a: usize, swaps: &[Vec<usize>], stops: &[usize], bounded: bool, run: &str| {
        let k = swaps.len();
        let mut defs = Vec::new();
        for (i, swaps) in swaps.iter().enumerate() {
            for (state, other_state) in [(2 * i, 2 * i + 1), (2 * i + 1, 2 * i)] {
                let mut arms = Vec::new();
                if (stops[i] >> (state % 2)) & 1 == 1 {
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
            assert_eq!(found, None, "a list of a meet answered empty ({run})");
        }
        (v, found.is_some())
    };
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
        let stops: Vec<usize> = (0..k).map(|_| g.below(4)).collect();
        let (v, found) = check(a, &swaps, &stops, bounded, &format!("ZED_TEST_SEED={seed}"));
        *tally.entry((format!("{v:?}"), found)).or_insert(0) += 1;
    }
    eprintln!("random parity meets, by verdict and whether a short list was found: {tally:?}");
    // A meet answered `Empty` on every run, built (PROOF-test-count-thresholds): two lists over
    // the integer 0, each swapping its states on 0; the first stops in its first state, after
    // an even count of 0s, and the second in its second state, after an odd count. No list has
    // a count of 0s both even and odd, so the meet is empty, and by the GF(2) reading.
    let built = check(1, &[vec![0], vec![0]], &[1, 2], false, "built");
    assert_eq!(built, (Verdict::Empty, false), "the built meet");
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
    bounded_parity_group(k, hi, exclude, repeated)
        .instance(vec![])
        .pop()
        .unwrap()
}

/// The group of [`bounded_parity_variant`], whose last member is the meet.
fn bounded_parity_group(
    k: usize,
    hi: usize,
    exclude: Option<usize>,
    repeated: Option<usize>,
) -> Group {
    Group::new(bounded_parity_definitions(k, hi, exclude, repeated)).unwrap()
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
    let mut elem = Type::union_all((0..=hi).map(lit));
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
    let inputs = scaling::inputs(n, |k| {
        Fresh::new(bounded_parity_group(k, k, None, Some(4)), 2 * k + 3)
    });
    scaling::check_order("bounded parity with a repeated scalar field", n, 1, |k| {
        Type::forget_emptiness();
        assert_eq!(inputs[&k].member().verdict(), Verdict::Inhabited);
    });
}

/// Two literal sets and two rows are shared by all columns. Written DAG size
/// is linear in k; a checked witness has k integer fields, not k squared.
fn shared_integer_columns(k: usize, distinct: bool) -> Type {
    let evens = Type::union_all((0..k).map(|j| lit(2 * j)));
    let odds = Type::union_all((0..k).map(|j| lit(2 * j + 1)));
    let a = &Type::int() - &evens;
    let b = &Type::int() - &odds;
    let right = if distinct {
        (0..k).map(|j| &b - &lit(4 * k + j)).collect()
    } else {
        vec![b; k]
    };
    &Type::tuple(vec![a; k]) & &Type::tuple(right)
}

/// The inputs of this check and of [`cofinite_rows_scale`] are built by `check_order_inputs`,
/// only at the sizes each process runs: built at both sizes before the first run
/// (`scaling::inputs`), they took the whole first phase where each run is counted under
/// DynamoRIO in a new process that builds its input again; both benchmarks stopped at their
/// 20 s limit on hm4 (job f25 on main b43e6d8bb), and with no limit counted 7.99 and 8.12 times
/// the instructions at 8n in 48 and 60 s (job f27; BENCH-main-43-pieces-v5e4).
fn shared_integer_columns_check(n: usize, distinct: bool) {
    scaling::check_order_inputs(
        "shared scalar boundaries across tuple columns",
        n,
        1,
        |k| shared_integer_columns(k, distinct),
        |t| {
            Type::forget_emptiness();
            assert_eq!(t.verdict(), Verdict::Inhabited);
        },
    );
}

fn cofinite_rows(k: usize) -> Type {
    let excluded = Type::union_all((0..k).map(lit));
    let common = &Type::int() - &excluded;
    Type::meet_all((0..k).map(|j| Type::tuple(vec![&common - &lit(4 * k + j)])))
}

fn cofinite_rows_scale(n: usize) {
    scaling::check_order_inputs(
        "shared integer boundaries across rows",
        n,
        1,
        cofinite_rows,
        |t| {
            Type::forget_emptiness();
            assert_eq!(t.verdict(), Verdict::Inhabited);
        },
    );
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

/// A state of a list linked by `more` and ending in `nil`: it holds `nil` when it `accepts`,
/// and `more(h, s)` for each step `(h, s)`, to the state defined `s`-th.
fn more_state(name: &str, accepts: bool, steps: Vec<(Type, usize)>) -> Def {
    let mut arms = Vec::new();
    if accepts {
        arms.push(nil());
    }
    for (h, s) in steps {
        arms.push(Expr::Atom("more".into(), vec![Expr::Type(h), r(s)]));
    }
    def(name, Expr::Union(arms))
}

/// The meet of the group's last member, the defs given then the meet of the members named.
fn meet_of(mut defs: Vec<Def>, of: Vec<usize>) -> Type {
    defs.push(def("M", Expr::And(of.into_iter().map(r).collect())));
    Group::new(defs).unwrap().instance(vec![]).pop().unwrap()
}

/// The two states of a parity operand, defined `at` and `at + 1`: `v` keeps the state, every
/// other integer swaps it, and state `at` accepts when `even`, else `at + 1` does.
fn keeps_one(at: usize, v: usize, even: bool) -> [Def; 2] {
    let other = &Type::int() - &lit(v);
    [
        more_state(
            &format!("S{at}"),
            even,
            vec![(lit(v), at), (other.clone(), at + 1)],
        ),
        more_state(
            &format!("S{}", at + 1),
            !even,
            vec![(lit(v), at + 1), (other, at)],
        ),
    ]
}

/// `affine_lists_empty` with an integer, 0, that keeps the state of two operands it names, which
/// no test had (TEST-kernel-unreached-paths-14): the lists with an even count of items other
/// than 0 met with those with an odd count. Every other integer swaps both, so the two are
/// joined, and the count they need is both even and odd: empty. The control swaps the second
/// operand on 0 instead (an odd count of 0): the second operand is then joined to the ground,
/// the class proves nothing, and the search finds `more(0, nil)`.
#[test]
fn a_parity_meet_with_an_integer_that_keeps_both_states() {
    let [a0, a1] = keeps_one(0, 0, true);
    let [b0, b1] = keeps_one(2, 0, false);
    let t = meet_of(vec![a0, a1, b0, b1], vec![0, 2]);
    let one = |v: i64, tail: Value| Value::atom_with("more", vec![Value::Int(v), tail]);
    for w in [
        one(0, Value::atom("nil")),
        one(1, one(1, Value::atom("nil"))),
    ] {
        assert!(!t.contains(&w), "{w:?}");
    }
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Empty);
    let [a0, a1] = keeps_one(0, 0, true);
    let other = &Type::int() - &lit(0);
    let control = meet_of(
        vec![
            a0,
            a1,
            more_state("S2", false, vec![(lit(0), 3), (other.clone(), 2)]),
            more_state("S3", true, vec![(lit(0), 2), (other, 3)]),
        ],
        vec![0, 2],
    );
    assert!(control.contains(&one(0, Value::atom("nil"))));
    Type::forget_emptiness();
    assert_eq!(control.verdict(), Verdict::Inhabited);
}

/// `affine_lists_empty` gives up when the integers no operand names swap three constraining
/// operands, which no test reached (TEST-kernel-unreached-paths-14): the lists of even length,
/// those with an odd count of items other than 7, and those with an even count of items other
/// than 8. Each of 7 and 8 swaps two, which the class takes; the unnamed ones swap all three, an
/// equation of three unknowns, so the search decides. `more(7, more(1, nil))` is in all three.
#[test]
fn a_parity_meet_whose_unnamed_integers_swap_three_operands_is_searched() {
    let even = more_state("S0", true, vec![(Type::int(), 1)]);
    let odd = more_state("S1", false, vec![(Type::int(), 0)]);
    let [b0, b1] = keeps_one(2, 7, false);
    let [c0, c1] = keeps_one(4, 8, true);
    let t = meet_of(vec![even, odd, b0, b1, c0, c1], vec![0, 2, 4]);
    let w = Value::atom_with(
        "more",
        vec![
            Value::Int(7),
            Value::atom_with("more", vec![Value::Int(1), Value::atom("nil")]),
        ],
    );
    assert!(t.contains(&w));
    assert!(!t.contains(&Value::atom("nil")));
    Type::forget_emptiness();
    assert_eq!(t.verdict(), Verdict::Inhabited);
}

/// Small instance of `bench::meets_of_k_members_scale`: the meet of a few even-length lists is
/// settled with no search when an endless list is among them, and searched once otherwise; a
/// meet of one member is a difference, which the decider settles with no search since
/// GROUP-order-cpoly-merge.
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
            (Verdict::Inhabited, usize::from(k > 1)),
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
/// chain of members with an arm the search refuses is refused for want of a witness.
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

/// The chain whose arm is `{x | y: int} - ({x: int} | {y: int})` is inhabited: the arm is the
/// first type, which has a closure, since a closure of it has both keys and one of the second
/// has one of them (REP-refusals-rest point (1), b22-ref3). On origin/main at 3ca4683ea it was
/// refused with [`Refusal::NoWitness`] for each `m` here.
#[test]
fn a_short_chain_with_morphism_split_arms_is_inhabited() {
    for m in [1, 2, 5] {
        let types = morphism_split_chain(m);
        Type::forget_emptiness();
        assert_eq!(types[0].verdict(), Verdict::Inhabited, "m = {m}");
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

/// Item TEST-kernel-unreached-paths-15 (`empty`, a member the parity reading proves empty, met
/// below a root): the meet `M` of `bounded_parity(2, 1, None)` holds lists over 0 and 1 with an
/// even count of each and an odd length, and an even count plus an even count is even, so `M`
/// is empty. As the field of a tuple it is asked by the search as an inner type, and the search
/// answers it from `diagonal_empty` at once, with no member searched. Control: that answer
/// skipped (`return Stack::ready(true)` not taken) leaves the field to the search of the
/// group's members, which also finds it empty, but only after searching members.
#[test]
fn a_tuple_with_a_parity_meet_as_a_field_is_empty() {
    let t = Type::tuple(vec![bounded_parity(2, 1, None), Type::int()]);
    assert_eq!(verdict_and_searched(&t), (Verdict::Empty, 0));
}

/// Small instance of `bench::the_verdict_on_k_parity_lists_is_inhabited`: the verdict, not only
/// `is_empty`, on the product of a few parity lists is `Inhabited` (`[k]` is in it), where the
/// value search after a fork once walked the product of the meet's states and answered
/// `Refused(Fork)` (row VERDICT-fork-value: 178M, 1.11G and 4.51G instructions at k 2, 3, 4).
#[test]
fn the_verdict_on_a_few_parity_lists_is_inhabited() {
    for k in 1..=6 {
        Type::forget_emptiness();
        assert_eq!(parity_meet(k).verdict(), Verdict::Inhabited, "k = {k}");
    }
}
