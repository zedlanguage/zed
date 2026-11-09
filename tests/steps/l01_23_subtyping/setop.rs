//! Members of recursive groups under `&` and `\` (plan item GROUP-setop). The group's decider
//! reads `A & B` as a node that needs both operands and `A \ B` as `A`: a set of values that
//! holds the member's, so a member it proves empty is empty, and the search is skipped
//! (`Type::members_searched` counts the members sent to it). A member it shows inhabited
//! through such a node may still be empty (`#a & #b` below), so that answer goes to the search.

use zed_kernel::Value;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
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

/// Meets of `k` members at `k` and `8k`: with one empty operand the decider settles the meet
/// with no search; with all operands inhabited only the meet is searched.
#[test]
fn meets_of_k_members_scale() {
    let empty = scaling::inputs(8, |k| meet_of_k(k, true));
    let full = scaling::inputs(8, |k| meet_of_k(k, false));
    scaling::check("the verdict on a meet of k members, one empty", 8, |k| {
        assert_eq!(verdict_and_searched(&empty[&k]), (Verdict::Empty, 0));
    });
    scaling::check("the verdict on a meet of k inhabited members", 8, |k| {
        assert_eq!(verdict_and_searched(&full[&k]), (Verdict::Inhabited, 1));
    });
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

/// The product of `k` parity lists is inhabited (`[k]` is in it), and the search for a value
/// meets a fork of recursive tuple types: the verdict is refused with `Refusal::Fork`, the named
/// refusal of this exponential case (COMPLEXITY.md K35), and emptiness counts the meet
/// inhabited in time of order `k log k`.
#[test]
fn the_product_of_k_parity_lists_is_refused_by_its_fork() {
    assert_eq!(
        verdict_and_searched(&parity_meet(2)),
        (Verdict::Refused(Refusal::Fork), 1)
    );
    let meets = scaling::inputs(4, parity_meet);
    scaling::check("emptiness of the product of k parity lists", 4, |k| {
        Type::forget_emptiness();
        assert!(!meets[&k].is_empty());
    });
}
