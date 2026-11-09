//! A group the decider decides stays decided however its union arms are written (item
//! GROUP-cycle-dup, DESIGN.md L1.23 and the rule that checking does not depend on how an equal
//! type is written). The decider refuses a component by counting its independent cycles as
//! edges minus nodes plus one, and takes an exact path when the component holds one morphism
//! type; with a node made for each arm as written, an arm written twice added nodes and edges,
//! and a decided group could be refused. Parts of a definition written alike up to the order,
//! repetition and grouping of union arms are now one node, and a union's arms a set.

use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Type, Verdict};
use zed_tests::scaling;

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn int() -> Expr {
    Expr::Type(Type::int())
}

/// `(int) -> x`.
fn f(x: Expr) -> Expr {
    Expr::exact(int(), x)
}

fn pair(a: Expr, b: Expr) -> Expr {
    Expr::Tuple(vec![a, b])
}

fn or(xs: Vec<Expr>) -> Expr {
    Expr::Union(xs)
}

const NODE: usize = 0;
const TREE: usize = 1;
const THUNK: usize = 2;

/// The group of `defs` named `Node`, `Tree` and `Thunk`, instantiated with no arguments.
fn group(defs: [Expr; 3]) -> Vec<Type> {
    let defs = (["Node", "Tree", "Thunk"].into_iter().zip(defs))
        .map(|(name, body)| Def {
            name: name.into(),
            params: vec![],
            body,
        })
        .collect();
    Group::new(defs)
        .map(|g| g.instance(vec![]))
        .unwrap_or_else(|e| panic!("{}", e.message))
}

/// What the decider and the checker say of each member.
fn verdicts(defs: [Expr; 3]) -> Vec<(Option<bool>, Verdict)> {
    Type::forget_emptiness();
    (group(defs).iter())
        .map(|t| (t.decided_by_group(), t.verdict()))
        .collect()
}

/// ```text
/// type Node = ((int) -> Thunk) | (Tree, Tree)
/// type Tree = (Tree, Thunk) | (Node, Thunk)
/// type Thunk = (int) -> Tree
/// ```
///
/// Each member has a value (a function may return a value that holds it), and the decider
/// shows it: its component has two morphism types, two independent cycles and tuples with two
/// undecided components, and one deletion cascade decides it.
fn base(node: Expr) -> [Expr; 3] {
    [
        node,
        or(vec![pair(r(TREE), r(THUNK)), pair(r(NODE), r(THUNK))]),
        f(r(TREE)),
    ]
}

fn node() -> Expr {
    or(vec![f(r(THUNK)), pair(r(TREE), r(TREE))])
}

/// Every member decided inhabited by the decider.
fn decided(v: &[(Option<bool>, Verdict)]) -> bool {
    v.iter()
        .all(|(d, verdict)| *d == Some(false) && *verdict == Verdict::Inhabited)
}

#[test]
fn the_group_as_written_is_decided() {
    let v = verdicts(base(node()));
    assert!(decided(&v), "{v:?}");
}

/// `type Node = ((int) -> Thunk) | (Tree, Tree) | (Tree, Tree)`. Before this item each member
/// was refused: the second `(Tree, Tree)` added a node and two edges, one more cycle.
#[test]
fn a_tuple_arm_written_twice_leaves_the_group_decided() {
    let tuple = || pair(r(TREE), r(TREE));
    let twice = or(vec![f(r(THUNK)), tuple(), tuple()]);
    assert_eq!(verdicts(base(twice)), verdicts(base(node())));
}

/// `type Node = ((int) -> Thunk) | ((int) -> Thunk) | (Tree, Tree)`: one morphism type written
/// twice is still one, so the count of morphism types the decider reads does not change.
#[test]
fn a_morphism_arm_written_twice_leaves_the_group_decided() {
    let twice = or(vec![f(r(THUNK)), f(r(THUNK)), pair(r(TREE), r(TREE))]);
    assert_eq!(verdicts(base(twice)), verdicts(base(node())));
}

/// `type Tree = (Node, Thunk) | (Tree, Thunk) | (Tree, Thunk)`: arms reordered and one repeated.
#[test]
fn reordered_arms_leave_the_group_decided() {
    let mut defs = base(node());
    defs[TREE] = or(vec![
        pair(r(NODE), r(THUNK)),
        pair(r(TREE), r(THUNK)),
        pair(r(TREE), r(THUNK)),
    ]);
    assert_eq!(verdicts(defs), verdicts(base(node())));
}

/// `type Node = ((int) -> Thunk) | (Tree | int, Tree) | (int | Tree, Tree)` against the same
/// with the second tuple left out: two tuples whose union components differ only in the order
/// of their arms are one tuple.
#[test]
fn tuples_whose_unions_differ_in_order_are_one() {
    let once = or(vec![f(r(THUNK)), pair(or(vec![r(TREE), int()]), r(TREE))]);
    let both = or(vec![
        f(r(THUNK)),
        pair(or(vec![r(TREE), int()]), r(TREE)),
        pair(or(vec![int(), r(TREE)]), r(TREE)),
    ]);
    let v = verdicts(base(once));
    assert!(decided(&v), "{v:?}");
    assert_eq!(verdicts(base(both)), v);
}

/// `type Node = ((int) -> Thunk) | ((Tree, Tree) | ((int) -> Thunk))` and
/// `type Node = (((int) -> Thunk) | (Tree, Tree)) | (Tree, Tree)`: a union written as an arm is
/// read as its arms.
#[test]
fn regrouped_arms_leave_the_group_decided() {
    let tuple = || pair(r(TREE), r(TREE));
    let right = or(vec![f(r(THUNK)), or(vec![tuple(), f(r(THUNK))])]);
    let left = or(vec![or(vec![f(r(THUNK)), tuple()]), tuple()]);
    let want = verdicts(base(node()));
    assert_eq!(verdicts(base(right)), want);
    assert_eq!(verdicts(base(left)), want);
}

/// `Node` with its union written as `n` arms nested to the left, `(((a0 | a1) | a2) | …)`,
/// the arm `k` being `(Tree | int, #ak)` with `Tree | int` in either order and every arm written
/// twice: `n` distinct tuples, one union `Tree | int`.
fn wide(n: usize) -> [Expr; 3] {
    let arm = |k: usize, flip: bool| {
        let (a, b) = if flip {
            (int(), r(TREE))
        } else {
            (r(TREE), int())
        };
        pair(or(vec![a, b]), Expr::Type(Type::atom(&format!("a{k}"))))
    };
    let mut node = f(r(THUNK));
    for k in 0..n {
        node = or(vec![node, arm(k, k % 2 == 1)]);
        node = or(vec![node, arm(k, k % 2 == 0)]);
    }
    base(node)
}

/// Each arm written once, in a flat union.
fn wide_once(n: usize) -> [Expr; 3] {
    let mut arms = vec![f(r(THUNK))];
    arms.extend((0..n).map(|k| {
        pair(
            or(vec![r(TREE), int()]),
            Expr::Type(Type::atom(&format!("a{k}"))),
        )
    }));
    base(or(arms))
}

#[test]
fn many_arms_written_twice_and_nested_are_read_as_written_once() {
    for n in [1, 2, 5] {
        let v = verdicts(wide_once(n));
        assert!(decided(&v), "n = {n}: {v:?}");
        assert_eq!(verdicts(wide(n)), v, "n = {n}");
    }
}

/// Deciding the group of [`wide`] at `n` and `8n` arms: each part is read once and a union's
/// arms sorted, so the work is within `n log n`. The definitions are checked before the runs are
/// timed; a run makes a fresh instance, whose group is decided anew.
#[test]
fn many_arms_scale() {
    let n = 256;
    let groups = scaling::inputs(n, |m| {
        let defs = (["Node", "Tree", "Thunk"].into_iter().zip(wide(m)))
            .map(|(name, body)| Def {
                name: name.into(),
                params: vec![],
                body,
            })
            .collect();
        Group::new(defs).unwrap_or_else(|e| panic!("{}", e.message))
    });
    scaling::check_order("a union of n arms written twice and nested", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}
