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
/// timed; a run makes a fresh instance, whose group is decided anew. Building the instance
/// costs about 57k instructions an arm, which hides a quadratic merge of equal arms at small
/// `n`: one that looks each arm up in a list of the arms before it passed at `n` 1024 (10.2
/// times) and failed at 2048 and 4096 (12.2 times), against 8.1 times here.
#[test]
fn many_arms_scale() {
    let n = 4096;
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

/// The group of `bodies` named `Node`, `Tree`, `Thunk`, then `A1`, `A2` and on.
fn named(bodies: Vec<Expr>) -> Group {
    let defs = (bodies.into_iter().enumerate())
        .map(|(i, body)| Def {
            name: match i {
                NODE => "Node".into(),
                TREE => "Tree".into(),
                THUNK => "Thunk".into(),
                _ => format!("A{}", i - THUNK),
            },
            params: vec![],
            body,
        })
        .collect();
    Group::new(defs).unwrap_or_else(|e| panic!("{}", e.message))
}

/// [`verdicts`] for a group of any number of definitions, named as [`named`] names them.
fn verdicts_of(bodies: Vec<Expr>) -> Vec<(Option<bool>, Verdict)> {
    Type::forget_emptiness();
    (named(bodies).instance(vec![]).iter())
        .map(|t| (t.decided_by_group(), t.verdict()))
        .collect()
}

/// The first definition after `Thunk`.
const A1: usize = 3;

/// `(Tree, Tree)`.
fn tt() -> Expr {
    pair(r(TREE), r(TREE))
}

fn atom(name: &str) -> Expr {
    Expr::Type(Type::atom(name))
}

/// [`base`] with `Node` and the definitions after `Thunk`.
fn with(node: Expr, more: Vec<Expr>) -> Vec<Expr> {
    let mut bodies = Vec::from(base(node));
    bodies.extend(more);
    bodies
}

/// ```text
/// type Node = A1 | (Tree, Tree)
/// type A1 = ((int) -> Thunk) | (Tree, Tree)
/// ```
///
/// `Node`'s arm `(Tree, Tree)` is also an arm of `A1`. Before item GROUP-cycle-dup-names the
/// two were two nodes, one more independent cycle than with `A1`'s arms written out, and every
/// member was refused; `Node` now drops the arm it reaches through `A1`.
#[test]
fn a_union_named_as_an_arm_is_read_as_its_arms() {
    let a1 = || or(vec![f(r(THUNK)), tt()]);
    let out = verdicts_of(with(node(), vec![a1()]));
    assert!(decided(&out), "{out:?}");
    assert_eq!(verdicts_of(with(or(vec![r(A1), tt()]), vec![a1()])), out);
    assert_eq!(verdicts_of(with(or(vec![tt(), r(A1)]), vec![a1()])), out);
}

/// `n` names, each the one before with its arm `(Tree, Tree)` repeated and an atom:
///
/// ```text
/// type Node = An | (Tree, Tree)
/// type A1 = ((int) -> Thunk) | (Tree, Tree)
/// type Ak = A(k-1) | (Tree, Tree) | #ak
/// ```
///
/// With `written_out`, `Node` is `((int) -> Thunk) | (Tree, Tree) | #a2 | … | #an`.
fn chain(n: usize, written_out: bool) -> Vec<Expr> {
    let mut more = vec![or(vec![f(r(THUNK)), tt()])];
    for k in 2..=n {
        more.push(or(vec![r(A1 + k - 2), tt(), atom(&format!("a{k}"))]));
    }
    let node = if written_out {
        let mut arms = vec![f(r(THUNK)), tt()];
        arms.extend((2..=n).map(|k| atom(&format!("a{k}"))));
        or(arms)
    } else {
        or(vec![r(A1 + n - 1), tt()])
    };
    with(node, more)
}

#[test]
fn a_chain_of_names_is_read_as_its_arms() {
    for n in [1, 2, 5] {
        let out = verdicts_of(chain(n, true));
        assert!(decided(&out), "n = {n}: {out:?}");
        assert_eq!(verdicts_of(chain(n, false)), out, "n = {n}");
    }
}

/// ```text
/// type Node = A1 | (Tree, Tree)
/// type A1 = ((int) -> Thunk) | (Tree, Tree)
/// type A2 = A1 | #o
/// ```
///
/// `A1` is named by two unions, so `Node` does not dominate it, but every union `Node` reaches
/// passes through `A1`: `A1` post-dominates `Node`.
#[test]
fn a_name_used_twice_is_read_as_its_arms() {
    let more = || vec![or(vec![f(r(THUNK)), tt()]), or(vec![r(A1), atom("o")])];
    let out = verdicts_of(with(node(), more()));
    assert!(decided(&out), "{out:?}");
    assert_eq!(verdicts_of(with(or(vec![r(A1), tt()]), more())), out);
}

/// ```text
/// type Node = A2 | (Tree, Tree)
/// type A1 = ((int) -> Thunk) | (Tree, Tree)
/// type A2 = A1 | (Tree, Tree) | (A2, #z)
/// ```
///
/// A name that refers to itself through a tuple, with arms that overlap those of the name it
/// names: `A2` drops `(Tree, Tree)`, an arm of `A1`, and `Node` drops it too. Written with
/// `(A2, #z)` as an arm of `Node` as well, `Node` drops that arm, an arm of `A2`. (With `A2`'s
/// arms written out in `Node`, `Node` and `A2` each have their own `(A2, #z)` and neither names
/// the other, and the group is refused: follow-up GROUP-cycle-dup-across.)
#[test]
fn names_in_a_cycle_are_read_as_their_arms() {
    let a2z = || pair(r(A1 + 1), atom("z"));
    let more = || vec![or(vec![f(r(THUNK)), tt()]), or(vec![r(A1), tt(), a2z()])];
    let out = verdicts_of(with(or(vec![r(A1 + 1), tt()]), more()));
    assert!(decided(&out), "{out:?}");
    assert_eq!(
        verdicts_of(with(or(vec![r(A1 + 1), tt(), a2z()]), more())),
        out
    );
}

/// Deciding the group of a [`chain`] of `n` and `8n` names: one topological order, two trees
/// with lowest common ancestors in `log n`, and one sort of the arms, so within `n log n`.
#[test]
fn a_chain_of_names_scales() {
    let n = 128;
    let groups = scaling::inputs(n, |m| named(chain(m, false)));
    scaling::check_order("a chain of n names", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}

/// ```text
/// type Node = (Node, Node) | Tree | ((Node, int), (int) -> Tree) | (int) -> (Node, Node)
/// type Tree = ((Node, int), (int) -> Tree) | (int) -> (Node, Node) | (Node, Node)
/// ```
///
/// `Node`'s arms other than `Tree` are arms of `Tree`, so `Node` with them dropped is `Tree`.
/// The group is decided inhabited as written, and refused with those arms dropped: the
/// decider's bounds depend on the graph's shape, so the dropped arms are decided as a second
/// system beside the one written, and a member either decides is decided.
#[test]
fn a_group_decided_as_written_stays_decided() {
    let nn = || pair(r(NODE), r(NODE));
    let both = || vec![pair(pair(r(NODE), int()), f(r(TREE))), f(nn())];
    let mut node = vec![nn(), r(TREE)];
    node.extend(both());
    let mut tree = both();
    tree.push(nn());
    let v = verdicts_of(vec![or(node), or(tree)]);
    assert!(
        v.iter().all(|&(d, _)| d == Some(false)),
        "both members are inhabited: {v:?}"
    );
}

/// ```text
/// type Node = Tree | (Node, Tree) | (int, (int) -> (int) -> Tree) | (Tree, Node) | ((int) -> Tree, Node | Tree)
/// type Tree = (Tree, Node) | ((int) -> Tree, Node | Tree)
/// ```
///
/// Every arm of `Tree` is an arm of `Node`, so `Node | Tree` is `Node`. Each `Node | Tree`
/// reaches `Tree` through `Node`, but `Node` is named by both, so neither dominates it and
/// neither is post-dominated by it: the arm is kept (`// Complexity tradeoff:` at
/// `names::absorb`), the decider refuses the group, and the search finds its values. With
/// `Node | Tree` written `Node` the decider decides it. Seed 34841 of the item's probe; when the
/// tradeoff is lifted, the first verdicts become decided too.
#[test]
fn a_name_reached_by_two_unions_is_left_to_the_search() {
    let (node, tree) = (|| r(NODE), || r(TREE));
    let group = |inner: &dyn Fn() -> Expr| {
        let arms = vec![
            tree(),
            pair(node(), tree()),
            pair(int(), f(f(tree()))),
            pair(tree(), node()),
            pair(f(tree()), inner()),
        ];
        vec![
            or(arms),
            or(vec![pair(tree(), node()), pair(f(tree()), inner())]),
        ]
    };
    let as_written = verdicts_of(group(&|| or(vec![node(), tree()])));
    assert_eq!(
        as_written,
        vec![(None, Verdict::Inhabited), (None, Verdict::Inhabited)]
    );
    let v = verdicts_of(group(&node));
    assert!(v.iter().all(|&(d, _)| d == Some(false)), "{v:?}");
}
