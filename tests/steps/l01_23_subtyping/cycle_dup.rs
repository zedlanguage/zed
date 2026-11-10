//! A group the decider decides stays decided however its union arms are written (item
//! GROUP-cycle-dup, DESIGN.md L1.23 and the rule that checking does not depend on how an equal
//! type is written). The decider refuses a component by counting its independent cycles as
//! edges minus nodes plus one, and takes an exact path when the component holds one morphism
//! type; with a node made for each arm as written, an arm written twice added nodes and edges,
//! and a decided group could be refused. Parts of a definition written alike up to the order,
//! repetition and grouping of union arms are now one node, and a union's arms a set.

use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
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

/// `(int) -> (x0 & x1 & …)`, the parts in the order given.
fn returns_meet(parts: Vec<Expr>) -> Expr {
    f(Expr::And(parts))
}

/// `Node` with `n` more arms `(int) -> ((Node | #bk, top) & Tree)`, each written once, or with
/// `twice` written a second time with the parts of its meet the other way round,
/// `(int) -> (Tree & (Node | #bk, top))`.
fn meets_in_orders(n: usize, twice: bool) -> [Expr; 3] {
    let mut arms = vec![f(r(THUNK)), tt()];
    for k in 0..n {
        let b = || {
            pair(
                or(vec![r(NODE), atom(&format!("b{k}"))]),
                Expr::Type(Type::top()),
            )
        };
        arms.push(returns_meet(vec![b(), r(TREE)]));
        if twice {
            arms.push(returns_meet(vec![r(TREE), b()]));
        }
    }
    base(or(arms))
}

/// A meet is one type whatever the order of its parts, as a union is whatever the order of its
/// arms (item GROUP-search-canon-key): `(int) -> ((Node | #bk, top) & Tree)` and the same with
/// the parts of its meet the other way round are one morphism type, so writing each arm a
/// second time in the other order changes no verdict. (The decider and the search already
/// agreed here before the item; the order differences it removed are those of
/// `group_oracle::meets_whose_parts_differ_in_order_agree_across_orders`.)
#[test]
fn many_meets_written_in_two_orders_are_read_as_written_once() {
    for n in [1, 2, 5] {
        assert_eq!(
            verdicts(meets_in_orders(n, true)),
            verdicts(meets_in_orders(n, false)),
            "n = {n}"
        );
    }
}

/// Deciding the group of [`meets_in_orders`] with every meet written twice, at `n` and `8n`
/// arms: each part is read once and the operands of a meet are of one color, so building the
/// canonical form stays within `n log n` (item GROUP-search-canon-key).
#[test]
fn many_meets_in_two_orders_scale() {
    let n = 512;
    let groups = scaling::inputs(n, |m| {
        let defs = (["Node", "Tree", "Thunk"]
            .into_iter()
            .zip(meets_in_orders(m, true)))
        .map(|(name, body)| Def {
            name: name.into(),
            params: vec![],
            body,
        })
        .collect();
        Group::new(defs).unwrap_or_else(|e| panic!("{}", e.message))
    });
    scaling::check_order("a union of n meets each written in two orders", n, 1, |m| {
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

/// Each member's refusal message, `None` for a member that is not refused.
fn messages(bodies: Vec<Expr>) -> Vec<Option<String>> {
    Type::forget_emptiness();
    (named(bodies).instance(vec![]).iter())
        .map(|t| t.refusal_site(Refusal::Group).and_then(|s| s.detail))
        .collect()
}

/// A member the decider decides is not empty, and whose value the checker builds.
const HAS_A_VALUE: (Option<bool>, Verdict) = (Some(false), Verdict::Inhabited);

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
/// `(A2, #z)` as an arm of `Node` as well, `Node` drops that arm, an arm of `A2`. With `A2`'s
/// arms written out in `Node`, `type Node = A1 | (Tree, Tree) | (A2, #z)`, `Node` and `A2`
/// each have their own `(A2, #z)` and neither names the other: the two equal tuples are
/// decided as one (item GROUP-cycle-dup-across); before that item the group was refused.
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
    let written_out = with(or(vec![r(A1), tt(), a2z()]), more());
    assert_eq!(verdicts_of(written_out), out);
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

/// Seed 34841 of the probe of item GROUP-cycle-dup-names (DOCS-TODO.md entry 48, example 4),
/// with each `Node | Tree` written `inner` (`node_inner` in `Node`, `tree_inner` in `Tree`):
///
/// ```text
/// type Node = Tree | (Node, Tree) | (int, (int) -> (int) -> Tree) | (Tree, Node) | ((int) -> Tree, Node | Tree)
/// type Tree = (Tree, Node) | ((int) -> Tree, Node | Tree)
/// ```
fn seed_34841(node_inner: Expr, tree_inner: Expr) -> Vec<Expr> {
    let (node, tree) = (|| r(NODE), || r(TREE));
    vec![
        or(vec![
            tree(),
            pair(node(), tree()),
            pair(int(), f(f(tree()))),
            pair(tree(), node()),
            pair(f(tree()), node_inner),
        ]),
        or(vec![pair(tree(), node()), pair(f(tree()), tree_inner)]),
    ]
}

fn node_or_tree() -> Expr {
    or(vec![r(NODE), r(TREE)])
}

/// Every arm of `Tree` is an arm of `Node`, so `Node | Tree` is `Node`; each `Node | Tree`
/// names `Tree` directly and through `Node`, a name reached by two unions, which neither
/// dominance nor post-dominance sees (`names::absorb`). Before item GROUP-cycle-dup-across the
/// decider refused the group and the search found its values. Now either of two things
/// decides it: the edge from `Node | Tree` to `Tree` runs along the cycle through `Node`, so
/// the ring is one cycle (`bes::one_cycle_but_union_chords`); and `Node`'s
/// `((int) -> Tree, Node | Tree)` is written alike in `Tree`, so the system with the nodes that
/// play alike merged has one node for both (`names::merged`). The verdicts are those of the group
/// with `Node | Tree` written `Node`: each member has a value and no message.
#[test]
fn a_name_reached_by_two_unions_is_read_as_its_arms() {
    let as_written = verdicts_of(seed_34841(node_or_tree(), node_or_tree()));
    assert_eq!(as_written, vec![HAS_A_VALUE; 2]);
    assert_eq!(
        messages(seed_34841(node_or_tree(), node_or_tree())),
        vec![None; 2]
    );
    assert_eq!(verdicts_of(seed_34841(r(NODE), r(NODE))), as_written);
}

/// Seed 34841 with a third arm in one `Node | Tree` (`x3` of the item's probe):
///
/// ```text
/// type Node = Tree | (Node, Tree) | (int, (int) -> (int) -> Tree) | (Tree, Node)
/// type Tree = (Tree, Node) | ((int) -> Tree, Node | Tree) | (Tree, Node | (Node, Node))
/// ```
///
/// `Node`'s and `Tree`'s parts differ, so merging the nodes that play alike changes nothing that
/// matters here (the decider refuses the merged system too); the edge from
/// `Node | Tree` to `Tree` runs along the cycle through `Node`, and the group is decided as with
/// `Node | Tree` written `Node`. Before the item, the decider refused it.
#[test]
fn a_union_edge_along_the_cycle_is_not_a_second_cycle() {
    let group = |inner: Expr| {
        let (node, tree) = (|| r(NODE), || r(TREE));
        vec![
            or(vec![
                tree(),
                pair(node(), tree()),
                pair(int(), f(f(tree()))),
                pair(tree(), node()),
            ]),
            or(vec![
                pair(tree(), node()),
                pair(f(tree()), inner),
                pair(tree(), or(vec![node(), pair(node(), node())])),
            ]),
        ]
    };
    let as_written = verdicts_of(group(node_or_tree()));
    assert!(decided(&as_written), "{as_written:?}");
    assert_eq!(verdicts_of(group(r(NODE))), as_written);
}

/// Seed 57360 of the probe of item GROUP-cycle-dup-names, `F(x)` standing for `(int) -> x`:
///
/// ```text
/// type Node = F(Thunk) | Thunk | A1 | F(Thunk) | Tree | (Thunk, Thunk)
/// type Tree = Thunk | A1 | A1 | F(Thunk) | Thunk | (A1, (#a, A1)) | (A1, Node)
/// type Thunk = (A1, (#a, A1)) | A1 | (A1, Node) | (A1, (#a, A1)) | (A1 | (Thunk | Tree, int)) | A1 | (Thunk, Thunk) | (Thunk, Thunk)
/// type A1 = (Thunk, Thunk)
/// ```
///
/// `A1` and the arm `(Thunk, Thunk)` of `Node` and of `Thunk` are one type written in three
/// places, and `(A1, (#a, A1))` and `(A1, Node)` are written in both `Tree` and `Thunk`, with no
/// union path between the places.
fn seed_57360() -> Vec<Expr> {
    let (node, tree, thunk, a1) = (|| r(NODE), || r(TREE), || r(THUNK), || r(A1));
    let a = || pair(a1(), pair(atom("a"), a1()));
    vec![
        or(vec![
            f(thunk()),
            thunk(),
            a1(),
            f(thunk()),
            tree(),
            pair(thunk(), thunk()),
        ]),
        or(vec![
            thunk(),
            a1(),
            a1(),
            f(thunk()),
            thunk(),
            a(),
            pair(a1(), node()),
        ]),
        or(vec![
            a(),
            a1(),
            pair(a1(), node()),
            a(),
            or(vec![a1(), pair(or(vec![thunk(), tree()]), int())]),
            a1(),
            pair(thunk(), thunk()),
            pair(thunk(), thunk()),
        ]),
        pair(thunk(), thunk()),
    ]
}

/// Each part of [`seed_57360`] written in two places was its own node before item
/// GROUP-cycle-dup-across, and the decider refused the group. Decided with the nodes that play
/// alike merged (`names::merged`), every member has a value and no message. A message reads the
/// system as written, so it still names the program's own definitions
/// (`group_refusal::a_mixed_component_is_refused_with_its_own_message`, whose group has a merged
/// system).
#[test]
fn equal_parts_in_two_definitions_are_one() {
    assert_eq!(verdicts_of(seed_57360()), vec![HAS_A_VALUE; 4]);
    assert_eq!(messages(seed_57360()), vec![None; 4]);
}

/// `Node | Tree` written `Node | Tree | (Tree, Node)`, the wider union of seed 34841.
fn wider() -> Expr {
    or(vec![r(NODE), r(TREE), pair(r(TREE), r(NODE))])
}

/// Seed 34841 written two more ways: `Node | Tree` in `Node` written
/// `Node | Tree | (Tree, Node)`, and `Node | Tree` in `Tree` written `Node`. Each union is still
/// `Node`, but the two `((int) -> Tree, …)` parts are equal only once arms are dropped:
/// `Node | Tree | (Tree, Node)` against `Node | Tree` in the first, `Node | Tree` against `Node`
/// in the second. Neither the union edge test nor the merge of nodes that play alike sees that
/// alone. Before item GROUP-arm-drop-merge the decider refused the group and the search found
/// every member's value. Now the system with arms dropped (`names::absorb`) is merged too, after
/// each union left with one arm is read as that arm (`names::contracted`): the two parts are one
/// node there, and every member has a value and no message.
#[test]
fn parts_equal_only_once_arms_are_dropped_are_one() {
    for (form, bodies) in [
        ("wider", seed_34841(wider(), node_or_tree())),
        ("Node", seed_34841(node_or_tree(), r(NODE))),
    ] {
        assert_eq!(verdicts_of(bodies.clone()), vec![HAS_A_VALUE; 2], "{form}");
        assert_eq!(messages(bodies), vec![None; 2], "{form}");
    }
}

/// Seed 34841 with `Tree`'s `Node | Tree` written through a name for `Node`, `Thunk`:
///
/// ```text
/// type Tree = (Tree, Node) | ((int) -> Tree, inner)
/// ```
///
/// with `inner` written `Thunk | Node` and `type Thunk = Node`; `Thunk | Node` and
/// `type Thunk = A1`, `type A1 = Node`; or `Thunk` and `type Thunk = Node`. `Thunk` is a second
/// union parent of `Node`, so no arm of `Thunk | Node` is dropped by dominance; read as one arm,
/// each `inner` is `Node`, and `Tree`'s `((int) -> Tree, inner)` plays alike with `Node`'s
/// `((int) -> Tree, Node | Tree)` once `Node | Tree` has dropped `Tree`. Before item
/// GROUP-arm-drop-merge each was left to the search; now every member has a value and no message.
#[test]
fn a_name_for_a_member_is_read_as_that_member() {
    let node_inner = node_or_tree();
    let mut alias = seed_34841(node_inner.clone(), or(vec![r(THUNK), r(NODE)]));
    alias.push(r(NODE));
    let mut alias_chain = seed_34841(node_inner.clone(), or(vec![r(THUNK), r(NODE)]));
    alias_chain.extend([r(A1), r(NODE)]);
    let mut alias_only = seed_34841(node_inner, r(THUNK));
    alias_only.push(r(NODE));
    for (form, bodies) in [
        ("alias", alias),
        ("alias chain", alias_chain),
        ("alias only", alias_only),
    ] {
        let len = bodies.len();
        assert_eq!(
            verdicts_of(bodies.clone()),
            vec![HAS_A_VALUE; len],
            "{form}"
        );
        assert_eq!(messages(bodies), vec![None; len], "{form}");
    }
}

/// `n` copies of seed 34841 with `Node | Tree` in `Node` written as in [`wider`], copy `i` its
/// definitions `2i` and `2i + 1`.
fn copies(n: usize) -> Vec<Expr> {
    let mut bodies = Vec::new();
    for i in 0..n {
        let (node, tree) = (|| r(2 * i), || r(2 * i + 1));
        let wide = or(vec![node(), tree(), pair(tree(), node())]);
        bodies.push(or(vec![
            tree(),
            pair(node(), tree()),
            pair(int(), f(f(tree()))),
            pair(tree(), node()),
            pair(f(tree()), wide),
        ]));
        bodies.push(or(vec![
            pair(tree(), node()),
            pair(f(tree()), or(vec![node(), tree()])),
        ]));
    }
    bodies
}

/// Every copy in [`copies`] is decided, as one copy is.
#[test]
fn copies_of_parts_equal_once_arms_are_dropped_are_decided() {
    for n in [1, 2, 5] {
        assert_eq!(verdicts_of(copies(n)), vec![HAS_A_VALUE; 2 * n], "n = {n}");
        assert_eq!(messages(copies(n)), vec![None; 2 * n], "n = {n}");
    }
}

/// Deciding [`copies`] of `n` and `8n`: one round of contraction, merging and dropping arms,
/// within `m log m`.
#[test]
fn copies_of_parts_equal_once_arms_are_dropped_scale() {
    let n = 64;
    let groups = scaling::inputs(n, |m| named(copies(m)));
    scaling::check_order("n copies of parts equal once arms are dropped", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}

/// `n` levels of seed 34841 in its wider form, level `k` its definitions `Nodek`, `Treek`, `Wk`
/// and `Vk`, numbered `4k` to `4k + 3`:
///
/// ```text
/// type Nodek = Treek | (Nodek, Treek) | (int, (int) -> (int) -> Treek) | (Treek, Nodek) | Wk
/// type Treek = (Treek, Nodek) | Vk | (Treek, V(k-1))
/// type Wk = ((int) -> Treek, Nodek | Treek | (Treek, W(k-1)))
/// type Vk = ((int) -> Treek, Nodek | Treek)
/// ```
///
/// with `(Treek, V(k-1))` absent and `W(k-1)` read as `Node0` at level 0. `Wk` and `Vk` are one
/// type once the arm `(Treek, W(k-1))` is dropped, as at level 0; that arm is an arm of `Treek`,
/// `(Treek, V(k-1))`, only once `W(k-1)` and `V(k-1)` are one node. So level `k` needs a round
/// of dropping arms and merging after level `k - 1`'s.
fn rounds(n: usize) -> Vec<Expr> {
    let mut bodies = Vec::new();
    for k in 0..n {
        let at = |i: usize| move || r(4 * k + i);
        let (node, tree, w, v) = (at(0), at(1), at(2), at(3));
        bodies.push(or(vec![
            tree(),
            pair(node(), tree()),
            pair(int(), f(f(tree()))),
            pair(tree(), node()),
            w(),
        ]));
        let mut tree_arms = vec![pair(tree(), node()), v()];
        if k > 0 {
            tree_arms.push(pair(tree(), r(4 * k - 1)));
        }
        bodies.push(or(tree_arms));
        let below = if k == 0 { node() } else { r(4 * k - 2) };
        bodies.push(pair(
            f(tree()),
            or(vec![node(), tree(), pair(tree(), below)]),
        ));
        bodies.push(pair(f(tree()), or(vec![node(), tree()])));
    }
    bodies
}

/// The decider takes one round of dropping arms and merging, so in [`rounds`] of 2 it decides
/// level 0 and leaves level 1 to the search, which finds its values with no message
/// (`// Complexity tradeoff:` at `names::contracted`; repeating the rounds until nothing changes
/// costs a round per level). With `W0` written as `V0` is, level 1 is still left: `W0` and `V0`
/// are then one node, but `W1` and `V1` are one only after `(Tree1, W0)` is dropped and the
/// parts merged again. With `W1`'s arm written `(Tree1, V0)`, level 1 is level 0 again, and one
/// round decides it.
#[test]
fn parts_equal_only_after_two_rounds_are_left_to_the_search() {
    let left = (None, Verdict::Inhabited);
    let level_1_left = [vec![HAS_A_VALUE; 4], vec![left; 4]].concat();
    assert_eq!(verdicts_of(rounds(2)), level_1_left);
    assert_eq!(messages(rounds(2)), vec![None; 8]);
    let (node1, tree1, v0, w1) = (4, 5, 3, 6);
    let mut w0_alike = rounds(2);
    w0_alike[2] = pair(f(r(TREE)), node_or_tree());
    assert_eq!(verdicts_of(w0_alike), level_1_left);
    let mut v0_in_w1 = rounds(2);
    v0_in_w1[w1] = pair(
        f(r(tree1)),
        or(vec![r(node1), r(tree1), pair(r(tree1), r(v0))]),
    );
    assert_eq!(verdicts_of(v0_in_w1), vec![HAS_A_VALUE; 8]);
}

/// [`seed_57360`], whose group the decider refuses as written, with two chains of `n` names
/// written alike after it, `Ak` for `k` from 2 to `n + 1` and `Bk` the `k`th after them:
///
/// ```text
/// type Ak = (A(k+1), Node) | (Tree, Tree)   type A(n+1) = (Node, Node)
/// type Bk = (B(k+1), Node) | (Tree, Tree)   type B(n+1) = (Node, Node)
/// ```
///
/// `Ak` and `Bk` play alike, and no two names of one chain do, since they lie at different
/// distances from its end: a partition refined one round at a time takes `n` rounds to tell
/// them apart.
fn two_chains(n: usize) -> Vec<Expr> {
    let mut bodies = seed_57360();
    for first in [A1 + 1, A1 + 1 + n] {
        for k in 0..n {
            bodies.push(if k + 1 == n {
                pair(r(NODE), r(NODE))
            } else {
                or(vec![pair(r(first + k + 1), r(NODE)), tt()])
            });
        }
    }
    bodies
}

/// The chains of [`two_chains`] change nothing in the members of [`seed_57360`], and each name
/// in them has a value.
#[test]
fn two_chains_written_alike_are_decided() {
    for n in [1, 2, 5] {
        let v = verdicts_of(two_chains(n));
        assert_eq!(v, vec![HAS_A_VALUE; 4 + 2 * n], "n = {n}");
        assert_eq!(messages(two_chains(n)), vec![None; 4 + 2 * n], "n = {n}");
    }
}

/// Deciding the group of [`two_chains`] of `n` and `8n` names, with the nodes that play alike
/// found by the refinement of `names::merged`, within `m log m`.
#[test]
fn two_chains_written_alike_scale() {
    let n = 512;
    let groups = scaling::inputs(n, |m| named(two_chains(m)));
    scaling::check_order("two chains of n names written alike", n, 1, |m| {
        Type::forget_emptiness();
        for t in &groups[&m].instance(vec![]) {
            std::hint::black_box(t.decided_by_group());
        }
    });
}

/// The groups of items GROUP-cycle-dup-across and GROUP-arm-drop-merge: seed 34841 as written
/// and in the two forms equal once arms are dropped, seed 57360, [`two_chains`] of 3, [`copies`]
/// of 2 and [`rounds`] of 2.
fn item_groups() -> Vec<Vec<Expr>> {
    vec![
        seed_34841(node_or_tree(), node_or_tree()),
        seed_34841(wider(), node_or_tree()),
        seed_34841(node_or_tree(), r(NODE)),
        seed_57360(),
        two_chains(3),
        copies(2),
        rounds(2),
    ]
}

/// What the decider says of `t`, its verdict, and its refusal message.
fn answers(t: &Type) -> (Option<bool>, Verdict, Option<String>) {
    let message = t.refusal_site(Refusal::Group).and_then(|s| s.detail);
    (t.decided_by_group(), t.verdict(), message)
}

/// Each group of [`item_groups`] checked alone, on a thread of its own with nothing cached,
/// gives the same answers as in a batch: every group checked on one thread after the others
/// with nothing forgotten, the groups and their members in reverse order, twice over.
#[test]
fn a_group_checked_alone_or_in_a_batch_gives_the_same_answers() {
    let alone: Vec<Vec<_>> = (0..item_groups().len())
        .map(|k| {
            std::thread::spawn(move || {
                let types = named(item_groups().swap_remove(k)).instance(vec![]);
                types.iter().map(answers).collect()
            })
            .join()
            .unwrap()
        })
        .collect();
    Type::forget_emptiness();
    for round in 0..2 {
        for (k, bodies) in item_groups().into_iter().enumerate().rev() {
            let types = named(bodies).instance(vec![]);
            let mut got: Vec<_> = types.iter().rev().map(answers).collect();
            got.reverse();
            assert_eq!(got, alone[k], "group {k}, round {round}");
        }
    }
}
