//! The forms of types, compared by structure (row FAIL-fold-rotating-tuple-rounds): a type's
//! tree of unions, tuples, payload shapes, functions and arrows, with each node's labels, and
//! either the leaves' scalars, atoms and variables (the type's canonical form) or only the
//! number of variables at each leaf (its skeleton). The checker's fold (`fold_dir_end` in
//! crates/zedc-check/src/check/walk.rs) reads these to end its rounds by a proved argument,
//! without a cap on their number: the argument is written there, every step, and uses the
//! facts proved here at each function.
//!
//! Each form is interned in a [`Forms`] arena: two forms are equal exactly when their ids
//! are, and a form shared by many paths of a type is built once. A node is interned after
//! its children, so each child's id is less than its parent's; [`Forms::embeds`] relies on
//! this to decide pairs in order of id, with no recursion.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::types::Type as KType;

use crate::ty::{Arrow, Dense, Row, Shape, Sig, Ty, WrittenRange};

/// A form in a [`Forms`] arena.
pub type FormId = u32;

/// The number of decimal characters of each end of an int range, `None` where the end is
/// open: a label of a function or family node. Two such labels compare end by end, `None`
/// only with `None` and a count with a count by `<=`.
type Ends = Option<[Option<u64>; 2]>;

/// What one node of a form is, beside its children.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Kind {
    /// A union of two or more distinct forms, its children sorted by id. A union of one form
    /// is that form, so no node is a union of one; and no child of a union is a union, since
    /// a type's parts (its leaf, payloads, rows and functions) are none of them unions.
    Union,
    /// The scalars, atoms, variables and unknown of a type, outside its tuples, payloads and
    /// functions: the number of its variables, and in a canonical form its [`Leaf`]
    /// (`None` in a skeleton).
    Leaf { vars: u64, label: Option<Leaf> },
    /// A tuple shape; its children are its components, in order.
    Tuple,
    /// The payload shapes of the atoms of one name, which is the label; `false` where they are
    /// not known. Its children are the shapes.
    Payload(Arc<str>, bool),
    /// A payload shape; its children are its items, then its fields in name order, whose names
    /// are the label.
    Shape(Vec<Arc<str>>),
    /// A function or family; its children are its arrows.
    Fn {
        data: bool,
        dense: u8,
        word: Option<Arc<str>>,
        positional: Vec<bool>,
        keys: Ends,
        hull: Ends,
    },
    /// An arrow; its children are its parameters' types, then its result.
    Arrow {
        partial: bool,
        stores_not_found: bool,
    },
}

/// The leaf of a canonical form: the carriers its scalars meet, as bits in the order of
/// [`zed_kernel::types::Split::bases`]; the names of its atoms, each with whether it holds the
/// bare atom, `None` where it holds every name it does not list; the same for its atoms that
/// are members of a named atom family; whether its kernel set holds tuples, structs or
/// morphisms (the kind-wide part); whether it holds the unknown; and its variables, each as
/// the place of its first appearance in the walk that built the form.
///
/// For one program and one skeleton, finitely many leaves can stand at a skeleton leaf of `k`
/// variables: six carrier bits; atom names from a finite set, since every atom a type holds is
/// made from a written name (each `KType::atom` in zedc-check and zedc-types outside tests
/// takes the name of an `ExprKind::Atom`, a `TypeKind::Atom`, a declared atom family or a
/// handle: checked by reading those sites, 2026-11-20); two bits; and `k` places, each less
/// than the number of variables of the whole form, which is at most the sum of `k` over the
/// skeleton's leaves.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Leaf {
    carriers: u8,
    atoms: Option<Vec<(Arc<str>, bool)>>,
    family: Option<Vec<(Arc<str>, bool)>>,
    wide: bool,
    dynamic: bool,
    vars: Vec<u32>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Node {
    kind: Kind,
    kids: Vec<FormId>,
}

/// The arena of forms. Ids are given in the order forms are first made.
#[derive(Default)]
pub struct Forms {
    nodes: Vec<Node>,
    depth: Vec<u64>,
    width: Vec<u64>,
    ids: HashMap<Node, FormId>,
    embeds: HashMap<(FormId, FormId), bool>,
}

/// One step of the walk of [`Forms::of`]: a part to enter, or a node to make from the last
/// forms on the stack of results once its children are made.
enum Step<'t> {
    Ty(&'t Ty),
    Row(&'t Row),
    Shape(&'t Shape),
    Payload(&'t Arc<str>, &'t Option<Vec<Shape>>),
    Sig(&'t Arc<Sig>),
    Arrow(&'t Arrow),
    MakeUnion(usize),
    MakeRow(&'t Row),
    MakeShape(&'t Shape),
    MakePayload(&'t Arc<str>, bool, usize),
    MakeSig(&'t Arc<Sig>),
    MakeArrow(&'t Arrow),
}

impl Forms {
    /// An empty arena.
    pub fn new() -> Forms {
        Forms::default()
    }

    /// The form of `t`: its canonical form where `leaves`, else its skeleton. The skeleton of
    /// a type is a function of its canonical form (each leaf's label erased and its number
    /// of variables kept, then equal children of a union merged), so two types of one
    /// canonical form have one skeleton.
    // Complexity tradeoff: each row, shape and function is entered once per call, by address
    // (the walked type keeps them alive during the call, so no address is reused within it),
    // so the cost is linear in the type's distinct nodes, however many paths share them; the
    // naive walk of the type as a tree is exponential in its depth where rows are shared
    // (`(r, r)` with `r = (s, s)`, ...). Given up: three address maps per call. The walk keeps
    // its own stack, as the checker's walks of types do, since a type nests as deep as the
    // program; it enters parts in the order a recursive walk would, so the places of the
    // variables are those of that order.
    pub fn of(&mut self, t: &Ty, leaves: bool) -> FormId {
        let mut vars: HashMap<Arc<str>, u32> = HashMap::new();
        let mut rows: HashMap<*const (), FormId> = HashMap::new();
        let mut shapes: HashMap<*const (), FormId> = HashMap::new();
        let mut sigs: HashMap<*const Sig, FormId> = HashMap::new();
        let mut made: Vec<FormId> = Vec::new();
        let mut todo = vec![Step::Ty(t)];
        while let Some(step) = todo.pop() {
            match step {
                Step::Ty(t) => {
                    let has_leaf = !t.set.is_empty() || t.dynamic || !t.vars.is_empty();
                    if has_leaf {
                        let label = leaves.then(|| leaf(t, &mut vars));
                        let vars = t.vars.iter().count() as u64;
                        made.push(self.intern(Node {
                            kind: Kind::Leaf { vars, label },
                            kids: Vec::new(),
                        }));
                    }
                    let mut parts = Vec::new();
                    parts.extend(t.payloads.iter().map(|(n, s)| Step::Payload(n, s)));
                    parts.extend(t.tuples.iter().map(Step::Row));
                    parts.extend(t.fns.iter().map(Step::Sig));
                    todo.push(Step::MakeUnion(parts.len() + usize::from(has_leaf)));
                    todo.extend(parts.into_iter().rev());
                }
                Step::Row(r) => match rows.get(&r.addr()) {
                    Some(&id) => made.push(id),
                    None => {
                        todo.push(Step::MakeRow(r));
                        todo.extend(r.iter().rev().map(Step::Ty));
                    }
                },
                Step::Shape(s) => match shapes.get(&s.as_ptr().cast::<()>()) {
                    Some(&id) => made.push(id),
                    None => {
                        todo.push(Step::MakeShape(s));
                        todo.extend(s.fields.values().rev().map(Step::Ty));
                        todo.extend(s.items.iter().rev().map(Step::Ty));
                    }
                },
                Step::Payload(name, shapes) => {
                    let n = shapes.iter().flatten().count();
                    todo.push(Step::MakePayload(name, shapes.is_some(), n));
                    todo.extend(shapes.iter().flatten().rev().map(Step::Shape));
                }
                Step::Sig(s) => match sigs.get(&Arc::as_ptr(s)) {
                    Some(&id) => made.push(id),
                    None => {
                        todo.push(Step::MakeSig(s));
                        todo.extend(s.arrows.iter().rev().map(Step::Arrow));
                    }
                },
                Step::Arrow(a) => {
                    todo.push(Step::MakeArrow(a));
                    todo.push(Step::Ty(&a.result));
                    todo.extend(a.params.iter().rev().map(Step::Ty));
                }
                Step::MakeUnion(n) => {
                    let kids = made.split_off(made.len() - n);
                    let id = self.union(kids);
                    made.push(id);
                }
                Step::MakeRow(r) => {
                    let kids = made.split_off(made.len() - r.len());
                    let id = self.intern(Node {
                        kind: Kind::Tuple,
                        kids,
                    });
                    rows.insert(r.addr(), id);
                    made.push(id);
                }
                Step::MakeShape(s) => {
                    let kids = made.split_off(made.len() - s.items.len() - s.fields.len());
                    let id = self.intern(Node {
                        kind: Kind::Shape(s.fields.keys().cloned().collect()),
                        kids,
                    });
                    shapes.insert(s.as_ptr().cast::<()>(), id);
                    made.push(id);
                }
                Step::MakePayload(name, known, n) => {
                    let kids = made.split_off(made.len() - n);
                    made.push(self.intern(Node {
                        kind: Kind::Payload(name.clone(), known),
                        kids,
                    }));
                }
                Step::MakeArrow(a) => {
                    let kids = made.split_off(made.len() - a.params.len() - 1);
                    made.push(self.intern(Node {
                        kind: Kind::Arrow {
                            partial: a.partial,
                            stores_not_found: a.stores_not_found,
                        },
                        kids,
                    }));
                }
                Step::MakeSig(s) => {
                    let kids = made.split_off(made.len() - s.arrows.len());
                    let id = self.intern(Node {
                        kind: Kind::Fn {
                            data: s.data,
                            dense: match s.dense {
                                Dense::No => 0,
                                Dense::Interval => 1,
                                Dense::Ranks => 2,
                            },
                            word: s.word.clone(),
                            positional: s.params.iter().map(|p| p.positional).collect(),
                            keys: ends(&s.keys),
                            hull: ends(&s.hull),
                        },
                        kids,
                    });
                    sigs.insert(Arc::as_ptr(s), id);
                    made.push(id);
                }
            }
        }
        debug_assert_eq!(made.len(), 1, "the walk makes one form");
        made[0]
    }

    /// The depth of a form: 0 for a leaf; one more than its deepest child for a tuple, payload,
    /// shape, function or arrow (1 for one with no children); and its deepest child's for a
    /// union, which nests nothing.
    pub fn depth(&self, f: FormId) -> u64 {
        self.depth[f as usize]
    }

    /// The width of a form: the most, over its nodes but its unions, of the node's children,
    /// a leaf's variables, a function's parameters, and the decimal characters of an end of a
    /// function's keys or hull. A union's children are not counted: they are distinct forms
    /// of no greater depth and width, so their number is bounded by the number of such forms.
    pub fn width(&self, f: FormId) -> u64 {
        self.width[f as usize]
    }

    /// Whether `a` embeds in `b` homeomorphically, in the ordered form (the children of a node
    /// kept in their order): `a` is `b`; or `a` embeds in a child of `b` (diving); or `a` and
    /// `b` are nodes of one kind whose labels fit (`labels_fit`) and whose children
    /// embed one by one, in order, in a subsequence of `b`'s (coupling). This is the
    /// embedding of Kruskal's tree theorem (Kruskal 1960, "Well-quasi-ordering, the tree
    /// theorem, and Vazsonyi's conjecture", Trans. AMS 95, DOI 10.2307/1993287): over finite
    /// trees whose labels are well-quasi-ordered, every infinite sequence has an earlier tree
    /// that embeds in a later one. Here the labels are a finite set under equality, times
    /// tuples of counts under `<=` count by count, which are well-quasi-ordered by Dickson's
    /// lemma; for ordered trees the theorem follows by the minimal-bad-sequence argument of
    /// Nash-Williams 1963 ("On well-quasi-ordering finite trees", Proc. Cambridge Philos. Soc.
    /// 59, DOI 10.1017/S0305004100003844), with Higman's lemma for the sequences of children
    /// (Higman 1952, "Ordering by divisibility in abstract algebras", Proc. London Math. Soc.
    /// s3-2, DOI 10.1112/plms/s3-2.1.326). The titles and DOIs were checked on Crossref on
    /// 2026-11-20; the theorems' proofs are those papers', not repeated here. Its use as a
    /// test that a run may not end is Leuschel's ("On the power of homeomorphic embedding for
    /// online termination", SAS 1998, DOI 10.1007/3-540-49727-7_14). Tested by the unit tests
    /// at the end of this file.
    ///
    /// Two facts the fold's argument uses, each proved by induction on `b`: if `a` embeds in
    /// `b`, then `depth(a) <= depth(b)` and `width(a) <= width(b)`. Where `a` is `b`, both
    /// hold. Diving: `a` embeds in a child `c` of `b`, so by induction `depth(a) <= depth(c)`
    /// and `width(a) <= width(c)`, and `depth(c) <= depth(b)` and `width(c) <= width(b)` by
    /// the definitions. Coupling: the kinds agree, so `a` is a union exactly where `b` is;
    /// each child of `a` embeds in a distinct child of `b`, so by induction `a`'s deepest and
    /// widest children are no deeper or wider than some child of `b`; and `a` has no more
    /// children than `b`, and its counted labels (a leaf's variables, a function's parameters,
    /// which are equal, and its ends) are no greater than `b`'s.
    // Complexity tradeoff: the pairs of sub-forms of `a` and of `b` are decided in order of
    // `b`'s then `a`'s id, children first, and each answer is kept for later calls, so a
    // pair is decided once: O(|a| |b|) pairs, each with O(children of a + children of b)
    // work, and no recursion. The match of children takes each child of `a` to the first
    // child of `b`, after the last one taken, that it embeds in, which finds a subsequence
    // where one exists (exchange argument: any match can move each child's partner to the
    // greedy one, which is no later). The naive search over subsequences is exponential in
    // the number of children.
    pub fn embeds(&mut self, a: FormId, b: FormId) -> bool {
        let below_a = self.below(a);
        let below_b = self.below(b);
        for &y in &below_b {
            for &x in &below_a {
                if x == y || self.embeds.contains_key(&(x, y)) {
                    continue;
                }
                let kb = &self.nodes[y as usize].kids;
                let mut r = kb.iter().any(|&c| self.decided(x, c));
                if !r && self.labels_fit(x, y) {
                    let mut j = 0;
                    r = self.nodes[x as usize].kids.iter().all(|&c| {
                        while j < kb.len() {
                            j += 1;
                            if self.decided(c, kb[j - 1]) {
                                return true;
                            }
                        }
                        false
                    });
                }
                self.embeds.insert((x, y), r);
            }
        }
        self.decided(a, b)
    }

    /// The answer for a pair already decided, children before parents ([`Forms::embeds`]).
    fn decided(&self, x: FormId, y: FormId) -> bool {
        x == y || self.embeds[&(x, y)]
    }

    /// The sub-forms of `f`, itself among them, in increasing id, so each child before its
    /// parent.
    fn below(&self, f: FormId) -> Vec<FormId> {
        let mut seen = HashSet::from([f]);
        let mut todo = vec![f];
        while let Some(n) = todo.pop() {
            for &k in &self.nodes[n as usize].kids {
                if seen.insert(k) {
                    todo.push(k);
                }
            }
        }
        let mut all: Vec<FormId> = seen.into_iter().collect();
        all.sort_unstable();
        all
    }

    /// Whether the labels of `a` and `b` let `a` couple with `b` ([`Forms::embeds`]): equal,
    /// but a leaf's variables and a function's key and hull ends compare by `<=`.
    fn labels_fit(&self, a: FormId, b: FormId) -> bool {
        let fit = |x: &Ends, y: &Ends| match (x, y) {
            (None, None) => true,
            (Some(x), Some(y)) => x.iter().zip(y).all(|e| match e {
                (None, None) => true,
                (Some(p), Some(q)) => p <= q,
                _ => false,
            }),
            _ => false,
        };
        match (&self.nodes[a as usize].kind, &self.nodes[b as usize].kind) {
            (Kind::Leaf { vars: v, label: l }, Kind::Leaf { vars: w, label: m }) => {
                v <= w && l == m
            }
            (
                Kind::Fn {
                    data,
                    dense,
                    word,
                    positional,
                    keys,
                    hull,
                },
                Kind::Fn {
                    data: d,
                    dense: e,
                    word: w,
                    positional: p,
                    keys: k,
                    hull: h,
                },
            ) => (data, dense, word, positional) == (d, e, w, p) && fit(keys, k) && fit(hull, h),
            (x, y) => x == y,
        }
    }

    /// The id of `node`, made once, with its depth and width.
    fn intern(&mut self, node: Node) -> FormId {
        if let Some(&id) = self.ids.get(&node) {
            return id;
        }
        let id = FormId::try_from(self.nodes.len()).expect("fewer than 2^32 forms");
        let kids_depth = node.kids.iter().map(|&k| self.depth(k)).max();
        let kids_width = node.kids.iter().map(|&k| self.width(k)).max().unwrap_or(0);
        let nested = kids_depth.map_or(1, |d| d + 1);
        let (depth, own) = match &node.kind {
            Kind::Union => (kids_depth.unwrap_or(0), 0),
            Kind::Leaf { vars, .. } => (0, *vars),
            Kind::Fn {
                keys,
                hull,
                positional,
                ..
            } => {
                let ends = [keys, hull].into_iter().flatten().flatten().flatten();
                let most = ends.copied().max().unwrap_or(0);
                let n = node.kids.len().max(positional.len()) as u64;
                (nested, most.max(n))
            }
            _ => (nested, node.kids.len() as u64),
        };
        self.nodes.push(node.clone());
        self.depth.push(depth);
        self.width.push(own.max(kids_width));
        self.ids.insert(node, id);
        id
    }

    /// The union of `kids`: sorted by id with repeats dropped, and the one form where only one
    /// is left.
    fn union(&mut self, mut kids: Vec<FormId>) -> FormId {
        kids.sort_unstable();
        kids.dedup();
        match kids.as_slice() {
            [one] => *one,
            _ => self.intern(Node {
                kind: Kind::Union,
                kids,
            }),
        }
    }
}

/// The canonical label of `t`'s leaf, its variables numbered by `vars` in order of first
/// appearance.
fn leaf(t: &Ty, vars: &mut HashMap<Arc<str>, u32>) -> Leaf {
    let split = t.set.split();
    let carriers = (split.bases.iter().enumerate())
        .filter(|(_, b)| b.is_some())
        .fold(0, |m, (i, _)| m | 1 << i);
    let names = |k: &KType| {
        k.atom_names()
            .map(|ns| ns.map(|(n, bare)| (Arc::from(n), bare)).collect())
    };
    let places = (t.vars.iter())
        .map(|v| {
            let n = vars.len() as u32;
            *vars.entry(v.clone()).or_insert(n)
        })
        .collect();
    Leaf {
        carriers,
        atoms: split.atoms.as_ref().map_or(Some(Vec::new()), names),
        family: names(&t.family),
        wide: split.rest.is_some(),
        dynamic: t.dynamic,
        vars: places,
    }
}

/// The [`Ends`] of a written range.
fn ends(r: &Option<WrittenRange>) -> Ends {
    let n = |v: &Option<Value>| v.as_ref().map(|v| v.to_string().len() as u64);
    r.as_ref().map(|r| [n(&r.low), n(&r.high)])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::Carrier;

    fn tuple(parts: &[Ty]) -> Ty {
        Ty::tuple(parts.to_vec())
    }

    /// A rotation's results, `(f64, int)` then `(int, f64)`, have one skeleton and two
    /// canonical forms; their union has that skeleton too.
    #[test]
    fn a_rotated_tuple_keeps_its_skeleton_and_changes_its_canonical_form() {
        let (i, f) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::F64));
        let mut forms = Forms::new();
        let (a, b) = (
            tuple(&[f.clone(), i.clone()]),
            tuple(&[i.clone(), f.clone()]),
        );
        assert_eq!(forms.of(&a, false), forms.of(&b, false));
        assert_ne!(forms.of(&a, true), forms.of(&b, true));
        assert_eq!(forms.of(&a.union(&b), false), forms.of(&a, false));
        let s = forms.of(&a, false);
        assert_eq!((forms.depth(s), forms.width(s)), (1, 2));
    }

    /// A tuple nested in itself embeds the smaller in the larger and is deeper; a wider tuple
    /// embeds a narrower one and is wider; neither embeds in the other the other way.
    #[test]
    fn nesting_and_widening_embed_and_grow() {
        let i = Ty::carrier(Carrier::Int);
        let mut forms = Forms::new();
        let one = tuple(&[i.clone(), i.clone()]);
        let nested = tuple(&[one.union(&i), i.clone()]);
        let wide = tuple(&[i.clone(), i.clone(), i.clone()]);
        let (s1, s2, s3) = (
            forms.of(&one, false),
            forms.of(&nested, false),
            forms.of(&wide, false),
        );
        assert!(forms.embeds(s1, s2) && !forms.embeds(s2, s1));
        assert!(forms.depth(s2) > forms.depth(s1));
        assert!(forms.embeds(s1, s3) && !forms.embeds(s3, s1));
        assert!(forms.width(s3) > forms.width(s1));
        assert!(!forms.embeds(s2, s3) && !forms.embeds(s3, s2));
    }

    /// Embedding keeps the children's order: `(int, (int,))` does not embed in
    /// `((int,), int)`, though each part of one is a part of the other.
    #[test]
    fn embedding_keeps_the_order_of_parts() {
        let i = Ty::carrier(Carrier::Int);
        let mut forms = Forms::new();
        let inner = tuple(std::slice::from_ref(&i));
        let a = forms.of(&tuple(&[i.clone(), inner.clone()]), false);
        let b = forms.of(&tuple(&[inner, i]), false);
        assert!(!forms.embeds(a, b) && !forms.embeds(b, a));
    }

    /// A type nested a hundred thousand levels deep is walked and compared without running
    /// out of stack: both walks keep their own.
    #[test]
    fn a_deep_type_is_walked_without_recursion() {
        let mut t = Ty::carrier(Carrier::Int);
        for _ in 0..100_000 {
            t = tuple(&[t]);
        }
        let mut forms = Forms::new();
        let s = forms.of(&t, false);
        assert_eq!(forms.depth(s), 100_000);
        let one = forms.of(&tuple(&[Ty::carrier(Carrier::Int)]), false);
        assert!(forms.embeds(one, s));
    }
}
