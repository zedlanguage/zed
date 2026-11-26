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
use zed_kernel::types::{Split, Type as KType};

use crate::ty::{Arrow, Dense, Row, Shape, Sig, Ty, WrittenRange};

/// A form in a [`Forms`] arena.
pub type FormId = u32;

/// The top-level constructor kind of a non-union form, used to partition skeletons into finitely
/// many groups before checking homeomorphic embedding: a finite partition of a well-quasi-order
/// is still a well-quasi-order (pigeonhole principle), so comparing only non-union pieces that
/// share a root tag still proves termination while avoiding false refusals when a fold
/// transitions once between distinct constructors (e.g. scalar to tuple, or `#ok` to `#err`).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum RootTag {
    /// A scalar/atom/variable/unknown leaf.
    Leaf,
    /// A tuple row.
    Tuple,
    /// An atom payload group, tagged by atom name.
    Payload(Arc<str>),
    /// A function (`false`) or data family (`true`).
    Fn(bool),
    /// Any other node kind (never top-level for a `Ty`).
    Other,
}

/// The number of decimal characters of each end of an int range, `None` where the end is
/// open: a label of a function or family node. Two such labels compare end by end, `None`
/// only with `None` and a count with a count by `<=`.
type Ends = Option<[Option<u64>; 2]>;

/// Exact printed ends of a written range, stored only on canonical forms so that distinct
/// ranges of the same digit length (such as `0 ..= 0`, `0 ..= 1`, `0 ..= 2`) get distinct
/// canonical forms while still lying in a finite set once `width` bounds the digit length.
type ExactEnds = Option<[Option<Arc<str>>; 2]>;

/// What one node of a form is, beside its children.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Kind {
    /// A union of zero or of two or more distinct forms, its children sorted by id (zero only
    /// for [`Ty::empty`]). A union of one form is that form, so no node is a union of one; and
    /// no child of a union is a union, since a type's parts (its leaf, payloads, rows and
    /// functions) are none of them unions.
    Union,
    /// The scalars, atoms, variables and unknown of a type, outside its tuples, payloads and
    /// functions: the count of its fresh variables (not in the pre-fold known set); the
    /// greatest length of the texts its [`Leaf`] prints in full (`leaf_texts`: its atoms where
    /// one carries a payload, and its kind-wide part) and of the literals of its narrowed
    /// scalars inside a function or family, where [`Ty::carriers`] does not widen them
    /// (`KType::scalar_literal_width`); and in a canonical form its [`Leaf`] (`None` in a
    /// skeleton).
    Leaf {
        vars: u64,
        text_len: u64,
        label: Option<Leaf>,
    },
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
        exact_ends: Option<(ExactEnds, ExactEnds)>,
    },
    /// An arrow; its children are its parameters' types, then its result.
    Arrow {
        partial: bool,
        stores_not_found: bool,
    },
}

/// The leaf of a canonical form: the carriers its scalars meet, as bits in the order of
/// [`zed_kernel::types::Split::bases`]; inside a function or family, each narrowed scalar base
/// exactly, tagged by its place (whole carriers are already told by the carrier bits); the
/// texts `leaf_texts` prints in full (its atoms where one carries a payload or the set lists
/// the names it leaves out; its kind-wide part of tuples, structs and morphisms);
/// the names of its atoms, each with whether it holds the bare atom, `None` where it holds
/// every name it does not list; the same for its atoms that are members of a named atom
/// family; whether it holds the unknown; its known (pre-fold) variables by name; and its fresh
/// variables, each as the place of its first appearance in the walk that built the form.
///
/// For one program, a fixed finite set of pre-fold known variables `K` (variables in `known_vars`
/// plus canonical class variables `$0..$(known_classes - 1)`), a bound `W` on width,
/// and a bound `V` on the total count of distinct fresh variables across the whole type,
/// finitely many canonical leaves can stand at a skeleton leaf: six carrier bits; at most six
/// narrowed scalar bases, each a finite or cofinite set of literals whose texts are at most
/// `W` bytes long (that length counts toward `text_len`), so one of finitely many sets
/// (`KType::scalar_literal_width`); at most 2 texts (the atoms, the kind-wide part), each a
/// UTF-8 string of byte length at most `W`, since that length is the leaf's `text_len` and so
/// at most its width (finitely many strings of bounded length); atom names from a finite set
/// fixed by the program and compiler (every `KType::atom` outside tests takes either a name
/// written in the program — an `ExprKind::Atom`, `TypeKind::Atom`, declared atom family, or
/// handle — or one of the thirteen compiler-fixed names `notFound`, `outOfBounds`, `empty`,
/// `divByZero`, `badUtf8`, `none`, `emptySeparator`, `ioError`, `errs`, plus `NaN`,
/// `overflow`, `invalid`, `notScalar` from `zed_kernel::Prim::arrows`; checked by reading all
/// sites, 2026-11-20), so
/// finitely many lists of them; one bit; a subset of the finite set `K`; and `k <= W`
/// fresh-variable places (the leaf's fresh count is at most its width), each less than `V`
/// (at most `V^k` choices).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Leaf {
    carriers: u8,
    scalars: Vec<(u8, KType)>,
    texts: Vec<(u8, Arc<str>)>,
    atoms: Option<Vec<(Arc<str>, bool)>>,
    family: Option<Vec<(Arc<str>, bool)>>,
    dynamic: bool,
    known: Vec<Arc<str>>,
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

    /// Collect every variable name appearing anywhere in `t`, walking each shared row, shape
    /// and signature once, without recursion.
    pub fn collect_vars(t: &Ty, out: &mut HashSet<Arc<str>>) {
        let mut rows: HashSet<*const ()> = HashSet::new();
        let mut shapes: HashSet<*const ()> = HashSet::new();
        let mut sigs: HashSet<*const Sig> = HashSet::new();
        enum Visit<'t> {
            Ty(&'t Ty),
            Row(&'t Row),
            Shape(&'t Shape),
            Sig(&'t Arc<Sig>),
        }
        let mut todo = vec![Visit::Ty(t)];
        while let Some(step) = todo.pop() {
            match step {
                Visit::Ty(t) => {
                    out.extend(t.vars.iter().cloned());
                    for shapes in t.payloads.values().flatten() {
                        todo.extend(shapes.iter().map(Visit::Shape));
                    }
                    todo.extend(t.tuples.iter().map(Visit::Row));
                    todo.extend(t.fns.iter().map(Visit::Sig));
                }
                Visit::Row(r) => {
                    if rows.insert(r.addr()) {
                        todo.extend(r.iter().map(Visit::Ty));
                    }
                }
                Visit::Shape(s) => {
                    if shapes.insert(s.as_ptr().cast::<()>()) {
                        todo.extend(s.fields.values().map(Visit::Ty));
                        todo.extend(s.items.iter().map(Visit::Ty));
                    }
                }
                Visit::Sig(s) => {
                    if sigs.insert(Arc::as_ptr(s)) {
                        for a in &s.arrows {
                            todo.push(Visit::Ty(&a.result));
                            todo.extend(a.params.iter().map(Visit::Ty));
                        }
                    }
                }
            }
        }
    }

    /// The form of `t` with no pre-fold known variables: its canonical form where `leaves`,
    /// else its skeleton. Convenience wrapper over [`Forms::of_in`].
    pub fn of(&mut self, t: &Ty, leaves: bool) -> FormId {
        self.of_in(t, leaves, &HashSet::new(), 0).0
    }

    /// The form of `t` relative to the finite set of variables already existing before the fold
    /// loop (`known_vars` together with canonical class variables `"$k"` for `k < known_classes`),
    /// paired with the count of distinct fresh variables (variables outside that set) occurring
    /// anywhere in `t`. The skeleton of a type is a function of its canonical form (each leaf's
    /// label and each function's exact ends erased, then equal children of a union merged), so
    /// two types of one canonical form have one skeleton and one fresh-variable count.
    // Complexity tradeoff: each row, shape and function is entered once per call (and once per
    // inside-function state for rows and shapes), by address (the walked type keeps them alive
    // during the call, so no address is reused within it), so the cost is linear in the type's
    // distinct nodes, however many paths share them; the naive walk of the type as a tree is
    // exponential in its depth where rows are shared (`(r, r)` with `r = (s, s)`, ...). Given
    // up: three address maps per call. The walk keeps its own stack, as the checker's walks of
    // types do, since a type nests as deep as the program; it enters parts in the order a
    // recursive walk would, so the places of the fresh variables are those of that order.
    pub fn of_in(
        &mut self,
        t: &Ty,
        leaves: bool,
        known_vars: &HashSet<Arc<str>>,
        known_classes: usize,
    ) -> (FormId, u64) {
        let mut vars: HashMap<Arc<str>, u32> = HashMap::new();
        let mut rows: HashMap<(*const (), bool), FormId> = HashMap::new();
        let mut shapes: HashMap<(*const (), bool), FormId> = HashMap::new();
        let mut sigs: HashMap<*const Sig, FormId> = HashMap::new();
        let mut made: Vec<FormId> = Vec::new();
        let mut todo = vec![Step::Ty(t)];
        let mut in_fn: usize = 0;
        while let Some(step) = todo.pop() {
            match step {
                Step::Ty(t) => {
                    let has_leaf = !t.set.is_empty() || t.dynamic || !t.vars.is_empty();
                    if has_leaf {
                        let (fresh, text_len, label) =
                            leaf_node(t, leaves, in_fn > 0, known_vars, known_classes, &mut vars);
                        made.push(self.intern(Node {
                            kind: Kind::Leaf {
                                vars: fresh,
                                text_len,
                                label,
                            },
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
                Step::Row(r) => match rows.get(&(r.addr(), in_fn > 0)) {
                    Some(&id) => made.push(id),
                    None => {
                        todo.push(Step::MakeRow(r));
                        todo.extend(r.iter().rev().map(Step::Ty));
                    }
                },
                Step::Shape(s) => match shapes.get(&(s.as_ptr().cast::<()>(), in_fn > 0)) {
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
                        in_fn += 1;
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
                    rows.insert((r.addr(), in_fn > 0), id);
                    made.push(id);
                }
                Step::MakeShape(s) => {
                    let kids = made.split_off(made.len() - s.items.len() - s.fields.len());
                    let id = self.intern(Node {
                        kind: Kind::Shape(s.fields.keys().cloned().collect()),
                        kids,
                    });
                    shapes.insert((s.as_ptr().cast::<()>(), in_fn > 0), id);
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
                    in_fn -= 1;
                    let kids = made.split_off(made.len() - s.arrows.len());
                    let exact_ends = leaves.then(|| (exact_ends(&s.keys), exact_ends(&s.hull)));
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
                            exact_ends,
                        },
                        kids,
                    });
                    sigs.insert(Arc::as_ptr(s), id);
                    made.push(id);
                }
            }
        }
        debug_assert_eq!(made.len(), 1, "the walk makes one form");
        (made[0], vars.len() as u64)
    }

    /// The top-level non-union pieces of `f`: its children if `f` is a union (empty for
    /// [`Ty::empty`]), else `f` alone.
    pub fn pieces<'a>(&'a self, f: &'a FormId) -> &'a [FormId] {
        match &self.nodes[*f as usize].kind {
            Kind::Union => &self.nodes[*f as usize].kids,
            _ => std::slice::from_ref(f),
        }
    }

    /// The top-level constructor tag of a non-union form `f` ([`RootTag`]).
    pub fn root_tag(&self, f: FormId) -> RootTag {
        match &self.nodes[f as usize].kind {
            Kind::Leaf { .. } => RootTag::Leaf,
            Kind::Tuple => RootTag::Tuple,
            Kind::Payload(name, _) => RootTag::Payload(name.clone()),
            Kind::Fn { data, .. } => RootTag::Fn(*data),
            _ => RootTag::Other,
        }
    }

    /// The depth of a form: 0 for a leaf; one more than its deepest child for a tuple, payload,
    /// shape, function or arrow (1 for one with no children); and its deepest child's for a
    /// union, which nests nothing.
    pub fn depth(&self, f: FormId) -> u64 {
        self.depth[f as usize]
    }

    /// The width of a form: the most, over its nodes but its unions, of the node's children,
    /// a leaf's fresh variables and the greatest byte length of its texts (`leaf_texts`), a
    /// function's parameters, and the decimal characters of an end of a function's keys or
    /// hull. A union's children are not counted: they are distinct forms of no greater depth
    /// and width, so their number is bounded by the number of such forms.
    pub fn width(&self, f: FormId) -> u64 {
        self.width[f as usize]
    }

    /// Whether `a` embeds in `b` homeomorphically, in the ordered form (the children of a node
    /// kept in their order): `a` is `b`; or `a` embeds in a child of `b` (diving); or `a` and
    /// `b` are nodes of one kind whose labels fit (`labels_fit`) and whose children
    /// embed one by one, in order, in a subsequence of `b`'s (coupling).
    ///
    /// On skeletons (`leaves == false`) drawn from a fixed program and prelude, this is the
    /// embedding of Kruskal's tree theorem for structured (ordered) labeled trees
    /// (Kruskal 1960, "Well-quasi-ordering, the tree theorem, and Vazsonyi's conjecture",
    /// Trans. AMS 95(2), pp. 210-225, DOI 10.2307/1993287, the unnumbered "Tree Theorem",
    /// p. 212: "X wqo implies T(X) wqo", where T(X) is the set of finite trees with a root,
    /// edges pointing away from it and the edges above each vertex linearly ordered, and an
    /// embedding maps the edges at a vertex to paths "in a manner which is strictly
    /// order-preserving", with labels compared in X, any quasi-order). The same statement in
    /// the term form used here, children coupled to a subsequence of children and a node
    /// allowed to map below its image, is Gallier 1991, "What's so special about Kruskal's
    /// theorem and the ordinal Γ0?", Ann. Pure Appl. Logic 53, pp. 199-260, DOI
    /// 10.1016/0168-0072(91)90022-E, Definition 4.4 (its rules (2) diving and (3) coupling)
    /// and Theorem 4.5, p. 207: "If ⊑ is a wqo on Σ, then ≤ is a wqo on T_Σ". The short
    /// minimal-bad-sequence proof is Nash-Williams 1963 ("On well-quasi-ordering finite
    /// trees", Proc. Cambridge Philos. Soc. 59(4), pp. 833-835, DOI
    /// 10.1017/S0305004100003844), whose Theorem 1, p. 833, is for unlabeled, unordered trees;
    /// its p. 835 notes the proof adapts to Kruskal's labeled, ordered theorem. Children are
    /// sequences, compared by Higman's lemma (Higman 1952, "Ordering by divisibility in
    /// abstract algebras", Proc. London Math. Soc. s3-2(1), pp. 326-336, DOI
    /// 10.1112/plms/s3-2.1.326, Theorem 4.3, p. 332: "If A has the f.b.p., so has V(A)", V(A)
    /// the finite sequences over A, x ≤ y when x is majorized by a subsequence of y; the
    /// finite basis property is a wqo by its Theorem 2.1, p. 328). Here, on
    /// skeletons from one program and prelude, each node's label is an element of a finite set
    /// under equality (kind tag, atom/field/word names from the program and prelude) times a
    /// `Vec<bool>` (`Kind::Fn.positional`) ordered by Higman subsequence (WQO on the 2-element
    /// alphabet `{false, true}` by Higman 1952 Theorem 4.3, with no arity bound required) times
    /// a fixed-length tuple of natural-number counts under `<=` component by component (a leaf's
    /// `(vars, text_len)`, or a function's `keys`/`hull` end lengths), which is
    /// well-quasi-ordered by Dickson's lemma (Dickson 1913, "Finiteness of the odd perfect
    /// and primitive abundant numbers with n distinct prime factors", Amer. J. Math. 35(4),
    /// pp. 413-422, DOI 10.2307/2370405, Lemma A, p. 414: every set of monomials in n
    /// variables holds finitely many F_1, ..., F_k such that each member is a multiple of some
    /// F_i; so every subset of N^n under `<=` component by component has finitely many minimal
    /// elements, and N^n has no infinite antichain and no infinite strictly falling chain,
    /// which is a wqo). Note that on canonical forms (`leaves == true`), `Leaf.vars` and
    /// `exact_ends` are compared by equality, so `embeds` is used for well-quasi-ordering only
    /// on skeletons (`leaves == false`). Homeomorphic embedding as a stop test is Marlet 1994
    /// (thesis "Vers une formalisation de l'évaluation partielle", Université de Nice -
    /// Sophia Antipolis, section 6.2.4, Définition 6.3, "Critère de Higman-Kruskal") and
    /// Sørensen & Glück 1995 ("An algorithm of generalization in positive supercompilation",
    /// ILPS'95, MIT Press, pp. 465-479; no copy found, so cited only as Leuschel 1998 and
    /// Mogensen 2013, EPTCS 129, p. 32, describe it). Leuschel 1998 ("On the power of
    /// homeomorphic embedding for online termination", SAS 1998, LNCS 1503, pp. 230-245, DOI
    /// 10.1007/3-540-49727-7_14), Proposition 4, p. 238, with Example 3, p. 239: every
    /// sequence admissible under a monotonic well-founded order (its Definition 5) or a
    /// simplification ordering is admissible under homeomorphic embedding, and the inclusion
    /// is strict; it does not hold for every well-founded order (p. 239). All read in full
    /// text on 2026-11-20 except Sørensen & Glück. Tested by the unit tests at the end of
    /// this file.
    ///
    /// Two facts the fold's argument uses, each proved by induction on `b`: if `a` embeds in
    /// `b`, then `depth(a) <= depth(b)` and `width(a) <= width(b)`. Where `a` is `b`, both
    /// hold. Diving: `a` embeds in a child `c` of `b`, so by induction `depth(a) <= depth(c)`
    /// and `width(a) <= width(c)`, and `depth(c) <= depth(b)` and `width(c) <= width(b)` by
    /// the definitions. Coupling: the kinds agree, so `a` is a union exactly where `b` is;
    /// each child of `a` embeds in a distinct child of `b`, so `a` has no more children than
    /// `b`; if `a` has no children, `depth(a)` is 0 (for a union or leaf) or 1 (for a
    /// zero-child non-union), while `depth(b)` is at least 0 or 1 respectively, and if `a` has
    /// children, by induction `a`'s deepest and widest children are no deeper or wider than
    /// some child of `b`; and `a`'s counted labels (a leaf's `(vars, text_len)`, a
    /// function's `positional.len()` which is `<=` by subsequence order, and its `keys`/`hull`
    /// ends) are no greater than `b`'s.
    // Complexity tradeoff: the pairs of sub-forms of `a` and of `b` are decided in order of
    // `b`'s then `a`'s id, children first, and each answer is kept for later calls, so a
    // pair is decided once: O(|V_a| |V_b|) pairs, with total child-matching work
    // O(|V_a| |E_b| + |E_a| |V_b|) (O(|a| |b|) on trees where |E| < |V|), plus label
    // comparison, and no recursion. The match of children takes each child of `a` to the first
    // child of `b`, after the last one taken, that it embeds in, which finds a subsequence
    // where one exists (exchange argument: any match can move each child's partner to the
    // greedy one, which is no later). The naive search over subsequences is exponential in
    // the number of children.
    pub fn embeds(&mut self, a: FormId, b: FormId) -> bool {
        if a == b {
            return true;
        }
        if let Some(&r) = self.embeds.get(&(a, b)) {
            return r;
        }
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
    /// but a leaf's counts `(vars, text_len)` and a function's key and hull ends compare
    /// by `<=`.
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
        let fit_bools = |x: &[bool], y: &[bool]| {
            let mut j = 0;
            x.iter().all(|&b| {
                while j < y.len() {
                    j += 1;
                    if y[j - 1] == b {
                        return true;
                    }
                }
                false
            })
        };
        match (&self.nodes[a as usize].kind, &self.nodes[b as usize].kind) {
            (
                Kind::Leaf {
                    vars: v1,
                    text_len: l1,
                    label: m1,
                },
                Kind::Leaf {
                    vars: v2,
                    text_len: l2,
                    label: m2,
                },
            ) => v1 <= v2 && l1 <= l2 && m1 == m2,
            (
                Kind::Fn {
                    data,
                    dense,
                    word,
                    positional,
                    keys,
                    hull,
                    exact_ends,
                },
                Kind::Fn {
                    data: d,
                    dense: e,
                    word: w,
                    positional: p,
                    keys: k,
                    hull: h,
                    exact_ends: x,
                },
            ) => {
                (data, dense, word, exact_ends) == (d, e, w, x)
                    && fit_bools(positional, p)
                    && fit(keys, k)
                    && fit(hull, h)
            }
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
            Kind::Leaf { vars, text_len, .. } => (0, (*vars).max(*text_len)),
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
        zed_collections::sorted::sort_dedup(&mut kids);
        match kids.as_slice() {
            [one] => *one,
            _ => self.intern(Node {
                kind: Kind::Union,
                kids,
            }),
        }
    }
}

/// The parts of a leaf's kernel set that a canonical form records as printed text, each tagged
/// with its place (6 for the atoms, 7 for the kind-wide part, the numbers kept from when 0 to
/// 5 were the scalar bases), so that two parts that print alike stay apart. The narrowed
/// scalar bases inside a function or family are kept as types in `Leaf.scalars` by
/// `leaf_node`, not printed: [`Ty::carriers`] does not widen scalars there (its doc: "at every
/// depth outside the functions it holds"), so a rotation of `(y: int) -> 0`, `(y: int) -> 1`,
/// ... would otherwise give one canonical form for distinct types (Gemini seat, round 1 of
/// FAIL-fold-rotating-tuple-rounds); and the length of a printed union `0 | 1000` grows with
/// its number of literals, so a map whose values gather a finite set of literals looked wider
/// each round (Codex seat, round 2, R2-3); its longest literal counts instead. The texts:
/// - the atoms, where one carries a payload in the kernel set (`KType::atom_with`) or the set
///   holds every name it does not list: the names and bare flags alone erase the payload
///   (Codex seat, round 1); a set of bare atoms only is told by its names, and is not printed,
///   so that its length does not count toward the width and an atom set that grows does not
///   look wider (the names come from a finite set, [`Leaf`]);
/// - the kind-wide part, which [`Ty::carriers`] keeps as it is.
///
/// The greatest length of these texts counts toward the leaf's width (`Kind::Leaf::text_len`),
/// so a bound on width bounds every text's length, and finitely many texts stand at a leaf of
/// bounded width (the argument at [`Leaf`]).
// Complexity tradeoff: printing each part is linear in its size; the naive record of a finite
// base, the list of its values (`values_listed`, Gemini's round-1 code), is linear in the
// number of values, which for `int[0..=10^9]` is 10^9. The bare-atom test builds the set of
// the bare atoms by `KType::union_all`, which adds the smaller set of literals to the larger,
// O(n log n) in the n names, and compares it with the atoms once; built one `|` at a time it
// could be O(n^2).
fn leaf_texts(split: &Split) -> Vec<(u8, Arc<str>)> {
    let mut texts: Vec<(u8, Arc<str>)> = Vec::new();
    if let Some(atoms) = &split.atoms {
        let bare_only = atoms.atom_names().is_some_and(|names| {
            let mut all_bare = true;
            let plain: Vec<KType> = names
                .map(|(n, bare)| {
                    all_bare &= bare;
                    KType::atom(n)
                })
                .collect();
            all_bare && *atoms == KType::union_all(plain)
        });
        if !bare_only {
            texts.push((6, Arc::from(atoms.to_string())));
        }
    }
    if let Some(rest) = &split.rest {
        texts.push((7, Arc::from(rest.to_string())));
    }
    texts
}

/// Whether `v` is in the finite set of pre-fold known variables: listed in `known_vars`, or a
/// canonical class variable `"$k"` with `k < known_classes` (strictly ASCII digits, no sign,
/// no leading zeros except `"$0"`, so at most `known_classes` strings satisfy the check).
fn is_known_var(v: &str, known_vars: &HashSet<Arc<str>>, known_classes: usize) -> bool {
    if known_vars.contains(v) {
        return true;
    }
    let Some(digits) = v.strip_prefix('$') else {
        return false;
    };
    let canonical = digits == "0"
        || (!digits.is_empty()
            && !digits.starts_with('0')
            && digits.bytes().all(|b| b.is_ascii_digit()));
    canonical && digits.parse::<usize>().is_ok_and(|k| k < known_classes)
}

/// The skeleton counts `(fresh_vars, text_len)` and optional canonical [`Leaf`] of `t`,
/// numbering fresh variables (those outside `known_vars` and `known_classes`) in `vars` by
/// first appearance. `text_len` is the greatest byte length of [`leaf_texts`], 0 where there
/// are none.
fn leaf_node(
    t: &Ty,
    keep_label: bool,
    in_fn: bool,
    known_vars: &HashSet<Arc<str>>,
    known_classes: usize,
    vars: &mut HashMap<Arc<str>, u32>,
) -> (u64, u64, Option<Leaf>) {
    let mut fresh_count = 0u64;
    let mut known = Vec::new();
    let mut places = Vec::new();
    for v in t.vars.iter() {
        if is_known_var(v, known_vars, known_classes) {
            if keep_label {
                known.push(v.clone());
            }
        } else {
            fresh_count += 1;
            let n = vars.len() as u32;
            let idx = *vars.entry(v.clone()).or_insert(n);
            if keep_label {
                places.push(idx);
            }
        }
    }
    let split = t.set.split();
    let texts = leaf_texts(&split);
    let mut text_len = texts.iter().map(|(_, s)| s.len() as u64).max().unwrap_or(0);
    // Inside a function or family each narrowed scalar base is kept exactly (`Leaf.scalars`)
    // and counts its longest literal toward the width, not the length of its printed union
    // (`KType::scalar_literal_width`, whose doc gives the finiteness argument).
    let mut scalars: Vec<(u8, KType)> = Vec::new();
    if in_fn {
        for (i, (base, whole)) in split.bases.iter().zip(&KType::scalars()).enumerate() {
            if let Some(b) = base
                && b != whole
            {
                text_len = text_len.max(b.scalar_literal_width());
                scalars.push((i as u8, b.clone()));
            }
        }
    }
    if !keep_label {
        return (fresh_count, text_len, None);
    }
    let carriers = (split.bases.iter().enumerate())
        .filter(|(_, b)| b.is_some())
        .fold(0, |m, (i, _)| m | 1 << i);
    let names = |k: &KType| {
        k.atom_names()
            .map(|ns| ns.map(|(n, bare)| (Arc::from(n), bare)).collect())
    };
    let label = Leaf {
        carriers,
        scalars,
        texts,
        atoms: split.atoms.as_ref().map_or(Some(Vec::new()), names),
        family: names(&t.family),
        dynamic: t.dynamic,
        known,
        vars: places,
    };
    (fresh_count, text_len, Some(label))
}

/// The [`Ends`] of a written range.
fn ends(r: &Option<WrittenRange>) -> Ends {
    let n = |v: &Option<Value>| v.as_ref().map(|v| v.to_string().len() as u64);
    r.as_ref().map(|r| [n(&r.low), n(&r.high)])
}

/// The [`ExactEnds`] of a written range.
fn exact_ends(r: &Option<WrittenRange>) -> ExactEnds {
    let s = |v: &Option<Value>| v.as_ref().map(|v| Arc::from(v.to_string()));
    r.as_ref().map(|r| [s(&r.low), s(&r.high)])
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

    /// Counterexample to the original Step 5 claim: `T_n = (v_1,) | ... | (v_n,)` collapses to
    /// one skeleton `(Leaf(1),)` for every `n`, yet yields `n` distinct canonical forms. Pairing
    /// the skeleton with `of_in`'s total fresh-variable count distinguishes every `n` and lets
    /// refusal (b) stop at `n = 2`.
    #[test]
    fn union_of_fresh_var_tuples_grows_total_fresh_vars() {
        let mut forms = Forms::new();
        let known = HashSet::new();
        let mut skels = Vec::new();
        let mut totals = Vec::new();
        let mut canons = Vec::new();
        let mut t = Ty::empty();
        for i in 0..4 {
            let v = Ty::var(Arc::from(format!("v{i}")));
            t = t.union(&tuple(&[v]));
            let (s, n) = forms.of_in(&t, false, &known, 0);
            let (c, cn) = forms.of_in(&t, true, &known, 0);
            assert_eq!(n, cn);
            skels.push(s);
            totals.push(n);
            canons.push(c);
        }
        assert!(skels.windows(2).all(|w| w[0] == w[1]));
        assert_eq!(totals, vec![1, 2, 3, 4]);
        let unique_canons: HashSet<FormId> = canons.into_iter().collect();
        assert_eq!(unique_canons.len(), 4);
    }

    /// Pre-fold known variables do not inflate skeleton width or fresh-variable counts, while
    /// canonical forms still distinguish which known variables appear at each leaf.
    #[test]
    fn known_vars_keep_skeleton_and_fresh_count_fixed() {
        let mut forms = Forms::new();
        let known: HashSet<Arc<str>> = ["y", "z", "w"].into_iter().map(Arc::from).collect();
        let (y, z, w) = (
            Ty::var(Arc::from("y")),
            Ty::var(Arc::from("z")),
            Ty::var(Arc::from("w")),
        );
        let r1 = tuple(&[z.clone(), y.union(&w)]);
        let r2 = tuple(&[y.union(&z).union(&w), y.union(&z).union(&w)]);
        let (s1, f1) = forms.of_in(&r1, false, &known, 0);
        let (s2, f2) = forms.of_in(&r2, false, &known, 0);
        assert_eq!((s1, f1), (s2, f2));
        assert_eq!((f1, forms.width(s1)), (0, 2));
        let (c1, _) = forms.of_in(&r1, true, &known, 0);
        let (c2, _) = forms.of_in(&r2, true, &known, 0);
        assert_ne!(c1, c2);
    }

    /// `Ty::empty()` is a zero-child union with depth 0, width 0, and zero top-level pieces,
    /// and embeds in any union.
    #[test]
    fn empty_type_has_zero_depth_width_and_no_pieces() {
        let mut forms = Forms::new();
        let e = forms.of(&Ty::empty(), false);
        assert_eq!((forms.depth(e), forms.width(e)), (0, 0));
        assert!(forms.pieces(&e).is_empty());
        let u = forms.of(
            &Ty::carrier(Carrier::Int).union(&tuple(&[Ty::carrier(Carrier::Int)])),
            false,
        );
        assert!(forms.embeds(e, u));
    }

    /// Inside a function or data family, distinct scalar literals of the same printed length
    /// share one skeleton and have distinct canonical forms; a longer literal increases width.
    /// A shared `Row` appearing both outside and inside a function is memoized per context.
    #[test]
    fn inside_function_literals_and_ranges_distinguish_canonical_forms() {
        use crate::ty::{Arrow, SParam, WrittenRange};
        let mut forms = Forms::new();
        let lit = |n: i64| Ty::set(KType::lit(&Value::Int(n)).unwrap());
        let pos = |name: &str| SParam {
            name: Arc::from(name),
            positional: true,
            default: None,
            range: None,
        };
        let make_arr = |k: i64, v: i64, hi: i64| {
            let mut s = Sig::one(vec![pos("k")], vec![lit(k)], lit(v));
            s.data = true;
            s.keys = Some(WrittenRange {
                low: Some(Value::Int(0)),
                high: Some(Value::Int(hi)),
                text: Arc::from(format!("int[0..={hi}]")),
            });
            Ty::func(Arc::new(s))
        };
        let a0 = make_arr(0, 0, 0);
        let a1 = make_arr(0, 1, 1);
        let a100 = make_arr(0, 100, 100);
        let s0 = forms.of(&a0, false);
        let s1 = forms.of(&a1, false);
        let s100 = forms.of(&a100, false);
        assert_eq!(s0, s1);
        // Each 1-parameter arrow has 2 children (param + result), so width starts at 2;
        // a 3-digit literal/range end raises width to 3.
        assert_eq!(forms.width(s0), 2);
        assert_eq!(forms.width(s100), 3);
        assert!(forms.embeds(s0, s100) && !forms.embeds(s100, s0));
        assert_ne!(forms.of(&a0, true), forms.of(&a1, true));

        // Same `Row` outside and inside a `Sig`: outside, its `10` has no text (its carrier
        // stands for it); inside, it is printed, `text_len = 2`.
        let row_ty = tuple(&[lit(10)]);
        let fn_of_row = Ty::func(Arc::new(Sig::of_arrow(
            vec![pos("x")],
            Arrow {
                params: vec![row_ty.clone()],
                result: row_ty.clone(),
                partial: false,
                stores_not_found: false,
            },
        )));
        let both = row_ty.union(&fn_of_row);
        let s = forms.of(&both, false);
        let pieces = forms.pieces(&s).to_vec();
        assert_eq!(pieces.len(), 2);
        let tags: HashSet<RootTag> = pieces.iter().map(|&p| forms.root_tag(p)).collect();
        assert!(tags.contains(&RootTag::Tuple));
        assert!(tags.contains(&RootTag::Fn(false)));

        // Higman subsequence order on `Fn.positional`: 1-param positional embeds in 2-param.
        let fn1 = Ty::func(Arc::new(Sig::one(
            vec![pos("a")],
            vec![Ty::carrier(Carrier::Int)],
            Ty::carrier(Carrier::Int),
        )));
        let fn2 = Ty::func(Arc::new(Sig::one(
            vec![pos("a"), pos("b")],
            vec![Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Int)],
            Ty::carrier(Carrier::Int),
        )));
        let sf1 = forms.of(&fn1, false);
        let sf2 = forms.of(&fn2, false);
        assert!(forms.embeds(sf1, sf2) && !forms.embeds(sf2, sf1));
        // Inside a function, whole carriers are told by `Leaf.carriers` with `text_len == 0`,
        // so width is the arrow child count: 2 for 1-parameter, 3 for 2-parameter.
        assert_eq!((forms.width(sf1), forms.width(sf2)), (2, 3));
    }

    /// Whole scalar carriers inside a function or family are recorded by `Leaf.carriers` with
    /// `text_len == 0`, so widening `int` to `bool` or `String` inside a function keeps the
    /// skeleton and width unchanged while still giving distinct canonical forms; a narrowed
    /// literal (`0`) stays distinct from whole `int`.
    #[test]
    fn whole_carriers_inside_a_function_have_zero_text_length() {
        use crate::ty::SParam;
        let mut forms = Forms::new();
        let fn_res = |res: Ty| {
            let p = SParam {
                name: Arc::from("y"),
                positional: true,
                default: None,
                range: None,
            };
            Ty::func(Arc::new(Sig::one(
                vec![p],
                vec![Ty::carrier(Carrier::Int)],
                res,
            )))
        };
        let f_int = fn_res(Ty::carrier(Carrier::Int));
        let f_bool = fn_res(Ty::carrier(Carrier::Bool));
        let f_str = fn_res(Ty::carrier(Carrier::Str));
        let f_zero = fn_res(Ty::set(KType::lit(&Value::Int(0)).unwrap()));
        let (si, sb, ss, sz) = (
            forms.of(&f_int, false),
            forms.of(&f_bool, false),
            forms.of(&f_str, false),
            forms.of(&f_zero, false),
        );
        assert_eq!(si, sb);
        assert_eq!(si, ss);
        assert_eq!(forms.width(si), 2);
        assert_ne!(si, sz);
        assert_ne!(forms.of(&f_int, true), forms.of(&f_bool, true));
        assert_ne!(forms.of(&f_int, true), forms.of(&f_str, true));
        assert_ne!(forms.of(&f_int, true), forms.of(&f_zero, true));
    }

    /// Inside a function a narrowed scalar counts its longest literal toward the width, not
    /// the length of its printed union: `0 | 1000` is as wide as `1000`, so a map whose values
    /// gather the literals of a finite set does not look wider each fold round (R2-3); the two
    /// keep distinct canonical forms (`Leaf.scalars`).
    #[test]
    fn a_union_of_literals_inside_a_function_is_as_wide_as_its_longest_literal() {
        use crate::ty::SParam;
        let mut forms = Forms::new();
        let lit = |n: i64| Ty::set(KType::lit(&Value::Int(n)).unwrap());
        let fn_res = |res: Ty| {
            let p = SParam {
                name: Arc::from("y"),
                positional: true,
                default: None,
                range: None,
            };
            Ty::func(Arc::new(Sig::one(
                vec![p],
                vec![Ty::carrier(Carrier::Int)],
                res,
            )))
        };
        let one = fn_res(lit(1000));
        let two = fn_res(lit(0).union(&lit(1000)));
        let (s1, s2) = (forms.of(&one, false), forms.of(&two, false));
        assert_eq!(s1, s2);
        assert_eq!(forms.width(s1), 4);
        assert_ne!(forms.of(&one, true), forms.of(&two, true));
    }

    /// `known_classes` treats only canonical `"$k"` with `k < known_classes` as known, so
    /// non-canonical spellings (`"$00"`, `"$+0"`, `"$01"`) and ids `>= known_classes` stay
    /// fresh and the known set remains strictly finite.
    #[test]
    fn known_classes_matches_only_canonical_class_ids_below_bound() {
        let mut forms = Forms::new();
        let known = HashSet::new();
        let ok = tuple(&[Ty::var(Arc::from("$0")), Ty::var(Arc::from("$1"))]);
        assert_eq!(forms.of_in(&ok, false, &known, 2).1, 0);
        for bad in ["$2", "$00", "$01", "$+0", "$"] {
            let t = Ty::var(Arc::from(bad));
            assert_eq!(forms.of_in(&t, false, &known, 2).1, 1, "{bad}");
        }
    }

    /// A function's positional flags couple by the subsequence order, a well-quasi-order over
    /// sequences of any length (Higman's lemma): a function of one positional `int` embeds in
    /// one of a named and a positional `int`, and not the other way (Opus seat, N1 of round 1).
    #[test]
    fn a_function_embeds_in_one_whose_flags_hold_its_own_as_a_subsequence() {
        use crate::ty::SParam;
        let i = Ty::carrier(Carrier::Int);
        let func = |flags: &[bool]| {
            let params = (flags.iter().enumerate())
                .map(|(j, &positional)| SParam {
                    name: Arc::from(format!("x{j}")),
                    positional,
                    default: None,
                    range: None,
                })
                .collect();
            Ty::func(Arc::new(Sig::one(
                params,
                vec![i.clone(); flags.len()],
                i.clone(),
            )))
        };
        let mut forms = Forms::new();
        let (a, b) = (
            forms.of(&func(&[true]), false),
            forms.of(&func(&[false, true]), false),
        );
        assert!(forms.embeds(a, b) && !forms.embeds(b, a));
        let c = forms.of(&func(&[false]), false);
        assert!(!forms.embeds(a, c) && !forms.embeds(c, a));
    }

    /// The pair cache and the greedy match of children agree with an exhaustive search over
    /// every ordered choice of child partners, and an embedding never makes a form shallower
    /// or narrower (Codex seat, round 1).
    #[test]
    fn a_greedy_match_agrees_with_all_ordered_choices() {
        fn embeds(forms: &Forms, source: FormId, target: FormId) -> bool {
            fn children(forms: &Forms, source: &[FormId], target: &[FormId]) -> bool {
                let Some((&first, rest)) = source.split_first() else {
                    return true;
                };
                target.iter().enumerate().any(|(at, &partner)| {
                    embeds(forms, first, partner) && children(forms, rest, &target[at + 1..])
                })
            }

            let a = &forms.nodes[source as usize].kids;
            let b = &forms.nodes[target as usize].kids;
            b.iter().any(|&child| embeds(forms, source, child))
                || (forms.labels_fit(source, target) && children(forms, a, b))
        }

        let leaf = Ty::carrier(Carrier::Int);
        let variable = Ty::var(Arc::from("T"));
        let parts = [leaf.clone(), variable, tuple(&[leaf])];
        let mut forms = Forms::new();
        let mut ids = Vec::new();
        for left in &parts {
            ids.push(forms.of(left, false));
            for right in &parts {
                ids.push(forms.of(&tuple(&[left.clone(), right.clone()]), false));
                ids.push(forms.of(&tuple(&[left.clone(), right.clone(), left.clone()]), false));
            }
        }
        for &a in &ids {
            for &b in ids.iter().rev() {
                assert_eq!(forms.embeds(a, b), embeds(&forms, a, b), "{a} in {b}");
                if forms.embeds(a, b) {
                    assert!(forms.depth(a) <= forms.depth(b));
                    assert!(forms.width(a) <= forms.width(b));
                }
            }
        }
    }

    /// A function's key-range end lengths count toward its width and compare by `<=`; an
    /// open end couples only with an open end (Codex seat, round 1).
    #[test]
    fn function_endpoint_counts_contribute_to_width() {
        let mut forms = Forms::new();
        let make = |keys| Node {
            kind: Kind::Fn {
                data: true,
                dense: 1,
                word: None,
                positional: vec![true],
                keys,
                hull: None,
                exact_ends: None,
            },
            kids: Vec::new(),
        };
        let short = forms.intern(make(Some([Some(1), Some(2)])));
        let long = forms.intern(make(Some([Some(1), Some(4)])));
        let open = forms.intern(make(Some([Some(1), None])));
        assert_eq!((forms.width(short), forms.width(long)), (2, 4));
        assert!(forms.embeds(short, long));
        assert!(!forms.embeds(long, short));
        assert!(!forms.embeds(open, short) && !forms.embeds(short, open));
    }

    /// Atoms whose payloads differ in the kernel set have distinct canonical forms: the
    /// payload is printed in the leaf's texts (Codex seat's test of round 1, which asserted
    /// the erasure, inverted).
    #[test]
    fn an_atom_fingerprint_keeps_different_payloads_apart() {
        let a = Ty::set(KType::atom_with(
            "tag",
            &KType::tuple(vec![KType::atom("red")]),
        ));
        let b = Ty::set(KType::atom_with(
            "tag",
            &KType::tuple(vec![KType::atom("blue")]),
        ));
        let mut forms = Forms::new();
        assert_ne!(forms.of(&a, true), forms.of(&Ty::empty(), true));
        assert_ne!(forms.of(&a, true), forms.of(&b, true));
        let (a, b) = (a.carriers().set, b.carriers().set);
        assert!(!a.subtype(&b) && !b.subtype(&a));
    }

    /// A set of bare atoms is told apart by its names and has no text, so an atom set that
    /// grows does not grow the width; an atom with a payload has its printed text, whose
    /// length counts in the width (`leaf_texts`).
    #[test]
    fn a_bare_atom_set_has_no_text_and_a_payload_atom_has_one() {
        let mut forms = Forms::new();
        let one = Ty::set(KType::atom("a"));
        let two = Ty::set(&KType::atom("a") | &KType::atom("bb"));
        let (s1, s2) = (forms.of(&one, false), forms.of(&two, false));
        assert_eq!((forms.width(s1), forms.width(s2)), (0, 0));
        assert_ne!(forms.of(&one, true), forms.of(&two, true));
        let payload = Ty::set(KType::atom_with("p", &KType::tuple(vec![KType::atom("q")])));
        let sp = forms.of(&payload, false);
        assert!(forms.width(sp) > 0);
    }
}
