//! Types (step L1.22, DESIGN.md sec:type_language): sets of values, closed under union,
//! intersection and complement.
//!
//! A type has one part per universe (sec:type_language, the kinding of the connectives): the
//! scalars, which are the literals of each base type and the atoms; the tuples; the structs;
//! and the morphisms. A connective acts on each part on its own, so a complement is taken
//! within each universe. A scalar part is exact: a finite or cofinite set of literals per base
//! type, and per atom name whether the bare atom is in it and which payloads are. The tuple
//! part is, per length, and the morphism part is, a decision diagram over types of the universe
//! (module `bdd`): a Boolean function of tuple or morphism types. Whether one is empty is
//! decided by subtyping (step L1.23), so two of them may denote one set and differ. Structs
//! join at L2: until then the struct part is every struct or none.
//!
//! A morphism type bounds its domain from both sides: the keys it guarantees and the keys it
//! permits, with every present key's value in the value type. `K -> V` is exact and
//! `K ->? V` guarantees no key.
//!
//! A recursive type (step L1.23, module `rec`) is a node that stands for its definition's body
//! and unfolds to it when a connective needs its parts. A node unfolds one level at a time: a
//! tuple component, atom payload or morphism bound that mentions a recursive type is kept
//! as written rather than met with another, so no connective unfolds a type without end.
//! Whether a type is empty, and so subtyping, is decided in module `empty`.

mod bdd;
pub mod bes;
mod debug;
mod empty;
pub use empty::{Refusal, Verdict};
mod print;
pub mod rec;

pub use print::Surface;

use imbl::ordmap::DiffItem;
use imbl::{OrdMap, OrdSet};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::ops::{BitAnd, BitOr, Not, Sub};
use std::sync::{Arc, OnceLock};

use crate::deep;
use crate::num::Rat;
use crate::value::{Id, Items, Value};
use bdd::{Form, Part};

/// A type: the set of values it denotes. Types are ordered by their digests first, so two
/// types are ordered without reading their contents unless their digests are equal, and then by
/// the loop of `bdd::order`, which reads the contents with a stack of its own.
#[derive(Clone)]
pub struct Type(Arc<Node>);

impl Ord for Type {
    fn cmp(&self, other: &Type) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        self.digest()
            .cmp(&other.digest())
            .then_with(|| bdd::order(bdd::Step::Types(self, other)))
    }
}

impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Type) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for Type {}

impl std::hash::Hash for Type {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        // Equal types have equal digests.
        self.digest().hash(h);
    }
}

/// Combines two hashes; the digests of types, nodes and expressions are built with it from
/// their children's, so that each is computed once, when it is made.
pub(crate) fn mix(a: u64, b: u64) -> u64 {
    // splitmix64's finalizer.
    let mut z = (a.rotate_left(29) ^ b).wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    crate::address::short64(salted(z ^ (z >> 31)))
}

#[cfg(test)]
thread_local! {
    /// A test's change of every digest made on its thread (module `print`'s tests): a thread with
    /// another salt orders the atoms of its diagrams as another hash would.
    pub(crate) static SALT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn salted(h: u64) -> u64 {
    h ^ SALT.get()
}

#[cfg(not(test))]
#[inline]
fn salted(h: u64) -> u64 {
    h
}

/// FNV-1a over `b`.
fn bytes(b: &[u8]) -> u64 {
    more_bytes(0xcbf2_9ce4_8422_2325, b)
}

/// FNV-1a over `b`, after the bytes whose hash is `h`, so a text hashes alike in any blocks.
fn more_bytes(h: u64, b: &[u8]) -> u64 {
    b.iter()
        .fold(h, |h, &x| (h ^ u64::from(x)).wrapping_mul(0x100_0000_01b3))
}

/// What the top level of a value says of its membership in a type.
enum Member<'v> {
    Known(bool),
    /// In the type exactly when the tuple of these values is, read in place: an atom's payload
    /// was copied into a tuple to be tested, so a value nested `d` deep was copied `d` times.
    Tuple(Type, &'v Items),
}

/// A hash of a literal: equal literals hash alike. A big integer or a `rat` hashes its
/// residues ([`Rat::residues`]), so a literal such as `1e400000r` costs its own length here,
/// not its digits.
fn scalar(v: &Value) -> u64 {
    let exact = |tag: u64, r: &Rat| {
        let (neg, n, d) = r.residues();
        mix(mix(mix(tag, u64::from(neg)), n), d)
    };
    match v {
        Value::Int(i) => mix(1, *i as u64),
        Value::Str(s) => mix(
            2,
            s.chunks()
                .fold(bytes(b""), |h, c| more_bytes(h, c.as_bytes())),
        ),
        Value::Big(r) => exact(4, r),
        Value::Rat(r) => exact(5, r),
        other => mix(3, bytes(other.to_string().as_bytes())),
    }
}

/// A literal as a type prints it: a `rat` in canonical form ([`Rat::literal_text`]), so its
/// text costs the literal's length; any other as the value prints.
pub(crate) fn lit_text(v: &Value) -> String {
    match v {
        Value::Rat(r) => r.literal_text(),
        other => other.to_string(),
    }
}

enum Node {
    Parts(Parts, Shown),
    Rec(Rec),
}

/// A node's parts and text are freed in a loop (module `deep`), so a type nested deep is freed
/// on any stack. A recursive node's body is a type, which frees its own node so.
impl Drop for Node {
    fn drop(&mut self) {
        if let Node::Parts(p, shown) = self {
            if !p.atoms.names.is_empty() {
                free(Freed::Atoms(std::mem::take(&mut p.atoms.names)));
            }
            if !p.tuples.lens.is_empty() {
                free(Freed::Lens(std::mem::take(&mut p.tuples.lens)));
            }
            if p.morphisms.is_leaf().is_none() {
                free(Freed::Morphisms(bdd::Owned::Part(std::mem::replace(
                    &mut p.morphisms,
                    Part::leaf(false),
                ))));
            }
            if let Some(r) = shown.0.take() {
                free(Freed::Rope(r));
            }
        }
    }
}

/// A part of a type whose owner is being dropped: what lies between one level of a type and the
/// next, which drops a type inside it by queueing that type's own parts.
#[expect(dead_code, reason = "a part is held only to be dropped")]
enum Freed {
    Atoms(OrdMap<Arc<str>, AtomPart>),
    Lens(BTreeMap<usize, Part<Row>>),
    Rope(Rope),
    Tuples(bdd::Owned<Row>),
    Morphisms(bdd::Owned<Morphism>),
}

thread_local! {
    /// The parts of types waiting to be dropped.
    static FREED: deep::Queue<Freed> = const { deep::Queue::new() };
}

fn free(part: Freed) {
    deep::free_in(&FREED, part);
}

/// Keeps [`FREED`] until after the thread-locals first used after this call, such as the tables
/// of diagram nodes, which hold types.
fn hold() {
    deep::hold(&FREED);
}

/// A type's text as a rope, made when first printed. It takes no part in comparing types.
#[derive(Default)]
struct Shown(OnceLock<Rope>);

impl PartialEq for Shown {
    fn eq(&self, _: &Shown) -> bool {
        true
    }
}

impl Eq for Shown {}

/// A recursive type, or a part of a recursive definition's body kept unevaluated: its parts are
/// `make()`, computed on first use. Two nodes are one type when their keys are equal.
struct Rec {
    /// What the node stands for, by its group's definitions and arguments: its digest and order.
    key: rec::Key,
    /// The name, made when first printed: a name spells out its part of the definition, so
    /// making every part's name at once cost the product of the definition's size and depth.
    /// It is a rope holding the texts of the argument types, which [`Type::rope`] makes in its
    /// loop like any other text.
    name: OnceLock<Rope>,
    naming: Box<dyn Fn() -> Rope + Send + Sync>,
    body: OnceLock<Type>,
    make: Box<dyn Fn() -> Type + Send + Sync>,
    /// The emptiness its group decides for it, if the group is decided (module `bes`).
    judge: Option<Box<dyn Fn() -> Option<bool> + Send + Sync>>,
}

impl fmt::Debug for Rec {
    /// The name, made apart from any text under way on this thread, in which a text not made yet
    /// is a placeholder. The argument types' texts are then each made by a loop of their own.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let outer = SHOWING.with_borrow_mut(Option::take);
        let name = self.name.get_or_init(|| (self.naming)()).clone();
        SHOWING.with_borrow_mut(|s| *s = outer);
        name.strs().try_for_each(|s| f.write_str(s))
    }
}

/// The universes of values, within each of which a complement is taken.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Universe {
    /// Booleans, numbers, strings and atoms.
    Scalar,
    /// Tuples of every length, and keypaths.
    Tuple,
    /// Structs, which join at L2.
    Struct,
    /// Functions and families.
    Morphism,
}

impl Universe {
    /// The universe of `v`. A keypath is a tuple of keys; an atom with its payload is a scalar.
    pub fn of(v: &Value) -> Universe {
        match v {
            Value::Tuple(_) | Value::Path(_) => Universe::Tuple,
            Value::Family(_) => Universe::Morphism,
            _ => Universe::Scalar,
        }
    }
}

/// A morphism type: `(guarantee ⊆ dom ⊆ permission) -> value`.
#[derive(Clone, PartialEq, Eq)]
pub struct Morphism {
    /// The keys certainly present.
    pub guarantee: Type,
    /// The keys possibly present.
    pub permission: Type,
    /// The type of every present key's value.
    pub value: Type,
}

/// By guarantee, then permission, then value, in the loop of `bdd::order`.
impl Ord for Morphism {
    fn cmp(&self, other: &Morphism) -> std::cmp::Ordering {
        bdd::order(bdd::Step::Morphisms(self, other))
    }
}

impl PartialOrd for Morphism {
    fn partial_cmp(&self, other: &Morphism) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// The component types of a tuple type, an atom of the tuple parts, kept with their hash in
/// one shared node: a row is copied in constant time, and compared in constant time unless it
/// equals a row built apart from it.
#[derive(Clone)]
pub(crate) struct Row(Arc<(u64, Vec<Type>)>);

impl Row {
    pub(crate) fn new(items: Vec<Type>) -> Row {
        let digest = items.iter().fold(5, |h, t| mix(h, t.digest()));
        Row(Arc::new((digest, items)))
    }

    pub(crate) fn digest(&self) -> u64 {
        self.0.0
    }
}

impl std::ops::Deref for Row {
    type Target = [Type];
    fn deref(&self) -> &[Type] {
        &self.0.1
    }
}

impl<'a> IntoIterator for &'a Row {
    type Item = &'a Type;
    type IntoIter = std::slice::Iter<'a, Type>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.1.iter()
    }
}

impl Ord for Row {
    fn cmp(&self, other: &Row) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        self.0
            .0
            .cmp(&other.0.0)
            .then_with(|| bdd::order(bdd::Step::Rows(self, other)))
    }
}

impl PartialOrd for Row {
    fn partial_cmp(&self, other: &Row) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Row {
    fn eq(&self, other: &Row) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for Row {}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Parts {
    /// The hash of the other fields, set by [`Type::new`].
    digest: u64,
    /// Bit 0 for `false`, bit 1 for `true`.
    bools: u8,
    ints: Lits,
    rats: Lits,
    floats: Lits,
    strings: Lits,
    atoms: Atoms,
    tuples: Tuples,
    structs: bool,
    morphisms: Part<Morphism>,
}

/// A finite set of literals, or the complement of one within its base type. The set is
/// persistent, so that a union or difference with a small set copies nothing else, and `sum`,
/// the wrapping sum of its literals' hashes, is kept as it changes.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Lits {
    cofinite: bool,
    values: OrdSet<Value>,
    sum: u64,
}

/// Per atom name, its part; a name not listed has every payload when `cofinite`, else none.
/// The map is persistent, and `sum` is the wrapping sum of its entries' hashes.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
struct Atoms {
    cofinite: bool,
    names: OrdMap<Arc<str>, AtomPart>,
    sum: u64,
}

/// The atoms of one name in a type: the bare atom, and those whose payload is in `payload`, a
/// type within the tuples and structs.
#[derive(Clone, PartialEq, Eq, Debug)]
struct AtomPart {
    bare: bool,
    payload: Type,
}

/// Per length, the tuples of that length, as a part over tuple types of it; a
/// length not listed has every tuple when `rest`, else none. Tuples of two lengths are disjoint.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
struct Tuples {
    rest: bool,
    lens: BTreeMap<usize, Part<Row>>,
}

thread_local! {
    static EMPTY: Type = Type::build_empty();
    static TOP: Type = !Type::build_empty();
    /// `bool`, `int`, `rat`, `f64` and `String`, made once, so that every use of one is one
    /// node and compares equal to another by pointer.
    static SCALARS: [Type; 5] = [
        Type::with(|p| p.bools = 3),
        Type::with(|p| p.ints.cofinite = true),
        Type::with(|p| p.rats.cofinite = true),
        Type::with(|p| p.floats.cofinite = true),
        Type::with(|p| p.strings.cofinite = true),
    ];
    /// Each universe's type, made once, in the order of [`Universe`].
    static UNIVERSES: [Type; 4] = [
        Universe::Scalar,
        Universe::Tuple,
        Universe::Struct,
        Universe::Morphism,
    ]
    .map(Type::build_universe);
}

impl Parts {
    fn hash(&self) -> u64 {
        let mut h = mix(0, u64::from(self.bools));
        for l in [&self.ints, &self.rats, &self.floats, &self.strings] {
            h = mix(mix(h, u64::from(l.cofinite)), l.sum);
        }
        h = mix(mix(h, u64::from(self.atoms.cofinite)), self.atoms.sum);
        h = mix(h, u64::from(self.tuples.rest));
        for (len, part) in &self.tuples.lens {
            h = mix(mix(h, *len as u64), part.digest());
        }
        mix(mix(h, u64::from(self.structs)), self.morphisms.digest())
    }
}

impl Type {
    fn new(mut p: Parts) -> Type {
        hold();
        p.digest = p.hash();
        Type(Arc::new(Node::Parts(p, Shown::default())))
    }

    /// The hash of the contents, computed when the type was made; a recursive node's is its
    /// key's, made of its group's definitions and arguments.
    pub(crate) fn digest(&self) -> u64 {
        match &*self.0 {
            Node::Parts(p, _) => p.digest,
            Node::Rec(r) => r.key.digest(),
        }
    }

    /// The address of this type's node: equal for two handles on one node, and not reused
    /// while a handle on the node is held.
    pub(crate) fn node_addr(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }

    /// The node named `naming()` whose parts are `make()`'s, each computed when first needed.
    /// `make` must not need this node's parts, which a contractive definition ensures.
    fn rec(
        key: rec::Key,
        naming: impl Fn() -> Rope + Send + Sync + 'static,
        make: impl Fn() -> Type + Send + Sync + 'static,
    ) -> Type {
        Type::rec_with(key, Box::new(naming), Box::new(make), None)
    }

    /// The node of [`Type::rec`], with its emptiness given by `judge` when there is one.
    fn rec_with(
        key: rec::Key,
        naming: Box<dyn Fn() -> Rope + Send + Sync>,
        make: Box<dyn Fn() -> Type + Send + Sync>,
        judge: Option<Box<dyn Fn() -> Option<bool> + Send + Sync>>,
    ) -> Type {
        Type(Arc::new(Node::Rec(Rec {
            key,
            name: OnceLock::new(),
            naming,
            body: OnceLock::new(),
            make,
            judge,
        })))
    }

    /// [`Type::rec`], with `judge()` giving its emptiness when its group decides it.
    fn rec_judged(
        key: rec::Key,
        naming: impl Fn() -> Rope + Send + Sync + 'static,
        make: impl Fn() -> Type + Send + Sync + 'static,
        judge: impl Fn() -> Option<bool> + Send + Sync + 'static,
    ) -> Type {
        Type::rec_with(key, Box::new(naming), Box::new(make), Some(Box::new(judge)))
    }

    /// The emptiness the group of a recursive node decides for it, if any.
    pub(crate) fn judged(&self) -> Option<bool> {
        match &*self.0 {
            Node::Parts(..) => None,
            Node::Rec(r) => r.judge.as_ref().and_then(|j| j()),
        }
    }

    /// Whether this is a recursive member of a group, which its group's decider is asked about.
    pub(crate) fn is_member(&self) -> bool {
        matches!(&*self.0, Node::Rec(r) if r.judge.is_some())
    }

    /// The group of a recursive member, as a number that two members share exactly when they
    /// are members of one instance of a group.
    pub(crate) fn group(&self) -> Option<usize> {
        match &*self.0 {
            Node::Parts(..) => None,
            Node::Rec(r) => r.key.group(),
        }
    }

    /// The recursive members of the group of a recursive member, in definition order.
    pub(crate) fn group_members(&self) -> Option<Vec<Type>> {
        match &*self.0 {
            Node::Parts(..) => None,
            Node::Rec(r) => r.key.members(),
        }
    }

    /// Whether this is a recursive type by name, not its unfolding.
    fn is_recursive(&self) -> bool {
        matches!(&*self.0, Node::Rec(_))
    }

    /// The parts, unfolding a recursive node.
    fn p(&self) -> &Parts {
        match &*self.0 {
            Node::Parts(p, _) => p,
            Node::Rec(r) => r.body.get_or_init(|| (r.make)()).p(),
        }
    }

    /// No value.
    pub fn empty() -> Type {
        EMPTY.with(Type::clone)
    }

    fn build_empty() -> Type {
        Type::new(Parts {
            digest: 0,
            bools: 0,
            ints: Lits::default(),
            rats: Lits::default(),
            floats: Lits::default(),
            strings: Lits::default(),
            atoms: Atoms::default(),
            tuples: Tuples::default(),
            structs: false,
            morphisms: Part::leaf(false),
        })
    }

    /// Every value, `_`.
    pub fn top() -> Type {
        TOP.with(Type::clone)
    }

    /// The union of `ts`, joined in pairs: `k` tuple or morphism types, each ordered after the
    /// last in the diagrams, cost `O(k log k)` nodes joined this way and `O(k²)` one at a time.
    pub fn union_all(ts: impl IntoIterator<Item = Type>) -> Type {
        Type::pairwise(ts, Type::empty(), |a, b| a | b)
    }

    /// The intersection of `ts`, joined in pairs as in [`Type::union_all`].
    pub fn meet_all(ts: impl IntoIterator<Item = Type>) -> Type {
        Type::pairwise(ts, Type::top(), |a, b| a & b)
    }

    fn pairwise(
        ts: impl IntoIterator<Item = Type>,
        unit: Type,
        op: impl Fn(Type, Type) -> Type,
    ) -> Type {
        let mut ts: Vec<Type> = ts.into_iter().collect();
        while ts.len() > 1 {
            let mut it = std::mem::take(&mut ts).into_iter();
            while let Some(a) = it.next() {
                ts.push(match it.next() {
                    Some(b) => op(a, b),
                    None => a,
                });
            }
        }
        ts.pop().unwrap_or(unit)
    }

    fn with(f: impl FnOnce(&mut Parts)) -> Type {
        let mut p = Type::empty().p().clone();
        f(&mut p);
        Type::new(p)
    }

    /// `bool`.
    pub fn bool() -> Type {
        SCALARS.with(|s| s[0].clone())
    }

    /// `int`.
    pub fn int() -> Type {
        SCALARS.with(|s| s[1].clone())
    }

    /// `rat`.
    pub fn rat() -> Type {
        SCALARS.with(|s| s[2].clone())
    }

    /// `f64`.
    pub fn f64() -> Type {
        SCALARS.with(|s| s[3].clone())
    }

    /// `String`.
    pub fn string() -> Type {
        SCALARS.with(|s| s[4].clone())
    }

    /// The type of one scalar literal or bare atom; `None` for any other value.
    pub fn lit(v: &Value) -> Option<Type> {
        let one = |l: &mut Lits| l.insert(v);
        Some(match v {
            Value::Bool(b) => Type::with(|p| p.bools = 1 << u8::from(*b)),
            Value::Int(_) | Value::Big(_) => Type::with(|p| one(&mut p.ints)),
            Value::Rat(_) => Type::with(|p| one(&mut p.rats)),
            Value::Float(_) => Type::with(|p| one(&mut p.floats)),
            Value::Str(_) => Type::with(|p| one(&mut p.strings)),
            Value::Atom(a) if a.args.is_empty() => Type::atom(&a.name),
            _ => return None,
        })
    }

    /// The bare atom `#name`.
    pub fn atom(name: &str) -> Type {
        Type::atom_part(name, true, Type::empty())
    }

    /// `#name(payload)`: the atoms of that name whose payload, a tuple or struct, is in
    /// `payload`.
    pub fn atom_with(name: &str, payload: &Type) -> Type {
        Type::atom_part(name, false, payload & &Type::payloads())
    }

    fn atom_part(name: &str, bare: bool, payload: Type) -> Type {
        let part = AtomPart { bare, payload };
        let mut atoms = Atoms::default();
        atoms.set(&name.into(), part);
        Type::with(|p| p.atoms = atoms)
    }

    /// The tuple type `(t1, …, tn)`.
    pub fn tuple(items: Vec<Type>) -> Type {
        Type::with(|p| p.tuples = Tuples::literal(items))
    }

    /// The morphism type with the given bounds and value type.
    pub fn morphism(guarantee: Type, permission: Type, value: Type) -> Type {
        Type::with(|p| {
            p.morphisms = Part::literal(Morphism {
                guarantee,
                permission,
                value,
            })
        })
    }

    /// `K -> V`, exact: every key of `K` is present.
    pub fn exact(key: Type, value: Type) -> Type {
        Type::morphism(key.clone(), key, value)
    }

    /// `K ->? V`: the keys are drawn from `K`, none promised.
    pub fn partial(key: Type, value: Type) -> Type {
        Type::morphism(Type::empty(), key, value)
    }

    /// Every value of `u`.
    pub fn universe(u: Universe) -> Type {
        UNIVERSES.with(|us| us[u as usize].clone())
    }

    fn build_universe(u: Universe) -> Type {
        Type::with(|p| match u {
            Universe::Scalar => {
                p.bools = 3;
                for l in [&mut p.ints, &mut p.rats, &mut p.floats, &mut p.strings] {
                    l.cofinite = true;
                }
                p.atoms.cofinite = true;
            }
            Universe::Tuple => {
                p.tuples = Tuples {
                    rest: true,
                    lens: BTreeMap::new(),
                }
            }
            Universe::Struct => p.structs = true,
            Universe::Morphism => p.morphisms = Part::leaf(true),
        })
    }

    /// The values an atom's payload may be: tuples and structs.
    fn payloads() -> Type {
        Type::universe(Universe::Tuple) | Type::universe(Universe::Struct)
    }

    /// The values of `self` in `u`.
    pub fn part(&self, u: Universe) -> Type {
        self & &Type::universe(u)
    }

    /// Whether the morphism part of `self` is neither every morphism nor none. A run-time
    /// test against such a type is not decidable (sec:type_notation: run-time type tests are
    /// restricted to decidable checks).
    fn has_morphism_bounds(&self) -> bool {
        self.p().morphisms.is_leaf().is_none()
    }

    /// Whether membership in `self` is decidable at run time: no part of it, nor of a tuple
    /// component or atom payload it holds, is a proper subset of the morphisms.
    pub fn decidable(&self) -> bool {
        self.decidable_from(&mut BTreeSet::new())
    }

    /// `decidable`, with `seen` the recursive nodes already being checked.
    fn decidable_from(&self, seen: &mut BTreeSet<Type>) -> bool {
        if matches!(&*self.0, Node::Rec(_)) && !seen.insert(self.clone()) {
            return true;
        }
        let p = self.p();
        !self.has_morphism_bounds()
            && p.atoms
                .names
                .values()
                .all(|a| a.payload.decidable_from(seen))
            && p.tuples
                .atoms(&mut |t| t.iter().all(|t| t.decidable_from(seen)))
    }

    /// Whether every function is in `self`; for a decidable type, either every function is or
    /// none is.
    pub fn functions(&self) -> bool {
        self.p().morphisms.is_leaf() == Some(true)
    }

    /// Whether `self` is known to have finitely many values: it holds only bools, finite
    /// literal sets, bare atoms, and tuples whose boxes (`Type::boxes`) hold only types known
    /// finite. A recursive type, a payload, a struct or a function is not known finite, and a
    /// box is read as written, so `(int, 0) - (int - 0, 0)` is not known finite although it has
    /// one value. No size is compared: the answer depends on the type alone, not on the order
    /// its diagram tests tuple types in.
    pub fn finite(&self) -> bool {
        self.finite_order().is_some()
    }

    /// The integers of `self`, when they are a finite set of literals. Its users: the checker's
    /// test that the exponent of `x ** n` is at least 0 (`zedc::check`, `exponent`) and the
    /// type facet of a product cell (`zedc::store::product`).
    pub fn ints_listed(&self) -> Option<Vec<Value>> {
        let p = self.p();
        (!p.ints.cofinite).then(|| p.ints.values.iter().cloned().collect())
    }

    /// Each value of `self` once, when `self` is [`Type::finite`]: its scalars and bare atoms,
    /// then its tuples, length by length and box by box, the last component of a box fastest.
    /// Every type inside the boxes is made lazily too, one value at a time when a box first
    /// reads it, and each value is kept for the other boxes that read it, so no type is listed
    /// further than the values taken need: the first value of `t(d)`, `t(i + 1) = (t(i),
    /// t(i))`, reads one value of each of its `d + 1` types, although `t(d - 1)` has `2^(2^(d -
    /// 1))`. Between two values the iterator can try every tuple of a box that the type does
    /// not hold, which can be exponential in the type's size: listing the values of a tuple
    /// type in time polynomial in their number would decide satisfiability. A tuple is checked
    /// on the type's part restricted to the tuple types that may hold it, found by its
    /// components: each tuple type is filed by the scalars, bare atoms and empty tuples its
    /// columns list, at any depth of first components, and one no column of which lists all it
    /// holds is decided by the kinds of a tuple that has none of its keys (`RowIndex`); and it
    /// is checked against the earlier boxes that may hold it (`BoxIndex`): the exclusive or of
    /// `c` tuple types lists its `c` values in about `c log² c` steps, not `c²`
    /// (LIST-parity-quad, LIST-parity-rest). Its user is the type facet of a
    /// product cell (`zedc::store::product`).
    pub fn each_value(&self) -> Option<Values> {
        let (types, boxes): (Vec<Type>, Vec<Vec<Row>>) = self.finite_order()?.into_iter().unzip();
        let index: HashMap<&Type, usize> = types.iter().enumerate().map(|(i, t)| (t, i)).collect();
        // A type is looked up once per box, never per value: two equal types built apart
        // compare by their contents.
        let boxes: Vec<Vec<(Vec<usize>, Row)>> = boxes
            .into_iter()
            .map(|boxes| {
                boxes
                    .into_iter()
                    .map(|r| (r.iter().map(|c| index[c]).collect(), r))
                    .collect()
            })
            .collect();
        // The rows the diagrams test a tuple against, each with the maker of each of its
        // types that has one, so that a tuple's check reads only the components made by
        // another type.
        let rows: Vec<BTreeMap<Row, Vec<Option<usize>>>> = types
            .iter()
            .map(|t| {
                let mut rows = BTreeMap::new();
                for part in t.p().tuples.lens.values() {
                    part.atoms(&mut |r: &Row| {
                        let makers = r.iter().map(|c| index.get(c).copied()).collect();
                        rows.insert(r.clone(), makers);
                        true
                    });
                }
                rows
            })
            .collect();
        drop(index);
        let makers = types
            .into_iter()
            .zip(boxes.into_iter().zip(rows))
            .map(|(t, (boxes, rows))| Maker::new(t, boxes, rows))
            .collect();
        Some(Values { makers, given: 0 })
    }

    /// The types `self`'s values are built from, each with its boxes and after the types in
    /// them, `self` last, when every one is known finite. One visit per type, kept in a visited
    /// set, and an explicit stack, since the nesting depth follows the input.
    fn finite_order(&self) -> Option<Vec<(Type, Vec<Row>)>> {
        let mut order = Vec::new();
        let mut seen: HashSet<Type> = HashSet::new();
        let mut stack: Vec<(Type, Option<Vec<Row>>)> = vec![(self.clone(), None)];
        while let Some((t, done)) = stack.pop() {
            if let Some(boxes) = done {
                order.push((t, boxes));
                continue;
            }
            if !seen.insert(t.clone()) {
                continue;
            }
            let boxes = t.boxes()?;
            let below: Vec<Type> = boxes
                .iter()
                .flat_map(|r| r.iter())
                .filter(|c| !seen.contains(*c))
                .cloned()
                .collect();
            stack.push((t, Some(boxes)));
            stack.extend(below.into_iter().map(|c| (c, None)));
        }
        Some(order)
    }

    /// Tuple types, the boxes, whose union holds every tuple of `self`, when the rest of
    /// `self` is finite and every tuple of it is in a tuple type the diagram takes; `None`
    /// otherwise. A value of a diagram is in the last tuple type its path takes, and in the
    /// meet of those the path took before; so each node that is the last tuple type taken on a
    /// path to `true` gives the box of its tuple type met with the union of the meets on the
    /// paths to it, one pass over the nodes, never over the paths. A node whose taken branch
    /// meets another tuple type before `true` gives no box of its own, so a meet of tuple types
    /// gives its meet in either order of the diagram. An expression gives each of its tuple types.
    fn boxes(&self) -> Option<Vec<Row>> {
        let Node::Parts(p, _) = &*self.0 else {
            return None;
        };
        if p.structs
            || p.morphisms.is_leaf() != Some(false)
            || p.atoms.cofinite
            || p.tuples.rest
            || [&p.ints, &p.rats, &p.floats, &p.strings]
                .iter()
                .any(|l| l.cofinite)
            || p.atoms.names.values().any(|a| a.payload != Type::empty())
        {
            return None;
        }
        let meet =
            |r: &Row, s: &Row| Row::new(r.iter().zip(s.iter()).map(|(x, y)| x & y).collect());
        let mut out = Vec::new();
        for (len, part) in &p.tuples.lens {
            // The tuples outside every tuple type of the part are not listed.
            if part.eval(&|_| false) {
                return None;
            }
            // The meet of a path's tuple types is kept as the meets of runs of them, each with
            // its count, the counts falling from first to last: a run met when one as long
            // follows it. A chain of `c` tuple types is so met in pairs, as `Type::meet_all`
            // meets, where meeting each into the meet of those before it cost order `c²` when
            // their columns grow with the count, as `(int - (2i + 1), 0)` do
            // (LIST-parity-tail).
            let met = |runs: &[(Row, usize)]| {
                let mut runs = runs.iter().rev().map(|(r, _)| r);
                let first = runs
                    .next()
                    .map_or_else(|| Row::new(vec![Type::top(); *len]), Row::clone);
                runs.fold(first, |m, r| meet(&m, r))
            };
            match part {
                Part::Bdd(b) => {
                    b.reaching(
                        Vec::new(),
                        |runs: &Vec<(Row, usize)>, a| {
                            let (mut runs, mut last) = (runs.clone(), (a.clone(), 1));
                            while let Some((r, n)) = runs.pop_if(|(_, n)| *n <= last.1) {
                                last = (meet(&r, &last.0), n + last.1);
                            }
                            runs.push(last);
                            runs
                        },
                        |r, s| {
                            let (m, n) = (met(r), met(s));
                            let count = r.iter().chain(s).map(|(_, k)| k).sum();
                            let join = m.iter().zip(n.iter()).map(|(x, y)| x | y).collect();
                            vec![(Row::new(join), count)]
                        },
                        |a, runs| {
                            out.push(meet(a, &met(runs)));
                            true
                        },
                    );
                }
                Part::Expr(_) => {
                    part.atoms(&mut |a| {
                        out.push(a.clone());
                        true
                    });
                }
            }
        }
        Some(out)
    }

    /// Whether `v` is in `self`, for a decidable `self`. Each tuple and payload of `v` is tested
    /// once against each component type it meets, innermost first, so the cost follows the
    /// size of `v` and its depth is limited by memory alone. A test is kept under the type, by
    /// its contents, and the sequence of `v` it reads, by the sequence's id (`Items::id`): copies
    /// of one sequence share it and no other sequence has it, and the kept tests are never
    /// iterated, so the answer does not depend on the ids' values or on where `v` is in memory.
    ///
    /// Exception to keying by content (deterministic checking): the id names one occurrence of
    /// a shared sequence. A content key would hash a sequence in full at each test, O(size) per
    /// node, and a value whose halves are one shared value at every level has `2^d` paths and
    /// `d` sequences, so its content is exponential to read while the id keeps the work linear
    /// in the sequences. Two sequences equal in content built apart are tested twice, which
    /// costs time and never changes the answer. Tests:
    /// `l01_23_subtyping::rec::membership_by_sequence_id_is_deterministic` (shared against
    /// apart, three allocation orders, one thread against a fresh thread per query) and
    /// `membership_of_a_value_whose_halves_share_scales`.
    pub fn contains(&self, v: &Value) -> bool {
        let first = match self.member(v) {
            Member::Known(b) => return b,
            Member::Tuple(ty, xs) => (ty, xs),
        };
        let key = |t: &Type, xs: &Items| (t.clone(), xs.id());
        let mut known = HashMap::new();
        let mut todo = vec![first];
        loop {
            let (ty, xs) = todo.last().expect("the first test ends the loop");
            let xs = *xs;
            let waiting = RefCell::new(Vec::new());
            let fits = ty.p().tuples.get(xs.len()).eval(&|row: &Row| {
                let mut fits = true;
                for (t, x) in row.iter().zip(xs) {
                    fits &= match t.member(x) {
                        Member::Known(b) => b,
                        Member::Tuple(t, ys) => match known.get(&key(&t, ys)) {
                            Some(b) => *b,
                            None => {
                                waiting.borrow_mut().push((t, ys));
                                false
                            }
                        },
                    };
                }
                fits
            });
            let waiting = waiting.into_inner();
            if !waiting.is_empty() {
                todo.extend(waiting);
                continue;
            }
            let (ty, xs) = todo.pop().expect("the loop read the top of the stack");
            if todo.is_empty() {
                return fits;
            }
            known.insert(key(&ty, xs), fits);
        }
    }

    /// Whether `v` is in `self`, as far as `v`'s top level decides.
    fn member<'v>(&self, v: &'v Value) -> Member<'v> {
        let p = self.p();
        Member::Known(match v {
            Value::Bool(b) => p.bools & (1 << u8::from(*b)) != 0,
            Value::Int(_) | Value::Big(_) => p.ints.contains(v),
            Value::Rat(_) => p.rats.contains(v),
            Value::Float(_) => p.floats.contains(v),
            Value::Str(_) => p.strings.contains(v),
            Value::Atom(a) => match p.atoms.names.get(&a.name) {
                None => p.atoms.cofinite,
                Some(part) if a.args.is_empty() => part.bare,
                Some(part) if a.fields.is_empty() => {
                    return Member::Tuple(part.payload.clone(), &a.args);
                }
                Some(part) => part.payload.p().structs,
            },
            Value::Tuple(xs) | Value::Path(xs) => return Member::Tuple(self.clone(), xs),
            Value::Family(_) => self.functions(),
        })
    }

    fn zip(&self, other: &Type, op: Op) -> Type {
        let (a, b) = (self.p(), other.p());
        Type::new(Parts {
            digest: 0,
            bools: match op {
                Op::Or => a.bools | b.bools,
                Op::And => a.bools & b.bools,
            },
            ints: a.ints.zip(&b.ints, op),
            rats: a.rats.zip(&b.rats, op),
            floats: a.floats.zip(&b.floats, op),
            strings: a.strings.zip(&b.strings, op),
            atoms: a.atoms.zip(&b.atoms, op),
            tuples: a.tuples.zip(&b.tuples, op),
            structs: match op {
                Op::Or => a.structs || b.structs,
                Op::And => a.structs && b.structs,
            },
            morphisms: a.morphisms.zip(&b.morphisms, op),
        })
    }

    /// Whether `self & other`, or `self - other` when `both` is false, is empty, when neither
    /// type holds anything but scalars; `None` otherwise. Nothing is built.
    fn scalar_cell(&self, other: &Type, both: bool) -> Option<bool> {
        let (a, b) = (self.p(), other.p());
        if !a.scalars_only() || !b.scalars_only() {
            return None;
        }
        Some(if both {
            a.bools & b.bools == 0
                && a.ints.disjoint(&b.ints)
                && a.rats.disjoint(&b.rats)
                && a.floats.disjoint(&b.floats)
                && a.strings.disjoint(&b.strings)
        } else {
            a.bools & !b.bools == 0
                && a.ints.within(&b.ints)
                && a.rats.within(&b.rats)
                && a.floats.within(&b.floats)
                && a.strings.within(&b.strings)
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    Or,
    And,
}

impl Parts {
    fn scalars_only(&self) -> bool {
        self.atoms == Atoms::default()
            && self.tuples == Tuples::default()
            && !self.structs
            && self.morphisms.is_leaf() == Some(false)
    }

    /// Whether it holds a boolean, number or string, read from the parts.
    fn has_scalars(&self) -> bool {
        self.bools != 0
            || [&self.ints, &self.rats, &self.floats, &self.strings]
                .iter()
                .any(|l| l.cofinite || !l.values.is_empty())
    }
}

/// A type split by universe: what [`Type::split`] gives.
pub struct Split {
    /// Its values of `bool`, `int`, `rat`, `f64` and `String`, in that order, each `None` when
    /// it has none.
    pub bases: [Option<Type>; 5],
    /// Its atoms, `None` when it has none.
    pub atoms: Option<Type>,
    /// Its tuples, structs and morphisms, `None` when it has none.
    pub rest: Option<Type>,
}

impl Type {
    /// Whether it may hold an atom, read from its parts: false only when it holds none.
    pub fn may_hold_atoms(&self) -> bool {
        self.p().atoms != Atoms::default()
    }

    /// The names of its atoms, each with whether it holds the bare atom `#name`, read from its
    /// parts in name order; `None` when it holds the atoms of every name it does not list. A
    /// listed name may hold no value, when its payload type is empty but not built as empty.
    pub fn atom_names(&self) -> Option<impl Iterator<Item = (&str, bool)>> {
        let a = &self.p().atoms;
        (!a.cofinite).then(|| a.names.iter().map(|(n, p)| (&**n, p.bare)))
    }

    /// `self` split into its values of each base type, its atoms and the rest: what `self & t`
    /// gives for `t` each base type, and then the atoms and the other universes, each made by
    /// copying one part of `self`, where the meets would build each part of each result.
    pub fn split(&self) -> Split {
        let p = self.p();
        let lits = |l: &Lits, set: fn(&mut Parts, Lits)| {
            (l.cofinite || !l.values.is_empty()).then(|| Type::with(|q| set(q, l.clone())))
        };
        let bools = (p.bools != 0).then(|| Type::with(|q| q.bools = p.bools));
        let atoms = (p.atoms != Atoms::default())
            .then(|| Type::with(|q| q.atoms = p.atoms.clone()))
            .filter(|t| !t.is_empty());
        let rest =
            (p.tuples != Tuples::default() || p.structs || p.morphisms.is_leaf() != Some(false))
                .then(|| {
                    Type::with(|q| {
                        q.tuples = p.tuples.clone();
                        q.structs = p.structs;
                        q.morphisms = p.morphisms.clone();
                    })
                })
                .filter(|t| !t.is_empty());
        Split {
            bases: [
                bools,
                lits(&p.ints, |q, l| q.ints = l),
                lits(&p.rats, |q, l| q.rats = l),
                lits(&p.floats, |q, l| q.floats = l),
                lits(&p.strings, |q, l| q.strings = l),
            ],
            atoms,
            rest,
        }
    }
}

impl Lits {
    /// Whether no literal is in both sets.
    fn disjoint(&self, other: &Lits) -> bool {
        let (a, b) = (self, other);
        match (a.cofinite, b.cofinite) {
            (false, false) if a.values.len() > b.values.len() => {
                !b.values.iter().any(|v| a.values.contains(v))
            }
            (false, false) => !a.values.iter().any(|v| b.values.contains(v)),
            (false, true) => a.values.iter().all(|v| b.values.contains(v)),
            (true, false) => b.values.iter().all(|v| a.values.contains(v)),
            (true, true) => false,
        }
    }

    /// Whether every literal of `self` is in `other`.
    fn within(&self, other: &Lits) -> bool {
        let (a, b) = (self, other);
        match (a.cofinite, b.cofinite) {
            (false, false) => a.values.iter().all(|v| b.values.contains(v)),
            (false, true) => !a.values.iter().any(|v| b.values.contains(v)),
            (true, false) => false,
            (true, true) => b.values.iter().all(|v| a.values.contains(v)),
        }
    }

    fn contains(&self, v: &Value) -> bool {
        self.values.contains(v) != self.cofinite
    }

    fn insert(&mut self, v: &Value) {
        if self.values.insert(v.clone()).is_none() {
            self.sum = self.sum.wrapping_add(scalar(v));
        }
    }

    fn remove(&mut self, v: &Value) {
        if self.values.remove(v).is_some() {
            self.sum = self.sum.wrapping_sub(scalar(v));
        }
    }

    /// The sets combined by `op`, each in `O(s log l)` steps for the smaller set's `s`
    /// literals and the larger's `l`: the result is the larger set changed by the smaller's
    /// literals, or the smaller set's literals filtered.
    fn zip(&self, other: &Lits, op: Op) -> Lits {
        let (a, b) = (self, other);
        let (cofinite, mut out) = match (op, a.cofinite, b.cofinite) {
            (Op::Or, false, false) => (false, Lits::union(a, b)),
            (Op::Or, false, true) => (true, Lits::minus(b, a)),
            (Op::Or, true, false) => (true, Lits::minus(a, b)),
            (Op::Or, true, true) => (true, Lits::meet(a, b)),
            (Op::And, false, false) => (false, Lits::meet(a, b)),
            (Op::And, false, true) => (false, Lits::minus(a, b)),
            (Op::And, true, false) => (false, Lits::minus(b, a)),
            (Op::And, true, true) => (true, Lits::union(a, b)),
        };
        out.cofinite = cofinite;
        out
    }

    fn union(a: &Lits, b: &Lits) -> Lits {
        let (large, small) = if a.values.len() >= b.values.len() {
            (a, b)
        } else {
            (b, a)
        };
        let mut out = large.clone();
        for v in &small.values {
            out.insert(v);
        }
        out
    }

    fn meet(a: &Lits, b: &Lits) -> Lits {
        let (large, small) = if a.values.len() >= b.values.len() {
            (a, b)
        } else {
            (b, a)
        };
        let mut out = Lits::default();
        for v in small.values.iter().filter(|&v| large.values.contains(v)) {
            out.insert(v);
        }
        out
    }

    /// The literals of `a` not in `b`.
    fn minus(a: &Lits, b: &Lits) -> Lits {
        if a.values.len() <= b.values.len() {
            let mut out = Lits::default();
            for v in a.values.iter().filter(|&v| !b.values.contains(v)) {
                out.insert(v);
            }
            return out;
        }
        let mut out = a.clone();
        for v in &b.values {
            out.remove(v);
        }
        out
    }

    fn not(&self) -> Lits {
        Lits {
            cofinite: !self.cofinite,
            ..self.clone()
        }
    }
}

impl AtomPart {
    fn all() -> AtomPart {
        AtomPart {
            bare: true,
            payload: Type::payloads(),
        }
    }

    fn none() -> AtomPart {
        AtomPart {
            bare: false,
            payload: Type::empty(),
        }
    }

    fn zip(&self, other: &AtomPart, op: Op) -> AtomPart {
        AtomPart {
            bare: match op {
                Op::Or => self.bare || other.bare,
                Op::And => self.bare && other.bare,
            },
            payload: self.payload.zip(&other.payload, op),
        }
    }

    fn not(&self) -> AtomPart {
        AtomPart {
            bare: !self.bare,
            payload: Type::payloads() - &self.payload,
        }
    }
}

impl Atoms {
    fn get(&self, name: &str) -> AtomPart {
        match self.names.get(name) {
            Some(p) => p.clone(),
            None if self.cofinite => AtomPart::all(),
            None => AtomPart::none(),
        }
    }

    fn entry(name: &str, p: &AtomPart) -> u64 {
        mix(
            mix(bytes(name.as_bytes()), u64::from(p.bare)),
            p.payload.digest(),
        )
    }

    /// Gives `name` the part `p`, unlisting it when `p` is what an unlisted name has.
    fn set(&mut self, name: &Arc<str>, p: AtomPart) {
        if let Some(old) = self.names.remove(name) {
            self.sum = self.sum.wrapping_sub(Atoms::entry(name, &old));
        }
        let default = if self.cofinite {
            AtomPart::all()
        } else {
            AtomPart::none()
        };
        if p != default {
            self.sum = self.sum.wrapping_add(Atoms::entry(name, &p));
            self.names.insert(name.clone(), p);
        }
    }

    /// The parts combined by `op`. A name the smaller map does not list has every payload or
    /// none, and a part combined with all or none is itself, all or none: so the result is the
    /// larger map, or nothing, changed at the smaller map's names. When it is the larger map,
    /// only the names where the two differ change, since a part combined with itself is itself;
    /// those are found by walking the smaller map, `O(s log l)` steps for its `s` names and the
    /// larger's `l`, or by a diff of the two maps, which skips the nodes they share, so that
    /// two sets grown from one another, as a chain of merged failures grows the set of its
    /// members beside its loose atoms (ERRS-precise), differ in `O(d log l)` for their `d`
    /// differing names. The two walks advance in turn and the first to finish is used:
    // Complexity tradeoff: twice the cheaper walk, so `O(min(s, d + log l) log l)`, against
    // `O(s log l)` alone, which is quadratic for a chain of `n` such unions.
    fn zip(&self, other: &Atoms, op: Op) -> Atoms {
        let cofinite = match op {
            Op::Or => self.cofinite || other.cofinite,
            Op::And => self.cofinite && other.cofinite,
        };
        let (large, small) = if self.names.len() >= other.names.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut out = match (op, small.cofinite) {
            (Op::Or, false) | (Op::And, true) => large.clone(),
            _ => {
                let mut out = Atoms {
                    cofinite,
                    ..Atoms::default()
                };
                for (n, p) in &small.names {
                    out.set(n, large.get(n).zip(p, op));
                }
                return out;
            }
        };
        out.cofinite = cofinite;
        let mut walk = small.names.iter();
        let mut diff = large.names.diff(&small.names);
        let mut differ = Vec::new();
        loop {
            if walk.next().is_none() {
                for (n, p) in &small.names {
                    out.set(n, large.get(n).zip(p, op));
                }
                return out;
            }
            match diff.next() {
                None => break,
                Some(DiffItem::Add(n, p) | DiffItem::Update { new: (n, p), .. }) => {
                    differ.push((n, p));
                }
                Some(DiffItem::Remove(..)) => {}
            }
        }
        for (n, p) in differ {
            out.set(n, large.get(n).zip(p, op));
        }
        out
    }

    fn not(&self) -> Atoms {
        let mut out = Atoms {
            cofinite: !self.cofinite,
            ..Atoms::default()
        };
        for (n, p) in &self.names {
            out.set(n, p.not());
        }
        out
    }
}

impl Tuples {
    fn literal(items: Vec<Type>) -> Tuples {
        Tuples {
            rest: false,
            lens: BTreeMap::from([(items.len(), Part::literal(Row::new(items)))]),
        }
    }

    fn get(&self, len: usize) -> Part<Row> {
        match self.lens.get(&len) {
            Some(b) => b.clone(),
            None => Part::leaf(self.rest),
        }
    }

    /// Drops the lengths whose part is what an unlisted length has.
    fn normal(rest: bool, lens: BTreeMap<usize, Part<Row>>) -> Tuples {
        let lens = lens
            .into_iter()
            .filter(|(_, b)| b.is_leaf() != Some(rest))
            .collect();
        Tuples { rest, lens }
    }

    fn zip(&self, other: &Tuples, op: Op) -> Tuples {
        let rest = match op {
            Op::Or => self.rest || other.rest,
            Op::And => self.rest && other.rest,
        };
        let lens = self
            .lens
            .keys()
            .chain(other.lens.keys())
            .map(|n| (*n, self.get(*n).zip(&other.get(*n), op)))
            .collect();
        Tuples::normal(rest, lens)
    }

    fn not(&self) -> Tuples {
        let lens = self.lens.iter().map(|(n, b)| (*n, b.not())).collect();
        Tuples::normal(!self.rest, lens)
    }

    /// Whether `f` holds of every tuple type in a part.
    fn atoms(&self, f: &mut impl FnMut(&Row) -> bool) -> bool {
        self.lens.values().all(|b| b.atoms(f))
    }
}

impl Not for &Type {
    type Output = Type;
    fn not(self) -> Type {
        let p = self.p();
        Type::new(Parts {
            digest: 0,
            bools: !p.bools & 3,
            ints: p.ints.not(),
            rats: p.rats.not(),
            floats: p.floats.not(),
            strings: p.strings.not(),
            atoms: p.atoms.not(),
            tuples: p.tuples.not(),
            structs: !p.structs,
            morphisms: p.morphisms.not(),
        })
    }
}

impl Not for Type {
    type Output = Type;
    fn not(self) -> Type {
        !&self
    }
}

impl BitOr for &Type {
    type Output = Type;
    fn bitor(self, other: &Type) -> Type {
        self.zip(other, Op::Or)
    }
}

impl BitAnd for &Type {
    type Output = Type;
    fn bitand(self, other: &Type) -> Type {
        self.zip(other, Op::And)
    }
}

/// The difference `a \ b`, which is `a & !b`.
impl Sub<&Type> for &Type {
    type Output = Type;
    fn sub(self, other: &Type) -> Type {
        self & &!other
    }
}

impl BitOr for Type {
    type Output = Type;
    fn bitor(self, other: Type) -> Type {
        &self | &other
    }
}

impl BitAnd for Type {
    type Output = Type;
    fn bitand(self, other: Type) -> Type {
        &self & &other
    }
}

impl Sub<&Type> for Type {
    type Output = Type;
    fn sub(self, other: &Type) -> Type {
        &self - other
    }
}

/// The parts as a prefix expression, the form of the syntax tree's types: `_` is every value
/// and `(|)` none; `int` every integer, `(\ int 3)` every one but 3; `#_` every atom; `(#a _)`
/// the atoms `#a` with any payload; `(tuple A B)`, `(! X)`, `(& X Y)`, and `tuple`, `struct`
/// and `morphism` every value of those universes; `(-> K V)` exact, `(->? K V)` with no
/// guarantee, `(-> L U V)` otherwise.
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.rope().strs().try_for_each(|s| f.write_str(s))
    }
}

/// Text made of pieces, each a string or a rope, so that a type's text holds the texts of the
/// types inside it without copying them. Ropes compare as their texts do.
#[derive(Clone)]
struct Rope(Arc<[Piece]>);

enum Piece {
    Str(String),
    Rope(Rope),
}

impl From<&str> for Piece {
    fn from(s: &str) -> Piece {
        Piece::Str(s.into())
    }
}

impl From<String> for Piece {
    fn from(s: String) -> Piece {
        Piece::Str(s)
    }
}

impl From<Rope> for Piece {
    fn from(r: Rope) -> Piece {
        Piece::Rope(r)
    }
}

/// The rope of the pieces given.
macro_rules! rope {
    ($($p:expr),* $(,)?) => {
        Rope(Arc::from(vec![$(Piece::from($p)),*]))
    };
}

/// The ropes inside are freed in a loop, as a type's parts are.
impl Drop for Rope {
    fn drop(&mut self) {
        if let Some(pieces) = Arc::get_mut(&mut self.0) {
            for p in pieces {
                if let Piece::Rope(_) = p
                    && let Piece::Rope(r) = std::mem::replace(p, Piece::Str(String::new()))
                {
                    free(Freed::Rope(r));
                }
            }
        }
    }
}

impl Rope {
    /// The pieces in order.
    fn cat(pieces: impl IntoIterator<Item = Piece>) -> Rope {
        Rope(pieces.into_iter().collect())
    }

    /// `head`, then the items with `sep` between them, then `tail`.
    fn joined(head: &str, items: impl IntoIterator<Item = Rope>, sep: &str, tail: &str) -> Rope {
        let mut pieces = vec![Piece::from(head)];
        for (k, i) in items.into_iter().enumerate() {
            if k > 0 {
                pieces.push(Piece::from(sep));
            }
            pieces.push(Piece::from(i));
        }
        pieces.push(Piece::from(tail));
        Rope(Arc::from(pieces))
    }

    /// `head`, then each item after a space, then `)`.
    fn listed(head: &str, items: impl IntoIterator<Item = Rope>) -> Rope {
        let mut pieces = vec![Piece::from(head)];
        for i in items {
            pieces.extend([Piece::from(" "), Piece::from(i)]);
        }
        pieces.push(Piece::from(")"));
        Rope(Arc::from(pieces))
    }

    /// The strings in order, read with a stack of their own, since a rope is as deep as its
    /// type.
    fn strs(&self) -> impl Iterator<Item = &str> + '_ {
        let mut stack = vec![self.0.iter()];
        std::iter::from_fn(move || {
            loop {
                match stack.last_mut()?.next() {
                    None => _ = stack.pop(),
                    Some(Piece::Str(s)) => return Some(s.as_str()),
                    Some(Piece::Rope(r)) => stack.push(r.0.iter()),
                }
            }
        })
    }
}

impl PartialEq for Rope {
    fn eq(&self, other: &Rope) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for Rope {}

impl PartialOrd for Rope {
    fn partial_cmp(&self, other: &Rope) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// As the texts' bytes compare, reading them only up to where they differ.
impl Ord for Rope {
    fn cmp(&self, other: &Rope) -> std::cmp::Ordering {
        (self.strs().flat_map(str::bytes)).cmp(other.strs().flat_map(str::bytes))
    }
}

/// The making of a type's text, which [`Type::rope`] does in a loop with its own stack, as a
/// type can be deeper than the call stack.
#[derive(Default)]
struct Showing {
    /// The texts made so far for types that keep none, such as the complement of a payload,
    /// which `show` builds anew at each try.
    made: BTreeMap<Type, Rope>,
    /// The types inside whose text the last try of `show` found missing.
    missing: Vec<Type>,
}

thread_local! {
    /// The making of a text under way on this thread, if any.
    static SHOWING: RefCell<Option<Showing>> = const { RefCell::new(None) };
}

/// Ends the making of a text, also when it panics.
struct EndShowing;

impl Drop for EndShowing {
    fn drop(&mut self) {
        SHOWING.with_borrow_mut(|s| *s = None);
    }
}

impl Type {
    /// The text as a rope, made once, which holds the ropes of the types inside without copying
    /// them, so that a type nested deep takes time linear in its text. The texts are made in a
    /// loop: a try of `show`, or of a recursive node's naming, that finds a text inside missing
    /// gives up, the types it named are made first, and the try is made again, so each type is
    /// tried at most twice.
    fn rope(&self) -> Rope {
        if let Some(r) = self.text().get() {
            return r.clone();
        }
        let inside = SHOWING.with_borrow_mut(|s| {
            s.as_mut().map(|s| match s.made.get(self) {
                Some(r) => Some(r.clone()),
                None => {
                    s.missing.push(self.clone());
                    None
                }
            })
        });
        match inside {
            Some(Some(r)) => r,
            // A placeholder: the try that asked for it is thrown away.
            Some(None) => rope![],
            None => self.make_rope(),
        }
    }

    /// Where the text is kept once made: a recursive node's name, or the text of its parts.
    fn text(&self) -> &OnceLock<Rope> {
        match &*self.0 {
            Node::Parts(_, shown) => &shown.0,
            Node::Rec(r) => &r.name,
        }
    }

    /// The loop of [`Type::rope`], from the outermost type whose text is asked for. A recursive
    /// node is an item like any other, since its name holds the texts of its arguments, which
    /// can be recursive nodes in turn: `Tree(Tree(int))`.
    fn make_rope(&self) -> Rope {
        SHOWING.with_borrow_mut(|s| *s = Some(Showing::default()));
        let _end = EndShowing;
        let mut stack = vec![self.clone()];
        while let Some(t) = stack.last() {
            let text = t.text();
            let made = SHOWING.with_borrow(|s| s.as_ref().and_then(|s| s.made.get(t).cloned()));
            if let Some(r) = made {
                let _ = text.set(r);
            }
            if text.get().is_some() {
                stack.pop();
                continue;
            }
            let r = match &*t.0 {
                Node::Parts(p, _) => t.show(p),
                Node::Rec(rec) => (rec.naming)(),
            };
            let missing = SHOWING.with_borrow_mut(|s| {
                std::mem::take(&mut s.as_mut().expect("the making is under way").missing)
            });
            if missing.is_empty() {
                let _ = text.set(r.clone());
                let t = stack.pop().expect("the stack holds `t`");
                SHOWING.with_borrow_mut(|s| {
                    s.as_mut()
                        .expect("the making is under way")
                        .made
                        .insert(t, r)
                });
            } else {
                stack.extend(missing);
            }
        }
        self.text().get().expect("the loop made the text").clone()
    }

    fn show(&self, p: &Parts) -> Rope {
        if *self == Type::top() {
            return rope!["_"];
        }
        let mut items: Vec<Rope> = Vec::new();
        match p.bools {
            1 => items.push(rope!["false"]),
            2 => items.push(rope!["true"]),
            3 => items.push(rope!["bool"]),
            _ => {}
        }
        for (name, l) in [
            ("int", &p.ints),
            ("rat", &p.rats),
            ("f64", &p.floats),
            ("String", &p.strings),
        ] {
            match (l.cofinite, l.values.is_empty()) {
                (true, true) => items.push(rope![name]),
                (true, false) => items.push(rope![format!("(\\ {name} {})", spaced(&l.values))]),
                (false, _) => items.extend(l.values.iter().map(|v| rope![lit_text(v)])),
            }
        }
        let atom = |name: &str, part: &AtomPart| {
            let mut out = Vec::new();
            if part.bare {
                out.push(rope![format!("#{name}")]);
            }
            if part.payload == Type::payloads() {
                out.push(rope![format!("(#{name} _)")]);
            } else if part.payload != Type::empty() {
                out.push(rope![format!("(#{name} "), part.payload.rope(), ")"]);
            }
            out
        };
        if p.atoms.cofinite {
            let except: Vec<Rope> = p
                .atoms
                .names
                .iter()
                .flat_map(|(n, part)| atom(n, &part.not()))
                .collect();
            match except.is_empty() {
                true => items.push(rope!["#_"]),
                false => items.push(Rope::listed("(\\ #_", except)),
            }
        } else {
            items.extend(p.atoms.names.iter().flat_map(|(n, part)| atom(n, part)));
        }
        tuples(&mut items, &p.tuples);
        if p.structs {
            items.push(rope!["struct"]);
        }
        let morphism = |m: &Morphism| {
            let (p, v) = (m.permission.rope(), m.value.rope());
            if m.guarantee == m.permission {
                rope!["(-> ", p, " ", v, ")"]
            } else if m.guarantee == Type::empty() {
                rope!["(->? ", p, " ", v, ")"]
            } else {
                rope!["(-> ", m.guarantee.rope(), " ", p, " ", v, ")"]
            }
        };
        clauses(&mut items, &rope!["morphism"], &p.morphisms, &morphism);
        union(items)
    }
}

/// `(| a b …)`, or the one item alone.
fn union(mut items: Vec<Rope>) -> Rope {
    match items.len() {
        1 => items.remove(0),
        _ => Rope::listed("(|", items),
    }
}

fn spaced(vs: &OrdSet<Value>) -> String {
    vs.iter().map(lit_text).collect::<Vec<_>>().join(" ")
}

/// The items of a tuple part. With `rest`, it is every tuple outside its complement's items.
fn tuples(items: &mut Vec<Rope>, t: &Tuples) {
    if t.rest {
        let mut except = Vec::new();
        tuples(&mut except, &t.not());
        items.push(match except.len() {
            0 => rope!["tuple"],
            _ => rope!["(& tuple (! ", union(except), "))"],
        });
        return;
    }
    let tuple = |t: &Row| Rope::listed("(tuple", t.iter().map(Type::rope));
    for (len, b) in &t.lens {
        clauses(items, &tuple(&Row::new(vec![Type::top(); *len])), b, &tuple);
    }
}

/// One item per clause of a diagram's decision list (`Bdd::list`), whose form does not depend
/// on the order of the atoms, which is that of their digests (step BDD-atom-order): each
/// literal of a block of value `true`, with the complements of the literals of the blocks of
/// value `false` before it, and, when the default is `true`, the complements of them all. A
/// clause is the intersection of the atoms it takes, or `all` when it takes none, and the
/// complements of those it refuses. The items, and the atoms within each, are sorted as text.
/// A part kept as an expression is its connective applied to the items of its operands, the
/// two operands of a union or intersection sorted as text.
fn clauses<A: bdd::Literal>(
    items: &mut Vec<Rope>,
    all: &Rope,
    part: &Part<A>,
    show: &impl Fn(&A) -> Rope,
) {
    let b = match part.view() {
        Ok(b) => b,
        Err(form) => {
            let item = |p: &Part<A>| {
                let mut sub = Vec::new();
                clauses(&mut sub, all, p, show);
                match sub.is_empty() {
                    true => rope!["(|)"],
                    false => union(sub),
                }
            };
            items.push(match form {
                Form::Not(a) => rope!["(& ", all.clone(), " (! ", item(a), "))"],
                Form::Or(a, b) => {
                    let (x, y) = sorted_pair(item(a), item(b));
                    rope!["(| ", x, " ", y, ")"]
                }
                Form::And(a, b) => {
                    let (x, y) = sorted_pair(item(a), item(b));
                    rope!["(& ", x, " ", y, ")"]
                }
            });
            return;
        }
    };
    let list = b.list();
    let mut found = Vec::new();
    // A clause: the atoms `pos` taken, those `neg` refused, and each literal of `zeros` false.
    let mut clause = |pos: &[&A], neg: &[&A], zeros: &[(&A, bool)]| {
        let taken = (pos.iter().copied()).chain(zeros.iter().filter(|z| !z.1).map(|z| z.0));
        let mut lits: Vec<Rope> = taken.map(show).collect();
        lits.sort();
        if lits.is_empty() {
            lits.push(all.clone());
        }
        let not = (neg.iter().copied()).chain(zeros.iter().filter(|z| z.1).map(|z| z.0));
        let mut refused: Vec<Rope> = not.map(|n| rope!["(! ", show(n), ")"]).collect();
        refused.sort();
        lits.extend(refused);
        match lits.len() {
            1 => found.push(lits.remove(0)),
            _ => found.push(Rope::listed("(&", lits)),
        }
    };
    // The literals of the blocks of value `false` so far, each with whether it is taken.
    let mut zeros: Vec<(&A, bool)> = Vec::new();
    for (value, lits) in &list.blocks {
        if *value {
            for (a, taken) in lits {
                match taken {
                    true => clause(&[a], &[], &zeros),
                    false => clause(&[], &[a], &zeros),
                }
            }
        } else {
            zeros.extend(lits.iter().map(|(a, t)| (a, *t)));
        }
    }
    if list.tail {
        clause(&[], &[], &zeros);
    }
    found.sort();
    items.extend(found);
}

/// The two texts in the order of their bytes.
fn sorted_pair(x: Rope, y: Rope) -> (Rope, Rope) {
    if x <= y { (x, y) } else { (y, x) }
}

/// The values of a finite type, one at a time, from [`Type::each_value`].
pub struct Values {
    /// One maker per type the values are built from, each after the types in its boxes, the
    /// listed type last.
    makers: Vec<Maker>,
    /// How many values of the listed type have been given.
    given: usize,
}

/// The values of one type of a [`Values`], made one at a time on demand and kept, since every
/// box that reads the type reads them by position.
struct Maker {
    ty: Type,
    /// Each box with the maker of each of its components.
    boxes: Vec<(Vec<usize>, Row)>,
    /// The rows of the type's diagrams, each with the maker of each of its types, if any.
    rows: BTreeMap<Row, Vec<Option<usize>>>,
    /// Per length, the type's part of that length with its rows by the values they may hold.
    by_value: BTreeMap<usize, RowIndex>,
    /// Per length, the boxes by the values they may hold.
    by_box: BTreeMap<usize, BoxIndex>,
    /// The box being listed.
    next: usize,
    at: At,
    /// The values made so far: the scalars and bare atoms, then the tuples.
    made: Vec<Value>,
    /// Whether every value has been made.
    done: bool,
}

/// Where a [`Maker`] is in its box.
enum At {
    /// Before the box: its components are not yet known to have a value.
    Start,
    /// At a position, one per component, whose values are all made.
    Tuple(Vec<usize>),
    /// Past a position, before moving to the next one.
    Past(Vec<usize>),
}

/// A value a maker waits for: the maker and the position.
type Need = (usize, usize);

/// The scalars and bare atoms of `p`, as a maker lists them.
fn scalars(p: &Parts) -> Vec<Value> {
    let mut made: Vec<Value> = [false, true]
        .into_iter()
        .filter(|&b| p.bools & (1 << u8::from(b)) != 0)
        .map(Value::Bool)
        .collect();
    for lits in [&p.ints, &p.rats, &p.floats, &p.strings] {
        made.extend(lits.values.iter().cloned());
    }
    made.extend(
        p.atoms
            .names
            .iter()
            .filter(|(_, a)| a.bare)
            .map(|(name, _)| Value::atom(name)),
    );
    made
}

/// What a column's type names of the values it may hold, at any depth of first components: a
/// value's component at depth 0 is the value, and at depth `d + 1` the first component of its
/// component at depth `d`.
struct Filed {
    /// The scalars and bare atoms the types at some depth list, and the empty tuple where they
    /// hold it, sorted and distinct: a value none of whose components is a key is in the type
    /// only as its kinds decide ([`kind_status`]).
    keys: Vec<Value>,
    /// Whether every value of the type has a component that is a key.
    listed: bool,
}

/// The types a value's first component is read in, below the column type `t`: the first
/// columns of its boxes (`Type::boxes`) with `by_boxes`, when they hold all its tuples, which
/// are finite where `t` is; otherwise those of every tuple type of its parts. `push` takes each.
/// Whether the tuples of `t` are all in tuple types these first columns are of.
fn firsts(t: &Type, by_boxes: bool, keys: &mut Vec<Value>, mut push: impl FnMut(&Type)) -> bool {
    if let Some(boxes) = by_boxes.then(|| t.boxes()).flatten() {
        for r in &boxes {
            match r.first() {
                Some(c) => push(c),
                None => keys.push(Value::tuple(Vec::new())),
            }
        }
        return true;
    }
    let p = t.p();
    let mut listed = !p.tuples.rest;
    for (&len, part) in &p.tuples.lens {
        if len == 0 {
            if part.eval(&|_| true) {
                keys.push(Value::tuple(Vec::new()));
            }
            continue;
        }
        // A tuple in no tuple type of the part, which the part holds when every tuple type is
        // taken as false, has a first component outside their first columns.
        listed &= !part.eval(&|_| false);
        for r in part.distinct_atoms() {
            push(&r[0]);
        }
    }
    listed
}

/// The keys of the column type `t` ([`Filed`]): each type it reaches through first columns
/// ([`firsts`]) is visited once, kept in a visited set, so a type recursive in its first
/// component ends too. A key is not tied to its depth: a component equal to a key at another
/// depth only makes its tuple type read.
fn file(t: &Type, by_boxes: bool) -> Filed {
    let (mut keys, mut listed) = (Vec::new(), true);
    let mut seen: HashSet<Type> = HashSet::from([t.clone()]);
    let mut todo = vec![t.clone()];
    while let Some(t) = todo.pop() {
        let p = t.p();
        for b in [false, true] {
            if p.bools & (1 << u8::from(b)) != 0 {
                keys.push(Value::Bool(b));
            }
        }
        for lits in [&p.ints, &p.rats, &p.floats, &p.strings] {
            keys.extend(lits.values.iter().cloned());
            listed &= !lits.cofinite;
        }
        // A name listed is an exception to the names not listed.
        let atoms = &p.atoms;
        keys.extend(
            atoms
                .names
                .iter()
                .filter(|(_, a)| a.bare != atoms.cofinite)
                .map(|(name, _)| Value::atom(name)),
        );
        listed &= !atoms.cofinite;
        listed &= firsts(&t, by_boxes, &mut keys, |c| {
            if seen.insert(c.clone()) {
                todo.push(c.clone());
            }
        });
    }
    keys.sort();
    keys.dedup();
    Filed { keys, listed }
}

/// The kind of a value, as far as the kinds decide whether a type holds a value none of whose
/// components is a key of it ([`Filed`]).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Kind {
    Bool,
    Int,
    Rat,
    Float,
    Str,
    Atom,
    Tuple(usize),
    /// A path or a function, which no maker makes.
    Other,
}

/// The kinds of `x` and of its first components, depth by depth.
fn kinds(x: &Value) -> Vec<Kind> {
    let mut out = Vec::new();
    let mut x = x;
    loop {
        out.push(match x {
            Value::Bool(_) => Kind::Bool,
            Value::Int(_) | Value::Big(_) => Kind::Int,
            Value::Rat(_) => Kind::Rat,
            Value::Float(_) => Kind::Float,
            Value::Str(_) => Kind::Str,
            Value::Atom(_) => Kind::Atom,
            Value::Tuple(items) => Kind::Tuple(items.len()),
            Value::Path(_) | Value::Family(_) => Kind::Other,
        });
        match x {
            Value::Tuple(items) if !items.is_empty() => x = &items[0],
            _ => return out,
        }
    }
}

/// Whether `t` holds a value of kind `kind` none of whose components is a key of `t`, when the
/// kind decides it; `first` gives the same for a first column of `t` and the next kind. A
/// tuple outside every first column of its tuple types is in `t` as the part is with every
/// tuple type false; one in the first column of a part's only tuple type, of length 1, is in
/// it as its component is in that column; any other is not decided by kinds.
fn kind_status(t: &Type, kind: &Kind, first: impl Fn(&Type) -> Option<bool>) -> Option<bool> {
    let p = t.p();
    match kind {
        Kind::Bool => Some(false),
        Kind::Int => Some(p.ints.cofinite),
        Kind::Rat => Some(p.rats.cofinite),
        Kind::Float => Some(p.floats.cofinite),
        Kind::Str => Some(p.strings.cofinite),
        Kind::Atom => Some(p.atoms.cofinite),
        Kind::Other => None,
        Kind::Tuple(len) => match p.tuples.lens.get(len) {
            None => Some(p.tuples.rest),
            // The empty tuple is a key where a type holds it.
            Some(_) if *len == 0 => Some(false),
            Some(part) => {
                let rows = part.distinct_atoms();
                let firsts: Vec<Option<bool>> = rows.iter().map(|r| first(&r[0])).collect();
                if firsts.iter().all(|s| *s == Some(false)) {
                    Some(part.eval(&|_| false))
                } else if *len == 1
                    && rows.len() == 1
                    && part.eval(&|_| true)
                    && !part.eval(&|_| false)
                {
                    firsts[0]
                } else {
                    None
                }
            }
        },
    }
}

/// Tuple types of one length by the values they may hold, so that the tuple types that may
/// hold a tuple are read by one lookup per component and per depth the component reaches. A
/// component none of whose depths is a key of a filed tuple type's column is in the column's
/// type only as its kinds decide, since `Type::contains` compares scalars by the order of
/// values and a tuple by its components, and a maker makes no atom with fields and no path.
struct Keyed {
    /// Per column, each key with the positions of the tuple types filed under it.
    by: Vec<BTreeMap<Value, Vec<usize>>>,
}

impl Keyed {
    fn new(len: usize) -> Keyed {
        Keyed {
            by: vec![BTreeMap::new(); len],
        }
    }

    /// Files the tuple type at position `at` under the keys of its column `j`.
    fn add(&mut self, at: usize, j: usize, keys: &[Value]) {
        for v in keys {
            self.by[j].entry(v.clone()).or_default().push(at);
        }
    }

    /// The positions of the filed tuple types under a key of the tuple `v`, at any depth,
    /// sorted and distinct. A key is a scalar, a bare atom or the empty tuple, so of a
    /// column's components at each depth only the innermost can be one.
    fn at(&self, v: &[Value]) -> Vec<usize> {
        let mut at = Vec::new();
        self.extend_at(v, false, &mut at);
        at.sort_unstable();
        at.dedup();
        at
    }

    /// Adds to `at` the positions [`Keyed::at`] gives, unsorted; with `tuples`, only those
    /// under a key of a column whose component is a tuple with components.
    fn extend_at(&self, v: &[Value], tuples: bool, at: &mut Vec<usize>) {
        for (by, x) in self.by.iter().zip(v) {
            if by.is_empty() || tuples && whole(x) {
                continue;
            }
            // No key is a tuple with components, so only the last component is looked up.
            let mut x = x;
            while let Value::Tuple(items) = x {
                match items.first() {
                    Some(c) => x = c,
                    None => break,
                }
            }
            at.extend(by.get(x).into_iter().flatten());
        }
    }
}

/// Whether `x` is a number, a string, a bool or the empty tuple: a value with no parts a
/// column of a row reads by another key than its own, so a listed column holds it exactly
/// when it is one of the column's keys and the column holds that key. Atoms are left out:
/// one with arguments is held by its arguments, and a bare one is read by its key ([`Keyed`]).
fn whole(x: &Value) -> bool {
    match x {
        Value::Tuple(items) => items.as_slice().is_empty(),
        Value::Bool(_) | Value::Int(_) | Value::Big(_) | Value::Rat(_) => true,
        Value::Float(_) | Value::Str(_) => true,
        _ => false,
    }
}

/// The keys of each column of `row` ([`file()`]), and the column with fewest keys among those
/// that list every value they hold: a tuple none of whose components there is a key is not in
/// the row. A column is first filed by its tuple types, and by its boxes only when that does
/// not list its values, since a box is made by walking the type's diagram.
fn file_row(row: &Row) -> (Vec<Filed>, Option<usize>) {
    let filed: Vec<Filed> = row
        .iter()
        .map(|t| {
            let f = file(t, false);
            if f.listed {
                return f;
            }
            let g = file(t, true);
            if g.listed { g } else { f }
        })
        .collect();
    let fewest = (0..filed.len())
        .filter(|&j| filed[j].listed)
        .min_by_key(|&j| filed[j].keys.len());
    (filed, fewest)
}

/// How a row of a [`RowIndex`] is filed.
enum Filing {
    /// Under the keys of a column that lists every value it holds: a tuple with no key there
    /// is not in the row.
    Listed,
    /// Under the keys of every column, as the open row at this position of `RowIndex::open`:
    /// a tuple with no key in any column is in the row as its class decides ([`Class`]).
    Open(usize),
}

/// The value of the row at `i` of `filing` on a tuple with no key of it; `open` gives each
/// open row's, for the tuple's class.
fn row_default(filing: &[Filing], open: &[bool], i: usize) -> bool {
    match filing[i] {
        Filing::Listed => false,
        Filing::Open(o) => open[o],
    }
}

/// A part of a tuple's [`Spine`].
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Bone {
    /// A tuple of this length along the first components.
    Len(usize),
    /// A component other than the first, by its sequence: the same sequence is the same value.
    Seq(bool, Id),
    /// A component other than the first that is no sequence.
    Value(Value),
    /// The last of the first components, a scalar or bare atom of this kind, which no row the
    /// class is read for has as a key ([`erase`]).
    Erased(Kind),
}

/// Per column of a tuple, its components along first components ([`Keyed::at`]), each with
/// its other components, the last one erased where it can be: tuples of one spine are in each
/// open row with no key of theirs alike.
type Spine = Vec<Vec<Bone>>;

/// Whether a value is erased when last along the first components, by its kind: a scalar or
/// bare atom other than a boolean. Booleans and the empty tuple are kept, as is anything a
/// maker does not make.
fn erasable(x: &Value) -> Option<Kind> {
    match x {
        Value::Int(_) | Value::Big(_) => Some(Kind::Int),
        Value::Rat(_) => Some(Kind::Rat),
        Value::Float(_) => Some(Kind::Float),
        Value::Str(_) => Some(Kind::Str),
        Value::Atom(a) if a.args.as_slice().is_empty() => Some(Kind::Atom),
        _ => None,
    }
}

/// The spine of the column component `x`: one walk down its first components, each other
/// component that is a sequence by its id, not its values, so a value whose parts are shared is
/// not walked, and any other by its value.
fn spine(x: &Value) -> Vec<Bone> {
    let mut out = Vec::new();
    let mut x = x;
    while let Value::Tuple(items) = x
        && let [first, rest @ ..] = items.as_slice()
    {
        out.push(Bone::Len(items.len()));
        out.extend(rest.iter().map(|y| match y {
            Value::Tuple(ys) => Bone::Seq(false, ys.id()),
            Value::Path(ys) => Bone::Seq(true, ys.id()),
            _ => Bone::Value(y.clone()),
        }));
        x = first;
    }
    out.push(match erasable(x) {
        Some(kind) => Bone::Erased(kind),
        None => Bone::Value(x.clone()),
    });
    out
}

/// A value of the kind `kind` that is not in `keys`: one of the first `keys.len() + 1`
/// candidates is not.
fn witness(kind: &Kind, keys: &BTreeSet<Value>) -> Value {
    (0..)
        .map(|n: i64| match kind {
            Kind::Int => Value::Int(n),
            Kind::Rat => Value::rat(Rat::int(n.into())),
            Kind::Float => Value::float(n as f64),
            Kind::Str => Value::str(&n.to_string()),
            _ => Value::atom(&format!("_{n}")),
        })
        .find(|w| !keys.contains(w))
        .expect("the candidates are distinct and infinitely many")
}

/// The column component `x` with the last of its first components replaced by a value of
/// its kind that no open row has as a key of the column, `keys`, when it is erasable
/// ([`erasable`]). Such a value and the one it replaces are each in a type that may read
/// that place, a type an open row reaches through first columns, as its kind decides: neither
/// is listed by one, since every scalar and bare atom such a type lists is a key. A tuple
/// type reads its components and nothing else, so an open row with no key of the tuple holds
/// the tuple and the replaced one alike. The components along first components are rebuilt
/// from the innermost out, without recursion; the others are shared.
fn erase(x: &Value, keys: &BTreeSet<Value>) -> Value {
    let mut chain: Vec<&Items> = Vec::new();
    let mut x = x;
    while let Value::Tuple(items) = x
        && let Some(first) = items.as_slice().first()
    {
        chain.push(items);
        x = first;
    }
    let mut out = match erasable(x) {
        Some(kind) => witness(&kind, keys),
        None => x.clone(),
    };
    for items in chain.into_iter().rev() {
        let mut vs = items.as_slice().to_vec();
        vs[0] = out;
        out = Value::tuple(vs);
    }
    out
}

/// What a tuple's class is read by: its shape, and per column an open row absorbs ([`Open`])
/// whose component is a scalar ([`whole`]), the region of that scalar there.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct ClassKey {
    shape: Shape,
    regions: Vec<Option<usize>>,
}

/// The shape part of a [`ClassKey`].
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Shape {
    /// The kinds of the components along first components, in the columns an open row has
    /// ([`kinds`]), when they decide every open row.
    Kinds(Vec<Vec<Kind>>),
    /// The tuple's spine, when the kinds leave an open row unknown.
    Spine(Spine),
}

/// A row of a [`RowIndex`] that a tuple with no key of it may be in.
struct Open {
    /// Per column, the column type and the types below it by depth, made as deep as a class
    /// has read: depth `d + 1` holds the first columns of the tuple types of the types at
    /// depth `d`.
    levels: Vec<Vec<Vec<Type>>>,
    /// Per column, whether the row absorbs it: the column lists every value it holds, but its
    /// keys are shared by more rows than those of the columns that do not, so the row is
    /// filed by the others, and the column's value on a scalar component is read from the
    /// scalar's region ([`RowIndex::regions`]).
    absorbs: Vec<bool>,
}

/// The part of one length of a maker's type, so that a tuple is checked on a part that holds
/// only the rows it may be in. Checking each tuple on the whole part tests every row on the
/// way: in an exclusive or of `c` tuple types, built as an expression, each of its `c` values
/// was checked against all `c` types, order `c²` (LIST-parity-quad). Every row is filed by its
/// parts, as the class split does (K36): by the scalars and bare atoms its columns list, of
/// any kinds and tuple lengths, at every depth of first components. A row no column of which
/// lists every value it holds, such as one given by its complement, is open: it is filed by
/// the keys of every column, and its value on a tuple with none of them is decided once per
/// class of tuples, by the tuple's kinds where they decide it (LIST-parity-rest) and
/// otherwise by the tuple with the last of each column's first components erased. A row with
/// such a column and a column that lists its values under keys more rows share, such as each
/// `(int - (2i + 1), 0)` of a meet, is open too, and absorbs the latter (LIST-parity-tail) where the classes of its
/// regions cost no more than filing by it.
struct RowIndex {
    /// The rows of the part, sorted.
    rows: Vec<Row>,
    /// How each row is filed.
    filing: Vec<Filing>,
    /// The positions in `rows` by the values they may hold.
    keyed: Keyed,
    /// The positions in `rows` of the open rows by the keys of the columns they absorb, read
    /// for components that are tuples with components.
    absorbed: Keyed,
    /// The open rows.
    open: Vec<Open>,
    /// Per column, the keys of the open rows there ([`erase`]).
    open_keys: Vec<BTreeSet<Value>>,
    /// Per column, the region of each key of an open row that absorbs the column: scalars of
    /// one region are in each such row's column alike. A scalar that is no such key is in
    /// region 0, held by none of them.
    regions: Vec<BTreeMap<Value, usize>>,
    /// Whether an open row has a column at each position: a tuple's kinds are those of
    /// those columns' components ([`kinds`]).
    read: Vec<bool>,
    /// Per kinds of tuples, the open rows' values on a tuple of them with no key of theirs,
    /// when the kinds decide it ([`kind_status`]), the columns a row absorbs left out where
    /// their component is a scalar.
    by_kinds: HashMap<Vec<Vec<Kind>>, Vec<Option<bool>>>,
    /// Per class, the open rows' values on a tuple of it with no key of theirs, and the part
    /// restricted to ranges of `rows`.
    classes: BTreeMap<ClassKey, Class>,
}

/// The rows of a [`RowIndex`] as a class of tuples sees them.
struct Class {
    /// Per open row, its value on a tuple of the class none of whose components is a key of
    /// it.
    open: Vec<bool>,
    /// The part restricted to the rows of a range of `rows`, the rows outside the range taken
    /// as their value on a tuple with no key of theirs, made when first needed: entry 1 for
    /// the whole range, and entries `2i` and `2i + 1` for the lower and upper halves of the
    /// range of entry `i`.
    halves: HashMap<usize, Part<Row>>,
    /// The part with every row so taken, made when first needed.
    none: Option<Part<Row>>,
}

/// Whether the kinds `chain` of a component are those of a scalar ([`whole`]).
fn whole_kinds(chain: &[Kind]) -> bool {
    matches!(
        chain,
        [Kind::Bool | Kind::Int | Kind::Rat | Kind::Float | Kind::Str | Kind::Tuple(0)]
    )
}

impl RowIndex {
    fn new(len: usize, part: &Part<Row>) -> RowIndex {
        let mut rows = part.distinct_atoms();
        rows.sort();
        let filed: Vec<(Vec<Filed>, Option<usize>)> = rows.iter().map(file_row).collect();
        // How many rows each key of each column files.
        let mut count: Vec<BTreeMap<&Value, usize>> = vec![BTreeMap::new(); len];
        for (columns, _) in &filed {
            for (j, f) in columns.iter().enumerate() {
                for k in &f.keys {
                    *count[j].entry(k).or_default() += 1;
                }
            }
        }
        let share = |j: usize, f: &Filed| -> usize { f.keys.iter().map(|k| count[j][k]).sum() };
        // A row filed by a column that lists its values is in no tuple with no key there. When
        // the columns that do not list theirs file it under keys fewer rows share, it may be
        // filed by those and absorb the others.
        let mut absorbs: Vec<Option<Vec<bool>>> = filed
            .iter()
            .map(|(columns, fewest)| {
                let j = (*fewest)?;
                let unlisted = columns.iter().enumerate().filter(|(_, f)| !f.listed);
                let others: usize = unlisted.clone().map(|(k, f)| share(k, f)).sum();
                (unlisted.count() > 0 && share(j, &columns[j]) > others)
                    .then(|| columns.iter().map(|f| f.listed).collect())
            })
            .collect();
        // Per key of a column, the rows absorbing the column whose type holds the key: its
        // region. A column a row absorbs lists every value it holds, so it holds no scalar
        // that is not one of its keys.
        let regions_of = |absorbs: &[Option<Vec<bool>>], j: usize| {
            let mut by_key: BTreeMap<&Value, Vec<usize>> = BTreeMap::new();
            for (i, a) in absorbs.iter().enumerate() {
                if a.as_ref().is_some_and(|a| a[j]) {
                    for k in &filed[i].0[j].keys {
                        let rs = by_key.entry(k).or_default();
                        if rows[i][j].contains(k) {
                            rs.push(i);
                        }
                    }
                }
            }
            by_key
        };
        // Complexity tradeoff: a column is absorbed where its regions' classes cost no more
        // than filing by it: a class reads every row once, and filing reads each row of a key
        // for each tuple with it, so at least the rows of all its keys. Elsewhere the rows are
        // filed by the column; the verdicts are the same either way.
        for j in 0..len {
            let by_key = regions_of(&absorbs, j);
            let filing_cost: usize = by_key.keys().map(|k| count[j][k]).sum();
            let classes: BTreeSet<&Vec<usize>> =
                by_key.values().filter(|rs| !rs.is_empty()).collect();
            if classes.len() * rows.len() > filing_cost {
                for a in &mut absorbs {
                    if a.as_ref().is_some_and(|a| a[j]) {
                        *a = None;
                    }
                }
            }
        }
        // The regions are numbered by their rows, the empty one 0.
        let mut ids: HashMap<Vec<usize>, usize> = HashMap::from([(Vec::new(), 0)]);
        let regions: Vec<BTreeMap<Value, usize>> = (0..len)
            .map(|j| {
                regions_of(&absorbs, j)
                    .into_iter()
                    .map(|(k, rs)| {
                        let next = ids.len();
                        (k.clone(), *ids.entry(rs).or_insert(next))
                    })
                    .collect()
            })
            .collect();
        let (mut keyed, mut absorbed) = (Keyed::new(len), Keyed::new(len));
        let (mut filing, mut open, mut read) = (Vec::new(), Vec::new(), vec![false; len]);
        let mut open_keys = vec![BTreeSet::new(); len];
        for (i, ((columns, fewest), absorbs)) in filed.iter().zip(absorbs).enumerate() {
            let absorbs = match (absorbs, *fewest) {
                (Some(a), _) => a,
                (None, Some(j)) => {
                    keyed.add(i, j, &columns[j].keys);
                    filing.push(Filing::Listed);
                    continue;
                }
                (None, None) => vec![false; len],
            };
            for (j, f) in columns.iter().enumerate() {
                match absorbs[j] {
                    true => absorbed.add(i, j, &f.keys),
                    false => keyed.add(i, j, &f.keys),
                }
                open_keys[j].extend(f.keys.iter().cloned());
                read[j] = true;
            }
            filing.push(Filing::Open(open.len()));
            open.push(Open {
                levels: rows[i].iter().map(|t| vec![vec![t.clone()]]).collect(),
                absorbs,
            });
        }
        RowIndex {
            rows,
            filing,
            keyed,
            absorbed,
            open,
            open_keys,
            regions,
            read,
            by_kinds: HashMap::new(),
            classes: BTreeMap::new(),
        }
    }

    /// The open rows' values on a tuple of the kinds `class` with no key of theirs, where the
    /// kinds decide them, leaving out the columns a row absorbs whose component is a scalar.
    /// Each column's types are made to the depth of the kinds and read deepest first, each
    /// type once per column and depth for all the open rows.
    fn by_kinds(&mut self, class: &[Vec<Kind>]) -> Vec<Option<bool>> {
        let mut memo: Vec<HashMap<(usize, Type), Option<bool>>> =
            vec![HashMap::new(); self.read.len()];
        self.open
            .iter_mut()
            .map(|row| {
                let mut value = Some(true);
                for (j, levels) in row.levels.iter_mut().enumerate() {
                    let (chain, memo) = (&class[j], &mut memo[j]);
                    if row.absorbs[j] && whole_kinds(chain) {
                        continue;
                    }
                    while levels.len() < chain.len() {
                        let mut next = Vec::new();
                        let mut here: HashSet<Type> = HashSet::new();
                        for t in levels.last().expect("the column type is at depth 0") {
                            firsts(t, false, &mut Vec::new(), |c| {
                                if here.insert(c.clone()) {
                                    next.push(c.clone());
                                }
                            });
                        }
                        if next.is_empty() {
                            break;
                        }
                        levels.push(next);
                    }
                    for k in (0..levels.len().min(chain.len())).rev() {
                        for t in &levels[k] {
                            if memo.contains_key(&(k, t.clone())) {
                                continue;
                            }
                            let first = |c: &Type| memo.get(&(k + 1, c.clone())).copied().flatten();
                            let s = kind_status(t, &chain[k], first);
                            memo.insert((k, t.clone()), s);
                        }
                    }
                    let s = memo.get(&(0, levels[0][0].clone())).copied().flatten();
                    value = match (value, s) {
                        (Some(false), _) | (_, Some(false)) => Some(false),
                        (None, _) | (_, None) => None,
                        _ => Some(true),
                    };
                }
                value
            })
            .collect()
    }

    /// Whether the tuple `v` is in `part`, the part indexed; `fits` tells whether a row holds
    /// `v`. The part is restricted, for the class of `v`, to the smallest range of halves that
    /// holds every row of `rows` that has a key of `v`: `O(log n)` steps for `n` rows, each
    /// restriction made once per class, and one check of the restricted part. A tuple's kinds
    /// decide most open rows, and are its shape when they decide all; when they leave one
    /// unknown, as for a column of pairs whose first column is given by its complement, the
    /// shape is the tuple's spine ([`spine`]), and each row the kinds leave unknown is read
    /// once, on the tuple erased ([`erase`]), which holds for every tuple of the spine with no
    /// key of the row. A column a row absorbs is read on the class's scalar there, which is in
    /// the column as every scalar of its region is.
    // Complexity tradeoff: the open rows' values and the restrictions are made once per class,
    // so tuples of `k` classes cost up to `k` times those of one; each class has a tuple, so
    // `k` is at most the number of tuples, and the classes are only those the tuples have,
    // never one per row. Tuples of one kinds are one class wherever the kinds decide every
    // open row, and scalars of one region are one. Where the kinds leave a row unknown, each
    // spine is a class: tuples that differ in a component other than one last along first
    // components, such as the `(2i, i)` of `((2i, i),)` met with each `((int - (2i + 1),
    // 0),)`, are one class each, and each reads the unknown rows, order `c` per tuple there.
    // A column is absorbed only where its regions, each a class reading every open row, cost
    // no more than filing its rows by it ([`RowIndex::new`]); the verdicts are the same either
    // way.
    fn holds(&mut self, part: &Part<Row>, v: &[Value], fits: impl Fn(&Row) -> bool) -> bool {
        let mut at = self.keyed.at(v);
        self.absorbed.extend_at(v, true, &mut at);
        at.sort_unstable();
        at.dedup();
        let kinds: Vec<Vec<Kind>> = v
            .iter()
            .zip(&self.read)
            .map(|(x, &read)| if read { kinds(x) } else { Vec::new() })
            .collect();
        if !self.by_kinds.contains_key(&kinds) {
            let decided = self.by_kinds(&kinds);
            self.by_kinds.insert(kinds.clone(), decided);
        }
        let RowIndex {
            rows,
            filing,
            open: open_rows,
            open_keys,
            regions,
            by_kinds,
            classes,
            ..
        } = self;
        let decided = &by_kinds[&kinds];
        let key = ClassKey {
            regions: v
                .iter()
                .zip(regions.iter())
                .map(|(x, by)| match by.is_empty() || !whole(x) {
                    true => None,
                    false => Some(by.get(x).copied().unwrap_or(0)),
                })
                .collect(),
            shape: match decided.iter().all(Option::is_some) {
                true => Shape::Kinds(kinds),
                false => Shape::Spine(v.iter().map(spine).collect()),
            },
        };
        let Class { open, halves, none } = classes.entry(key).or_insert_with(|| {
            let mut erased: Option<Vec<Value>> = None;
            let open = decided
                .iter()
                .zip(open_rows.iter())
                .map(|(s, row)| {
                    let columns = row.levels.iter().zip(&row.absorbs).zip(v);
                    match s {
                        Some(false) => false,
                        // A column absorbed, at a scalar, is read on the class's scalar.
                        Some(true) => columns
                            .filter(|((_, absorbs), x)| **absorbs && whole(x))
                            .all(|((levels, _), x)| levels[0][0].contains(x)),
                        None => {
                            let erased = erased.get_or_insert_with(|| {
                                v.iter()
                                    .zip(open_keys.iter())
                                    .map(|(x, keys)| erase(x, keys))
                                    .collect()
                            });
                            columns
                                .zip(erased.iter())
                                .all(|(((levels, &absorbs), x), e)| {
                                    levels[0][0].contains(if absorbs && whole(x) { x } else { e })
                                })
                        }
                    }
                })
                .collect();
            Class {
                open,
                halves: HashMap::new(),
                none: None,
            }
        });
        let (rows, filing, open) = (&*rows, &*filing, &*open);
        let restricted = match (at.first(), at.last()) {
            (Some(&first), Some(&last)) => {
                let i = half(rows, filing, open, halves, part, first, last);
                &halves[&i]
            }
            _ => none.get_or_insert_with(|| {
                part.restrict(&|r| {
                    rows.binary_search(r)
                        .ok()
                        .map(|i| row_default(filing, open, i))
                })
            }),
        };
        // A row that may hold `v` either has a key of `v`, and is in `at`, or holds it as its
        // value on a tuple of the class with no key of it.
        restricted.eval(&|r| match rows.binary_search(r) {
            Ok(i) if at.binary_search(&i).is_err() => row_default(filing, open, i),
            _ => fits(r),
        })
    }
}

/// The entry of `halves` for the smallest range of halves that holds the rows `first` to
/// `last` of `rows`, its part made from its enclosing range's part when first needed.
fn half(
    rows: &[Row],
    filing: &[Filing],
    open: &[bool],
    halves: &mut HashMap<usize, Part<Row>>,
    part: &Part<Row>,
    first: usize,
    last: usize,
) -> usize {
    let (mut i, mut lo, mut hi) = (1, 0, rows.len());
    halves.entry(1).or_insert_with(|| part.clone());
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        let (j, l, h) = if last < mid {
            (2 * i, lo, mid)
        } else if first >= mid {
            (2 * i + 1, mid, hi)
        } else {
            break;
        };
        if !halves.contains_key(&j) {
            let inner = halves[&i].restrict(&|r| match rows.binary_search(r) {
                Ok(k) if !(l..h).contains(&k) => Some(row_default(filing, open, k)),
                _ => None,
            });
            halves.insert(j, inner);
        }
        (i, lo, hi) = (j, l, h);
    }
    i
}

/// The boxes of one length of a maker, by the values they may hold, so that whether an earlier
/// box gave a tuple is checked against those boxes alone. A box is a meet of tuple types of a
/// finite type, so each of its columns is finite and lists every value it holds, its tuples
/// read by its boxes ([`file_row`]).
struct BoxIndex {
    /// The positions in the maker's boxes of the boxes filed under a column's keys.
    keyed: Keyed,
    /// The positions of the others, ascending: each is checked for every tuple.
    open: Vec<usize>,
}

impl Maker {
    fn new(
        ty: Type,
        boxes: Vec<(Vec<usize>, Row)>,
        rows: BTreeMap<Row, Vec<Option<usize>>>,
    ) -> Maker {
        let p = ty.p();
        let made = scalars(p);
        let by_value = p
            .tuples
            .lens
            .iter()
            .map(|(&len, part)| (len, RowIndex::new(len, part)))
            .collect();
        let mut by_box: BTreeMap<usize, BoxIndex> = BTreeMap::new();
        for (b, (_, r)) in boxes.iter().enumerate() {
            let index = by_box.entry(r.len()).or_insert_with(|| BoxIndex {
                keyed: Keyed::new(r.len()),
                open: Vec::new(),
            });
            match file_row(r) {
                (filed, Some(j)) => index.keyed.add(b, j, &filed[j].keys),
                (_, None) => index.open.push(b),
            }
        }
        Maker {
            ty,
            boxes,
            rows,
            by_value,
            by_box,
            next: 0,
            at: At::Start,
            made,
            done: false,
        }
    }

    /// Whether the value at `pos` is made (`Ok(true)`) or will never be (`Ok(false)`); `Err`
    /// when it must be made first.
    fn has(&self, me: usize, pos: usize) -> Result<bool, Need> {
        match (self.made.len() > pos, self.done) {
            (true, _) => Ok(true),
            (false, true) => Ok(false),
            (false, false) => Err((me, pos)),
        }
    }

    /// One step of the maker `me` of `makers`: it enters a box, makes the tuple at its
    /// position, or moves past it, or says which value of a component it needs first, before
    /// changing anything. The components' makers come before `me`.
    fn step(makers: &mut [Maker], me: usize) -> Result<(), Need> {
        let (below, rest) = makers.split_at_mut(me);
        let m = &mut rest[0];
        match std::mem::replace(&mut m.at, At::Start) {
            At::Start => {
                let Some((cols, _)) = m.boxes.get(m.next) else {
                    m.done = true;
                    return Ok(());
                };
                for &c in cols {
                    if !below[c].has(c, 0)? {
                        // A component with no value: the box has no tuple.
                        m.next += 1;
                        return Ok(());
                    }
                }
                m.at = At::Tuple(vec![0; cols.len()]);
            }
            At::Tuple(pos) => {
                let (cols, row) = &m.boxes[m.next];
                let v: Vec<Value> = cols
                    .iter()
                    .zip(&pos)
                    .map(|(&c, &i)| below[c].made[i].clone())
                    .collect();
                // A component's value is in the type that made it, so only a row whose type
                // differs there reads the value: a value deep in shared parts is not walked
                // again at each level that holds it.
                let fits = |r: &Row| {
                    let makers = m
                        .rows
                        .get(r)
                        .expect("every row of the diagram is collected");
                    r.iter()
                        .zip(makers)
                        .zip(cols.iter().zip(&v))
                        .all(|((t, &by), (&c, x))| by == Some(c) || t.contains(x))
                };
                let index = m.by_value.get_mut(&row.len()).expect("an index per length");
                let holds = index.holds(&m.ty.p().tuples.lens[&row.len()], &v, fits);
                // A tuple is given by the first box that has it. Within one box the positions
                // give distinct tuples, since each maker gives each value once. Only the earlier
                // boxes that may hold the tuple are read.
                let earlier = holds && {
                    let within = |b: usize| {
                        let (cs, r) = &m.boxes[b];
                        r.iter()
                            .zip(cs)
                            .zip(cols.iter().zip(&v))
                            .all(|((t, &c), (&made_by, x))| c == made_by || t.contains(x))
                    };
                    let index = &m.by_box[&row.len()];
                    let before = |b: &usize| *b < m.next;
                    index.open.iter().copied().take_while(before).any(within)
                        || index
                            .keyed
                            .at(&v)
                            .into_iter()
                            .take_while(before)
                            .any(within)
                };
                m.at = At::Past(pos);
                if holds && !earlier {
                    m.made.push(Value::tuple(v));
                }
            }
            At::Past(mut pos) => {
                let cols = &m.boxes[m.next].0;
                // The next position, the last component fastest; past the last, the next box.
                for k in (0..pos.len()).rev() {
                    match below[cols[k]].has(cols[k], pos[k] + 1) {
                        Ok(true) => {
                            pos[k] += 1;
                            pos[k + 1..].fill(0);
                            m.at = At::Tuple(pos);
                            return Ok(());
                        }
                        Ok(false) => {}
                        Err(need) => {
                            m.at = At::Past(pos);
                            return Err(need);
                        }
                    }
                }
                m.next += 1;
            }
        }
        Ok(())
    }
}

impl Values {
    /// Whether the value at `pos` of the maker `me` is made, after making what it needs. A
    /// maker waits only for makers before it, so the stack holds at most one entry per type
    /// and the nesting depth of the type is not the depth of the Rust stack.
    fn fill(&mut self, me: usize, pos: usize) -> bool {
        let mut stack: Vec<Need> = vec![(me, pos)];
        while let Some(&(m, p)) = stack.last() {
            match self.makers[m].has(m, p) {
                Ok(_) => {
                    stack.pop();
                }
                Err(_) => {
                    if let Err(need) = Maker::step(&mut self.makers, m) {
                        stack.push(need);
                    }
                }
            }
        }
        self.makers[me].made.len() > pos
    }
}

impl Iterator for Values {
    type Item = Value;

    fn next(&mut self) -> Option<Value> {
        let top = self.makers.len() - 1;
        if !self.fill(top, self.given) {
            return None;
        }
        self.given += 1;
        Some(self.makers[top].made[self.given - 1].clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every union of a subset of `lits`, and the complement of each within `within`.
    fn subsets_and_complements(lits: &[Type], within: &Type) -> Vec<Type> {
        let finite: Vec<Type> = (0..1u32 << lits.len())
            .map(|mask| {
                Type::union_all(
                    (0..lits.len())
                        .filter(|i| mask & (1 << i) != 0)
                        .map(|i| lits[i].clone()),
                )
            })
            .collect();
        let complements: Vec<Type> = finite.iter().map(|t| within - t).collect();
        finite.into_iter().chain(complements).collect()
    }

    /// `scalar_cell` decides a meet or a difference of two scalar-only types from their parts;
    /// each answer must be what the explicit set operation and `is_empty` give.
    fn agree(all: &[Type]) {
        for a in all {
            for b in all {
                assert_eq!(
                    a.scalar_cell(b, true),
                    Some((a & b).is_empty()),
                    "{a} & {b}"
                );
                assert_eq!(
                    a.scalar_cell(b, false),
                    Some((a - b).is_empty()),
                    "{a} - {b}"
                );
            }
        }
    }

    #[test]
    fn scalar_cells_agree_with_explicit_set_operations() {
        // The 32 types of the old review test: the subsets of 0..4 and their complements in int.
        let ints: Vec<Type> = (0..4).map(|i| Type::lit(&Value::Int(i)).unwrap()).collect();
        let all = subsets_and_complements(&ints, &Type::int());
        assert_eq!(all.len(), 32);
        agree(&all);
    }

    #[test]
    fn scalar_cells_agree_with_explicit_set_operations_across_carriers() {
        // One or two literals of each carrier, so that every clause of `scalar_cell` decides
        // some pair: 128 types, finite and cofinite in each carrier.
        let half = Rat::decimal("0.5").expect("given").unwrap();
        let lits: Vec<Type> = [
            Value::Bool(true),
            Value::Int(0),
            Value::rat(half),
            Value::float(0.5),
            Value::str("a"),
            Value::str("b"),
        ]
        .iter()
        .map(|v| Type::lit(v).unwrap())
        .collect();
        let scalars = Type::union_all([
            Type::bool(),
            Type::int(),
            Type::rat(),
            Type::f64(),
            Type::string(),
        ]);
        let all = subsets_and_complements(&lits, &scalars);
        assert_eq!(all.len(), 128);
        agree(&all);
    }

    /// [`Atoms::zip`] by the walk over the smaller map alone, as it was before the diff.
    fn zip_by_walk(a: &Atoms, b: &Atoms, op: Op) -> Atoms {
        let (large, small) = if a.names.len() >= b.names.len() {
            (a, b)
        } else {
            (b, a)
        };
        let mut out = match (op, small.cofinite) {
            (Op::Or, false) | (Op::And, true) => large.clone(),
            _ => Atoms::default(),
        };
        out.cofinite = match op {
            Op::Or => a.cofinite || b.cofinite,
            Op::And => a.cofinite && b.cofinite,
        };
        for (n, p) in &small.names {
            out.set(n, large.get(n).zip(p, op));
        }
        out
    }

    /// The diff of two maps that share nodes gives what the walk gives, for sets grown from
    /// one another as a chain of merged failures grows them, for unrelated sets, for payloads
    /// and bare atoms, for complements, and for both operations (ERRS-precise).
    #[test]
    fn atoms_combined_by_a_diff_agree_with_the_walk() {
        let atom = |i: usize| match i % 3 {
            0 => Type::atom(&format!("a{i}")),
            1 => Type::atom_with(&format!("a{i}"), &Type::tuple(vec![Type::int()])),
            _ => Type::atom(&format!("a{i}")) | Type::atom_with(&format!("a{i}"), &Type::top()),
        };
        let mut grown = vec![Type::empty()];
        for i in 0..200 {
            let last = grown.last().expect("one at least").clone();
            grown.push(&last | &atom(i));
        }
        let mut sets = grown.clone();
        // Grown again from a midpoint, so the two lines share their first nodes.
        let mut other = grown[100].clone();
        for i in 300..380 {
            other = &other | &atom(i);
            sets.push(other.clone());
        }
        sets.push(Type::union_all((0..150).step_by(2).map(atom)));
        let complements: Vec<Type> = sets.iter().step_by(17).map(|t| !t).collect();
        sets.extend(complements);
        for a in sets.iter().step_by(3) {
            for b in sets.iter().step_by(5) {
                for op in [Op::Or, Op::And] {
                    let (x, y) = (&a.p().atoms, &b.p().atoms);
                    assert_eq!(x.zip(y, op), zip_by_walk(x, y, op));
                    assert_eq!(y.zip(x, op), zip_by_walk(y, x, op));
                }
            }
        }
    }
}
