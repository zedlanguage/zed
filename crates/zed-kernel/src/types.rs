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
mod empty;
pub use empty::{Refusal, Verdict};
mod print;
pub mod rec;

pub use print::Surface;

use imbl::{OrdMap, OrdSet};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::ops::{BitAnd, BitOr, Not, Sub};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use crate::deep;
use crate::num::Rat;
use crate::value::Value;
use bdd::{Form, Part};

/// A type: the set of values it denotes. Types are ordered by their digests first, so two
/// types are ordered without reading their contents unless their digests are equal.
#[derive(Clone, Debug)]
pub struct Type(Arc<Node>);

impl Ord for Type {
    fn cmp(&self, other: &Type) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        self.digest()
            .cmp(&other.digest())
            .then_with(|| self.0.cmp(&other.0))
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
    z ^ (z >> 31)
}

/// FNV-1a over `b`.
fn bytes(b: &[u8]) -> u64 {
    b.iter().fold(0xcbf2_9ce4_8422_2325, |h, &x| {
        (h ^ u64::from(x)).wrapping_mul(0x100_0000_01b3)
    })
}

/// What the top level of a value says of its membership in a type.
enum Member<'v> {
    Known(bool),
    /// In the type exactly when the tuple of these values is, read in place: an atom's payload
    /// was copied into a tuple to be tested, so a value nested `d` deep was copied `d` times.
    Tuple(Type, &'v [Value]),
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
        Value::Str(s) => mix(2, bytes(s.as_bytes())),
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Parts(Parts, Shown),
    Rec(Rec),
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Parts(p, _) => f.debug_tuple("Parts").field(p).finish(),
            Node::Rec(r) => f.debug_tuple("Rec").field(r).finish(),
        }
    }
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
                free(Freed::Morphisms(std::mem::replace(
                    &mut p.morphisms,
                    Part::leaf(false),
                )));
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
    Tuples(Part<Row>),
    Morphisms(Part<Morphism>),
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

impl PartialOrd for Shown {
    fn partial_cmp(&self, other: &Shown) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Shown {
    fn cmp(&self, _: &Shown) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

/// A recursive type, or a part of a recursive definition's body kept unevaluated: its parts are
/// `make()`, computed on first use. Two nodes are one type only when they are one node.
struct Rec {
    id: u64,
    /// The name, made when first printed: a name spells out its part of the definition, so
    /// making every part's name at once cost the product of the definition's size and depth.
    name: OnceLock<String>,
    naming: Box<dyn Fn() -> String + Send + Sync>,
    body: OnceLock<Type>,
    make: Box<dyn Fn() -> Type + Send + Sync>,
    /// The emptiness its group decides for it, if the group is decided (module `bes`).
    judge: Option<Box<dyn Fn() -> Option<bool> + Send + Sync>>,
}

impl PartialEq for Rec {
    fn eq(&self, other: &Rec) -> bool {
        self.id == other.id
    }
}

impl Eq for Rec {}

impl PartialOrd for Rec {
    fn partial_cmp(&self, other: &Rec) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rec {
    fn cmp(&self, other: &Rec) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl Rec {
    fn name(&self) -> &str {
        self.name.get_or_init(|| (self.naming)())
    }

    /// The name, made apart from any text under way on this thread: a name prints the types of its
    /// arguments, and inside the loop of [`Type::rope`] a type whose text is not made yet prints
    /// as a placeholder, which the name would keep.
    fn name_apart(&self) -> &str {
        if let Some(n) = self.name.get() {
            return n;
        }
        let outer = SHOWING.with_borrow_mut(Option::take);
        let name = self.name();
        SHOWING.with_borrow_mut(|s| *s = outer);
        name
    }
}

impl fmt::Debug for Rec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Morphism {
    /// The keys certainly present.
    pub guarantee: Type,
    /// The keys possibly present.
    pub permission: Type,
    /// The type of every present key's value.
    pub value: Type,
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
            .then_with(|| self.0.1.cmp(&other.0.1))
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

impl fmt::Debug for Row {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.1.fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Atoms {
    cofinite: bool,
    names: OrdMap<Arc<str>, AtomPart>,
    sum: u64,
}

/// The atoms of one name in a type: the bare atom, and those whose payload is in `payload`, a
/// type within the tuples and structs.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct AtomPart {
    bare: bool,
    payload: Type,
}

/// Per length, the tuples of that length, as a part over tuple types of it; a
/// length not listed has every tuple when `rest`, else none. Tuples of two lengths are disjoint.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
struct Tuples {
    rest: bool,
    lens: BTreeMap<usize, Part<Row>>,
}

thread_local! {
    static EMPTY: Type = Type::build_empty();
    static TOP: Type = !Type::build_empty();
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
    /// identity's, since two such nodes are one type only when they are one node.
    pub(crate) fn digest(&self) -> u64 {
        match &*self.0 {
            Node::Parts(p, _) => p.digest,
            Node::Rec(r) => mix(4, r.id),
        }
    }

    /// The node named `naming()` whose parts are `make()`'s, each computed when first needed.
    /// `make` must not need this node's parts, which a contractive definition ensures.
    fn rec(
        naming: impl Fn() -> String + Send + Sync + 'static,
        make: impl Fn() -> Type + Send + Sync + 'static,
    ) -> Type {
        Type::rec_with(Box::new(naming), Box::new(make), None)
    }

    /// The node of [`Type::rec`], with its emptiness given by `judge` when there is one.
    fn rec_with(
        naming: Box<dyn Fn() -> String + Send + Sync>,
        make: Box<dyn Fn() -> Type + Send + Sync>,
        judge: Option<Box<dyn Fn() -> Option<bool> + Send + Sync>>,
    ) -> Type {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Type(Arc::new(Node::Rec(Rec {
            id: NEXT.fetch_add(1, Ordering::Relaxed),
            name: OnceLock::new(),
            naming,
            body: OnceLock::new(),
            make,
            judge,
        })))
    }

    /// [`Type::rec`], with `judge()` giving its emptiness when its group decides it.
    pub(crate) fn rec_judged(
        naming: impl Fn() -> String + Send + Sync + 'static,
        make: impl Fn() -> Type + Send + Sync + 'static,
        judge: impl Fn() -> Option<bool> + Send + Sync + 'static,
    ) -> Type {
        Type::rec_with(Box::new(naming), Box::new(make), Some(Box::new(judge)))
    }

    /// The emptiness the group of a recursive node decides for it, if any.
    pub(crate) fn judged(&self) -> Option<bool> {
        match &*self.0 {
            Node::Parts(..) => None,
            Node::Rec(r) => r.judge.as_ref().and_then(|j| j()),
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
        Type::with(|p| p.bools = 3)
    }

    /// `int`.
    pub fn int() -> Type {
        Type::with(|p| p.ints.cofinite = true)
    }

    /// `rat`.
    pub fn rat() -> Type {
        Type::with(|p| p.rats.cofinite = true)
    }

    /// `f64`.
    pub fn f64() -> Type {
        Type::with(|p| p.floats.cofinite = true)
    }

    /// `String`.
    pub fn string() -> Type {
        Type::with(|p| p.strings.cofinite = true)
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
    /// literal sets, bare atoms, and tuples whose boxes ([`Type::boxes`]) hold only types known
    /// finite. A recursive type, a payload, a struct or a function is not known finite, and a
    /// box is read as written, so `(int, 0) & (0, 0)` is not known finite although it has one
    /// value. No size is compared: the answer depends on the type alone.
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
    /// type in time polynomial in their number would decide satisfiability. Its user is the
    /// type facet of a product cell (`zedc::store::product`).
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
    /// meet of those the path took before; so each node of the diagram gives the box of its
    /// tuple type met with the union of the meets on the paths to it, one pass over the
    /// nodes, never over the paths. An expression gives each of its tuple types.
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
            match part {
                Part::Bdd(b) => {
                    b.reaching(
                        Row::new(vec![Type::top(); *len]),
                        meet,
                        |r, s| Row::new(r.iter().zip(s.iter()).map(|(x, y)| x | y).collect()),
                        |a, r| {
                            out.push(meet(a, r));
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
    /// its contents, and the sequence of `v` it reads, by the sequence's address and length as
    /// `Items::addr` does: `v` is borrowed for the call, so no sequence is freed and an address
    /// names one sequence while the call runs, and the kept tests are never iterated, so the
    /// answer does not depend on where `v` is in memory.
    ///
    /// Exception to keying by content (deterministic checking): the address is the
    /// occurrence id of a shared sequence. A content key would hash a sequence in full at
    /// each test, O(size) per node, and a value whose halves are one shared value at every
    /// level has `2^d` paths and `d` sequences, so its content is exponential to read while
    /// the address keeps the work linear in the sequences. Two sequences equal in content at
    /// different addresses are tested twice, which costs time and never changes the answer.
    /// Test: `l01_23_subtyping::rec::membership_by_sequence_address_is_deterministic` (shared
    /// against apart, three allocation orders, one thread against a fresh thread per query).
    /// At the port: a hash-consed id of the value (ZED_PORT_GAPS.md, the `deep::walk` row).
    pub fn contains(&self, v: &Value) -> bool {
        let first = match self.member(v) {
            Member::Known(b) => return b,
            Member::Tuple(ty, xs) => (ty, xs),
        };
        let key = |t: &Type, xs: &[Value]| (t.clone(), xs.as_ptr().addr(), xs.len());
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

    /// The parts combined by `op`, in `O(s log l)` steps for the smaller map's `s` names and
    /// the larger's `l`. A name the smaller map does not list has every payload or none, and
    /// a part combined with all or none is itself, all or none: so the result is the larger
    /// map, or nothing, changed at the smaller map's names.
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
            _ => Atoms::default(),
        };
        out.cofinite = cofinite;
        for (n, p) in &small.names {
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
    /// loop: a try of `show` that finds a text inside missing gives up, the types it named are
    /// made first, and the try is made again, so each type is tried at most twice.
    fn rope(&self) -> Rope {
        let shown = match &*self.0 {
            Node::Parts(_, shown) => shown,
            Node::Rec(r) => return rope![r.name_apart()],
        };
        if let Some(r) = shown.0.get() {
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

    /// The loop of [`Type::rope`], from the outermost type whose text is asked for.
    fn make_rope(&self) -> Rope {
        SHOWING.with_borrow_mut(|s| *s = Some(Showing::default()));
        let _end = EndShowing;
        let mut stack = vec![self.clone()];
        while let Some(t) = stack.last() {
            let Node::Parts(p, shown) = &*t.0 else {
                unreachable!("a recursive node's text is its name, never missing")
            };
            let made = SHOWING.with_borrow(|s| s.as_ref().and_then(|s| s.made.get(t).cloned()));
            if let Some(r) = made {
                let _ = shown.0.set(r);
            }
            if shown.0.get().is_some() {
                stack.pop();
                continue;
            }
            let r = t.show(p);
            let missing = SHOWING.with_borrow_mut(|s| {
                std::mem::take(&mut s.as_mut().expect("the making is under way").missing)
            });
            if missing.is_empty() {
                let _ = shown.0.set(r.clone());
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
        match &*self.0 {
            Node::Parts(_, shown) => shown.0.get().expect("the loop made the text").clone(),
            Node::Rec(r) => rope![r.name_apart()],
        }
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

/// One item per path of a diagram: the intersection of the atoms it takes, or `all` when it
/// takes none, and the complements of those it refuses. The items, and the atoms within each,
/// are sorted as text, since the diagram's order of atoms is that of their digests. A part
/// kept as an expression is its connective applied to the items of its operands.
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
                Form::Or(a, b) => rope!["(| ", item(a), " ", item(b), ")"],
                Form::And(a, b) => rope!["(& ", item(a), " ", item(b), ")"],
            });
            return;
        }
    };
    let mut found = Vec::new();
    b.paths(&mut |pos, neg| {
        let mut lits: Vec<Rope> = pos.iter().map(|a| show(a)).collect();
        lits.sort();
        if lits.is_empty() {
            lits.push(all.clone());
        }
        let mut refused: Vec<Rope> = neg.iter().map(|n| rope!["(! ", show(n), ")"]).collect();
        refused.sort();
        lits.extend(refused);
        match lits.len() {
            1 => found.push(lits.remove(0)),
            _ => found.push(Rope::listed("(&", lits)),
        }
        true
    });
    found.sort();
    items.extend(found);
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

impl Maker {
    fn new(
        ty: Type,
        boxes: Vec<(Vec<usize>, Row)>,
        rows: BTreeMap<Row, Vec<Option<usize>>>,
    ) -> Maker {
        let p = ty.p();
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
        Maker {
            ty,
            boxes,
            rows,
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
                let within = |r: &Row, cs: &[usize]| {
                    r.iter()
                        .zip(cs)
                        .zip(cols.iter().zip(&v))
                        .all(|((t, &c), (&made_by, x))| c == made_by || t.contains(x))
                };
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
                let holds = m.ty.p().tuples.lens[&row.len()].eval(&fits);
                // A tuple is given by the first box that has it. Within one box the positions
                // give distinct tuples, since each maker gives each value once.
                let earlier = m.boxes[..m.next]
                    .iter()
                    .any(|(cs, r)| r.len() == row.len() && within(r, cs));
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
