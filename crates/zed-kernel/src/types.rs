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
mod bucket;
mod debug;
mod empty;
mod hash;
#[cfg(test)]
use hash::SALT;
pub(crate) use hash::mix;
mod print;
pub use print::{defs, names};

use imbl::ordmap::DiffItem;
use imbl::{OrdMap, OrdSet};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, Bound, HashMap, HashSet};
use std::fmt;
use std::ops::{BitAnd, BitOr, Not, Sub};
use std::sync::{Arc, Mutex, OnceLock, PoisonError};

use crate::deep;
use crate::num::Rat;
use crate::value::{Id, Items, Value};
use bdd::{Bdd, Form, Literal, Op, Owned, Part, Tables, Walk};
use bucket::Bucket;

/// A type: the set of values it denotes. Types are ordered by their digests first, so two
/// types are ordered without reading their contents unless their digests are equal, and then by
/// the loop of `order`, which reads the contents with a stack of its own.
#[derive(Clone)]
pub struct Type(Arc<Node>);

// Complexity tradeoff (COMPLEXITY.md K12): the naive comparison reads both types' contents,
// O(s·depth) per comparison for a type of size `s` nested `depth` deep, and rebuilds `empty`
// and `top` per call. Used: a deterministic digest made from the children's digests when a node
// is made, compared first; the contents are read only on equal digests, by the loop of `order`,
// once per pair of nodes. O(1) for types of different digest. Tradeoffs: one 64-bit digest per
// node; the order is that of the digests, not of the text, so the printer sorts each part's
// clauses as text itself; on a digest tie (a collision, or the short-addresses build) two
// types are read in full, linear in their size.
impl Ord for Type {
    fn cmp(&self, other: &Type) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        self.digest()
            .cmp(&other.digest())
            .then_with(|| order(Step::Types(self, other)))
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
    /// The names of the unfolding's atoms, when first asked ([`Type::atom_names`]).
    #[expect(clippy::type_complexity, reason = "a list of names, each with a flag")]
    names: OnceLock<Option<Vec<(Arc<str>, bool)>>>,
    /// The unfolding, made when first needed. A member's unfolding holds the member, so the
    /// end of the unit that made it drops it (`rec::unfold::end_unit`), and it is made again if the
    /// node is used after.
    body: Mutex<Option<Type>>,
    make: Box<dyn Fn() -> Type + Send + Sync>,
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

impl Rec {
    /// The unfolding, made by `make()` outside the lock when not kept: `make` reads other
    /// nodes' unfoldings, and a thread that made it at the same time may have kept its own
    /// first, which is then the one.
    fn unfolding(&self) -> Type {
        let cell = || self.body.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(b) = &*cell() {
            return b.clone();
        }
        let made = (self.make)();
        let kept = cell().get_or_insert_with(|| made.clone()).clone();
        // `made` is dropped here, after the lock, when another thread kept its own.
        drop(made);
        kept
    }

    /// Drops the kept unfolding, after the lock is released.
    fn forget_unfolding(&self) {
        let old = self
            .body
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        drop(old);
    }
}

/// The parts of a type ([`Type::p`]): its node's own, or those of a recursive node's
/// unfolding, which the guard holds, since the end of a unit may drop the node's copy
/// (`rec::unfold::end_unit`) while the parts are read.
enum PartsRef<'a> {
    Node(&'a Parts),
    /// A node of parts, never a recursive node.
    Unfolded(Type),
}

impl std::ops::Deref for PartsRef<'_> {
    type Target = Parts;

    fn deref(&self) -> &Parts {
        match self {
            PartsRef::Node(p) => p,
            PartsRef::Unfolded(t) => match &*t.0 {
                Node::Parts(p, _) => p,
                Node::Rec(_) => unreachable!("an unfolding is unfolded to a node of parts"),
            },
        }
    }
}

/// Unfoldings held while their parts are borrowed ([`Type::p_held`]): each is put in through a
/// shared reference and stays at its place until the holder is dropped, so a walk may keep
/// borrows into the parts of every recursive type it meets. Block `k` has room for `2^k`.
// Complexity tradeoff: a put walks to the block with room, O(log n) for the `n`th; a block
// that knew the last block would refer into its own holder. The standard form, one growing
// `Vec`, puts in O(1) amortized but moves its items when it grows, which would end the
// borrows into them; a pointer to the last block would put in O(1) but make the holder
// refer into itself.
#[derive(Default)]
struct Held {
    used: std::cell::Cell<usize>,
    first: HeldBlock,
}

struct HeldBlock {
    slots: Box<[std::cell::OnceCell<Type>]>,
    next: std::cell::OnceCell<Box<HeldBlock>>,
}

impl HeldBlock {
    fn new(room: usize) -> HeldBlock {
        HeldBlock {
            slots: (0..room).map(|_| std::cell::OnceCell::new()).collect(),
            next: std::cell::OnceCell::new(),
        }
    }
}

impl Default for HeldBlock {
    fn default() -> HeldBlock {
        HeldBlock::new(1)
    }
}

impl Held {
    /// Holds `t` until the holder is dropped.
    fn put(&self, t: Type) -> &Type {
        let n = self.used.get() + 1;
        self.used.set(n);
        // The `n`th type goes to block `log2 n`, at `n - 2^k`.
        let k = n.ilog2();
        let mut block = &self.first;
        for i in 1..=k {
            block = block.next.get_or_init(|| Box::new(HeldBlock::new(1 << i)));
        }
        let slot = &block.slots[n - (1 << k)];
        let _ = slot.set(t);
        slot.get().expect("the slot was empty and is set")
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

/// The bounds and value type of a morphism type: `(guarantee ⊆ dom ⊆ permission) -> value`.
pub struct Arrow {
    /// The keys certainly present.
    pub guarantee: Type,
    /// The keys possibly present.
    pub permission: Type,
    /// The type of every present key's value.
    pub value: Type,
}

/// Equal when the three types are, read in one loop of `order`.
impl PartialEq for Arrow {
    fn eq(&self, other: &Arrow) -> bool {
        order(Step::Morphisms(self, other)) == std::cmp::Ordering::Equal
    }
}

/// A morphism type, an atom of the morphism parts, kept with its hash in one shared node as a
/// row is: the live morphism types of a thread are kept in a table by digest (item
/// ATOM-intern), so two equal ones alive on one thread are one node and compare by pointer.
/// The fields are read through [`Arrow`].
#[derive(Clone)]
pub struct Morphism(Arc<Shared<Arrow>>);

impl Morphism {
    pub(crate) fn new(guarantee: Type, permission: Type, value: Type) -> Morphism {
        let m = mix(6, guarantee.digest());
        let digest = mix(mix(m, permission.digest()), value.digest());
        let arrow = Arrow {
            guarantee,
            permission,
            value,
        };
        Morphism(Shared::new(digest, arrow))
    }

    pub(crate) fn digest(&self) -> u64 {
        self.0.digest
    }
}

impl std::ops::Deref for Morphism {
    type Target = Arrow;
    fn deref(&self) -> &Arrow {
        &self.0.key
    }
}

/// By guarantee, then permission, then value, the order `order` gives two morphism types;
/// one node is equal to itself without reading it. Each pair of types is compared by
/// [`Type::cmp`], by pointer and then by digest before its contents, so that a table of
/// morphism types, whose lookups compare a key with some `log n` others that nearly always
/// differ in a field's digest, enters the loop of `order` only where two digests tie
/// (EMPTY-morphism-diff-cost: a search through nested morphism types had entered that loop
/// some 1,900 times a level, and enters it some 170 times).
impl Ord for Morphism {
    fn cmp(&self, other: &Morphism) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        let (a, b) = (&self.0.key, &other.0.key);
        (a.guarantee.cmp(&b.guarantee))
            .then_with(|| a.permission.cmp(&b.permission))
            .then_with(|| a.value.cmp(&b.value))
    }
}

impl PartialOrd for Morphism {
    fn partial_cmp(&self, other: &Morphism) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Morphism {
    fn eq(&self, other: &Morphism) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for Morphism {}

/// A key kept with its digest in a node of a weak per-thread table (step TABLE-life), so that
/// equal keys alive together on one thread are one node: the rows of the tuple parts and the
/// morphism types of the morphism parts.
struct Shared<K: Tabled> {
    digest: u64,
    /// The node's slot in its bucket of the table (module `bucket`).
    slot: u32,
    key: K,
}

/// The thread's live nodes of one kind, by digest; nodes of one digest that differ share a
/// bucket, ordered by their keys (module `bucket`).
type Live<K> =
    RefCell<HashMap<u64, Bucket<Shared<K>>, std::hash::BuildHasherDefault<crate::digest::Digest>>>;

/// A kind of key kept in a table of live nodes, with the thread-local that holds the table.
trait Tabled: PartialEq + Sized + 'static {
    /// The thread's table of the kind.
    fn live() -> &'static std::thread::LocalKey<Live<Self>>;
    /// The order of keys, by their contents, that a bucket of the table keeps.
    fn order(a: &Self, b: &Self) -> Ordering;
}

thread_local! {
    /// The live rows of the thread.
    static ROWS: Live<Vec<Type>> = RefCell::default();
    /// The live morphism types of the thread.
    static ARROWS: Live<Arrow> = RefCell::default();
}

impl Tabled for Vec<Type> {
    fn live() -> &'static std::thread::LocalKey<Live<Self>> {
        &ROWS
    }

    fn order(a: &Self, b: &Self) -> Ordering {
        order(Step::Items(a.iter(), b.iter()))
    }
}

impl Tabled for Arrow {
    fn live() -> &'static std::thread::LocalKey<Live<Self>> {
        &ARROWS
    }

    fn order(a: &Self, b: &Self) -> Ordering {
        order(Step::Morphisms(a, b))
    }
}

/// A node leaves its thread's table when dropped, by its slot; one dropped on another thread
/// leaves an entry that no longer upgrades, which the next lookup to meet it takes out. The
/// key's types are freed in the loop of type parts (module `deep`), as every type is.
impl<K: Tabled> Drop for Shared<K> {
    fn drop(&mut self) {
        let me: *const Shared<K> = self;
        let _ = K::live().try_with(|t| {
            if let Ok(mut t) = t.try_borrow_mut()
                && let Some(bucket) = t.get_mut(&self.digest)
            {
                bucket.leave(self.slot, me);
                if bucket.is_empty() {
                    t.remove(&self.digest);
                }
            }
        });
    }
}

impl<K: Tabled> Shared<K> {
    /// The live node of the thread whose key equals `key`, or a new one put in the table.
    fn new(digest: u64, key: K) -> Arc<Shared<K>> {
        let bucket = |f: &mut dyn FnMut(&mut Bucket<Shared<K>>)| {
            K::live().with(|t| f(t.borrow_mut().entry(digest).or_default()));
        };
        match bucket::find(bucket, |r| K::order(&r.key, &key)) {
            Ok(r) => r,
            Err(place) => {
                let r = Arc::new(Shared {
                    digest,
                    slot: place.slot(),
                    key,
                });
                bucket(&mut |b| b.insert(&place, Arc::downgrade(&r)));
                r
            }
        }
    }
}

/// The component types of a tuple type, an atom of the tuple parts, kept with their hash in
/// one shared node: a row is copied in constant time, and compared in constant time unless it
/// equals a row built apart from it on another thread. The live rows of a thread are kept in a
/// table by digest, so two equal rows alive on one thread are one node (step TABLE-life; the
/// tables of diagram nodes once kept every row's node for the life of the thread, which had
/// made equal rows one node only while their first diagram's nodes were never freed).
#[derive(Clone)]
pub(crate) struct Row(Arc<Shared<Vec<Type>>>);

impl Row {
    pub(crate) fn new(items: Vec<Type>) -> Row {
        let digest = items.iter().fold(5, |h, t| mix(h, t.digest()));
        Row(Shared::new(digest, items))
    }

    pub(crate) fn digest(&self) -> u64 {
        self.0.digest
    }
}

impl std::ops::Deref for Row {
    type Target = [Type];
    fn deref(&self) -> &[Type] {
        &self.0.key
    }
}

impl<'a> IntoIterator for &'a Row {
    type Item = &'a Type;
    type IntoIter = std::slice::Iter<'a, Type>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.key.iter()
    }
}

impl Ord for Row {
    fn cmp(&self, other: &Row) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        self.0
            .digest
            .cmp(&other.0.digest)
            .then_with(|| order(Step::Rows(self, other)))
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

thread_local! {
    static TUPLES: RefCell<Tables<Row>> = const { RefCell::new(Tables::new()) };
    static MORPHISMS: RefCell<Tables<Morphism>> = const { RefCell::new(Tables::new()) };
}

impl Literal for Row {
    fn table<R>(f: impl FnOnce(&mut Tables<Self>) -> R) -> R {
        hold();
        TUPLES.with(|t| f(&mut t.borrow_mut()))
    }
    fn untable(f: impl FnOnce(&mut Tables<Self>)) {
        let _ = TUPLES.try_with(|t| t.try_borrow_mut().map(|mut t| f(&mut t)));
    }
    fn digest(&self) -> u64 {
        Row::digest(self)
    }
    fn free(part: Owned<Row>) {
        free(Freed::Tuples(part));
    }
    fn order(w: Walk<'_, Row>) -> std::cmp::Ordering {
        order(Row::walk(w))
    }
}

impl Literal for Morphism {
    fn table<R>(f: impl FnOnce(&mut Tables<Self>) -> R) -> R {
        hold();
        MORPHISMS.with(|t| f(&mut t.borrow_mut()))
    }
    fn untable(f: impl FnOnce(&mut Tables<Self>)) {
        let _ = MORPHISMS.try_with(|t| t.try_borrow_mut().map(|mut t| f(&mut t)));
    }
    fn digest(&self) -> u64 {
        Morphism::digest(self)
    }
    fn free(part: Owned<Morphism>) {
        free(Freed::Morphisms(part));
    }
    fn order(w: Walk<'_, Morphism>) -> std::cmp::Ordering {
        order(Morphism::walk(w))
    }
}

/// The steps of [`order`] for the atoms of a universe and the nodes of its diagrams.
trait Ordered: Literal {
    /// The step that compares two atoms.
    fn atoms<'a>(a: &'a Self, b: &'a Self) -> Step<'a>;
    /// The step that compares two lists, cells, sets, expressions or parts of the universe.
    fn walk(w: Walk<'_, Self>) -> Step<'_>;
}

impl Ordered for Row {
    fn atoms<'a>(a: &'a Row, b: &'a Row) -> Step<'a> {
        Step::Rows(a, b)
    }
    fn walk(w: Walk<'_, Row>) -> Step<'_> {
        Step::Tuples(w)
    }
}

impl Ordered for Morphism {
    fn atoms<'a>(a: &'a Morphism, b: &'a Morphism) -> Step<'a> {
        Step::Morphisms(a, b)
    }
    fn walk(w: Walk<'_, Morphism>) -> Step<'_> {
        Step::Arrows(w)
    }
}

/// The atom names of a type with their parts.
type AtomNames = imbl::OrdMap<Arc<str>, AtomPart>;

/// The tuple lengths of a type with their parts.
type Lens = BTreeMap<usize, Part<Row>>;

/// A pair to compare in [`order`], the rest of two sequences compared in order, the order of two
/// fields already compared, or two nodes or expressions whose contents compared equal.
enum Step<'a> {
    Types(&'a Type, &'a Type),
    Rows(&'a Row, &'a Row),
    Morphisms(&'a Arrow, &'a Arrow),
    Tuples(Walk<'a, Row>),
    Arrows(Walk<'a, Morphism>),
    /// The remaining components of two rows.
    Items(std::slice::Iter<'a, Type>, std::slice::Iter<'a, Type>),
    /// The atom names of two types after the bound, each with its part: the maps and the last
    /// name read rather than two iterators, which would make every step five times the size.
    Names(&'a AtomNames, &'a AtomNames, Bound<&'a Arc<str>>),
    /// The tuple lengths of two types after the bound, each with its part.
    Lens(&'a Lens, &'a Lens, Bound<usize>),
    /// The order of two scalar fields, read when every field before them compared equal.
    Is(Ordering),
    Equal(u64, u64),
}

/// The pairs of node ids [`order`] found equal, hashed by `digest::Digest`: the default hasher
/// seeds itself per set and runs SipHash on each pair (EMPTY-morphism-next).
type Equal = HashSet<(u64, u64), std::hash::BuildHasherDefault<crate::digest::Digest>>;

/// The order of the pair in `first`, the order of contents that `Ord` gives every type, row,
/// morphism type, part, diagram and expression: two types by digest, then by their parts field
/// by field (a recursive node after every other, two of them by key, `rec::Key::order`); two
/// rows by digest, then component by component; two morphism types by guarantee, permission and
/// value; two diagrams or expressions by digest, then by atom or connective, then by `hi` and
/// `lo` or by operands, a diagram before an expression; sequences (rows, atom names, tuple
/// lengths) lexicographically, a prefix first. Two nodes or expressions found equal are kept by node id
/// and not compared again, so the cost is one step per pair of nodes compared, not one per path
/// to them, and linear in the size when the two are equal. A loop with its own stack, as a type
/// can be deeper than the call stack: a row's components are types, whose tuple parts are
/// diagrams over rows, so where the digests tie (short-addresses build, step L1.37a, or a 64-bit
/// collision) two types n deep are compared n levels down (SHORT-stack-l01_22).
fn order(first: Step<'_>) -> Ordering {
    // Complexity tradeoff (COMPLEXITY.md K48): the naive order recurses on the call stack with
    // no memo, so it reads a shared node once per path to it, exponential in the depth of
    // sharing of two equal diagrams, and takes one native frame per level where the digests tie.
    // Used: the pairs found equal are kept in `equal` for the whole comparison, so each pair of
    // nodes is read once, O(pairs compared) steps, each a hash lookup; the stack is on the heap.
    // Given up: memory for the set, O(pairs found equal), and one hash insert per pair found
    // equal; a comparison its digests decide allocates nothing.
    let mut equal = Equal::default();
    // The first step is held apart, so that a comparison its digests decide allocates nothing.
    let mut steps = Vec::new();
    let mut next = Some(first);
    while let Some(step) = next.take().or_else(|| steps.pop()) {
        let c = match step {
            Step::Equal(a, b) => {
                equal.insert((a, b));
                Ordering::Equal
            }
            Step::Is(c) => c,
            Step::Tuples(w) => walk(w, &mut steps, &equal),
            Step::Arrows(w) => walk(w, &mut steps, &equal),
            Step::Types(a, b) => types(a, b, &mut steps, &equal),
            Step::Rows(a, b) => {
                if Arc::ptr_eq(&a.0, &b.0) {
                    continue;
                }
                a.digest()
                    .cmp(&b.digest())
                    .then_with(|| items(a.iter(), b.iter(), &mut steps, &equal))
            }
            Step::Morphisms(a, b) => {
                if std::ptr::eq(a, b) {
                    continue;
                }
                // Each pair is read at once where its fields decide it, as in [`items`], so that
                // two morphism types told apart by a digest push nothing; at the first pair that
                // needs a nested comparison, the pairs after it wait below what it pushed.
                let pairs = [
                    (&a.guarantee, &b.guarantee),
                    (&a.permission, &b.permission),
                    (&a.value, &b.value),
                ];
                let mut c = Ordering::Equal;
                for (i, &(x, y)) in pairs.iter().enumerate() {
                    let n = steps.len();
                    c = types(x, y, &mut steps, &equal);
                    if c != Ordering::Equal {
                        break;
                    }
                    if steps.len() > n {
                        let rest = pairs[i + 1..].iter().rev();
                        steps.splice(n..n, rest.map(|&(x, y)| Step::Types(x, y)));
                        break;
                    }
                }
                c
            }
            Step::Items(x, y) => items(x, y, &mut steps, &equal),
            Step::Names(p, q, from) => atom_names((p, q), from, &mut steps),
            Step::Lens(p, q, from) => tuple_lens((p, q), from, &mut steps, &equal),
        };
        if c != Ordering::Equal {
            return c;
        }
    }
    Ordering::Equal
}

/// One step of [`order`] on the remaining components of two rows: each pair of components is
/// read at once by [`types`] where its fields decide it, so that two rows told apart without
/// reading a nested type push nothing; at the first pair that needs one, the rest of the rows is
/// pushed below what [`types`] pushed. [`types`] calls neither this nor itself, so the depth of
/// the call stack is fixed.
fn items<'a>(
    mut x: std::slice::Iter<'a, Type>,
    mut y: std::slice::Iter<'a, Type>,
    steps: &mut Vec<Step<'a>>,
    equal: &Equal,
) -> Ordering {
    loop {
        match (x.next(), y.next()) {
            (Some(s), Some(t)) => {
                let n = steps.len();
                let c = types(s, t, steps, equal);
                if c != Ordering::Equal {
                    return c;
                }
                if steps.len() > n {
                    steps.insert(n, Step::Items(x, y));
                    return Ordering::Equal;
                }
            }
            (s, t) => return s.is_some().cmp(&t.is_some()),
        }
    }
}

/// One step of [`order`] on two types: the fields in order, each read at once where it can be,
/// so that two types told apart without reading a nested type push nothing; at the first field
/// that needs a nested comparison (an atom's payload, a tuple length's part, the morphism part)
/// the fields after it are pushed in reverse and the nested comparison above them, so that they
/// are compared in order.
fn types<'a>(a: &'a Type, b: &'a Type, steps: &mut Vec<Step<'a>>, equal: &Equal) -> Ordering {
    if Arc::ptr_eq(&a.0, &b.0) {
        return Ordering::Equal;
    }
    let c = a.digest().cmp(&b.digest());
    if c != Ordering::Equal {
        return c;
    }
    let (p, q) = match (&*a.0, &*b.0) {
        (Node::Parts(p, _), Node::Parts(q, _)) => (p, q),
        (Node::Parts(..), Node::Rec(_)) => return Ordering::Less,
        (Node::Rec(_), Node::Parts(..)) => return Ordering::Greater,
        (Node::Rec(r), Node::Rec(s)) => {
            // The types inside the keys that tie in digest wait on the stack, in order.
            let mut ties = Vec::new();
            let c = r.key.order(&s.key, &mut ties);
            if c.is_eq() {
                steps.extend(ties.into_iter().rev().map(|(x, y)| Step::Types(x, y)));
            }
            return c;
        }
    };
    let c = (p.digest.cmp(&q.digest))
        .then(p.bools.cmp(&q.bools))
        .then_with(|| p.ints.cmp(&q.ints))
        .then_with(|| p.rats.cmp(&q.rats))
        .then_with(|| p.floats.cmp(&q.floats))
        .then_with(|| p.strings.cmp(&q.strings))
        .then(p.atoms.cofinite.cmp(&q.atoms.cofinite));
    if c != Ordering::Equal {
        return c;
    }
    let n = steps.len();
    let names = (&p.atoms.names, &q.atoms.names);
    let c = atom_names(names, Bound::Unbounded, steps);
    if c != Ordering::Equal {
        return c;
    }
    let sum = (p.atoms.sum.cmp(&q.atoms.sum)).then(p.tuples.rest.cmp(&q.tuples.rest));
    let lens = (&p.tuples.lens, &q.tuples.lens);
    if steps.len() > n {
        // A payload ties in digest: the fields after the atoms wait below its contents.
        steps.splice(
            n..n,
            [
                Step::Arrows(Walk::Parts(&p.morphisms, &q.morphisms)),
                Step::Is(p.structs.cmp(&q.structs)),
                Step::Lens(lens.0, lens.1, Bound::Unbounded),
                Step::Is(sum),
            ],
        );
        return Ordering::Equal;
    }
    if sum != Ordering::Equal {
        return sum;
    }
    let c = tuple_lens(lens, Bound::Unbounded, steps, equal);
    if c != Ordering::Equal {
        return c;
    }
    if steps.len() > n {
        // A part ties in digest: the fields after the tuples wait below its contents.
        steps.splice(
            n..n,
            [
                Step::Arrows(Walk::Parts(&p.morphisms, &q.morphisms)),
                Step::Is(p.structs.cmp(&q.structs)),
            ],
        );
        return Ordering::Equal;
    }
    p.structs
        .cmp(&q.structs)
        .then_with(|| walk(Walk::Parts(&p.morphisms, &q.morphisms), steps, equal))
}

/// One step of [`order`] on the atom names of two types after `from`, each with its part, read
/// at once where the names, the bare atoms or the payloads' digests decide them; at the first
/// payload that ties in digest, the rest of the names is pushed (as the last name read) and the
/// two payloads above it. Resuming takes `O(log n)` in the names, read only after a nested
/// comparison.
fn atom_names<'a>(
    (p, q): (&'a AtomNames, &'a AtomNames),
    from: Bound<&'a Arc<str>>,
    steps: &mut Vec<Step<'a>>,
) -> Ordering {
    // Complexity tradeoff: a step resumes by a search, O(log n) in the names, after a nested
    // comparison of at least that cost, rather than holding two iterators, which made each step
    // 208 bytes and the bytes a comparison allocates on ties more than 24x at 8n in the pinwheel
    // tests of `l01_23` (short-addresses build).
    //
    // Two maps on one root are equal, and two that differ nearly always do in their first
    // entries, which `get_min` reads by one descent, while setting up the two ranges took most of
    // a comparison of two atoms of tied digest. With the same for empty sets in `Lits`, that
    // comparison went from 1,629 instructions to 446 (BUCKET-cmp-cost). A first entry that does
    // not decide is read again by the loop.
    if p.ptr_eq(q) {
        return Ordering::Equal;
    }
    if matches!(from, Bound::Unbounded) {
        match (p.get_min(), q.get_min()) {
            (Some((k, u)), Some((l, v))) => {
                let c = k.cmp(l).then(u.bare.cmp(&v.bare)).then_with(|| {
                    match Arc::ptr_eq(&u.payload.0, &v.payload.0) {
                        true => Ordering::Equal,
                        false => u.payload.digest().cmp(&v.payload.digest()),
                    }
                });
                if c != Ordering::Equal {
                    return c;
                }
            }
            (s, t) => return s.is_some().cmp(&t.is_some()),
        }
    }
    let (mut x, mut y) = (
        p.range::<_, Arc<str>>((from, Bound::Unbounded)),
        q.range::<_, Arc<str>>((from, Bound::Unbounded)),
    );
    loop {
        match (x.next(), y.next()) {
            (Some((k, u)), Some((l, v))) => {
                let c = k.cmp(l).then(u.bare.cmp(&v.bare));
                if c != Ordering::Equal {
                    return c;
                }
                if Arc::ptr_eq(&u.payload.0, &v.payload.0) {
                    continue;
                }
                let c = u.payload.digest().cmp(&v.payload.digest());
                if c == Ordering::Equal {
                    steps.extend([
                        Step::Names(p, q, Bound::Excluded(k)),
                        Step::Types(&u.payload, &v.payload),
                    ]);
                }
                return c;
            }
            (s, t) => return s.is_some().cmp(&t.is_some()),
        }
    }
}

/// One step of [`order`] on the tuple lengths of two types after `from`, each with its part,
/// read at once where the lengths or the parts' digests decide them; at the first pair of parts
/// that ties in digest, the rest of the lengths is pushed (as the last length read) below what
/// [`walk`] pushed. Resuming takes `O(log n)` in the lengths, read only after a nested
/// comparison.
fn tuple_lens<'a>(
    (p, q): (&'a Lens, &'a Lens),
    from: Bound<usize>,
    steps: &mut Vec<Step<'a>>,
    equal: &Equal,
) -> Ordering {
    // Complexity tradeoff: as in `atom_names`, O(log n) to resume against a step a fifth the size.
    let (mut x, mut y) = (
        p.range((from, Bound::Unbounded)),
        q.range((from, Bound::Unbounded)),
    );
    loop {
        match (x.next(), y.next()) {
            (Some((k, s)), Some((l, t))) => {
                let c = k.cmp(l);
                if c != Ordering::Equal {
                    return c;
                }
                let n = steps.len();
                let c = walk(Walk::Parts(s, t), steps, equal);
                if c != Ordering::Equal {
                    return c;
                }
                if steps.len() > n {
                    steps.insert(n, Step::Lens(p, q, Bound::Excluded(*k)));
                    return Ordering::Equal;
                }
            }
            (s, t) => return s.is_some().cmp(&t.is_some()),
        }
    }
}

/// One step of [`order`] on two diagrams, expressions or parts of one universe.
fn walk<'a, A: Ordered>(w: Walk<'a, A>, steps: &mut Vec<Step<'a>>, equal: &Equal) -> Ordering {
    match w {
        Walk::Parts(Part::Bdd(a), Part::Bdd(b)) => walk(Walk::Bdds(a, b), steps, equal),
        Walk::Parts(Part::Expr(a), Part::Expr(b)) => walk(Walk::Exprs(a, b), steps, equal),
        Walk::Parts(Part::Bdd(_), Part::Expr(_)) => Ordering::Less,
        Walk::Parts(Part::Expr(_), Part::Bdd(_)) => Ordering::Greater,
        Walk::Bdds(Bdd::Leaf(a), Bdd::Leaf(b)) => a.cmp(b),
        Walk::Bdds(Bdd::Leaf(_), Bdd::List(..)) => Ordering::Less,
        Walk::Bdds(Bdd::List(..), Bdd::Leaf(_)) => Ordering::Greater,
        Walk::Bdds(x @ Bdd::List(a, v), y @ Bdd::List(b, w)) => {
            let c = x.digest().cmp(&y.digest()).then(v.cmp(w));
            if c != Ordering::Equal {
                return c;
            }
            walk(Walk::Cells(Some(a), Some(b)), steps, equal)
        }
        Walk::Cells(None, None) | Walk::Sets(None, None) => Ordering::Equal,
        Walk::Cells(None, Some(_)) | Walk::Sets(None, Some(_)) => Ordering::Less,
        Walk::Cells(Some(_), None) | Walk::Sets(Some(_), None) => Ordering::Greater,
        Walk::Cells(Some(a), Some(b)) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            let c = a.digest.cmp(&b.digest);
            if c == Ordering::Equal {
                // A sequence has one shape, so equal digests are compared cell by cell: the
                // cells before, the blocks, then the cells after, each pushed after the next.
                steps.extend([
                    Step::Equal(key.0, key.1),
                    A::walk(Walk::Cells(a.right.as_deref(), b.right.as_deref())),
                    A::walk(Walk::Sets(Some(&a.block), Some(&b.block))),
                    A::walk(Walk::Cells(a.left.as_deref(), b.left.as_deref())),
                ]);
            }
            c
        }
        Walk::Sets(Some(a), Some(b)) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            let c = a.digest.cmp(&b.digest).then(a.key.1.cmp(&b.key.1));
            if c == Ordering::Equal {
                // The atoms are pushed last, so they are compared first, then the left sets.
                steps.extend([
                    Step::Equal(key.0, key.1),
                    A::walk(Walk::Sets(a.right.as_deref(), b.right.as_deref())),
                    A::walk(Walk::Sets(a.left.as_deref(), b.left.as_deref())),
                    A::atoms(&a.key.0, &b.key.0),
                ]);
            }
            c
        }
        Walk::Exprs(a, b) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            // The digests are compared first: an exclusive or's halves are made only when the
            // digests tie (`Expr::form`).
            let c = a.digest.cmp(&b.digest);
            if c != Ordering::Equal {
                return c;
            }
            let (x, y) = (a.form().operands(), b.form().operands());
            let c = x.0.cmp(&y.0);
            if c == Ordering::Equal {
                steps.push(Step::Equal(key.0, key.1));
                if let (Some(p), Some(q)) = (x.2, y.2) {
                    steps.push(A::walk(Walk::Parts(p, q)));
                }
                steps.push(A::walk(Walk::Parts(x.1, y.1)));
            }
            c
        }
    }
}

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
#[derive(Clone, PartialEq, Eq, Debug, Default)]
struct Lits {
    cofinite: bool,
    values: OrdSet<Value>,
    sum: u64,
}

/// By `cofinite`, then the values in order, then `sum`, as derived; but two equal sets are
/// found equal by `==`, which skips the nodes they share, before the values are read in order.
/// So two equal sets made apart from one set compare in order `log n`, not `n`: the meets of a
/// side `u` with the rows `(int - (2k + 1), int)` make each `u - (2k + 1)` once in the type
/// and again in its boxes (LIST-xor-finite). Two sets on one root, two empty sets among them,
/// are equal before either walk starts: `==` sets up two cursors even then, and every type
/// without literals of a kind compares such a pair (BUCKET-cmp-cost).
// Complexity tradeoff: two unequal sets with equal sums pay for both walks, `==` then the
// ordered one; equal sums of unequal sets are a hash collision.
impl Ord for Lits {
    fn cmp(&self, other: &Lits) -> std::cmp::Ordering {
        self.cofinite.cmp(&other.cofinite).then_with(|| {
            let same = self.values.ptr_eq(&other.values);
            match same || (self.sum == other.sum && self.values == other.values) {
                true => std::cmp::Ordering::Equal,
                false => self
                    .values
                    .cmp(&other.values)
                    .then(self.sum.cmp(&other.sum)),
            }
        })
    }
}

impl PartialOrd for Lits {
    fn partial_cmp(&self, other: &Lits) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
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
        Type(Arc::new(Node::Rec(Rec {
            key,
            name: OnceLock::new(),
            naming: Box::new(naming),
            names: OnceLock::new(),
            body: Mutex::new(None),
            make: Box::new(make),
        })))
    }

    /// Whether this is a recursive member of a group, which its group's decider is asked about.
    pub(crate) fn is_member(&self) -> bool {
        matches!(&*self.0, Node::Rec(r) if r.key.member_at().is_some())
    }

    /// The group of a recursive member, as a number that two members share exactly when they
    /// are members of one instance of a group, and that no other instance has, alive or not.
    pub(crate) fn group(&self) -> Option<u64> {
        match &*self.0 {
            Node::Parts(..) => None,
            Node::Rec(r) => r.key.group(),
        }
    }

    /// Whether `self` is a recursive member whose group's decider has run, so `judged` is O(1).
    pub(crate) fn judged_known(&self) -> bool {
        match &*self.0 {
            Node::Parts(..) => false,
            Node::Rec(r) => r.key.judged_known(),
        }
    }

    /// Whether this is a recursive type by name, not its unfolding.
    fn is_recursive(&self) -> bool {
        matches!(&*self.0, Node::Rec(_))
    }

    /// Whether this is a recursive member on a cycle of its group, or a part kept unevaluated: a
    /// type that may unfold to itself. A member on no cycle unfolds, in a bounded number of steps,
    /// to types none of which is it.
    fn on_cycle(&self) -> bool {
        match &*self.0 {
            Node::Parts(..) => false,
            Node::Rec(r) => r.key.on_cycle(),
        }
    }

    /// The parts, unfolding a recursive node, and its unfolding while that is recursive too.
    fn p(&self) -> PartsRef<'_> {
        match &*self.0 {
            Node::Parts(p, _) => PartsRef::Node(p),
            Node::Rec(r) => {
                let mut t = r.unfolding();
                while let Node::Rec(r) = &*t.0 {
                    let next = r.unfolding();
                    t = next;
                }
                PartsRef::Unfolded(t)
            }
        }
    }

    /// The parts, as [`Type::p`] gives them, borrowed for as long as `held`: a recursive node's
    /// unfolding is put in `held`.
    fn p_held<'a>(&'a self, held: &'a Held) -> &'a Parts {
        match &*self.0 {
            Node::Parts(p, _) => p,
            Node::Rec(_) => {
                let PartsRef::Unfolded(t) = self.p() else {
                    unreachable!("a recursive node's parts are its unfolding's")
                };
                let Node::Parts(p, _) = &*held.put(t).0 else {
                    unreachable!("an unfolding is unfolded to a node of parts")
                };
                p
            }
        }
    }

    /// Drops the unfolding a recursive node keeps (`rec::unfold::end_unit`).
    fn forget_unfolding(&self) {
        if let Node::Rec(r) = &*self.0 {
            r.forget_unfolding();
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

    /// The tuple type `(t1, …, tn)`, or [`Type::empty`] when a component lists no value in
    /// its parts: a product with an empty factor has no value.
    pub fn tuple(items: Vec<Type>) -> Type {
        // Complexity tradeoff: only a component that lists no value in its parts, as
        // `Type::empty` and every tuple built from one, makes the tuple empty here; one whose
        // emptiness only the search proves, as `(int, int) & (bool, int)`, which the tuple
        // part keeps as a meet, or a recursive type with no finite value, is kept as written.
        // Why: the search costs up to the size of the component per tuple built, and this
        // check costs O(1). Trigger: a component empty by a meet, difference or
        // recursion the parts do not show. Tests:
        // `types::tests::a_tuple_with_an_empty_component_is_empty`. COMPLEXITY.md C33. The
        // complete solution runs the memoized `is_empty` on each component; `is_empty`
        // already answers such a tuple right.
        if items.iter().any(Type::lists_nothing) {
            return Type::empty();
        }
        Type::with(|p| p.tuples = Tuples::literal(items))
    }

    /// Whether `self` lists no value in its parts, the form [`Type::empty`] has: O(1). A type
    /// for which this is false may still be empty ([`Type::is_empty`]).
    pub fn lists_nothing(&self) -> bool {
        matches!(&*self.0, Node::Parts(p, _) if p.scalars_only() && !p.has_scalars())
    }

    /// The morphism type with the given bounds and value type.
    pub fn morphism(guarantee: Type, permission: Type, value: Type) -> Type {
        Type::with(|p| p.morphisms = Part::literal(Morphism::new(guarantee, permission, value)))
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
        // Complexity tradeoff: COMPLEXITY.md C22. A type with finitely many values that is not
        // of the forms above (a recursive type, an atom payload, a struct, a function, or a box
        // with an infinite component that a negated tuple type cuts down to finitely many
        // values, such as `(int, 0) - (int - 0, 0)`, which equals `(0, 0)`) is answered "not
        // known finite". The Trick (`zedc::stage::trick`) then keeps the parameter whole, and
        // the type facet of a product cell (`zedc::store::product`) does not list its values.
        // Why: deciding finiteness decides emptiness, since `(int, X)` is finite exactly when
        // `X` is empty, and emptiness of Boolean combinations of tuple types is coNP-hard
        // (`types/empty.rs`); this test reads the type's own parts and boxes once and compares
        // no size. Trigger: any of those forms in the type. Tests:
        // `l01_23_subtyping::scaling::listing_a_diagram_with_exponentially_many_paths_scales`
        // and `l01_28_staging::trick::a_finite_domain_is_split_on_the_values_passed_and_an_infinite_one_is_kept`.
        // A complete solution would decide, for each box with an infinite component, whether
        // the type holds finitely many of its tuples, by the emptiness search with a full case
        // split over the tuple types (exponential in them, or a SAT solver), and would follow
        // atom payloads, struct fields and recursive groups into the types they hold.
        self.finite_order(false).is_some()
    }

    /// The integers of `self`, when they are a finite set of literals. Its users: the checker's
    /// test that the exponent of `x ^ n` is at least 0 (`zedc::check`, `exponent`) and the
    /// type facet of a product cell (`zedc::store::product`).
    pub fn ints_listed(&self) -> Option<Vec<Value>> {
        let p = self.p();
        (!p.ints.cofinite).then(|| p.ints.values.iter().cloned().collect())
    }

    /// The values of `self` when its form writes each of them as a list, `None` otherwise:
    /// `self` is [`Type::finite`], and each tuple type its tuples lie in has components of at
    /// most one value each by their form, at any depth, as `(true, false) | (false, true)` or
    /// `(1, (#a, 2))`. Its scalars and bare atoms are literals of the type, as in `1 | 2 | 3`,
    /// `#red | #green` and `bool`, which is `true | false`. So each value is one literal or one
    /// tuple type of the form, and the values number no more than those, whatever the type.
    /// A tuple type with a component of two or more values, as `(bool, bool)`, `(0 | 1, 0)` or
    /// `t(d)`, `t(i + 1) = (t(i), t(i))`, is a product, which is not a list: its values grow
    /// as the product of its components' counts, so it gives `None`, in time linear in the
    /// type's distinct parts, whatever its number of values. No count is compared with
    /// another: whether a component has one value is read from its form alone. Its user is
    /// the type facet of a product cell (`zedc::store::product`), which lists only these
    /// types' values (COMPLEXITY.md row S34).
    pub fn values_listed(&self) -> Option<Vec<Value>> {
        let order = self.finite_order(false)?;
        // The types of the order with at most one value by their form: at most one literal or
        // tuple type, each component of which is such a type. The order puts each type after
        // the types in its boxes, so a component is decided before the type that holds it.
        let mut single: HashSet<&Type> = HashSet::new();
        let ones = |boxes: &[Row], single: &HashSet<&Type>| {
            boxes.iter().all(|r| r.iter().all(|c| single.contains(c)))
        };
        let (last, below) = order.split_last()?;
        for (t, boxes) in below {
            let p = t.p();
            let literals = p.bools.count_ones() as usize
                + [&p.ints, &p.rats, &p.floats, &p.strings]
                    .iter()
                    .map(|l| l.values.len())
                    .sum::<usize>()
                + p.atoms.names.values().filter(|a| a.bare).count();
            if literals + boxes.len() <= 1 && ones(boxes, &single) {
                single.insert(t);
            }
        }
        ones(&last.1, &single).then(|| self.each_value().map(Iterator::collect))?
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
    /// holds is decided by the kinds of a tuple that has none of its keys (`RowIndex`), the part
    /// read again only where those rows change it (`Graph`); and a tuple is tried once, in the
    /// first box that gives it: the exclusive or of `c` tuple types lists its `c` values in
    /// about `c log c` steps, not `c²` (LIST-parity-quad, LIST-parity-rest, LIST-xor-finite).
    /// Boxes equal in all columns but one are first merged into one box whose column is the
    /// union of theirs, where that union is a set of scalars or a tuple type of one row
    /// (`merge_boxes`): `n` boxes `((u - (2k + 1), 0),)` sharing most of `u` are listed as one
    /// box of `u`, not `n` boxes of `n - 1` values each (LIST-box-overlap). Its user is the
    /// type facet of a product cell (`zedc::store::product`), which keeps the values as a set.
    pub fn each_value(&self) -> Option<Values> {
        let (types, boxes): (Vec<Type>, Vec<Vec<Row>>) =
            self.finite_order(true)?.into_iter().unzip();
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
        let mut numbers = Numbers::default();
        let makers = types
            .into_iter()
            .zip(boxes.into_iter().zip(rows))
            .map(|(t, (boxes, rows))| Maker::new(t, boxes, rows, &mut numbers))
            .collect();
        Some(Values {
            makers,
            numbers,
            given: 0,
        })
    }

    /// The types `self`'s values are built from, each with its boxes and after the types in
    /// them, `self` last, when every one is known finite. One visit per type, kept in a visited
    /// set, and an explicit stack, since the nesting depth follows the input. With `merge`, each
    /// type's boxes are merged ([`merge_boxes`]) before the types in them are visited; the
    /// answer is `None` exactly when it is without, since a merged column is the union of
    /// columns each of which is visited without merging, finite exactly when they all are.
    fn finite_order(&self, merge: bool) -> Option<Vec<(Type, Vec<Row>)>> {
        let mut unions = HashMap::new();
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
            let boxes = match merge {
                true => merge_boxes(t.boxes()?, &mut unions),
                false => t.boxes()?,
            };
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
    /// `self` is finite and every tuple of it is in a tuple type the part names; `None`
    /// otherwise. A diagram gives its boxes as [`list_boxes`] finds them, and an expression
    /// gives them from its operands' ([`part_boxes`]), so a meet with a finite type and an
    /// exclusive or of finite types give finite boxes (LIST-xor-finite).
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
        let mut out = Vec::new();
        for (len, part) in &p.tuples.lens {
            // The tuples outside every tuple type of the part are not listed.
            if part.eval(&|_| false) {
                return None;
            }
            out.extend(part_boxes(part, *len)?.iter().cloned());
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
        let mut todo: Vec<(Type, &Items)> = vec![first];
        loop {
            let (ty, xs) = todo.last().expect("the first test ends the loop");
            let xs = *xs;
            let waiting: RefCell<Vec<(Type, &Items)>> = RefCell::new(Vec::new());
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
            let waiting: Vec<(Type, &Items)> = waiting.into_inner();
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
        if let Some(t) = self.zip_at_once(other, op) {
            return t;
        }
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

    /// `self op other` without building a node, when one operand is the result: `a op a` is
    /// `a`, the empty type joined to `a` or `_` met with it is `a`, and the empty type met with
    /// `a` or `_` joined to it is that operand. Only nodes of parts are taken, so that a
    /// recursive type is never given in place of the parts its union or meet would print as.
    /// EMPTY-morphism-diff-cost: half the unions and meets of a search through nested morphism
    /// types are of these kinds, and each had built a node equal to an operand.
    fn zip_at_once(&self, other: &Type, op: Op) -> Option<Type> {
        let (Node::Parts(..), Node::Parts(..)) = (&*self.0, &*other.0) else {
            return None;
        };
        if Arc::ptr_eq(&self.0, &other.0) {
            return Some(self.clone());
        }
        // The operand that absorbs under `op`, and the one that leaves the other operand.
        let (absorbs, unit) = match op {
            Op::Or => (&TOP, &EMPTY),
            Op::And => (&EMPTY, &TOP),
        };
        let is =
            |t: &Type, k: &'static std::thread::LocalKey<Type>| k.with(|k| Arc::ptr_eq(&t.0, &k.0));
        if is(self, absorbs) || is(other, unit) {
            Some(self.clone())
        } else if is(other, absorbs) || is(self, unit) {
            Some(other.clone())
        } else {
            None
        }
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

impl Parts {
    fn scalars_only(&self) -> bool {
        self.atoms.is_default()
            && self.tuples.is_default()
            && !self.structs
            && self.morphisms.is_leaf() == Some(false)
    }

    /// Whether these are the parts of [`Type::lit`] of `v`, a boolean or a value of its
    /// carrier's part here: that one value in its carrier's part and every other part empty.
    /// Types of parts are equal exactly when their parts are, so this is `Type::lit(v) == t`
    /// for the type `t` of these parts, with no type built.
    fn only(&self, v: &Value) -> bool {
        let lits = [
            (&self.ints, matches!(v, Value::Int(_) | Value::Big(_))),
            (&self.rats, matches!(v, Value::Rat(_))),
            (&self.floats, matches!(v, Value::Float(_))),
            (&self.strings, matches!(v, Value::Str(_))),
        ];
        let bools = match v {
            Value::Bool(b) => 1 << u8::from(*b),
            _ => 0,
        };
        self.bools == bools
            && lits
                .iter()
                .all(|(l, here)| !l.cofinite && l.values.len() == usize::from(*here))
            && self.scalars_only()
    }

    /// Whether it holds a boolean, number or string, read from the parts.
    fn has_scalars(&self) -> bool {
        self.bools != 0
            || [&self.ints, &self.rats, &self.floats, &self.strings]
                .iter()
                .any(|l: &&Lits| l.cofinite || !l.values.is_empty())
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

/// Which universes a type holds values of: the parts [`Type::split`] gives, each true where
/// that gives a type, as [`Type::universes`] reads them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Universes {
    /// Whether it has values of `bool`, `int`, `rat`, `f64` and `String`, in that order.
    pub bases: [bool; 5],
    /// Whether it has atoms.
    pub atoms: bool,
    /// Whether it has tuples, structs or morphisms.
    pub rest: bool,
}

impl Type {
    /// Its one value, when it is one boolean or one literal of `int`, `rat`, `f64` or `String`,
    /// and nothing else: its first such value, read from the parts. A node of parts is that
    /// literal's type exactly when its parts are the literal's (`Parts::only`), which is read
    /// with no type built; a recursive node is compared with the type of the literal alone.
    pub fn scalar(&self) -> Option<Value> {
        let p = self.p();
        let first = |l: &&Lits| match l.cofinite {
            true => None,
            false => l.values.iter().next().cloned(),
        };
        let v = match p.bools {
            1 => Some(Value::Bool(false)),
            2 => Some(Value::Bool(true)),
            _ => [&p.ints, &p.rats, &p.floats, &p.strings]
                .iter()
                .find_map(first),
        }?;
        match &*self.0 {
            Node::Parts(p, _) => p.only(&v).then_some(v),
            Node::Rec(_) => (Type::lit(&v)? == *self).then_some(v),
        }
    }

    /// Whether it may hold an atom, read from its parts: false only when it holds none.
    pub fn may_hold_atoms(&self) -> bool {
        !self.p().atoms.is_default()
    }

    /// The names of its atoms, each with whether it holds the bare atom `#name`, read from its
    /// parts in name order; `None` when it holds the atoms of every name it does not list. A
    /// listed name may hold no value, when its payload type is empty but not built as empty. A
    /// recursive node keeps its unfolding's names, which hold no type, so they outlive the
    /// unfolding (`rec::unfold::end_unit`).
    pub fn atom_names(&self) -> Option<impl Iterator<Item = (&str, bool)>> {
        let (map, list) = match &*self.0 {
            Node::Parts(p, _) => match p.atoms.cofinite {
                true => return None,
                false => (Some(p.atoms.names.iter()), None),
            },
            Node::Rec(r) => {
                let names = r.names.get_or_init(|| {
                    let p = self.p();
                    let names = p.atoms.names.iter();
                    (!p.atoms.cofinite).then(|| names.map(|(n, a)| (n.clone(), a.bare)).collect())
                });
                (None, Some(names.as_deref()?.iter()))
            }
        };
        let map = map.into_iter().flatten().map(|(n, a)| (&**n, a.bare));
        Some(map.chain(list.into_iter().flatten().map(|(n, b)| (&**n, *b))))
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

    /// The larger set with the smaller's literals added. Those it lacks are found by walking
    /// the smaller set, `O(s log l)`, or by a diff of the two, which skips the nodes they
    /// share, so two sets made from one set, as `u - 1` and `u - 3` are made from `u`, are
    /// joined in `O(d log l)` for their `d` differing literals. The two walks advance in turn
    /// and the first to finish is used, as `Atoms::zip` does; a literal already in the larger
    /// set is not inserted again, so the result shares the larger set's nodes and a chain of
    /// such unions stays cheap (LIST-box-overlap).
    // Complexity tradeoff: twice the cheaper walk, so `O(min(s, d + log l) log l)`, against
    // `O(s log l)` alone, which is quadratic for a chain of `n` unions of sets made from one
    // set of `n` literals (COMPLEXITY.md K69).
    fn union(a: &Lits, b: &Lits) -> Lits {
        let (large, small) = if a.values.len() >= b.values.len() {
            (a, b)
        } else {
            (b, a)
        };
        let mut out = large.clone();
        let mut walk = small.values.iter();
        let mut diff = large.values.diff(&small.values);
        let mut missing = Vec::new();
        loop {
            if walk.next().is_none() {
                for v in &small.values {
                    if !large.values.contains(v) {
                        out.insert(v);
                    }
                }
                return out;
            }
            match diff.next() {
                None => break,
                Some(imbl::ordset::DiffItem::Add(v)) => missing.push(v),
                Some(imbl::ordset::DiffItem::Remove(_)) => {}
            }
        }
        for v in missing {
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
    /// Whether it is the part of no atom, `Atoms::default()`, read with nothing built.
    fn is_default(&self) -> bool {
        !self.cofinite && self.names.is_empty() && self.sum == 0
    }

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
    /// Whether it is the part of no tuple, `Tuples::default()`, read with nothing built.
    fn is_default(&self) -> bool {
        !self.rest && self.lens.is_empty()
    }

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
    // Complexity tradeoff (COMPLEXITY.md K19, K39): the naive text copies the texts of the
    // types inside into each type's text, O(n·depth) for a type `depth` deep, and recurses on
    // the thread's stack, which overflows at depth 100,000 on 2 MiB. Used: a rope made once per
    // type and kept with it, holding the inner ropes by reference, made in a loop with a stack
    // of its own, each type tried at most twice, O(text) time. Tradeoffs: every type keeps its
    // rope until dropped (memory O(pieces) per distinct type); a try that finds a text missing
    // is thrown away and made again, at most twice the work.
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
            let missing: Vec<Type> = SHOWING.with_borrow_mut(|s| {
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
            let l: &Lits = l;
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
                let mut sub: Vec<Rope> = Vec::new();
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
    /// The number of each value the makers made.
    numbers: Numbers,
    /// How many values of the listed type have been given.
    given: usize,
}

/// Numbers for the values a [`Values`] makes, equal exactly when the values are: a scalar or
/// bare atom is numbered by its value, a tuple by its components' numbers. Equal values built
/// apart, as two boxes of one type build them, get one number, and a tuple's number is found
/// in the time of its length, whatever the depth of its components.
#[derive(Default)]
struct Numbers {
    leaves: BTreeMap<Value, usize>,
    tuples: HashMap<Vec<usize>, usize>,
}

impl Numbers {
    /// The number of the scalar or bare atom `v`.
    fn leaf(&mut self, v: &Value) -> usize {
        let next = self.leaves.len() + self.tuples.len();
        *self.leaves.entry(v.clone()).or_insert(next)
    }

    /// The number of the tuple whose components have the numbers `items`.
    fn tuple(&mut self, items: Vec<usize>) -> usize {
        let next = self.leaves.len() + self.tuples.len();
        *self.tuples.entry(items).or_insert(next)
    }
}

/// The values of one type of a [`Values`], made one at a time on demand and kept, since every
/// box that reads the type reads them by position.
struct Maker {
    /// Each box with the maker of each of its components.
    boxes: Vec<(Vec<usize>, Row)>,
    /// The rows of the type's diagrams, each with the maker of each of its types, if any.
    rows: BTreeMap<Row, Vec<Option<usize>>>,
    /// Per length, the type's part of that length with its rows by the values they may hold.
    by_value: BTreeMap<usize, RowIndex>,
    /// The tuples tried so far, each once, by their components' numbers ([`Numbers`]): a tuple
    /// an earlier box gave was tried there.
    // Complexity tradeoff: the set holds each distinct tuple tried, memory order the tuples
    // tried times their length, where testing a tuple against the earlier boxes that may hold
    // it kept nothing but cost order `n` per tuple when `n` boxes overlap; a lookup costs the
    // tuple's length, never the depth of its components.
    tried: HashSet<Vec<usize>>,
    /// The box being listed.
    next: usize,
    at: At,
    /// The values made so far: the scalars and bare atoms, then the tuples.
    made: Vec<Value>,
    /// The number of each value made ([`Numbers`]).
    ids: Vec<usize>,
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

/// The one row of `t` when `t` is the tuple type of that row and nothing else.
fn only_row(t: &Type) -> Option<Row> {
    let p = t.p();
    let [(_, part)] = Vec::from_iter(&p.tuples.lens)[..] else {
        return None;
    };
    let [row] = &part.distinct_atoms()[..] else {
        return None;
    };
    (Type::tuple(row.to_vec()) == *t).then(|| row.clone())
}

/// The boxes of one type, for listing ([`Type::each_value`]), with each set of boxes equal in
/// all columns but one merged into one box whose column there is the union of theirs, where
/// that union is known exactly as a set of scalars or a tuple type of one row
/// ([`union_column`]): the union of the products is the product with that column joined. Boxes
/// of one length are merged column by column, each pass grouping the boxes by the wrapping sum
/// of their other columns' hashes, found from the box's sum in constant time, and checking a
/// box against its group's first only when the sums match; the merged box takes the first's
/// place, so the boxes not merged keep their order. A pass costs order `b` for its `b` boxes
/// and `L` for each box checked against another; summed over the `L` passes, the boxes checked
/// number at most `b ln b` (Han's inequality: the projections of `b` points that drop one
/// column number `g_i` with `Σ ln(b / g_i) ≤ ln b`, and `b - g_i ≤ b ln(b / g_i)`).
// Complexity tradeoff: a set of boxes whose union column is neither a set of scalars nor a
// tuple type of one row differing from the others in one scalar column is listed box by box,
// as before, at the cost of every tuple of every box, `n²` for `n` boxes of `n` values that
// overlap. Deciding such a union exactly needs the union type's own boxes, which `|` may give
// as a meet of joins that is not known finite where the boxes were (`part_boxes`). A merged
// tuple type is a new type whose values are made again, `L` per value for its row length `L`,
// once per distinct set of members (kept in `unions`). Test:
// l01_23_subtyping::scaling::finding_the_boxes_of_a_meet_with_an_exclusive_or_scales;
// COMPLEXITY.md K69.
fn merge_boxes(boxes: Vec<Row>, unions: &mut HashMap<Vec<Type>, Option<Type>>) -> Vec<Row> {
    let hash = |j: usize, t: &Type| mix(j as u64, t.digest());
    let mut out = Vec::with_capacity(boxes.len());
    let mut boxes = boxes.into_iter().peekable();
    while let Some(first) = boxes.next() {
        // The boxes of one length, which `Type::boxes` gives together.
        let len = first.len();
        let mut rows = vec![first];
        while let Some(r) = boxes.next_if(|r| r.len() == len) {
            rows.push(r);
        }
        let mut sums: Vec<u64> = rows
            .iter()
            .map(|r| {
                r.iter()
                    .enumerate()
                    .fold(0, |s: u64, (j, t)| s.wrapping_add(hash(j, t)))
            })
            .collect();
        for i in 0..len {
            // Per sum of the other columns, the groups with it, by their members.
            let mut by_sum: HashMap<u64, Vec<usize>> = HashMap::new();
            let mut groups: Vec<Vec<usize>> = Vec::new();
            for (x, r) in rows.iter().enumerate() {
                let ids = by_sum
                    .entry(sums[x].wrapping_sub(hash(i, &r[i])))
                    .or_default();
                let same = ids.iter().copied().find(|&g| {
                    let first = &rows[groups[g][0]];
                    (0..len).all(|j| j == i || first[j] == r[j])
                });
                match same {
                    Some(g) => groups[g].push(x),
                    None => {
                        ids.push(groups.len());
                        groups.push(vec![x]);
                    }
                }
            }
            if groups.len() == rows.len() {
                continue;
            }
            let (mut next, mut next_sums) = (Vec::new(), Vec::new());
            for g in groups {
                let members: Vec<Type> = g.iter().map(|&x| rows[x][i].clone()).collect();
                let union = match g.len() {
                    1 => None,
                    _ => unions
                        .entry(members)
                        .or_insert_with_key(|m| union_column(m))
                        .clone(),
                };
                match union {
                    Some(u) => {
                        let first = &rows[g[0]];
                        let sum = sums[g[0]]
                            .wrapping_sub(hash(i, &first[i]))
                            .wrapping_add(hash(i, &u));
                        let mut items = first.to_vec();
                        items[i] = u;
                        next.push(Row::new(items));
                        next_sums.push(sum);
                    }
                    None => {
                        for x in g {
                            next.push(rows[x].clone());
                            next_sums.push(sums[x]);
                        }
                    }
                }
            }
            (rows, sums) = (next, next_sums);
        }
        out.extend(rows);
    }
    out
}

/// The union of `ts`, two or more distinct column types of boxes, when it is known exactly
/// without reading its own boxes: the union of sets of scalars and bare atoms, made by `|`;
/// or, for tuple types of one row each, equal in all columns but one whose types are such
/// sets, the tuple type of that row with the union in that column. `None` otherwise. The
/// unions are made one at a time into the first, so each set is walked at most once, and sets
/// made from one set are joined by their differing nodes (`Lits::union`).
fn union_column(ts: &[Type]) -> Option<Type> {
    let scalar = |t: &Type| match &*t.0 {
        Node::Parts(p, _) => {
            p.tuples.lens.is_empty()
                && !p.tuples.rest
                && !p.structs
                && p.morphisms.is_leaf() == Some(false)
        }
        _ => false,
    };
    let join = |ts: &mut dyn Iterator<Item = &Type>| {
        let first = ts.next().expect("two or more types").clone();
        ts.fold(first, |u, t| &u | t)
    };
    if ts.iter().all(scalar) {
        return Some(join(&mut ts.iter()));
    }
    let rows: Vec<Row> = ts.iter().map(only_row).collect::<Option<_>>()?;
    let first = &rows[0];
    // The one column where the rows differ.
    let j = (0..first.len()).find(|&j| rows[1].get(j) != Some(&first[j]))?;
    let agree = rows.iter().all(|r| {
        r.len() == first.len()
            && (0..first.len()).all(|k| k == j || r[k] == first[k])
            && scalar(&r[j])
    });
    if !agree {
        return None;
    }
    let mut items = first.to_vec();
    items[j] = join(&mut rows.iter().map(|r| &r[j]));
    Some(Type::tuple(items))
}

/// The tuple type of the meets of the columns of `r` and `s`, two rows of one length.
fn meet_rows(r: &Row, s: &Row) -> Row {
    Row::new(r.iter().zip(s).map(|(x, y)| meet_types(x, y)).collect())
}

/// The boxes of a diagram of tuple types of length `len` ([`Type::boxes`]), or `None` when it
/// holds a tuple outside every tuple type it takes. A value of a diagram is in the last tuple
/// type its path takes, and in the meet of those the path took before; so each node that is
/// the last tuple type taken on a path to `true` gives the box of its tuple type met with the
/// union of the meets on the paths to it, one pass over the nodes, never over the paths. A node
/// whose taken branch meets another tuple type before `true` gives no box of its own, so a meet
/// of tuple types gives its meet in either order of the diagram.
fn list_boxes(b: &Bdd<Row>, len: usize) -> Option<Vec<Row>> {
    if b.eval(|_| false) {
        return None;
    }
    // The meet of a path's tuple types is kept as the meets of runs of them, each with its
    // count, the counts falling from first to last: a run met when one as long follows it. A
    // chain of `c` tuple types is so met in pairs, as `Type::meet_all` meets, where meeting each
    // into the meet of those before it cost order `c²` when their columns grow with the count,
    // as `(int - (2i + 1), 0)` do (LIST-parity-tail).
    let met = |runs: &[(Row, usize)]| {
        let mut runs = runs.iter().rev().map(|(r, _)| r);
        let first = runs
            .next()
            .map_or_else(|| Row::new(vec![Type::top(); len]), Row::clone);
        runs.fold(first, |m, r| meet_rows(&m, r))
    };
    let mut out = Vec::new();
    b.reaching(
        Vec::new(),
        |runs: &Vec<(Row, usize)>, a| {
            let (mut runs, mut last) = (runs.clone(), (a.clone(), 1));
            while let Some((r, n)) = runs.pop_if(|(_, n)| *n <= last.1) {
                last = (meet_rows(&r, &last.0), n + last.1);
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
            out.push(meet_rows(a, &met(runs)));
            true
        },
    );
    Some(out)
}

/// The boxes of a tuple part of length `len` ([`Type::boxes`]), or `None` when they are not
/// found: a diagram's from [`list_boxes`]; an expression's from its operands', the complement
/// taken down to the diagrams by De Morgan's laws. A first pass finds which operands, under
/// which sign, have boxes: a diagram that holds no tuple outside its tuple types, a union of two
/// that have, a meet of one or two that have; so a part has boxes exactly when it is `false`
/// with every tuple type refused. A second pass reads the boxes of those operands only: a
/// union's are those of its operands, each once, and a meet's are those of its one operand
/// that has boxes, or, when both have, those of the operand with fewer boxes, each whose
/// columns are not all finite met with the join of the other's, column by column
/// ([`join_of`]). A box whose columns are finite already holds its part of the meet, and
/// meeting it with a join of `n` tuple types made a type of `n` rows that lists order `n²`
/// candidates. So the exclusive or `p&!q | !p&q` of the one form (module `bdd::xor`) gives the
/// boxes of `p` and of `q`, a meet with a finite type gives finite boxes, and the boxes of a
/// complement that is not finite are never built. Each operand, under each sign, is read once
/// per pass, kept in a map by its id, and the expressions are read from an explicit stack,
/// since a part's operands are shared and nested as deep as the input. The boxes are kept in
/// persistent sets, ordered as rows are, so a union adds the smaller set to the larger, and a
/// chain of `n` unions costs order `n log n`, not the `n²` of copying the growing set.
// Complexity tradeoff: a meet of two operands that both have boxes is given the boxes of the
// one with fewer, each met with the join of the other's, not the meet of every pair, which
// costs the product of their counts at each meet and so grows exponentially along a chain of
// meets of unions. A type whose pairs meet to finite boxes while the join does not, such as
// `((int, 0) | (0, int)) & ((int, 1) | (1, int))` with `(0, 1)` and `(1, 0)`, is not known
// finite, and `each_value` gives `None` for it, as `Type::finite` documents for a box read as
// written. A complete answer needs the pairwise meets, which the product bounds. Tests:
// l01_23_subtyping listing::finiteness_sees_through_meets_and_exclusive_ors and
// scaling::finding_the_boxes_of_a_meet_with_an_exclusive_or_scales; COMPLEXITY row K69.
fn part_boxes(part: &Part<Row>, len: usize) -> Option<OrdSet<Row>> {
    let key = |p: &Part<Row>, negated: bool| (p.expr_id().is_some(), p.id(), negated);
    // Whether an expression read under `negated` joins its operands, by De Morgan's laws.
    let joins = |form: &Form<Row>, negated: bool| matches!(form, Form::Or(..)) != negated;
    enum Step<'a> {
        Read(&'a Part<Row>, bool),
        Combine(&'a Part<Row>, &'a Form<Row>, bool),
    }
    // The first pass: whether each operand under each sign has boxes.
    let mut finite: HashMap<BoxKey, bool> = HashMap::new();
    let mut stack = vec![Step::Read(part, false)];
    while let Some(step) = stack.pop() {
        match step {
            Step::Read(p, negated) => {
                if finite.contains_key(&key(p, negated)) {
                    continue;
                }
                match p.view() {
                    // As `list_boxes` finds: the complement of `b` holds no tuple outside its
                    // tuple types exactly when `b` holds one.
                    Ok(b) => {
                        finite.insert(key(p, negated), b.eval(|_| false) == negated);
                    }
                    Err(form) => {
                        stack.push(Step::Combine(p, form, negated));
                        match form {
                            Form::Not(q) => stack.push(Step::Read(q, !negated)),
                            Form::Or(x, y) | Form::And(x, y) => {
                                stack.push(Step::Read(y, negated));
                                stack.push(Step::Read(x, negated));
                            }
                        }
                    }
                }
            }
            Step::Combine(p, form, negated) => {
                let is = |q: &Part<Row>, negated: bool| finite[&key(q, negated)];
                let has = match form {
                    Form::Not(q) => is(q, !negated),
                    Form::Or(x, y) | Form::And(x, y) if joins(form, negated) => {
                        is(x, negated) && is(y, negated)
                    }
                    Form::Or(x, y) | Form::And(x, y) => is(x, negated) || is(y, negated),
                };
                finite.insert(key(p, negated), has);
            }
        }
    }
    if !finite[&key(part, false)] {
        return None;
    }
    // The second pass: the boxes of the operands found to have them, and of no other.
    let mut found: HashMap<BoxKey, Boxed> = HashMap::new();
    let mut joined: HashMap<BoxKey, Row> = HashMap::new();
    // Per box, whether its columns are finite.
    let mut bounded: BTreeMap<Row, bool> = BTreeMap::new();
    let mut stack = vec![Step::Read(part, false)];
    while let Some(step) = stack.pop() {
        match step {
            Step::Read(p, negated) => {
                if found.contains_key(&key(p, negated)) {
                    continue;
                }
                match p.view() {
                    Ok(b) => {
                        let boxes = if negated {
                            list_boxes(&b.not(), len)
                        } else {
                            list_boxes(b, len)
                        };
                        let boxes = boxes.expect("the first pass found boxes");
                        let boxed = Boxed {
                            boxes: boxes.into_iter().collect(),
                            from: Made::Diagram,
                        };
                        found.insert(key(p, negated), boxed);
                    }
                    Err(form) => {
                        stack.push(Step::Combine(p, form, negated));
                        match form {
                            Form::Not(q) => stack.push(Step::Read(q, !negated)),
                            Form::Or(x, y) | Form::And(x, y) => {
                                for q in [y, x] {
                                    if finite[&key(q, negated)] {
                                        stack.push(Step::Read(q, negated));
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Step::Combine(p, form, negated) => {
                // Each operand that has boxes is read before the expression, and a persistent
                // set is copied in constant time.
                let has = |q: &Part<Row>, negated: bool| {
                    let k = key(q, negated);
                    found.contains_key(&k).then_some(k)
                };
                let (boxes, from) = match form {
                    Form::Not(q) => {
                        let k = key(q, !negated);
                        (found[&k].boxes.clone(), Made::Same(k))
                    }
                    Form::Or(x, y) | Form::And(x, y) => {
                        match (has(x, negated), has(y, negated)) {
                            (Some(a), Some(b)) if joins(form, negated) => {
                                let boxes = found[&a].boxes.clone().union(found[&b].boxes.clone());
                                (boxes, Made::Union(a, b))
                            }
                            (Some(a), Some(b)) => {
                                let (few, many) =
                                    match found[&a].boxes.len() <= found[&b].boxes.len() {
                                        true => (a, b),
                                        false => (b, a),
                                    };
                                // A box whose columns are finite holds the meet already; the others
                                // are met with the join, made only when one needs it.
                                let mut join = None;
                                let mut boxes = OrdSet::new();
                                for r in &found[&few].boxes {
                                    let finite = bounded
                                        .entry(r.clone())
                                        .or_insert_with(|| r.iter().all(Type::finite));
                                    if *finite {
                                        boxes.insert(r.clone());
                                    } else {
                                        let j = join.get_or_insert_with(|| {
                                            join_of(many, &found, &mut joined, len)
                                        });
                                        boxes.insert(meet_rows(r, j));
                                    }
                                }
                                (boxes, Made::Meet(few, many))
                            }
                            (Some(k), None) | (None, Some(k)) => {
                                (found[&k].boxes.clone(), Made::Same(k))
                            }
                            (None, None) => unreachable!("the first pass found boxes"),
                        }
                    }
                };
                found.insert(key(p, negated), Boxed { boxes, from });
            }
        }
    }
    found.remove(&key(part, false)).map(|b| b.boxes)
}

/// A part read under a sign ([`part_boxes`]): an expression or a diagram, its id, and whether it
/// is negated.
type BoxKey = (bool, u64, bool);

/// The boxes of a part read under a sign, and how they were made from its operands'.
struct Boxed {
    boxes: OrdSet<Row>,
    from: Made,
}

/// How the boxes of a [`Boxed`] were made.
enum Made {
    Diagram,
    /// The boxes of the one operand that has them.
    Same(BoxKey),
    Union(BoxKey, BoxKey),
    /// The boxes of the first, each met with the join of the second's.
    Meet(BoxKey, BoxKey),
}

/// A tuple type that holds every box of the part at `key`, column by column: the join of a
/// diagram's boxes, the join of a union's operands' and the meet of a meet's, each made once,
/// when first asked for, from an explicit stack. So a meet with a union that grows along a
/// chain joins each operand once, not the whole union at each meet.
fn join_of(
    key: BoxKey,
    found: &HashMap<BoxKey, Boxed>,
    joined: &mut HashMap<BoxKey, Row>,
    len: usize,
) -> Row {
    let mut stack = vec![key];
    while let Some(&k) = stack.last() {
        if joined.contains_key(&k) {
            stack.pop();
            continue;
        }
        let row = match found[&k].from {
            Made::Diagram => {
                let boxes = &found[&k].boxes;
                // In pairs, as `Type::pairwise` joins.
                let column = |i: usize| {
                    Type::pairwise(boxes.iter().map(|r| r[i].clone()), Type::empty(), |x, y| {
                        &x | &y
                    })
                };
                Some(Row::new((0..len).map(column).collect()))
            }
            Made::Same(a) => joined.get(&a).cloned(),
            Made::Union(a, b) | Made::Meet(a, b) => match (joined.get(&a), joined.get(&b)) {
                (Some(r), Some(s)) if matches!(found[&k].from, Made::Union(..)) => Some(Row::new(
                    r.iter().zip(s.iter()).map(|(x, y)| x | y).collect(),
                )),
                (Some(r), Some(s)) => Some(meet_rows(r, s)),
                _ => {
                    stack.extend([a, b].into_iter().filter(|o| !joined.contains_key(o)));
                    None
                }
            },
        };
        match (row, &found[&k].from) {
            (Some(row), _) => {
                joined.insert(k, row);
                stack.pop();
            }
            (None, Made::Same(a)) => stack.push(*a),
            (None, _) => {}
        }
    }
    joined[&key].clone()
}

/// `x & y`, where both are tuple types of one row each, of one length, as the tuple type of
/// their columns' meets, column by column to any depth: the meet of two tuple types of one
/// row is the tuple type of the meets of their columns, so a run of `c` such meets keeps one
/// row, where `&` keeps a diagram of `c` rows. The boxes of `((2i, i),)` met with each
/// `((int - (2k + 1), x),)` for `k < c` each held all `c` rows, order `c²` to build and to
/// list, and order `c³` where `x` lists `c` values, met with itself at each row
/// (LIST-parity-keys). Equal types meet as themselves, and a type met with `top` is itself: a
/// type equal to it built apart made a row that `Row::new` compared with the live one literal
/// by literal, so a tuple type of `n` literals took order `n` to be found finite
/// (LIST-xor-finite). An explicit stack, since the depth follows the input.
fn meet_types(x: &Type, y: &Type) -> Type {
    let top = Type::top();
    enum Step {
        Meet(Type, Type),
        /// Make the tuple type of the last `n` results.
        Tuple(usize),
    }
    let (mut todo, mut done) = (vec![Step::Meet(x.clone(), y.clone())], Vec::new());
    while let Some(step) = todo.pop() {
        match step {
            Step::Meet(x, y) if x == y || y == top => done.push(x),
            Step::Meet(x, y) if x == top => done.push(y),
            Step::Meet(x, y) => match (only_row(&x), only_row(&y)) {
                (Some(r), Some(s)) if r.len() == s.len() => {
                    todo.push(Step::Tuple(r.len()));
                    let pairs = r.iter().cloned().zip(s.iter().cloned());
                    todo.extend(pairs.rev().map(|(a, b)| Step::Meet(a, b)));
                }
                _ => done.push(&x & &y),
            },
            Step::Tuple(n) => {
                let items = done.split_off(done.len() - n);
                done.push(Type::tuple(items));
            }
        }
    }
    done.pop().expect("the first step leaves one result")
}

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
            let by: &BTreeMap<Value, Vec<usize>> = by;
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
    /// A component other than the first that is no sequence and no scalar or bare atom
    /// ([`erasable`]).
    Value(Value),
    /// A component other than the first that is a scalar or bare atom, by its kind and its
    /// region at its place ([`place_regions`]): scalars of one region there are in each open
    /// row alike.
    Region(Kind, usize),
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
/// not walked, a scalar or bare atom by its region, which `region` gives from the depth, the
/// tuple length, the position and the scalar, and any other by its value.
fn spine(x: &Value, mut region: impl FnMut(usize, usize, usize, &Value) -> usize) -> Vec<Bone> {
    let mut out = Vec::new();
    let mut x = x;
    let mut depth = 0;
    while let Value::Tuple(items) = x
        && let [first, rest @ ..] = items.as_slice()
    {
        out.push(Bone::Len(items.len()));
        out.extend(rest.iter().enumerate().map(|(m, y)| match y {
            Value::Tuple(ys) => Bone::Seq(false, ys.id()),
            Value::Path(ys) => Bone::Seq(true, ys.id()),
            _ => match erasable(y) {
                Some(kind) => Bone::Region(kind, region(depth, items.len(), m + 1, y)),
                None => Bone::Value(y.clone()),
            },
        }));
        x = first;
        depth += 1;
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

/// A place in a column component other than along first components: the column, the depth
/// along first components, the length of the tuple there and the position in it, not 0.
type Place = (usize, usize, usize, usize);

/// The regions of the scalars and bare atoms at the place `(j, d, len, m)` ([`Place`]): per
/// scalar that some type there lists, the region of the types there that list it, numbered
/// from 1 per place. The types there are the components `m` of the tuple types of length
/// `len` of the open rows' types at depth `d` of column `j`, each distinct type read once. A
/// type holds a scalar it does not list as its kind decides, and one it lists as its kind
/// decides the other way, so two scalars of one kind and region are in each type there alike,
/// and a tuple type reads its components and nothing else, so tuples that differ only in such
/// scalars there are in each open row alike (LIST-parity-keys: the `(2i, i)` of `((2i, i),)`
/// met with each `((int - (2i + 1), 0),)` were a class each). A scalar no type there lists is
/// in region 0. The cost is the sum of the distinct types' lists, read once per place.
fn place_regions(open: &[Open], (j, d, len, m): Place) -> BTreeMap<Value, usize> {
    let (mut types, mut parents) = (HashSet::new(), HashSet::new());
    let mut by_key: BTreeMap<Value, Vec<usize>> = BTreeMap::new();
    for t in open
        .iter()
        .filter_map(|row| row.levels.get(j)?.get(d))
        .flatten()
    {
        if !parents.insert(t.clone()) {
            continue;
        }
        let tp = t.p();
        let Some(part) = tp.tuples.lens.get(&len) else {
            continue;
        };
        for r in part.distinct_atoms() {
            let u = &r[m];
            if !types.insert(u.clone()) {
                continue;
            }
            let n = types.len();
            let p = u.p();
            let lists = [&p.ints, &p.rats, &p.floats, &p.strings];
            let atoms = &p.atoms;
            let names = atoms.names.iter().filter(|(_, a)| a.bare != atoms.cofinite);
            for k in lists
                .into_iter()
                .flat_map(|l| l.values.iter().cloned())
                .chain(names.map(|(name, _)| Value::atom(name)))
            {
                by_key.entry(k).or_default().push(n);
            }
        }
    }
    let mut ids: HashMap<Vec<usize>, usize> = HashMap::new();
    by_key
        .into_iter()
        .map(|(k, us)| {
            let next = ids.len() + 1;
            (k, *ids.entry(us).or_insert(next))
        })
        .collect()
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
    /// Per place of a spine, the regions of its scalars ([`place_regions`]), made when first
    /// read.
    places: HashMap<Place, BTreeMap<Value, usize>>,
    /// Per row, how many tuples' checks it changed in.
    changes: Vec<usize>,
    /// The part's nodes ([`Graph`]).
    graph: Graph,
}

/// A decision list of a part, by the rows of a [`RowIndex`]: its value on a tuple is that
/// of the first block with a literal that holds, so it is read from the blocks the rows with
/// a key of the tuple change, and the first block that holds on a tuple with no key of any
/// row ([`Firsts`]), never by walking the list. A restriction of the list to the smallest
/// range of halves that holds those rows reads every row in the range, and the rows are in
/// the order of their hashes, so rows with a key of the tuple, two or more, spread over most
/// of `rows` (LIST-parity-keys: the meet `(0..3, 0..=c) & ((int - (2i + 1), i | i + 1) | ...)`
/// read order `c` rows per tuple).
struct Blocks {
    /// The value of each block, in order.
    values: Vec<bool>,
    /// The value when no literal holds.
    tail: bool,
    /// The list's rows by their position in `rows`, ascending, each with its block and whether
    /// its literal takes the row: each atom of a list is in one block.
    of_row: Vec<(usize, usize, bool)>,
}

/// A part as the graph of its distinct lists and expressions, each once, operands before the
/// expressions that read them and the part last, so that a tuple's value is read by
/// evaluating again only the nodes the rows with a key of the tuple change ([`Graph::apply`]).
/// Evaluating the whole part read every row of an exclusive or for each tuple, `O(n)` for `n`
/// rows (LIST-xor-finite: `(0..n, 0) & ((int - 1, int) ^ (int - 3, int) ^ ...)`, whose rows
/// with a key of a tuple are the side's and one other, far apart in `rows`).
struct Graph {
    nodes: Vec<Vertex>,
    /// Per node, the expressions that read it.
    parents: Vec<Vec<usize>>,
    /// The lists, each with its node.
    lists: Vec<(Blocks, usize)>,
    /// Per row of `rows`, the lists it is in.
    lists_of_row: Vec<Vec<usize>>,
}

/// A node of a [`Graph`]: a list, by its position in `lists`, or a connective on nodes, a
/// union, a meet or an exclusive or of any number of them, the last with the constant joined
/// to them ([`Graph::parities`]).
enum Vertex {
    List(usize),
    Not(usize),
    Or(Vec<usize>),
    And(Vec<usize>),
    Xor(Vec<usize>, bool),
}

/// A [`Graph`] on a tuple of a class with no key of any row.
struct Base {
    /// Per list, its blocks that hold.
    firsts: Vec<Firsts>,
    /// Per node, its value.
    values: Vec<bool>,
    /// Per union or exclusive or, how many of its operands hold; per meet, how many do not.
    counts: Vec<usize>,
}

/// The blocks of a [`Blocks`] on a tuple of a class with no key of any row.
struct Firsts {
    /// Per block, how many of its literals hold.
    holding: Vec<usize>,
    /// The blocks with a literal that holds, ascending.
    any: Vec<usize>,
}

impl Blocks {
    fn new(rows: &[Row], b: &Bdd<Row>) -> Blocks {
        let list = b.list();
        let mut of_row = Vec::new();
        for (k, (_, literals)) in list.blocks.iter().enumerate() {
            for (r, taken) in literals {
                let i = rows
                    .binary_search(r)
                    .expect("every atom of the list is a row");
                of_row.push((i, k, *taken));
            }
        }
        of_row.sort_unstable();
        Blocks {
            values: list.blocks.iter().map(|(v, _)| *v).collect(),
            tail: list.tail,
            of_row,
        }
    }

    /// The blocks that hold on a tuple of the class whose rows have the values `default`.
    fn firsts(&self, default: impl Fn(usize) -> bool) -> Firsts {
        let mut holding = vec![0; self.values.len()];
        for &(i, k, taken) in &self.of_row {
            holding[k] += usize::from(default(i) == taken);
        }
        let any = (0..holding.len()).filter(|&k| holding[k] > 0).collect();
        Firsts { holding, any }
    }

    /// The list's value when its rows at `changed` take the value beside each, the other of
    /// their value on `firsts`' class, in `O(k log n)` for `k` rows of `n`: a block that held
    /// may stop holding only where a changed row is, so the walk over the blocks that held
    /// passes at most `k` of them.
    fn eval(&self, firsts: &Firsts, changed: &[(usize, bool)]) -> bool {
        // Per block a changed row is in, the change in how many of its literals hold.
        let mut delta: Vec<(usize, isize)> = changed
            .iter()
            .map(|&(i, holds)| {
                let at = (self.of_row)
                    .binary_search_by_key(&i, |&(i, _, _)| i)
                    .expect("a changed row of a list is in it");
                let (_, k, taken) = self.of_row[at];
                (k, if holds == taken { 1 } else { -1 })
            })
            .collect();
        delta.sort_unstable();
        delta.dedup_by(|(k, d), (k0, d0)| {
            let same = k == k0;
            if same {
                *d0 += *d;
            }
            same
        });
        let after = |k: usize, d: isize| firsts.holding[k] as isize + d > 0;
        let raised = delta.iter().find(|&&(k, d)| after(k, d)).map(|&(k, _)| k);
        let kept = firsts.any.iter().copied().find(|&k| {
            match delta.binary_search_by_key(&k, |&(k, _)| k) {
                Ok(at) => after(k, delta[at].1),
                Err(_) => true,
            }
        });
        match raised.into_iter().chain(kept).min() {
            Some(k) => self.values[k],
            None => self.tail,
        }
    }
}

impl Graph {
    /// The graph of `part`, whose atoms are among `rows`, from a stack: each node once, kept in
    /// a visited set by its id. A union read by one union only is merged into it, and so a
    /// meet into a meet ([`Graph::merged`]).
    fn new(rows: &[Row], part: &Part<Row>) -> Graph {
        let mut graph = Graph {
            nodes: Vec::new(),
            parents: Vec::new(),
            lists: Vec::new(),
            lists_of_row: vec![Vec::new(); rows.len()],
        };
        // A list's id and an expression's may be equal, so each is keyed with its sort.
        let key = |p: &Part<Row>| (p.expr_id().is_some(), p.id());
        let mut at: HashMap<(bool, u64), usize> = HashMap::new();
        let mut stack = vec![(part, false)];
        while let Some((p, ready)) = stack.pop() {
            if at.contains_key(&key(p)) {
                continue;
            }
            let operands: Vec<&Part<Row>> = match p.view() {
                Ok(_) => Vec::new(),
                Err(Form::Not(a)) => vec![a],
                Err(Form::Or(a, b) | Form::And(a, b)) => vec![a, b],
            };
            if !ready {
                stack.push((p, true));
                stack.extend(operands.into_iter().map(|q| (q, false)));
                continue;
            }
            let n = graph.nodes.len();
            let of = |q: &Part<Row>| at[&key(q)];
            let node = match p.view() {
                Ok(b) => {
                    let blocks = Blocks::new(rows, b);
                    for &(i, _, _) in &blocks.of_row {
                        graph.lists_of_row[i].push(graph.lists.len());
                    }
                    graph.lists.push((blocks, n));
                    Vertex::List(graph.lists.len() - 1)
                }
                Err(Form::Not(a)) => Vertex::Not(of(a)),
                Err(Form::Or(a, b)) => Vertex::Or(vec![of(a), of(b)]),
                Err(Form::And(a, b)) => Vertex::And(vec![of(a), of(b)]),
            };
            graph.nodes.push(node);
            at.insert(key(p), n);
        }
        graph.parities().merged()
    }

    /// The graph with each choice `c&x | !c&!x` between two complements, and each
    /// `(x|y) & (!x|!y)`, made one exclusive or ([`Vertex::Xor`]) of the nodes `x` and `y` are
    /// made from, where nodes are known complements by their forms: a list is the complement
    /// of one with the same rows and the other value in every block and its tail, `!a` is
    /// `a`'s, and two exclusive ors of the same nodes with other constants are complements.
    /// Each node is kept as a node and a polarity (`canon`), equal for equal lists and
    /// exclusive ors and opposite for complements, so an exclusive or of a chain reads the
    /// previous link and never its complement, which is read no more. The exclusive or of `n`
    /// meets `t(i) = s & r(i)` with a common side, made as `(x - t) | (t - x)` one at a time,
    /// is otherwise a chain of `n` such choices and their complements, every link of which a
    /// change of `r(0)` changes (LIST-box-overlap); merged ([`Graph::merged`]), it is one
    /// exclusive or that counts its operands that hold.
    // Complexity tradeoff: each node is checked once, in constant time but for its key, a
    // list's blocks or an exclusive or's two operands; a choice whose halves are not known
    // complements by these forms stays a union of meets. Naive version (COMPLEXITY.md K69,
    // item 10): the chain left as built, `n` choices and their complements, each changed by a
    // change of `r(0)`, so a check reads order `n` nodes per tuple, O(n²) over the listing;
    // used: one pass over the nodes, O(nodes), then a change reaches one exclusive or.
    fn parities(mut self) -> Graph {
        let mut canon: Vec<(usize, bool)> = Vec::with_capacity(self.nodes.len());
        // A list by its rows and each block's value, flipped so its tail is false.
        type ListKey = (Vec<(usize, usize, bool)>, Vec<bool>);
        let mut lists: HashMap<ListKey, (usize, bool)> = HashMap::new();
        let mut xors: HashMap<[usize; 2], (usize, bool)> = HashMap::new();
        for n in 0..self.nodes.len() {
            let opposite = |canon: &[(usize, bool)], a: usize, b: usize| {
                canon[a].0 == canon[b].0 && canon[a].1 != canon[b].1
            };
            // The two operands of a binary node.
            let two = |v: &Vertex| match v {
                Vertex::Or(xs) | Vertex::And(xs) if xs.len() == 2 => Some([xs[0], xs[1]]),
                _ => None,
            };
            let choice = match &self.nodes[n] {
                Vertex::Or(_) | Vertex::And(_) => (|| {
                    let [p, q] = two(&self.nodes[n])?;
                    let inner = |x: usize| {
                        let alike = matches!(
                            (&self.nodes[n], &self.nodes[x]),
                            (Vertex::Or(_), Vertex::And(_)) | (Vertex::And(_), Vertex::Or(_))
                        );
                        alike.then(|| two(&self.nodes[x])).flatten()
                    };
                    let ([a, b], [c, d]) = (inner(p)?, inner(q)?);
                    let pairs = opposite(&canon, a, c) && opposite(&canon, b, d)
                        || opposite(&canon, a, d) && opposite(&canon, b, c);
                    // `a&b | !a&!b` is `!(a ^ b)`; `(a|b) & (!a|!b)` is `a ^ b`.
                    let negated = matches!(self.nodes[n], Vertex::Or(_));
                    (pairs && canon[a].0 != canon[b].0).then_some((a, b, negated))
                })(),
                _ => None,
            };
            let own = (n, false);
            let c = match (&self.nodes[n], choice) {
                (_, Some((a, b, negated))) => {
                    let ((x, px), (y, py)) = (canon[a], canon[b]);
                    let constant = negated ^ px ^ py;
                    let key = [x.min(y), x.max(y)];
                    let &mut (e, ce) = xors.entry(key).or_insert((n, constant));
                    self.nodes[n] = Vertex::Xor(key.to_vec(), constant);
                    (e, constant ^ ce)
                }
                (Vertex::List(l), None) => {
                    let b = &self.lists[*l].0;
                    let flip = b.tail;
                    let key = (
                        b.of_row.clone(),
                        b.values.iter().map(|&v| v ^ flip).collect(),
                    );
                    let &mut (e, fe) = lists.entry(key).or_insert((n, flip));
                    (e, flip ^ fe)
                }
                (Vertex::Not(a), None) => (canon[*a].0, !canon[*a].1),
                _ => own,
            };
            canon.push(c);
            // A node equal to an earlier one, or its complement, reads it.
            if c.0 != n {
                self.nodes[n] = Vertex::Xor(vec![c.0], c.1);
            }
        }
        self
    }

    /// The graph with each union read by one union only merged into it, and each meet read by
    /// one meet only into it, and so each exclusive or into an exclusive or, each operand of a
    /// union or meet once and of an exclusive or once or not at all, and the readers of each
    /// node the part reads. A union of `n` parts made one at a time is a chain of `n` unions,
    /// whose every node a changed row of the first part changed ([`Graph::apply`]); merged, the
    /// chain is one union that counts its operands that hold.
    // Complexity tradeoff: a merged node takes the operand list of its largest merged operand
    // and adds the others to it, so each operand moves order `log n` times; the lists are then
    // sorted, order `n log n` for `n` nodes. Naive version: the chain of unions not merged,
    // read again node by node for each candidate, order `n` per candidate (K69: listing 25
    // times at 8n with the chain not merged).
    fn merged(mut self) -> Graph {
        let len = self.nodes.len();
        let operands = |v: &Vertex| -> Vec<usize> {
            match v {
                Vertex::List(_) => Vec::new(),
                Vertex::Not(a) => vec![*a],
                Vertex::Or(xs) | Vertex::And(xs) | Vertex::Xor(xs, _) => xs.clone(),
            }
        };
        // The nodes the part reads, operands before readers.
        let read = |nodes: &[Vertex]| {
            let mut read = vec![false; len];
            read[len - 1] = true;
            for n in (0..len).rev() {
                if read[n] {
                    operands(&nodes[n]).into_iter().for_each(|x| read[x] = true);
                }
            }
            read
        };
        let reached = read(&self.nodes);
        let mut readers = vec![0usize; len];
        for n in (0..len).filter(|&n| reached[n]) {
            operands(&self.nodes[n])
                .into_iter()
                .for_each(|x| readers[x] += 1);
        }
        let alike = |a: &Vertex, b: &Vertex| {
            matches!(
                (a, b),
                (Vertex::Or(_), Vertex::Or(_))
                    | (Vertex::And(_), Vertex::And(_))
                    | (Vertex::Xor(..), Vertex::Xor(..))
            )
        };
        // Operands come before their readers, so a merged operand is merged already.
        for n in (0..len).filter(|&n| reached[n]) {
            let operands = match &mut self.nodes[n] {
                Vertex::Or(xs) | Vertex::And(xs) | Vertex::Xor(xs, _) => std::mem::take(xs),
                Vertex::List(_) | Vertex::Not(_) => continue,
            };
            let (mut kept, mut taken): (Vec<usize>, Vec<Vec<usize>>) = (Vec::new(), Vec::new());
            let mut flip = false;
            for x in operands {
                if readers[x] == 1 && alike(&self.nodes[x], &self.nodes[n]) {
                    // `x` is read by `n` alone, and is read no more.
                    readers[x] = 0;
                    match &mut self.nodes[x] {
                        Vertex::Or(ys) | Vertex::And(ys) => taken.push(std::mem::take(ys)),
                        Vertex::Xor(ys, c) => {
                            flip ^= *c;
                            taken.push(std::mem::take(ys));
                        }
                        Vertex::List(_) | Vertex::Not(_) => unreachable!("x is like n"),
                    }
                } else {
                    kept.push(x);
                }
            }
            taken.push(kept);
            let largest = (0..taken.len())
                .max_by_key(|&i| taken[i].len())
                .expect("taken holds `kept`");
            let mut all = taken.swap_remove(largest);
            taken.into_iter().for_each(|ys| all.extend(ys));
            match &mut self.nodes[n] {
                Vertex::Or(xs) | Vertex::And(xs) => *xs = all,
                Vertex::Xor(xs, c) => {
                    *xs = all;
                    *c ^= flip;
                }
                Vertex::List(_) | Vertex::Not(_) => {
                    unreachable!("n is a union, meet or exclusive or")
                }
            }
        }
        // `p | p` reads its operand once, `p ^ p` not at all. A merged node is read by none and
        // reads none, and a node the part does not read is read by none.
        let reached = read(&self.nodes);
        self.parents = vec![Vec::new(); len];
        for n in (0..len).filter(|&n| reached[n]) {
            match &mut self.nodes[n] {
                Vertex::List(_) => {}
                Vertex::Not(a) => self.parents[*a].push(n),
                Vertex::Or(xs) | Vertex::And(xs) => {
                    xs.sort_unstable();
                    xs.dedup();
                    xs.iter().for_each(|&x| self.parents[x].push(n));
                }
                Vertex::Xor(xs, _) => {
                    xs.sort_unstable();
                    let mut odd: Vec<usize> = Vec::with_capacity(xs.len());
                    for &x in xs.iter() {
                        match odd.last() == Some(&x) {
                            true => {
                                odd.pop();
                            }
                            false => odd.push(x),
                        }
                    }
                    *xs = odd;
                    xs.iter().for_each(|&x| self.parents[x].push(n));
                }
            }
        }
        // A list the part does not read is read again for no tuple.
        for lists in &mut self.lists_of_row {
            lists.retain(|&l| {
                let n = self.lists[l].1;
                reached[n] && matches!(self.nodes[n], Vertex::List(_))
            });
        }
        self
    }

    /// Each node's value on a tuple of the class whose rows have the values `default`.
    fn base(&self, default: impl Fn(usize) -> bool) -> Base {
        let firsts: Vec<Firsts> = (self.lists.iter())
            .map(|(b, _)| b.firsts(&default))
            .collect();
        let mut values: Vec<bool> = Vec::with_capacity(self.nodes.len());
        let mut counts: Vec<usize> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let (v, count) = match node {
                Vertex::List(l) => (self.lists[*l].0.eval(&firsts[*l], &[]), 0),
                Vertex::Not(a) => (!values[*a], 0),
                Vertex::Or(xs) => {
                    let holding = xs.iter().filter(|&&x| values[x]).count();
                    (holding > 0, holding)
                }
                Vertex::And(xs) => {
                    let failing = xs.iter().filter(|&&x| !values[x]).count();
                    (failing == 0, failing)
                }
                Vertex::Xor(xs, c) => {
                    let holding = xs.iter().filter(|&&x| values[x]).count();
                    ((holding % 2 == 1) ^ c, holding)
                }
            };
            values.push(v);
            counts.push(count);
        }
        Base {
            firsts,
            values,
            counts,
        }
    }

    /// The changes to `base`, already changed by `under`, when the rows at `changed`, none of
    /// them in `under`, also take the value beside each, the other of their value on `base`'s
    /// class: the lists those rows are in are read from their blocks ([`Blocks::eval`]), with
    /// `under`'s rows in them, and a node whose operand changed is evaluated again, operands
    /// first, a union by how many of its operands hold and a meet by how many do not, so a
    /// changed operand costs its reader order 1. The exclusive or of `n` rows is a tree of
    /// depth `O(log n)` in expectation (module `xor` of `bdd`), so a changed row changes
    /// `O(log n)` expressions, and a union of `n` parts is one node ([`Graph::merged`]).
    // Complexity tradeoff: a tuple costs the nodes whose value its changed rows change, each
    // with its readers; a node read by many expressions, such as the side of a meet distributed
    // over a union, sends the change to each, which `RowIndex::holds` pays once per set of rows
    // that recurs (`Class::under`). Evaluating the whole part costs every node for every tuple.
    fn apply(&self, base: &Base, under: &Overlay, changed: &[(usize, bool)]) -> Overlay {
        let mut by_list: BTreeMap<usize, Vec<(usize, bool)>> = BTreeMap::new();
        for &(i, holds) in changed {
            for &l in &self.lists_of_row[i] {
                by_list.entry(l).or_default().push((i, holds));
            }
        }
        let mut out = Overlay::default();
        let mut dirty = BTreeSet::new();
        let change = |n: usize, v: bool, out: &mut Overlay, dirty: &mut BTreeSet<usize>| {
            out.now.insert(n, v);
            for &p in &self.parents[n] {
                let d = match (&self.nodes[p], v) {
                    (Vertex::Or(_) | Vertex::Xor(..), true) | (Vertex::And(_), false) => 1,
                    (Vertex::Or(_) | Vertex::Xor(..), false) | (Vertex::And(_), true) => -1,
                    (Vertex::List(_) | Vertex::Not(_), _) => 0,
                };
                *out.delta.entry(p).or_default() += d;
                dirty.insert(p);
            }
        };
        for (l, mut rows) in by_list {
            rows.extend(under.rows.get(&l).into_iter().flatten().copied());
            let (blocks, n) = &self.lists[l];
            let was = under.value(base, *n);
            if blocks.eval(&base.firsts[l], &rows) != was {
                change(*n, !was, &mut out, &mut dirty);
            }
            out.rows.insert(l, rows);
        }
        // Operands come before their readers, so a node taken lowest first has its operands'
        // values settled.
        while let Some(n) = dirty.pop_first() {
            let count = || {
                let d = |o: &Overlay| o.delta.get(&n).copied().unwrap_or(0);
                base.counts[n] as isize + d(under) + d(&out)
            };
            let v = match &self.nodes[n] {
                Vertex::List(_) => unreachable!("a list reads no node"),
                Vertex::Not(a) => !out.now.get(a).copied().unwrap_or(under.value(base, *a)),
                Vertex::Or(_) => count() > 0,
                Vertex::And(_) => count() == 0,
                Vertex::Xor(_, c) => (count().rem_euclid(2) == 1) ^ c,
            };
            if v != under.value(base, n) {
                change(n, v, &mut out, &mut dirty);
            }
        }
        out
    }

    /// The part's value on `base` changed by `under` and then by `over`, made from it.
    fn root(&self, base: &Base, under: &Overlay, over: &Overlay) -> bool {
        let root = self.nodes.len() - 1;
        over.now
            .get(&root)
            .copied()
            .unwrap_or(under.value(base, root))
    }
}

/// The changes some rows make to a [`Base`] ([`Graph::apply`]).
#[derive(Default)]
struct Overlay {
    /// Per list those rows are in, they and their values.
    rows: BTreeMap<usize, Vec<(usize, bool)>>,
    /// The nodes whose value changes, by their value.
    now: HashMap<usize, bool>,
    /// Per union or meet, the change in its count.
    delta: HashMap<usize, isize>,
}

impl Overlay {
    /// The value of node `n`.
    fn value(&self, base: &Base, n: usize) -> bool {
        self.now.get(&n).copied().unwrap_or(base.values[n])
    }
}

/// The rows of a [`RowIndex`] as a class of tuples sees them.
struct Class {
    /// Per open row, its value on a tuple of the class none of whose components is a key of
    /// it.
    open: Vec<bool>,
    /// The part's nodes on such a tuple, made when first needed.
    base: Option<Base>,
    /// Per set of changed rows a tuple's check applied before its last row, the changes they
    /// make to `base`, kept from the second time the set recurs: each value of the side of a
    /// meet distributed over `n` operands changes the side and one operand, and the side's
    /// change, read by all `n`, is made once, not once per value (LIST-box-overlap).
    // Complexity tradeoff: a set's changes are kept, order the nodes they change, only when it
    // recurs, so the memory kept is at most the time spent making them a second time; a set
    // seen once costs its key. Naive version: no memo, the side's change made again for each
    // value, read by all `n` operands, order `n` per value (K69, LIST-box-overlap); used: made
    // once per recurring set, then a hash lookup costing the set's length.
    under: HashMap<Vec<(usize, bool)>, Option<Overlay>>,
    /// Per set of changed rows a tuple's check applied, the part's value: a set every tuple of
    /// a box changes, such as the side of a meet alone, is applied once.
    // Complexity tradeoff: one entry per set applied, its key the size of the set, so at most
    // the time spent applying it. Naive version: the set applied again for every tuple of the
    // box, its changed nodes each time; used: applied once, then a hash lookup costing the
    // set's length (K69).
    known: HashMap<Vec<(usize, bool)>, bool>,
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
            let classes: BTreeSet<&Vec<usize>> = by_key
                .values()
                .filter(|rs: &&Vec<usize>| !rs.is_empty())
                .collect();
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
        let graph = Graph::new(&rows, part);
        let rows_len = rows.len();
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
            places: HashMap::new(),
            changes: vec![0; rows_len],
            graph,
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
                        let mut next: Vec<Type> = Vec::new();
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

    /// Whether the tuple `v` is in the part indexed; `fits` tells whether a row holds `v`. The
    /// rows with a key of `v` whose value on it is not their value on its class change the
    /// part's nodes on the class, made once per class, and only the nodes they change are
    /// evaluated again ([`Graph::apply`]). A tuple's kinds
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
    // spine is a class, and a scalar or bare atom in a spine is given by its region at its
    // place ([`place_regions`]): the `(2i, i)` of `((2i, i),)` met with each `((int - (2i +
    // 1), x),)` are one class for any `x` that lists none or all of the `i`, and one class
    // per set of the open rows' types listing it otherwise, never one per tuple
    // (LIST-parity-keys: 46 times the instructions from `c` 64 to 512 per tuple class). The
    // regions of a place cost the sum of the lists of the distinct types there, once.
    // A column is absorbed only where its regions, each a class reading every open row, cost
    // no more than filing its rows by it ([`RowIndex::new`]); the verdicts are the same either
    // way.
    fn holds(&mut self, v: &[Value], fits: impl Fn(&Row) -> bool) -> bool {
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
            places,
            changes,
            graph,
            ..
        } = self;
        let decided = &by_kinds[&kinds];
        let key = ClassKey {
            regions: v
                .iter()
                .zip(regions.iter())
                .map(|(x, by): (&Value, &BTreeMap<Value, usize>)| {
                    match by.is_empty() || !whole(x) {
                        true => None,
                        false => Some(by.get(x).copied().unwrap_or(0)),
                    }
                })
                .collect(),
            shape: match decided.iter().all(Option::is_some) {
                true => Shape::Kinds(kinds),
                false => Shape::Spine(
                    v.iter()
                        .enumerate()
                        .map(|(j, x)| {
                            spine(x, |d, len, m, y| {
                                let place = (j, d, len, m);
                                let by = places
                                    .entry(place)
                                    .or_insert_with(|| place_regions(open_rows, place));
                                by.get(y).copied().unwrap_or(0)
                            })
                        })
                        .collect(),
                ),
            },
        };
        let Class {
            open,
            base,
            under,
            known,
        } = classes.entry(key).or_insert_with(|| {
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
                base: None,
                under: HashMap::new(),
                known: HashMap::new(),
            }
        });
        let (rows, filing, open) = (&*rows, &*filing, &*open);
        let base = base.get_or_insert_with(|| graph.base(|i| row_default(filing, open, i)));
        // A row that may hold `v` either has a key of `v`, and is in `at`, or holds it as its
        // value on a tuple of the class with no key of it.
        let mut changed: Vec<(usize, bool)> = at
            .iter()
            .map(|&i| (i, fits(&rows[i])))
            .filter(|&(i, holds)| holds != row_default(filing, open, i))
            .collect();
        // The rows that changed most often first, so that all but the last are the rows tuples
        // share, such as the side of a meet, which each value of the side changes; their
        // changes are kept from the second time they recur on (`Class::under`).
        for &(i, _) in &changed {
            changes[i] += 1;
        }
        changed.sort_unstable_by_key(|&(i, _)| (std::cmp::Reverse(changes[i]), i));
        if let Some(&holds) = known.get(&changed) {
            return holds;
        }
        let none = Overlay::default();
        let Some((last, shared)) = changed.split_last() else {
            return graph.root(base, &none, &none);
        };
        let shared: &[(usize, bool)] = shared;
        let once;
        let under = match under.get_mut(shared) {
            _ if shared.is_empty() => &none,
            None => {
                under.insert(shared.to_vec(), None);
                once = graph.apply(base, &none, shared);
                &once
            }
            Some(kept) => kept.get_or_insert_with(|| graph.apply(base, &none, shared)),
        };
        let over = graph.apply(base, under, std::slice::from_ref(last));
        let holds = graph.root(base, under, &over);
        known.insert(changed, holds);
        holds
    }
}

impl Maker {
    fn new(
        ty: Type,
        boxes: Vec<(Vec<usize>, Row)>,
        rows: BTreeMap<Row, Vec<Option<usize>>>,
        numbers: &mut Numbers,
    ) -> Maker {
        let p = ty.p();
        let made = scalars(&p);
        let ids = made.iter().map(|v| numbers.leaf(v)).collect();
        let by_value = p
            .tuples
            .lens
            .iter()
            .map(|(&len, part)| (len, RowIndex::new(len, part)))
            .collect();
        Maker {
            boxes,
            rows,
            by_value,
            tried: HashSet::new(),
            next: 0,
            at: At::Start,
            made,
            ids,
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
    fn step(makers: &mut [Maker], numbers: &mut Numbers, me: usize) -> Result<(), Need> {
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
                let key: Vec<usize> = cols
                    .iter()
                    .zip(&pos)
                    .map(|(&c, &i)| below[c].ids[i])
                    .collect();
                // A tuple is given by the first box that has it, and is tried there. Within one
                // box the positions give distinct tuples, since each maker gives each value
                // once, and a box's makers give every value of its columns. The tuple is
                // looked up by its components' numbers, never by their contents.
                m.at = At::Past(pos);
                if !m.tried.insert(key.clone()) {
                    return Ok(());
                }
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
                if index.holds(&v, fits) {
                    m.made.push(Value::tuple(v));
                    m.ids.push(numbers.tuple(key));
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
                    if let Err(need) = Maker::step(&mut self.makers, &mut self.numbers, m) {
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

/// The outcomes of a check; each has its own message.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// No value is in the type.
    Empty,
    /// A value in the type was built and checked against it.
    Inhabited,
    /// Not proved empty, and no value built: nothing is claimed about the type.
    Refused(Refusal),
}

/// Why a check was refused.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Refusal {
    /// A tuple part holds two tuple types open on one box that differ in a recursive
    /// component, or two that narrowing takes out of one component with different recursive
    /// types there, each on a cycle of its group (`Type::on_cycle`); and no value was found.
    /// Following both is the subset construction, exponential in the recursive types; every
    /// NFA universality question (PSPACE-complete) is such a difference of list types, and
    /// unless P = PSPACE the ones refused here are not all decidable in polynomial time
    /// (COMPLEXITY.md K35).
    Fork,
    /// Negated lists of periodic lengths: whether they cover the lengths left is the covering
    /// problem for residues, which is NP-hard.
    Residues,
    /// A tuple part that only a split of the box in more than one component at once decides.
    TupleSplit,
    /// A tuple part of one choice per component with an `&` or `|` whose operands share this
    /// component through different cells and are not both decision lists or exclusive ors:
    /// deciding it is the Orthogonal Vectors problem.
    SharedCells(usize),
    /// A morphism part that neither the meets it forces nor a split into its morphism types
    /// decides.
    MorphismSplit,
    /// The search ended with the type not proved empty, and no value of it was built.
    NoWitness,
    /// The type is, or reads, a member of a recursive group whose decider (module `bes`) left
    /// it undecided, and which the search for a value then left undecided too: a component
    /// mixing cycles through tuples and through the value types of function types, with two or
    /// more independent cycles and a tuple with two undecided components (DESIGN.md L1.23). The
    /// definitions, cycles and tuple are named by [`Type::refusal_site`].
    Group,
}

impl Refusal {
    /// What the refusal says to the programmer.
    pub fn message(self) -> String {
        let text = match self {
            Refusal::Fork => {
                "no value of it was found, and two of the tuple types involved differ in a \
                 component whose type refers back to itself; following both at once can take \
                 time exponential in the size of the types, so the checker does not try; write \
                 the two tuple types so that they agree in that component, or test the value \
                 with `is` first"
            }
            Refusal::Residues => {
                "the types involved allow list lengths that repeat with a period, and telling \
                 whether the lengths they exclude cover all the lengths left can take time \
                 exponential in the number of periods, so the checker does not try; write the \
                 lengths allowed as one list type, or test the length with `is` first"
            }
            Refusal::TupleSplit => {
                "one part of the tuple types involved is decided only by splitting more than \
                 one of its components into cases at once, which the checker does not do; \
                 write those cases out as a union of tuple types"
            }
            Refusal::SharedCells(j) => {
                return format!(
                    "the tuple types involved combine, with `&` or `|`, types that restrict \
                     component {j} of a tuple in different ways, and comparing every pair of \
                     them takes time that grows with the square of their number, so the \
                     checker does not try; write the combination as a union of cases on \
                     component {j}"
                );
            }
            Refusal::MorphismSplit => {
                "one part of the function types involved is decided neither by the types its \
                 arguments must have nor by splitting it into its separate function types; \
                 write the function type as one type `(…) -> …`, or as a union of them"
            }
            Refusal::NoWitness => {
                "the checker could neither show that no value has the type nor build a value \
                 that has it; write the type more simply, or test the value with `is` first"
            }
            Refusal::Group => {
                "the type refers to recursive definitions that reach each other both through \
                 tuples, which a value cannot go around forever, and through the results of \
                 function types, which a value can; deciding such a group takes time that \
                 grows with the square of its size, while the checker decides each group in \
                 time linear in it, and a search for a value neither finds one nor shows that \
                 there is none, so it counts the type as possibly having a value; add a \
                 case such as `| #end` to one of the definitions"
            }
        };
        text.to_owned()
    }
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message())
    }
}

/// Where a refused check points, when it rests on a recursive group ([`Type::refusal_site`]).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GroupSite {
    /// The definition the refusal points at: the member whose answer was being decided.
    pub head: String,
    /// Each definition that takes part, as `type name = body`: the head first, then by name.
    pub defs: Vec<String>,
    /// For a refusal by the group's decider (`Refusal::Group`), the whole reason, written to
    /// follow "because".
    pub detail: Option<String>,
}

/// A type in the surface syntax: the definitions it needs, in order, then the type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Surface {
    /// Each definition's name and body.
    pub defs: Vec<(String, String)>,
    /// The type, which may name the definitions.
    pub root: String,
    /// Whether every word is in the surface syntax (the module comment names the exceptions).
    pub exact: bool,
}

/// Several types in the surface syntax with one set of definitions ([`Type::surfaces_by_name`]):
/// the definitions come before the whole text the types stand in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Surfaces {
    /// Each definition's name and body.
    pub defs: Vec<(String, String)>,
    /// Each type's text, in the order given, which may name the definitions.
    pub roots: Vec<String>,
    /// Whether every word is in the surface syntax.
    pub exact: bool,
}

/// Where a text stands, and so which classes it may have there unparenthesized: anywhere, as an
/// operand of `|`, of `&`, the left of `\`, an operand of any connective, the key of an arrow,
/// or a bound of `L .. U -> V` ([`Type::surface_by_name`]).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum TextPlace {
    /// Anywhere: the whole of a type.
    Any,
    /// An operand of `|`.
    Union,
    /// An operand of `&`.
    And,
    /// The left of `\`.
    DiffLeft,
    /// An operand of any connective.
    Prim,
    /// The key of an arrow, `K -> V`.
    Key,
    /// A bound of `L .. U -> V`.
    Bound,
}

impl fmt::Display for Surface {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, body) in &self.defs {
            defs::declare(f, name, body)?;
        }
        f.write_str(&self.root)
    }
}

pub mod rec {
    //! Recursive type definitions (step L1.23, DESIGN.md sec:type_language): a group of mutually
    //! recursive definitions, checked when it is defined and instantiated at its arguments.
    //!
    //! A group is accepted when it is
    //! - *contractive*: every cycle of recursive occurrences passes through a constructor (a tuple
    //!   component, an atom payload, or a morphism bound or value), so a type unfolds to its
    //!   parts in finitely many steps;
    //! - *regular*: every recursive occurrence passes the group's parameters unchanged, so a type
    //!   has finitely many components;
    //! - *of the form the admission check accepts*: no recursive occurrence stands under a
    //!   complement, to the right of `\`, or in the guarantee of a morphism type whose value type
    //!   may be empty or mentions the group, since `type T = (T) -> (#a & #b)` is inhabited exactly
    //!   when it is empty; nor in the guarantee of a morphism type whose guarantee and permission
    //!   differ, or that stands under `&`, `\`, a complement or differing domain bounds, directly
    //!   or through a definition named there (cross-review X14: `W = (W) -> int` is accepted,
    //!   `((W) -> int) & top` and `R0 = (R1) -> int; R1 = (int, R0 & ((empty) -> int))` are not).
    //!
    //! The admission check is sufficient for the group's emptiness to be monotone in its members'
    //! emptiness, not necessary: `((W) -> int) & top` is monotone and refused (X14). So a refusal
    //! says the type is outside the form the checker accepts, with the reason, the expression where
    //! it holds and, for a definition narrowed where it is named, the definitions it is named
    //! through; it says "not monotone" only of a complement or the right of `\`, each of which is
    //! not monotone in its operand.
    //!
    //! A value type that mentions a parameter may be empty when that parameter is: it counts as
    //! possibly empty when it is empty with every parameter empty, or has a parameter under a
    //! complement or to the right of `\`, where a larger argument shrinks it.

    use std::collections::HashMap;
    use std::sync::atomic::AtomicU64;
    use std::sync::{Arc, Mutex, OnceLock};

    use super::bes::{Answer, Bes, Decision};
    use super::{Type, bytes, mix};
    use crate::deep;

    mod group;
    pub(super) mod unfold;

    mod walk {
        //! `Clone`, `==` and `Debug` of [`Expr`], and `Debug` of a body's tree ([`Node`]) and `==` of
        //! its shapes, each keeping its own stack on the heap, so an expression of any depth is copied, compared and
        //! written on a small stack (COMPLEXITY.md K39). Each costs O(size). `Debug` writes the one line
        //! a derived `Debug` writes for `{:?}`, under `{:#?}` too.

        use std::fmt;
        use std::sync::Arc;

        use super::{Expr, Node, Shape};

        /// An expression or tree: its parts below, and what it holds besides them.
        pub(super) trait Tree: Sized {
            /// The parts directly below, in order.
            fn kids(&self) -> impl DoubleEndedIterator<Item = &Self>;

            /// Whether the two hold the same besides their parts below, and as many of those.
            fn same_head(&self, other: &Self) -> bool;

            /// Writes the text before the parts below, and gives the text after them.
            fn open(&self, f: &mut fmt::Formatter<'_>) -> Result<&'static str, fmt::Error>;
        }

        impl Expr {
            /// The parts of `self` directly below it, in order.
            pub(super) fn kids(&self) -> impl DoubleEndedIterator<Item = &Expr> {
                let (list, boxes): (&[Expr], [Option<&Expr>; 3]) = match self {
                    Expr::Param(_) | Expr::Type(_) => (&[], [None; 3]),
                    Expr::Ref(_, xs)
                    | Expr::Union(xs)
                    | Expr::And(xs)
                    | Expr::Tuple(xs)
                    | Expr::Atom(_, xs) => (xs, [None; 3]),
                    Expr::Not(a) => (&[], [Some(a), None, None]),
                    Expr::Diff(a, b) => (&[], [Some(a), Some(b), None]),
                    Expr::Morphism(l, u, v) => (&[], [Some(l), Some(u), Some(v)]),
                };
                list.iter().chain(boxes.into_iter().flatten())
            }
        }

        impl Shape {
            /// The trees directly below `self`, in order.
            pub(super) fn kids(&self) -> impl DoubleEndedIterator<Item = &Arc<Node>> {
                let (list, boxes): (&[Arc<Node>], [Option<&Arc<Node>>; 3]) = match self {
                    Shape::Param(_) | Shape::Type(_) => (&[], [None; 3]),
                    Shape::Ref(_, xs)
                    | Shape::Union(xs)
                    | Shape::And(xs)
                    | Shape::Tuple(xs)
                    | Shape::Atom(_, xs) => (xs, [None; 3]),
                    Shape::Not(a) => (&[], [Some(a), None, None]),
                    Shape::Diff(a, b) => (&[], [Some(a), Some(b), None]),
                    Shape::Morphism(l, u, v) => (&[], [Some(l), Some(u), Some(v)]),
                };
                list.iter().chain(boxes.into_iter().flatten())
            }

            pub(super) fn same_head(&self, other: &Shape) -> bool {
                match (self, other) {
                    (Shape::Param(i), Shape::Param(j)) => i == j,
                    (Shape::Ref(i, xs), Shape::Ref(j, ys)) => i == j && xs.len() == ys.len(),
                    (Shape::Type(s), Shape::Type(t)) => s == t,
                    (Shape::Union(xs), Shape::Union(ys))
                    | (Shape::And(xs), Shape::And(ys))
                    | (Shape::Tuple(xs), Shape::Tuple(ys)) => xs.len() == ys.len(),
                    (Shape::Atom(m, xs), Shape::Atom(n, ys)) => m == n && xs.len() == ys.len(),
                    (Shape::Not(_), Shape::Not(_))
                    | (Shape::Diff(..), Shape::Diff(..))
                    | (Shape::Morphism(..), Shape::Morphism(..)) => true,
                    _ => false,
                }
            }

            fn open(&self, f: &mut fmt::Formatter<'_>) -> Result<&'static str, fmt::Error> {
                Ok(match self {
                    Shape::Param(i) => {
                        write!(f, "Param({i:?}")?;
                        ")"
                    }
                    Shape::Type(t) => {
                        write!(f, "Type({t:?}")?;
                        ")"
                    }
                    Shape::Ref(i, _) => {
                        write!(f, "Ref({i:?}, [")?;
                        "])"
                    }
                    Shape::Union(_) => {
                        f.write_str("Union([")?;
                        "])"
                    }
                    Shape::And(_) => {
                        f.write_str("And([")?;
                        "])"
                    }
                    Shape::Tuple(_) => {
                        f.write_str("Tuple([")?;
                        "])"
                    }
                    Shape::Atom(name, _) => {
                        write!(f, "Atom({name:?}, [")?;
                        "])"
                    }
                    Shape::Not(_) => {
                        f.write_str("Not(")?;
                        ")"
                    }
                    Shape::Diff(..) => {
                        f.write_str("Diff(")?;
                        ")"
                    }
                    Shape::Morphism(..) => {
                        f.write_str("Morphism(")?;
                        ")"
                    }
                })
            }
        }

        impl Tree for Expr {
            fn kids(&self) -> impl DoubleEndedIterator<Item = &Expr> {
                Expr::kids(self)
            }

            fn same_head(&self, other: &Expr) -> bool {
                match (self, other) {
                    (Expr::Param(i), Expr::Param(j)) => i == j,
                    (Expr::Ref(i, xs), Expr::Ref(j, ys)) => i == j && xs.len() == ys.len(),
                    (Expr::Type(s), Expr::Type(t)) => s == t,
                    (Expr::Union(xs), Expr::Union(ys))
                    | (Expr::And(xs), Expr::And(ys))
                    | (Expr::Tuple(xs), Expr::Tuple(ys)) => xs.len() == ys.len(),
                    (Expr::Atom(m, xs), Expr::Atom(n, ys)) => m == n && xs.len() == ys.len(),
                    (Expr::Not(_), Expr::Not(_))
                    | (Expr::Diff(..), Expr::Diff(..))
                    | (Expr::Morphism(..), Expr::Morphism(..)) => true,
                    _ => false,
                }
            }

            fn open(&self, f: &mut fmt::Formatter<'_>) -> Result<&'static str, fmt::Error> {
                Ok(match self {
                    Expr::Param(i) => {
                        write!(f, "Param({i:?}")?;
                        ")"
                    }
                    Expr::Type(t) => {
                        write!(f, "Type({t:?}")?;
                        ")"
                    }
                    Expr::Ref(i, _) => {
                        write!(f, "Ref({i:?}, [")?;
                        "])"
                    }
                    Expr::Union(_) => {
                        f.write_str("Union([")?;
                        "])"
                    }
                    Expr::And(_) => {
                        f.write_str("And([")?;
                        "])"
                    }
                    Expr::Tuple(_) => {
                        f.write_str("Tuple([")?;
                        "])"
                    }
                    Expr::Atom(name, _) => {
                        write!(f, "Atom({name:?}, [")?;
                        "])"
                    }
                    Expr::Not(_) => {
                        f.write_str("Not(")?;
                        ")"
                    }
                    Expr::Diff(..) => {
                        f.write_str("Diff(")?;
                        ")"
                    }
                    Expr::Morphism(..) => {
                        f.write_str("Morphism(")?;
                        ")"
                    }
                })
            }
        }

        impl Tree for Node {
            fn kids(&self) -> impl DoubleEndedIterator<Item = &Node> {
                self.e.kids().map(|n| &**n)
            }

            fn same_head(&self, other: &Node) -> bool {
                self.digest == other.digest
                    && self.recursive == other.recursive
                    && self.open == other.open
                    && self.e.same_head(&other.e)
            }

            fn open(&self, f: &mut fmt::Formatter<'_>) -> Result<&'static str, fmt::Error> {
                write!(
                    f,
                    "Node {{ digest: {:?}, recursive: {:?}, open: {:?}, e: ",
                    self.digest, self.recursive, self.open
                )?;
                Ok(match self.e.open(f)? {
                    ")" => ") }",
                    _ => "]) }",
                })
            }
        }

        /// Whether `a` and `b` are equal, part by part, from a stack of pairs. A pair that is one
        /// value twice is equal unread. A body's tree is a tree, built by `Node::of` from an expression,
        /// so no pair is met twice.
        pub(super) fn equal<T: Tree>(a: &T, b: &T) -> bool {
            let mut pairs = vec![(a, b)];
            while let Some((a, b)) = pairs.pop() {
                if std::ptr::eq(a, b) {
                    continue;
                }
                if !a.same_head(b) {
                    return false;
                }
                pairs.extend(a.kids().zip(b.kids()));
            }
            true
        }

        /// What is left to write.
        enum Task<'a, T> {
            Text(&'static str),
            Tree(&'a T),
        }

        /// Writes `t`, each part when its turn comes, from a stack of what is left.
        fn show<T: Tree>(t: &T, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut todo = vec![Task::Tree(t)];
            while let Some(task) = todo.pop() {
                match task {
                    Task::Text(s) => f.write_str(s)?,
                    Task::Tree(t) => {
                        todo.push(Task::Text(t.open(f)?));
                        let mut first = true;
                        for k in t.kids().rev() {
                            if !first {
                                todo.push(Task::Text(", "));
                            }
                            first = false;
                            todo.push(Task::Tree(k));
                        }
                    }
                }
            }
            Ok(())
        }

        impl PartialEq for Expr {
            fn eq(&self, other: &Expr) -> bool {
                equal(self, other)
            }
        }

        impl Eq for Expr {}

        impl PartialEq for Shape {
            fn eq(&self, other: &Shape) -> bool {
                self.same_head(other)
                    && self
                        .kids()
                        .zip(other.kids())
                        .all(|(a, b)| equal(&**a, &**b))
            }
        }

        impl fmt::Debug for Expr {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                show(self, f)
            }
        }

        impl fmt::Debug for Node {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                show(self, f)
            }
        }

        /// The last of the copied parts, boxed.
        fn last(parts: &mut Vec<Expr>) -> Box<Expr> {
            Box::new(parts.pop().expect("each part was copied"))
        }

        impl Clone for Expr {
            /// Copies the parts in a loop: each expression with parts is rebuilt once they are copied.
            fn clone(&self) -> Expr {
                enum Step<'a> {
                    Copy(&'a Expr),
                    Rebuild(&'a Expr),
                }
                let mut todo = vec![Step::Copy(self)];
                let mut done: Vec<Expr> = Vec::new();
                while let Some(step) = todo.pop() {
                    match step {
                        Step::Copy(e) => match e {
                            Expr::Param(i) => done.push(Expr::Param(*i)),
                            Expr::Type(t) => done.push(Expr::Type(t.clone())),
                            _ => {
                                todo.push(Step::Rebuild(e));
                                todo.extend(e.kids().rev().map(Step::Copy));
                            }
                        },
                        Step::Rebuild(e) => {
                            let n = e.kids().count();
                            let mut parts = done.split_off(done.len() - n);
                            let built = match e {
                                Expr::Ref(i, _) => Expr::Ref(*i, parts),
                                Expr::Union(_) => Expr::Union(parts),
                                Expr::And(_) => Expr::And(parts),
                                Expr::Tuple(_) => Expr::Tuple(parts),
                                Expr::Atom(name, _) => Expr::Atom(name.clone(), parts),
                                Expr::Not(_) => Expr::Not(last(&mut parts)),
                                Expr::Diff(..) => {
                                    let b = last(&mut parts);
                                    Expr::Diff(last(&mut parts), b)
                                }
                                Expr::Morphism(..) => {
                                    let v = last(&mut parts);
                                    let u = last(&mut parts);
                                    Expr::Morphism(last(&mut parts), u, v)
                                }
                                Expr::Param(_) | Expr::Type(_) => {
                                    unreachable!("an expression with no parts is copied whole")
                                }
                            };
                            done.push(built);
                        }
                    }
                }
                done.pop().expect("the copy of the expression")
            }
        }
    }

    /// A type expression in a definition's body. Its `Clone`, `==` and `Debug` are written in
    /// module `walk`, each in a loop.
    pub enum Expr {
        /// The definition's parameter of this index.
        Param(usize),
        /// The group's definition of this index, at these arguments.
        Ref(usize, Vec<Expr>),
        /// A type that does not mention the group.
        Type(Type),
        /// `a | b | …`.
        Union(Vec<Expr>),
        /// `a & b & …`.
        And(Vec<Expr>),
        /// `!a`.
        Not(Box<Expr>),
        /// `a \ b`.
        Diff(Box<Expr>, Box<Expr>),
        /// `(a, b, …)`.
        Tuple(Vec<Expr>),
        /// `#name(a, b, …)`, whose payload is the tuple of its items.
        Atom(String, Vec<Expr>),
        /// The morphism type with this guarantee, permission and value type.
        Morphism(Box<Expr>, Box<Expr>, Box<Expr>),
    }

    impl Expr {
        /// `K -> V`, exact.
        pub fn exact(key: Expr, value: Expr) -> Expr {
            Expr::Morphism(Box::new(key.clone()), Box::new(key), Box::new(value))
        }

        /// Applies `f` to `self` and every expression in it, each before its parts, from a stack.
        fn walk(&self, f: &mut impl FnMut(&Expr)) {
            let mut todo = vec![self];
            while let Some(e) = todo.pop() {
                f(e);
                todo.extend(e.kids().rev());
            }
        }
    }

    /// A definition `type name(params) = body`.
    #[derive(Clone, PartialEq, Eq, Debug)]
    pub struct Def {
        /// Its name.
        pub name: String,
        /// Its parameters' names.
        pub params: Vec<String>,
        /// Its body.
        pub body: Expr,
    }

    /// A checked group of mutually recursive definitions.
    #[derive(Clone, Debug)]
    pub struct Group(pub(in crate::types) Arc<Checked>);

    #[derive(Debug)]
    pub(in crate::types) struct Checked {
        /// The group's number in `INSTANCES`: one per distinct definition list (`GROUPS`). It
        /// counts the groups the process made before, so it only finds a table entry: no digest
        /// and no order reads it (deterministic checking, repair REC-id-order).
        number: u64,
        /// The hash of the definitions (`group::digest`), by which `GROUPS` finds the group; its
        /// types' digests are made from the canonical form's ([`Canon`]).
        digest: u64,
        defs: Vec<Def>,
        /// Each body as a shared tree.
        pub(in crate::types) bodies: Vec<Arc<Node>>,
        /// Whether each definition is plain: on no cycle of the group and naming only plain
        /// definitions. A plain member is its unfolding, built as an ordinary type, so equal plain
        /// members of groups built apart are one type.
        plain: Vec<bool>,
        /// Whether each definition is on a cycle of the group: names itself through the group.
        cyclic: Vec<bool>,
        /// The plain definitions, each after those it names.
        order: Vec<usize>,
        /// The canonical form, made when the group is first instantiated ([`canon`]).
        canon: OnceLock<Canon>,
    }

    /// A group's canonical form (item REC-canon): the coarsest partition of its bodies' nodes in
    /// which two nodes of one class have the same head and, place by place, children of one
    /// class, a recursive occurrence standing for the body it names. The classes are numbered by
    /// the structure alone ([`crate::refine`]), so a copy of the group with its definitions
    /// renamed and listed in another order has the same form, and its members and parts the same
    /// classes. Two nodes of one class unfold alike to every depth, and so denote one type.
    #[derive(Debug)]
    struct Canon {
        /// A hash of the classes, in order.
        digest: u64,
        /// Each class, in order: a node of it, and its children's classes in place order.
        classes: Vec<(Arc<Node>, Vec<u32>)>,
        /// The class of each definition's body.
        member: Vec<u32>,
        /// The class of each node, by its number (`Node::at`), an occurrence taking its body's;
        /// `u32::MAX` for an argument of a recursive occurrence, which is not read.
        at: Vec<u32>,
        /// A hash of each node's spelling, by its number: its shape with each occurrence by the
        /// name it is written with, which is what a part kept unevaluated prints as (`Show`).
        spell: Vec<u64>,
        /// Each node, by its number; `None` for an argument of a recursive occurrence.
        node: Vec<Option<Arc<Node>>>,
    }

    /// An expression as a shared tree, each node knowing whether it mentions the group, so that a
    /// part kept unevaluated is shared rather than copied, and no node's flag is computed twice.
    pub(in crate::types) struct Node {
        /// A hash of the shape, from the children's: equal shapes hash alike.
        digest: u64,
        pub(in crate::types) recursive: bool,
        /// Whether the node names a definition that is not plain.
        open: bool,
        /// The node's place in its group: its number in the order the bodies' nodes are left,
        /// children first, the bodies in order. A part kept unevaluated is known by it ([`Key`]).
        at: u32,
        /// The number (`at`) of the first node of its group built with an equal shape: two nodes of
        /// one group are equal exactly when these are, so two domain bounds are compared in O(1)
        /// ([`same`]).
        pub(in crate::types) class: u32,
        pub(in crate::types) e: Shape,
    }

    pub(in crate::types) enum Shape {
        Param(usize),
        Ref(usize, Vec<Arc<Node>>),
        Type(Type),
        Union(Vec<Arc<Node>>),
        And(Vec<Arc<Node>>),
        Not(Arc<Node>),
        Diff(Arc<Node>, Arc<Node>),
        Tuple(Vec<Arc<Node>>),
        Atom(String, Vec<Arc<Node>>),
        Morphism(Arc<Node>, Arc<Node>, Arc<Node>),
    }

    impl Shape {
        /// A hash of the top of the shape, without its children.
        fn tag(&self) -> u64 {
            match self {
                Shape::Param(i) => mix(1, *i as u64),
                Shape::Ref(i, _) => mix(2, *i as u64),
                Shape::Type(t) => mix(3, t.digest()),
                Shape::Union(_) => 4,
                Shape::And(_) => 5,
                Shape::Not(_) => 6,
                Shape::Diff(..) => 7,
                Shape::Tuple(_) => 8,
                Shape::Atom(name, _) => mix(9, bytes(name.as_bytes())),
                Shape::Morphism(..) => 10,
            }
        }

        /// The top of the shape, without its children or type, for [`Canon::order`] and [`canon`]:
        /// the kind, the index of a parameter or definition, and an atom's name.
        fn head(&self) -> (u8, usize, &str) {
            match self {
                Shape::Param(i) => (1, *i, ""),
                Shape::Ref(i, _) => (2, *i, ""),
                Shape::Type(_) => (3, 0, ""),
                Shape::Union(_) => (4, 0, ""),
                Shape::And(_) => (5, 0, ""),
                Shape::Not(_) => (6, 0, ""),
                Shape::Diff(..) => (7, 0, ""),
                Shape::Tuple(_) => (8, 0, ""),
                Shape::Atom(name, _) => (9, 0, name),
                Shape::Morphism(..) => (10, 0, ""),
            }
        }
    }

    /// A part of an expression, tree or instance whose owner is being dropped (module `deep`): an
    /// expression nested deep, or an instance nested deep in its own arguments, is freed in a
    /// loop, on any stack.
    #[expect(dead_code, reason = "a part is held only to be dropped")]
    enum Freed {
        Expr(Expr),
        Exprs(Vec<Expr>),
        Shape(Shape),
        Nodes(Vec<Arc<Node>>),
        /// An instance's arguments, and its members (`Env`'s `Drop`, in module `group`).
        Types(Vec<Type>),
        Members(Vec<Mutex<Option<Type>>>),
    }

    thread_local! {
        /// The parts of expressions, trees and instances waiting to be dropped.
        static FREED: deep::Queue<Freed> = const { deep::Queue::new() };
    }

    fn free(part: Freed) {
        deep::free_in(&FREED, part);
    }

    /// Keeps the queues that free types and instances until after the thread-locals first used
    /// after this call, such as a thread's unit (`unfold::Unit`), which holds instances.
    fn hold() {
        super::hold();
        deep::hold(&FREED);
    }

    /// An expression's parts are freed in a loop, not by recursion.
    impl Drop for Expr {
        fn drop(&mut self) {
            match self {
                Expr::Param(_) | Expr::Type(_) => {}
                Expr::Ref(_, xs)
                | Expr::Union(xs)
                | Expr::And(xs)
                | Expr::Tuple(xs)
                | Expr::Atom(_, xs) => {
                    if !xs.is_empty() {
                        free(Freed::Exprs(std::mem::take(xs)));
                    }
                }
                Expr::Not(a) => free(Freed::Expr(std::mem::replace(&mut **a, Expr::Param(0)))),
                Expr::Diff(a, b) => {
                    for x in [a, b] {
                        free(Freed::Expr(std::mem::replace(&mut **x, Expr::Param(0))));
                    }
                }
                Expr::Morphism(l, u, v) => {
                    for x in [l, u, v] {
                        free(Freed::Expr(std::mem::replace(&mut **x, Expr::Param(0))));
                    }
                }
            }
        }
    }

    /// Queues the shape `n` holds, when `n` is its last owner.
    fn free_node(n: &mut Arc<Node>) {
        if let Some(n) = Arc::get_mut(n) {
            free(Freed::Shape(std::mem::replace(&mut n.e, Shape::Param(0))));
        }
    }

    /// A tree's children are freed in a loop, as an expression's are.
    impl Drop for Shape {
        fn drop(&mut self) {
            match self {
                Shape::Param(_) | Shape::Type(_) => {}
                Shape::Ref(_, xs)
                | Shape::Union(xs)
                | Shape::And(xs)
                | Shape::Tuple(xs)
                | Shape::Atom(_, xs) => {
                    if !xs.is_empty() {
                        free(Freed::Nodes(std::mem::take(xs)));
                    }
                }
                Shape::Not(a) => free_node(a),
                Shape::Diff(a, b) => {
                    free_node(a);
                    free_node(b);
                }
                Shape::Morphism(l, u, v) => {
                    free_node(l);
                    free_node(u);
                    free_node(v);
                }
            }
        }
    }

    /// Why a group is rejected: the definition at fault and the reason.
    #[derive(Clone, PartialEq, Eq, Debug)]
    pub struct Rejection {
        /// The index of the definition.
        pub def: usize,
        /// The reason, naming the definition.
        pub message: String,
    }

    /// Whether the domain bounds `l` and `u`, of one group, are written the same: their classes,
    /// given when the group's trees were built ([`Node::of`]), are equal. O(1) (COMPLEXITY.md K27).
    // Complexity tradeoff (COMPLEXITY.md K27): the naive test compares the two bounds by
    // structure, O(n log n) in all on equal bounds nested `log n` deep, since a node lies in at
    // most log2 n bounds compared equal. Used: each node is given a class when its tree is built
    // (`Numbering::first`, keyed by digest; a node joins the first node of equal head and child
    // classes), expected O(1) a node, and the test compares classes, O(1). Tradeoffs: the table
    // lives while the group's trees are built, O(nodes) memory; nodes of equal digest and
    // differing shape take further probes, never a wrong class.
    fn same(l: &Node, u: &Node) -> bool {
        l.class == u.class
    }

    /// What an expression is evaluated in: the arguments, and the group's types at them.
    pub(in crate::types) struct Env {
        /// The instance's number among all instances made: never another's, so a group's members
        /// are told from another instance's after this one is dropped ([`Key::group`]).
        id: u64,
        /// The thread that made it, under which it is in `group::INSTANCES`.
        thread: u64,
        /// The last unit that made its recursive members, which ends them (`unfold::Unit`).
        registered: AtomicU64,
        group: Option<Group>,
        /// A hash of the group's definitions and the arguments' digests.
        digest: u64,
        args: Vec<Type>,
        /// Each member's type: a plain member's set when the group is instantiated, a recursive
        /// member's when first read and until the end of the unit that read it ([`Env::forget`]).
        members: Vec<Mutex<Option<Type>>>,
        /// What the group's decider found for each member (`empty::judge`), when first asked.
        pub(in crate::types) judged: OnceLock<Judgment>,
    }

    impl Env {
        pub(in crate::types) fn group(&self) -> &Group {
            self.group
                .as_ref()
                .expect("a recursive occurrence is in a group")
        }
    }

    // The decider's findings are defined here, with the instance that keeps them, and made by
    // module `empty` (`judge`) and read by its module `refused`, which build on this module:
    // defined there, the instance would name them and the two files would import each other.

    /// What a group's decider found for its members (`empty::judge`), kept with the instance.
    pub(in crate::types) struct Judgment {
        /// Each member's emptiness, where the decider decides it.
        pub(in crate::types) answers: Vec<Option<bool>>,
        /// Whether each member the decider does not decide is refused by it: searched as every
        /// member left open is, and given `Refusal::Group` by `verdict` if the search does not
        /// decide it.
        pub(in crate::types) refused: Vec<bool>,
        /// What the message of a refused member reads; only when one is refused.
        pub(in crate::types) why: Option<Why>,
    }

    /// What a refused member's message reads, kept with its group's judgment ([`Judgment`]);
    /// made and read in `empty::refused`.
    pub(in crate::types) struct Why {
        /// The decider's system, as it was built, its leaves last set `Top`.
        pub(in crate::types) graph: Bes,
        /// The definition and the expression each node stands for, by its number.
        pub(in crate::types) origin: Vec<(usize, Arc<Node>)>,
        /// The decisions: with the leaves `Bot`, and, when there are leaves, with them `Top`.
        pub(in crate::types) runs: Vec<Decision>,
        /// For each run, the refusal whose component holds each node it refused for its shape.
        pub(in crate::types) of: Vec<HashMap<u32, usize>>,
        /// The number of members, whose nodes come first.
        pub(in crate::types) members: u32,
        /// Whether each node reaches a meet or a difference, so that an inhabited answer does
        /// not decide it (`empty::settled`).
        pub(in crate::types) wide: Vec<bool>,
        /// Whether each node reaches a node that some run refused. A node that does not is
        /// decided in every run, and a repair, which changes only refused members, cannot
        /// change it.
        pub(in crate::types) open: Vec<bool>,
        /// For each set of members given `| #end`, the answers of the two runs of the decider
        /// then for each member already re-checked with it, or reached by such a re-check.
        pub(in crate::types) checked: Mutex<HashMap<Vec<usize>, Rechecked>>,
    }

    /// The answers of the two runs of the decider in a re-check (`Why::recheck`), by member.
    pub(in crate::types) type Rechecked = HashMap<u32, [Answer; 2]>;

    /// What the decider makes of a refused member once a repair is written (`Why::recheck`).
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub(in crate::types) enum Recheck {
        /// It decides the member.
        Decided,
        /// It refuses the member no longer, and leaves it to the search, as it leaves a member
        /// read through a meet or a difference, or one whose answer rests on a part it does not
        /// take.
        Searched,
        /// It still refuses the member.
        Refused,
    }

    /// What a recursive node stands for, by which it is hashed and ordered: a member of a group, or
    /// a part of a body kept unevaluated (by its node's place, `Node::at`), at the group's
    /// arguments. It is hashed and ordered by the group's canonical form ([`Canon`]), the class
    /// of the member or part in it, what it prints as (a member's name, a part's spelling) and
    /// the arguments, so a type's digest and its place in every order do not depend on what the
    /// process built before it, and checking a program alone or after another agrees
    /// (deterministic checking, repair REC-id-order); nor on the order the definitions are
    /// listed in (item REC-canon). Two nodes with equal keys denote one type, since their classes
    /// unfold alike at equal arguments, and print alike, so which of them a union keeps is never
    /// seen. The names count for that alone: a copy with its definitions renamed is the same type
    /// by two-way subtyping, but another node.
    pub(super) struct Key {
        digest: u64,
        env: Arc<Env>,
        at: At,
        /// The class of the member or part in its group's canonical form.
        class: u32,
    }

    /// Which type of an instance a key names.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    enum At {
        /// The member of this index.
        Member(usize),
        /// The part kept unevaluated at the body node of this number.
        Part(u32),
    }

    impl Key {
        fn new(env: Arc<Env>, at: At) -> Key {
            let (group, canon) = (env.group(), env.group().canon());
            let (class, spell) = match at {
                At::Member(i) => (
                    canon.member[i],
                    mix(15, bytes(group.0.defs[i].name.as_bytes())),
                ),
                At::Part(n) => (canon.at[n as usize], canon.spell[n as usize]),
            };
            let digest = mix(
                mix(mix(env.digest, u64::from(class)), u64::from(at.kind())),
                spell,
            );
            Key {
                digest,
                env,
                at,
                class,
            }
        }

        /// The order of two keys of equal class by what they print as: a member by its
        /// definition's name, a part by its spelling ([`spelled`]).
        fn spelling(&self, other: &Key) -> std::cmp::Ordering {
            let (a, b) = (&self.env.group().0, &other.env.group().0);
            match (self.at, other.at) {
                (At::Member(i), At::Member(j)) => a.defs[i].name.cmp(&b.defs[j].name),
                (At::Part(n), At::Part(m)) if !(Arc::ptr_eq(a, b) && n == m) => {
                    spelled(a.part(n), &a.defs, b.part(m), &b.defs)
                }
                _ => std::cmp::Ordering::Equal,
            }
        }

        /// Whether the key names a member or a part, and its class: what orders two keys of one
        /// group after their digests.
        fn rank(&self) -> (u8, u32) {
            (self.at.kind(), self.class)
        }

        pub(super) fn digest(&self) -> u64 {
            self.digest
        }

        /// The group of the member the key names, by the number of the instance its members share,
        /// when the key names a member: equal for two members of one instance of a group, and never
        /// reused, so a member of an instance made after another is dropped is not taken for one of
        /// the other's.
        pub(super) fn group(&self) -> Option<u64> {
            matches!(self.at, At::Member(_)).then_some(self.env.id)
        }

        /// Whether the key names a member on a cycle of its group, or a part, which is taken as on
        /// one.
        pub(super) fn on_cycle(&self) -> bool {
            match self.at {
                At::Member(i) => self.env.group().0.cyclic[i],
                At::Part(_) => true,
            }
        }

        /// Whether the decider of the group (`judge`) has run, which a member's `judged` reads.
        pub(super) fn judged_known(&self) -> bool {
            self.env.judged.get().is_some()
        }

        /// The name of the member the key names and its instance's arguments, when it names a
        /// member: a message writes it so, `name(args)` (`Type::surface_by_name`).
        pub(in crate::types) fn member_name(&self) -> Option<(&str, &[Type])> {
            match self.at {
                At::Member(i) => Some((&self.env.group().0.defs[i].name, &self.env.args)),
                At::Part(_) => None,
            }
        }

        /// The instance and the index of the member the key names, when it names a member: the
        /// node is then a recursive member of a group, which its group's decider is asked about.
        pub(in crate::types) fn member_at(&self) -> Option<(&Arc<Env>, usize)> {
            match self.at {
                At::Member(i) => Some((&self.env, i)),
                At::Part(_) => None,
            }
        }

        /// The order of two keys: by digest, kind and class, the groups' canonical forms, the
        /// spelling and the arguments. What the forms' shapes decide is decided here; the pairs of
        /// types inside them that tie in digest, then the arguments, are pushed to `types` in the
        /// order they are to be compared when the rest ties, by the caller's loop (`order`), so
        /// that no type is compared by recursion here. Time linear in the classes where the groups
        /// differ and tie in digest, linear in the part where two parts are spelled alike, and
        /// constant otherwise.
        pub(super) fn order<'a>(
            &'a self,
            other: &'a Key,
            types: &mut Vec<(&'a Type, &'a Type)>,
        ) -> std::cmp::Ordering {
            let c = self
                .digest
                .cmp(&other.digest)
                .then(self.rank().cmp(&other.rank()));
            if c.is_ne() {
                return c;
            }
            if Arc::ptr_eq(&self.env, &other.env) {
                return self.spelling(other);
            }
            let (a, b) = (self.env.group(), other.env.group());
            if !Arc::ptr_eq(&a.0, &b.0) {
                let c = a.canon().order(b.canon(), types);
                if c.is_ne() {
                    return c;
                }
            }
            let c = self.spelling(other);
            if c.is_ne() {
                return c;
            }
            types.extend(self.env.args.iter().zip(&other.env.args));
            std::cmp::Ordering::Equal
        }
    }

    impl At {
        fn kind(self) -> u8 {
            match self {
                At::Member(_) => 0,
                At::Part(_) => 1,
            }
        }
    }

    impl Group {
        /// The canonical form, made on first use.
        fn canon(&self) -> &Canon {
            self.0
                .canon
                .get_or_init(|| canon(&self.0.bodies, &self.0.defs))
        }
    }

    impl Checked {
        /// The node of number `n`, which a key names, so the form is made.
        fn part(&self, n: u32) -> &Node {
            let canon = self.canon.get().expect("a key's group has its form");
            canon.node[n as usize].as_deref().expect("a part is read")
        }
    }

    impl Canon {
        /// The order of two groups' canonical forms, after their digests: the classes in order, each
        /// by its head, its children's classes and the type it holds by digest; the pairs of types
        /// that tie in digest are pushed to `types` ([`Key::order`]). Time linear in the classes.
        fn order<'a>(
            &'a self,
            other: &'a Canon,
            types: &mut Vec<(&'a Type, &'a Type)>,
        ) -> std::cmp::Ordering {
            let c = self
                .digest
                .cmp(&other.digest)
                .then(self.classes.len().cmp(&other.classes.len()));
            if c.is_ne() {
                return c;
            }
            for ((x, xs), (y, ys)) in self.classes.iter().zip(&other.classes) {
                let c = x.e.head().cmp(&y.e.head()).then_with(|| xs.cmp(ys));
                if c.is_ne() {
                    return c;
                }
                if let (Shape::Type(s), Shape::Type(t)) = (&x.e, &y.e) {
                    match s.digest().cmp(&t.digest()) {
                        std::cmp::Ordering::Equal => types.push((s, t)),
                        c => return c,
                    }
                }
            }
            std::cmp::Ordering::Equal
        }
    }

    /// The canonical form of a group whose bodies are `bodies` ([`Canon`]). The graph has a vertex
    /// for each node of the bodies but a recursive occurrence, and one for each place a node has a
    /// child at, colored by the place, with an arc from the child to the place and from the place
    /// to the node; an occurrence of a definition stands for the node of its body, through a chain
    /// of occurrences, which contractiveness ends. A node starts colored by its head, a type held
    /// by its order. Refinement by the arcs' tails ([`crate::refine`]) then splits two nodes
    /// exactly when some place holds children of two colors: its coarsest stable coloring is the
    /// partition in which nodes of one class unfold alike. O((N + M) log N) for N nodes and M
    /// children, besides the O(N log N) comparisons of the starting sort, of which those of two
    /// types cost what [`Type::cmp`] costs.
    fn canon(bodies: &[Arc<Node>], defs: &[Def]) -> Canon {
        // Complexity tradeoff (COMPLEXITY.md K72): the naive canonical form numbers each member
        // by a walk of its own reachable part, O(N) per member and O(N²) on one strongly
        // connected component; numbering by written order is O(N) but makes a reordered group a
        // second type. Used: color refinement with Hopcroft's smaller-half rule
        // (`crate::refine`), O((N + M) log N), plus the O(N log N) comparisons of the starting
        // sort. Given up: memory for the graph (a vertex per node and per place, an arc per
        // child) and a log factor over the written-order numbering; bisimilar members fall into
        // one class.
        // The nodes by number, but the arguments of an occurrence, which are not read.
        let mut nodes: Vec<&Arc<Node>> = Vec::new();
        let mut todo: Vec<&Arc<Node>> = bodies.iter().collect();
        while let Some(n) = todo.pop() {
            nodes.push(n);
            if !matches!(n.e, Shape::Ref(..)) {
                todo.extend(n.e.kids());
            }
        }
        let count = nodes.iter().map(|n| n.at as usize + 1).max().unwrap_or(0);
        // The node each body is, through its chain of occurrences.
        let mut root: Vec<Option<usize>> = vec![None; bodies.len()];
        for i in 0..bodies.len() {
            let mut chain = Vec::new();
            let mut d = i;
            let at = loop {
                if let Some(r) = root[d] {
                    break r;
                }
                chain.push(d);
                match &bodies[d].e {
                    Shape::Ref(j, _) => d = *j,
                    _ => break bodies[d].at as usize,
                }
            };
            for d in chain {
                root[d] = Some(at);
            }
        }
        let root: Vec<usize> = root
            .into_iter()
            .map(|r| r.expect("each body's node"))
            .collect();
        // Vertices: the nodes, then the places.
        let mut vertex = vec![u32::MAX; count];
        let mut of: Vec<&Arc<Node>> = Vec::new();
        for n in &nodes {
            if !matches!(n.e, Shape::Ref(..)) {
                vertex[n.at as usize] = of.len() as u32;
                of.push(n);
            }
        }
        let target = |c: &Node| -> usize {
            let at = match &c.e {
                Shape::Ref(j, _) => root[*j],
                _ => c.at as usize,
            };
            vertex[at] as usize
        };
        let v = of.len();
        // Each place: the node and the child's vertex.
        let mut places: Vec<(usize, usize, usize)> = Vec::new();
        for (u, n) in of.iter().enumerate() {
            for (k, c) in n.e.kids().enumerate() {
                places.push((u, k, target(c)));
            }
        }
        let size = v + places.len();
        let mut color = vec![0; size];
        let mut sorted: Vec<usize> = (0..v).collect();
        let head = |a: usize, b: usize| {
            let (x, y) = (&of[a].e, &of[b].e);
            x.head()
                .cmp(&y.head())
                .then_with(|| x.kids().count().cmp(&y.kids().count()))
                .then_with(|| match (x, y) {
                    (Shape::Type(s), Shape::Type(t)) => s.cmp(t),
                    _ => std::cmp::Ordering::Equal,
                })
        };
        sorted.sort_by(|&a, &b| head(a, b));
        let mut next = 0;
        for (i, &a) in sorted.iter().enumerate() {
            if i > 0 && head(sorted[i - 1], a).is_ne() {
                next += 1;
            }
            color[a] = next;
        }
        next += usize::from(v > 0);
        let widest = places.iter().map(|p| p.1 + 1).max().unwrap_or(0);
        for (e, &(_, k, _)) in places.iter().enumerate() {
            color[v + e] = next + k;
        }
        next += widest;
        // The vertices counted when the class of a vertex refines: a child's places, a place's node.
        let mut start = vec![0; size + 1];
        for (e, &(_, _, c)) in places.iter().enumerate() {
            start[c + 1] += 1;
            start[v + e + 1] = 1;
        }
        for x in 0..size {
            start[x + 1] += start[x];
        }
        let mut adj = vec![0; start[size]];
        let mut cursor = start[..size].to_vec();
        for (e, &(u, _, c)) in places.iter().enumerate() {
            adj[cursor[c]] = v + e;
            cursor[c] += 1;
            adj[cursor[v + e]] = u;
        }
        let degree = (0..size)
            .map(|x| start[x + 1] - start[x])
            .max()
            .unwrap_or(0);
        let mut refine = crate::refine::Refine::new(color, next, degree);
        refine.run(&start, &adj);
        let color = refine.color;
        // The nodes' colors, numbered from 0 in their order.
        let mut class = vec![u32::MAX; size];
        for &c in &color[..v] {
            class[c] = 0;
        }
        let mut classes = 0;
        for c in &mut class {
            if *c == 0 {
                *c = classes;
                classes += 1;
            }
        }
        let class_of = |u: usize| class[color[u]];
        let mut reps: Vec<Option<(Arc<Node>, Vec<u32>)>> = vec![None; classes as usize];
        for (u, n) in of.iter().enumerate() {
            let rep = &mut reps[class_of(u) as usize];
            if rep.is_none() {
                let kids = n.e.kids().map(|c| class_of(target(c))).collect();
                *rep = Some(((*n).clone(), kids));
            }
        }
        let classes: Vec<(Arc<Node>, Vec<u32>)> = reps
            .into_iter()
            .map(|r| r.expect("a node of each class"))
            .collect();
        let mut at = vec![u32::MAX; count];
        for n in &nodes {
            at[n.at as usize] = class_of(target(n));
        }
        let member = root.iter().map(|&r| class_of(vertex[r] as usize)).collect();
        let digest = classes.iter().fold(14, |h, (n, kids)| {
            kids.iter()
                .fold(mix(h, n.e.tag()), |h, &k| mix(h, u64::from(k)))
        });
        // The spellings, children first: a node's number is above its children's.
        let mut node: Vec<Option<Arc<Node>>> = vec![None; count];
        for n in &nodes {
            node[n.at as usize] = Some((*n).clone());
        }
        let mut spell = vec![0; count];
        for n in node.iter().flatten() {
            spell[n.at as usize] = match &n.e {
                Shape::Ref(j, _) => mix(2, bytes(defs[*j].name.as_bytes())),
                e => e.kids().fold(e.tag(), |h, c| mix(h, spell[c.at as usize])),
            };
        }
        Canon {
            digest,
            classes,
            member,
            at,
            spell,
            node,
        }
    }

    /// The order of two nodes of one class by their spelling ([`Canon::spell`]), `defs` naming the
    /// definitions each one's occurrences name: by head, an occurrence by the name it is written
    /// with, then the children in place order, in a loop. The types they hold are not read: two
    /// nodes of one class hold equal ones. Time linear in the nodes.
    fn spelled(x: &Node, xs: &[Def], y: &Node, ys: &[Def]) -> std::cmp::Ordering {
        fn head<'a>(n: &'a Node, defs: &'a [Def]) -> (u8, usize, &'a str) {
            match &n.e {
                Shape::Ref(i, _) => (2, 0, defs[*i].name.as_str()),
                e => e.head(),
            }
        }
        let mut stack: Vec<(&Node, &Node)> = vec![(x, y)];
        while let Some((x, y)) = stack.pop() {
            let c = (head(x, xs).cmp(&head(y, ys)))
                .then_with(|| x.e.kids().count().cmp(&y.e.kids().count()));
            if c.is_ne() {
                return c;
            }
            if !matches!(x.e, Shape::Ref(..)) {
                // The counts are equal, so the pairs from the ends are the pairs in reverse.
                stack.extend(
                    x.e.kids()
                        .rev()
                        .zip(y.e.kids().rev())
                        .map(|(p, q)| (&**p, &**q)),
                );
            }
        }
        std::cmp::Ordering::Equal
    }
}

#[cfg(test)]
mod tests;
