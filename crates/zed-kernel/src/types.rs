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

use atoms::Atoms;
mod bdd;
pub mod bes;
mod bucket;
mod debug;
mod empty;
mod hash;
#[cfg(test)]
use hash::SALT;
pub(crate) use hash::mix;
use hash::{blind, digests_cmp, names_blind};
mod print;
pub use print::{defs, names, order};

use imbl::ordmap::DiffItem;
use imbl::{OrdMap, OrdSet};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, Bound, HashMap, HashSet};
use std::fmt;
use std::ops::{BitAnd, BitOr, Not, Sub};
use std::rc::Rc;
use std::sync::{Arc, Mutex, OnceLock, PoisonError, Weak};

use zed_collections::intern::Interner;
// FNV-1a 64 over a name's or a literal's text (the module kept a copy until
// DRY-hash-crate-2026-11-26; zed-hash has its source and the draft's test vectors).
use zed_hash::fnv1a_64;

use crate::deep;
use crate::frames::{Deep, Stack};
use crate::num::Rat;
use crate::treap_set::{Elem, HashConsTable, TreapSet};
use crate::value::{Id, Items, Value};
use bdd::{Bdd, Form, Literal, Op, Owned, Part, Tables, Walk};
use bucket::Bucket;
use zed_collections::priority::Priorities;

/// A type: the set of values it denotes. The primary fingerprint orders structure first;
/// a second fingerprint distinguishes retained names before the loop of `order` compares
/// contents, using its own stack. Both fingerprints are cached at construction.
#[derive(Clone)]
pub struct Type(Arc<Node>);

// Complexity tradeoff (COMPLEXITY.md K12): the naive comparison reads both types' contents,
// O(s·depth) per comparison for a type of size `s` nested `depth` deep, and rebuilds `empty`
// and `top` per call. Used: a deterministic digest made from the children's digests when a node
// is made, compared first; the contents are read only on equal digests, by the loop of `order`,
// once per pair of nodes. O(1) for types of different digest. Tradeoffs: one 64-bit digest per
// node for each fingerprint; the order is that of the hashes, so the printer sorts each part's
// clauses as text itself; on a digest tie (a collision, or the short-addresses build) two
// types are read in full, linear in their size.
impl Ord for Type {
    fn cmp(&self, other: &Type) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return std::cmp::Ordering::Equal;
        }
        digests_cmp(
            (self.digest(), self.name_digest()),
            (other.digest(), other.name_digest()),
        )
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
        // Types equal under `==` have equal presentation hashes, as a hash map needs
        // (PROOF-sweep-zed-kernel):
        // 1. Outside `hash::blind`: `Type::cmp` answers `Equal` by pointer equality, or after
        //    `digests_cmp` answered `Equal`. With `NAMED` set it compares the presentation
        //    digests first; without, the name-free digests and then `named_cmp`, which compares
        //    the presentation digests unless names are left out. So `Equal` implies equal
        //    `name_digest`, which is what is hashed.
        // 2. Inside `hash::blind`, `named_cmp` answers `Equal`, so types equal but for
        //    definition names compare equal while their presentation hashes may differ; no hash
        //    of a type or row runs there. `blind` is called only by `Ids::get`, `Ids::insert`
        //    and `Ids::remove` (`types/empty.rs`), each around a linear search of one list by
        //    `Type::eq`; `Ids` itself is keyed by the name-free `Type::digest`, outside `blind`,
        //    and that digest agrees with `==` under `blind` (step 1, without `NAMED`).
        //    `Type::eq` (`order`, `types`, `walk`, `rec::Key::order`, `Canon::order`) reads
        //    stored digests, a `HashSet` of node ids, ordered maps and vectors, and builds
        //    nothing. The one drop in those searches, of the key `Ids::remove`'s `retain`
        //    removes, could reach `Env::drop`, which looks up `ThreadInstances`, a hash map
        //    keyed by types; it runs no drop there, since the key is a clone of the entry of
        //    `Search::types` that `pop_open_forks` holds while it removes it (`met` inserts the
        //    two together, and only after `Ids::get` missed, so a list holds one key equal to
        //    it), so the count of that allocation stays above zero.
        // The assertion checks step 2 on every hash of a test build. Tests:
        // `equal_types_built_apart_hash_alike`,
        // `colliding_presentation_hashes_keep_named_graphs_apart`.
        debug_assert!(
            !names_blind(),
            "a type or row is hashed while names are left out"
        );
        self.name_digest().hash(h);
    }
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
        // The text's hash from its tree, each distinct node once ([`Text::poly_hash`]), so a
        // string doubled 62 times, a few thousand nodes, takes that many steps and not 2^62
        // (item BUILD-doubling-60s).
        Value::Str(s) => mix(2, s.poly_hash()),
        Value::Big(r) => exact(4, r),
        Value::Rat(r) => exact(5, r),
        other => mix(3, fnv1a_64(other.to_string().as_bytes())),
    }
}

/// A value as a key of a [`TreapSet`]: the literals of a type (`Lits`) and the finite-set
/// domain of the reduced product. Its weight is `scalar` for a number or a string, so a
/// set of literals sums what `Lits` summed before it was a treap (CHECK-literal-union-cost),
/// and the digest of any other value, which costs its size once, when its node is first made.
/// Its class is one bit per kind ([`Value::INT_CLASS`] and the others below), so a set holds
/// only integers exactly when its classes are within `INT_CLASS | BIG_CLASS`, read in `O(1)`.
///
/// Priorities: a 64-bit integer's point is the integer with its sign bit flipped, so at most
/// 118 integers tie whatever the draw, as for `i64` (module [`crate::treap_set`]); any other
/// value's is its `Hash` stream ([`Priorities::hash`]), so two values tie whatever the draw only
/// when their digests are equal, which a program can choose (as for the atoms of `bdd::set`,
/// plan row PERF-set-tied-digest-depth). A big integer's or a fraction's stream is its
/// fingerprint ([`Rat::fingerprint`](crate::num::Rat::fingerprint), the residues modulo two
/// primes drawn at run time), not its digest, which is its residue modulo `2^61 - 1` and so ties
/// on `2^64 + k (2^61 - 1)` for every `k`; the same fingerprint gives its seeded weight
/// ([`Elem::seeded_weight`]), so a set of such values is a treap of expected depth O(log n)
/// whatever its program chose, under the conjecture stated at
/// [`fingerprint_primes`](zed_collections::priority::fingerprint_primes). Values that still tie
/// whatever the draw (tuples and families of equal digests) remain under
/// PERF-set-tied-digest-depth.
impl Elem for Value {
    fn priority(&self) -> u64 {
        static PRIORITIES: Priorities = Priorities::eight_wise(17).fixed_in_unit_tests(cfg!(test));
        match self {
            Value::Int(n) => PRIORITIES.of((*n as u64) ^ (1 << 63)),
            Value::Big(r) => PRIORITIES.hash(&(2u8, r.fingerprint())),
            Value::Rat(r) => PRIORITIES.hash(&(3u8, r.fingerprint())),
            v => PRIORITIES.hash(v),
        }
    }
    fn seeded_weight(&self) -> u64 {
        match self {
            Value::Big(r) => crate::treap_set::seeded((2u8, r.fingerprint())),
            Value::Rat(r) => crate::treap_set::seeded((3u8, r.fingerprint())),
            v => crate::treap_set::seeded(v.weight()),
        }
    }
    fn weight(&self) -> u64 {
        match self {
            Value::Int(_)
            | Value::Big(_)
            | Value::Rat(_)
            | Value::Float(_)
            | Value::Float32(_)
            | Value::Str(_) => scalar(self),
            v => {
                use std::hash::{Hash, Hasher};
                let mut h = crate::digest::Digest::default();
                v.hash(&mut h);
                h.finish()
            }
        }
    }
    /// By class, then 64-bit integers by value, big integers and `rat`s by their forms as held
    /// (`Rat::held_cmp`, which copies nothing where `Ord` may
    /// align the two), and every other kind by `Ord`: a total order, as each part is one.
    fn held_cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Value::Int(x), Value::Int(y)) => x.cmp(y),
            (Value::Big(x), Value::Big(y)) | (Value::Rat(x), Value::Rat(y)) => x.held_cmp(y),
            _ => match self.class().cmp(&other.class()) {
                Ordering::Equal => self.cmp(other),
                o => o,
            },
        }
    }
    fn class(&self) -> u32 {
        match self {
            Value::Int(_) => Value::INT_CLASS,
            Value::Big(_) => Value::BIG_CLASS,
            Value::Rat(_) => 4,
            Value::Float(_) => 8,
            Value::Float32(_) => 16,
            Value::Str(_) => 32,
            _ => 64,
        }
    }
}

impl Value {
    /// The class ([`Elem::class`]) of a 64-bit integer.
    pub const INT_CLASS: u32 = 1;
    /// The class of an integer wider than 64 bits.
    pub const BIG_CLASS: u32 = 2;
}

/// The program's own spelling of a literal value, if it has one: the text of a literal it
/// wrote, which reads back to that value ([`Type::surfaces_apart`]), with whether it is the
/// spelling wherever a message is written ([`Spelled`]).
pub type Spell<'a> = &'a dyn Fn(&Value) -> Spelled<'a>;

/// A literal value as the program spells it ([`Spell`]).
pub struct Spelled<'a> {
    /// The text of a literal the program wrote with the value, or `None` when it wrote none
    /// and the value is printed in canonical form. Borrowed where the program's text holds it,
    /// made where it adds a sign.
    pub text: Option<std::borrow::Cow<'a, str>>,
    /// Whether every message, written about any part of the program, spells the value so: a
    /// program that writes `0x1F` in one place and `31` in another spells `31` as written near
    /// each, so a printed type that holds it is printed again for each message rather than
    /// taken from an earlier one (MSG-derive-print-per-message).
    pub everywhere: bool,
}

/// A literal as a type prints it: a `rat` in canonical form ([`Rat::literal_text`]), so its
/// text costs the literal's length; an integer beyond 64 bits as its digits or, where shorter,
/// its powers ([`Rat::integer_text`]), so `3^200000` costs its own text; any other as the
/// value prints.
pub(crate) fn lit_text(v: &Value) -> String {
    match v {
        Value::Rat(r) => r.literal_text(),
        Value::Big(r) => r.integer_text(),
        other => other.to_string(),
    }
}

// Each type is one `Arc<Node>`, nearly all of them `Parts`: boxing `Parts` would add a second
// allocation and an indirection to every type, to save the unused bytes of the few recursive
// nodes (`Rec`). The `f32` part (FLOAT-f32) took `Parts` past clippy's limit.
#[allow(clippy::large_enum_variant)]
enum Node {
    Parts(Parts, Shown),
    Rec(Rec),
}

/// A node's parts and text are freed in a loop (module `deep`), so a type nested deep is freed
/// on any stack. A recursive node's body is a type, which frees its own node so.
impl Drop for Node {
    fn drop(&mut self) {
        if let Node::Parts(p, shown) = self {
            if let Some(key) = shown.compound.take() {
                let id = shown.id;
                let _ = COMPOUND_TYPES.try_with(|c| {
                    if let Ok(mut c) = c.try_borrow_mut()
                        && c.get(&key).is_some_and(|(n, _)| *n == id)
                    {
                        c.remove(&key);
                    }
                });
            }
            if !p.atoms.names().is_empty() {
                free(Freed::Atoms(p.atoms.take_names()));
            }
            if !p.atoms.payloads().is_empty() {
                free(Freed::Payloads(p.atoms.take_payloads()));
            }
            if let Some(dag) = p.atoms.take_payload_dag() {
                free(Freed::PayloadDag(dag));
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
            if let Some(r) = shown.text.take() {
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
    Payloads(atoms::PayloadTree),
    PayloadDag(Arc<atoms::PayloadNode>),
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

/// A number for local graph walks, never a type's digest, order or printed name.
fn next_type_node() -> u64 {
    static NEXT: zed_graph::IdSource = zed_graph::IdSource::starting_at(1);
    NEXT.next()
}

/// A type's text and local graph number. Neither takes part in comparing types.
struct Shown {
    text: OnceLock<Rope>,
    id: u64,
    compound: Option<Arc<CompoundKey>>,
}

impl Default for Shown {
    fn default() -> Self {
        Self {
            text: OnceLock::new(),
            id: next_type_node(),
            compound: None,
        }
    }
}

/// A recursive type, or a part of a recursive definition's body kept unevaluated: its parts are
/// `make()`, computed on first use. Two nodes are one type when their keys are equal.
struct Rec {
    id: u64,
    /// What the node stands for, by its group's definitions and arguments: its digest and order.
    key: rec::Key,
    /// The name, made when first printed: a name spells out its part of the definition, so
    /// making every part's name at once cost the product of the definition's size and depth.
    /// It is a rope holding the texts of the argument types, which [`Type::rope`] makes in its
    /// loop like any other text, and the names of the parts inside it, made once per instance
    /// (`rec::unfold::Env::part_name`).
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
                // `Type::p`, the one maker of `Unfolded`, unfolds in a loop until the node is no
                // `Rec`, so `t` is a node of parts.
                Node::Rec(_) => unreachable!("an unfolding is unfolded to a node of parts"),
            },
        }
    }
}

/// Unfoldings held while their parts are borrowed ([`Type::p_held`]): each is put in through a
/// shared reference and stays at its place until the holder is dropped, so a walk may keep
/// borrows into the parts of every recursive type it meets (the holder, its costs and their
/// tradeoff: [`zed_collections::held`]).
type Held = zed_collections::held::Held<Type>;

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
        let name_digest = mix(
            mix(
                mix(6, arrow.guarantee.name_digest()),
                arrow.permission.name_digest(),
            ),
            arrow.value.name_digest(),
        );
        Morphism(Shared::new(digest, name_digest, arrow))
    }

    pub(crate) fn digest(&self) -> u64 {
        self.0.digest
    }

    pub(crate) fn name_digest(&self) -> u64 {
        self.0.name_digest
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
    name_digest: u64,
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
                && let Some(bucket) = t.get_mut(&self.name_digest)
            {
                bucket.leave(self.slot, me);
                if bucket.is_empty() {
                    t.remove(&self.name_digest);
                }
            }
        });
    }
}

impl<K: Tabled> Shared<K> {
    /// The live node of the thread whose key equals `key`, or a new one put in the table.
    fn new(digest: u64, name_digest: u64, key: K) -> Arc<Shared<K>> {
        let bucket = |f: &mut dyn FnMut(&mut Bucket<Shared<K>>)| {
            crate::local::with(K::live(), |t| {
                f(t.borrow_mut().entry(name_digest).or_default())
            });
        };
        match bucket::find(bucket, |r| K::order(&r.key, &key)) {
            Ok(r) => r,
            Err(place) => {
                let r = Arc::new(Shared {
                    digest,
                    name_digest,
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
        let name_digest = items.iter().fold(5, |h, t| mix(h, t.name_digest()));
        Row(Shared::new(digest, name_digest, items))
    }

    pub(crate) fn digest(&self) -> u64 {
        self.0.digest
    }

    pub(crate) fn name_digest(&self) -> u64 {
        self.0.name_digest
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
        digests_cmp(
            (self.0.digest, self.name_digest()),
            (other.0.digest, other.name_digest()),
        )
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

impl std::hash::Hash for Row {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        // Rows equal under `==` have equal presentation hashes, by the proof at the hash of
        // `Type` (PROOF-sweep-zed-kernel): `Row::cmp` answers `Equal` by pointer equality or
        // through `digests_cmp` in the same way, and no hash of a row runs inside
        // `hash::blind`, which the assertion checks in a test build.
        debug_assert!(
            !names_blind(),
            "a type or row is hashed while names are left out"
        );
        self.name_digest().hash(h);
    }
}

thread_local! {
    static TUPLES: RefCell<Tables<Row>> = const { RefCell::new(Tables::new()) };
    static MORPHISMS: RefCell<Tables<Morphism>> = const { RefCell::new(Tables::new()) };
}

impl Literal for Row {
    fn table<R>(f: impl FnOnce(&mut Tables<Self>) -> R) -> R {
        crate::local::with(&TUPLES, |t| f(&mut t.borrow_mut()))
    }
    fn untable(f: impl FnOnce(&mut Tables<Self>)) {
        let _ = TUPLES.try_with(|t| t.try_borrow_mut().map(|mut t| f(&mut t)));
    }
    fn digest(&self) -> u64 {
        Row::digest(self)
    }
    fn name_digest(&self) -> u64 {
        Row::name_digest(self)
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
        crate::local::with(&MORPHISMS, |t| f(&mut t.borrow_mut()))
    }
    fn untable(f: impl FnOnce(&mut Tables<Self>)) {
        let _ = MORPHISMS.try_with(|t| t.try_borrow_mut().map(|mut t| f(&mut t)));
    }
    fn digest(&self) -> u64 {
        Morphism::digest(self)
    }
    fn name_digest(&self) -> u64 {
        Morphism::name_digest(self)
    }
    fn free(part: Owned<Morphism>) {
        free(Freed::Morphisms(part));
    }
    fn order(w: Walk<'_, Morphism>) -> std::cmp::Ordering {
        order(Morphism::walk(w))
    }
}

/// The steps of [`order()`] for the atoms of a universe and the nodes of its diagrams.
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

/// A pair to compare in [`order()`], the rest of two sequences compared in order, the order of two
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

/// The pairs of node ids [`order()`] found equal, hashed by `digest::Digest`: the default hasher
/// seeds itself per set and runs SipHash on each pair (EMPTY-morphism-next). SipHash: Aumasson
/// and Bernstein 2012, doi:10.1007/978-3-642-34931-7_28; the full comment is in `digest.rs`,
/// type `FixedState`.
type Equal = HashSet<(u64, u64), std::hash::BuildHasherDefault<crate::digest::Digest>>;

/// The order of the pair in `first`, the order of contents that `Ord` gives every type, row,
/// morphism type, part, diagram and expression: two types by digest, then by their parts field
/// by field (a recursive node after every other, two of them by key, `rec::Key::order`); two
/// rows by digest, then component by component; two morphism types by guarantee, permission and
/// value; two diagrams or expressions by digest, then by atom or connective, then by `hi` and
/// `lo` or by operands, a diagram before an expression; sequences (rows, atom names, tuple
/// lengths) lexicographically, a prefix first. Two nodes or expressions found equal are kept by
/// node id and not compared again, so the cost is one step per pair of nodes compared, not one per
/// path to them, and linear in the size when the two are equal. A loop with its own stack, as a
/// type can be deeper than the call stack: a row's components are types, whose tuple parts are
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
    //
    // Complexity tradeoff (COMPLEXITY.md K143): a stack made for each comparison allocated it
    // again at every comparison of tied digests, and a lookup among `n` keys of one digest
    // makes `O(log n)` of them, so `n` lookups allocated `O(n log n)` bytes. Used: the stack's
    // buffer is kept on the thread between comparisons (`STEPS`), so that a comparison
    // allocates for its stack only past the largest stack before it on its thread. Given up:
    // each thread holds the buffer of its largest stack, one `Step` per entry, until it ends.
    // A comparison made by another thread-local's destructor, once `STEPS` is gone, makes a
    // stack of its own and frees it.
    let mut steps = emptied(STEPS.try_with(std::cell::Cell::take).unwrap_or_default());
    let c = order_on(first, &mut steps);
    let _ = STEPS.try_with(|s| s.set(emptied(steps)));
    c
}

thread_local! {
    /// The buffer of the stack [`order()`] last used on this thread, empty. Taken while a
    /// comparison runs, so that a comparison inside it starts with an empty one of its own.
    static STEPS: std::cell::Cell<Vec<Step<'static>>> = const { std::cell::Cell::new(Vec::new()) };
}

/// `v` emptied, as a vector of another element type of the same size and alignment, with its
/// buffer: collecting a vector's own iterator into a vector reuses its buffer in place, so no
/// allocation is made (`alloc::vec::in_place_collect`; the scaling tests of `row_hash_sites`
/// in `bdd/set/tests.rs` count the bytes).
fn emptied<T, U>(mut v: Vec<T>) -> Vec<U> {
    v.clear();
    v.into_iter()
        .map(|_| unreachable!("the vector is empty"))
        .collect()
}

/// The loop of [`order()`] on the stack `steps`, empty at the start.
fn order_on<'a>(first: Step<'a>, steps: &mut Vec<Step<'a>>) -> Ordering {
    let mut equal = Equal::default();
    // The first step is held apart, so that a comparison its digests decide pushes nothing.
    let mut next = Some(first);
    while let Some(step) = next.take().or_else(|| steps.pop()) {
        let c = match step {
            Step::Equal(a, b) => {
                equal.insert((a, b));
                Ordering::Equal
            }
            Step::Is(c) => c,
            Step::Tuples(w) => walk(w, steps, &equal),
            Step::Arrows(w) => walk(w, steps, &equal),
            Step::Types(a, b) => types(a, b, steps, &equal),
            Step::Rows(a, b) => {
                if Arc::ptr_eq(&a.0, &b.0) {
                    continue;
                }
                digests_cmp((a.digest(), a.name_digest()), (b.digest(), b.name_digest()))
                    .then_with(|| items(a.iter(), b.iter(), steps, &equal))
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
                    c = types(x, y, steps, &equal);
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
            Step::Items(x, y) => items(x, y, steps, &equal),
            Step::Names(p, q, from) => atom_names((p, q), from, steps),
            Step::Lens(p, q, from) => tuple_lens((p, q), from, steps, &equal),
        };
        if c != Ordering::Equal {
            return c;
        }
    }
    Ordering::Equal
}

/// One step of [`order()`] on the remaining components of two rows: each pair of components is
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

/// One step of [`order()`] on two types: the fields in order, each read at once where it can be,
/// so that two types told apart without reading a nested type push nothing; at the first field
/// that needs a nested comparison (an atom's payload, a tuple length's part, the morphism part)
/// the fields after it are pushed in reverse and the nested comparison above them, so that they
/// are compared in order.
fn types<'a>(a: &'a Type, b: &'a Type, steps: &mut Vec<Step<'a>>, equal: &Equal) -> Ordering {
    if Arc::ptr_eq(&a.0, &b.0) {
        return Ordering::Equal;
    }
    let c = digests_cmp((a.digest(), a.name_digest()), (b.digest(), b.name_digest()));
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
        .then_with(|| p.f32s.cmp(&q.f32s))
        .then_with(|| p.strings.cmp(&q.strings))
        .then(p.atoms.cofinite().cmp(&q.atoms.cofinite()));
    if c != Ordering::Equal {
        return c;
    }
    let n = steps.len();
    let names = (p.atoms.names(), q.atoms.names());
    let c = atom_names(names, Bound::Unbounded, steps);
    if c != Ordering::Equal {
        return c;
    }
    let sum = (p.atoms.sum().cmp(&q.atoms.sum())).then(p.tuples.rest.cmp(&q.tuples.rest));
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

/// One step of [`order()`] on the atom names of two types after `from`, each with its part, read
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

/// One step of [`order()`] on the tuple lengths of two types after `from`, each with its part,
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

/// One step of [`order()`] on two diagrams, expressions or parts of one universe.
/// The step that compares two literals of sets (`(atom, taken)`): whether taken, then the atoms.
/// One step either way, so that it can wait on the stack behind the literals before it.
fn literals<'a, A: Ordered>(a: &'a (A, bool), b: &'a (A, bool)) -> Step<'a> {
    match a.1.cmp(&b.1) {
        Ordering::Equal => A::atoms(&a.0, &b.0),
        c => Step::Is(c),
    }
}

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
            let c = digests_cmp((x.digest(), x.name_digest()), (y.digest(), y.name_digest()))
                .then(v.cmp(w));
            if c != Ordering::Equal {
                return c;
            }
            walk(Walk::Cells(a, b), steps, equal)
        }
        Walk::SetsInOrder(None, None) => Ordering::Equal,
        Walk::SetsInOrder(None, Some(_)) => Ordering::Less,
        Walk::SetsInOrder(Some(_), None) => Ordering::Greater,
        Walk::Cells(a, b) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            let c = digests_cmp((a.digest, a.name_digest), (b.digest, b.name_digest));
            if c == Ordering::Equal {
                // The shapes follow the run's draw of priorities, so sequences of tied digests
                // are compared by their blocks in order (`bdd::Rest`), and found equal last.
                steps.extend([
                    Step::Equal(key.0, key.1),
                    A::walk(Walk::CellRest(bdd::Rest::new(a, b))),
                ]);
            }
            c
        }
        Walk::Sets(a, b) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            // A set's digests are sums over its literals, the same for every shape.
            let c = digests_cmp((a.digest, a.name_digest), (b.digest, b.name_digest));
            if c == Ordering::Equal {
                // Compared by their literals at once (one level, not a step on the stack);
                // `SetsInOrder` records the pair as equal once its literals compare equal.
                return walk(Walk::SetsInOrder(Some(a), Some(b)), steps, equal);
            }
            c
        }
        Walk::SetsInOrder(Some(a), Some(b)) => {
            // Two sets of tied digests, or two subtrees at one place in them, compared by their
            // literals in order. The shape follows the run's draw of priorities (module
            // `bdd::set`), but one draw gives one set one shape, so two subtrees of one size at
            // one place are compared subtree by subtree, with no allocation: when the left
            // subtrees have one size, the sequences compare as the left subtrees (of one
            // length), then the literals, then the right subtrees, each pair compared again the
            // same way; the right subtrees may differ in length, and an empty one is before a
            // non-empty one (`SetsInOrder(None, Some(_))`), a prefix first. Where the left sizes
            // differ, the two are distinct sets whose digests collide, and the rest of the two
            // is read in order by pieces (`bdd::Rest`, as sequences of blocks are). No digest
            // of a subtree is compared: which literals a subtree holds follows the draw.
            // Complexity tradeoff (PERF-xor-shape-free): the naive method compared the sets
            // root first, their roots' literals then their subtrees by digest, `O(1)` where the
            // roots differ, but reading the shape, which drawn priorities make a function of
            // the draw; read in order by pieces from the start, it took three allocations a
            // pair, 38% more instructions comparing equal lists built on two threads. Used:
            // `O(n)` with no allocation where the shapes agree, as they do for equal sets, one
            // step per pair of nodes; `O(k + d)` for a first difference at the `k`-th literal,
            // with the three allocations, only where they differ, which takes a collision of
            // two sets' 64-bit digests. Comparing by rank (`Set::select`) where they differ
            // would allocate nothing but cost `O(k d)`.
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            let (l, m) = (a.left.as_deref(), b.left.as_deref());
            if l.map_or(0, |s| s.len()) == m.map_or(0, |s| s.len()) {
                steps.extend([
                    Step::Equal(key.0, key.1),
                    A::walk(Walk::SetsInOrder(a.right.as_deref(), b.right.as_deref())),
                    literals(&a.key, &b.key),
                    A::walk(Walk::SetsInOrder(l, m)),
                ]);
            } else {
                steps.push(A::walk(Walk::SetRest(bdd::Rest::new(a, b))));
            }
            Ordering::Equal
        }
        Walk::SetRest(mut rest) => match rest.next(|x, y| equal.contains(&(x, y))) {
            Err(c) => c,
            Ok((x, y)) => {
                // The literals are compared before the rest, which waits below them.
                steps.extend([A::walk(Walk::SetRest(rest)), literals(&x.key, &y.key)]);
                Ordering::Equal
            }
        },
        Walk::CellRest(mut rest) => match rest.next(|x, y| equal.contains(&(x, y))) {
            Err(c) => c,
            Ok((x, y)) => {
                // The blocks are compared before the rest, which waits below them.
                steps.extend([
                    A::walk(Walk::CellRest(rest)),
                    A::walk(Walk::Sets(&x.block, &y.block)),
                ]);
                Ordering::Equal
            }
        },
        Walk::Exprs(a, b) => {
            let key = (a.id, b.id);
            if key.0 == key.1 || equal.contains(&key) {
                return Ordering::Equal;
            }
            // The digests are compared first: an exclusive or's halves are made only when the
            // digests tie (`Expr::form`).
            let c = digests_cmp((a.digest, a.name_digest), (b.digest, b.name_digest));
            if c != Ordering::Equal {
                return c;
            }
            // An exclusive or in its one form is compared by its constant and set, which its
            // digests are made from (module `bdd::xor`), before every other expression.
            match (a.xor_set(), b.xor_set()) {
                (Some((s, c)), Some((t, d))) => {
                    let c = c.cmp(&d);
                    if c == Ordering::Equal {
                        steps.extend([Step::Equal(key.0, key.1), A::walk(Walk::Sets(s, t))]);
                    }
                    return c;
                }
                (Some(_), None) => return Ordering::Less,
                (None, Some(_)) => return Ordering::Greater,
                (None, None) => {}
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

/// A type split by the places its members take in a union ([`Type::print_groups`]); each part
/// may be empty.
pub struct PrintGroups {
    /// Its numbers, booleans and string literals.
    pub low: Type,
    /// `String`, or what is left of it after some literals are taken out.
    pub string: Type,
    /// Its tuples and structs.
    pub tuples: Type,
    /// Its functions.
    pub morphisms: Type,
    /// Its atoms, cut by name at the cuts given.
    pub atoms: Vec<Type>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Parts {
    name_digest: u64,
    /// The hash of the other fields, set by [`Type::new`].
    digest: u64,
    /// Bit 0 for `false`, bit 1 for `true`.
    bools: u8,
    ints: Lits,
    rats: Lits,
    floats: Lits,
    f32s: Lits,
    strings: Lits,
    atoms: Atoms,
    tuples: Tuples,
    structs: bool,
    morphisms: Part<Morphism>,
}

/// A finite set of literals, or the complement of one within its base type. The set is a
/// persistent treap ([`TreapSet`]), so that a union or difference with a small set copies
/// nothing else, a cut to a range of literals is one path, and [`Lits::sum`], the wrapping sum
/// of its literals' hashes ([`scalar`]), is kept at each node as it changes. The finite-set
/// domain of the reduced product is a set of the same kind, so the two share their nodes
/// (CHECK-literal-union-cost).
#[derive(Clone, PartialEq, Eq, Debug, Default)]
struct Lits {
    cofinite: bool,
    values: TreapSet<Value>,
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
        self.cofinite
            .cmp(&other.cofinite)
            .then_with(|| match self.values == other.values {
                true => std::cmp::Ordering::Equal,
                false => self
                    .values
                    .cmp(&other.values)
                    .then(self.sum().cmp(&other.sum())),
            })
    }
}

impl PartialOrd for Lits {
    fn partial_cmp(&self, other: &Lits) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// The atoms of one name in a type: the bare atom, and those whose payload is in `payload`, a
/// type within the tuples and structs.
#[derive(Clone, PartialEq, Eq, Debug)]
struct AtomPart {
    bare: bool,
    payload: Type,
}

/// The atoms part of a type, [`Atoms`], in a module of its own so that its fields are private
/// to it: only [`Atoms::set`] writes the map of names, and only this module's constructors set
/// `cofinite`. So the invariant `set` keeps, that a map lists no name whose part is the default
/// of its kind (`AtomPart::none()` when finite, `AtomPart::all()` when cofinite), holds of every
/// `Atoms` the compiler accepts. The emptiness check's atom walks rely on it (`empty.rs`, the
/// `(false, true)` arms of `cycle_meet`, `find_prefix_chains`, `check_chain_witness` and
/// `list_rows`). The module is written here, not in a file of its own: `Atoms` reads
/// `AtomPart` and `Type`, and this file reads `Atoms`, so two files would import each other,
/// which Zed forbids (test `s_01f_import_graph`).
mod atoms {
    use super::*;

    /// Unique id for [`PayloadNode`] and [`PayloadEntry`], never reused.
    fn next_payload_node() -> u64 {
        static NEXT: zed_graph::IdSource = zed_graph::IdSource::starting_at(1);
        NEXT.next()
    }

    /// One `(name, bare, payload)` entry shared across path-copied [`PayloadNode`] ancestors,
    /// so walks that memoize per-entry work (`fields`, `decide_groups_read`) do not redo it on
    /// copied ancestor nodes along an AVL insertion path.
    #[derive(Debug)]
    struct PayloadEntry {
        id: u64,
        name: Arc<str>,
        bare: bool,
        payload: Type,
    }

    /// A node of a persistent AVL tree of payload-bearing atom entries `(name, bare, payload)`.
    ///
    /// Complexity tradeoff (R11-C3): `imbl::OrdSet<Arc<str>>` hides its internal B+ tree nodes,
    /// so `n` prefix unions sharing one persistent map were iterated in `O(n^2 log n)` by
    /// `decide_groups_read`, `fields`, and `Heights` (`r11_payload_name_prefixes_must_scale`:
    /// 68.9x instructions and 33.6x bytes from 128 to 1,024). A persistent AVL tree with unique
    /// `id`s per node and shared `Arc<PayloadEntry>` across path copies exposes structural sharing
    /// so every DAG walk visits each shared node once and evaluates each distinct entry once:
    /// `O(n log n)` total nodes, time, and bytes across `n` prefix unions. Insert/remove/lookup
    /// remain `O(log k)` with `height <= 1.44 log_2(k + 2)`.
    #[derive(Debug)]
    pub(in crate::types) struct PayloadNode {
        id: u64,
        height: u8,
        len: usize,
        entry: Arc<PayloadEntry>,
        left: Option<Arc<PayloadNode>>,
        right: Option<Arc<PayloadNode>>,
    }

    impl PayloadNode {
        #[inline]
        pub(in crate::types) fn id(&self) -> u64 {
            self.id
        }

        #[inline]
        pub(in crate::types) fn entry_id(&self) -> u64 {
            self.entry.id
        }

        #[inline]
        pub(in crate::types) fn name(&self) -> &Arc<str> {
            &self.entry.name
        }

        #[inline]
        pub(in crate::types) fn bare(&self) -> bool {
            self.entry.bare
        }

        #[inline]
        pub(in crate::types) fn payload(&self) -> &Type {
            &self.entry.payload
        }

        #[inline]
        pub(in crate::types) fn left(&self) -> Option<&Arc<PayloadNode>> {
            self.left.as_ref()
        }

        #[inline]
        pub(in crate::types) fn right(&self) -> Option<&Arc<PayloadNode>> {
            self.right.as_ref()
        }

        fn h(n: &Option<Arc<PayloadNode>>) -> i8 {
            n.as_ref().map_or(0, |x| x.height as i8)
        }

        fn sz(n: &Option<Arc<PayloadNode>>) -> usize {
            n.as_ref().map_or(0, |x| x.len)
        }

        fn new_entry(name: Arc<str>, bare: bool, payload: Type) -> Arc<PayloadEntry> {
            Arc::new(PayloadEntry {
                id: next_payload_node(),
                name,
                bare,
                payload,
            })
        }

        fn make(
            entry: Arc<PayloadEntry>,
            left: Option<Arc<PayloadNode>>,
            right: Option<Arc<PayloadNode>>,
        ) -> Arc<PayloadNode> {
            let height = 1 + Self::h(&left).max(Self::h(&right)) as u8;
            let len = 1 + Self::sz(&left) + Self::sz(&right);
            Arc::new(PayloadNode {
                id: next_payload_node(),
                height,
                len,
                entry,
                left,
                right,
            })
        }

        fn rot_left(x: &PayloadNode) -> Arc<PayloadNode> {
            let y = x.right.as_ref().expect("rot_left requires right child");
            let new_x = Self::make(x.entry.clone(), x.left.clone(), y.left.clone());
            Self::make(y.entry.clone(), Some(new_x), y.right.clone())
        }

        fn rot_right(y: &PayloadNode) -> Arc<PayloadNode> {
            let x = y.left.as_ref().expect("rot_right requires left child");
            let new_y = Self::make(y.entry.clone(), x.right.clone(), y.right.clone());
            Self::make(x.entry.clone(), x.left.clone(), Some(new_y))
        }

        fn balance(
            entry: Arc<PayloadEntry>,
            left: Option<Arc<PayloadNode>>,
            right: Option<Arc<PayloadNode>>,
        ) -> Arc<PayloadNode> {
            let bf = Self::h(&left) - Self::h(&right);
            if bf > 1 {
                let l = left.as_ref().expect("left-heavy node has left child");
                let l_rot = if Self::h(&l.left) < Self::h(&l.right) {
                    Some(Self::rot_left(l))
                } else {
                    None
                };
                let x = l_rot.as_deref().unwrap_or(l);
                let new_y = Self::make(entry, x.right.clone(), right);
                Self::make(x.entry.clone(), x.left.clone(), Some(new_y))
            } else if bf < -1 {
                let r = right.as_ref().expect("right-heavy node has right child");
                let r_rot = if Self::h(&r.right) < Self::h(&r.left) {
                    Some(Self::rot_right(r))
                } else {
                    None
                };
                let y = r_rot.as_deref().unwrap_or(r);
                let new_x = Self::make(entry, left, y.left.clone());
                Self::make(y.entry.clone(), Some(new_x), y.right.clone())
            } else {
                Self::make(entry, left, right)
            }
        }

        fn step(entry: Arc<PayloadEntry>, prev: Option<Arc<PayloadNode>>) -> Arc<PayloadNode> {
            Arc::new(PayloadNode {
                id: next_payload_node(),
                height: 1,
                len: 1,
                entry,
                left: prev,
                right: None,
            })
        }

        fn insert_entry(
            node: &Option<Arc<PayloadNode>>,
            entry: Arc<PayloadEntry>,
        ) -> Arc<PayloadNode> {
            let Some(n) = node else {
                return Self::make(entry, None, None);
            };
            match entry.name.cmp(&n.entry.name) {
                Ordering::Equal => {
                    if n.entry.bare == entry.bare && n.entry.payload == entry.payload {
                        n.clone()
                    } else {
                        Self::make(entry, n.left.clone(), n.right.clone())
                    }
                }
                Ordering::Less => Self::balance(
                    n.entry.clone(),
                    Some(Self::insert_entry(&n.left, entry)),
                    n.right.clone(),
                ),
                Ordering::Greater => Self::balance(
                    n.entry.clone(),
                    n.left.clone(),
                    Some(Self::insert_entry(&n.right, entry)),
                ),
            }
        }

        fn remove_min(n: &PayloadNode) -> (Arc<PayloadEntry>, Option<Arc<PayloadNode>>) {
            match &n.left {
                None => (n.entry.clone(), n.right.clone()),
                Some(l) => {
                    let (e, new_l) = Self::remove_min(l);
                    (
                        e,
                        Some(Self::balance(n.entry.clone(), new_l, n.right.clone())),
                    )
                }
            }
        }

        fn remove(node: &Option<Arc<PayloadNode>>, name: &str) -> (Option<Arc<PayloadNode>>, bool) {
            let Some(n) = node else {
                return (None, false);
            };
            match name.cmp(n.entry.name.as_ref()) {
                Ordering::Equal => match (&n.left, &n.right) {
                    (None, r) => (r.clone(), true),
                    (l, None) => (l.clone(), true),
                    (l, Some(r)) => {
                        let (e, new_r) = Self::remove_min(r);
                        (Some(Self::balance(e, l.clone(), new_r)), true)
                    }
                },
                Ordering::Less => {
                    let (new_l, removed) = Self::remove(&n.left, name);
                    if !removed {
                        (Some(n.clone()), false)
                    } else {
                        (
                            Some(Self::balance(n.entry.clone(), new_l, n.right.clone())),
                            true,
                        )
                    }
                }
                Ordering::Greater => {
                    let (new_r, removed) = Self::remove(&n.right, name);
                    if !removed {
                        (Some(n.clone()), false)
                    } else {
                        (
                            Some(Self::balance(n.entry.clone(), n.left.clone(), new_r)),
                            true,
                        )
                    }
                }
            }
        }
    }

    /// Persistent ordered map of payload-bearing atom names to `(bare, payload)` with node sharing.
    #[derive(Clone, Debug, Default)]
    pub(in crate::types) struct PayloadTree {
        root: Option<Arc<PayloadNode>>,
    }

    impl PartialEq for PayloadTree {
        fn eq(&self, other: &Self) -> bool {
            match (&self.root, &other.root) {
                (None, None) => true,
                (Some(a), Some(b)) if Arc::ptr_eq(a, b) => true,
                (Some(a), Some(b)) if a.len == b.len => {
                    self.iter_nodes().zip(other.iter_nodes()).all(|(x, y)| {
                        Arc::ptr_eq(&x.entry, &y.entry)
                            || (x.entry.name == y.entry.name
                                && x.entry.bare == y.entry.bare
                                && x.entry.payload == y.entry.payload)
                    })
                }
                _ => false,
            }
        }
    }

    impl Eq for PayloadTree {}

    pub(in crate::types) struct PayloadNodeIter<'a> {
        stack: Vec<&'a PayloadNode>,
    }

    impl<'a> PayloadNodeIter<'a> {
        fn new(root: Option<&'a PayloadNode>) -> Self {
            let mut it = PayloadNodeIter { stack: Vec::new() };
            it.push_left(root);
            it
        }

        fn push_left(&mut self, mut cur: Option<&'a PayloadNode>) {
            while let Some(n) = cur {
                self.stack.push(n);
                cur = n.left.as_deref();
            }
        }
    }

    impl<'a> Iterator for PayloadNodeIter<'a> {
        type Item = &'a PayloadNode;

        fn next(&mut self) -> Option<Self::Item> {
            let n = self.stack.pop()?;
            self.push_left(n.right.as_deref());
            Some(n)
        }
    }

    pub(in crate::types) struct PayloadNameIter<'a>(PayloadNodeIter<'a>);

    impl<'a> Iterator for PayloadNameIter<'a> {
        type Item = &'a Arc<str>;

        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|n| &n.entry.name)
        }
    }

    impl<'a> IntoIterator for &'a PayloadTree {
        type Item = &'a Arc<str>;
        type IntoIter = PayloadNameIter<'a>;

        fn into_iter(self) -> Self::IntoIter {
            self.iter()
        }
    }

    impl PayloadTree {
        #[inline]
        pub(in crate::types) fn is_empty(&self) -> bool {
            self.root.is_none()
        }

        #[inline]
        pub(in crate::types) fn len(&self) -> usize {
            self.root.as_ref().map_or(0, |n| n.len)
        }

        #[inline]
        pub(in crate::types) fn root(&self) -> Option<&Arc<PayloadNode>> {
            self.root.as_ref()
        }

        pub(in crate::types) fn contains(&self, name: &str) -> bool {
            let mut cur = self.root.as_deref();
            while let Some(n) = cur {
                match name.cmp(n.entry.name.as_ref()) {
                    Ordering::Equal => return true,
                    Ordering::Less => cur = n.left.as_deref(),
                    Ordering::Greater => cur = n.right.as_deref(),
                }
            }
            false
        }

        pub(in crate::types) fn get_min(&self) -> Option<&Arc<str>> {
            let mut cur = self.root.as_deref()?;
            while let Some(l) = cur.left.as_deref() {
                cur = l;
            }
            Some(&cur.entry.name)
        }

        pub(in crate::types) fn iter(&self) -> PayloadNameIter<'_> {
            PayloadNameIter(self.iter_nodes())
        }

        fn iter_nodes(&self) -> PayloadNodeIter<'_> {
            PayloadNodeIter::new(self.root.as_deref())
        }

        /// Visits every node reachable from `root` whose `id` is not yet in `seen`, skipping
        /// whole subtrees/prefixes already visited in an earlier shared DAG.
        pub(in crate::types) fn visit_unseen<S: std::hash::BuildHasher>(
            root: &PayloadNode,
            seen: &mut std::collections::HashSet<u64, S>,
            f: &mut impl FnMut(&Arc<str>, bool, &Type),
        ) {
            let mut stack = vec![(root, false)];
            while let Some((node, emit)) = stack.pop() {
                if emit {
                    f(&node.entry.name, node.entry.bare, &node.entry.payload);
                    continue;
                }
                if !seen.insert(node.id) {
                    continue;
                }
                if let Some(r) = node.right.as_deref() {
                    stack.push((r, false));
                }
                stack.push((node, true));
                if let Some(l) = node.left.as_deref() {
                    stack.push((l, false));
                }
            }
        }

        fn insert_entry(&mut self, entry: Arc<PayloadEntry>) {
            self.root = Some(PayloadNode::insert_entry(&self.root, entry));
        }

        fn remove(&mut self, name: &str) {
            let (new_root, _) = PayloadNode::remove(&self.root, name);
            self.root = new_root;
        }
    }

    impl Drop for PayloadNode {
        fn drop(&mut self) {
            let mut stack = Vec::new();
            if let Some(l) = self.left.take() {
                stack.push(l);
            }
            if let Some(r) = self.right.take() {
                stack.push(r);
            }
            while let Some(arc) = stack.pop() {
                if let Ok(mut node) = Arc::try_unwrap(arc) {
                    if let Some(l) = node.left.take() {
                        stack.push(l);
                    }
                    if let Some(r) = node.right.take() {
                        stack.push(r);
                    }
                }
            }
        }
    }

    /// Per atom name, its part; a name not listed has every payload when `cofinite`, else none.
    /// Invariant: no listed name has the part an unlisted one has (`AtomPart::none()` when
    /// finite, `AtomPart::all()` when cofinite), which the `(false, true) => unreachable!` arms
    /// of `types::empty` rely on. Proof, by the writers of `names`, all in this module (its
    /// fields are private): [`Atoms::set`] unlists a name given that part; `Atoms::default` and
    /// the universe list no name; [`Atoms::zip`] either builds through `set` or clones `large`
    /// and keeps `large.cofinite` (the comment there); `Atoms::minus` either builds through
    /// `set` or clones `self` with its own `cofinite`; `Atoms::join` and `Atoms::not` write
    /// only through `set`. Tests: the `unreachable!` arms are
    /// reached by no test (COMPLETENESS.md, cover7 round), which a test cannot prove.
    /// The map is persistent, and `sum` is the wrapping sum of its entries' hashes. `payloads`
    /// is the persistent AVL tree of listed names whose payload lists something, kept by
    /// [`Atoms::set`] in O(log n). When every payload mutation so far was a pure addition (no
    /// overwrite or removal of an existing payload name), `payload_dag` keeps the exact
    /// monotonic addition chain (`O(1)` nodes per addition, so `n` prefix unions create `n`
    /// shared nodes instead of `O(n log n)` AVL path-copy nodes, keeping DAG walks `O(n)` at
    /// `8x` per `8n` instead of `n log_2 n`'s `11.4x`); any overwrite or removal drops
    /// `payload_dag` to `None`, falling back to `payloads.root()` (`O(n log n)`). `bare` is the
    /// persistent set of the listed names that hold their bare atom, kept by [`Atoms::set`] in
    /// O(log n).
    // Complexity tradeoff: a count of the bare names (O(1) per `set`) says whether there is one
    // but not which, so finding it scanned `names` in order: `#a_0((0,)) | ... | #a_i((0,)) |
    // #z` read all i payload names before `#z` at every prefix, Θ(n²) over n prefixes
    // (`front_bare_name_after_payload_prefixes_must_scale`, 14.0 times for 8 times n). Used: the
    // set of bare names, O(log n) per `set` beside the O(log n) of `names` itself, so a bare name
    // is read in O(log n) and all of them in O(b) for their b.
    #[derive(Clone, Debug)]
    pub(super) struct Atoms {
        name_sum: u64,
        cofinite: bool,
        names: OrdMap<Arc<str>, AtomPart>,
        sum: u64,
        payloads: PayloadTree,
        /// `Some(head)` when all payload entries were added monotonically with no overwrite or
        /// removal; `None` otherwise (fall back to `payloads.root()`).
        payload_dag: Option<Option<Arc<PayloadNode>>>,
        bare: OrdSet<Arc<str>>,
    }

    impl Default for Atoms {
        fn default() -> Self {
            Atoms {
                name_sum: 0,
                cofinite: false,
                names: OrdMap::default(),
                sum: 0,
                payloads: PayloadTree::default(),
                payload_dag: Some(None),
                bare: OrdSet::new(),
            }
        }
    }

    impl PartialEq for Atoms {
        fn eq(&self, other: &Self) -> bool {
            // `payloads`, `payload_dag` and `bare` are derived indexes of `names`, kept solely by
            // `Atoms::set`.
            self.cofinite == other.cofinite
                && self.sum == other.sum
                && self.name_sum == other.name_sum
                && self.bare.len() == other.bare.len()
                && self.names == other.names
        }
    }

    impl Eq for Atoms {}

    impl Atoms {
        /// Every atom: cofinite, no name listed.
        pub(super) fn all() -> Atoms {
            Atoms {
                cofinite: true,
                ..Atoms::default()
            }
        }

        /// The listed names and their parts. No part listed is the default of the map's kind.
        pub(super) fn names(&self) -> &OrdMap<Arc<str>, AtomPart> {
            &self.names
        }

        /// Whether a name not listed has every payload (else none).
        pub(super) fn cofinite(&self) -> bool {
            self.cofinite
        }

        /// The wrapping sum of the entries' hashes.
        pub(super) fn sum(&self) -> u64 {
            self.sum
        }

        /// [`Atoms::sum`] by reference, for the debug writer, which queues references.
        pub(super) fn sum_ref(&self) -> &u64 {
            &self.sum
        }

        /// The wrapping sum of the entries' hashes by name digests.
        pub(super) fn name_sum(&self) -> u64 {
            self.name_sum
        }

        /// The persistent tree of listed names whose payload lists something.
        pub(super) fn payloads(&self) -> &PayloadTree {
            &self.payloads
        }

        /// The shared persistent DAG root of all payload-bearing entries: the `O(1)`-per-step
        /// monotonic addition chain when no payload entry was overwritten or removed, else the
        /// balanced AVL `PayloadTree` root.
        #[inline]
        pub(in crate::types) fn payload_dag(&self) -> Option<&Arc<PayloadNode>> {
            match &self.payload_dag {
                Some(opt) => opt.as_ref(),
                None => self.payloads.root(),
            }
        }

        /// Visits every payload-bearing entry reachable from [`Atoms::payload_dag`] whose node
        /// `id` is not yet in `seen`.
        pub(in crate::types) fn payload_entries_unseen<S: std::hash::BuildHasher>(
            &self,
            seen: &mut std::collections::HashSet<u64, S>,
            f: &mut impl FnMut(&Arc<str>, bool, &Type),
        ) {
            if let Some(root) = self.payload_dag() {
                PayloadTree::visit_unseen(root.as_ref(), seen, f);
            }
        }

        /// How many listed names hold their bare atom, O(1).
        pub(super) fn bare_names(&self) -> usize {
            self.bare.len()
        }

        /// The listed names that hold their bare atom, in name order.
        pub(super) fn bare(&self) -> &OrdSet<Arc<str>> {
            &self.bare
        }

        /// The map of names, taken out to be freed in a loop when the node holding it is
        /// dropped (`Drop for Node`). The empty map left behind lists no part, so it keeps the
        /// invariant; the sums are left stale, which nothing reads of a node being dropped.
        /// Proof: the one caller is `Drop for Node`, which takes the names, then the payloads
        /// and the payload DAG, and reads no sum or name of `p.atoms` after; the fields are
        /// then dropped without being read.
        pub(super) fn take_names(&mut self) -> OrdMap<Arc<str>, AtomPart> {
            std::mem::take(&mut self.names)
        }

        /// The tree of payload entries, taken out to be freed in a loop (`Drop for Node`).
        pub(super) fn take_payloads(&mut self) -> PayloadTree {
            std::mem::take(&mut self.payloads)
        }

        /// The monotonic payload DAG head, taken out to be freed in a loop (`Drop for Node`).
        pub(super) fn take_payload_dag(&mut self) -> Option<Arc<PayloadNode>> {
            self.payload_dag.take().flatten()
        }

        /// Whether it is the part of no atom, `Atoms::default()`, read with nothing built.
        pub(super) fn is_default(&self) -> bool {
            !self.cofinite && self.names.is_empty() && self.sum == 0
        }

        pub(super) fn get(&self, name: &str) -> AtomPart {
            match self.names.get(name) {
                Some(p) => p.clone(),
                None if self.cofinite => AtomPart::all(),
                None => AtomPart::none(),
            }
        }

        fn entries(name: &str, p: &AtomPart) -> (u64, u64) {
            let head = mix(fnv1a_64(name.as_bytes()), u64::from(p.bare));
            (
                mix(head, p.payload.digest()),
                mix(head, p.payload.name_digest()),
            )
        }

        /// Gives `name` the part `p`, unlisting it when `p` is what an unlisted name has.
        pub(super) fn set(&mut self, name: &Arc<str>, p: AtomPart) {
            let default = if self.cofinite {
                AtomPart::all()
            } else {
                AtomPart::none()
            };
            if let Some(old) = self.names.get(name) {
                if *old == p {
                    return;
                }
            } else if p == default {
                return;
            }
            let mut had_payload = false;
            let mut was_bare = false;
            if let Some(old) = self.names.remove(name) {
                let (primary, named) = Atoms::entries(name, &old);
                self.sum = self.sum.wrapping_sub(primary);
                self.name_sum = self.name_sum.wrapping_sub(named);
                had_payload = !old.payload.lists_nothing();
                was_bare = old.bare;
            }
            // `bare` lists a name exactly when it is listed in `names` with its bare atom.
            let is_bare = p.bare && p != default;
            if was_bare && !is_bare {
                self.bare.remove(name);
            } else if is_bare && !was_bare {
                self.bare.insert(name.clone());
            }
            if p != default {
                let (primary, named) = Atoms::entries(name, &p);
                self.sum = self.sum.wrapping_add(primary);
                self.name_sum = self.name_sum.wrapping_add(named);
                if !p.payload.lists_nothing() {
                    let entry = PayloadNode::new_entry(name.clone(), p.bare, p.payload.clone());
                    self.payloads.insert_entry(entry.clone());
                    if had_payload {
                        self.payload_dag = None;
                    } else if let Some(prev) = self.payload_dag.take() {
                        self.payload_dag = Some(Some(PayloadNode::step(entry, prev)));
                    }
                } else if had_payload {
                    self.payloads.remove(name);
                    self.payload_dag = None;
                }
                self.names.insert(name.clone(), p);
            } else if had_payload {
                self.payloads.remove(name);
                self.payload_dag = None;
            }
        }

        /// The parts combined by `op`. A name the smaller map does not list has every payload or
        /// none, and a part combined with all or none is itself, all or none: so the result is
        /// the larger map, or nothing, changed at the smaller map's names. When it is the larger
        /// map, only the names where the two differ change, since a part combined with itself is
        /// itself; those are found by walking the smaller map, `O(s log l)` steps for its `s`
        /// names and the larger's `l`, or by a diff of the two maps, which skips the nodes they
        /// share, so that two sets grown from one another, as a chain of merged failures grows
        /// the set of its members beside its loose atoms (ERRS-precise), differ in
        /// `O(d log l)` for their `d` differing names. The two walks advance in turn and the
        /// first to finish is used:
        // Complexity tradeoff: twice the cheaper walk, so `O(min(s, d + log l) log l)`, against
        // `O(s log l)` alone, which is quadratic for a chain of `n` such unions.
        pub(super) fn zip(&self, other: &Atoms, op: Op) -> Atoms {
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
            // `cofinite` is `large.cofinite` here (`Or` with `small` finite, `And` with it
            // cofinite), so the clone's names stay valid for it. Proof: this arm is reached
            // only for `(Or, false)`, where `cofinite` is `large.cofinite || false`, and for
            // `(And, true)`, where it is `large.cofinite && true`; so the default part of the
            // clone's kind is unchanged and no name it lists becomes the default.
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

        /// Joins `other` into `self` in place, both listing every name they hold (neither
        /// cofinite): `O(s log l)` for `other`'s `s` names and the result's `l`. A node `self`
        /// shares with another map is copied the first time it changes, and then changed in
        /// place.
        pub(super) fn join(&mut self, other: &Atoms) {
            debug_assert!(!self.cofinite && !other.cofinite);
            for (n, p) in &other.names {
                let joined = self.get(n).zip(p, Op::Or);
                self.set(n, joined);
            }
        }

        pub(super) fn not(&self) -> Atoms {
            let mut out = Atoms {
                cofinite: !self.cofinite,
                ..Atoms::default()
            };
            for (n, p) in &self.names {
                out.set(n, p.not());
            }
            out
        }

        /// The parts of `self` outside `other`: `self.zip(&other.not(), Op::And)`, each name's
        /// part the same, without building `other.not()`.
        ///
        /// Proof that it is that map. Write `s(n)` and `o(n)` for the parts `get` gives; the
        /// result at `n` is `s(n) & !o(n)` (`at`), and `set` leaves a name unlisted exactly when
        /// its part is the default of the result's kind, so it is enough that every name whose
        /// part may differ from that default is set. An unlisted name has the part none in a
        /// finite map and all in a cofinite one, and `!all` is none.
        /// - `self` cofinite, `other` finite: the result is cofinite (default all). At a name
        ///   `other` does not list, `!o(n)` is all and the part is `s(n)`, which `self.clone()`
        ///   already holds; so only `other`'s names are set.
        /// - Both cofinite: the result is finite (default none). At a name `other` does not
        ///   list, `!o(n)` is none; so only `other`'s names can be other than none.
        /// - `self` finite, `other` cofinite: finite. A name either map leaves unlisted gives
        ///   none (`s(n)` none, or `!o(n)` none), so only names both list matter, and setting
        ///   the names of either map, the smaller, covers them.
        /// - Both finite: finite. A name `self` leaves unlisted gives none, so setting `self`'s
        ///   names is enough; or, from `self.clone()`, a name `other` leaves unlisted keeps
        ///   `s(n) & all = s(n)`, so setting `other`'s names is enough.
        ///
        /// Each case reads the names of one map and gets `s(n)` and `o(n)` in O(log) each.
        // Complexity tradeoff: `O(min(s, o) log max(s, o))` for the `s` and `o` names listed,
        // where `self & !other` complemented each of `other`'s names first, `O(o log o)`
        // whatever `self` is. So `#a <: (#r1 | ... | #rk)`, asked of each arm of an `else if`
        // chain of `n` links returning `n` atoms, cost `O(k)` at depth `k`, the chain `Θ(n²)`:
        // 25.2 times the instructions for 8 times the links, 8.0 now (row
        // BENCH-if-chain-other-paths; test
        // `l08_02_remaps::bench::an_else_if_chain_returning_n_different_types_is_checked_in_n_log_n_time`;
        // COMPLEXITY.md K119).
        pub(super) fn minus(&self, other: &Atoms) -> Atoms {
            let at = |n: &Arc<str>| self.get(n).zip(&other.get(n).not(), Op::And);
            let fresh = |cofinite: bool, names: &OrdMap<Arc<str>, AtomPart>| {
                let mut out = Atoms {
                    cofinite,
                    ..Atoms::default()
                };
                for n in names.keys() {
                    out.set(n, at(n));
                }
                out
            };
            let changed = |names: &OrdMap<Arc<str>, AtomPart>| {
                let mut out = self.clone();
                for n in names.keys() {
                    out.set(n, at(n));
                }
                out
            };
            let smaller_self = self.names.len() <= other.names.len();
            match (self.cofinite, other.cofinite) {
                (true, false) => changed(&other.names),
                (true, true) => fresh(false, &other.names),
                (false, true) if smaller_self => fresh(false, &self.names),
                (false, true) => fresh(false, &other.names),
                (false, false) if smaller_self => fresh(false, &self.names),
                (false, false) => changed(&other.names),
            }
        }
    }
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
    /// `bool`, `int`, `rat`, `f64`, `String` and `f32`, made once, so that every use of one is
    /// one node and compares equal to another by pointer.
    static SCALARS: [Type; 6] = [
        Type::with(|p| p.bools = 3),
        Type::with(|p| p.ints.cofinite = true),
        Type::with(|p| p.rats.cofinite = true),
        Type::with(|p| p.floats.cofinite = true),
        Type::with(|p| p.strings.cofinite = true),
        Type::with(|p| p.f32s.cofinite = true),
    ];
    /// Each universe's type, made once, in the order of [`Universe`].
    static UNIVERSES: [Type; 4] = [
        Universe::Scalar,
        Universe::Tuple,
        Universe::Struct,
        Universe::Morphism,
    ]
    .map(Type::build_universe);
    /// The values an atom's payload may be, tuples and structs, made once.
    static PAYLOADS: Type = Type::universe(Universe::Tuple) | Type::universe(Universe::Struct);
}

impl Parts {
    /// Both fingerprints share the literal prefix and one pass over tuple lengths.
    fn hashes(&self) -> (u64, u64) {
        let mut h = mix(0, u64::from(self.bools));
        for l in [&self.ints, &self.rats, &self.floats, &self.strings] {
            h = mix(mix(h, u64::from(l.cofinite)), l.sum());
        }
        let base = mix(h, u64::from(self.atoms.cofinite()));
        let mut named = mix(base, self.atoms.name_sum());
        h = mix(base, self.atoms.sum());
        h = mix(h, u64::from(self.tuples.rest));
        named = mix(named, u64::from(self.tuples.rest));
        for (len, part) in &self.tuples.lens {
            h = mix(mix(h, *len as u64), part.digest());
            named = mix(mix(named, *len as u64), part.name_digest());
        }
        h = mix(mix(h, u64::from(self.structs)), self.morphisms.digest());
        named = mix(
            mix(named, u64::from(self.structs)),
            self.morphisms.name_digest(),
        );
        // The `f32` part is mixed in only where it holds a value, so a type without `f32`
        // values keeps the fingerprints it had before `f32` came (FLOAT-f32): orders that
        // follow digests stay as they were.
        let f = &self.f32s;
        match f.cofinite || !f.values.is_empty() {
            true => (
                mix(mix(h, u64::from(f.cofinite)), f.sum()),
                mix(mix(named, u64::from(f.cofinite)), f.sum()),
            ),
            false => (h, named),
        }
    }
}

impl Type {
    // Complexity tradeoff: rebuilding equal compound nodes during a search gives its
    // memos distinct local graph numbers: q copies can repeat a walk of g nodes,
    // costing O(q*g) work. Reuse a live node with identical retained diagram nodes
    // instead, so those memos can share the walk.
    // The key costs O(l) for l tuple lengths, the same as hashing these parts;
    // lookup is expected O(l). No structural equivalence or scalar sets are
    // compared. Nodes leave on drop on their creating thread; another thread's
    // dead entries are cleared at forget_emptiness. Neither these local numbers
    // nor this table affect the digest, comparison or printed text. Every search
    // route enters CompoundScope; construction outside a search keeps no index.
    // Exercised by
    // shared_parts_are_read_once_when_deciding_their_groups and the morphism
    // scaling tests, including the refused-member routes.
    fn new(mut p: Parts) -> Type {
        if crate::local::with(&COMPOUND_SEARCH, std::cell::Cell::get)
            && p.bools == 0
            && [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
                .iter()
                .all(|l| !l.cofinite && l.values.is_empty())
            && p.atoms.is_default()
        {
            let key = Arc::new((
                p.tuples.rest,
                p.structs,
                p.morphisms.id(),
                p.tuples.lens.iter().map(|(&n, f)| (n, f.id())).collect(),
            ));
            return crate::local::with(&COMPOUND_TYPES, |c| {
                let mut c = c.borrow_mut();
                if let Some(n) = c.get(&key).and_then(|(_, n)| Weak::upgrade(n)) {
                    return Type(n);
                }
                (p.digest, p.name_digest) = p.hashes();
                let shown = Shown {
                    compound: Some(key.clone()),
                    ..Shown::default()
                };
                let id = shown.id;
                let n = Arc::new(Node::Parts(p, shown));
                c.insert(key, (id, Arc::downgrade(&n)));
                Type(n)
            });
        }
        // Equal literal sets made apart become one tree ([`HashConsTable`], TYPE-hashcons), so
        // `Lits::cmp` decides them by `ptr_eq`. The digest reads only each set's sum, which
        // sharing leaves as it is.
        crate::local::with(&LITS, |t| {
            let mut t = t.borrow_mut();
            for l in [
                &mut p.ints,
                &mut p.rats,
                &mut p.floats,
                &mut p.f32s,
                &mut p.strings,
            ] {
                t.share(&mut l.values);
            }
        });
        (p.digest, p.name_digest) = p.hashes();
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

    /// A cached hash of the retained spelling, used by identity tables, never as a proof.
    // Complexity tradeoff: hashing a presentation by walking its DAG costs O(nodes) per
    // lookup. Cache one word at construction from the children's cached words, O(1)
    // per fixed-arity node and O(arity) for a variable-arity node.
    pub(crate) fn name_digest(&self) -> u64 {
        match &*self.0 {
            Node::Parts(p, _) => p.name_digest,
            Node::Rec(r) => r.key.name_digest(),
        }
    }

    /// The address of this type's node: equal for two handles on one node, and not reused
    /// while a handle on the node is held. A set or map keyed by it must hold a handle on each
    /// node it is keyed by, or borrow one, for as long as it lives, and must not be iterated
    /// where the order would reach an answer, since addresses differ from run to run. The
    /// users (`first_member`, `Env::member`) do both; `decide_groups_read` and
    /// `Searching::cut` key by [`Type::node_id`] instead.
    pub(crate) fn node_addr(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }

    /// The number of this allocation, shared by its handles and never reused. It is used
    /// only for local lookups; allocation order does not enter comparison or hashing of types.
    pub(crate) fn node_id(&self) -> u64 {
        match &*self.0 {
            Node::Parts(_, shown) => shown.id,
            Node::Rec(r) => r.id,
        }
    }

    /// The node named `naming()` whose parts are `make()`'s, each computed when first needed.
    /// `make` must not need this node's parts, which a contractive definition ensures.
    fn rec(
        key: rec::Key,
        naming: impl Fn() -> Rope + Send + Sync + 'static,
        make: impl Fn() -> Type + Send + Sync + 'static,
    ) -> Type {
        Type(Arc::new(Node::Rec(Rec {
            id: next_type_node(),
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
    pub fn is_recursive(&self) -> bool {
        matches!(&*self.0, Node::Rec(_))
    }

    /// Whether its parts hold no other type: it is no recursive type by name, it has no
    /// tuple, struct or morphism, no atom of it has a payload (the tree of payloads lists
    /// every name whose payload is not empty, [`Atoms::payloads`]), and its atoms are
    /// finitely many names (a cofinite set holds every payload of a name it does not list).
    /// Then each value of it is a scalar or a bare atom, and every type its parts name is
    /// none: so it reaches no type, a recursive one least of all. A sufficient test, not a
    /// complete one: `(int,)` holds no recursive type and is not such a type. O(1).
    pub(super) fn holds_no_type(&self) -> bool {
        let Node::Parts(p, _) = &*self.0 else {
            return false;
        };
        !p.structs
            && p.morphisms.is_leaf() == Some(false)
            && !p.tuples.rest
            && p.tuples.lens.is_empty()
            && !p.atoms.cofinite()
            && p.atoms.payloads().is_empty()
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
            // `Type::p` of a `Rec` node gives `Unfolded` and unfolds it to a node of parts, and
            // `Held::put` gives back the type it was given.
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
        crate::local::with(&EMPTY, Type::clone)
    }

    fn build_empty() -> Type {
        Type::new(Parts {
            digest: 0,
            name_digest: 0,
            bools: 0,
            ints: Lits::default(),
            rats: Lits::default(),
            floats: Lits::default(),
            f32s: Lits::default(),
            strings: Lits::default(),
            atoms: Atoms::default(),
            tuples: Tuples::default(),
            structs: false,
            morphisms: Part::leaf(false),
        })
    }

    /// Every value, `_`.
    pub fn top() -> Type {
        crate::local::with(&TOP, Type::clone)
    }

    /// The union of `ts`, joined in pairs: `k` tuple or morphism types, each ordered after the
    /// last in the diagrams, cost `O(k log k)` nodes joined this way and `O(k²)` one at a time.
    /// The types of atoms alone (no name holding every payload) are first joined into one map
    /// of names: the largest one's, shared as `Atoms::zip` shares it, with the others' names
    /// added in turn, so that a node is copied once and then changed in place.
    // Complexity tradeoff: in pairs, the atoms of `k` such types are added to a map shared
    // with an operand, copying a path each time, about `log k` times each, so `O(k log² k)`
    // steps, each copying a node; into one map, each once, `O(k log k)`. The union of a
    // finite set's `k` atom literals (`Product::reduce_domains`) took the larger. A fresh map
    // in place of the largest operand's would copy every name of a union of a large type with
    // a small one, quadratic in space over a chain of such unions
    // (`l01_23_subtyping::rec::recursive_definitions_scale`: 32.2 times the bytes from 100 to
    // 800 definitions). The maps are imbl B-trees, persistent by path copying: J. R. Driscoll,
    // N. Sarnak, D. D. Sleator and R. E. Tarjan, "Making data structures persistent", J. Comput.
    // System Sci. 38(1):86-124, 1989, doi:10.1016/0022-0000(89)90034-2, §4 p. 116, credit it to
    // Myers, Krijnen and Meertens, Reps et al. and Swart: "copying the entire access path and
    // all other changed nodes each time an insertion or deletion occurs ... O(log n) space and
    // time in the worst case per insertion or deletion" (the paper's own node copying saves the
    // log factor in space; imbl does not use it). Checked 2026-11-19 against the paper's text
    // and Crossref; imbl's code not read for this. An insert here copies the nodes on its path
    // only while another map shares them. Measured by
    // `l01_27_absences::scaling::the_repairs_for_a_family_of_many_atoms_scale`: 9.06 times the
    // instructions from 1000 to 8000 atoms joined in pairs, 8.67 now, with 17% and 20% fewer
    // instructions at the two sizes.
    // The types of finitely many booleans, numbers and strings alone are joined the same way,
    // into the sets of the one with the most literals (FAIL-setop-parity-bench-time): in pairs,
    // a union of `k` literals copied a path of each set `log k` times per literal, and folded
    // one at a time with `|`, as tests built such sets, each step copies the path of a set
    // shared with the operand before. Measured on the 2,097,152 even integers below 2^22 made
    // as literal types (`shared_integer_columns`), in one process at load 33: joined here,
    // 1.46 s; folded with `|`, 7.66 s (262,144: 0.26 s and 0.78 s); making the literal types
    // takes 2.69 s more either way.
    // Complexity tradeoff (PERF-equal-functions-forms-ratio): the types whose every value is a
    // tuple of a union of tuple literals at each length, as `KType::tuple` makes, are joined at
    // once ([`Tuples::union_of_literals`]): their literals sorted, `O(k log k)` comparisons, and
    // the one treap of them built bottom up, `k` set nodes each looked up once in the table.
    // In pairs, each level of the pairing made the nodes of the merged treaps again, `O(k log k)`
    // nodes made and looked up in all, each lookup comparing tuple types: 71% of the set nodes
    // made by `functions_equal_at_one_place_are_decided_a_second_time_in_linear_time`, 10.9
    // times as many from n = 256 to 2048. The joined type takes the place of the first of the
    // tuple types in `rest`, and the empty type the places of the others, and only where no
    // other type in `rest` holds a tuple; else they stay as they came (PROOF-union-all-expr-parts).
    // Proof that the result is the one the pairs make on `rest` as it came: `|` (`Type::zip`)
    // joins each part apart from the others, and a part joined with the part of nothing is the
    // other part (`Part::zip_at_once`; the scalar and atom parts are sets, so equal as values).
    // A tuple type has the part of nothing in every part but its tuples, as the empty type and
    // the joined type do, so every part but the tuples sees the same types at the same places
    // and the same pairs. In the tuples, every other type has the part of nothing, so the pairs
    // join the tuple literals, at each length a list or treap of literals, which has one form
    // for each set (`Bdd`), the form `union_of_literals` builds. Where another type holds tuples,
    // perhaps as an expression (`Part::Expr`), whose form depends on how it is bracketed, nothing
    // is moved. Before PROOF-union-all-expr-parts, the joined type went to the end of `rest`,
    // which changed the bracketing of the other parts.
    // The joined literals and the joined atoms are placed the same way
    // (PROOF-kernel-proofdoc3a-gaps
    // (g)); before, both went to the end of `rest`, which changed the pairing of the morphisms of
    // the other types (the test with literal and atom types added fails so: mask 0b1000101010).
    // Literals: a literal type has the part of nothing in every part but its scalars, as the
    // empty type and the joined type do, so every other part sees the same types at the same
    // places; the scalar parts are sets (`Lits`, a sorted set and a cofinite flag, one form per
    // set), so any bracketing of their unions gives one value, here the union of all of them.
    // No condition is needed. Atoms: an atom type alone has the part of nothing but in its atoms,
    // so again every other part is unchanged. Its atoms part is a map from names to payloads,
    // and a payload is a type whose form may depend on bracketing; so the map is placed only when
    // (1) no other type in `rest` holds an atom (its atoms part lists no name and is not
    // cofinite), so the pairs join the atoms of these types alone, and (2) no name is in two of
    // them, checked by counting: `join` keeps a listed name listed (a listed payload is not the
    // part of nothing, nor its union with another), so the joined map lists the sum of the
    // names exactly when no two maps share one. Then each name's payload is joined with the part
    // of nothing only, so it is that payload under any pairing, and the map, a persistent sorted
    // map with one form per content, is the one the pairs build. Else the atom types stay as
    // they came and the join made for the check is dropped: `O(s log l)` steps wasted, and the
    // `O(k log² k)` of the pairs where names repeat. Tests:
    // `union_all_is_the_union_joined_in_pairs_in_order` and, for the chains of literals,
    // `a_chain_joined_at_once_is_the_chain_joined_literal_by_literal`.
    pub fn union_all(ts: impl IntoIterator<Item = Type>) -> Type {
        // The literal types are joined as they come, each dropped once joined, so that `k` of
        // them are never all held at once; the smaller set is added to the larger.
        let (mut first_lits, mut lits): (Option<Type>, Option<Parts>) = (None, None);
        let (mut atoms, mut tuples, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        // The place in `rest` of the first literal type; the others hold the empty type.
        let mut lits_at = None;
        for t in ts {
            if t.finite_literals_only() {
                lits_at.get_or_insert(rest.len());
                rest.push(Type::empty());
                match (&first_lits, &mut lits) {
                    (None, _) => first_lits = Some(t),
                    (Some(first), None) => {
                        let (p, q) = (first.p(), t.p());
                        let (mut big, small) = match p.literal_count() < q.literal_count() {
                            true => (q.clone(), p),
                            false => (p.clone(), q),
                        };
                        big.join_literals(&small);
                        lits = Some(big);
                    }
                    (Some(_), Some(joined)) => {
                        let q = t.p();
                        if joined.literal_count() < q.literal_count() {
                            let mut big = q.clone();
                            big.join_literals(&*joined);
                            *joined = big;
                        } else {
                            joined.join_literals(&q);
                        }
                    }
                }
            } else if t.tuple_literals_only() {
                tuples.push(rest.len());
                rest.push(t);
            } else if t.atoms_only() && !t.p().atoms.cofinite() {
                atoms.push(rest.len());
                rest.push(t);
            } else {
                rest.push(t);
            }
        }
        // The tuples joined at once take the place of the first of them, and the type of
        // nothing the places of the others, so that the pairs below join every other part in
        // the order they joined it before; only where no other type holds a tuple, so that the
        // tuples are those of the joined type alone (proof above).
        let alone = || {
            (rest.iter().enumerate())
                .all(|(i, t)| tuples.binary_search(&i).is_ok() || t.holds_no_tuple())
        };
        if tuples.len() > 1 && alone() {
            let joined = {
                let parts: Vec<_> = tuples.iter().map(|&i| rest[i].p()).collect();
                Tuples::union_of_literals(parts.iter().map(|p| &p.tuples))
            };
            if let Some(joined) = joined {
                rest[tuples[0]] = Type::with(|p| p.tuples = joined);
                for &i in &tuples[1..] {
                    rest[i] = Type::empty();
                }
            }
        }
        if let Some(at) = lits_at {
            rest[at] = match lits {
                Some(joined) => Type::new(joined),
                None => first_lits.expect("a literal type was met"),
            };
        }
        // The atoms joined into one map take the place of the first atom type, and the empty
        // type the places of the others, only where no name is in two of them and no other type
        // in `rest` holds an atom; else they stay as they came (proof above).
        let atoms_alone = || {
            (rest.iter().enumerate()).all(|(i, t)| {
                let a = &t.p().atoms;
                atoms.binary_search(&i).is_ok() || (!a.cofinite() && a.names().is_empty())
            })
        };
        if atoms.len() > 1 && atoms_alone() {
            let largest = (atoms.iter().copied())
                .max_by_key(|&i| rest[i].p().atoms.names().len())
                .expect("two at least");
            let mut joined = rest[largest].p().atoms.clone();
            let mut listed = joined.names().len();
            for &i in &atoms {
                if i != largest {
                    let other = &rest[i].p().atoms;
                    listed += other.names().len();
                    joined.join(other);
                }
            }
            if joined.names().len() == listed {
                rest[atoms[0]] = Type::with(|p| p.atoms = joined);
                for &i in &atoms[1..] {
                    rest[i] = Type::empty();
                }
            }
        }
        Type::pairwise(rest, Type::empty(), |a, b| a | b)
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
        crate::local::with(&SCALARS, |s| s[0].clone())
    }

    /// `int`.
    pub fn int() -> Type {
        crate::local::with(&SCALARS, |s| s[1].clone())
    }

    /// `rat`.
    pub fn rat() -> Type {
        crate::local::with(&SCALARS, |s| s[2].clone())
    }

    /// `f64`.
    pub fn f64() -> Type {
        crate::local::with(&SCALARS, |s| s[3].clone())
    }

    /// `String`.
    pub fn string() -> Type {
        crate::local::with(&SCALARS, |s| s[4].clone())
    }

    /// `f32`.
    pub fn f32() -> Type {
        crate::local::with(&SCALARS, |s| s[5].clone())
    }

    /// The six whole scalar types `bool`, `int`, `rat`, `f64`, `String` and `f32`, in the order
    /// of [`Split::bases`], so that `split.bases[i]` is whole where it equals `scalars()[i]`.
    pub fn scalars() -> [Type; 6] {
        crate::local::with(&SCALARS, |s| s.clone())
    }

    /// The type of one scalar literal or bare atom; `None` for any other value.
    pub fn lit(v: &Value) -> Option<Type> {
        let one = |l: &mut Lits| l.insert(v);
        Some(match v {
            Value::Bool(b) => Type::with(|p| p.bools = 1 << u8::from(*b)),
            Value::Int(_) | Value::Big(_) => Type::with(|p| one(&mut p.ints)),
            Value::Rat(_) => Type::with(|p| one(&mut p.rats)),
            Value::Float(_) => Type::with(|p| one(&mut p.floats)),
            Value::Float32(_) => Type::with(|p| one(&mut p.f32s)),
            Value::Str(_) => Type::with(|p| one(&mut p.strings)),
            Value::Atom(a) if a.is_bare() => Type::atom(&a.name),
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

    /// The first part, at any depth, that holds values a function may be in: every tuple or
    /// struct, every tuple of a length outside the tuple types listed for it, or a morphism.
    /// The part found is given as its tuples, structs and morphisms, as [`Type::split`] gives
    /// them; `None` when every value is data. The components of the tuple types a tuple of the
    /// part may be in are walked: those some path of the part to `true` takes, so a tuple type
    /// the part only subtracts is not, as `((..), int)` in `(int, int) \ ((..), int)`. A tuple
    /// of the part with a function in a component is in some tuple type of the part, since it
    /// is outside every one only when the part holds a tuple outside them all, which is found
    /// first; and a tuple type it is in that a path to `true` takes holds the function in that
    /// component. The payloads of each atom name listed are walked; the atoms of the names not
    /// listed are not read as holding a function, since a payload not listed is not known
    /// (`zedc_types::Ty::payloads`), as a set's own atoms are not.
    // Complexity tradeoff (COMPLEXITY.md K103): naive version, a walk of the paths from the
    // root, 2^n for a pair nested n deep whose components are one node, and endless on a
    // recursive type. Used: each type walked once, by a set of node numbers, and each node of
    // a tuple part once for each value it is walked toward, by a set of node ids, O(n) for a
    // type of n nodes. Given up: a tuple type taken on a path to `true` is walked whether or
    // not the other tuple types that path takes leave a value with a function in it, so
    // `(int, int) & ((..), int)` is read as holding a function though it holds only pairs of
    // `int`s. Why: which tuple types a value with a function may be in together is a search
    // over the meets of the tuple types (coNP-hard, as emptiness is, `types/empty.rs`).
    // Trigger: a meet of tuple types, one with a component that holds a kind-wide part and
    // another that cuts it away. Tests: `types::tests::a_function_part_is_found_at_any_depth`,
    // `a_function_part_follows_only_the_tuple_types_a_path_to_true_takes`,
    // `a_function_part_is_found_in_a_recursive_type_once_per_node`, and
    // `l01_22_type_representation::kinds::the_function_part_of_a_kind_wide_part_is_found_in_linear_time`.
    // The complete solution meets the component types each path takes before walking them.
    // Each type is pushed once, when first met, not skipped when popped a second time: the
    // walk of a part (`Part::taken_toward`) skips a subtree it has walked and walks again a node
    // that another set rebuilt, so how often a row is met follows the draw of the treaps'
    // priorities, while the order in which rows are first met does not (a skipped subtree was
    // walked in full before, and the walk reads each set in order). Skipping at the pop let a
    // row met a second time come out first under some draws (cross-review of
    // PERF-xor-shape-free, Sol X2-F1; test
    // `the_function_part_of_a_meet_of_unions_sharing_rows_is_fixed_by_the_type`).
    pub fn function_part(&self) -> Option<Type> {
        let mut seen = HashSet::new();
        let mut paths = crate::digest::DigestSet::default();
        seen.insert(self.node_id());
        let mut stack = vec![self.clone()];
        while let Some(t) = stack.pop() {
            let p = t.p();
            let open = p.tuples.rest || p.tuples.lens.values().any(|b| b.eval(&|_| false));
            if open || p.structs || p.morphisms.is_leaf() != Some(false) {
                // A part whose tuples, structs and morphisms are empty holds no value there.
                match t.split().rest {
                    Some(rest) => return Some(rest),
                    None => continue,
                }
            }
            let payloads = p.atoms.names().values().map(|a| &a.payload);
            stack.extend(payloads.filter(|t| seen.insert(t.node_id())).cloned());
            for part in p.tuples.lens.values() {
                part.taken_toward(true, &mut paths, &mut |r| {
                    stack.extend(r.iter().filter(|t| seen.insert(t.node_id())).cloned())
                });
            }
        }
        None
    }

    /// Every value of `u`.
    pub fn universe(u: Universe) -> Type {
        crate::local::with(&UNIVERSES, |us| us[u as usize].clone())
    }

    fn build_universe(u: Universe) -> Type {
        Type::with(|p| match u {
            Universe::Scalar => {
                p.bools = 3;
                for l in [
                    &mut p.ints,
                    &mut p.rats,
                    &mut p.floats,
                    &mut p.f32s,
                    &mut p.strings,
                ] {
                    l.cofinite = true;
                }
                p.atoms = Atoms::all();
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
        crate::local::with(&PAYLOADS, Type::clone)
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
        // Complexity tradeoff: the recursive descent this replaces kept only recursive nodes
        // in its seen set, so a type shared by two components of a tuple was walked once per
        // path: 2^d visits for `t(d) = (t(d-1), t(d-1))` with d + 1 distinct types (Codex R9,
        // R9-C7), on O(d) native stack. Now a worklist visits each distinct type once: O(V + E)
        // visits and O((V + E) log V) key comparisons for V types and E written edges, on the
        // heap. It reads only the atom names whose payload lists something
        // (`Atoms::payloads`), as a payload that lists nothing has no morphisms; reading every
        // name made a chain of n failure atoms cost n^2 log n in the sweeps (batch merge 128).
        // The answer is unchanged: false exactly when a reachable type has morphism bounds.
        let mut seen = BTreeSet::new();
        let mut payload_seen = crate::digest::DigestSet::default();
        zed_graph::reach_until(
            [self.clone()],
            |t| seen.insert(t.clone()),
            |t| {
                if t.has_morphism_bounds() {
                    return std::ops::ControlFlow::Break(());
                }
                let mut kids = Vec::new();
                let p = t.p();
                p.atoms
                    .payload_entries_unseen(&mut payload_seen, &mut |_, _, payload| {
                        kids.push(payload.clone());
                    });
                p.tuples.atoms(&mut |row| {
                    kids.extend(row.iter().cloned());
                    true
                });
                std::ops::ControlFlow::Continue(kids)
            },
        )
        .is_none()
    }

    /// Whether every function is in `self`; for a decidable type, either every function is or
    /// none is.
    pub fn functions(&self) -> bool {
        self.p().morphisms.is_leaf() == Some(true)
    }

    /// Whether it holds every function (`Some(true)`) or none (`Some(false)`), read from its
    /// parts in O(1); `None` when it holds some and not others.
    pub fn functions_leaf(&self) -> Option<bool> {
        self.p().morphisms.is_leaf()
    }

    /// The type with each node of parts at every depth outside functions made again by
    /// `level`: the type itself, the payload of each atom name its parts list, and each
    /// component of each tuple type its tuple parts are made of, each made by `level` from the
    /// node with the nodes below it made first. A name its parts do not list, the tuples of a
    /// length they do not list, its structs and its functions are kept as they are. `None` when
    /// `level` gives none for a node, or for a recursive node whose unfolding holds, at any
    /// depth, a node `level` does not give back unchanged: such a node is not made again.
    /// `level` must give a node of parts, never a recursive node, for the node of parts it is
    /// given (checked; panics otherwise), since what it gives may become an atom's payload.
    ///
    /// A tuple part is made again from the tuple types it is made of, each replaced by the one
    /// of its components made again (`Part::map_atoms`): a value is in a tuple part exactly
    /// when the part's connectives, applied to whether the value is in each tuple type, give
    /// true, so a value is in the part made again exactly when they give true applied to
    /// whether it is in each tuple type made again.
    ///
    /// `memo` holds what each node was made into, across calls: each node is made once, from a
    /// stack, since nodes nest as deep as the program. A recursive node's unfolding is walked
    /// once, by node number, stopping at nodes `memo` has; a node it changes ends the walk with
    /// `None`. Cost: the nodes of the type not in `memo`, each read once and `level` once, plus
    /// the tuple parts made again (`Part::map_atoms`); a node no node below it changes, and
    /// `level` gives back, is the node itself, with nothing built.
    pub fn rewrite_levels(
        &self,
        memo: &mut HashMap<Type, Option<Type>>,
        level: &mut impl FnMut(&Type) -> Option<Type>,
    ) -> Option<Type> {
        let mut stack = vec![(self.clone(), false)];
        while let Some((t, ready)) = stack.pop() {
            if memo.contains_key(&t) {
                continue;
            }
            let Node::Parts(p, _) = &*t.0 else {
                let kept = Type::rec_kept(&t, memo, level).then(|| t.clone());
                memo.insert(t, kept);
                continue;
            };
            let rows: Vec<(usize, Vec<Row>)> = (p.tuples.lens.iter())
                .map(|(n, part)| (*n, part.distinct_atoms()))
                .collect();
            let payloads = p.atoms.names().values().map(|a| &a.payload);
            let mut below = payloads.chain(rows.iter().flat_map(|(_, rs)| rs.iter().flatten()));
            if !ready {
                stack.push((t.clone(), true));
                let left: Vec<Type> = below.filter(|c| !memo.contains_key(*c)).cloned().collect();
                stack.extend(left.into_iter().map(|c| (c, false)));
                continue;
            }
            if below.any(|c| memo[c].is_none()) {
                memo.insert(t, None);
                continue;
            }
            let made = |c: &Type| memo[c].clone().expect("tested above");
            let mut q: Option<Parts> = None;
            for (n, a) in p.atoms.names() {
                let payload = made(&a.payload);
                if payload != a.payload {
                    let bare = a.bare;
                    (q.get_or_insert_with(|| p.clone()).atoms).set(n, AtomPart { bare, payload });
                }
            }
            for (n, rs) in &rows {
                let again: HashMap<&Row, Row> = (rs.iter())
                    .filter_map(|r| {
                        let cs: Vec<Type> = r.iter().map(made).collect();
                        (cs.iter().zip(r.iter()).any(|(c, d)| c != d)).then(|| (r, Row::new(cs)))
                    })
                    .collect();
                if !again.is_empty() {
                    let part = p.tuples.lens[n].map_atoms(&|r| again.get(r).unwrap_or(r).clone());
                    (q.get_or_insert_with(|| p.clone()).tuples.lens).insert(*n, part);
                }
            }
            let node = match q {
                None => t.clone(),
                Some(mut q) => {
                    q.tuples = Tuples::normal(q.tuples.rest, std::mem::take(&mut q.tuples.lens));
                    Type::new(q)
                }
            };
            let r = level(&node);
            // `level` gives a node of parts for a node of parts: what it gives becomes an atom's
            // payload above, and every payload is a node of parts (the proof of sub-case (c) at
            // `Printer::force_cycles`). The one caller outside tests, zedc-types `Forms::level`,
            // gives `cut | fns`, `cut` or `set - marks`, each built by `Type::zip` or
            // `Type::minus` from nodes of parts. Checked here in every build, O(1).
            assert!(
                (r.as_ref()).is_none_or(|r| matches!(&*r.0, Node::Parts(..))),
                "`level` gave a recursive node for a node of parts"
            );
            memo.insert(t, r);
        }
        memo[self].clone()
    }

    /// Whether `level` gives back unchanged every node of the recursive node `t`'s unfolding at
    /// every depth outside functions, walked once by node number and not past a node `memo`
    /// has. When it does, each node walked is put in `memo` as kept.
    fn rec_kept(
        t: &Type,
        memo: &mut HashMap<Type, Option<Type>>,
        level: &mut impl FnMut(&Type) -> Option<Type>,
    ) -> bool {
        let (mut seen, mut walked) = (HashSet::new(), Vec::new());
        let mut stack = vec![t.clone()];
        while let Some(u) = stack.pop() {
            if !seen.insert(u.node_id()) {
                continue;
            }
            match memo.get(&u) {
                Some(Some(v)) if *v == u => continue,
                Some(_) => return false,
                None => {}
            }
            if level(&u).is_none_or(|v| v != u) {
                return false;
            }
            let p = u.p();
            stack.extend(p.atoms.names().values().map(|a| a.payload.clone()));
            for part in p.tuples.lens.values() {
                stack.extend(part.distinct_atoms().iter().flat_map(|r| r.iter().cloned()));
            }
            walked.push(u);
        }
        memo.extend(walked.into_iter().map(|u| (u.clone(), Some(u))));
        true
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
        // `l01_23_subtyping::scaling::listing_a_diagram_with_exponentially_many_paths_scales`,
        // `l01_28_staging::trick::a_finite_domain_is_split_on_the_values_passed_and_an_infinite_one_is_kept`
        // and, for `(int, 0) - (int - 0, 0)`,
        // `l01_23_subtyping::listing::the_difference_of_int_0_and_int_minus_0_0_is_one_value_not_known_finite`.
        // A complete solution would decide, for each box with an infinite component, whether
        // the type holds finitely many of its tuples, by the emptiness search with a full case
        // split over the tuple types (exponential in them, or a SAT solver), and would follow
        // atom payloads, struct fields and recursive groups into the types they hold.
        self.finite_order(false).is_some()
    }

    /// The integers of `self`, when they are a finite set of literals; `None` when `self` holds
    /// all but finitely many integers. Its users read it as the ints the type holds: the
    /// checker's exact key reads (`exact_key_read`), byte and exponent tests, and the type
    /// facet of a product cell (`zedc::store::product`).
    // Proof that the list is complete, for every way the type was made (PROOF-ints-listed-
    // complete): an int, `Value::Int` or `Value::Big`, is in a type exactly when its parts'
    // `ints` hold it ([`Type::member`], the one test [`Type::contains`] makes on a scalar), and
    // a recursive node's parts are those of its unfolding ([`Type::p`]), as here. `ints` is a
    // `Lits`: the set `values` when not `cofinite`, and its complement in the ints otherwise
    // (`Lits::contains`). So when not cofinite, the ints the type holds are `values`, each
    // listed once, and nothing outside them; no other part holds an int. What a caller then
    // concludes about a run-time value rests on the value lying in the type it reads this
    // from, the checker's typing of that value, not on this list. Test:
    // `types::tests::ints_listed_are_the_ints_the_type_holds`, on 5 000 random types made of
    // literals, `int` and other kinds by `|`, `&`, `-` and `!`: every int of a window and two
    // big ints is listed exactly when held, every listed int is held, and none is listed twice.
    // It cannot catch a recursive type (the `Type::p` step) or another way of making one, and
    // it reads `ints` as `contains` does, so it checks the reading, not `Type::member`.
    pub fn ints_listed(&self) -> Option<Vec<Value>> {
        let p = self.p();
        (!p.ints.cofinite).then(|| p.ints.values.iter().cloned().collect())
    }

    /// The integers of `self` as the set the type keeps, when they are a finite set of
    /// literals ([`Type::ints_listed`], which this is without the copy): `O(1)`, the set shared.
    pub fn ints_set(&self) -> Option<TreapSet<Value>> {
        let p = self.p();
        (!p.ints.cofinite).then(|| p.ints.values.clone())
    }

    /// The type of exactly the integers `vs`, every member a `Value::Int` or `Value::Big`:
    /// `O(1)`, the set shared, where [`Type::union_all`] of their [`Type::lit`]s joins `k`
    /// literals. It is that union: a literal of an integer is the type whose `ints` hold it
    /// alone and every other part nothing, and `|` joins part by part, so the union's `ints`
    /// are `vs` and its other parts nothing; the empty set gives [`Type::empty`], as the union
    /// of no types does. Test: `types::tests::ints_of_a_set_is_the_union_of_its_literals`.
    pub fn ints_of(vs: TreapSet<Value>) -> Type {
        assert!(
            vs.classes() & !(Value::INT_CLASS | Value::BIG_CLASS) == 0,
            "`Type::ints_of` of a set holding a value that is not an integer"
        );
        match vs.is_empty() {
            true => Type::empty(),
            false => Type::with(|p| {
                p.ints = Lits {
                    cofinite: false,
                    values: vs,
                }
            }),
        }
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
                + [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
                    .iter()
                    .map(|l| l.values.len())
                    .sum::<usize>()
                + p.atoms.names().values().filter(|a| a.bare).count();
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
        // Each type is filed once for all makers: a chain of types each holding the one before
        // in its first component is walked once, not once per maker (COMPLEXITY.md K109).
        let mut filer = Filer::default();
        let makers = types
            .into_iter()
            .zip(boxes.into_iter().zip(rows))
            .map(|(t, (boxes, rows))| Maker::new(t, boxes, rows, &mut numbers, &mut filer))
            .collect();
        Some(Values {
            makers,
            numbers,
            known: RefCell::default(),
            chains: Chains::default(),
            given: 0,
        })
    }

    /// `self` made ready for many tests of [`Type::contains`] ([`Membership`]).
    pub fn membership(&self) -> Membership {
        let p = self.p();
        let mut filer = Filer::default();
        let by_len = match p.tuples.rest {
            true => BTreeMap::new(),
            false => (p.tuples.lens.iter())
                .map(|(&len, part)| (len, RowIndex::new(len, part, &mut filer)))
                .collect(),
        };
        Membership {
            ty: self.clone(),
            by_len,
            chains: Chains::default(),
            known: HashMap::new(),
        }
    }

    /// The types `self`'s values are built from, each with its boxes and after the types in
    /// them, `self` last, when every one is known finite. One visit per type, kept in a visited
    /// set, and an explicit stack, since the nesting depth follows the input. With `merge`, each
    /// type's boxes are merged ([`merge_boxes`]) before the types in them are visited; the
    /// answer is `None` exactly when it is without, since a merged column is the union of
    /// columns each of which is visited without merging, finite exactly when they all are.
    /// The finiteness questions the boxes ask in turn ([`part_boxes`]) are answered on the
    /// same [`Finiteness`], with `self` the question in progress.
    fn finite_order(&self, merge: bool) -> Option<Vec<(Type, Vec<Row>)>> {
        let cx = Finiteness::default();
        cx.asking.borrow_mut().insert(self.clone());
        cx.stack.run(cx.order(self.clone(), merge, false))
    }

    /// Tuple types, the boxes, whose union holds every tuple of `self`, when the rest of
    /// `self` is finite and every tuple of it is in a tuple type the part names; `None`
    /// otherwise. A diagram gives its boxes as [`list_boxes`] finds them, and an expression
    /// gives them from its operands' ([`part_boxes`]), so a meet with a finite type and an
    /// exclusive or of finite types give finite boxes (LIST-xor-finite).
    fn boxes(&self) -> Option<Vec<Row>> {
        let cx = Finiteness::default();
        cx.stack.run(cx.boxes(self))
    }
}

/// The answers of [`Type::finite`] found while one question is answered: [`part_boxes`] asks
/// whether the columns of a box are finite, which reads their boxes, which may ask again, as
/// deep as the types nest. The questions are calls on a stack on the heap ([`Stack`]), run in
/// the order plain recursion would run them, so the thread's stack holds one call whatever the
/// depth (FAIL-group-oracle-order-stack-overflow-seed: plain recursion overflowed it).
///
/// Each answer is kept, so a type is asked once. A type asked while its own question is in
/// progress is answered "not known finite": its boxes reach a column equal to itself through
/// the meets that [`part_boxes`] builds, as a member of a recursive group does once unfolded
/// (`cells913` of the group oracle's cells family), and asking it again would repeat the same
/// questions without end. The answer only chooses, in a meet, between a box and the box met
/// with the join of the other operand's boxes, both of which hold that box's part of the meet,
/// so it never makes the boxes miss a tuple; and any question that reaches such a type never
/// ended before. An answer cut so is kept with the others for the rest of the one question, so
/// a type may be "not known finite" inside one question and finite asked alone; both are sound,
/// and each question's answer depends on its root alone (the stack runs the calls in the order
/// plain recursion would).
///
/// Answers that change: [`Finiteness::meet_rows`] no longer meets two columns neither known
/// finite (unless their meet has no tuple types), so a meet of two infinite types
/// whose meet is finite and holds tuples, found finite before when its unfolding ended, is now
/// "not known finite". No test of the affected groups depends on one, and no caller does
/// (PROOF-sweep-zed-kernel B1): every caller of [`Type::finite`], [`Type::values_listed`],
/// [`Type::each_value`] and [`Type::boxes`] reads false or `None` as "not known", and takes
/// the general path, never one that needs the type infinite. The callers, read 2026-11-20:
/// `zedc_stage::stage::trick` keeps the domain whole and says why; `zedc_preimage::product`
/// (the element test and the cell's facet) does not list the values; in zedc-check,
/// `check/mod.rs` (the two listings), `check/walk.rs` (the word operands, the numeric parts,
/// which keep `Ty::set(part)`, the literal repairs, which are not offered, and the remaining
/// listings) and `check/walk/fp_ops.rs` (the one value of a region) each fall back to the type
/// as a set, or to no repair; and here `firsts` reads the parts' own tuple types when the
/// boxes are `None`, and `values_listed` gives `None` with no order. So a weaker answer costs
/// only precision: a split not made, a list not printed, a repair not offered.
#[derive(Default)]
struct Finiteness<'m> {
    stack: Stack<'m>,
    /// The types whose question is in progress.
    asking: RefCell<HashSet<Type>>,
    /// The answers found.
    known: RefCell<HashMap<Type, bool>>,
}

impl<'m> Finiteness<'m> {
    /// Whether `t` is known finite ([`Type::finite`]), on a frame of its own.
    fn finite(&'m self, t: &Type) -> Deep<'m, bool> {
        if let Some(&known) = self.known.borrow().get(t) {
            return Stack::ready(known);
        }
        if !self.asking.borrow_mut().insert(t.clone()) {
            return Stack::ready(false);
        }
        let t = t.clone();
        self.stack.call(move || async move {
            let finite = self.order(t.clone(), false, true).await.is_some();
            self.asking.borrow_mut().remove(&t);
            self.known.borrow_mut().insert(t, finite);
            finite
        })
    }

    /// [`Type::finite_order`] of `root`. One visit per type, kept in a visited set, and an
    /// explicit stack, since the nesting depth follows the input. With `leaves`, for a question
    /// of [`Finiteness::finite`], which reads only whether the order exists, a type already
    /// known finite is not walked again: its own walk ended, so the types below it are finite.
    // Complexity tradeoff: without `leaves`, each nested question walked every type below it
    // again, so `n` questions nested one in the next cost order `n²` (the `nested_meets` family
    // of l01_23_subtyping); with it each walk stops at the questions answered before, and
    // the types are walked order `n` times in all. Before this item the nested questions shared
    // no answers and were asked again at each level: exponential in the depth (10 ms at depth 16,
    // 17 s at 32 for a meet of unions) and plain recursion, which overflowed the thread's stack.
    async fn order(
        &'m self,
        root: Type,
        merge: bool,
        leaves: bool,
    ) -> Option<Vec<(Type, Vec<Row>)>> {
        let mut unions = HashMap::new();
        // Complexity tradeoff (PERF-walk-allocs-by-stack): a root with no columns, such as an
        // integer domain, was walked as any other, a stack and two sets made for one type:
        // about 9 allocations a binding of the walk of `fees(d, 1)` (l01_39 `deep_let`) in a
        // heap profile grouped by call stack. Used: such a root answered at once. It is the
        // walk below with one type: a known leaf is skipped (an empty order); otherwise the
        // root is seen and opened, has no column to be open or to push, and is closed into
        // the order with its boxes.
        if leaves && self.known.borrow().get(&root) == Some(&true) {
            return Some(Vec::new());
        }
        let boxes = match merge {
            true => merge_boxes(self.boxes(&root).await?, &mut unions),
            false => self.boxes(&root).await?,
        };
        if boxes.iter().all(|r| r.is_empty()) {
            return Some(vec![(root, boxes)]);
        }
        let mut order = Vec::new();
        let mut seen: HashSet<Type> = HashSet::new();
        // The types whose walk is open: visited, and not yet in `order`. A box with an open
        // column makes the answer `None`, "not known finite" (PROOF-sweep-zed-kernel).
        // Proof that an open column is a cycle of boxes: the stack is last in, first out, and
        // a type's `Some` frame is pushed below the frames of its columns, so every frame
        // popped while that `Some` frame is on the stack was pushed while the type's boxes, or
        // the boxes of a type pushed by them, were expanded. So the type being expanded is
        // reached from each open type through a chain of boxes, and a column equal to an open
        // type closes the chain into a cycle. A walk that skipped such a column, as this one
        // did before, answered finite for an infinite type: `() | ((0, R) & (0, S))`, with
        // `R = () | (0, R)` and `S = () | (0, S) | 1`, has the box `(0, t)` of itself, holds
        // every list of zeros, and was "finite" (test
        // `types::tests::a_meet_of_two_recursive_lists_is_not_known_finite`). `None` is always
        // a sound answer here (callers read it as "not known", PROOF B1 at `Finiteness`), so a
        // finite type whose boxes form a cycle loses only precision. Cost: one insert and one
        // removal per type and one lookup per column, as the `seen` filter below already makes.
        let mut open: HashSet<Type> = HashSet::new();
        // The root, its boxes made above, expanded as the loop expands a type: a column equal
        // to the root is a cycle, and the others are pushed above it.
        if boxes.iter().flat_map(|r| r.iter()).any(|c| *c == root) {
            return None;
        }
        seen.insert(root.clone());
        open.insert(root.clone());
        let below: Vec<(Type, Option<Vec<Row>>)> = boxes
            .iter()
            .flat_map(|r| r.iter())
            .map(|c| (c.clone(), None))
            .collect();
        let mut stack: Vec<(Type, Option<Vec<Row>>)> = vec![(root, Some(boxes))];
        stack.extend(below);
        while let Some((t, done)) = stack.pop() {
            if let Some(boxes) = done {
                open.remove(&t);
                order.push((t, boxes));
                continue;
            }
            let leaf = leaves && self.known.borrow().get(&t) == Some(&true);
            if leaf || !seen.insert(t.clone()) {
                continue;
            }
            open.insert(t.clone());
            let boxes = match merge {
                true => merge_boxes(self.boxes(&t).await?, &mut unions),
                false => self.boxes(&t).await?,
            };
            if boxes
                .iter()
                .flat_map(|r| r.iter())
                .any(|c| open.contains(c))
            {
                return None;
            }
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

    /// A box holding the meet of rows `r` and `s`, for [`part_boxes`] to meet a box with the
    /// join of the other operand's boxes: [`meet_types`] column by column, except that two
    /// columns neither known finite are met only when their meet has no tuple types,
    /// and otherwise give the column of `r`, which holds their meet.
    ///
    /// Why: meeting two columns neither known finite makes a new type whose boxes meet again,
    /// and when one of them is recursive each meet unfolds it once more, a new and larger type
    /// at each step that the visited set of [`Finiteness::order`] never meets twice, so the walk
    /// never ended. In `cells913`, R1 = `((#a | #b), (#a | #b | R1)) \ ... | #b` met with a join
    /// that holds it gave `A & (A | (A | ...))`, one copy of R1's tuple type more per step, and
    /// 2240 types of 51 KB after 30 s. Such a meet is finite only when the two infinite types
    /// share finitely many values, which these rows do not decide; "not known finite" is the
    /// answer [`Type::finite`] allows when it cannot tell, as for a box read as written. A meet
    /// with no tuple types has boxes with no columns, so it unfolds nothing.
    ///
    /// Assumption, not proved: every type this makes is a meet with a known finite side or a
    /// meet without tuple types, and a meet's boxes meet the other side's columns only with
    /// joins of the finite side's box columns, which come before it in its finite order, so
    /// each chain of new types follows a chain down that order and ends. Evidence: the five seeds
    /// of FAIL-group-oracle-order-stack-overflow-seed end, and the listing and group tests pass.
    ///
    /// Split into what is proved and what is not (PROOF-sweep-zed-kernel):
    /// (a) Proved: a question on one [`Finiteness`] ends exactly when the set `U` of types
    ///     reached through boxes (the root, the columns of its boxes, theirs, and so on, the
    ///     new meets made here and by [`list_boxes`] included) is finite. Each walk of
    ///     [`Finiteness::order`] expands a type at most once (`seen`); a `finite` question is
    ///     asked at most once per type (`known`, `asking`); `meet_columns` descends by
    ///     [`only_row`], which reads a row only of a `Node::Parts` node and never unfolds a
    ///     recursive node, so each descent goes down the graph of parts, which is acyclic (a
    ///     node's components exist before the node is made, so every cycle passes through a
    ///     recursive node, where `only_row` stops), and ends; and
    ///     `part_boxes` reads each operand once per pass (its explicit stack and maps). So the
    ///     work is finite when `U` is, and a type of `U` is reached only by such a step.
    /// (b) Proved: `U` is finite when no step meets two types neither of which is `top` or
    ///     equal to the other, that is, when each path of each diagram takes one tuple type and
    ///     each meet of the parts has boxes on one side only. Then `meet_types` and this
    ///     function return one of their arguments (their first two arms), so every column in
    ///     `U` is a component of a row written in the root's diagrams, at some depth, and the
    ///     root has finitely many.
    /// (c) Not proved: the general case, where a meet makes a new type that is a meet again;
    ///     the assumption above, with its evidence, is what is relied on there. A type of `U`
    ///     met again inside its own walk now ends the walk with "not known finite" (`open` in
    ///     [`Finiteness::order`]), so a cycle of boxes no longer hides an infinite type, but a
    ///     chain of new types that never repeats is not ruled out.
    async fn meet_rows(&'m self, r: &Row, s: &Row) -> Row {
        let mut columns = Vec::with_capacity(r.len());
        for (x, y) in r.iter().zip(s) {
            columns.push(self.meet_columns(x, y).await);
        }
        Row::new(columns)
    }

    /// One column of [`Finiteness::meet_rows`]: [`meet_types`], with the leaves met only when
    /// one side is known finite or the meet has no tuple types.
    async fn meet_columns(&'m self, x: &Type, y: &Type) -> Type {
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
                    _ => {
                        let meet = &x & &y;
                        // A meet with no tuple types has boxes with no columns, so it unfolds
                        // nothing and is kept with no question asked: the scalar leaves of
                        // tuple types met column by column ask none.
                        let flat = matches!(&*meet.0, Node::Parts(p, _)
                            if p.tuples.lens.is_empty() && !p.tuples.rest);
                        let keep = flat || self.finite(&x).await || self.finite(&y).await;
                        done.push(if keep { meet } else { x });
                    }
                },
                Step::Tuple(n) => {
                    let items = done.split_off(done.len() - n);
                    done.push(Type::tuple(items));
                }
            }
        }
        done.pop().expect("the first step leaves one result")
    }

    /// [`Type::boxes`] of `t`.
    async fn boxes(&'m self, t: &Type) -> Option<Vec<Row>> {
        let Node::Parts(p, _) = &*t.0 else {
            return None;
        };
        if p.structs
            || p.morphisms.is_leaf() != Some(false)
            || p.atoms.cofinite()
            || p.tuples.rest
            || [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
                .iter()
                .any(|l| l.cofinite)
            || p.atoms.names().values().any(|a| a.payload != Type::empty())
        {
            return None;
        }
        let mut out = Vec::new();
        for (len, part) in &p.tuples.lens {
            // The tuples outside every tuple type of the part are not listed.
            if part.eval(&|_| false) {
                return None;
            }
            out.extend(part_boxes(self, part, *len).await?.iter().cloned());
        }
        Some(out)
    }
}

impl Type {
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
        self.contains_kept(v, &mut HashMap::new())
    }

    /// [`Type::contains`], with the tests kept in `known` across calls, `v`'s own among them.
    /// An id is never given twice in the process (`Items::id`), so a kept test stays true of
    /// its sequence whether or not the sequence is still held.
    fn contains_kept(&self, v: &Value, known: &mut HashMap<(Type, Id), bool>) -> bool {
        let first = match self.member(v) {
            Member::Known(b) => return b,
            Member::Tuple(ty, xs) => (ty, xs),
        };
        let key = |t: &Type, xs: &Items| (t.clone(), xs.id());
        if let Some(&b) = known.get(&key(&first.0, first.1)) {
            return b;
        }
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
            known.insert(key(&ty, xs), fits);
            if todo.is_empty() {
                return fits;
            }
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
            Value::Float32(_) => p.f32s.contains(v),
            Value::Str(_) => p.strings.contains(v),
            Value::Atom(a) => match p.atoms.names().get(&a.name) {
                None => p.atoms.cofinite(),
                Some(part) if a.is_bare() => part.bare,
                Some(part) if a.fields.is_empty() => {
                    return Member::Tuple(part.payload.clone(), a.args());
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
            name_digest: 0,
            bools: match op {
                Op::Or => a.bools | b.bools,
                Op::And => a.bools & b.bools,
            },
            ints: a.ints.zip(&b.ints, op),
            rats: a.rats.zip(&b.rats, op),
            floats: a.floats.zip(&b.floats, op),
            f32s: a.f32s.zip(&b.f32s, op),
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

    /// `self & !other`, part by part as [`Type::zip`] meets them with the parts of `!other`,
    /// but with the atoms taken by [`Atoms::minus`], which does not complement each name
    /// `other` lists. The empty type minus anything is itself, as `zip_at_once` gives it.
    /// Proof that it equals `self & &!other`: `!other` (`Not for &Type`) is the parts of
    /// `other` each complemented, and `zip` with `Op::And` meets each part of `self` with the
    /// part of `!other`, which is what each line below does (the atoms by the proof at
    /// [`Atoms::minus`]); where `zip_at_once` instead gives an operand whole (`self` is `!other`,
    /// or `!other` is the empty or the full type), that operand equals the parts met, so the
    /// type built here is equal to it, though a new node. Test
    /// `types::tests::a_difference_of_types_is_the_meet_with_the_complement`.
    fn minus(&self, other: &Type) -> Type {
        if crate::local::with(&EMPTY, |k| Arc::ptr_eq(&self.0, &k.0)) {
            return self.clone();
        }
        let (a, b) = (self.p(), other.p());
        Type::new(Parts {
            digest: 0,
            name_digest: 0,
            bools: a.bools & !b.bools & 3,
            ints: a.ints.zip(&b.ints.not(), Op::And),
            rats: a.rats.zip(&b.rats.not(), Op::And),
            floats: a.floats.zip(&b.floats.not(), Op::And),
            f32s: a.f32s.zip(&b.f32s.not(), Op::And),
            strings: a.strings.zip(&b.strings.not(), Op::And),
            atoms: a.atoms.minus(&b.atoms),
            tuples: a.tuples.zip(&b.tuples.not(), Op::And),
            structs: a.structs && !b.structs,
            morphisms: a.morphisms.zip(&b.morphisms.not(), Op::And),
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
        let is = |t: &Type, k: &'static std::thread::LocalKey<Type>| {
            crate::local::with(k, |k| Arc::ptr_eq(&t.0, &k.0))
        };
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
                && a.f32s.disjoint(&b.f32s)
                && a.strings.disjoint(&b.strings)
        } else {
            a.bools & !b.bools == 0
                && a.ints.within(&b.ints)
                && a.rats.within(&b.rats)
                && a.floats.within(&b.floats)
                && a.f32s.within(&b.f32s)
                && a.strings.within(&b.strings)
        })
    }
}

type CompoundKey = (bool, bool, u64, Vec<(usize, u64)>);
/// Each compound key with the id and the node built for it. Complexity tradeoff
/// (PERF-deep-ops-slow): the keys are flags, ids and digests the kernel drew, never a program's
/// text, so the map hashes them by [`crate::digest::Digest`] with no seed, as its doc allows;
/// SipHash-1-3 over each key showed in the profile of a deep tuple (GSX-unsolved made more
/// compound types a level), the lookup O(1) either way. SipHash: Aumasson and Bernstein 2012,
/// doi:10.1007/978-3-642-34931-7_28; the full comment is in `digest.rs`, type `FixedState`.
type CompoundTypes = crate::digest::DigestMap<Arc<CompoundKey>, (u64, Weak<Node>)>;
thread_local! {
    static COMPOUND_TYPES: RefCell<CompoundTypes> = RefCell::new(CompoundTypes::default());
    static COMPOUND_SEARCH: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The live literal sets of the thread's types, by sum ([`Type::new`], TYPE-hashcons).
    static LITS: RefCell<HashConsTable<Value>> = RefCell::new(HashConsTable::default());
}

/// Reuse is useful to the search's local graph memos; ordinary type construction
/// needs neither that table nor its key allocation. Nesting restores the caller.
struct CompoundScope(bool);

impl CompoundScope {
    fn enter() -> Self {
        Self(COMPOUND_SEARCH.with(|s| s.replace(true)))
    }
}

impl Drop for CompoundScope {
    fn drop(&mut self) {
        COMPOUND_SEARCH.with(|s| s.set(self.0));
    }
}

fn clear_compound_types() {
    COMPOUND_TYPES.with(|c| c.borrow_mut().clear());
}

impl Parts {
    /// Whether it lists finitely many booleans, numbers and strings and nothing else.
    fn finite_literals_only(&self) -> bool {
        [
            &self.ints,
            &self.rats,
            &self.floats,
            &self.f32s,
            &self.strings,
        ]
        .iter()
        .all(|l| !l.cofinite)
            && self.atoms.is_default()
            && self.tuples.is_default()
            && !self.structs
            && self.morphisms.is_leaf() == Some(false)
    }

    /// How many numbers and strings it lists.
    fn literal_count(&self) -> usize {
        [
            &self.ints,
            &self.rats,
            &self.floats,
            &self.f32s,
            &self.strings,
        ]
        .iter()
        .map(|l| l.values.len())
        .sum()
    }

    /// Adds the booleans, numbers and strings of `other`, both of
    /// [`Parts::finite_literals_only`], one literal at a time.
    fn join_literals(&mut self, other: &Parts) {
        debug_assert!(self.finite_literals_only() && other.finite_literals_only());
        self.bools |= other.bools;
        for (mine, theirs) in [
            (&mut self.ints, &other.ints),
            (&mut self.rats, &other.rats),
            (&mut self.floats, &other.floats),
            (&mut self.f32s, &other.f32s),
            (&mut self.strings, &other.strings),
        ] {
            for v in &theirs.values {
                mine.insert(v);
            }
        }
    }

    fn scalars_only(&self) -> bool {
        self.atoms.is_default()
            && self.tuples.is_default()
            && !self.structs
            && self.morphisms.is_leaf() == Some(false)
    }

    /// Whether these hold tuples only, at each length a union of literals
    /// ([`Tuples::literals_only`]).
    fn tuple_literals_only(&self) -> bool {
        !self.has_scalars()
            && self.atoms.is_default()
            && !self.structs
            && self.morphisms.is_leaf() == Some(false)
            && self.tuples.literals_only()
    }

    /// Whether it lists atoms and nothing else: no boolean, number, string, tuple, struct or
    /// morphism. Its every value is then an atom, as an atom's payload is within the tuples
    /// and structs ([`AtomPart`]).
    fn atoms_only(&self) -> bool {
        !self.has_scalars()
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
            (&self.f32s, matches!(v, Value::Float32(_))),
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

    /// Whether it holds a bare atom, `#a`, or the atoms of every name it does not list, read
    /// from the parts in O(1) ([`Atoms`] counts the names that hold their bare atom).
    fn has_bare_atoms(&self) -> bool {
        self.atoms.cofinite() || self.atoms.bare_names() > 0
    }

    /// Whether it holds a boolean, number or string, read from the parts.
    fn has_scalars(&self) -> bool {
        self.bools != 0
            || [
                &self.ints,
                &self.rats,
                &self.floats,
                &self.f32s,
                &self.strings,
            ]
            .iter()
            .any(|l: &&Lits| l.cofinite || !l.values.is_empty())
    }
}

/// A type split by universe: what [`Type::split`] gives.
pub struct Split {
    /// Its values of `bool`, `int`, `rat`, `f64`, `String` and `f32`, in that order, each
    /// `None` when it has none.
    pub bases: [Option<Type>; 6],
    /// Its atoms, `None` when it has none.
    pub atoms: Option<Type>,
    /// Its tuples, structs and morphisms, `None` when it has none.
    pub rest: Option<Type>,
}

/// Which universes a type holds values of: the parts [`Type::split`] gives, each true where
/// that gives a type, as [`Type::universes`] reads them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Universes {
    /// Whether it has values of `bool`, `int`, `rat`, `f64`, `String` and `f32`, in that order.
    pub bases: [bool; 6],
    /// Whether it has atoms.
    pub atoms: bool,
    /// Whether it has tuples, structs or morphisms.
    pub rest: bool,
}

impl Type {
    /// Its one value, when it is one boolean or one literal of `int`, `rat`, `f64`, `f32` or
    /// `String`, and nothing else: its first such value, read from the parts. A node of parts
    /// is that literal's type exactly when its parts are the literal's (`Parts::only`), which
    /// is read with no type built; a recursive node is compared with the type of the literal
    /// alone.
    pub fn scalar(&self) -> Option<Value> {
        let p = self.p();
        let first = |l: &&Lits| match l.cofinite {
            true => None,
            false => l.values.iter().next().cloned(),
        };
        let v = match p.bools {
            1 => Some(Value::Bool(false)),
            2 => Some(Value::Bool(true)),
            _ => [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
                .iter()
                .find_map(first),
        }?;
        match &*self.0 {
            Node::Parts(p, _) => p.only(&v).then_some(v),
            Node::Rec(_) => (Type::lit(&v)? == *self).then_some(v),
        }
    }

    /// A hash of the set it denotes, where its parts list booleans, numbers and strings and
    /// nothing else; None where they may list an atom, tuple, struct or morphism. Two such
    /// types that denote one set hash alike: their parts are a set of booleans and, for each
    /// base type, a finite set of literals or the complement of one (`Lits`), every other
    /// part its default (`Parts::scalars_only`), and the digest is made from those alone
    /// (`Parts::hashes`, each `Lits` by `cofinite` and the sum of its literals' hashes). Equal
    /// hashes do not prove equal sets. A recursive node is read through its unfolding. O(1)
    /// after the unfolding.
    ///
    /// Proof that a set given a digest has one form, whether written or computed
    /// (PROOF-kernel-proofdoc3a-gaps (f)). Booleans are a set of two. For `int`, `rat` and
    /// `String`, which are infinite, a finite list `L` and the complement of a finite list `C`
    /// never denote one set. For `f64` and `f32` they can, when `L` and `C` split the base:
    /// `|L| + |C| = N` for the base's `N` values. A float `Lits` is given a digest only when
    /// `2 |values| < N` (`Type::F64_VALUES`, `Type::F32_VALUES`); two forms of one set
    /// that both pass would have `|L| + |C| < N`, so at most one passes, and a set past it has
    /// no digest, the answer for a type that is not of scalars alone (its caller,
    /// `domain_key` in zedc-types, then keys no domain, and compares the function as it does
    /// any other). The cutoff costs one length read per float part (`TreapSet::len`, O(1)) and
    /// is never reached by a list that fits in memory, half of `f32`'s values being about
    /// 2^31 literals. Test: `types::tests::a_float_set_has_one_digest_however_it_is_made`.
    pub fn scalars_digest(&self) -> Option<u64> {
        let p = self.p();
        let one_form = |l: &Lits, n: u128| 2 * (l.values.len() as u128) < n;
        (p.scalars_only()
            && one_form(&p.floats, Type::F64_VALUES)
            && one_form(&p.f32s, Type::F32_VALUES))
        .then_some(p.digest)
    }

    /// The number of `f64` values: the `2^64` bit patterns less the `2 (2^52 - 1)` NaNs, which
    /// [`crate::value::F64::new`] makes one value, plus that one NaN; `-0.0` and `0.0` differ.
    /// Odd, so no float list holds exactly half. Test:
    /// `a_float_set_has_one_digest_however_it_is_made`
    /// counts the values among the bit patterns of `f32`'s all-ones exponent, the one case
    /// where bit patterns and values differ, by the same rule.
    const F64_VALUES: u128 = (1 << 64) - (1 << 53) + 3;

    /// The number of `f32` values, as [`Type::F64_VALUES`] with `2^32` patterns and
    /// `2 (2^23 - 1)` NaNs.
    const F32_VALUES: u128 = (1 << 32) - (1 << 24) + 3;

    /// The greatest byte length of the text (`lit_text`) of a literal its numbers and
    /// strings list, whether as a set or as the complement of one; 0 where they list none.
    /// The booleans are not counted: they make at most four sets, whatever the length.
    ///
    /// What relies on it: the fold rounds of `zedc-check` (`fold_dir_end`) bound the scalar
    /// part of a leaf inside a function by this length (`zedc_types::forms`, `leaf_node`). The
    /// argument: a number or string part is a `cofinite` flag and a finite set of literals
    /// (`Lits`; `Parts` holds no interval), and each text names one value (a `rat` in
    /// canonical form, a big integer as digits or powers that evaluate to it, an `f64` or
    /// `f32` as its shortest round-trip text, a string quoted), so for a bound `W` on this
    /// length finitely many values print in at most `W` bytes and finitely many such parts
    /// exist. A union of literals such as `0 | 1000` is as wide as `1000`, so a part that
    /// gathers the literals of a finite set does not look wider each round
    /// (FAIL-fold-rotating-tuple-rounds, Codex seat, round 2, R2-3).
    // Complexity tradeoff: linear in the number of literals listed, read once per leaf per
    // round; the naive measure, the length of the printed union, is also linear but grows
    // with the number of literals, so a set of k literals of bounded length looked k times
    // wider.
    pub fn scalar_literal_width(&self) -> u64 {
        let p = self.p();
        [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
            .into_iter()
            .flat_map(|lits| lits.values.iter())
            .map(|v| lit_text(v).len() as u64)
            .max()
            .unwrap_or(0)
    }

    /// Whether its values of the base type `base`, in the order of [`Split::bases`] (`bool`,
    /// `int`, `rat`, `f64`, `String`, `f32`), are one or more, each listed: what
    /// `(self & base type).values_listed()` giving a nonempty list says, read from the parts
    /// in O(1) with no type met and no value listed. The meet keeps the base's part of
    /// `self` alone, `Lits` or the booleans, and such a type is listed exactly when that part
    /// is not `cofinite`; the booleans are always a list.
    ///
    /// Complexity tradeoff (CHECK-literal-union-cost): naive version, the meet and the list,
    /// O(k) for k literals of the base, made for each numeric base at each argument of each
    /// call the checker reads at a carrier, so a call site of a callee that lists k literals,
    /// read in each of k arms, cost O(k²). Used: the parts read, O(1). Test:
    /// `types::tests::lists_values_of_agrees_with_listing_the_meet`.
    pub fn lists_values_of(&self, base: usize) -> bool {
        let p = self.p();
        let l = match base {
            0 => return p.bools != 0,
            1 => &p.ints,
            2 => &p.rats,
            3 => &p.floats,
            4 => &p.strings,
            5 => &p.f32s,
            _ => return false,
        };
        !l.cofinite && !l.values.is_empty()
    }

    /// Whether it holds values of the base type `base` (order as in [`Type::lists_values_of`])
    /// that are not a list: what `(self & base type)` being nonempty with no
    /// `values_listed()` says, read from the parts in O(1). That is the base's `Lits` being
    /// `cofinite`, the complement of finitely many values in an infinite set, or one too large
    /// to list; the booleans are always a list.
    ///
    /// Complexity tradeoff (CHECK-literal-union-cost): naive version, the meet, its emptiness
    /// and the list, O(k) for k literals, made for each numeric carrier of each argument the
    /// checker splits (`whole_carriers` in zedc-check); used: the flag read, O(1). Test:
    /// `types::tests::lists_values_of_agrees_with_listing_the_meet`.
    pub fn holds_unlisted_values_of(&self, base: usize) -> bool {
        let p = self.p();
        match base {
            1 => p.ints.cofinite,
            2 => p.rats.cofinite,
            3 => p.floats.cofinite,
            4 => p.strings.cofinite,
            5 => p.f32s.cofinite,
            _ => false,
        }
    }

    /// Whether it may hold an atom, read from its parts: false only when it holds none.
    pub fn may_hold_atoms(&self) -> bool {
        !self.p().atoms.is_default()
    }

    /// Whether its parts list atoms and nothing else, so that it is within every atom; read
    /// from the parts in O(1). False for a recursive node and for parts that list another kind,
    /// which may still hold no value of it: ask [`Type::subtype`] then.
    pub fn atoms_only(&self) -> bool {
        matches!(&*self.0, Node::Parts(p, _) if p.atoms_only())
    }

    /// Whether its parts list finitely many booleans, numbers and strings and nothing else; read
    /// in O(1). False for a recursive node.
    fn finite_literals_only(&self) -> bool {
        matches!(&*self.0, Node::Parts(p, _) if p.finite_literals_only())
    }

    /// Whether its parts hold tuples only, at each length a union of literals
    /// ([`Tuples::literals_only`]); read in O(1). False for a recursive node.
    fn tuple_literals_only(&self) -> bool {
        matches!(&*self.0, Node::Parts(p, _) if p.tuple_literals_only())
    }

    /// Whether its parts hold no tuple: their tuples are `Tuples::default()`; read in O(1).
    /// False for a recursive node.
    fn holds_no_tuple(&self) -> bool {
        matches!(&*self.0, Node::Parts(p, _) if p.tuples.is_default())
    }

    /// The names of its atoms, each with whether it holds the bare atom `#name`, read from its
    /// parts in name order; `None` when it holds the atoms of every name it does not list. A
    /// listed name may hold no value, when its payload type is empty but not built as empty. A
    /// recursive node keeps its unfolding's names, which hold no type, so they outlive the
    /// unfolding (`rec::unfold::end_unit`).
    pub fn atom_names(&self) -> Option<impl Iterator<Item = (&str, bool)>> {
        let (map, list) = match &*self.0 {
            Node::Parts(p, _) => match p.atoms.cofinite() {
                true => return None,
                false => (Some(p.atoms.names().iter()), None),
            },
            Node::Rec(r) => {
                let names = r.names.get_or_init(|| {
                    let p = self.p();
                    let names = p.atoms.names().iter();
                    (!p.atoms.cofinite()).then(|| names.map(|(n, a)| (n.clone(), a.bare)).collect())
                });
                (None, Some(names.as_deref()?.iter()))
            }
        };
        let map = map.into_iter().flatten().map(|(n, a)| (&**n, a.bare));
        Some(map.chain(list.into_iter().flatten().map(|(n, b)| (&**n, *b))))
    }

    /// The name of its one atom and whether it is bare, when it is `Type::atom(name)` or
    /// `Type::atom_with(name, &Type::top())` and nothing else. A node of parts is read from
    /// its parts, as types of parts are equal exactly when their parts are; a recursive node
    /// is compared with the atom's type.
    pub fn one_atom(&self) -> Option<(&str, bool)> {
        // Complexity tradeoff (PERF-deep-ops-slow): naive, build the atom's type and compare
        // it with `self`, about 3k instructions for each component of every row the checker
        // makes (MSG-article-atom-value, 608b01025); here O(1) reads of the parts and one
        // comparison of the payload with a type made once.
        let mut names = self.atom_names()?;
        let (name, bare) = names.next()?;
        if names.next().is_some() {
            return None;
        }
        let one = match &*self.0 {
            Node::Parts(p, _) => {
                let payload = match bare {
                    true => Type::empty(),
                    false => Type::payloads(),
                };
                p.atoms
                    .names()
                    .get_min()
                    .is_some_and(|(_, a)| a.payload == payload)
                    && p.atoms_only()
            }
            Node::Rec(_) => match bare {
                true => *self == Type::atom(name),
                false => *self == Type::atom_with(name, &Type::top()),
            },
        };
        one.then_some((name, bare))
    }

    /// `self` split by the places its members take in a union ([`mod@order`], DESIGN.md
    /// sec:diagnostics), for a printer that writes members of its own among them: the checker's
    /// type, whose type variables, tuple shapes, functions and atoms with known payloads stand
    /// between these parts. `cuts` are names in ascending order, where the atoms are cut: the
    /// atoms of [`PrintGroups::atoms`] at `i` have names after `cuts[i - 1]` and up to `cuts[i]`,
    /// so that an atom another printer writes with the name `cuts[i]` follows them. `None` when
    /// `self` prints as one text whatever stands beside it: a recursive type, by its name, and a
    /// type of every atom, tuple and struct, `_` or `_ \ c`. Linear in its parts, with
    /// O(log a) for each of its a atom names.
    pub fn print_groups(&self, cuts: &[&str]) -> Option<PrintGroups> {
        let Node::Parts(p, _) = &*self.0 else {
            return None;
        };
        if p.atoms.cofinite() && p.tuples.rest && p.structs {
            return None;
        }
        let low = Type::with(|q| {
            q.bools = p.bools;
            q.ints = p.ints.clone();
            q.rats = p.rats.clone();
            q.floats = p.floats.clone();
            q.f32s = p.f32s.clone();
            if !p.strings.cofinite {
                q.strings = p.strings.clone();
            }
        });
        let string = match p.strings.cofinite {
            true => Type::with(|q| q.strings = p.strings.clone()),
            false => Type::empty(),
        };
        let tuples = Type::with(|q| {
            q.tuples = p.tuples.clone();
            q.structs = p.structs;
        });
        let morphisms = Type::with(|q| q.morphisms = p.morphisms.clone());
        let mut buckets = vec![Atoms::default(); cuts.len() + 1];
        match p.atoms.cofinite() {
            true => buckets[0] = p.atoms.clone(),
            false => {
                for (name, part) in p.atoms.names().iter() {
                    // `cuts` ascend, so `c < name` holds on a prefix of them and `i` is its
                    // length: `cuts[i - 1] < name <= cuts[i]`, the bucket the doc gives. A binary
                    // search, O(log c) for c cuts, beside the O(log a) of `set`.
                    let i = cuts.partition_point(|c| *c < &**name);
                    buckets[i].set(name, part.clone());
                }
            }
        }
        let atoms = buckets
            .into_iter()
            .map(|a| Type::with(|q| q.atoms = a))
            .collect();
        Some(PrintGroups {
            low,
            string,
            tuples,
            morphisms,
            atoms,
        })
    }
}

impl Lits {
    /// Whether no literal is in both sets.
    // Complexity tradeoff (COMPLEXITY.md F113): the naive test walks the first set whatever the
    // sizes, `O(s log l)` for its `s` values; a set of `n` literals tested against a cofinite
    // set that leaves out none, as `0 | 1 | ... | n` within `int` in each link of a chain of
    // `n` tuple `min`s, costs `n` each and `n^2` for the chain. Used: the treap's join-based
    // intersection and difference, `O(s log(l/s + 1))` for `s <= l`, `O(1)` against an empty
    // set, and only the unshared nodes visited (module `crate::treap_set`).
    fn disjoint(&self, other: &Lits) -> bool {
        let (a, b) = (&self.values, &other.values);
        match (self.cofinite, other.cofinite) {
            (false, false) => a.is_disjoint(b),
            (false, true) => a.is_subset(b),
            (true, false) => b.is_subset(a),
            (true, true) => false,
        }
    }

    /// Whether every literal of `self` is in `other`.
    fn within(&self, other: &Lits) -> bool {
        let (a, b) = (&self.values, &other.values);
        match (self.cofinite, other.cofinite) {
            (false, false) => a.is_subset(b),
            (false, true) => a.is_disjoint(b),
            (true, false) => false,
            (true, true) => b.is_subset(a),
        }
    }

    fn contains(&self, v: &Value) -> bool {
        self.values.contains(v) != self.cofinite
    }

    fn insert(&mut self, v: &Value) {
        self.values.insert(v.clone());
    }

    /// The wrapping sum of the literals' hashes ([`scalar`]), kept at each node, `O(1)`.
    fn sum(&self) -> u64 {
        self.values.sum()
    }

    /// The sets combined by `op`, by the treap's join-based union, intersection and difference
    /// (module `crate::treap_set`): `O(s log(l/s + 1))` expected for the smaller set's `s`
    /// literals and the larger's `l`, and only the nodes the two do not share visited, so two
    /// sets made from one set, as `u - 1` and `u - 3` are made from `u`, combine in about the
    /// paths that differ, and a result equal to an operand is that operand, so a chain of
    /// such unions stays cheap (LIST-box-overlap).
    // Complexity tradeoff (COMPLEXITY.md K69): the naive union walks the smaller set and inserts
    // each literal, `O(s log l)`, quadratic for a chain of `n` unions of sets made from one set
    // of `n` literals; `imbl`'s diff, used before, skipped shared nodes but still inserted one
    // literal at a time. Used: the treap's recursion, which stops at shared subtrees.
    fn zip(&self, other: &Lits, op: Op) -> Lits {
        let (a, b) = (&self.values, &other.values);
        let (cofinite, values) = match (op, self.cofinite, other.cofinite) {
            (Op::Or, false, false) => (false, a.union(b)),
            (Op::Or, false, true) => (true, b.difference(a)),
            (Op::Or, true, false) => (true, a.difference(b)),
            (Op::Or, true, true) => (true, a.intersection(b)),
            (Op::And, false, false) => (false, a.intersection(b)),
            (Op::And, false, true) => (false, a.difference(b)),
            (Op::And, true, false) => (false, b.difference(a)),
            (Op::And, true, true) => (true, a.union(b)),
        };
        Lits { cofinite, values }
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

    /// Whether it holds no length it does not list and, at each length listed, a union of
    /// literals ([`Part::is_union_of_literals`]), in O(1) a length.
    fn literals_only(&self) -> bool {
        !self.rest && self.lens.values().all(Part::is_union_of_literals)
    }

    /// The union of `ts`, each [`Tuples::literals_only`], made at once at each length
    /// ([`Part::union_of_literals`]); `None` when two take and refuse one tuple type.
    fn union_of_literals<'t>(ts: impl Iterator<Item = &'t Tuples>) -> Option<Tuples> {
        let mut at: BTreeMap<usize, Vec<&Part<Row>>> = BTreeMap::new();
        for t in ts {
            for (n, p) in &t.lens {
                at.entry(*n).or_default().push(p);
            }
        }
        let lens = at
            .into_iter()
            .map(|(n, ps)| Some((n, Part::union_of_literals(&ps)?)))
            .collect::<Option<_>>()?;
        Some(Tuples::normal(false, lens))
    }

    fn get(&self, len: usize) -> Part<Row> {
        match self.lens.get(&len) {
            Some(b) => b.clone(),
            None => Part::leaf(self.rest),
        }
    }

    /// Whether the meet of `ts` may hold a tuple, read from their lengths with nothing built:
    /// each holds the tuples of every length it does not list, or some length is held by each,
    /// its part not the empty leaf. The meet of the parts at one length is empty by form alone
    /// when one is the complement of another, which this does not see, so it may answer yes
    /// where the meet holds no tuple, never no where it holds one. The lengths tried are those
    /// of a part that holds no unlisted length, the one listing fewest, O(l·m log l) for `m`
    /// parts each listing at most `l` lengths, no more than building the meet.
    fn may_meet(ts: &[&Tuples]) -> bool {
        match ts.iter().filter(|t| !t.rest).min_by_key(|t| t.lens.len()) {
            None => true,
            Some(fewest) => fewest.lens.keys().any(|n| {
                ts.iter().all(|t| match t.lens.get(n) {
                    Some(b) => b.is_leaf() != Some(false),
                    None => t.rest,
                })
            }),
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
            name_digest: 0,
            bools: !p.bools & 3,
            ints: p.ints.not(),
            rats: p.rats.not(),
            floats: p.floats.not(),
            f32s: p.f32s.not(),
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
        self.minus(other)
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

/// Whether the try under way on this thread has found every text it read so far, so that what it
/// makes is kept and not thrown away ([`Type::rope`]); always so outside the making of a text.
fn showing_complete() -> bool {
    SHOWING.with_borrow(|s| s.as_ref().is_none_or(|s| s.missing.is_empty()))
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
            Node::Parts(_, shown) => &shown.text,
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
            ("f32", &p.f32s),
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
        if p.atoms.cofinite() {
            let except: Vec<Rope> = p
                .atoms
                .names()
                .iter()
                .flat_map(|(n, part)| atom(n, &part.not()))
                .collect();
            match except.is_empty() {
                true => items.push(rope!["#_"]),
                false => items.push(Rope::listed("(\\ #_", except)),
            }
        } else {
            items.extend(p.atoms.names().iter().flat_map(|(n, part)| atom(n, part)));
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

fn spaced(vs: &TreapSet<Value>) -> String {
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
    /// The membership tests of the values made in the types of rows, kept for the whole
    /// listing ([`Type::contains_kept`]). A value of depth `k` tested in a type of depth `k`
    /// reads the tests of its components kept from the level below, so a row's test of a value
    /// costs its length, not its depth.
    // Complexity tradeoff (PERF-list-nested-meets): a test per check, kept for that check alone,
    // walked each value to its bottom, O(k) for a value of depth k; `n` nested meets list `k`
    // values at each depth `k`, each tested so, O(n³) in all for the O(n²) values listed. Kept
    // for the listing, a test of a type and a sequence is made once: O(1) amortized per row
    // and component, O(n²) here. Cost: one entry per type and sequence tested, memory of the
    // order of the tests made.
    known: RefCell<HashMap<(Type, Id), bool>>,
    /// The kinds chains of the tuples the makers' indexes read, one table for all of them
    /// ([`Chains`]).
    chains: Chains,
    /// How many values of the listed type have been given.
    given: usize,
}

/// One type tested for many values ([`Type::membership`]): [`Membership::contains`] answers
/// as [`Type::contains`] does.
// Complexity tradeoff (COMPLEXITY.md F124, FAIL-print-two-variables-one-name): naive version,
// `Type::contains` for each value, which evaluates the part of the value's length over all its
// `r` rows, O(r) a test, so `n` values against a union of `n` tuple types cost O(n²). Used:
// the type's tuple parts filed once by the values their rows may hold ([`RowIndex`], as
// [`Values`] files them), O(r log r), and a tuple of plain values ([`makeable`]) tested on the
// rows with a key of it and on the kinds of a tuple with none, the latter decided once per
// class of tuple and kept: about the rows it may be in times `log r` a test. Given up: a value
// that is not a tuple of plain values, or a type that holds tuples of every length, is tested
// the naive way; the tests of components are kept for the life of the `Membership`, memory of
// the order of the tests made.
pub struct Membership {
    ty: Type,
    by_len: BTreeMap<usize, RowIndex>,
    chains: Chains,
    known: HashMap<(Type, Id), bool>,
}

impl Membership {
    /// Whether `v` is in the type: [`Type::contains`].
    pub fn contains(&mut self, v: &Value) -> bool {
        let Membership {
            ty,
            by_len,
            chains,
            known,
        } = self;
        if let Value::Tuple(items) = v
            && makeable(v)
            && let Some(index) = by_len.get_mut(&items.len())
        {
            let xs: Vec<Value> = items.as_slice().to_vec();
            let cell = RefCell::new(std::mem::take(known));
            let fits = |r: &Row| {
                (r.iter().zip(&xs)).all(|(t, x)| t.contains_kept(x, &mut cell.borrow_mut()))
            };
            let holds = index.holds_in(&xs, chains, fits);
            *known = cell.into_inner();
            return holds;
        }
        ty.contains_kept(v, known)
    }
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

/// Where a [`Maker`] is in its box. A step that waits for a component's value keeps how far
/// its scan of the components got, and the step after that value is made resumes there
/// ([`Maker::step`]).
enum At {
    /// Before the box: the components before the first `k` are known to have a value.
    Start(usize),
    /// At a position, one per component, whose values are all made.
    Tuple(Vec<usize>),
    /// Past a position, before moving to the next one: the components from the `k`-th on are
    /// known to have no value after theirs in the position.
    Past(Vec<usize>, usize),
}

/// A value a maker waits for: the maker and the position.
type Need = (usize, usize);

/// The one row of `t` when `t` is the tuple type of that row and nothing else: `t` equals
/// `Type::tuple(row)` by contents. Read from the parts, field by field as [`Type::with`] and
/// [`Tuples::literal`] fill them, in O(1) and O(`L`) for the row's `L` components.
// Complexity tradeoff: the naive test builds `Type::tuple(row)` and compares it with `t`. The
// row it builds is a live row, found in the table by comparing contents, and the comparison of
// the two types reads their parts again; where a column is a large literal set made apart
// from the live row's, each reads the set (`Lits` skips the shared nodes, O(log n) for a set
// of `n` made from one set): `only_row` was 63% of `meet_types` in
// `listing_each_row_met_first_scales`, 9.154 times the instructions at 8n, now 8.94
// (COMPLEXITY.md PERF-listing-each-row-met-first). Given up: nothing; the reads are the
// fields `Type::with` fills. A recursive node is never equal to a type of parts (`types`
// sorts them apart), so it has no row here either.
fn only_row(t: &Type) -> Option<Row> {
    let Node::Parts(p, _) = &*t.0 else {
        return None;
    };
    let bare = p.bools == 0
        && [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
            .iter()
            .all(|l| !l.cofinite && l.values.is_empty())
        && p.atoms.is_default()
        && !p.tuples.rest
        && !p.structs
        && p.morphisms.is_leaf() == Some(false);
    let mut lens = p.tuples.lens.iter();
    let (true, Some((&len, part)), None) = (bare, lens.next(), lens.next()) else {
        return None;
    };
    let row = part.literal_atom()?;
    // `Type::tuple` makes the empty type of a row with a component that lists nothing.
    (row.len() == len && !row.iter().any(Type::lists_nothing)).then(|| row.clone())
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
    let hash = |j: usize, t: &Type| mix(j as u64, t.name_digest());
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
/// meet of those taken on the one path to it (a list's nodes form one chain, [`Bdd::reaching`]),
/// one pass over the nodes. A node
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
async fn part_boxes<'m>(
    cx: &'m Finiteness<'m>,
    part: &Part<Row>,
    len: usize,
) -> Option<OrdSet<Row>> {
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
                                    let finite = match bounded.get(r) {
                                        Some(&finite) => finite,
                                        None => {
                                            // Column by column, up to the first not known
                                            // finite, as `Iterator::all` reads them.
                                            let mut finite = true;
                                            for c in r.iter() {
                                                if !cx.finite(c).await {
                                                    finite = false;
                                                    break;
                                                }
                                            }
                                            bounded.insert(r.clone(), finite);
                                            finite
                                        }
                                    };
                                    if finite {
                                        boxes.insert(r.clone());
                                    } else {
                                        let j = join.get_or_insert_with(|| {
                                            join_of(many, &found, &mut joined, len)
                                        });
                                        boxes.insert(cx.meet_rows(r, j).await);
                                    }
                                }
                                (boxes, Made::Meet(few, many))
                            }
                            (Some(k), None) | (None, Some(k)) => {
                                (found[&k].boxes.clone(), Made::Same(k))
                            }
                            // The second pass reads only operands the first found to have boxes,
                            // and the first gives an `|` or `&` boxes only when one operand has
                            // them; each operand read is read before its `Combine`, popped later.
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
    for lits in [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings] {
        made.extend(lits.values.iter().cloned());
    }
    made.extend(
        p.atoms
            .names()
            .iter()
            .filter(|(_, a)| a.bare)
            .map(|(name, _)| Value::atom(name)),
    );
    made
}

/// What a column's type names of the values it may hold, at any depth of first components: a
/// value's component at depth 0 is the value, and at depth `d + 1` the first component of its
/// component at depth `d`; with [`Reading::Payloads`], the first component of an atom with a
/// tuple payload is the first of its arguments, as if the atom were the tuple of them.
#[derive(Clone)]
struct Filed {
    /// The scalars and bare atoms the types at some depth list, and the empty tuple where they
    /// hold it, sorted and distinct: a value none of whose components is a key is in the type
    /// only as its kinds decide ([`kind_status`]). A type whose keys are all those of one type
    /// below it shares that type's set ([`Filer`]).
    keys: Rc<Vec<Value>>,
    /// Whether every value of the type has a component that is a key. Read by tuple types or
    /// boxes, this holds of the plain values only ([`makeable`]), which have no atom with a
    /// payload; read with [`Reading::Payloads`], of every value with a key (`Columns` in
    /// `empty.rs`).
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

/// How [`Filer::file`] reads the types below a column type.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reading {
    /// The first columns of its tuple types ([`firsts`]).
    Tuples,
    /// The first columns of its boxes, when they hold all its tuples ([`firsts`]).
    Boxes,
    /// The first columns of its tuple types and the payload types of its atom names, for the
    /// emptiness search, whose values include atoms with payloads (`Columns` in `empty.rs`): a
    /// value's key is then read along first components and atoms' payloads alike, the payload
    /// being a tuple of the atom's arguments.
    Payloads,
}

/// The keys of column types ([`Filed`]) for one [`Type::each_value`] call, each type filed
/// once for the whole call, by each way of reading the types below it ([`Reading`]). A key is
/// not tied to its depth: a component equal to a key at another depth only makes its tuple
/// type read.
/// A node in [`Filer`]'s key-filing DAG: either a [`Type`] or a shared persistent
/// [`atoms::PayloadNode`] whose keys are the union of its subtree's payload types' keys.
#[derive(Clone)]
enum FileNode {
    Type(Type),
    Payloads(Arc<atoms::PayloadNode>),
}

impl PartialEq for FileNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (FileNode::Type(a), FileNode::Type(b)) => a == b,
            (FileNode::Payloads(a), FileNode::Payloads(b)) => a.id() == b.id(),
            _ => false,
        }
    }
}

impl Eq for FileNode {}

impl std::hash::Hash for FileNode {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            FileNode::Type(t) => {
                0u8.hash(state);
                t.hash(state);
            }
            FileNode::Payloads(n) => {
                1u8.hash(state);
                n.id().hash(state);
            }
        }
    }
}

#[derive(Default)]
struct Filer {
    /// Per way of reading ([`Reading`], in order), the types filed.
    filed: [HashMap<Type, Filed>; 3],
    /// Per way of reading, the shared persistent [`atoms::PayloadNode`]s filed (used under
    /// [`Reading::Payloads`]), so `n` prefix unions sharing a payload tree are filed in
    /// `O(n log n)` instead of `Theta(n^2 log n)`.
    filed_payloads: [crate::digest::DigestMap<u64, Filed>; 3],
}

/// A node that [`Filer::file`] is filing.
struct Visit {
    node: FileNode,
    /// Its own keys: its scalars, bare atoms and empty tuple, unsorted.
    keys: Vec<Value>,
    /// Whether every value of the node has its own key or a first component in a first column.
    listed: bool,
    /// Its first columns / payload children not yet read.
    firsts: Vec<FileNode>,
    /// The keys of the children filed before it was done, each read once.
    below: Vec<Filed>,
}

impl Visit {
    /// The node `node`, with its own keys and children, and with [`Reading::Payloads`] the shared
    /// persistent [`atoms::PayloadNode`] root of its payload-bearing atom names.
    fn new(node: FileNode, reading: Reading) -> Visit {
        let (mut keys, mut listed, mut next) = (Vec::new(), true, Vec::new());
        match &node {
            FileNode::Type(ty) => {
                let p = ty.p();
                for b in [false, true] {
                    if p.bools & (1 << u8::from(b)) != 0 {
                        keys.push(Value::Bool(b));
                    }
                }
                for lits in [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings] {
                    keys.extend(lits.values.iter().cloned());
                    listed &= !lits.cofinite;
                }
                // A name listed is an exception to the names not listed. Finite, the exceptions
                // are the bare names, read in name order from their index (`Atoms::bare`) in
                // O(b), where a scan of `names()` read every name.
                let atoms = &p.atoms;
                if !atoms.cofinite() {
                    keys.extend(atoms.bare().iter().map(|name| Value::atom(name)));
                } else {
                    keys.extend(
                        atoms
                            .names()
                            .iter()
                            .filter(|(_, a)| a.bare != atoms.cofinite())
                            .map(|(name, _)| Value::atom(name)),
                    );
                }
                listed &= !atoms.cofinite();
                // An atom with a tuple payload is in the type when its name is listed and the
                // tuple of its arguments is in the name's payload type, so its key is one of that
                // type's. Stepping through the persistent `PayloadNode` tree files each shared
                // node once across all prefix unions (`O(n log n)` instead of `Theta(n^2 log n)`).
                if reading == Reading::Payloads
                    && let Some(pr) = atoms.payload_dag()
                {
                    next.push(FileNode::Payloads(pr.clone()));
                }
                let by_boxes = reading == Reading::Boxes;
                listed &= firsts(ty, by_boxes, &mut keys, |c| {
                    next.push(FileNode::Type(c.clone()));
                });
            }
            FileNode::Payloads(u) => {
                next.push(FileNode::Type(u.payload().clone()));
                if let Some(l) = u.left() {
                    next.push(FileNode::Payloads(l.clone()));
                }
                if let Some(r) = u.right() {
                    next.push(FileNode::Payloads(r.clone()));
                }
            }
        }
        Visit {
            node,
            keys,
            listed,
            firsts: next,
            below: Vec::new(),
        }
    }
}

impl Filer {
    /// The keys of the column type `t`: those of every type it reaches through first columns
    /// ([`firsts`]). The types are walked depth first, and the types that reach each other, as
    /// a type recursive in its first component does itself, are filed together when the walk
    /// leaves the first of them (Tarjan's strongly connected components, [`zed_graph::Search`];
    /// Tarjan 1972, doi:10.1137/0201010, full comment in zed-graph `lib.rs`, fn `tarjan`),
    /// each with the keys of all of them and of the types below them, which were filed before.
    // Complexity tradeoff: the naive form, one walk per column with a visited set that lives
    // for the walk, read every type the column reaches again for each column, O(n²) for a
    // chain of n types each holding the one before in its first component, as the makers of
    // `t_i = (t_{i-1}, t_{i-1})` file `t_{i-1}`, …, `t_0` for each i (COMPLEXITY.md K109). Here
    // each type and shared `PayloadNode` is walked and filed once per `each_value` call and way
    // of reading, O(T + E) for the T nodes and E edges reached, plus the keys copied: a node
    // whose keys are those of one set below it, as each type of such a chain or each prefix union
    // sharing one payload, shares that set, and only a node with keys of its own beside a set
    // below, or two distinct sets below, merges them, in O(k log k) for the k keys it reads; a
    // row reading the type copies those k keys into its index anyway ([`Keyed::add`]). The cost
    // is a map of every node filed, each with a shared set, held until the makers are built. The
    // nodes are numbered as the walk meets them (`FileWalk::numbers`), since the column types
    // have no numbers of their own; the search is the workspace's one Tarjan search, which takes
    // nodes numbered as met (GRAPH-lazy-tarjan), in place of a copy of it here, at the same
    // O(T + E).
    fn file(&mut self, t: &Type, reading: Reading) -> Filed {
        let idx = reading as usize;
        let filed = &mut self.filed[idx];
        let filed_payloads = &mut self.filed_payloads[idx];
        if let Some(f) = filed.get(t) {
            return f.clone();
        }
        let start = FileNode::Type(t.clone());
        let mut walk = FileWalk {
            filed,
            filed_payloads,
            reading,
            numbers: HashMap::from([(start.clone(), 0)]),
            visits: vec![Visit::new(start, reading)],
        };
        zed_graph::Search::new().run(&mut walk, [0]);
        walk.filed[t].clone()
    }
}

/// The walk of [`Filer::file`] over the types and shared [`atoms::PayloadNode`]s below a column
/// type, read one way.
struct FileWalk<'f> {
    /// The types filed, by this walk and earlier ones.
    filed: &'f mut HashMap<Type, Filed>,
    /// The shared `PayloadNode`s filed, by this walk and earlier ones.
    filed_payloads: &'f mut crate::digest::DigestMap<u64, Filed>,
    reading: Reading,
    /// Each node of this walk by its number, the position of its visit.
    numbers: HashMap<FileNode, usize>,
    visits: Vec<Visit>,
}

impl FileWalk<'_> {
    fn get_filed(&self, c: &FileNode) -> Option<&Filed> {
        match c {
            FileNode::Type(t) => self.filed.get(t),
            FileNode::Payloads(u) => self.filed_payloads.get(&u.id()),
        }
    }
}

impl zed_graph::Walk for FileWalk<'_> {
    /// A visit's children not yet read are kept in the visit.
    type At = ();

    /// The next child of node `v` not yet filed; a filed one adds its keys to `v`'s.
    fn next(&mut self, v: usize, _: &mut ()) -> Option<usize> {
        while let Some(c) = self.visits[v].firsts.pop() {
            if let Some(f) = self.get_filed(&c).cloned() {
                self.visits[v].below.push(f);
            } else if let Some(&w) = self.numbers.get(&c) {
                // Walked and not yet filed: `c` reaches `v`, and is filed with it.
                return Some(w);
            } else {
                let w = self.visits.len();
                self.numbers.insert(c.clone(), w);
                self.visits.push(Visit::new(c, self.reading));
                return Some(w);
            }
        }
        None
    }

    /// Files the nodes that reach each other with the keys of all of them and of the nodes
    /// below them, and adds those keys to the node the walk reached them from.
    fn found(&mut self, members: &mut [usize], from: Option<usize>) {
        let (mut keys, mut listed, mut below) = (Vec::new(), true, Vec::new());
        for &w in &*members {
            let visit = &mut self.visits[w];
            keys.append(&mut visit.keys);
            listed &= visit.listed;
            below.append(&mut visit.below);
        }
        let f = merged(keys, listed, below);
        for &w in &*members {
            match &self.visits[w].node {
                FileNode::Type(ty) => {
                    self.filed.insert(ty.clone(), f.clone());
                }
                FileNode::Payloads(u) => {
                    self.filed_payloads.insert(u.id(), f.clone());
                }
            }
        }
        if let Some(u) = from {
            self.visits[u].below.push(f);
        }
    }
}

/// The keys of types that reach each other, from their own `keys`, unsorted, and the keys of
/// the types `below` them. A set below is read once however many of them hold it, and is
/// shared where it is the only one and the types have no keys of their own.
fn merged(mut keys: Vec<Value>, listed: bool, below: Vec<Filed>) -> Filed {
    let listed = listed && below.iter().all(|f| f.listed);
    // The distinct sets below, by identity: a set shared by two types is one allocation.
    let mut seen: HashSet<*const Vec<Value>> = HashSet::new();
    let sets: Vec<&Rc<Vec<Value>>> = below
        .iter()
        .map(|f| &f.keys)
        .filter(|s| !s.is_empty() && seen.insert(Rc::as_ptr(s)))
        .collect();
    let keys = match sets[..] {
        [] if keys.is_empty() => Rc::new(Vec::new()),
        [set] if keys.is_empty() => Rc::clone(set),
        // Complexity tradeoff (DRY-sorted-structures, D1): the own keys sorted, then they and the
        // `k` sets below, each sorted and distinct ([`Filed::keys`]), merged in pairs as
        // references, O(m log m + N log k) comparisons for `m` own keys and `N` keys in all, and
        // each distinct key cloned once. Before, every key was cloned and all `N` sorted together,
        // O(N log N) unless the stable sort found the sets as runs, which it does only for runs
        // longer than about √N.
        [] => {
            zed_collections::sorted::sort_dedup(&mut keys);
            Rc::new(keys)
        }
        _ => {
            zed_collections::sorted::sort_dedup(&mut keys);
            let mut lists: Vec<Vec<&Value>> = Vec::with_capacity(sets.len() + 1);
            lists.push(keys.iter().collect());
            lists.extend(sets.iter().map(|s| s.iter().collect()));
            let all = zed_collections::sorted::union_all(lists);
            Rc::new(all.into_iter().cloned().collect())
        }
    };
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
    Float32,
    Str,
    Atom,
    Tuple(usize),
}

/// The kind of `x` itself, a value [`makeable`] holds of.
fn kind(x: &Value) -> Kind {
    match x {
        Value::Bool(_) => Kind::Bool,
        Value::Int(_) | Value::Big(_) => Kind::Int,
        Value::Rat(_) => Kind::Rat,
        Value::Float(_) => Kind::Float,
        Value::Float32(_) => Kind::Float32,
        Value::Str(_) => Kind::Str,
        Value::Atom(_) => Kind::Atom,
        Value::Tuple(items) => Kind::Tuple(items.len()),
        // `kind` is read only by `Chains::descent`, which only `RowIndex::holds_in` calls, on
        // the components of a makeable tuple and their first components ([`makeable`], where
        // the proof is), so never on a path or a function.
        Value::Path(_) | Value::Family(_) => {
            unreachable!("a row index reads only makeable values")
        }
    }
}

/// The kinds of a value and of its first components, depth by depth, as a number given by
/// [`Chains`]: equal chains have equal numbers within one table.
type Chain = usize;

/// The kinds chains of the values a [`RowIndex`] reads, each numbered once, and what is
/// derived from them, kept for as long as the table: a value's chain and innermost first
/// component, and whether a type holds a value of a chain none of whose components is a key
/// of it ([`kind_status`]). Every index read with one table numbers chains alike, so a
/// listing keeps one for all its makers ([`Values`]).
// Complexity tradeoff (PERF-list-nested-meets): the chain was a vector of kinds made for each
// tuple checked, its innermost first component found by walking down again, and the statuses
// made for each new chain with a memo kept for that chain alone, each O(k) for a value of
// depth k; `n` nested meets check O(n²) tuples, the maker at depth `k` about `k` of depths up
// to `k`, so O(n³) in all. Numbered, a value's chain
// is its first component's with one kind more, read by the tuple's id, and a status of a type
// and a chain reads those of the types below on the chain below, each made once per table:
// O(1) amortized per tuple and per status. Cost: one entry per tuple read and per status
// made, never dropped before the table. With the memo of `Values::known` and the length-1
// parts of [`kind_status`]: bench `l01_23_subtyping::scaling::bench::listing_nested_meets_scales`,
// sizes 32 and 256, 65.9 times the instructions (power 2, debug build, load 66, 2026-11-15);
// before, the same bench ran past its 45 s limit.
#[derive(Default)]
struct Chains {
    /// Per chain, its first kind and the chain below it, if any, each numbered once.
    table: Interner<(Kind, Option<Chain>)>,
    /// Per chain, its number of kinds.
    lens: Vec<usize>,
    /// Per tuple with components, by its id, its chain and its innermost first component. An
    /// id is never given twice in the process (`Items::id`), so an entry stays true of its
    /// sequence whether or not the sequence is still held.
    of: HashMap<Id, (Chain, Value)>,
    /// Per type and chain, [`kind_status`] of the type on the chain's kinds.
    status: HashMap<(Type, Chain), Option<bool>>,
}

impl Chains {
    /// The number of the chain whose first kind is `kind`, above the chain `below`.
    fn intern(&mut self, kind: Kind, below: Option<Chain>) -> Chain {
        let (id, new) = self.table.insert((kind, below));
        if new {
            self.lens.push(below.map_or(1, |b| self.lens[b] + 1));
        }
        id
    }

    /// The chain of `x` and its innermost first component: the first component of each tuple
    /// with components along the way, down to a value that is no such tuple. A tuple read before
    /// is not walked again, and the walk is a loop, never a recursion.
    fn descent(&mut self, x: &Value) -> (Chain, Value) {
        let mut path: Vec<&Items> = Vec::new();
        let mut x = x;
        let (mut chain, leaf) = loop {
            match x {
                Value::Tuple(items) if !items.is_empty() => {
                    if let Some((c, leaf)) = self.of.get(&items.id()) {
                        break (*c, leaf.clone());
                    }
                    path.push(items);
                    x = &items[0];
                }
                _ => break (self.intern(kind(x), None), x.clone()),
            }
        };
        for items in path.into_iter().rev() {
            chain = self.intern(Kind::Tuple(items.len()), Some(chain));
            self.of.insert(items.id(), (chain, leaf.clone()));
        }
        (chain, leaf)
    }

    /// Whether `chain` is that of a scalar ([`whole`]).
    fn whole(&self, chain: Chain) -> bool {
        matches!(
            self.table[chain],
            (
                Kind::Bool
                    | Kind::Int
                    | Kind::Rat
                    | Kind::Float
                    | Kind::Float32
                    | Kind::Str
                    | Kind::Tuple(0),
                None
            )
        )
    }

    /// [`kind_status`] of `t` on the kinds of `chain`, the first columns read on the chain
    /// below. Each status needs only those of a shorter chain, so the work ends; it is done
    /// with a stack of its own, never a recursion, and each status once.
    fn status(&mut self, t: &Type, chain: Chain) -> Option<bool> {
        let mut stack: Vec<(Type, Chain)> = vec![(t.clone(), chain)];
        while let Some((t, c)) = stack.last().cloned() {
            if self.status.contains_key(&(t.clone(), c)) {
                stack.pop();
                continue;
            }
            let (kind, below) = self.table[c].clone();
            // The first columns `kind_status` reads, on the chain below, made first.
            let mut missing = false;
            if let (Kind::Tuple(len), Some(b)) = (&kind, below)
                && let Some(part) = t.p().tuples.lens.get(len)
            {
                for r in part.distinct_atoms() {
                    if !self.status.contains_key(&(r[0].clone(), b)) {
                        stack.push((r[0].clone(), b));
                        missing = true;
                    }
                }
            }
            if missing {
                continue;
            }
            let status = &self.status;
            let s = kind_status(&t, &kind, |f| {
                below.and_then(|b| status.get(&(f.clone(), b)).copied().flatten())
            });
            self.status.insert((t, c), s);
            stack.pop();
        }
        self.status[&(t.clone(), chain)]
    }

    /// The number of kinds in `chain`.
    fn len(&self, chain: Chain) -> usize {
        self.lens[chain]
    }
}

/// Whether `t` holds a value of kind `kind` none of whose components is a key of `t`, when the
/// kind decides it; `first` gives the same for a first column of `t` and the next kind. A
/// tuple outside every first column of its tuple types is in `t` as the part is with every
/// tuple type false. A tuple of length 1 is in a tuple type `(c,)` exactly when its component
/// is in `c`, so where `first` decides every first column, it is in `t` as the part is with
/// each tuple type taken as `first` gives for its column. Any other is not decided by kinds.
// Complexity tradeoff (PERF-list-nested-meets): of the parts of length 1, only one of a single
// tuple type was decided, and each tuple of a part of more was read on its spine, a class per
// spine, made by erasing the tuple and testing it in each open row, O(k) for a tuple of depth k:
// `n` nested meets `((t,) | (k,)) & ((t | int,) | (int,))` list O(n²) tuples of depths up to n,
// each its own spine, O(n³) in all. Decided by kinds, the tuples of one chain of kinds are one
// class, and the status costs the part's evaluation once per type and chain ([`Chains`]).
fn kind_status(t: &Type, kind: &Kind, first: impl Fn(&Type) -> Option<bool>) -> Option<bool> {
    let p = t.p();
    match kind {
        Kind::Bool => Some(false),
        Kind::Int => Some(p.ints.cofinite),
        Kind::Rat => Some(p.rats.cofinite),
        Kind::Float => Some(p.floats.cofinite),
        Kind::Float32 => Some(p.f32s.cofinite),
        Kind::Str => Some(p.strings.cofinite),
        Kind::Atom => Some(p.atoms.cofinite()),
        Kind::Tuple(len) => match p.tuples.lens.get(len) {
            None => Some(p.tuples.rest),
            // The empty tuple is a key where a type holds it.
            Some(_) if *len == 0 => Some(false),
            Some(part) => {
                let rows = part.distinct_atoms();
                let firsts: Vec<Option<bool>> = rows.iter().map(|r| first(&r[0])).collect();
                if firsts.iter().all(|s| *s == Some(false)) {
                    Some(part.eval(&|_| false))
                } else if *len == 1 && firsts.iter().all(Option::is_some) {
                    Some(part.eval(&|r: &Row| first(&r[0]) == Some(true)))
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
    /// sorted and distinct, `leaves` holding the innermost first component of each component
    /// ([`Chains::descent`]). A key is a scalar, a bare atom or the empty tuple, so of a
    /// column's components at each depth only the innermost can be one.
    fn at(&self, v: &[Value], leaves: &[&Value]) -> Vec<usize> {
        let mut at = Vec::new();
        self.extend_at(v, leaves, false, &mut at);
        zed_collections::sorted::sort_dedup(&mut at);
        at
    }

    /// Adds to `at` the positions [`Keyed::at`] gives, unsorted; with `tuples`, only those
    /// under a key of a column whose component is a tuple with components.
    fn extend_at(&self, v: &[Value], leaves: &[&Value], tuples: bool, at: &mut Vec<usize>) {
        for ((by, x), leaf) in self.by.iter().zip(v).zip(leaves) {
            let by: &BTreeMap<Value, Vec<usize>> = by;
            if by.is_empty() || tuples && whole(x) {
                continue;
            }
            // No key is a tuple with components, so only the last component is looked up.
            at.extend(by.get(*leaf).into_iter().flatten());
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
        Value::Float(_) | Value::Float32(_) | Value::Str(_) => true,
        _ => false,
    }
}

/// Whether `x` is a value of the kinds a [`RowIndex`] reads ([`Keyed`]): a scalar, a bare atom,
/// or a tuple of such values. An atom with a payload, a path and a function are not.
///
/// Every value `RowIndex::holds_in` is given is a tuple of makeable values, which is why
/// [`kind`] and [`spine`] treat a path and a function as unreachable. Its three callers:
/// `Membership::contains` tests `makeable` first; `Searching::holds_known` in `empty.rs` reads
/// values through `Search::plain`, which gives a value only when `makeable` holds of it or it is
/// a tuple of such values; and `Maker::step` passes the values of the makers below, `made`,
/// which `Maker::new` starts with [`scalars`] and `Maker::step` extends only with tuples of
/// values already made. `scalars` gives booleans, bare atoms and the values of the five `Lits`
/// of a `Parts`. A `Lits` holds only values of its own kind: its fields are private to this
/// module, a value enters one only through `Type::lit`, which picks the `Lits` by the value's
/// kind, `Type::ints_of`, which asserts integers, and `Parts::join_literals`, which copies from
/// the same field of another `Parts`; every other write (`Lits::zip`, `Lits::not`, the copies in
/// `Type::split` and `empty.rs`) combines or copies the same field. So by induction on the steps
/// that make them, every value made is makeable.
fn makeable(x: &Value) -> bool {
    match x {
        Value::Tuple(items) => items.as_slice().iter().all(makeable),
        Value::Atom(a) => a.is_bare(),
        Value::Path(_) | Value::Family(_) => false,
        _ => whole(x),
    }
}

/// The keys of each column of `row` ([`Filer::file`]), and the column with fewest keys among those
/// that list every value they hold: a tuple none of whose components there is a key is not in
/// the row. A column is first filed by its tuple types, and by its boxes only when that does
/// not list its values, since a box is made by walking the type's diagram.
fn file_row(row: &Row, filer: &mut Filer) -> (Vec<Filed>, Option<usize>) {
    let filed: Vec<Filed> = row
        .iter()
        .map(|t| {
            let f = filer.file(t, Reading::Tuples);
            if f.listed {
                return f;
            }
            let g = filer.file(t, Reading::Boxes);
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
    Seq(Id),
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
        Value::Float32(_) => Some(Kind::Float32),
        Value::Str(_) => Some(Kind::Str),
        Value::Atom(a) if a.is_bare() => Some(Kind::Atom),
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
            Value::Tuple(ys) => Bone::Seq(ys.id()),
            // `x` is a component of a makeable tuple ([`makeable`], where the proof is).
            Value::Path(_) => unreachable!("a row index reads only makeable values"),
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
            Kind::Float32 => Value::float32(n as f32),
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
            let lists = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings];
            let atoms = &p.atoms;
            let names = atoms
                .names()
                .iter()
                .filter(|(_, a)| a.bare != atoms.cofinite());
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
    /// ([`Chains::descent`]), when they decide every open row.
    Kinds(Vec<Option<Chain>>),
    /// The tuple's spine, when the kinds leave an open row unknown.
    Spine(Spine),
}

/// Per kinds, in [`RowIndex::by_kinds`]: the open rows' values (`None` where the kinds leave
/// a row unknown), and whether every one is known.
type KindsDecided = (Vec<Option<bool>>, bool);

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
/// `(int - (2i + 1), 0)` of a meet, is open too, and absorbs the latter (LIST-parity-tail) where
/// the classes of its regions cost no more than filing by it.
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
    /// those columns' components' chains ([`Chains::descent`]).
    read: Vec<bool>,
    /// Per kinds of tuples, the open rows' values on a tuple of them with no key of theirs,
    /// when the kinds decide it ([`kind_status`]), the columns a row absorbs left out where
    /// their component is a scalar, and whether the kinds decide every open row. The chains
    /// are numbered by the table the index is read with, always the same one.
    // Complexity tradeoff (PERF-listing-complement-meets): whether every open row is decided
    // is kept with the values, one word per kinds, read in O(1) by each tuple's check. It was
    // read again by each check, a walk of the `k` open rows, so listing a meet of `c` types
    // given by their complements, each one open row, took order `c²` (12.2 times the
    // instructions from 1024 to 8192 types, the walk 337 M of the 1,262 M at 8192).
    by_kinds: HashMap<Vec<Option<Chain>>, KindsDecided>,
    /// The table [`RowIndex::holds`] reads the chains with; [`RowIndex::holds_in`] is given one.
    chains: Chains,
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
            zed_collections::sorted::sorted_get(&delta, &k).is_none_or(|&d| after(k, d))
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
    /// exclusive or that counts its operands that hold. A list of one row is the same list with
    /// the literal's other value and the block's value and tail swapped, so the literal and its
    /// complement are known complements in either form. The exclusive or of two rows the diagram
    /// joins as `!a & b | a & !b` has lists for its two meets, not nodes, and a list of two rows
    /// in one block is read as the union or meet of its two literals; such a choice is known by
    /// its two rows, and the choices above it then are exclusive ors (PERF-kernel-ratios-9-to-10_5:
    /// the exclusive or of the `c` one-tuples `(i | (i, i))`).
    // Complexity tradeoff: each node is checked once, in constant time but for its key, a
    // list's blocks or an exclusive or's two operands; a choice whose halves are not known
    // complements by these forms stays a union of meets. Naive version (COMPLEXITY.md K69,
    // item 10): the chain left as built, `n` choices and their complements, each changed by a
    // change of `r(0)`, so a check reads order `n` nodes per tuple, O(n²) over the listing;
    // used: one pass over the nodes, O(nodes), then a change reaches one exclusive or. Before
    // the lists of two rows were read as choices, a choice at the bottom of the diagram was not
    // known, none above it was, and a change of one row of `(i | (i, i))` reached 81 nodes at
    // `c = 64` (about `log² c`, the depth of the diagram's balanced exclusive or of unions and
    // meets); read, it reaches 4 at any `c` (`a_change_of_a_row_of_an_exclusive_or_reaches_few_
    // nodes`), and the bench went from 9.94 to 8.65 times the instructions at 8n.
    fn parities(mut self) -> Graph {
        let mut canon: Vec<(usize, bool)> = Vec::with_capacity(self.nodes.len());
        // A list by its rows and each block's value, flipped so its tail is false.
        type ListKey = (Vec<(usize, usize, bool)>, Vec<bool>);
        let mut lists: HashMap<ListKey, (usize, bool)> = HashMap::new();
        let mut xors: HashMap<[usize; 2], (usize, bool)> = HashMap::new();
        let len = self.nodes.len();
        // The literal "row `i` holds" as an operand of a choice when it is no node of its own
        // (inside a list of two rows, below), numbered past the nodes: `(len + i, false)`, and
        // its complement `(len + i, true)`.
        let literal = |i: usize, holds: bool| (len + i, !holds);
        for n in 0..len {
            let opposite = |a: (usize, bool), b: (usize, bool)| a.0 == b.0 && a.1 != b.1;
            // The two operands of a binary node.
            let two = |v: &Vertex| match v {
                Vertex::Or(xs) | Vertex::And(xs) if xs.len() == 2 => Some([xs[0], xs[1]]),
                _ => None,
            };
            let choice = match &self.nodes[n] {
                Vertex::Or(_) | Vertex::And(_) => (|| {
                    let [p, q] = two(&self.nodes[n])?;
                    let union = matches!(self.nodes[n], Vertex::Or(_));
                    // The two operands of `x`, a meet under a union or a union under a meet, by
                    // their canonical nodes. A list of one block of two rows whose value is not
                    // its tail is one too: `(r_i = t_i or r_j = t_j) ? v : !v` is the union of
                    // the two literals when `v` is true and the meet of their complements when
                    // it is false. So the exclusive or of two literals, whose two meets are
                    // such lists (module `xor` of `bdd`), is a choice.
                    let inner = |x: usize| -> Option<[(usize, bool); 2]> {
                        match (&self.nodes[n], &self.nodes[x]) {
                            (Vertex::Or(_), Vertex::And(_)) | (Vertex::And(_), Vertex::Or(_)) => {
                                two(&self.nodes[x]).map(|[a, b]| [canon[a], canon[b]])
                            }
                            (_, Vertex::List(l)) => {
                                let b = &self.lists[*l].0;
                                let [(i, 0, ti), (j, 0, tj)] = b.of_row[..] else {
                                    return None;
                                };
                                let [v] = b.values[..] else { return None };
                                // A meet (`v` false) under a union, a union (`v` true) under a
                                // meet.
                                (v != b.tail && v != union)
                                    .then(|| [literal(i, ti == v), literal(j, tj == v)])
                            }
                            _ => None,
                        }
                    };
                    let ([a, b], [c, d]) = (inner(p)?, inner(q)?);
                    let pairs =
                        opposite(a, c) && opposite(b, d) || opposite(a, d) && opposite(b, c);
                    // `a&b | !a&!b` is `!(a ^ b)`; `(a|b) & (!a|!b)` is `a ^ b`.
                    (pairs && a.0 != b.0).then_some((a, b, union))
                })(),
                _ => None,
            };
            let own = (n, false);
            let c = match (&self.nodes[n], choice) {
                (_, Some(((x, px), (y, py), negated))) => {
                    let constant = negated ^ px ^ py;
                    let key = [x.min(y), x.max(y)];
                    let &mut (e, ce) = xors.entry(key).or_insert((n, constant));
                    // An exclusive or of two literals of no node of their own stays the union
                    // or meet of its two lists; it is known by its canonical node all the same.
                    if key[1] < len {
                        self.nodes[n] = Vertex::Xor(key.to_vec(), constant);
                    }
                    (e, constant ^ ce)
                }
                (Vertex::List(l), None) => {
                    let b = &self.lists[*l].0;
                    // A list of one row, `r = t ? v : u`, is also `r = !t ? u : v`: taken as the
                    // form with `t` true, so a literal and its complement share their key.
                    let (rows, values, tail) = match (&b.of_row[..], &b.values[..]) {
                        (&[(i, 0, false)], &[v]) => (vec![(i, 0, true)], vec![b.tail], v),
                        _ => (b.of_row.clone(), b.values.clone(), b.tail),
                    };
                    let flip = tail;
                    let key = (rows, values.iter().map(|&v| v ^ flip).collect());
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
                        // `alike` holds only of two unions, two meets or two exclusive ors.
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
                    // `n` was matched as one of these three above, only its operands were taken
                    // out, and the loop writes only operands `x`, which come before `n`.
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
                    zed_collections::sorted::sort_dedup(xs);
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
                // `dirty` holds only nodes in `parents`, which are filled from the operands of
                // the `Not`, `Or`, `And` and `Xor` nodes alone.
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

    /// How many nodes a change of row `row` can reach: the lists it is in and every node above
    /// them.
    #[cfg(test)]
    fn reach(&self, row: usize) -> usize {
        let mut seen = HashSet::new();
        zed_graph::reach(
            (self.lists_of_row[row].iter()).map(|&l| self.lists[l].1),
            |&n| seen.insert(n),
            |&n| self.parents[n].iter().copied(),
        );
        seen.len()
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

impl RowIndex {
    fn new(len: usize, part: &Part<Row>, filer: &mut Filer) -> RowIndex {
        let mut rows = part.distinct_atoms();
        rows.sort();
        let filed: Vec<(Vec<Filed>, Option<usize>)> =
            rows.iter().map(|r| file_row(r, filer)).collect();
        // How many rows each key of each column files.
        let mut count: Vec<BTreeMap<&Value, usize>> = vec![BTreeMap::new(); len];
        for (columns, _) in &filed {
            for (j, f) in columns.iter().enumerate() {
                for k in f.keys.iter() {
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
                    for k in filed[i].0[j].keys.iter() {
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
            chains: Chains::default(),
            classes: BTreeMap::new(),
            places: HashMap::new(),
            changes: vec![0; rows_len],
            graph,
        }
    }

    /// The open rows' values on a tuple of the kinds `class` with no key of theirs, where the
    /// kinds decide them, leaving out the columns a row absorbs whose component is a scalar.
    /// Each column's types are made to the depth of the kinds, for [`place_regions`], and a
    /// type's status on a chain is read from `chains`, made once per table.
    fn by_kinds(&mut self, class: &[Option<Chain>], chains: &mut Chains) -> Vec<Option<bool>> {
        self.open
            .iter_mut()
            .map(|row| {
                let mut value = Some(true);
                for (j, levels) in row.levels.iter_mut().enumerate() {
                    // Every column of an open row is read (`RowIndex::new`), so `class[j]` is
                    // a chain; were it not, the kinds would not decide the row.
                    let s = match class[j] {
                        None => None,
                        Some(chain) if row.absorbs[j] && chains.whole(chain) => continue,
                        Some(chain) => Self::status(levels, chain, chains),
                    };
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

    /// The status of a column type, `levels[0][0]`, on `chain` ([`Chains::status`]), after
    /// making the column's types to the chain's depth.
    fn status(levels: &mut Vec<Vec<Type>>, chain: Chain, chains: &mut Chains) -> Option<bool> {
        while levels.len() < chains.len(chain) {
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
        chains.status(&levels[0][0], chain)
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
        let mut chains = std::mem::take(&mut self.chains);
        let holds = self.holds_in(v, &mut chains, fits);
        self.chains = chains;
        holds
    }

    /// [`RowIndex::holds`], the chains read with `chains`, which every call on this index is
    /// given: a listing's makers share one ([`Values`]).
    fn holds_in(&mut self, v: &[Value], chains: &mut Chains, fits: impl Fn(&Row) -> bool) -> bool {
        let descents: Vec<(Chain, Value)> = v.iter().map(|x| chains.descent(x)).collect();
        let leaves: Vec<&Value> = descents.iter().map(|(_, leaf)| leaf).collect();
        let mut at = self.keyed.at(v, &leaves);
        self.absorbed.extend_at(v, &leaves, true, &mut at);
        zed_collections::sorted::sort_dedup(&mut at);
        let kinds: Vec<Option<Chain>> = descents
            .iter()
            .zip(&self.read)
            .map(|(&(c, _), &read)| read.then_some(c))
            .collect();
        if !self.by_kinds.contains_key(&kinds) {
            let decided = self.by_kinds(&kinds, chains);
            let all = decided.iter().all(Option::is_some);
            self.by_kinds.insert(kinds.clone(), (decided, all));
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
        let (decided, all_decided) = &by_kinds[&kinds];
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
            shape: match *all_decided {
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
        filer: &mut Filer,
    ) -> Maker {
        let p = ty.p();
        let made = scalars(&p);
        let ids = made.iter().map(|v| numbers.leaf(v)).collect();
        let by_value = p
            .tuples
            .lens
            .iter()
            .map(|(&len, part)| (len, RowIndex::new(len, part, filer)))
            .collect();
        Maker {
            boxes,
            rows,
            by_value,
            tried: HashSet::new(),
            next: 0,
            at: At::Start(0),
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
    /// changing anything but how far it got. The components' makers come before `me`.
    // Complexity tradeoff: a scan of a box's components that stops at one whose value is not
    // made yet keeps where it stopped, and the next step resumes there: what it found holds
    // for good, since a maker's values only grow and one done makes no more. A first version
    // scanned again from the box's first component (from its last, past a position) at each
    // step, 1 + 2 + ... + L checks for a box of L components each made on demand, O(L²):
    // 4.7·10⁷ instructions at L = 400 and 7.8·10⁸ at L = 3200, 16.6 times, for the one value
    // of a tuple of L literals (PERF-tuple-print). Resumed, each component is checked once on
    // entering the box and once per position past it, O(L) per tuple made. Test:
    // l01_23_subtyping::listing::listing_one_wide_tuple_scales; COMPLEXITY.md K116.
    fn step(
        makers: &mut [Maker],
        numbers: &mut Numbers,
        known: &RefCell<HashMap<(Type, Id), bool>>,
        chains: &mut Chains,
        me: usize,
    ) -> Result<(), Need> {
        let (below, rest) = makers.split_at_mut(me);
        let m = &mut rest[0];
        match std::mem::replace(&mut m.at, At::Start(0)) {
            At::Start(from) => {
                let Some((cols, _)) = m.boxes.get(m.next) else {
                    m.done = true;
                    return Ok(());
                };
                for (k, &c) in cols.iter().enumerate().skip(from) {
                    match below[c].has(c, 0) {
                        Ok(true) => {}
                        Ok(false) => {
                            // A component with no value: the box has no tuple.
                            m.next += 1;
                            return Ok(());
                        }
                        Err(need) => {
                            m.at = At::Start(k);
                            return Err(need);
                        }
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
                m.at = At::Past(pos, cols.len());
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
                        .all(|((t, &by), (&c, x))| {
                            by == Some(c) || t.contains_kept(x, &mut known.borrow_mut())
                        })
                };
                let index = m.by_value.get_mut(&row.len()).expect("an index per length");
                if index.holds_in(&v, chains, fits) {
                    m.made.push(Value::tuple(v));
                    m.ids.push(numbers.tuple(key));
                }
            }
            At::Past(mut pos, upto) => {
                let cols = &m.boxes[m.next].0;
                // The next position, the last component fastest; past the last, the next box.
                for k in (0..upto).rev() {
                    match below[cols[k]].has(cols[k], pos[k] + 1) {
                        Ok(true) => {
                            pos[k] += 1;
                            pos[k + 1..].fill(0);
                            m.at = At::Tuple(pos);
                            return Ok(());
                        }
                        Ok(false) => {}
                        Err(need) => {
                            m.at = At::Past(pos, k + 1);
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
                    let (known, chains) = (&self.known, &mut self.chains);
                    if let Err(need) =
                        Maker::step(&mut self.makers, &mut self.numbers, known, chains, m)
                    {
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
/// a bound of `L .. U -> V`, or after `is` ([`Type::surface_by_name`]).
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
    /// The key of an arrow, `K -> V`: a `TypeNot`, so a union, intersection or difference is
    /// parenthesized, `(int | #a) -> int` (author P222).
    Key,
    /// A bound of `L .. U -> V`: a `TypeNot`, as a key is, but a tuple stands bare.
    Bound,
    /// After `is`, in `IsTest` and `IsPat`: a `TypeUnion`, so only an arrow is parenthesized.
    Is,
}

/// How a text binds, for parenthesizing it as an operand.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) enum TextClass {
    Arrow,
    Union,
    Diff,
    And,
    /// `(A, B)`: a primary, except as an arrow's key, where it would read as parameters.
    Tuple,
    Prim,
    /// The class of the one node the text is.
    Of(usize),
}

impl TextPlace {
    pub(crate) fn admits(self, c: TextClass) -> bool {
        use TextClass as C;
        match self {
            TextPlace::Any => true,
            TextPlace::Union => matches!(c, C::Union | C::And | C::Tuple | C::Prim),
            TextPlace::And => matches!(c, C::And | C::Tuple | C::Prim),
            TextPlace::DiffLeft => matches!(c, C::Diff | C::Tuple | C::Prim),
            TextPlace::Prim => matches!(c, C::Tuple | C::Prim),
            // `Arrow` takes a `TypeNot` as its key, and `|`, `&` and `\` bind tighter than `->`
            // (DESIGN.md sec:grammar, author P222), so a connective key is parenthesized,
            // `(int | #a) -> int`; so is a tuple, which would read as the parameters.
            TextPlace::Key => c == C::Prim,
            TextPlace::Bound => matches!(c, C::Tuple | C::Prim),
            TextPlace::Is => c != C::Arrow,
        }
    }
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
    //!   when it is empty, unless the value type is inhabited wherever the guarantee is
    //!   (`holds`: `type U = (U) -> U` holds the identity on `U`, and `type U = (U) -> (int, U)`
    //!   a morphism pairing its argument with an integer, and `type U = (U) -> ((U) -> _)` a
    //!   morphism whose values are constant morphisms, plan row GROUP-admit-precision); nor in
    //!   the guarantee of a morphism type whose guarantee and permission differ, or that stands
    //!   under `&`, `\`, a complement or differing domain bounds, directly or through a
    //!   definition named there (cross-review X14: `W = (W) -> int` is accepted,
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
    use super::{Type, mix};
    use crate::deep;
    use zed_hash::fnv1a_64;

    pub(super) mod group;
    pub(super) mod unfold;

    mod walk {
        //! `Clone`, `==` and `Debug` of [`Expr`], and `Debug` of a body's tree ([`Node`]), each
        //! keeping its own stack on the heap, so an expression of any depth is copied, compared and
        //! written on a small stack (COMPLEXITY.md K39). Each costs O(size). `Debug` writes the one
        //! line a derived `Debug` writes for `{:?}`, under `{:#?}` too.

        use std::fmt;
        use std::sync::Arc;

        use super::{Expr, Node, Shape};

        /// An expression or tree: its parts below, and what it holds besides them.
        pub(super) trait Tree: Sized {
            /// The parts directly below, in order.
            fn kids(&self) -> impl DoubleEndedIterator<Item = &Self>;

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

            /// Whether the two hold the same besides their parts below, and as many of those.
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

            /// Whether the two hold the same besides their parts below, and as many of those:
            /// the equality test of `ByShape` in module `group`, cheaper than its order.
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
        /// value twice is equal unread. An expression owns its parts, so no pair is met twice.
        fn equal(a: &Expr, b: &Expr) -> bool {
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

        /// The order of two expressions, part by part from a stack of pairs as [`equal`] reads
        /// them: the first pair whose heads differ decides. Two expressions are equal in it
        /// exactly when `==` says so. Two equal heads have as many parts, so the heads read form
        /// a code of each expression that no other's extends, and the order is total.
        /// The stack's buffer is kept on the thread between comparisons, as in
        /// [`super::super::order()`] (COMPLEXITY.md K143).
        fn order(a: &Expr, b: &Expr) -> std::cmp::Ordering {
            let mut pairs =
                super::super::emptied(PAIRS.try_with(std::cell::Cell::take).unwrap_or_default());
            pairs.push((a, b));
            let mut c = std::cmp::Ordering::Equal;
            while let Some((a, b)) = pairs.pop() {
                if std::ptr::eq(a, b) {
                    continue;
                }
                c = a.head().cmp(&b.head());
                if c.is_ne() {
                    break;
                }
                pairs.extend(a.kids().zip(b.kids()));
            }
            let _ = PAIRS.try_with(|s| s.set(super::super::emptied(pairs)));
            c
        }

        thread_local! {
            /// The buffer of the stack [`order`] last used on this thread, empty.
            static PAIRS: std::cell::Cell<Vec<(&'static Expr, &'static Expr)>> =
                const { std::cell::Cell::new(Vec::new()) };
        }

        impl Expr {
            /// What [`Expr::same_head`] compares, in an order: the kind, the index of a
            /// parameter or definition, an atom's name, a held type, and the number of parts.
            fn head(&self) -> (u8, usize, &str, Option<&super::Type>, usize) {
                let n = self.kids().count();
                match self {
                    Expr::Param(i) => (1, *i, "", None, n),
                    Expr::Ref(i, _) => (2, *i, "", None, n),
                    Expr::Type(t) => (3, 0, "", Some(t), n),
                    Expr::Union(_) => (4, 0, "", None, n),
                    Expr::And(_) => (5, 0, "", None, n),
                    Expr::Not(_) => (6, 0, "", None, n),
                    Expr::Diff(..) => (7, 0, "", None, n),
                    Expr::Tuple(_) => (8, 0, "", None, n),
                    Expr::Atom(name, _) => (9, 0, name, None, n),
                    Expr::Morphism(..) => (10, 0, "", None, n),
                }
            }
        }

        impl Ord for Expr {
            fn cmp(&self, other: &Expr) -> std::cmp::Ordering {
                order(self, other)
            }
        }

        impl PartialOrd for Expr {
            fn partial_cmp(&self, other: &Expr) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
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
            /// Copies the parts in a loop: each expression with parts is rebuilt once they are
            /// copied.
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
                                    // `Step::Copy` copies these two at once and pushes
                                    // `Step::Rebuild` only for the other shapes.
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
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
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
        /// Shared with the group's key in `GROUPS`, which orders the groups of one digest by
        /// their definitions.
        defs: Arc<Vec<Def>>,
        /// Each definition identifier hashed once, before its occurrences and instances.
        name_hashes: Vec<u64>,
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
        /// The definitions by their classes, then their names, made when first asked
        /// ([`Checked::by_name`]).
        by_name: OnceLock<Vec<usize>>,
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
        spell: Vec<u64>,
        node: Vec<Option<Arc<Node>>>,
    }

    /// An expression as a shared tree, each node knowing whether it mentions the group, so that a
    /// part kept unevaluated is shared rather than copied, and no node's flag is computed twice.
    pub(in crate::types) struct Node {
        /// A hash of the shape, from the children's: equal shapes hash alike.
        digest: u64,
        /// The retained syntax, including names in the types it holds.
        name_digest: u64,
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
                Shape::Atom(name, _) => mix(9, fnv1a_64(name.as_bytes())),
                Shape::Morphism(..) => 10,
            }
        }

        /// The same constructor tag for retained syntax, with a held type's presentation.
        fn name_tag(&self) -> u64 {
            match self {
                Shape::Type(t) => mix(3, t.name_digest()),
                other => other.tag(),
            }
        }

        /// Whether the order of the children does not count: the operands of a union or a meet.
        /// `A | B` and `B | A` are one type, as are `A & B` and `B & A`, so [`canon`] and
        /// [`spelled`] read these operands as a set (items GROUP-search-canon-key for the meet,
        /// FAIL-codex-r3-order-seed for the union).
        fn unordered(&self) -> bool {
            matches!(self, Shape::Union(_) | Shape::And(_))
        }

        /// The top of the shape, without its children or type, for [`Canon::order`] and [`canon`]:
        /// the kind, the index of a parameter or definition, and an atom's name.
        pub(in crate::types) fn head(&self) -> (u8, usize, &str) {
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
    pub(in crate::types) fn same(l: &Node, u: &Node) -> bool {
        l.class == u.class
    }

    /// Whether the value type `v` of a morphism type holds its guarantee `l` as written: each
    /// arm of `l` (`l` itself when it is not a union) is written as `v` or as an arm of `v`.
    /// Then `l <: v` at every argument and every value of the group's members, so `l -> v`
    /// holds a value whatever they are: with `l` empty the empty morphism, and otherwise `v`
    /// is inhabited too and a constant morphism into it is one (plan row GROUP-admit-precision).
    /// `type U = (U) -> U` is the case: `U` holds the identity on `U`.
    /// Proof that `l <: v`: two nodes of one group of equal class are written alike
    /// ([`same`]), so they denote one type at every argument and every value of the members;
    /// an arm of a union is a subtype of it. Sufficient, not necessary: `l = int`, `v = num`
    /// is not seen. O(|arms of l| + |arms of v|) expected, by one hash set of classes.
    pub(in crate::types) fn covers(v: &Node, l: &Node) -> bool {
        let arms = |e: &Node| -> Vec<u32> {
            match &e.e {
                Shape::Union(xs) => xs.iter().map(|x| x.class).collect(),
                _ => vec![e.class],
            }
        };
        let mut held: std::collections::HashSet<u32> = arms(v).into_iter().collect();
        held.insert(v.class);
        arms(l).iter().all(|c| held.contains(c))
    }

    /// Whether the value type `v` of a morphism type is inhabited at every argument and every
    /// value of the group's members at which its guarantee `l` is; then `l -> v` holds a value
    /// whatever they are, as with [`covers`], which this extends (plan row
    /// GROUP-admit-precision). `closed` says whether a part that names no definition is
    /// inhabited at every argument. `type U = (U) -> (int, U)` is the case [`covers`] misses:
    /// a value of `U` gives one of `(int, U)`.
    ///
    /// Proof. Write `inh(x)` for "x is inhabited" at fixed arguments and members.
    /// 1. The parts `l` forces (`forced`): each of `x` in a tuple or an atom's payload `x`
    ///    (an atom is its name with a tuple of its payload), each `x` of a meet `x & y`, and
    ///    `x` in `x \ y`, are supertypes of a value's part or hold the value, so
    ///    `inh(parent) ⇒ inh(x)`; by induction `inh(arm) ⇒ inh(x)` for every `x` reached from
    ///    an arm of `l` through these. `inh(l)` makes some arm inhabited, so `inh(l) ⇒ inh(x)`
    ///    for `x` reached from every arm, and for `l` itself. Two nodes of one class are
    ///    written alike and denote one type ([`same`]), so the classes stand for the parts.
    /// 2. `v` holds (`inh(l) ⇒ inh(v)`) when its class is forced; or it names no definition
    ///    and `closed` says it is inhabited; or it is a union with an arm that holds; or a tuple
    ///    or atom each of whose parts holds (`inh` of a tuple is the meet of its parts'); or a
    ///    morphism type `a -> c` with guarantee and permission written alike, `a` naming no
    ///    definition and `c` holding, since a constant morphism into `c` is a value of it.
    /// 3. A morphism type whose guarantee is written as the empty type holds a value at every
    ///    argument and every value of the members, whatever its permission and value type: a
    ///    morphism type is `(guarantee ⊆ dom ⊆ permission) -> value`
    ///    ([`crate::types::Arrow`]), and the morphism with no key has `dom = ∅`, which lies
    ///    between `∅` and any permission and has no key whose value must lie in the value
    ///    type. So `v` holds.
    /// 4. A morphism type `a -> c` with guarantee and permission written alike holds when `c`
    ///    does, whether or not `a` names a definition: at fixed arguments and members `a` is
    ///    one set `A`; if `A` is empty the morphism with no key is a value, and otherwise, with
    ///    `w` a value of `c`, the constant morphism on `dom = A` with value `w` everywhere is.
    ///    So `inh(c) ⇒ inh(a -> c)`, and `inh(l) ⇒ inh(c)` gives `inh(l) ⇒ inh(v)`. Here `c`
    ///    holds when its class is forced or it names no definition and `closed` says it is
    ///    inhabited; it is not walked further, which keeps the cost below. The guarantee `a`
    ///    itself is read by the admission check on its own, as every such guarantee is.
    ///    Cases steps 3 and 4 accept and step 2 did not: `type U = (U) -> ((U) -> _)` and
    ///    `type U = (U) -> (empty .. _ -> U)`, test
    ///    `l01_23_subtyping::admission::a_value_type_morphism_inhabited_whatever_its_guarantee_is_accepted`.
    ///
    /// Sufficient, not necessary: `inh(l) ⇒ inh(v)` for formulas with meets of recursive types
    /// is as hard as the monotonicity it stands for (coNP-complete, COMPLEXITY.md K27).
    ///
    /// Cost: one walk of `l` and one of `v`, O(|l| + |v|) expected with one hash set, plus
    /// `closed` on disjoint parts of `v`. The walks stop at a morphism type whose guarantee names
    /// a definition, which the admission check reads on its own, so each node is read by the
    /// walks of at most one enclosing morphism type: O(size of the bodies) over a group. Both
    /// walks keep their own stacks, so any depth is read on a small stack (COMPLEXITY.md K39).
    pub(in crate::types) fn holds(
        l: &Node,
        v: &Arc<Node>,
        mut closed: impl FnMut(&Arc<Node>) -> bool,
    ) -> bool {
        use std::collections::HashSet;
        if covers(v, l) {
            return true;
        }
        let forced = |arm: &Node| -> HashSet<u32> {
            let (mut out, mut todo) = (HashSet::new(), vec![arm]);
            while let Some(x) = todo.pop() {
                if !out.insert(x.class) {
                    continue;
                }
                match &x.e {
                    Shape::Tuple(xs) | Shape::Atom(_, xs) | Shape::And(xs) => {
                        todo.extend(xs.iter().map(|x| &**x));
                    }
                    Shape::Diff(a, _) => todo.push(a),
                    _ => {}
                }
            }
            out
        };
        let mut need = match &l.e {
            Shape::Union(xs) if !xs.is_empty() => {
                let mut need = forced(&xs[0]);
                for x in &xs[1..] {
                    let more = forced(x);
                    need.retain(|c| more.contains(c));
                }
                need
            }
            _ => forced(l),
        };
        need.insert(l.class);
        // The parts of `v` read, in pre-order, each with its parent's index and its value so
        // far: `Any` a union (false until an arm holds), `All` a tuple, an atom or a morphism's
        // value (true until a part fails), `Leaf` decided.
        enum Op {
            Any,
            All,
            Leaf,
        }
        let mut nodes: Vec<(usize, Op, bool)> = Vec::new();
        let mut todo: Vec<(&Arc<Node>, usize)> = vec![(v, 0)];
        while let Some((x, parent)) = todo.pop() {
            let me = nodes.len();
            let op = if need.contains(&x.class) {
                (Op::Leaf, true)
            } else if !x.recursive {
                (Op::Leaf, closed(x))
            } else {
                match &x.e {
                    Shape::Union(xs) => {
                        todo.extend(xs.iter().map(|x| (x, me)));
                        (Op::Any, false)
                    }
                    Shape::Tuple(xs) | Shape::Atom(_, xs) => {
                        todo.extend(xs.iter().map(|x| (x, me)));
                        (Op::All, true)
                    }
                    Shape::Morphism(a, b, c) if same(a, b) && !a.recursive => {
                        todo.push((c, me));
                        (Op::All, true)
                    }
                    // Step 3 of the proof: the empty morphism.
                    Shape::Morphism(a, ..) if matches!(&a.e, Shape::Type(t) if t.lists_nothing()) => {
                        (Op::Leaf, true)
                    }
                    // Step 4 of the proof: `c` is read here and not walked, so this walk does
                    // not enter a morphism type whose guarantee names a definition.
                    Shape::Morphism(a, b, c) if same(a, b) => (
                        Op::Leaf,
                        need.contains(&c.class) || (!c.recursive && closed(c)),
                    ),
                    _ => (Op::Leaf, false),
                }
            };
            nodes.push((parent, op.0, op.1));
        }
        // A part's index is above its parent's, so reading down from the last settles every
        // part before its parent.
        for i in (1..nodes.len()).rev() {
            let (parent, _, value) = nodes[i];
            let p = &mut nodes[parent];
            match p.1 {
                Op::Any => p.2 |= value,
                Op::All => p.2 &= value,
                Op::Leaf => unreachable!("a decided part has no parts read"),
            }
        }
        nodes[0].2
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
        name_digest: u64,
        args: Vec<Type>,
        /// Each member's type: a plain member's set when the group is instantiated, a recursive
        /// member's when first read and until the end of the unit that read it ([`Env::forget`]).
        members: Vec<Mutex<Option<Type>>>,
        /// What the group's decider found for each member (`empty::judge`), when first asked.
        pub(in crate::types) judged: OnceLock<Judgment>,
        /// Empty meets proved by the diagonal occurrence-parity test, by member, when first
        /// asked ([`diagonal_empty`]). It is kept with the instance, as [`Env::judged`] is, and not
        /// with the group: groups are shared by every thread, so a result kept with the group
        /// would outlive `Type::forget_emptiness` and make the cost of a first decision depend
        /// on what other units and threads decided before (item GSX-unsolved, I6.7).
        diagonal_empty: OnceLock<Vec<bool>>,
        /// The names made so far of the parts kept unevaluated at these arguments, by their nodes'
        /// numbers (`Node::at`), which the name of a part around them holds rather than spells
        /// out again (`unfold::Env::part_name`).
        part_names: Mutex<HashMap<u32, super::Rope>>,
        /// The node of each recursive member and part kept unevaluated made at these arguments,
        /// held weakly: while one is held, by anyone, it is the one node of its place, so a
        /// member or part made again after the end of a unit is the node still held, not a copy
        /// beside it (`unfold::Env::node`). The end of a unit forgets the unfoldings of those
        /// alive, since a part's unfolding holds the parts of the body below it, and the parts
        /// of a cycle of definitions hold one another without passing through a member
        /// (`unfold::Env::forget`).
        nodes: Mutex<HashMap<At, std::sync::Weak<super::Node>>>,
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
        /// Each meet's node, with the node of each of its operands as written in its origin, a
        /// recursive meet among them read as its own operands (`empty::system`).
        pub(in crate::types) meets: HashMap<u32, Vec<u32>>,
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

    /// A member or unevaluated part at one instance's arguments. Its primary hash uses
    /// the canonical form and class. Its presentation hash also uses the full named
    /// definition graph and the node's own spelling, so equal unfoldings with different
    /// printed bodies stay separate. Both are followed by structural collision checks.
    pub(super) struct Key {
        digest: u64,
        name_digest: u64,
        env: Arc<Env>,
        at: At,
        /// The class of the member or part in its group's canonical form.
        class: u32,
    }

    /// Which type of an instance a key names.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    enum At {
        /// The member of this index.
        Member(usize),
        /// The part kept unevaluated at the body node of this number.
        Part(u32),
    }

    impl Key {
        pub(in crate::types) fn diagonal_empty(&self) -> bool {
            let At::Member(i) = self.at else {
                return false;
            };
            let g = &self.env.group().0;
            if !matches!(g.defs[i].body, Expr::And(_)) {
                return false;
            }
            self.env.diagonal_empty.get_or_init(|| {
                diagonal_empty(
                    &g.defs,
                    &g.canon.get().expect("a key has a canonical form").member,
                )
            })[i]
        }

        pub(in crate::types) fn search_class(&self) -> u32 {
            self.class
        }

        fn new(env: Arc<Env>, at: At) -> Key {
            let canon = env.group().canon();
            let (class, spell) = match at {
                At::Member(i) => (canon.member[i], mix(15, env.group().0.name_hashes[i])),
                At::Part(n) => (canon.at[n as usize], canon.spell[n as usize]),
            };
            let digest = mix(mix(env.digest, u64::from(class)), u64::from(at.kind()));
            let name_digest = mix(
                mix(mix(env.name_digest, u64::from(class)), u64::from(at.kind())),
                spell,
            );
            Key {
                digest,
                name_digest,
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
                (At::Part(n), At::Part(m)) if !(Arc::ptr_eq(a, b) && n == m) => spelled(
                    (a.part(n), &a.defs, a.spells()),
                    (b.part(m), &b.defs, b.spells()),
                ),
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

        pub(super) fn name_digest(&self) -> u64 {
            self.name_digest
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

        /// The order of two keys: by digest, kind and class, the groups' canonical forms and the
        /// arguments. What the forms' shapes decide is decided here; the pairs of types inside
        /// them that tie in digest, then the arguments, are pushed to `types` in the order they
        /// are to be compared when the rest ties, by the caller's loop (`order`), so that no type
        /// is compared by recursion here. Two keys of one instance and one class are equal. Time
        /// linear in the classes where the groups differ and tie in digest, and constant
        /// otherwise.
        pub(super) fn order<'a>(
            &'a self,
            other: &'a Key,
            types: &mut Vec<(&'a Type, &'a Type)>,
        ) -> std::cmp::Ordering {
            let c = super::digests_cmp(
                (self.digest, self.name_digest),
                (other.digest, other.name_digest),
            )
            .then(self.rank().cmp(&other.rank()));
            if c.is_ne() {
                return c;
            }
            // Under `blind`, names are left out: two keys of one instance and one class, and two
            // keys of groups of one form whose arguments tie, are then equal.
            let blinded = super::names_blind();
            if Arc::ptr_eq(&self.env, &other.env) {
                return match blinded {
                    true => std::cmp::Ordering::Equal,
                    false => self.spelling(other),
                };
            }
            let (a, b) = (self.env.group(), other.env.group());
            if !Arc::ptr_eq(&a.0, &b.0) {
                let c = a.canon().order(b.canon(), types);
                if c.is_ne() {
                    return c;
                }
                // Equal fingerprints still need the retained definition graph compared:
                // reusing another spelling would carry its names through the type memos.
                // The presentation hash already orders most renamed copies above, including
                // members of one semantic class. This fallback confirms genuine collisions;
                // it does not establish that the emptiness search is independent of that
                // presentation order (item GSX-unsolved).
                if !blinded {
                    let c = a.0.names_order(&b.0);
                    if c.is_ne() {
                        return c;
                    }
                }
            }
            if !blinded {
                let c = self.spelling(other);
                if c.is_ne() {
                    return c;
                }
            }
            // Two groups of one form can take different numbers of arguments, when a parameter
            // is not read; `zip` would drop the extra ones.
            let c = self.env.args.len().cmp(&other.env.args.len());
            if c.is_ne() {
                return c;
            }
            types.extend(self.env.args.iter().zip(&other.env.args));
            std::cmp::Ordering::Equal
        }
    }

    /// A sufficient Empty proof for meets of written two-state occurrence counters.
    // Complexity tradeoff: a product of k counters has 2^k states, and general
    // affine elimination costs O(k^3). Read singleton counters, a length counter,
    // and a finite alphabet directly, O((nodes + literal entries) log n) per
    // written group, cached once per instance. The equations here are diagonal: x_a = b_a,
    // and sum x_a = b_length. Other equations and non-list definitions receive
    // no answer here and keep the existing search and its refusals. No names or
    // written operand positions enter the proof. Test:
    // setop::bounded_empty_parity_is_decided_in_the_size_of_the_constraints.
    fn diagonal_empty(defs: &[Def], classes: &[u32]) -> Vec<bool> {
        use super::Lits;
        use crate::Value;
        use std::collections::{BTreeMap, HashSet};
        struct State<'a> {
            nil: bool,
            edges: Vec<(&'a Lits, usize)>,
        }
        enum Counter<'a> {
            Symbol(&'a Value, bool),
            Length(bool),
            Alphabet(&'a Lits),
        }
        fn ints(e: &Expr) -> Option<&Lits> {
            let Expr::Type(t) = e else { return None };
            let super::Node::Parts(p, _) = &*t.0 else {
                return None;
            };
            (p.scalars_only()
                && p.bools == 0
                && [&p.rats, &p.floats, &p.f32s, &p.strings]
                    .iter()
                    .all(|l| !l.cofinite && l.values.is_empty()))
            .then_some(&p.ints)
        }
        fn reference(e: &Expr) -> Option<usize> {
            match e {
                Expr::Ref(i, args) if args.is_empty() => Some(*i),
                _ => None,
            }
        }
        fn state(d: &Def) -> Option<State<'_>> {
            if !d.params.is_empty() {
                return None;
            }
            let mut s = State {
                nil: false,
                edges: Vec::new(),
            };
            // Expr is an owned tree; recursive references are edges, never unfolded.
            let mut todo = vec![&d.body];
            while let Some(e) = todo.pop() {
                match e {
                    Expr::Union(xs) => todo.extend(xs),
                    Expr::Type(t) if *t == Type::atom("nil") => s.nil = true,
                    Expr::Atom(name, xs) if name == "nil" && xs.is_empty() => s.nil = true,
                    Expr::Atom(name, xs) if name == "cons" && xs.len() == 2 => {
                        s.edges.push((ints(&xs[0])?, reference(&xs[1])?));
                    }
                    _ => return None,
                }
            }
            Some(s)
        }
        let states: Vec<_> = defs.iter().map(state).collect();
        let counters: Vec<_> = states
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let s = s.as_ref()?;
                if s.edges.len() == 1 {
                    let (head, j) = s.edges[0];
                    if j == i && s.nil {
                        return Some(Counter::Alphabet(head));
                    }
                    let other = states.get(j)?.as_ref()?;
                    if j != i
                        && s.nil != other.nil
                        && head.cofinite
                        && head.values.is_empty()
                        && other.edges.len() == 1
                        && other.edges[0].1 == i
                        && other.edges[0].0.cofinite
                        && other.edges[0].0.values.is_empty()
                    {
                        return Some(Counter::Length(!s.nil));
                    }
                    return None;
                }
                if s.edges.len() != 2 {
                    return None;
                }
                let &(single, j) = s
                    .edges
                    .iter()
                    .find(|(l, _)| !l.cofinite && l.values.len() == 1)?;
                let &(rest, stay) = s.edges.iter().find(|(l, _)| l.cofinite)?;
                if j == i || stay != i || rest.values != single.values {
                    return None;
                }
                let other = states.get(j)?.as_ref()?;
                if s.nil == other.nil || other.edges.len() != 2 {
                    return None;
                }
                if !other.edges.iter().any(|&(l, to)| to == i && l == single)
                    || !other.edges.iter().any(|&(l, to)| to == j && l == rest)
                {
                    return None;
                }
                Some(Counter::Symbol(single.values.iter().next()?, !s.nil))
            })
            .collect();
        defs.iter()
            .map(|d| {
                let Expr::And(xs) = &d.body else { return false };
                if !d.params.is_empty() {
                    return false;
                }
                let (mut length, mut alphabet) = (None, None::<(&Lits, u32)>);
                let mut symbols = BTreeMap::new();
                let mut references = HashSet::new();
                for e in xs {
                    let Some(i) = reference(e) else { continue };
                    if !references.insert(i) {
                        continue;
                    }
                    let Some(c) = counters.get(i).and_then(Option::as_ref) else {
                        continue;
                    };
                    match c {
                        Counter::Symbol(a, b) => {
                            if symbols.insert(*a, *b).is_some_and(|old| old != *b) {
                                return true;
                            }
                        }
                        Counter::Length(b) => {
                            if length.replace(*b).is_some_and(|old| old != *b) {
                                return true;
                            }
                        }
                        Counter::Alphabet(a) if !a.cofinite => {
                            // Reuse the group's exact stable classes to order a
                            // fingerprint tie. Comparing tied large sets at every
                            // reference would repeat their boundaries. Equal
                            // classes unfold alike, including the scalar label.
                            let key = (a.values.len(), a.sum(), classes[i]);
                            let old =
                                alphabet.map(|(old, class)| (old.values.len(), old.sum(), class));
                            if old.is_none_or(|old| key < old) {
                                alphabet = Some((a, classes[i]));
                            }
                        }
                        Counter::Alphabet(_) => {}
                    }
                }
                let Some((alphabet, _)) = alphabet else {
                    return false;
                };
                if symbols.iter().any(|(a, b)| *b && !alphabet.contains(a)) {
                    return true;
                }
                // A full alphabet walk is charged to the written singleton references
                // in this meet; shared large alphabets with fewer counters are skipped.
                if alphabet.values.len() > symbols.len() {
                    return false;
                }
                let mut sum = false;
                for a in &alphabet.values {
                    let Some(b) = symbols.get(a) else {
                        return false;
                    };
                    sum ^= *b;
                }
                length.is_some_and(|b| b != sum)
            })
            .collect()
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
            // Complexity tradeoff (COMPLEXITY.md K27, GROUP-decide-bytes): making the form at
            // each instance and each comparison costs O((N + M) log N) each time; it is made once,
            // on first use, and kept with the group, so later instances read it in O(1), at the
            // cost of the form's memory, O(N + M), for the group's life. The first instance of a
            // group pays for it: `l01_23_groups_and_refusals::judgments::deciding_a_group_scales`
            // holds that first run, at 256 and 2,048 definitions, to the n log n limit (2,141,806
            // and 17,071,066 bytes, 8.0 times, 2026-11-12), and so decides neither ring before.
            self.0
                .canon
                .get_or_init(|| canon(&self.0.bodies, &self.0.name_hashes))
        }
    }

    impl Checked {
        /// The node of number `n`, which a key names, so the form is made.
        fn part(&self, n: u32) -> &Node {
            let canon = self.canon.get().expect("a key's group has its form");
            canon.node[n as usize].as_deref().expect("a part is read")
        }

        /// The spelling hashes of the nodes, by number ([`Canon::spell`]), so the form is made.
        fn spells(&self) -> &[u64] {
            &self.canon.get().expect("a key's group has its form").spell
        }

        /// The definitions in the order of their classes, then their names: what tells apart two
        /// groups of one canonical form ([`Key::order`]). The list fixes the named binding
        /// context; a key's own spelling distinguishes members of one class. Time O(d log d)
        /// comparisons for d definitions, once per group.
        fn by_name(&self) -> &[usize] {
            self.by_name.get_or_init(|| {
                let member = &self.canon.get().expect("a key has a canonical form").member;
                let mut v: Vec<usize> = (0..self.defs.len()).collect();
                v.sort_unstable_by(|&i, &j| {
                    (member[i], &self.defs[i].name).cmp(&(member[j], &self.defs[j].name))
                });
                v
            })
        }

        /// The order of two groups of one canonical form by their definitions' names, listed by
        /// [`Checked::by_name`]. Time linear in the definitions.
        fn names_order(&self, other: &Checked) -> std::cmp::Ordering {
            let (ma, mb) = (
                &self.canon.get().expect("a key has a canonical form").member,
                &other
                    .canon
                    .get()
                    .expect("a key has a canonical form")
                    .member,
            );
            let a = self.by_name().iter().map(|&i| (ma[i], &self.defs[i].name));
            let b = other
                .by_name()
                .iter()
                .map(|&i| (mb[i], &other.defs[i].name));
            let c = a.cmp(b);
            if c.is_ne() {
                return c;
            }
            // A hash collision must not equate different named graphs. All roots share
            // one visited set so a shared body is not walked once per definition.
            let roots = self
                .by_name()
                .iter()
                .zip(other.by_name())
                .map(|(&i, &j)| (&*self.bodies[i], &*other.bodies[j]));
            spelled_roots(
                roots,
                &self.defs,
                &other.defs,
                self.spells(),
                other.spells(),
            )
        }
    }

    impl Canon {
        /// The order of two groups' canonical forms, after their digests: the classes in order,
        /// each by its head, its children's classes and the type it holds by digest; the pairs of
        /// types that tie in digest are pushed to `types` ([`Key::order`]). Time linear in the
        /// classes.
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
                // Under `blind` this answer is the only one for two groups whose forms tie in
                // digest, since `Key::order` then skips the names: the emptiness search would give
                // them one number. Reached there, on the children's classes, by
                // `l01_37a_short_addresses::collide::an_emptiness_search_tells_apart_groups_whose_forms_tie`.
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
    fn canon(bodies: &[Arc<Node>], names: &[u64]) -> Canon {
        // Complexity tradeoff (COMPLEXITY.md K72): the naive canonical form numbers each member
        // by a walk of its own reachable part, O(N) per member and O(N²) on one strongly
        // connected component; numbering by written order is O(N) but makes a reordered group a
        // second type. Used: color refinement with Hopcroft's smaller-half rule
        // (`crate::refine`; Hopcroft 1971, doi:10.1016/b978-0-12-417750-5.50022-1, cited at the
        // head of `refine.rs`), O((N + M) log N), plus the O(N log N) comparisons of the starting
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
                vertex[n.at as usize] = zed_collections::index::to_u32(of.len(), "vertices");
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
        // Each vertex's head and number of children, read once and not at each of the sort's
        // O(V log V) comparisons (PERF-parity-cold-verdict: `Fresh::new` of the parity verdict
        // bench 452.2 M to 374.4 M instructions at k = 4096, 3,798.8 M to 3,086.4 M at 32768);
        // only a tie of two types calls `Type::cmp`.
        let keys: Vec<((u8, usize, &str), usize)> = of
            .iter()
            .map(|n| (n.e.head(), n.e.kids().count()))
            .collect();
        let head = |a: usize, b: usize| {
            keys[a]
                .cmp(&keys[b])
                .then_with(|| match (&of[a].e, &of[b].e) {
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
        // An operand of a meet or a union is at no position: `A & B` and `B & A` are one type, so
        // their nodes are of one class (item GROUP-search-canon-key), and so are `A | B` and
        // `B | A` (FAIL-codex-r3-order-seed). Every color below `next + widest` then has a place,
        // as `Refine` needs.
        let position = |&(u, k, _): &(usize, usize, usize)| {
            if of[u].e.unordered() { 0 } else { k }
        };
        let widest = places.iter().map(|p| position(p) + 1).max().unwrap_or(0);
        for (e, p) in places.iter().enumerate() {
            color[v + e] = next + position(p);
        }
        next += widest;
        // The graph built and refined by `refine_places`, whose degree bound counts the places
        // of a meet or a union, all of one color, into one class.
        let color = crate::refine::refine_places(color, next, v, places.iter().map(|p| (p.0, p.2)));
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
                let mut kids: Vec<u32> = n.e.kids().map(|c| class_of(target(c))).collect();
                if n.e.unordered() {
                    // The operands' classes in their order, not the node's, so the form does
                    // not depend on which node of the class comes first.
                    // Complexity tradeoff (COMPLEXITY.md K102): the naive form keeps the
                    // written order, O(k) for a meet or union of k operands, but then `A & B`
                    // and `B & A` are two forms, as are `A | B` and `B | A`; sorting costs
                    // O(k log k) per meet or union, once per form.
                    kids.sort_unstable();
                }
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
                Shape::Ref(j, _) => mix(2, names[*j]),
                // The operands of a meet or a union in the order of their spellings, so that
                // `A & B` and `B & A` spell alike and are one part (item GROUP-search-canon-key),
                // and so do `A | B` and `B | A` (FAIL-codex-r3-order-seed).
                e if e.unordered() => {
                    let mut kids: Vec<u64> = e.kids().map(|c| spell[c.at as usize]).collect();
                    // Complexity tradeoff (COMPLEXITY.md K102): hashing in the written order is
                    // O(k) for k operands but depends on that order; the sort is O(k log k).
                    kids.sort_unstable();
                    kids.into_iter().fold(e.name_tag(), mix)
                }
                e => e
                    .kids()
                    .fold(e.name_tag(), |h, c| mix(h, spell[c.at as usize])),
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
    /// nodes of one class hold equal ones. The operands of a meet or a union are paired in the
    /// order of their spelling hashes (`xh`, `yh`, by node number), as [`canon`] hashes them, so
    /// that the order they are written in does not count; operands whose hashes tie keep their
    /// written order, which decides only where two spellings collide in hash. Time linear in the
    /// nodes, besides a sort of each meet's or union's operands.
    ///
    /// Tests (PROOF-kernel-proofdoc3a-gaps (l)): pairing by hash, not by written order, is
    /// checked by `l01_23_groups_and_refusals::refusals::reordered_union_arms_give_equal_members`
    /// and `::codex_r3_order_seed_10489595623140704143_trial_26` (unions), and for meets only by
    /// verdict, in
    /// `l01_23_groups_and_refusals::group_oracle::meets_whose_parts_differ_in_order_agree_across_orders`
    /// and `cycle_dup::many_meets_written_in_two_orders_are_read_as_written_once`. No test
    /// reaches a hash tie: with 64-bit hashes none occurs in practice, and the short-address
    /// build's collision tests (`l01_37a_short_addresses`) do not take this path.
    fn spelled<'a>(
        (x, xs, xh): (&'a Node, &'a [Def], &[u64]),
        (y, ys, yh): (&'a Node, &'a [Def], &[u64]),
    ) -> std::cmp::Ordering {
        spelled_roots([(x, y)], xs, ys, xh, yh)
    }

    /// Compares retained spellings, with one visited set across all the roots.
    // Complexity tradeoff: comparing d roots independently can read a shared N-node DAG
    // d times, O(d*N). One set of pairs visits each pair once across every root, with
    // O(pairs) memory; meet operands still need their spelling-order sorts.
    fn spelled_roots<'a>(
        roots: impl IntoIterator<Item = (&'a Node, &'a Node)>,
        xs: &'a [Def],
        ys: &'a [Def],
        xh: &[u64],
        yh: &[u64],
    ) -> std::cmp::Ordering {
        fn head<'a>(n: &'a Node, defs: &'a [Def]) -> (u8, usize, &'a str) {
            match &n.e {
                Shape::Ref(i, _) => (2, 0, defs[*i].name.as_str()),
                e => e.head(),
            }
        }
        let mut stack: Vec<(&'a Node, &'a Node)> = roots.into_iter().collect();
        stack.reverse();
        let mut visited = std::collections::HashSet::new();
        while let Some((x, y)) = stack.pop() {
            if !visited.insert((x.at, y.at)) {
                continue;
            }
            let c = (head(x, xs).cmp(&head(y, ys)))
                .then_with(|| x.e.kids().count().cmp(&y.e.kids().count()));
            if c.is_ne() {
                return c;
            }
            if x.e.unordered() {
                // Complexity tradeoff (COMPLEXITY.md K102): pairing in place order is O(k), but
                // depends on the written order; the sort by hash costs O(k log k) per meet or
                // union pair, so the walk stays O(N log N) in the nodes, and a hash tie falls back
                // to the written order, which then decides only between colliding spellings.
                let by_hash = |n: &'a Node, h: &[u64]| {
                    let mut kids: Vec<&'a Node> = n.e.kids().map(|c| &**c).collect();
                    kids.sort_by_key(|c| h[c.at as usize]);
                    kids
                };
                stack.extend(
                    by_hash(x, xh)
                        .into_iter()
                        .rev()
                        .zip(by_hash(y, yh).into_iter().rev()),
                );
            } else if !matches!(x.e, Shape::Ref(..)) {
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
