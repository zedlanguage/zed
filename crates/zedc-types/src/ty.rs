//! The checker's types (step L1.26): a kernel type for the scalars and atoms, structured
//! tuples, function signatures, type variables, and the unknown type `_` of a value no rule
//! has typed yet (a port's lines, a pattern's bound names).
//!
//! A type is a union of pieces: the values of one scalar carrier, the atoms, one tuple shape,
//! one function, one type variable, or the unknown. An operator or a function applies to each
//! combination of its arguments' pieces, so `int | f64` plus `int` is checked as `int + int`
//! and `f64 + int`.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use zed_kernel::digest::Digest;
use zed_kernel::frames::{Deep, Stack};
pub use zed_kernel::types::names::{Names, ProgramNames, fresh_name};
use zed_kernel::types::order;
use zed_kernel::types::{Refusal, Spell, TextPlace, Type as KType, Verdict, defs};
use zed_kernel::{Items, Universe, Value};

use zedc_syntax::lex::Span;

/// A type.
#[derive(Clone, Eq)]
pub struct Ty {
    /// The scalars and atoms, and the kind-wide part: every tuple or every struct as `(..)`
    /// and `{..}` write them (L1.40d), and what narrowing leaves of those. A tuple shape built
    /// from values is in `tuples`, and a function in `fns`.
    pub set: KType,
    /// The tuple shapes, each with its components.
    pub tuples: Members<Row>,
    /// The functions.
    pub fns: Members<Arc<Sig>>,
    /// The type variables.
    pub vars: VarSet,
    /// Whether the type holds the unknown `_`.
    pub dynamic: bool,
    /// The atoms of `set` that are members of a named atom family: data, which `else` keeps
    /// and an operator rejects (sec:failure). The other atoms are loose.
    pub family: KType,
    /// What the payloads of its atoms hold, by atom name: the shapes the atoms were built
    /// with, or `None` where that is not known. The payload of an atom whose name is not
    /// listed is not known.
    pub payloads: BTreeMap<Arc<str>, Option<Vec<Shape>>>,
}

/// The type variables of a type, by name, in the order of the names: a persistent set, which
/// copies share, with the sum of the hashes of its names kept as it changes.
///
/// Complexity tradeoff (FAIL-types-binding-union-copied): naive version, a `BTreeSet`, copied
/// whole with the type and hashed name by name. A variable bound to one more piece is bound to
/// the union of what it was bound to and that piece ([`Binds::unite`]), which copied the
/// type and hashed it for the binding's digest: one variable taking `n` variables as members
/// cost `1 + 2 + … + n`, O(n^2). Used: `imbl::OrdSet` (a B-tree whose nodes copies share, as
/// [`Binds`]'s map), copied in O(1), a name added or removed in O(log n), copying only the
/// nodes on its path; and the wrapping sum of the names' hashes, kept as names are added and
/// removed, so a type is hashed in O(1) for its variables, and two sets of different sums or
/// sizes compare unequal in O(1). Given up: a constant factor on each lookup and insert
/// (reference-counted nodes of 16 names), and one hash of a name per insert.
#[derive(Clone, Default)]
pub struct VarSet {
    set: imbl::OrdSet<Arc<str>>,
    /// The sum, wrapping, of [`name_digest`] of each name.
    digest: u64,
}

/// The hash of the name `v`, a term of [`VarSet`]'s digest.
fn name_digest(v: &str) -> u64 {
    use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
    BuildHasherDefault::<DefaultHasher>::default().hash_one(v)
}

impl VarSet {
    /// No variable.
    pub fn new() -> VarSet {
        VarSet::default()
    }

    /// The names, in order.
    pub fn iter(&self) -> imbl::ordset::Iter<'_, Arc<str>, imbl::shared_ptr::DefaultSharedPtr> {
        self.set.iter()
    }

    /// The number of names.
    pub fn len(&self) -> usize {
        self.set.len()
    }

    /// Whether it holds no name.
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }

    /// Whether it holds `v`.
    pub fn contains(&self, v: &str) -> bool {
        self.set.contains(v)
    }

    /// The first name.
    pub fn first(&self) -> Option<&Arc<str>> {
        self.set.get_min()
    }

    /// Adds `v`, giving whether it was not there.
    pub fn insert(&mut self, v: Arc<str>) -> bool {
        let d = name_digest(&v);
        let new = self.set.insert(v).is_none();
        if new {
            self.digest = self.digest.wrapping_add(d);
        }
        new
    }

    /// Removes `v`, giving whether it was there.
    pub fn remove(&mut self, v: &str) -> bool {
        let there = self.set.remove(v).is_some();
        if there {
            self.digest = self.digest.wrapping_sub(name_digest(v));
        }
        there
    }

    /// Keeps the names `f` keeps: found in one walk and removed after, O(n + d log n) for `d`
    /// removed (the set lends no mutable walk).
    pub fn retain(&mut self, mut f: impl FnMut(&Arc<str>) -> bool) {
        let drop: Vec<Arc<str>> = self.iter().filter(|v| !f(v)).cloned().collect();
        for v in &drop {
            self.remove(v);
        }
    }

    /// Adds the names of `other`: the smaller set's names into a copy of the larger, so
    /// O(m log n) for `m` names of the smaller.
    pub fn add_all(&mut self, other: &VarSet) {
        if other.len() > self.len() {
            let small = std::mem::replace(self, other.clone());
            self.extend(small.iter().cloned());
        } else {
            self.extend(other.iter().cloned());
        }
    }
}

impl PartialEq for VarSet {
    fn eq(&self, other: &VarSet) -> bool {
        self.digest == other.digest && self.len() == other.len() && self.set == other.set
    }
}

impl Eq for VarSet {}

impl std::hash::Hash for VarSet {
    /// Hashes the size and the sum of the names' hashes, in O(1).
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.len().hash(h);
        self.digest.hash(h);
    }
}

impl fmt::Debug for VarSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl Extend<Arc<str>> for VarSet {
    fn extend<I: IntoIterator<Item = Arc<str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(|v| {
            self.insert(v);
        });
    }
}

impl FromIterator<Arc<str>> for VarSet {
    fn from_iter<I: IntoIterator<Item = Arc<str>>>(iter: I) -> VarSet {
        let mut out = VarSet::new();
        out.extend(iter);
        out
    }
}

impl<'a> IntoIterator for &'a VarSet {
    type Item = &'a Arc<str>;
    type IntoIter = imbl::ordset::Iter<'a, Arc<str>, imbl::shared_ptr::DefaultSharedPtr>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// The tuple shapes or the functions of a type, in the order they were added: a persistent
/// list, which copies share, with the sum of the hashes of its members and, once asked for, a
/// persistent set of its members, kept as it grows.
///
/// Complexity tradeoff (COMPLEXITY.md F202): naive version, a `Vec`,
/// copied whole with the type, hashed member by member, and searched through a hash set built
/// from all of it at each union. A variable bound to one more piece is bound to the union of
/// what it was bound to and that piece ([`Binds::unite`]): one variable taking `n` distinct
/// tuple shapes cost `1 + 2 + … + n` in copies, set entries and hashes, O(n^2) (32.3x
/// instructions at 8n). Used: one shared node holding an `imbl::Vector` (a tree whose nodes
/// copies share), copied in O(1) and pushed onto in O(log n), copying the nodes on its path;
/// the wrapping sum of the members' hashes, kept as members are added, so a type is hashed in
/// O(1) for its shapes and two lists of different sums or lengths compare unequal in O(1);
/// and an `imbl::HashSet` of the members, made the first time a union asks whether a member
/// is there (O(n) once) and then kept as members are pushed and shared with the copies, so a
/// union of one more shape costs O(log n). Given up: a constant factor on each read through
/// the tree (nodes of 64 members), one hash per member pushed, and no slice of the members (a
/// caller that needs one copies them out, O(n)). An empty list is no node, so a type with no
/// shapes, the common case, costs one word and no allocation, as an empty `Vec` cost three.
/// A removal drops the set, and the next union that asks makes it again.
pub struct Members<T: Clone + std::hash::Hash + Eq>(Option<Arc<MembersData<T>>>);

/// The node of a nonempty [`Members`].
#[derive(Clone)]
struct MembersData<T: Clone + std::hash::Hash + Eq> {
    list: imbl::Vector<T>,
    /// The sum, wrapping, of [`member_digest`] of each member.
    digest: u64,
    /// The members, once a union has asked whether one is there.
    set: std::sync::OnceLock<imbl::HashSet<T>>,
}

/// The hash of a member of a [`Members`], a term of its digest: a row and a signature hash the
/// digest they keep, so O(1).
fn member_digest<T: std::hash::Hash>(x: &T) -> u64 {
    use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
    BuildHasherDefault::<DefaultHasher>::default().hash_one(x)
}

impl<T: Clone + std::hash::Hash + Eq> Members<T> {
    /// No member.
    pub fn new() -> Members<T> {
        Members(None)
    }

    /// The number of members.
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |d| d.list.len())
    }

    /// Whether it holds no member.
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// Whether another copy holds the same list, so that a member may be met through either:
    /// what each member's own count said when every copy kept its own list ([`Same`]).
    fn shared(&self) -> bool {
        self.0.as_ref().is_some_and(|d| Arc::strong_count(d) > 1)
    }

    /// The members, in order.
    pub fn iter(&self) -> MembersIter<'_, T> {
        MembersIter(self.0.as_ref().map(|d| d.list.iter()))
    }

    /// The member at `i`, in O(log n).
    pub fn get(&self, i: usize) -> Option<&T> {
        self.0.as_ref()?.list.get(i)
    }

    /// The first member.
    pub fn first(&self) -> Option<&T> {
        self.0.as_ref()?.list.front()
    }

    /// The last member.
    pub fn last(&self) -> Option<&T> {
        self.0.as_ref()?.list.back()
    }

    /// The only member, if it holds one only.
    pub fn only(&self) -> Option<&T> {
        (self.len() == 1).then(|| self.first()).flatten()
    }

    /// The members, copied out, for a caller that needs a slice: O(n).
    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    /// The node, made unique and present: a shared node is copied, in O(1) for its tree.
    fn data(&mut self) -> &mut MembersData<T> {
        Arc::make_mut(self.0.get_or_insert_with(|| {
            Arc::new(MembersData {
                list: imbl::Vector::new(),
                digest: 0,
                set: std::sync::OnceLock::new(),
            })
        }))
    }

    /// Adds `x` at the end.
    pub fn push(&mut self, x: T) {
        let d = self.data();
        d.digest = d.digest.wrapping_add(member_digest(&x));
        if let Some(set) = d.set.get_mut() {
            set.insert(x.clone());
        }
        d.list.push_back(x);
    }

    /// Adds `x` at the end if it is not a member, giving whether it was not: the set of the
    /// members is made now if it was not, O(n) once, and kept after, so O(log n).
    pub fn insert_new(&mut self, x: T) -> bool {
        if self.contains(&x) {
            return false;
        }
        self.push(x);
        true
    }

    /// Whether `x` is a member: the set of the members is made now if it was not.
    pub fn contains(&self, x: &T) -> bool {
        self.0
            .as_ref()
            .is_some_and(|d| (d.set.get_or_init(|| d.list.iter().cloned().collect())).contains(x))
    }

    /// Removes the last member and gives it.
    pub fn pop(&mut self) -> Option<T> {
        let d = self.data();
        let x = d.list.pop_back();
        let empty = d.list.is_empty();
        if let Some(x) = &x {
            d.digest = d.digest.wrapping_sub(member_digest(x));
            d.set = std::sync::OnceLock::new();
        }
        if empty {
            self.0 = None;
        }
        x
    }

    /// Keeps the members `f` keeps, in order: O(n), a new list.
    pub fn retain(&mut self, mut f: impl FnMut(&T) -> bool) {
        if self.iter().all(&mut f) {
            return;
        }
        *self = self.iter().filter(|x| f(x)).cloned().collect();
    }

    /// The members, moved out where the node is not shared: its set is dropped first, so each
    /// member is held by the list only, and a caller taking a type apart member by member
    /// (`drop_types`) holds the only reference to it.
    pub fn into_vec(self) -> Vec<T> {
        let Some(d) = self.0 else { return Vec::new() };
        match Arc::try_unwrap(d) {
            Ok(MembersData { list, set, .. }) => {
                drop(set);
                list.into_iter().collect()
            }
            Err(d) => d.list.iter().cloned().collect(),
        }
    }
}

impl<T: Clone + std::hash::Hash + Eq> Clone for Members<T> {
    fn clone(&self) -> Members<T> {
        Members(self.0.clone())
    }
}

impl<T: Clone + std::hash::Hash + Eq> Default for Members<T> {
    fn default() -> Members<T> {
        Members(None)
    }
}

impl<T: Clone + std::hash::Hash + Eq> std::ops::Index<usize> for Members<T> {
    type Output = T;

    fn index(&self, i: usize) -> &T {
        self.get(i).expect("an index within the list")
    }
}

impl<T: Clone + std::hash::Hash + Eq> PartialEq for Members<T> {
    /// Member by member, in order; lists of different lengths or sums of hashes in O(1).
    fn eq(&self, other: &Members<T>) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some(a), Some(b)) => {
                Arc::ptr_eq(a, b)
                    || (a.digest == b.digest
                        && a.list.len() == b.list.len()
                        && a.list.iter().zip(&b.list).all(|(x, y)| x == y))
            }
            _ => false,
        }
    }
}

impl<T: Clone + std::hash::Hash + Eq> Eq for Members<T> {}

impl<T: Clone + std::hash::Hash + Eq> std::hash::Hash for Members<T> {
    /// Hashes the length and the sum of the members' hashes, in O(1).
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.len().hash(h);
        self.0.as_ref().map_or(0, |d| d.digest).hash(h);
    }
}

impl<T: Clone + std::hash::Hash + Eq + fmt::Debug> fmt::Debug for Members<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Clone + std::hash::Hash + Eq> Extend<T> for Members<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(|x| self.push(x));
    }
}

impl<T: Clone + std::hash::Hash + Eq> FromIterator<T> for Members<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Members<T> {
        let mut out = Members::new();
        out.extend(iter);
        out
    }
}

impl<T: Clone + std::hash::Hash + Eq> From<Vec<T>> for Members<T> {
    fn from(v: Vec<T>) -> Members<T> {
        v.into_iter().collect()
    }
}

impl<'a, T: Clone + std::hash::Hash + Eq> IntoIterator for &'a Members<T> {
    type Item = &'a T;
    type IntoIter = MembersIter<'a, T>;

    fn into_iter(self) -> MembersIter<'a, T> {
        self.iter()
    }
}

impl<T: Clone + std::hash::Hash + Eq> IntoIterator for Members<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> std::vec::IntoIter<T> {
        self.into_vec().into_iter()
    }
}

/// The members of a [`Members`], in order.
pub struct MembersIter<'a, T>(
    Option<imbl::vector::Iter<'a, T, imbl::shared_ptr::DefaultSharedPtr>>,
);

impl<'a, T> Iterator for MembersIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.0.as_mut()?.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.as_ref().map_or((0, Some(0)), |i| i.size_hint())
    }
}

impl<T> DoubleEndedIterator for MembersIter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.as_mut()?.next_back()
    }
}

impl<T> ExactSizeIterator for MembersIter<'_, T> {}

impl<T: Clone> Clone for MembersIter<'_, T> {
    fn clone(&self) -> Self {
        MembersIter(self.0.clone())
    }
}

/// The components of a tuple shape, kept in one shared node with what they hold at any depth,
/// found from the components' rows when the row is made. A row is copied in constant time, so
/// a type is copied in the time of its outer level; and a check that walks into tuples reads
/// a row where it would walk into it, so a tuple nested `n` deep costs `O(n)` in all, not
/// `O(n)` at each level.
// Complexity tradeoff (COMPLEXITY.md row F89): naive version, a row held by value and walked
// at each level, O(n^2) for a tuple nested n deep (three walks of the whole type per level
// in `Ck::finish`). Used: one shared node holding what the row holds at any depth (its
// variables merged small into large, whether a tuple expression checked it, its first
// unchecked function), copied in O(1), each read O(1). Tradeoffs: those facts are made with
// every row, read or not, and a reference count per row.
#[derive(Clone)]
pub struct Row(Arc<RowData>);

struct RowData {
    cs: Vec<Ty>,
    /// Its number, which no other row or shape made in this process has ([`NodeId`]).
    id: NodeId,
    /// The hash of the components.
    digest: u64,
    /// Whether a component holds a type variable or the unknown, outside functions, at any
    /// depth, in payloads too: whether [`Ty::closed`] fails on one.
    open: bool,
    /// Whether a component holds the unknown, outside functions, at any depth, in payloads too.
    dynamic: bool,
    /// The first function, not a family, that a component holds at any depth.
    held: Option<Arc<Sig>>,
    /// The first function, not a family, that a component holds at any depth and no tuple
    /// expression has checked as data: none for a row that [`Self::checked`] says was.
    unchecked: Option<Arc<Sig>>,
    /// Whether no component holds a type variable, a function or a payload, at any depth:
    /// replacing variables keeps the row whole.
    fixed: bool,
    /// Whether every type variable it holds outside functions, at any depth, was checked as
    /// data when the row was made: set only for the row of a tuple expression, whose
    /// components are each checked as data first.
    data: bool,
    /// Whether this row, or the row it was made from by replacing variables, is the row of a
    /// tuple expression: a function it held then was reported at that tuple, and a function
    /// that took the place of a variable since is reported by the variable's data need.
    checked: bool,
    /// The variables a component holds at any depth, inside functions and payloads too, as
    /// bits ([`VarBits`]): so replacing variables keeps whole a row that holds none of them.
    bits: VarBits,
    /// The kernel type of the tuple shape ([`Row::kernel`]): none when a component holds a
    /// function, a variable or the unknown at any depth.
    kernel: Option<KType>,
    /// The kernel type of the tuple shape with its atoms' payloads read ([`Ty::exact_data`]):
    /// none where [`Self::kernel`] has none.
    exact: Option<KType>,
    /// The one value of the tuple shape, when each component is one value ([`Ty::point`]).
    point: Option<Value>,
    /// Whether each component is one value that its text writes as that value
    /// ([`Ty::is_one_value`]): a scalar literal, a bare atom, an atom whose payload is one
    /// value, or a tuple of such values. The tuple shape is then one value too.
    one: bool,
    /// The first kind-wide part, `(..)` or `{..}`, a component holds at any depth outside
    /// functions, in payloads too: a part that may hold a function ([`Ty::held_wide`]).
    wide: Option<KType>,
    /// Whether a component lists no value ([`Ty::lists_nothing`]): the row has no value, and
    /// [`Ty::of_row`] makes the empty type of it.
    void: bool,
    /// Whether a component lists the payloads of an atom at any depth outside functions: when
    /// not, [`Self::exact`] is [`Self::kernel`].
    listed: bool,
    /// Whether a component, at any depth outside functions, in payloads too, holds the atoms
    /// of every name it does not list ([`Ty::open_atoms`]).
    open_atoms: bool,
    /// Whether a value of a component may hold a function with needs ([`Ty::may_hold_needs`]).
    needs: bool,
    /// Whether a component holds, at any depth, inside functions and payloads too, the unknown
    /// beside another member, which the printer writes as `_` alone ([`Ty::may_absorb`]).
    absorbs: bool,
    /// The class of each component and its value where it is one value ([`class`]), and what
    /// is read from them to file the row, found the first time the row is filed
    /// ([`Row::keys`]) and kept.
    keys: std::sync::OnceLock<Keys>,
}

impl Row {
    /// The row of `cs`.
    pub fn new(cs: Vec<Ty>) -> Row {
        Row::made(cs, false, false)
    }

    /// The row of `cs`, each checked as data.
    pub fn of_data(cs: Vec<Ty>) -> Row {
        Row::made(cs, true, true)
    }

    /// The row of `cs`, which took the place of this row's components when variables were
    /// replaced: its variables' data needs are met anew, and a function it holds is reported
    /// as this row's would be.
    fn replaced(&self, cs: Vec<Ty>) -> Row {
        Row::made(cs, false, self.0.checked)
    }

    fn made(cs: Vec<Ty>, data: bool, checked: bool) -> Row {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let digest = BuildHasherDefault::<DefaultHasher>::default().hash_one(&cs);
        // Each component's rows and payload shapes keep what they hold at any depth, so this
        // reads the components' outer levels.
        let open = cs.iter().any(|c| !c.closed());
        let dynamic = cs.iter().any(Ty::holds_unknown);
        let held = cs.iter().find_map(|c| c.held_function().cloned());
        let unchecked = match checked {
            true => None,
            false => cs.iter().find_map(|c| c.unchecked_function().cloned()),
        };
        let mut bits = VarBits::default();
        cs.iter().for_each(|c| bits.ty(c));
        let fixed = cs.iter().all(|c| {
            c.vars.is_empty()
                && c.fns.is_empty()
                && c.payloads.is_empty()
                && c.tuples.iter().all(|r| r.0.fixed)
        });
        // Each component's kernel type reads the kernel types its rows keep, so it costs the
        // component's outer level. A row that holds a variable or the unknown has none.
        let kernel = match open {
            true => None,
            false => (cs.iter().map(Ty::kernel))
                .collect::<Option<Vec<_>>>()
                .map(KType::tuple),
        };
        // A row with no payload listed at any depth reads no payload, so its exact kernel
        // type is its kernel type, made once.
        let listed = cs
            .iter()
            .any(|c| !c.payloads.is_empty() || c.tuples.iter().any(|r| r.0.listed));
        let exact = match (&kernel, listed) {
            (None, _) => None,
            (Some(k), false) => Some(k.clone()),
            (Some(_), true) => (cs.iter().map(Ty::exact_data))
                .collect::<Option<Vec<_>>>()
                .map(KType::tuple),
        };
        // Each component's rows keep their own, so this reads the components' outer levels.
        let point = (cs.iter().map(Ty::point))
            .collect::<Option<Vec<_>>>()
            .map(Value::tuple);
        // A point is one value; each component's rows and shapes keep their own, so this
        // reads the components' outer levels.
        let one = point.is_some() || cs.iter().all(Ty::is_one_value);
        let wide = cs.iter().find_map(Ty::held_wide);
        let open_atoms = cs.iter().any(Ty::open_atoms);
        // Complexity tradeoff: as in `KType::tuple`, only a component that lists no value
        // makes the row void; one that only the kernel's search proves empty keeps the row.
        // Why: the search costs up to the size of the component per row made; this is O(1)
        // per component. Trigger: a component empty by a meet or recursion. Tests:
        // `l01_26_type_resolution::never::a_tuple_with_an_empty_component_is_never`.
        // COMPLEXITY.md C34.
        let void = cs.iter().any(Ty::lists_nothing);
        // Complexity tradeoff (FAIL-l01-26-deep-bench-bytes): the naive version, the checker
        // walking every tuple below a call's result at each call (`type_holds_needs`), is
        // Θ(n^2) for n nested calls that each put the last result in a tuple (37.1 times the
        // bytes at 8n). Used: each row keeps the answer, made from its components' outer
        // levels and their rows' and shapes' answers, O(width) per row, with each function's answer kept
        // on it ([`Sig::may_hold_needs`]). Tradeoff: every row pays for it when made, read or not.
        let needs = cs.iter().any(Ty::may_hold_needs);
        let absorbs = cs.iter().any(Ty::may_absorb);
        Row(Arc::new(RowData {
            cs,
            id: NodeId::next(),
            digest,
            open,
            dynamic,
            held,
            unchecked,
            fixed,
            data,
            checked,
            bits,
            kernel,
            exact,
            point,
            one,
            wide,
            void,
            listed,
            open_atoms,
            needs,
            absorbs,
            keys: std::sync::OnceLock::new(),
        }))
    }

    /// The kernel type of the tuple shape, `(t1, …, tn)` of its components' kernel types
    /// ([`Ty::kernel`]), or none when a component holds a function, a variable or the unknown
    /// at any depth. Made with the row, from the kernel types the components' rows keep, so
    /// each row's is made once, whatever the paths to it: `d(positional x) = (x, x)` called
    /// `n` times nested gives `n` rows each holding the one below twice, `2^n` paths, which a
    /// walk into the components took `2^n` time for at each call (TUPLE-eq-dup).
    // Complexity tradeoff (COMPLEXITY.md row F109): naive version, a walk into the components
    // at each call, O(2^n) for that family. Used: made once with the row from its components'
    // kept kernel types, O(1) per read. Tradeoff: every row pays for its kernel type when it is
    // made, whether or not it is read, and keeps it.
    fn kernel(&self) -> Option<KType> {
        self.0.kernel.clone()
    }

    /// Whether a component holds a type variable or the unknown, outside functions, at any
    /// depth, in payloads too.
    pub fn open(&self) -> bool {
        self.0.open
    }

    /// Whether a component holds the unknown, outside functions, at any depth, in payloads too.
    pub fn dynamic(&self) -> bool {
        self.0.dynamic
    }

    /// Whether every type variable it holds outside functions was checked as data when the
    /// row was made.
    pub fn data(&self) -> bool {
        self.0.data
    }

    /// Its address: the same for each path to a shared row, so a walk visits it once.
    pub fn addr(&self) -> *const () {
        Arc::as_ptr(&self.0).cast()
    }

    /// The class of each component and its value where it is one value ([`class`]), by which
    /// tuples are filed ([`Holders`], [`Groups`], [`Choices`]). Found once per row, the first
    /// time it is asked for, and kept: filing a row again, in another walk or against another
    /// type, reads them instead of working out each component's class from its set again,
    /// which cost about 17,000 instructions a tuple of two components (TY-row-class). Filing a
    /// tuple of two components now costs about 8.4k to 9.7k instructions the first time and 1.9k
    /// to 2.9k after, the same from 16 to 4,096 tuples: the filings are hash maps (TY-row-hash).
    fn keys(&self) -> &Keys {
        self.0
            .keys
            .get_or_init(|| Keys::new(self.0.cs.iter().map(class).collect()))
    }

    /// Its number, the same for each path to a shared row and never another row's or shape's.
    pub fn node(&self) -> NodeId {
        self.0.id
    }

    /// Whether a component holds a variable at any depth, inside functions and payloads too.
    pub fn holds_vars(&self) -> bool {
        !self.0.bits.is_empty()
    }

    /// The components, to change.
    pub fn to_vec(&self) -> Vec<Ty> {
        self.0.cs.clone()
    }

    /// Whether a text written at `at` is parenthesized: a tuple alone as an arrow's key,
    /// `((int, int)) ->? V`, since `(int, int) ->? V` has two parameters; `(int,) ->? V` has
    /// one.
    fn wraps(&self, at: PrintAt) -> bool {
        at == PrintAt::Key && self.len() != 1
    }

    /// Pushes the parts of its text, standing at `at`, to `parts`, in order.
    fn parts<'a>(&'a self, at: PrintAt, parts: &mut Vec<Print<'a>>) {
        let wrap = self.wraps(at);
        parts.push(Print::Text(if wrap { "((" } else { "(" }));
        let mut one = true;
        for c in self.iter() {
            between(parts, &mut one, ", ");
            parts.push(Print::Ty(c, PrintAt::Any));
        }
        parts.push(Print::Text(match (self.len() == 1, wrap) {
            (true, _) => ",)",
            (false, true) => "))",
            (false, false) => ")",
        }));
    }
}

/// The number of a row or payload shape, given when it is made from one count for the whole
/// process: no two rows or shapes have the same one, and a node that is dropped does not pass
/// its number on to a later one, as it may pass on its address. A memo that outlives one walk,
/// and so may outlive a node it holds, is keyed by it (`Ck::data`, `Ck::bound`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(u64);

impl NodeId {
    /// The next number.
    fn next() -> NodeId {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        NodeId(NEXT.fetch_add(1, Ordering::Relaxed))
    }
}

impl std::ops::Deref for Row {
    type Target = [Ty];
    fn deref(&self) -> &[Ty] {
        &self.0.cs
    }
}

impl<'a> IntoIterator for &'a Row {
    type Item = &'a Ty;
    type IntoIter = std::slice::Iter<'a, Ty>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.cs.iter()
    }
}

impl FromIterator<Ty> for Row {
    fn from_iter<I: IntoIterator<Item = Ty>>(it: I) -> Row {
        Row::new(it.into_iter().collect())
    }
}

impl PartialEq for Row {
    /// Compares the components as [`Ty`]'s `==` does, with no stack as deep as the row: two
    /// equal rows built apart share no node, and a comparison that recursed once a level
    /// overflowed an 8 MiB stack a few tens of thousands of levels deep (ROW-eq-deep).
    fn eq(&self, other: &Row) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || {
            let mut lazy = Lazy::default();
            let equal = self.0.alike(&other.0)
                && (self.0.cs.iter().zip(&other.0.cs)).all(|(a, b)| outer(&mut lazy, a, b));
            lazy.rest(equal)
        }
    }
}

impl RowData {
    /// Whether it and `other` have equal hashes and as many components: what [`Row`]'s `==`
    /// checks before it compares the components.
    #[inline]
    fn alike(&self, other: &RowData) -> bool {
        self.digest == other.digest && self.cs.len() == other.cs.len()
    }
}

impl PartialEq for Ty {
    /// Compares the two types at their outer level, and the rows, payload shapes and functions
    /// they hold with a `Same`, made only for a pair of these that is not one node: with no
    /// stack as deep as the types, and, for types that hold none, the common case, as cheaply
    /// as the derived `==` did. Inlined, as the derived `==` was, so a caller in another crate
    /// compares the outer level without a call.
    #[inline]
    fn eq(&self, other: &Ty) -> bool {
        let mut lazy = Lazy::default();
        let equal = outer(&mut lazy, self, other);
        lazy.rest(equal)
    }
}

impl std::hash::Hash for Ty {
    /// Hashes each part in turn; a row, payload shape or signature by the hash it keeps.
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        let Ty {
            set,
            tuples,
            fns,
            vars,
            dynamic,
            family,
            payloads,
        } = self;
        set.hash(h);
        tuples.hash(h);
        fns.hash(h);
        vars.hash(h);
        dynamic.hash(h);
        family.hash(h);
        payloads.hash(h);
    }
}

impl Ty {
    /// Whether it holds a row, a payload shape or a function, which `==` descends into.
    fn holds_nodes(&self) -> bool {
        !self.tuples.is_empty()
            || !self.fns.is_empty()
            || (!self.payloads.is_empty() && self.payloads.values().any(Option::is_some))
    }
}

/// A comparison of two types, two rows, two payload shapes or two signatures, which needs no
/// stack as deep as the types: `==` on types nested as deep as the program.
///
/// Each type is compared at its outer level, and the pairs of components of the rows, shapes
/// and signatures it holds are compared by recursion while the thread's stack has room
/// ([`Same::room`]); where it has none, they are pushed on `left`, to be compared once the
/// recursion has returned. Shallow types, the common case, are so compared as a plain
/// recursion compares them, with nothing pushed and no allocation.
///
/// Two nodes, one from each side, are assumed equal once their pair is met, and the pairs of
/// nodes found equal so are kept as classes in a union-find (Hopcroft and Karp's test of
/// equivalence): a pair whose nodes are already in one class is not compared again. Each pair
/// of recorded nodes compared joins two classes, so at most one is compared for each node, and
/// the comparison costs the size of the two types as graphs, not as trees: two types each
/// holding `n` nodes and `2^n` paths, built apart, cost `O(n)`. The assumption holds: if every
/// pair met is found equal at its outer level, the classes relate only equal nodes, as the
/// types hold no cycles; and a pair that differs makes `==` false.
///
/// A node is known by its address. Every node it records is reachable from the two operands
/// `==` borrows, so none is freed, and no address is reused, while the comparison runs.
///
/// A pair of nodes neither of which is shared (one owner each, `Arc::strong_count` 1) is not
/// recorded, so a comparison of types built once and never shared allocates no table. A row or
/// function in a list of a type's members ([`Members`]) that copies of the type share counts
/// as shared, though the list is its one owner: a copy of a type shares the list, not each
/// member, and `(t, t)` holds `t`'s rows through one list twice. Before
/// (FAIL-types-binding-tuple-shapes-copied), each copy kept its own list, so the members' own
/// counts said it; read from them alone, two types of 40 doubled levels built apart did not
/// compare in two minutes. The cost
/// stays linear: an unshared node is reached only through its one owner, so it is compared once
/// each time the nearest recorded node above it is; each recorded node is compared again only
/// when its pair joins two classes, and the joins form a forest over the recorded nodes, so each
/// join can be charged to a node of its own (its child end), which pays for the unshared nodes
/// below it, each of which lies below one recorded node only. The records only save work: they
/// are never needed for the answer, as the types hold no cycles.
///
/// A function counts as unshared in the same way when its other owners are only the rows and
/// shapes on the path to it, which keep it as their held or unchecked function (`above`,
/// [`Same::shared_sigs`]): those are not met again below it, so a function held once, in a
/// type built once, is not recorded either.
///
/// Complexity tradeoff: naive version, the derived `==`, one recursion per level, O(paths):
/// `2^n` for two types of `n` shared nodes built apart (n = 2,000 did not finish in 60 s), and
/// a stack overflow at 100,000 levels on 2 MiB. Used: the union-find above, O((n + m) α) for
/// types of `n` and `m` nodes as graphs, with recursion while the stack has room and `left`
/// after. Tradeoffs: the table's memory, one entry per shared node met; nodes are keyed by
/// address, which is sound only because the borrowed operands keep every recorded node alive
/// for the whole comparison (the table never outlives it); the `Arc::strong_count` test that
/// skips unshared nodes is a constant-factor saving, not needed for the answer.
/// COMPLEXITY.md row F118.
#[derive(Default)]
struct Same<'a> {
    /// The lowest stack address the recursion descends from ([`Same::room`]), set when it first
    /// descends; 0 before.
    floor: usize,
    /// The pairs of types left to compare, pushed where the stack had no room, each with the
    /// `above` of its path, so a function below it is counted as shared as it would be had
    /// the recursion reached it.
    left: Vec<(&'a Ty, &'a Ty, [Above; 2])>,
    /// The union-find forest, by address: for each node met, the node it was joined to, or
    /// itself, and, for the root of a class, the number of nodes in it. One table, so the
    /// first node recorded costs one allocation. Every key is the address of a row, shape or
    /// function reachable from the two operands `==` borrows, so none is freed while the table
    /// lives, and the table is only read by key, never iterated.
    ids: HashMap<*const (), (*const (), usize), std::hash::BuildHasherDefault<AddressHasher>>,
    /// The functions the rows and shapes on the path to the pair now compared keep as held or
    /// unchecked, on the left and on the right ([`Same::shared_sigs`]).
    above: [Above; 2],
}

/// The stack [`Same`]'s recursion may take, from where it first descends: a small part of the
/// 2 MiB a thread is given by default, so the caller and what the comparison calls at its
/// deepest (`==` on scalar types, sets of variables and payload maps) keep the rest.
const SAME_STACK: usize = 128 << 10;

impl<'a> Same<'a> {
    /// Whether the pairs left, and those they push, are each equal.
    fn rest(mut self) -> bool {
        // A pair pushed is compared under the `above` of its path, as the recursion would
        // have compared it. Compared under none, as before, a function below a cut that fell
        // between two rows or shapes keeping it was counted as shared and recorded, so the
        // table's size followed where the cuts fell: `levels(n)` of the deep_ops benchmarks
        // recorded none at n = 20,000 and 3,136 functions at 160,000 (`bench::deep_ops::
        // fits_sig_takes_linear_time_in_the_depth`, bytes 30.9x). Cost: two `Above` a pair
        // pushed.
        // Assumption, not proved: a function whose only owners are its list and the rows and
        // shapes counted in the restored `above` is reached only along this path, so leaving
        // it out of the table loses no repeat the table would have caught. It is the same
        // assumption the recursion makes before any cut; the evidence is the l01_26 and l01_23
        // tests and the recording counts (0 at n = 20,000 to 160,000 with the fix), not a
        // proof that a pair popped here has no other way down to the function.
        while let Some((a, b, above)) = self.left.pop() {
            self.above = above;
            if !outer(&mut self, a, b) {
                return false;
            }
        }
        true
    }

    /// Whether either of `x` and `y` has another owner, so the comparison may meet it again.
    fn shared<T>(x: &Arc<T>, y: &Arc<T>) -> bool {
        Arc::strong_count(x) > 1 || Arc::strong_count(y) > 1
    }

    /// Whether either of the signatures `x` and `y` has an owner other than the type that
    /// holds it and the rows and shapes on the path to it that keep it as held or unchecked.
    /// Those rows and shapes keep the first function they hold, so a signature in a row is
    /// never alone; counted as shared, each would be recorded, and a comparison of types that
    /// hold functions and share no node would allocate a table. A signature no other node owns
    /// is met only through the type that holds it, as an unshared row is.
    fn shared_sigs(&self, x: &Arc<Sig>, y: &Arc<Sig>) -> bool {
        let [l, r] = self.above;
        Arc::strong_count(x) > 1 + l.keeping(x) || Arc::strong_count(y) > 1 + r.keeping(y)
    }

    /// `then` run with `above` set for a pair under rows or shapes whose held and unchecked
    /// functions are `x` on the left and `y` on the right, and restored after.
    #[inline]
    fn under(
        &mut self,
        x: [&Option<Arc<Sig>>; 2],
        y: [&Option<Arc<Sig>>; 2],
        then: impl FnOnce(&mut Self) -> bool,
    ) -> bool {
        let [l, r] = self.above;
        self.above = [l.under(x), r.under(y)];
        let equal = then(self);
        self.above = [l, r];
        equal
    }

    /// Whether the signatures `x` and `y` are equal, field by field in the order the derived
    /// `==` took; the types of their arrows are compared by [`Same::descend`]. Their needs are
    /// compared by `==` on each type they hold, each comparison a `Same` of its own: a need's
    /// types are variables of the signature, or the types of a call's arguments, which nest
    /// only as deep as the call's text. `facts` is a cache, equal to any other.
    fn sig(&mut self, x: &'a Sig, y: &'a Sig) -> bool {
        let Sig {
            params,
            arrows,
            bounds,
            data,
            dense,
            keys,
            word,
            needs,
            own,
            held,
            named,
            hull,
            facts: _,
        } = x;
        *params == y.params
            && *hull == y.hull
            && *keys == y.keys
            && arrows.len() == y.arrows.len()
            && (arrows.iter().zip(&y.arrows)).all(|(p, q)| {
                p.params.len() == q.params.len()
                    && p.partial == q.partial
                    && self.descend(
                        (p.params.iter().zip(&q.params)).chain([(&p.result, &q.result)]),
                    )
            })
            && *bounds == y.bounds
            && *data == y.data
            && *dense == y.dense
            && *word == y.word
            // No needs, the common case, and the slice compare is not free.
            && ((needs.is_empty() && y.needs.is_empty()) || *needs == y.needs)
            && *own == y.own
            && *held == y.held
            && *named == y.named
    }

    /// Whether each of `pairs` is equal, or, for a pair whose left type holds a row, shape or
    /// function and where the stack has no room ([`Same::room`]), may be: such a pair is
    /// pushed on `left`. A pair whose left type holds none is compared now, as that pushes
    /// nothing.
    fn descend(&mut self, pairs: impl IntoIterator<Item = (&'a Ty, &'a Ty)>) -> bool {
        match self.room() {
            true => pairs.into_iter().all(|(a, b)| outer(self, a, b)),
            false => pairs.into_iter().all(|(a, b)| match a.holds_nodes() {
                true => {
                    self.left.push((a, b, self.above));
                    true
                }
                false => outer(self, a, b),
            }),
        }
    }

    /// Whether the stack has room to recurse a level deeper: whether the address of this frame
    /// lies above `floor`, [`SAME_STACK`] below where the recursion first descended.
    // Complexity tradeoff: none is given up. Whether a pair is compared by recursion or pushed
    // on `left` changes where it is compared, never the answer or the order of growth, which
    // is linear in the size of the two types as graphs either way; each pair pushed is compared
    // by `rest`, from the top of the stack again. Recursion is the faster: it keeps a shallow
    // type, the common case, as cheap to compare as the derived `==` was
    // (l01_26_type_resolution bench::deep_types::shallow_types_compare_as_cheaply_as_a_plain_recursion).
    // The switch is on the stack the recursion has taken, which bounds it whatever the types'
    // depth: types 100,000 deep compare on a 2 MiB stack
    // (types_built_apart_100000_deep_compare_on_a_2_mib_stack). The stack the thread has left
    // is not read: the crates that read it (`stacker`, `libc`) cannot be linked into this
    // dylib as well as into the test binaries. COMPLEXITY F118.
    #[inline]
    fn room(&mut self) -> bool {
        let mark = 0u8;
        let here = std::ptr::addr_of!(mark) as usize;
        if self.floor == 0 {
            self.floor = here.saturating_sub(SAME_STACK).max(1);
        }
        here > self.floor
    }

    /// Whether the rows `x` and `y`, two nodes found alike, are already in one class, or equal
    /// in each component.
    fn alike_rows(&mut self, x: &'a Row, y: &'a Row, listed: bool) -> bool {
        let (x, y) = (&x.0, &y.0);
        ((listed || Self::shared(x, y))
            && self.assumed(Arc::as_ptr(x).cast(), Arc::as_ptr(y).cast()))
            || match x.held.is_some() {
                // A row that holds no function, the common case, keeps none.
                false => self.descend(x.cs.iter().zip(&y.cs)),
                true => self.under([&x.held, &x.unchecked], [&y.held, &y.unchecked], |s| {
                    s.descend(x.cs.iter().zip(&y.cs))
                }),
            }
    }

    /// Whether the payload shapes `x` and `y`, two nodes found alike, are already in one
    /// class, or equal in each component and field.
    fn alike_shapes(&mut self, x: &'a Shape, y: &'a Shape) -> bool {
        (Self::shared(&x.0, &y.0)
            && self.assumed(Arc::as_ptr(&x.0).cast(), Arc::as_ptr(&y.0).cast()))
            || {
                let named = std::cell::Cell::new(true);
                let (x, y) = (&x.0, &y.0);
                let equal = match x.held.is_some() {
                    false => self.descend(x.pairs(y, &named)),
                    true => self.under([&x.held, &x.unchecked], [&y.held, &y.unchecked], |s| {
                        s.descend(x.pairs(y, &named))
                    }),
                };
                equal && named.get()
            }
    }

    /// Whether the nodes at `x` and `y`, two nodes at least one of them shared, are already in
    /// one class; if not, their classes are joined, so the caller compares them now and no
    /// later pair does again.
    fn assumed(&mut self, x: *const (), y: *const ()) -> bool {
        let (i, j) = (self.root(x), self.root(y));
        if i == j {
            return true;
        }
        // Union by size, the smaller class under the larger.
        let (si, sj) = (self.ids[&i].1, self.ids[&j].1);
        let (small, large) = match si < sj {
            true => (i, j),
            false => (j, i),
        };
        self.ids.insert(small, (large, si.min(sj)));
        self.ids.insert(large, (large, si + sj));
        false
    }

    /// The root of the class of the node at `x`, which is met here first if it is new; the
    /// path to it is halved.
    fn root(&mut self, x: *const ()) -> *const () {
        let mut up = self.ids.entry(x).or_insert((x, 1)).0;
        let mut i = x;
        while up != i {
            let above = self.ids[&up].0;
            self.ids.insert(i, (above, 0));
            i = above;
            up = self.ids[&i].0;
        }
        i
    }
}

/// How [`outer`] compares the rows, payload shapes and functions two types hold.
trait Nodes<'a> {
    /// Whether the rows `x` and `y` are equal, or, where the comparison is put off, may be;
    /// `listed` when the list of either is shared ([`Members::shared`]), so either row may be
    /// met again though it has one owner.
    fn row(&mut self, x: &'a Row, y: &'a Row, listed: bool) -> bool;
    /// Whether the payload shapes `x` and `y` are equal, or may be.
    fn shape(&mut self, x: &'a Shape, y: &'a Shape) -> bool;
    /// Whether the functions `x` and `y` are equal, or may be; `listed` as for rows.
    fn func(&mut self, x: &'a Arc<Sig>, y: &'a Arc<Sig>, listed: bool) -> bool;
}

/// Whether `a` and `b` are equal at their outer level, field by field in the order the derived
/// `==` took, and in the rows, payload shapes and functions they hold, which `n` compares.
#[inline]
fn outer<'a>(n: &mut impl Nodes<'a>, a: &'a Ty, b: &'a Ty) -> bool {
    let Ty {
        set,
        tuples,
        fns,
        vars,
        dynamic,
        family,
        payloads,
    } = a;
    *set == b.set
        && tuples.len() == b.tuples.len()
        && {
            let listed = tuples.shared() || b.tuples.shared();
            (tuples.iter().zip(&b.tuples)).all(|(x, y)| n.row(x, y, listed))
        }
        && fns.len() == b.fns.len()
        && {
            let listed = fns.shared() || b.fns.shared();
            (fns.iter().zip(&b.fns)).all(|(x, y)| n.func(x, y, listed))
        }
        && *vars == b.vars
        && *dynamic == b.dynamic
        && *family == b.family
        && payloads.len() == b.payloads.len()
        // An empty map is the common case, and its iterator is not free.
        && (payloads.is_empty()
            || (payloads.iter().zip(&b.payloads)).all(|((k, x), (l, y))| {
                k == l
                    && match (x, y) {
                        (Some(x), Some(y)) => {
                            x.len() == y.len() && x.iter().zip(y).all(|(p, q)| n.shape(p, q))
                        }
                        (None, None) => true,
                        (Some(_), None) | (None, Some(_)) => false,
                    }
            }))
}

/// How `==` starts: a pair of rows, payload shapes or functions that is one node is equal, and
/// the first pair that is not makes the [`Same`] that compares it and the rest. Most types
/// the checker compares hold none, and no `Same` is made for them.
#[derive(Default)]
struct Lazy<'a>(Option<Same<'a>>);

impl<'a> Lazy<'a> {
    /// The `Same`, made now if it was not.
    fn same(&mut self) -> &mut Same<'a> {
        self.0.get_or_insert_with(Same::default)
    }

    /// Whether `equal`, what the comparison found before the pairs the `Same` put off, holds,
    /// and those pairs are each equal. It takes the `Lazy`, so no path drops it apart.
    #[inline]
    fn rest(self, equal: bool) -> bool {
        match self.0 {
            None => equal,
            // Nothing was put off unless the types are deep, so the call is skipped.
            Some(same) => equal && (same.left.is_empty() || same.rest()),
        }
    }
}

impl<'a> Nodes<'a> for Lazy<'a> {
    // Inlined into a caller in another crate, with `Ty`'s `==`: the checks that settle the
    // common pairs, one node or two that differ, take no call.
    #[inline]
    fn row(&mut self, x: &'a Row, y: &'a Row, listed: bool) -> bool {
        Arc::ptr_eq(&x.0, &y.0) || (x.0.alike(&y.0) && self.same().alike_rows(x, y, listed))
    }

    #[inline]
    fn shape(&mut self, x: &'a Shape, y: &'a Shape) -> bool {
        Arc::ptr_eq(&x.0, &y.0) || (x.0.alike(&y.0) && self.same().alike_shapes(x, y))
    }

    #[inline]
    fn func(&mut self, x: &'a Arc<Sig>, y: &'a Arc<Sig>, listed: bool) -> bool {
        Arc::ptr_eq(x, y) || self.same().func(x, y, listed)
    }
}

impl<'a> Nodes<'a> for Same<'a> {
    /// One node, already in one class, or alike and equal in each component.
    fn row(&mut self, x: &'a Row, y: &'a Row, listed: bool) -> bool {
        Arc::ptr_eq(&x.0, &y.0) || (x.0.alike(&y.0) && self.alike_rows(x, y, listed))
    }

    /// One node, already in one class, or alike and equal in each component and field.
    fn shape(&mut self, x: &'a Shape, y: &'a Shape) -> bool {
        Arc::ptr_eq(&x.0, &y.0) || (x.0.alike(&y.0) && self.alike_shapes(x, y))
    }

    /// One node, already in one class, or equal as signatures ([`Same::sig`]).
    fn func(&mut self, x: &'a Arc<Sig>, y: &'a Arc<Sig>, listed: bool) -> bool {
        Arc::ptr_eq(x, y)
            || ((listed || self.shared_sigs(x, y))
                && self.assumed(Arc::as_ptr(x).cast(), Arc::as_ptr(y).cast()))
            || self.sig(x, y)
    }
}

/// On one side of a [`Same`], the function the row or shape just above the pair compared keeps
/// as held, by address, and how many references to it the rows and shapes in a run up to it
/// keep, as held or as unchecked: owners of a signature the comparison may meet that lie on its
/// path. A row's held function is the first its components hold, so the rows keeping a
/// function lie on the paths to it; each counted is a node of the path, and a run counts no
/// more references than there are. A function kept as unchecked only is not counted, and is
/// so taken for shared, which costs a record, never the answer.
#[derive(Clone, Copy, Default)]
struct Above {
    at: usize,
    run: usize,
}

impl Above {
    /// The same under a row or shape that keeps `held` and `unchecked`.
    #[inline]
    fn under(self, [held, unchecked]: [&Option<Arc<Sig>>; 2]) -> Above {
        let addr = |s: &Option<Arc<Sig>>| s.as_ref().map_or(0, |s| Arc::as_ptr(s).addr());
        let at = addr(held);
        let refs = usize::from(at != 0) + usize::from(at != 0 && addr(unchecked) == at);
        Above {
            at,
            run: refs + if at == self.at { self.run } else { 0 },
        }
    }

    /// How many references to `s` the rows and shapes it counts keep.
    #[inline]
    fn keeping(self, s: &Arc<Sig>) -> usize {
        if Arc::as_ptr(s).addr() == self.at {
            self.run
        } else {
            0
        }
    }
}

/// The hasher of [`Same`]'s table of nodes by address: one folded multiply of the address;
/// of [`Added`]'s names, one per byte.
#[derive(Default)]
struct AddressHasher(u64);

impl std::hash::Hasher for AddressHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_usize(usize::from(b));
        }
    }

    fn write_usize(&mut self, x: usize) {
        let p = u128::from(self.0 ^ x as u64) * 0x9e37_79b9_7f4a_7c15;
        self.0 = (p as u64) ^ ((p >> 64) as u64);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

impl Eq for Row {}

impl Drop for RowData {
    /// Drops the components on a stack of its own: a type nests as deep as the program, and the
    /// drop glue would recurse once per level, through tuples, functions and payloads. A row or
    /// signature another type still holds is left to it.
    fn drop(&mut self) {
        let sigs = [self.held.take(), self.unchecked.take()];
        drop_types(std::mem::take(&mut self.cs), sigs.into_iter().flatten());
    }
}

impl std::hash::Hash for Row {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.0.digest);
    }
}

impl fmt::Debug for Row {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_debug(Dbg::Row(self), f)
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_debug(Dbg::Ty(self), f)
    }
}

impl fmt::Debug for Sig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_debug(Dbg::Sig(self), f)
    }
}

/// A part of the `Debug` text of a type ([`write_debug`]).
enum Dbg<'a> {
    /// Text written as it is.
    Text(&'static str),
    /// A part that holds no type, written by its own `Debug`.
    Leaf(&'a dyn fmt::Debug),
    Ty(&'a Ty),
    Row(&'a Row),
    Shape(&'a Shape),
    Sig(&'a Sig),
    Need(&'a Need),
}

/// Writes `start` as a derived `Debug` writes it on one line, for `{:#?}` too. A type nests as
/// deep as the program, and the derived `Debug` recursed once a level (100,000 levels overflowed
/// a 2 MiB stack), so the writing keeps its own stack, as [`write_parts`] does: each part
/// expands to the parts it is made of, pushed so that they pop in order.
fn write_debug(start: Dbg, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut stack = vec![start];
    let mut parts = Vec::new();
    while let Some(d) = stack.pop() {
        match d {
            Dbg::Text(s) => f.write_str(s)?,
            Dbg::Leaf(x) => write!(f, "{x:?}")?,
            Dbg::Ty(t) => debug_ty(t, &mut parts),
            Dbg::Row(r) => debug_list(&mut parts, "[", r.iter(), "]", |p, t| p.push(Dbg::Ty(t))),
            Dbg::Shape(s) => {
                parts.push(Dbg::Text("Shape { items: "));
                debug_list(&mut parts, "[", &s.items, "]", |p, t| p.push(Dbg::Ty(t)));
                parts.push(Dbg::Text(", fields: "));
                debug_map(&mut parts, &s.fields);
                parts.push(Dbg::Text(" }"));
            }
            Dbg::Sig(s) => debug_sig(s, &mut parts),
            Dbg::Need(n) => debug_need(n, &mut parts),
        }
        stack.extend(parts.drain(..).rev());
    }
    Ok(())
}

/// Pushes `open`, the parts `each` pushes for each of `items`, separated by commas, and
/// `close`.
fn debug_list<'a, T>(
    parts: &mut Vec<Dbg<'a>>,
    open: &'static str,
    items: impl IntoIterator<Item = T>,
    close: &'static str,
    mut each: impl FnMut(&mut Vec<Dbg<'a>>, T),
) {
    parts.push(Dbg::Text(open));
    for (i, x) in items.into_iter().enumerate() {
        if i > 0 {
            parts.push(Dbg::Text(", "));
        }
        each(parts, x);
    }
    parts.push(Dbg::Text(close));
}

/// Pushes the parts of a map of names to types.
fn debug_map<'a>(parts: &mut Vec<Dbg<'a>>, m: &'a BTreeMap<Arc<str>, Ty>) {
    debug_list(parts, "{", m, "}", |p, (k, t)| {
        p.extend([Dbg::Leaf(k), Dbg::Text(": "), Dbg::Ty(t)]);
    });
}

fn debug_ty<'a>(t: &'a Ty, parts: &mut Vec<Dbg<'a>>) {
    let Ty {
        set,
        tuples,
        fns,
        vars,
        dynamic,
        family,
        payloads,
    } = t;
    parts.extend([
        Dbg::Text("Ty { set: "),
        Dbg::Leaf(set),
        Dbg::Text(", tuples: "),
    ]);
    debug_list(parts, "[", tuples, "]", |p, r| p.push(Dbg::Row(r)));
    parts.push(Dbg::Text(", fns: "));
    debug_list(parts, "[", fns, "]", |p, s| p.push(Dbg::Sig(s)));
    parts.extend([
        Dbg::Text(", vars: "),
        Dbg::Leaf(vars),
        Dbg::Text(", dynamic: "),
        Dbg::Leaf(dynamic),
        Dbg::Text(", family: "),
        Dbg::Leaf(family),
        Dbg::Text(", payloads: "),
    ]);
    debug_list(parts, "{", payloads, "}", |p, (k, shapes)| {
        p.extend([Dbg::Leaf(k), Dbg::Text(": ")]);
        match shapes {
            None => p.push(Dbg::Text("None")),
            Some(shapes) => {
                p.push(Dbg::Text("Some("));
                debug_list(p, "[", shapes, "]", |p, s| p.push(Dbg::Shape(s)));
                p.push(Dbg::Text(")"));
            }
        }
    });
    parts.push(Dbg::Text(" }"));
}

fn debug_sig<'a>(s: &'a Sig, parts: &mut Vec<Dbg<'a>>) {
    let Sig {
        params,
        arrows,
        bounds,
        data,
        dense,
        keys,
        word,
        needs,
        own,
        held,
        named,
        hull,
        facts,
    } = s;
    parts.extend([
        Dbg::Text("Sig { params: "),
        Dbg::Leaf(params),
        Dbg::Text(", arrows: "),
    ]);
    debug_list(parts, "[", arrows, "]", |p, a| {
        p.push(Dbg::Text("Arrow { params: "));
        debug_list(p, "[", &a.params, "]", |p, t| p.push(Dbg::Ty(t)));
        p.extend([
            Dbg::Text(", result: "),
            Dbg::Ty(&a.result),
            Dbg::Text(", partial: "),
            Dbg::Leaf(&a.partial),
            Dbg::Text(" }"),
        ]);
    });
    parts.extend([
        Dbg::Text(", bounds: "),
        Dbg::Leaf(bounds),
        Dbg::Text(", data: "),
        Dbg::Leaf(data),
        Dbg::Text(", dense: "),
        Dbg::Leaf(dense),
        Dbg::Text(", keys: "),
        Dbg::Leaf(keys),
        Dbg::Text(", word: "),
        Dbg::Leaf(word),
        Dbg::Text(", needs: "),
    ]);
    debug_list(parts, "[", needs, "]", |p, n| p.push(Dbg::Need(n)));
    parts.extend([
        Dbg::Text(", own: "),
        Dbg::Leaf(own),
        Dbg::Text(", held: "),
        Dbg::Leaf(held),
        Dbg::Text(", named: "),
        Dbg::Leaf(named),
        Dbg::Text(", hull: "),
        Dbg::Leaf(hull),
        Dbg::Text(", facts: "),
        Dbg::Leaf(facts),
        Dbg::Text(" }"),
    ]);
}

/// Pushes the parts of a need. A kind that holds no type is written by its derived `Debug`;
/// each is named, so that a kind added with a type is written here.
fn debug_need<'a>(n: &'a Need, parts: &mut Vec<Dbg<'a>>) {
    parts.extend([
        Dbg::Text("Need { on: "),
        Dbg::Ty(&n.on),
        Dbg::Text(", kind: "),
    ]);
    match &n.kind {
        NeedKind::Component { i, key, .. } => parts.extend([
            Dbg::Text("Component { i: "),
            Dbg::Leaf(i),
            Dbg::Text(", key: "),
            Dbg::Ty(key),
            Dbg::Text(" }"),
        ]),
        NeedKind::Index(t) => parts.extend([Dbg::Text("Index("), Dbg::Ty(t), Dbg::Text(")")]),
        NeedKind::Map { f, filter } => parts.extend([
            Dbg::Text("Map { f: "),
            Dbg::Ty(f),
            Dbg::Text(", filter: "),
            Dbg::Leaf(filter),
            Dbg::Text(" }"),
        ]),
        NeedKind::Group { f, recv } => parts.extend([
            Dbg::Text("Group { f: "),
            Dbg::Ty(f),
            Dbg::Text(", recv: "),
            Dbg::Leaf(recv),
            Dbg::Text(" }"),
        ]),
        NeedKind::Level { word, f, site } => parts.extend([
            Dbg::Text("Level { word: "),
            Dbg::Leaf(word),
            Dbg::Text(", f: "),
            Dbg::Ty(f),
            Dbg::Text(", site: "),
            Dbg::Leaf(site),
            Dbg::Text(" }"),
        ]),
        NeedKind::Remap { at, src, .. } => parts.extend([
            Dbg::Text("Remap { at: "),
            Dbg::Leaf(at),
            Dbg::Text(", src: "),
            Dbg::Ty(src),
            Dbg::Text(" }"),
        ]),
        NeedKind::Call {
            what,
            positional,
            named,
            curry,
        } => {
            parts.extend([Dbg::Text("Call { what: "), Dbg::Leaf(what)]);
            parts.push(Dbg::Text(", positional: "));
            debug_list(parts, "[", positional, "]", |p, t| p.push(Dbg::Ty(t)));
            parts.push(Dbg::Text(", named: "));
            debug_list(parts, "[", named, "]", |p, (k, t)| {
                p.extend([
                    Dbg::Text("("),
                    Dbg::Leaf(k),
                    Dbg::Text(", "),
                    Dbg::Ty(t),
                    Dbg::Text(")"),
                ]);
            });
            parts.extend([Dbg::Text(", curry: "), Dbg::Leaf(curry), Dbg::Text(" }")]);
        }
        NeedKind::Fold { tys, right, by } => {
            parts.push(Dbg::Text("Fold { tys: "));
            debug_list(parts, "[", tys, "]", |p, t| p.push(Dbg::Ty(t)));
            parts.extend([
                Dbg::Text(", right: "),
                Dbg::Leaf(right),
                Dbg::Text(", by: "),
                Dbg::Leaf(by),
                Dbg::Text(" }"),
            ]);
        }
        NeedKind::Into { what, ty } => parts.extend([
            Dbg::Text("Into { what: "),
            Dbg::Leaf(what),
            Dbg::Text(", ty: "),
            Dbg::Ty(ty),
            Dbg::Text(" }"),
        ]),
        NeedKind::Narrow(Narrow::Not(t)) => {
            parts.extend([Dbg::Text("Narrow(Not("), Dbg::Ty(t), Dbg::Text("))")]);
        }
        NeedKind::SumMethod { site, beside } => parts.extend([
            Dbg::Text("SumMethod { site: "),
            Dbg::Leaf(site),
            Dbg::Text(", beside: "),
            Dbg::Ty(beside),
            Dbg::Text(" }"),
        ]),
        NeedKind::Order {
            what,
            word,
            other,
            first,
        } => parts.extend([
            Dbg::Text("Order { what: "),
            Dbg::Leaf(what),
            Dbg::Text(", word: "),
            Dbg::Leaf(word),
            Dbg::Text(", other: "),
            Dbg::Ty(other),
            Dbg::Text(", first: "),
            Dbg::Leaf(first),
            Dbg::Text(" }"),
        ]),
        k @ (NeedKind::Destructure { .. }
        | NeedKind::Data(..)
        | NeedKind::Payload { .. }
        | NeedKind::Narrow(Narrow::Loose | Narrow::Atom(_))
        | NeedKind::NoInt(_)
        | NeedKind::Power(_)
        | NeedKind::Sum
        | NeedKind::Entries
        | NeedKind::Reduce(..)
        | NeedKind::InDomain { .. }) => parts.push(Dbg::Leaf(k)),
    }
    parts.push(Dbg::Text(", result: "));
    match &n.result {
        None => parts.push(Dbg::Text("None")),
        Some(t) => parts.extend([Dbg::Text("Some("), Dbg::Ty(t), Dbg::Text(")")]),
    }
    parts.extend([Dbg::Text(", span: "), Dbg::Leaf(&n.span), Dbg::Text(" }")]);
}

/// The payload an atom was built with, kept in one shared node with what it holds at any depth,
/// as a [`Row`] is: a shape is copied in constant time, so a type is copied in the time of its
/// outer level; and a walk that would enter a payload reads what the shape keeps instead, so
/// `n` atoms nested directly in atoms cost `O(n)` in all, not `O(n)` at each level
/// (ATOM-nested-sq).
// Complexity tradeoff (COMPLEXITY.md rows F106 and ATOM-payload-open, whose walks read
// whether a shape is open from what it keeps rather than with no visited set, O(2^n)):
// naive version, a payload held by value, so
// each copy of a type copies every payload under it, O(n^2) for n atoms nested in atoms since
// the checker keeps the type of each expression. Used: one shared node per payload, a copy
// in O(1), O(n) in all. Tradeoffs: a reference count and an indirection per payload; a change
// to a payload builds a new node.
#[derive(Clone)]
pub struct Shape(Arc<ShapeData>);

/// What a [`Shape`] holds.
pub struct ShapeData {
    /// Its components, by position.
    pub items: Vec<Ty>,
    /// Its fields, by name.
    pub fields: BTreeMap<Arc<str>, Ty>,
    /// Its number, which no other row or shape made in this process has ([`NodeId`]).
    id: NodeId,
    /// The hash of the components and fields.
    digest: u64,
    /// Whether a component or field holds a type variable or the unknown, outside functions,
    /// at any depth, in payloads too.
    open: bool,
    /// Whether a component or field holds the unknown, outside functions, at any depth, in
    /// payloads too.
    dynamic: bool,
    /// The first function, not a family, that a component or field holds at any depth.
    held: Option<Arc<Sig>>,
    /// The first function, not a family, that a component or field holds at any depth and no
    /// tuple expression has checked as data.
    unchecked: Option<Arc<Sig>>,
    /// Whether no component or field holds a type variable or a function at any depth:
    /// replacing variables, or settling them, keeps the shape whole.
    fixed: bool,
    /// The variables its components and fields hold at any depth, inside functions and
    /// payloads too, as bits (`VarBits`).
    bits: VarBits,
    /// The payload as a kernel type, with its atoms' payloads read: a tuple of its items.
    /// None when it has fields, which only a normal form with a mark of their names tells
    /// apart ([`Forms`]), or when a component holds a function, a variable or the unknown at
    /// any depth.
    exact: Option<KType>,
    /// The first kind-wide part a component or field holds at any depth outside functions.
    wide: Option<KType>,
    /// Whether a component or field, at any depth outside functions, holds the atoms of every
    /// name it does not list ([`Ty::open_atoms`]).
    open_atoms: bool,
    /// Whether a component or field lists no value ([`Ty::lists_nothing`]): no atom has this
    /// payload, and [`Ty::atom_of`] and the rebuilding walk leave it out.
    void: bool,
    /// Whether each component and field is one value that its text writes as that value
    /// ([`Ty::is_one_value`]): an atom with this payload is one value too, `#a(1)`.
    one: bool,
    /// Whether a value of a component or field may hold a function with needs
    /// ([`Ty::may_hold_needs`]), kept as a row keeps its own.
    needs: bool,
    /// Whether a component or field holds, at any depth, inside functions and payloads too,
    /// the unknown beside another member ([`Ty::may_absorb`]), kept as a row keeps its own.
    absorbs: bool,
    /// The class of each component and field and its value where it is one value ([`class`]),
    /// found the first time the shape is filed ([`near_pairs`]) and kept, as a row keeps its own.
    keys: std::sync::OnceLock<Keys>,
}

impl std::ops::Deref for Shape {
    type Target = ShapeData;
    fn deref(&self) -> &ShapeData {
        &self.0
    }
}

impl PartialEq for Shape {
    /// Compares the components and fields as a row does.
    fn eq(&self, other: &Shape) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || {
            let mut lazy = Lazy::default();
            let named = std::cell::Cell::new(true);
            let equal = self.0.alike(&other.0)
                && (self.0.pairs(&other.0, &named)).all(|(a, b)| outer(&mut lazy, a, b))
                && named.get();
            lazy.rest(equal)
        }
    }
}

impl ShapeData {
    /// Whether it and `other` have equal hashes and as many components and fields: what
    /// [`Shape`]'s `==` checks before it compares the components and fields.
    #[inline]
    fn alike(&self, other: &ShapeData) -> bool {
        self.digest == other.digest
            && self.items.len() == other.items.len()
            && self.fields.len() == other.fields.len()
    }

    /// Its components and fields, each paired with the one in the same place in `other`, up
    /// to the first field whose name differs, where `named` is set false.
    fn pairs<'a: 'b, 'b>(
        &'a self,
        other: &'a ShapeData,
        named: &'b std::cell::Cell<bool>,
    ) -> impl Iterator<Item = (&'a Ty, &'a Ty)> + 'b {
        let fields = (self.fields.iter().zip(&other.fields)).map_while(|((k, x), (l, y))| {
            let same = k == l;
            named.set(same);
            same.then_some((x, y))
        });
        (self.items.iter().zip(&other.items)).chain(fields)
    }
}

impl Eq for Shape {}

impl std::hash::Hash for Shape {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.0.digest);
    }
}

impl fmt::Debug for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_debug(Dbg::Shape(self), f)
    }
}

impl Drop for ShapeData {
    /// Drops the components and fields on a stack of their own, as a row does: payloads
    /// nest as deep as the program.
    fn drop(&mut self) {
        let mut stack = std::mem::take(&mut self.items);
        stack.extend(std::mem::take(&mut self.fields).into_values());
        drop_types(
            stack,
            [self.held.take(), self.unchecked.take()]
                .into_iter()
                .flatten(),
        );
    }
}

/// Drops the types `tys` and the signatures `sigs` on stacks of their own: the rows,
/// signatures and payload shapes no other type holds are opened and what they hold pushed,
/// the function a row or shape keeps as held and the signature a signature was settled into
/// among it, so dropping a type nested `n` deep needs no recursion `n` deep.
// Complexity tradeoff (COMPLEXITY.md row TY-write-stack, with `Sig::facts` and `Sig::digest`,
// which work out the functions held deepest first by `held_without`): naive version, the drop
// glue and plain recursion, O(n) time and O(n) frames of the thread's stack, which overflowed
// 2 MiB at 8,000 nested lambdas. Used: heap stacks, O(n) time and O(n) heap. Tradeoffs: the
// parts are moved onto a `Vec` before they drop, a constant factor; nothing is refused.
fn drop_types(mut tys: Vec<Ty>, sigs: impl IntoIterator<Item = Arc<Sig>>) {
    let mut sigs: Vec<Arc<Sig>> = sigs.into_iter().collect();
    loop {
        if let Some(s) = sigs.pop() {
            if let Some(mut s) = Arc::into_inner(s) {
                s.take_parts(&mut tys, &mut sigs);
            }
            continue;
        }
        let Some(mut t) = tys.pop() else { break };
        for r in std::mem::take(&mut t.tuples) {
            if let Some(mut d) = Arc::into_inner(r.0) {
                tys.append(&mut d.cs);
                sigs.extend([d.held.take(), d.unchecked.take()].into_iter().flatten());
            }
        }
        sigs.extend(std::mem::take(&mut t.fns).into_vec());
        for s in std::mem::take(&mut t.payloads)
            .into_values()
            .flatten()
            .flatten()
        {
            if let Some(mut d) = Arc::into_inner(s.0) {
                tys.append(&mut d.items);
                tys.extend(std::mem::take(&mut d.fields).into_values());
                sigs.extend([d.held.take(), d.unchecked.take()].into_iter().flatten());
            }
        }
    }
}

impl Drop for Sig {
    /// Drops its arrows, needs and settled signature on a stack of their own, as a row does:
    /// a function type nests functions as deep as the program, and the drop glue would recurse
    /// once per level through `Arc<Sig>` (8,000 nested lambdas overflowed a 2 MiB stack).
    fn drop(&mut self) {
        let (mut tys, mut sigs) = (Vec::new(), Vec::new());
        self.take_parts(&mut tys, &mut sigs);
        drop_types(tys, sigs);
    }
}

/// A parameter list as [`Sig::param_list`] gives it: for each parameter, whether it is passed
/// by position, and its name where it is not.
pub type ParamList = Vec<(bool, Option<Arc<str>>)>;

impl Sig {
    /// Moves the types and signatures it holds to `tys` and `sigs`, for [`drop_types`]: the
    /// types of its arrows and needs, and the signature it was settled into.
    fn take_parts(&mut self, tys: &mut Vec<Ty>, sigs: &mut Vec<Arc<Sig>>) {
        for a in std::mem::take(&mut self.arrows) {
            tys.extend(a.params);
            tys.push(a.result);
        }
        tys.extend(
            std::mem::take(&mut self.needs)
                .into_iter()
                .flat_map(Need::into_tys),
        );
        sigs.extend(self.facts.1.take());
    }
}

impl Shape {
    /// The payload of `items` by position and `fields` by name.
    ///
    /// What it keeps of its components and fields is read from their outer levels, and from
    /// what their rows and shapes keep, so it costs the size of their outer levels.
    pub fn new(items: Vec<Ty>, fields: BTreeMap<Arc<str>, Ty>) -> Shape {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let digest = BuildHasherDefault::<DefaultHasher>::default().hash_one((&items, &fields));
        let cs = || items.iter().chain(fields.values());
        let open = cs().any(|c| !c.closed());
        let dynamic = cs().any(Ty::holds_unknown);
        let fixed = cs().all(|c| {
            c.vars.is_empty()
                && c.fns.is_empty()
                && c.tuples.iter().all(|r| r.0.fixed)
                && c.payload_shapes().all(|s| s.fixed)
        });
        let held = cs().find_map(|c| c.held_function().cloned());
        let unchecked = cs().find_map(|c| c.unchecked_function().cloned());
        let mut bits = VarBits::default();
        cs().for_each(|c| bits.ty(c));
        // Each component's exact kernel type reads what its rows and shapes keep, so this
        // costs the outer levels of the components.
        let exact = match open || held.is_some() || !fields.is_empty() {
            true => None,
            false => (items.iter().map(Ty::exact_kernel))
                .collect::<Option<Vec<_>>>()
                .map(KType::tuple),
        };
        let wide = cs().find_map(Ty::held_wide);
        let open_atoms = cs().any(Ty::open_atoms);
        let void = cs().any(Ty::lists_nothing);
        let one = cs().all(Ty::is_one_value);
        let needs = cs().any(Ty::may_hold_needs);
        let absorbs = cs().any(Ty::may_absorb);
        Shape(Arc::new(ShapeData {
            items,
            fields,
            id: NodeId::next(),
            digest,
            held,
            unchecked,
            open,
            dynamic,
            fixed,
            bits,
            exact,
            wide,
            open_atoms,
            void,
            one,
            needs,
            absorbs,
            keys: std::sync::OnceLock::new(),
        }))
    }

    /// Whether a component or field holds a type variable or the unknown, outside functions,
    /// at any depth.
    pub fn open(&self) -> bool {
        self.0.open
    }

    /// Whether a component or field holds the unknown, outside functions, at any depth.
    pub fn dynamic(&self) -> bool {
        self.0.dynamic
    }

    /// Its number, the same for each path to a shared shape and never another shape's or row's.
    pub fn node(&self) -> NodeId {
        self.0.id
    }

    /// Whether a component or field holds a variable at any depth, inside functions and
    /// payloads too.
    pub fn holds_vars(&self) -> bool {
        !self.bits.is_empty()
    }

    /// The address of what it holds, which only tells one shared shape from another.
    pub fn as_ptr(&self) -> *const ShapeData {
        Arc::as_ptr(&self.0)
    }

    /// What it holds at `slot`, if it has that place.
    pub fn at(&self, slot: &Slot) -> Option<&Ty> {
        match slot {
            Slot::Field(n) => self.fields.get(n),
            Slot::Item(i) => self.items.get(*i),
        }
    }

    /// Pushes the parts of the text of the type of the atom `#name` with this payload to
    /// `parts`, in order: `#name(int, f: String)`.
    fn parts<'a>(&'a self, name: &'a str, parts: &mut Vec<Print<'a>>) {
        parts.push(Print::Text("#"));
        parts.push(Print::Text(name));
        parts.push(Print::Text("("));
        let mut first = true;
        for t in &self.items {
            between(parts, &mut first, ", ");
            // The family of an `#errs` is written bare, `#errs((#a | #b) ->? #a | #b)`.
            match t.fns.only() {
                Some(s) if name == "errs" && s.is_family() && *t == Ty::func(s.clone()) => {
                    parts.push(Print::Family(s));
                }
                _ => parts.push(Print::Ty(t, PrintAt::Any)),
            }
        }
        for (f, t) in &self.fields {
            between(parts, &mut first, ", ");
            parts.push(Print::Text(f));
            parts.push(Print::Text(": "));
            parts.push(Print::Ty(t, PrintAt::Any));
        }
        parts.push(Print::Text(")"));
    }
}

/// The payloads of the union of the types `ts`: each name's shapes, once each, and a name some
/// type may hold an unknown payload of is not known. That is found in one union of what of
/// each type's scalars and atoms its payloads do not describe, so the join costs one pass over
/// the types and their shapes.
fn join_payloads(ts: &[&Ty]) -> BTreeMap<Arc<str>, Option<Vec<Shape>>> {
    let mut out: BTreeMap<Arc<str>, Option<Vec<Shape>>> = BTreeMap::new();
    let mut seen: HashSet<(&str, &Shape)> = HashSet::new();
    let mut rest = Vec::new();
    for t in ts {
        let listed = t
            .payloads
            .keys()
            .map(|n| KType::atom_with(n, &KType::top()));
        rest.push(&t.set - &KType::union_all(listed));
        for (n, ss) in &t.payloads {
            let entry = out.entry(n.clone()).or_insert_with(|| Some(Vec::new()));
            match (entry, ss) {
                (entry, None) => *entry = None,
                (Some(have), Some(ss)) => {
                    have.extend(ss.iter().filter(|s| seen.insert((n, s))).cloned());
                }
                (None, Some(_)) => {}
            }
        }
    }
    let rest = KType::union_all(rest);
    for (n, ss) in out.iter_mut() {
        if holds_payload(&rest, n) {
            *ss = None;
        }
    }
    out
}

/// Whether `set` may hold an atom named `n` with a payload.
fn holds_payload(set: &KType, n: &str) -> bool {
    !(set & &KType::atom_with(n, &KType::top())).is_empty()
}

/// A value no program writes, one for each `name`: the bare atom of a name that starts with
/// a NUL, which no atom written has. Marks of two names are apart. The normal form of payloads
/// and tuples ([`Forms`]) puts one where a payload's fields end and one for each function
/// compared, and takes the marks out of each component that holds the atoms of every name it
/// does not list ([`Forms::cut`]), so only the same mark holds a mark.
///
/// Not a function of the kernel, which no component holds either: the kernel builds no value
/// of a function type in a union of payloads, so `#a(x: 0, f: (int) -> int) | … <: #a(x: int,
/// f: (int) -> String)` was refused for want of a value, and that search grew as `n^1.6`.
fn mark(name: &str) -> KType {
    KType::atom(name)
}

/// The name of the mark of the field names of a payload with fields, in name order.
fn fields_mark(fields: &BTreeMap<Arc<str>, Ty>) -> String {
    let mut name = String::from("\u{0}fields");
    for f in fields.keys() {
        name.push(' ');
        name.push_str(f);
    }
    name
}

/// The kernel type of a payload of the components `ks`, items then fields: a tuple of them,
/// and, when it has fields, after them a mark of the fields' names, so that a payload with
/// fields is held only by one with the same names, or by a payload not known.
fn payload_form(mut ks: Vec<KType>, fields: &BTreeMap<Arc<str>, Ty>) -> KType {
    if !fields.is_empty() {
        ks.push(mark(&fields_mark(fields)));
    }
    KType::tuple(ks)
}

/// `set` with the payloads `payloads` lists read: each listed atom of `set` holds the payloads
/// `form` gives of its shapes (and none other), and an atom whose payload is not known any
/// payload. None when `form` gives none for a shape.
///
/// Each name costs a meet and a union with the payloads of its shapes, so the set costs the
/// size of its listed payloads, not the product of the names and their shapes.
fn payload_set(
    set: &KType,
    payloads: &BTreeMap<Arc<str>, Option<Vec<Shape>>>,
    mut form: impl FnMut(&Arc<str>, &Shape) -> Option<KType>,
) -> Option<KType> {
    let mut listed = Vec::new();
    let mut read = Vec::new();
    for (n, ss) in payloads {
        let Some(ss) = ss else { continue };
        let all = KType::atom_with(n, &KType::top());
        let p = ss.iter().map(|s| form(n, s)).collect::<Option<Vec<_>>>()?;
        // A payload of no value is left out, so a name whose payloads hold none is built as
        // empty: the kernel then has no union of empty rows to prove empty one by one.
        let p: Vec<KType> = p.into_iter().filter(|k| *k != KType::empty()).collect();
        if !p.is_empty() {
            read.push(&(set & &all) & &KType::atom_with(n, &KType::union_all(p)));
        }
        listed.push(all);
    }
    if listed.is_empty() {
        return Some(set.clone());
    }
    let rest = set - &KType::union_all(listed);
    Some(KType::union_all(std::iter::once(rest).chain(read)))
}

/// A walk that rebuilds the types it is given from what they hold at every depth:
/// [`Ty::subst`], [`Ty::settle`] and the replacements of [`Ty::replace_in`] each say through
/// these methods what they keep whole, what they give again from a memo and what they put in
/// the place of a variable, and [`rebuild`] walks.
trait Rebuild {
    /// What the type `t` is made into without entering it, if it is.
    fn known_ty(&mut self, t: &Ty) -> Option<Ty>;
    /// What the row `r` is made into without entering it, if it is: kept whole, or made before.
    fn known_row(&mut self, r: &Row) -> Option<Row>;
    /// Notes that the row `r`, entered, was made into `out`.
    fn made_row(&mut self, r: &Row, out: &Row);
    /// What the payload shape `s` is made into without entering it, if it is.
    fn known_shape(&mut self, s: &Shape) -> Option<Shape>;
    /// Notes that the payload shape `s`, entered, was made into `out`.
    fn made_shape(&mut self, s: &Shape, out: &Shape);
    /// What the function `s` a type holds is made into without entering it, if it is. If not,
    /// the walk enters it next and leaves it by [`Self::made_held`].
    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>>;
    /// The function `s`, entered, with its arrows and needs made into `arrows` and `needs`.
    fn made_held(&mut self, s: &Arc<Sig>, arrows: Vec<Arrow>, needs: Vec<Need>) -> Arc<Sig>;
    /// What the variable `v` is replaced by, if it is.
    fn binding(&self, v: &str) -> Option<Cow<'_, Ty>>;
    /// The set of scalars, atoms and kind-wide part made of the set `s` a type holds: `s`
    /// itself, unless the walk widens it ([`Ty::carriers`]).
    fn made_set(&mut self, s: KType) -> KType {
        s
    }
    /// The type made of a type entered, its parts made and its variables bound: `t` itself,
    /// unless the walk changes it again ([`Absorb`]).
    fn made_ty(&mut self, t: Ty) -> Ty {
        t
    }
}

/// A step of [`rebuild`]: a part to enter, or a part whose parts are made, to be made from them.
enum Step<'a> {
    Ty(&'a Ty),
    Row(&'a Row),
    Shape(&'a Shape),
    Held(&'a Arc<Sig>),
    TyDone(&'a Ty),
    RowDone(&'a Row),
    ShapeDone(&'a Shape),
    HeldDone(&'a Arc<Sig>),
}

/// What [`rebuild`] made, each kind on a stack of its own, the last made last.
#[derive(Default)]
struct Rebuilt {
    tys: Vec<Ty>,
    rows: Vec<Row>,
    shapes: Vec<Shape>,
    sigs: Vec<Arc<Sig>>,
}

/// What `w` makes of the types `roots`, in order.
// Complexity tradeoff (COMPLEXITY.md rows F97 and TY-subst-stacks): naive version, a
// recursive walk that enters a row once per path to it, O(2^n) for n rows each holding the one
// below twice, and one frame of the thread's stack per level, so a deep type overflowed it.
// Used: each row, shape and held function made once and given again from the walker's memo
// ([`Rebuild::known_row`], `made_row`), O(distinct parts), on an explicit heap stack, O(depth)
// heap. Tradeoffs: the memo holds each part made until the walk ends; the steps and results
// are pushed and popped where recursion would call, a constant factor.
fn rebuild_tys<'a>(w: &mut impl Rebuild, roots: impl IntoIterator<Item = &'a Ty>) -> Vec<Ty> {
    let mut stack: Vec<Step<'a>> = roots.into_iter().map(Step::Ty).collect();
    stack.reverse();
    let mut out = Rebuilt::default();
    rebuild(w, stack, &mut out);
    out.tys
}

/// What `w` makes of the type `t`.
fn rebuild_ty(w: &mut impl Rebuild, t: &Ty) -> Ty {
    let mut out = Rebuilt::default();
    rebuild(w, vec![Step::Ty(t)], &mut out);
    out.tys
        .pop()
        .expect("a walk makes one type of the one it is given")
}

/// What `w` makes of the function `s`, as a type holding it would have it.
fn rebuild_held(w: &mut impl Rebuild, s: &Arc<Sig>) -> Arc<Sig> {
    let mut out = Rebuilt::default();
    rebuild(w, vec![Step::Held(s)], &mut out);
    out.sigs
        .pop()
        .expect("a walk makes one signature of the one it is given")
}

/// Makes what `w` makes of each part on `stack`, the top first, and pushes it to `out`.
///
/// A type nests as deep as the program, so the walk keeps its own stack. It enters the parts
/// of a part in the order a recursive walk would (a type's rows, then its functions, then its
/// payload shapes; a function's arrows, each parameter then the result, then its needs), and
/// makes each part once its own are made, the last on top of their stacks in `out`; `w` sees
/// each part as the recursive walk did, so its memos and the variables it hides do not change.
fn rebuild<'a>(w: &mut impl Rebuild, mut stack: Vec<Step<'a>>, out: &mut Rebuilt) {
    /// Pushes `done`, then `parts` so that they pop in order.
    fn enter<'a>(stack: &mut Vec<Step<'a>>, done: Step<'a>, parts: impl Iterator<Item = Step<'a>>) {
        stack.push(done);
        let from = stack.len();
        stack.extend(parts);
        stack[from..].reverse();
    }
    while let Some(step) = stack.pop() {
        match step {
            Step::Ty(t) => match w.known_ty(t) {
                Some(done) => out.tys.push(done),
                None => {
                    let rows = t.tuples.iter().map(Step::Row);
                    let fns = t.fns.iter().map(Step::Held);
                    let shapes = t.payload_shapes().map(Step::Shape);
                    enter(&mut stack, Step::TyDone(t), rows.chain(fns).chain(shapes));
                }
            },
            Step::Row(r) => match w.known_row(r) {
                Some(done) => out.rows.push(done),
                None => enter(&mut stack, Step::RowDone(r), r.iter().map(Step::Ty)),
            },
            Step::Shape(s) => match w.known_shape(s) {
                Some(done) => out.shapes.push(done),
                None => {
                    let cs = s.items.iter().chain(s.fields.values());
                    enter(&mut stack, Step::ShapeDone(s), cs.map(Step::Ty));
                }
            },
            Step::Held(s) => match w.known_held(s) {
                Some(done) => out.sigs.push(done),
                None => enter(&mut stack, Step::HeldDone(s), sig_tys(s).map(Step::Ty)),
            },
            Step::TyDone(t) => {
                let mut tuples = out.rows.split_off(out.rows.len() - t.tuples.len());
                let fns = out.sigs.split_off(out.sigs.len() - t.fns.len());
                let from = out.shapes.len() - t.payload_shapes().count();
                let mut shapes = out.shapes.drain(from..);
                let mut payloads = t.map_payloads(|_| {
                    (shapes.next()).expect("a walk makes one shape of each payload shape")
                });
                // A variable replaced by the empty type leaves a row with no value, and a
                // payload shape with none, as `#a(g(x), 1)` once `g`'s result is `Never`; a name
                // left with no shape has no atom with a payload, which the type then drops (its
                // bare atom stays). O(1) per shape, and one difference of the set when a name
                // is dropped.
                tuples.retain(|r| !r.0.void);
                let mut gone = Vec::new();
                payloads.retain(|n, ss| {
                    let Some(ss) = ss else { return true };
                    let had = !ss.is_empty();
                    ss.retain(|s| !s.void);
                    if had && ss.is_empty() {
                        gone.push(KType::atom_with(n, &KType::top()));
                        return false;
                    }
                    true
                });
                let (set, family) = match gone.is_empty() {
                    true => (t.set.clone(), t.family.clone()),
                    false => {
                        let gone = KType::union_all(gone);
                        (&t.set - &gone, &t.family - &gone)
                    }
                };
                let set = w.made_set(set);
                let mut made = Ty {
                    set,
                    tuples: tuples.into(),
                    fns: fns.into(),
                    vars: VarSet::new(),
                    dynamic: t.dynamic,
                    family,
                    payloads,
                };
                for v in &t.vars {
                    match w.binding(v) {
                        Some(b) => made = made.union(&b),
                        None => {
                            made.vars.insert(v.clone());
                        }
                    }
                }
                out.tys.push(w.made_ty(made));
            }
            Step::RowDone(r) => {
                let made = r.replaced(out.tys.split_off(out.tys.len() - r.len()));
                w.made_row(r, &made);
                out.rows.push(made);
            }
            Step::ShapeDone(s) => {
                let from = out.tys.len() - s.items.len() - s.fields.len();
                let mut cs = out.tys.drain(from..);
                let items = cs.by_ref().take(s.items.len()).collect();
                let fields = (s.fields.keys())
                    .map(|n| {
                        let c = cs.next().expect("a walk makes one type of each field");
                        (n.clone(), c)
                    })
                    .collect();
                let made = Shape::new(items, fields);
                w.made_shape(s, &made);
                out.shapes.push(made);
            }
            Step::HeldDone(s) => {
                let from = out.tys.len() - sig_tys(s).count();
                let (arrows, needs) = sig_parts(s, out.tys.drain(from..));
                out.sigs.push(w.made_held(s, arrows, needs));
            }
        }
    }
}

/// The types of the arrows and needs of `s` that a rebuilding walk enters, in order: each
/// arrow's parameters, then its result, then each need's types ([`Need::tys`]).
fn sig_tys(s: &Sig) -> impl Iterator<Item = &Ty> {
    (s.arrows.iter())
        .flat_map(|a| a.params.iter().chain(std::iter::once(&a.result)))
        .chain(s.needs.iter().flat_map(Need::tys))
}

/// Whether `s`, or a function below it, has a property: `here` gives none where a signature
/// has it in its own types, and otherwise the functions below it to read; `known` gives an
/// answer kept for a signature, and `keep` keeps one. Each signature entered is answered and
/// kept, innermost first, so a later ask of any of them reads its answer.
///
/// Proof of the answers kept: a signature is kept false only once `here` found the property
/// absent in its own types and each function `here` gave was answered false, so none below it
/// has it. When a signature has the property, or a function read is answered true, the walk
/// stops; each signature then on the chain holds the next one (each was entered from the
/// function list of the one before), so each has the property below it and is kept true.
/// Signatures held in a type are not changed (a clone starts with no facts) and hold no cycle
/// (each holds its functions by `Arc`, made before it), so the walk ends and a kept answer
/// stays right.
// Complexity tradeoff: the naive version walks every function below `s` at each ask, Θ(n^2)
// over a nest of n asked one level at a time. Used: each signature's own types are read by
// `here` at most once in all, plus one read of a kept answer for each function it lists;
// an explicit stack, since functions nest as deep as the text.
fn found_in_nest<'a>(
    s: &'a Sig,
    known: impl Fn(&Sig) -> Option<bool>,
    keep: impl Fn(&Sig, bool),
    here: impl Fn(&'a Sig) -> Option<Vec<&'a Sig>>,
) -> bool {
    if let Some(b) = known(s) {
        return b;
    }
    // The signatures entered whose answer is not known yet, each held by the one before, each
    // with the functions below it still to read.
    let mut chain: Vec<(&'a Sig, Vec<&'a Sig>)> = Vec::new();
    let mut enter = Some(s);
    loop {
        if let Some(g) = enter.take() {
            match here(g) {
                Some(fns) => chain.push((g, fns)),
                None => {
                    chain.push((g, Vec::new()));
                    break;
                }
            }
        }
        let (g, todo) = chain.last_mut().expect("the chain holds `s` until it ends");
        let g = *g;
        match todo.pop() {
            Some(f) => match known(f) {
                Some(false) => {}
                Some(true) => break,
                None => enter = Some(f),
            },
            None => {
                keep(g, false);
                chain.pop();
                if chain.is_empty() {
                    return false;
                }
            }
        }
    }
    for (g, _) in chain {
        keep(g, true);
    }
    true
}

/// The functions the types of `s` hold outside functions, as [`vars_of`] meets them, or none
/// if one of those types holds, outside functions, a variable for which `may_hold` is false:
/// the `here` of [`found_in_nest`] for [`Sig::holds_no_variable`] and
/// [`Sig::holds_only_own_variables`].
fn fns_outside(s: &Sig, may_hold: impl Fn(&Arc<str>) -> bool) -> Option<Vec<&Sig>> {
    // By address: every row and shape is borrowed from `s` for the whole walk, so no key
    // names a freed node, and the sets are only read by insert, never iterated. The sets are
    // this signature's own: a row skipped here because another signature of the chain walked
    // it would leave its functions unread when this one is answered.
    let (mut rows, mut shapes) = (HashSet::new(), HashSet::new());
    let mut fns = Vec::new();
    // A row or shape whose bits are empty holds no variable at any depth, inside functions
    // too, own, bounded and held ones among them ([`VarFacts::names`]), so no variable for
    // which `may_hold` is false is in it or in a function below it, and it is passed over.
    // Complexity tradeoff (PERF-types-shared-row-bench-2ec6b9418): naive version, as before
    // for rows, every row walked but the fixed ones, which hold no function: a row of n
    // functions shared by the results of n nested function types was walked once for each
    // of them, as these sets are each signature's own, O(n^2) on the first ask (16.1 times
    // the instructions at 8n). Used: O(1) for a row that holds no variable.
    let mut stack: Vec<&Ty> = sig_tys(s).collect();
    while let Some(t) = stack.pop() {
        if !t.vars.iter().all(&may_hold) {
            return None;
        }
        for r in t.tuples.iter().filter(|r| r.holds_vars()) {
            if rows.insert(Arc::as_ptr(&r.0)) {
                stack.extend(r.iter());
            }
        }
        for sh in t.payload_shapes().filter(|sh| !sh.bits.is_empty()) {
            if shapes.insert(Arc::as_ptr(&sh.0)) {
                stack.extend(sh.items.iter().chain(sh.fields.values()));
            }
        }
        fns.extend(t.fns.iter().map(|f| &**f));
    }
    Some(fns)
}

/// The variables of `tys` added to `out` in order of first appearance, as [`Ty::vars_in`]
/// gives them, by one walk that enters each shared row, payload shape and held function once.
// Complexity tradeoff (COMPLEXITY.md FAIL-returned-chain-quadratic): a walk that enters every
// function it meets walks a function held by several once for each, O(2^n) for a nest where
// each holds the one below twice, so each is entered once per walk. Across walks, a function
// whose order of variables is kept ([`Sig::vars_order`]) gives it at the cost of its length
// in place of being entered: the checker names the variables of each signature it shows
// through `vars_order`, so n functions each returning the one before cost O(n), not the
// O(n^2) of walking each to the bottom. Only a signature `vars_order` is asked of keeps its
// order; keeping one at each function met, as first written, was O(n^2) in time and memory
// for n nested lambdas that each hold all n variables (60.4 times the work for 8 times n,
// against 8.5). The order is that of the naive walk: a variable met again is skipped.
fn vars_of<'a>(tys: impl Iterator<Item = &'a Ty>, out: &mut Vars) {
    enum Walk<'a> {
        Ty(&'a Ty),
        Row(&'a Row),
        Shape(&'a Shape),
        Held(&'a Sig),
    }
    let add = |out: &mut Vars, v: &Arc<str>| {
        if out.seen.insert(v.clone()) {
            out.order.push(v.clone());
        }
    };
    // By address: every row, shape and function is borrowed for the whole walk, so no key
    // names a freed node, and the sets are only read by insert, never iterated.
    let mut rows = HashSet::new();
    let mut shapes = HashSet::new();
    let mut held = HashSet::new();
    let mut stack: Vec<Walk<'a>> = tys.map(Walk::Ty).collect();
    stack.reverse();
    while let Some(w) = stack.pop() {
        let from = stack.len();
        let t = match w {
            Walk::Row(r) => {
                if rows.insert(Arc::as_ptr(&r.0)) {
                    stack.extend(r.iter().map(Walk::Ty));
                    stack[from..].reverse();
                }
                continue;
            }
            Walk::Shape(s) => {
                if shapes.insert(Arc::as_ptr(&s.0)) {
                    stack.extend(s.items.iter().chain(s.fields.values()).map(Walk::Ty));
                    stack[from..].reverse();
                }
                continue;
            }
            Walk::Held(s) => {
                if held.insert(s as *const Sig) {
                    match s.facts.4.get() {
                        Some(order) => order.iter().for_each(|v| add(out, v)),
                        None => {
                            stack.extend(sig_tys(s).map(Walk::Ty));
                            stack[from..].reverse();
                        }
                    }
                }
                continue;
            }
            Walk::Ty(t) => t,
        };
        t.vars.iter().for_each(|v| add(out, v));
        stack.extend(t.tuples.iter().filter(|r| !r.0.fixed).map(Walk::Row));
        let open = t.payload_shapes().filter(|s| !s.bits.is_empty());
        stack.extend(open.map(Walk::Shape));
        stack.extend(t.fns.iter().map(|s| Walk::Held(s)));
        stack[from..].reverse();
    }
}

/// The arrows and needs of `s` with the types [`sig_tys`] gives replaced by `tys`, in order.
fn sig_parts(s: &Sig, mut tys: impl Iterator<Item = Ty>) -> (Vec<Arrow>, Vec<Need>) {
    let mut next = || {
        tys.next()
            .expect("a walk makes one type of each type of a signature")
    };
    let arrows = (s.arrows.iter())
        .map(|a| Arrow {
            params: a.params.iter().map(|_| next()).collect(),
            result: next(),
            partial: a.partial,
        })
        .collect();
    let needs = s.needs.iter().map(|n| n.map_tys(|_| next())).collect();
    (arrows, needs)
}

/// One replacement of variables ([`Ty::replace_in`]) over a type, a signature or a need.
///
/// Rows, payload shapes and signatures are shared, so a type of `n` rows may have `2^n` paths
/// through them, as the result of `p(p(p(a0, a1), a2), ...)` with `p(s, v) = (s, (s, v))` has.
/// The walk keeps what it made of each row, shape and signature, by address, and gives that
/// again where it meets one once more, so each is replaced once (REPLACE-shared-rows). The
/// addresses are those of rows, shapes and signatures the input holds, which outlive the
/// walk, so no two are the same.
struct Replacer<'b> {
    binds: &'b Binds,
    mode: Mode,
    /// The variables `binds` binds that are own variables of a signature the walk is inside,
    /// each with the number of such signatures: there they are the signature's, and are kept.
    /// Looked up per variable met, so a signature that hides some costs the variables it
    /// holds, not a copy of `binds` without them.
    hidden: HashMap<Arc<str>, usize>,
    /// What each row and signature met was replaced by, under the variables hidden now: one
    /// memo for each signature entered that hides one, last entered last.
    // Complexity tradeoff: a row shared by several signatures that each hide variables is
    // made once in each of their memos, though two that hide the same variables would make
    // it alike: O(rows held times such signatures) at worst, not O(rows). Keying the memo by
    // the set hidden would share those, at the cost of hashing that set at each signature.
    memos: Vec<Memo>,
    /// The variables each signature the walk is inside hides, last entered last: none for one
    /// that hides none, which has no memo of its own.
    entered: Vec<Vec<Arc<str>>>,
}

/// The rows and payload shapes a walk that rebuilds a type met, by address, with what it made
/// of each: both are shared, so a walk without it would rebuild one once per path to it,
/// `2^n` times for `n` rows or shapes that each hold the one below twice. The addresses are
/// those of rows and shapes the input holds: each walk ([`Replacer`], [`Subst`], [`Widen`],
/// [`HeldFns`], [`Settle`]) is made and dropped within one call that borrows the input, so no key names a
/// freed node, and the maps are only read by key, never iterated.
#[derive(Default)]
struct Made {
    rows: HashMap<*const RowData, Row>,
    shapes: HashMap<*const ShapeData, Shape>,
}

/// The rows, payload shapes and signatures a [`Replacer`] met under one set of hidden
/// variables, by address, with what it made of each. As in [`Made`], the signatures are held by
/// the input the walk borrows for its whole life, and `sigs` is only read by key, never
/// iterated.
#[derive(Default)]
struct Memo {
    made: Made,
    sigs: HashMap<*const Sig, Arc<Sig>>,
}

impl<'b> Replacer<'b> {
    fn new(binds: &'b Binds, mode: Mode) -> Self {
        Replacer {
            binds,
            mode,
            hidden: HashMap::new(),
            memos: vec![Memo::default()],
            entered: Vec::new(),
        }
    }

    /// The memo of the variables hidden now.
    fn memo(&mut self) -> &mut Memo {
        self.memos
            .last_mut()
            .expect("a replacer holds a memo from its start to its end")
    }

    /// What the variable `v` is replaced by here, if it is.
    fn bound(&self, v: &str) -> Option<&'b Ty> {
        self.binds.get(v).filter(|_| !self.hidden.contains_key(v))
    }

    /// Whether `f` holds a variable replaced here that `own` does not hold: read from the
    /// smaller of `binds` and `f`, so a call that binds many variables pays at each row or
    /// signature it replaces in for the variables that holds, not for every one it binds.
    fn holds(&self, f: &VarFacts, own: &BTreeSet<Arc<str>>) -> bool {
        let here = |v: &Arc<str>| !own.contains(v) && !self.hidden.contains_key(v);
        if self.binds.len() <= f.classes.len() + f.names.len() {
            self.binds.keys().any(|v| here(v) && f.holds(v))
        } else {
            (f.classes.iter().chain(&f.names)).any(|v| here(v) && self.binds.contains_key(v))
        }
    }

    /// [`Sig::replace_in`]: renamed, its own and held variables take their new names.
    fn sig(&mut self, s: &Sig) -> Sig {
        let tys = rebuild_tys(self, sig_tys(s));
        let (arrows, needs) = sig_parts(s, tys.into_iter());
        self.sig_of(s, arrows, needs)
    }

    /// The signature `s` with its arrows and needs replaced in, `arrows` and `needs`: its own
    /// and held variables and its bounds as the variables hidden now replace them.
    fn sig_of(&self, s: &Sig, arrows: Vec<Arrow>, needs: Vec<Need>) -> Sig {
        // Its own or held variable `v` under `binds`: renamed, kept, or dropped as replaced.
        let keep = |v: &Arc<str>| match self.bound(v) {
            None => Some(v.clone()),
            Some(t) if self.mode == Mode::Rename => t.vars.first().cloned(),
            Some(_) => None,
        };
        let own = s.own.iter().filter_map(keep).collect();
        let held = s.held.iter().filter_map(keep).collect();
        let mut bounds = BTreeMap::new();
        for (v, m) in &s.bounds {
            match self.bound(v) {
                None => {
                    bounds.insert(v.clone(), *m);
                }
                Some(t) => {
                    for w in &t.vars {
                        bounds.insert(w.clone(), *m);
                    }
                }
            }
        }
        Sig {
            params: s.params.clone(),
            arrows,
            bounds,
            data: s.data,
            dense: s.dense,
            keys: s.keys.clone(),
            word: s.word.clone(),
            needs,
            own,
            held,
            named: s.named,
            // A result of `int` holds no variable, so it is the same after the replacement.
            hull: s.hull.clone(),
            facts: Facts::default(),
        }
    }
}

impl Rebuild for Replacer<'_> {
    fn known_ty(&mut self, t: &Ty) -> Option<Ty> {
        // A type with no tuple, function or payload holds only its own variables; outside
        // functions, one with no tuple or payload does.
        let fns = !t.fns.is_empty() && self.mode != Mode::Outside;
        let leaf = t.tuples.is_empty() && !fns && t.payloads.is_empty();
        (leaf && !t.vars.iter().any(|v| self.bound(v).is_some())).then(|| t.clone())
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        if let Some(done) = self.memo().made.rows.get(&Arc::as_ptr(&r.0)) {
            return Some(done.clone());
        }
        let kept = match self.mode {
            _ if r.0.fixed => true,
            Mode::Outside if !r.open() => true,
            _ => !self.binds.index().meets(&r.0.bits),
        };
        kept.then(|| {
            self.made_row(r, r);
            r.clone()
        })
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.memo().made.rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    /// A payload shape: kept whole where it holds none of the variables replaced here.
    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        if let Some(done) = self.memo().made.shapes.get(&s.as_ptr()) {
            return Some(done.clone());
        }
        let kept = match self.mode {
            _ if s.fixed => true,
            Mode::Outside if !s.open() => true,
            _ => !self.binds.index().meets(&s.bits),
        };
        kept.then(|| {
            self.made_shape(s, s);
            s.clone()
        })
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.memo().made.shapes.insert(s.as_ptr(), out.clone());
    }

    /// A signature held in a type: replaced in, but its own variables are its own, so those
    /// `binds` binds are hidden inside it, under a memo of their own.
    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        if self.mode == Mode::Outside {
            return Some(s.clone());
        }
        if let Some(done) = self.memo().sigs.get(&Arc::as_ptr(s)) {
            return Some(done.clone());
        }
        // A signature that holds none of the variables replaced is kept whole.
        if self.mode != Mode::Rename && !self.holds(s.facts(), &s.own) {
            self.memo().sigs.insert(Arc::as_ptr(s), s.clone());
            return Some(s.clone());
        }
        let hide: Vec<Arc<str>> = match self.mode {
            Mode::Rename => Vec::new(),
            _ => (s.own.iter())
                .filter(|v| self.bound(v).is_some())
                .cloned()
                .collect(),
        };
        if !hide.is_empty() {
            for v in &hide {
                *self.hidden.entry(v.clone()).or_default() += 1;
            }
            self.memos.push(Memo::default());
        }
        self.entered.push(hide);
        None
    }

    fn made_held(&mut self, s: &Arc<Sig>, arrows: Vec<Arrow>, needs: Vec<Need>) -> Arc<Sig> {
        // Its own and held variables are read with its own hidden, as its arrows were.
        let out = Arc::new(self.sig_of(s, arrows, needs));
        let hide = (self.entered.pop()).expect("a signature the walk leaves is one it entered");
        if !hide.is_empty() {
            self.memos.pop();
            for v in &hide {
                if let Some(n) = self.hidden.get_mut(v) {
                    *n -= 1;
                    if *n == 0 {
                        self.hidden.remove(v);
                    }
                }
            }
        }
        self.memo().sigs.insert(Arc::as_ptr(s), out.clone());
        out
    }

    fn binding(&self, v: &str) -> Option<Cow<'_, Ty>> {
        self.bound(v).map(Cow::Borrowed)
    }
}

/// Signatures renamed and then replaced in ([`Sig::renamed`], then [`Sig::replace`]) one after
/// another, as the checker names the variables of each signature it shows: where two are given
/// the same names and the same replacement, the functions they share are made once, not once
/// for each. So `n` functions each returning the one before, whose signatures hold each other,
/// cost each one's outer level, not its depth.
// Complexity tradeoff (COMPLEXITY.md FAIL-returned-chain-quadratic): the naive version renames
// and replaces each signature with a walk of its own, which rebuilds every function it holds:
// O(n^2) for the chain above (57 times the instructions for 8 times the functions). Used: the
// memo of each walk ([`Memo`], by address) kept for each pair of maps, found by the pair's
// digests and compared in full, and each signature walked kept alive with what was made of
// it, so no address in a memo is freed and taken again. A signature held in many is then made
// once per distinct pair of maps. Tradeoff: the memos and the signatures walked live until
// it is dropped; signatures given different maps share nothing, so a chain where each level
// adds variables of its own still costs the sum of the depths, against a memo keyed by the
// maps restricted to the variables of each function, which would hash those at each function.
#[derive(Default)]
pub struct Renamings {
    pairs: HashMap<(u64, u64), Vec<Renaming>>,
}

/// The walks of a [`Renamings`] under one pair of maps.
struct Renaming {
    to: Binds,
    binds: Binds,
    renamed: Memo,
    replaced: Memo,
    /// Each signature walked, and each made by renaming, which the replacement walked: the
    /// addresses the memos are keyed by.
    walked: Vec<Arc<Sig>>,
}

impl Renamings {
    /// `s.renamed(&to).replace(&binds)`, sharing with the signatures given before.
    pub fn renamed_replaced(&mut self, s: &Arc<Sig>, to: Binds, binds: Binds) -> Arc<Sig> {
        let at = self.pairs.entry((to.digest, binds.digest)).or_default();
        let i = match at.iter().position(|r| r.to == to && r.binds == binds) {
            Some(i) => i,
            None => {
                at.push(Renaming {
                    to,
                    binds,
                    renamed: Memo::default(),
                    replaced: Memo::default(),
                    walked: Vec::new(),
                });
                at.len() - 1
            }
        };
        let r = &mut at[i];
        let walk = |binds: &Binds, mode: Mode, memo: &mut Memo, s: &Arc<Sig>| -> Arc<Sig> {
            if binds.is_empty() {
                return s.clone();
            }
            let mut w = Replacer::new(binds, mode);
            w.memos[0] = std::mem::take(memo);
            let out = Arc::new(w.sig(s));
            *memo = w.memos.swap_remove(0);
            out
        };
        let renamed = walk(&r.to, Mode::Rename, &mut r.renamed, s);
        let out = walk(&r.binds, Mode::Replace, &mut r.replaced, &renamed);
        r.walked.push(s.clone());
        r.walked.push(renamed);
        out
    }
}

/// [`Ty::subst`]: the variables `binds` binds replaced outside the functions a type holds,
/// which are kept whole, as is a row or payload shape that holds none of them; each other row
/// and shape is made once, by address ([`Made`]).
struct Subst<'b> {
    binds: &'b Binds,
    made: Made,
}

impl Rebuild for Subst<'_> {
    fn known_ty(&mut self, _: &Ty) -> Option<Ty> {
        None
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        match self.binds.index().meets(&r.0.bits) {
            false => Some(r.clone()),
            true => self.made.rows.get(&Arc::as_ptr(&r.0)).cloned(),
        }
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.made.rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        match self.binds.index().meets(&s.bits) {
            false => Some(s.clone()),
            true => self.made.shapes.get(&s.as_ptr()).cloned(),
        }
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.made.shapes.insert(s.as_ptr(), out.clone());
    }

    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        Some(s.clone())
    }

    fn made_held(&mut self, _: &Arc<Sig>, _: Vec<Arrow>, _: Vec<Need>) -> Arc<Sig> {
        unreachable!("`subst` keeps each function whole, so it enters none")
    }

    fn binding(&self, v: &str) -> Option<Cow<'_, Ty>> {
        self.binds.get(v).map(Cow::Borrowed)
    }
}

/// [`Ty::carriers`]: each set of scalars widened to every value of the carriers it holds, at
/// every depth outside functions, which are kept whole; each row and payload shape is made
/// once, by address ([`Made`]).
#[derive(Default)]
struct Widen {
    made: Made,
}

impl Rebuild for Widen {
    fn known_ty(&mut self, _: &Ty) -> Option<Ty> {
        None
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        self.made.rows.get(&Arc::as_ptr(&r.0)).cloned()
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.made.rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        self.made.shapes.get(&s.as_ptr()).cloned()
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.made.shapes.insert(s.as_ptr(), out.clone());
    }

    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        Some(s.clone())
    }

    fn made_held(&mut self, _: &Arc<Sig>, _: Vec<Arrow>, _: Vec<Need>) -> Arc<Sig> {
        unreachable!("`carriers` keeps each function whole, so it enters none")
    }

    fn binding(&self, _: &str) -> Option<Cow<'_, Ty>> {
        None
    }

    fn made_set(&mut self, s: KType) -> KType {
        let held: Vec<_> = (Carrier::ALL.into_iter())
            .filter(|c| !(&s & &c.ty()).is_empty())
            .collect();
        held.into_iter().fold(s, |s, c| &s | &c.ty())
    }
}

/// [`Ty::with_held_fns`]: each function a type holds outside functions replaced by what
/// `each` makes of it, without entering it; a row or payload shape that holds no function at
/// any depth outside functions is kept whole, and each other is made once, by address
/// ([`Made`]). A family that holds a function ([`Sig::holds_fn_as_data`]) is entered as a
/// tuple is, and made once, by address (`families`, read only by key, as [`Made`]'s maps).
struct HeldFns<F> {
    each: F,
    made: Made,
    families: HashMap<*const Sig, Arc<Sig>>,
}

impl<F: FnMut(&Arc<Sig>) -> Arc<Sig>> Rebuild for HeldFns<F> {
    fn known_ty(&mut self, _: &Ty) -> Option<Ty> {
        None
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        match r.0.held {
            None => Some(r.clone()),
            Some(_) => self.made.rows.get(&Arc::as_ptr(&r.0)).cloned(),
        }
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.made.rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        match s.held {
            None => Some(s.clone()),
            Some(_) => self.made.shapes.get(&s.as_ptr()).cloned(),
        }
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.made.shapes.insert(s.as_ptr(), out.clone());
    }

    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        match s.holds_fn_as_data() {
            false => Some((self.each)(s)),
            true => self.families.get(&Arc::as_ptr(s)).cloned(),
        }
    }

    /// A family entered: the same family with its keys and entries made anew. It has no needs
    /// ([`Sig::holds_fn_as_data`]), and the walk changes no variable, so its own, held and
    /// bounded variables are those it had.
    fn made_held(&mut self, s: &Arc<Sig>, arrows: Vec<Arrow>, needs: Vec<Need>) -> Arc<Sig> {
        debug_assert!(
            s.data && needs.is_empty(),
            "only a family of no needs is entered"
        );
        let made = Arc::new(Sig {
            params: s.params.clone(),
            arrows,
            bounds: s.bounds.clone(),
            data: s.data,
            dense: s.dense,
            keys: s.keys.clone(),
            word: s.word.clone(),
            needs,
            own: s.own.clone(),
            held: s.held.clone(),
            named: s.named,
            hull: s.hull.clone(),
            facts: Facts::default(),
        });
        self.families.insert(Arc::as_ptr(s), made.clone());
        made
    }

    fn binding(&self, _: &str) -> Option<Cow<'_, Ty>> {
        None
    }
}

/// The type a text prints, as the reader reads the text back (FAIL-print-absorbed-members-twice):
/// at every depth, inside functions too, a union that holds `_` beside other members is `_`
/// alone, since `_` holds every value (A92, DESIGN.md sec:diagnostics, "Types in a message");
/// the members of each union that are then equal are one, as [`Ty::union_all`] makes them,
/// which the reader uses for `|`; and a morphism `L .. U -> V` whose bounds are then equal is
/// the one arrow `U -> V`, as the reader makes `L .. U -> V` with `L` equal to `U`. Without
/// it, `#box(0 | _) | #box(_)` printed `#box(_) | #box(_)`, two members as one text, and
/// `Sig::morphism` chose `L .. U` on a difference the text does not show.
///
/// The printer's own walk ([`Walk::plan`]) still writes `_` for a union that holds a variable
/// standing once, and for the unions that leaves; this walk changes only what holds the
/// unknown itself, so the variables the printer counts are those of the type it writes.
///
/// A type, row, payload shape or signature that holds no union to absorb at any depth is kept
/// whole, read from what each row, shape and signature keeps ([`Ty::may_absorb`]); each other
/// row and shape, and each signature, is made once, by address ([`Made`]). `changes` counts
/// the unions written `_`, the members merged and the morphisms made one arrow; a type or
/// signature in which none happened is kept as it was, so a type with none is printed from
/// itself.
// Complexity tradeoff: naive, the members of each union compared pairwise after the walk,
// O(n²) in the members; used, one walk over the type's graph, each part once, with the
// members of each changed union merged by the hash sets [`Ty::union_all`] and
// [`join_payloads`] keep, O(n log n) in the size n of the type, and one comparison of the two
// bounds of each morphism made from changed parts, as the reader compares them. A type with
// no union to absorb is printed from itself after one read of its outer level, O(width), so
// a check that prints each of n nested types pays O(n) in all, not O(n^2) ([`Ty::may_absorb`]).
// The text the printer writes was already O(n log n) (COMPLEXITY.md F169).
#[derive(Default)]
struct Absorb {
    made: Made,
    sigs: HashMap<*const Sig, Arc<Sig>>,
    changes: usize,
    /// For each type and signature entered and not yet made, innermost last, `changes` when
    /// it was entered.
    entered: Vec<usize>,
}

impl Absorb {
    /// What [`Absorb`] makes of `t`, if it changes it.
    fn ty(t: &Ty) -> Option<Ty> {
        if !t.may_absorb() {
            return None;
        }
        let mut w = Absorb::default();
        let made = rebuild_ty(&mut w, t);
        (w.changes > 0).then_some(made)
    }

    /// What [`Absorb`] makes of `s`, if it changes it.
    fn sig(s: &Sig) -> Option<Sig> {
        if !s.may_absorb() {
            return None;
        }
        let mut w = Absorb::default();
        w.entered.push(0);
        let tys = rebuild_tys(&mut w, sig_tys(s));
        let (arrows, needs) = sig_parts(s, tys.into_iter());
        w.remade(s, arrows, needs)
    }

    /// The signature `s` entered, with its arrows and needs made into `arrows` and `needs`,
    /// if anything in it changed: a morphism `L .. U -> V` whose bounds are now equal keeps its
    /// first arrow only, as the reader reads `L .. L -> V`. Its own and bounded variables are
    /// kept, as the printer writes those that still stand ([`Walk`]), and those its parameters
    /// hold are found again.
    fn remade(&mut self, s: &Sig, mut arrows: Vec<Arrow>, needs: Vec<Need>) -> Option<Sig> {
        if !self.changed_inside() {
            return None;
        }
        if matches!(s.morphism(), Some(Morphism::Bounded { .. }))
            && arrows[0].params[0] == arrows[1].params[0]
        {
            arrows.truncate(1);
            self.changes += 1;
        }
        let mut made = Sig {
            params: s.params.clone(),
            arrows,
            bounds: s.bounds.clone(),
            data: s.data,
            dense: s.dense,
            keys: s.keys.clone(),
            word: s.word.clone(),
            needs,
            own: s.own.clone(),
            held: BTreeSet::new(),
            named: s.named,
            hull: s.hull.clone(),
            facts: Facts::default(),
        };
        made.note_held();
        Some(made)
    }

    /// Whether a change happened inside the type or signature made now, which it leaves.
    fn changed_inside(&mut self) -> bool {
        let at = (self.entered.pop()).expect("a part the walk makes is one it entered");
        self.changes > at
    }
}

impl Rebuild for Absorb {
    fn known_ty(&mut self, t: &Ty) -> Option<Ty> {
        if t.dynamic {
            if t.absorbs_here() {
                self.changes += 1;
            }
            return Some(Ty::dynamic());
        }
        if !t.may_absorb() {
            return Some(t.clone());
        }
        self.entered.push(self.changes);
        None
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        if !r.0.absorbs {
            return Some(r.clone());
        }
        self.made.rows.get(&Arc::as_ptr(&r.0)).cloned()
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.made.rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        if !s.absorbs {
            return Some(s.clone());
        }
        self.made.shapes.get(&s.as_ptr()).cloned()
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.made.shapes.insert(s.as_ptr(), out.clone());
    }

    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        if !s.may_absorb() {
            return Some(s.clone());
        }
        if let Some(done) = self.sigs.get(&Arc::as_ptr(s)) {
            return Some(done.clone());
        }
        self.entered.push(self.changes);
        None
    }

    /// A signature entered: itself if nothing in it changed, else [`Absorb::remade`].
    fn made_held(&mut self, s: &Arc<Sig>, arrows: Vec<Arrow>, needs: Vec<Need>) -> Arc<Sig> {
        let made = (self.remade(s, arrows, needs)).map_or_else(|| s.clone(), Arc::new);
        self.sigs.insert(Arc::as_ptr(s), made.clone());
        made
    }

    fn binding(&self, _: &str) -> Option<Cow<'_, Ty>> {
        None
    }

    /// A type entered whose parts changed: its members merged as [`Ty::union_all`] merges
    /// them, so the members made equal are one.
    fn made_ty(&mut self, t: Ty) -> Ty {
        if !self.changed_inside() {
            return t;
        }
        let merged = Ty::union_all([&t]);
        let shapes = |t: &Ty| t.payload_shapes().count();
        if merged.tuples.len() < t.tuples.len()
            || merged.fns.len() < t.fns.len()
            || shapes(&merged) < shapes(&t)
        {
            self.changes += 1;
        }
        merged
    }
}

/// [`Ty::settle`] and [`Sig::settle`]: each class variable `solve` gives a type replaced by
/// it at every depth. A row that holds no variable, the unknown or a function, and a payload
/// shape that holds no variable or function, are kept whole; each other is made once, by
/// address, in the memo of the signature the walk is inside, or of the type it started at;
/// each signature is settled once, and kept in its own facts.
struct Settle<'s> {
    solve: Solve<'s>,
    /// One memo for the type the walk started at, if it started at one, and one for each
    /// signature it is inside, last entered last.
    made: Vec<Made>,
}

impl Settle<'_> {
    /// The memo of the signature the walk is inside, or of the type it started at.
    fn memo(&mut self) -> &mut Made {
        self.made
            .last_mut()
            .expect("a settling walk enters a row or shape only inside a memo")
    }
}

impl Rebuild for Settle<'_> {
    fn known_ty(&mut self, _: &Ty) -> Option<Ty> {
        None
    }

    fn known_row(&mut self, r: &Row) -> Option<Row> {
        match r.open() || r.0.held.is_some() {
            false => Some(r.clone()),
            true => self.memo().rows.get(&Arc::as_ptr(&r.0)).cloned(),
        }
    }

    fn made_row(&mut self, r: &Row, out: &Row) {
        self.memo().rows.insert(Arc::as_ptr(&r.0), out.clone());
    }

    fn known_shape(&mut self, s: &Shape) -> Option<Shape> {
        match s.fixed {
            true => Some(s.clone()),
            false => self.memo().shapes.get(&s.as_ptr()).cloned(),
        }
    }

    fn made_shape(&mut self, s: &Shape, out: &Shape) {
        self.memo().shapes.insert(s.as_ptr(), out.clone());
    }

    /// A signature that holds no class variable is itself, and one settled before is what it
    /// was settled into; another is entered under a memo of its own.
    fn known_held(&mut self, s: &Arc<Sig>) -> Option<Arc<Sig>> {
        if s.facts().classes.is_empty() {
            return Some(s.clone());
        }
        if let Some(done) = s.facts.1.get() {
            return Some(done.clone());
        }
        self.made.push(Made::default());
        None
    }

    fn made_held(&mut self, s: &Arc<Sig>, arrows: Vec<Arrow>, needs: Vec<Need>) -> Arc<Sig> {
        self.made.pop();
        // A variable `solve` gives a type is replaced, so no longer bounded, own or held.
        let solve = self.solve;
        let open = |v: &&Arc<str>| solve(v).is_none();
        let settled = Sig {
            params: s.params.clone(),
            arrows,
            bounds: (s.bounds.iter())
                .filter(|(v, _)| open(v))
                .map(|(v, m)| (v.clone(), *m))
                .collect(),
            data: s.data,
            dense: s.dense,
            keys: s.keys.clone(),
            word: s.word.clone(),
            needs,
            own: s.own.iter().filter(open).cloned().collect(),
            held: s.held.iter().filter(open).cloned().collect(),
            named: s.named,
            // A result of `int` holds no class variable, so it is the same once solved.
            hull: s.hull.clone(),
            facts: Facts::default(),
        };
        s.facts.1.get_or_init(|| Arc::new(settled)).clone()
    }

    fn binding(&self, v: &str) -> Option<Cow<'_, Ty>> {
        (self.solve)(v).map(Cow::Owned)
    }
}

/// What a family's keys are known to be ([`Sig::dense`]). A key type `int` holds no interval,
/// so this is the one place a family's type says that its keys are one interval, every key
/// present, and whether that interval starts at `0`.
///
/// Complexity tradeoff: a tag set once where the family's type is made, and one comparison
/// at each read and each `flatMap`, O(1). The naive way, the interval's ends kept in `Sig` and
/// compared at each use, costs the same order but holds two integers where a read needs one
/// of three cases (COMPLEXITY.md, RANGE-read-out-of-bounds). Where both ends are known, as
/// for `0 ..< 3`, they are kept as well, in [`Sig::keys`], for `zip` and `++`, which need the
/// keys and not only the case (row RANGE-literal-keys).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Dense {
    /// Nothing more than its arrows say: a read that misses gives `#notFound`.
    No,
    /// One integer interval, every key present, whose low end is not known to be `0`: a range
    /// `a ..< b` or `a ..= b`. A read that misses gives `#outOfBounds` (DESIGN.md
    /// sec:type_language, the `m[k]` row, `lst : int[a..<b]`).
    Interval,
    /// The ranks `0 ..< n`, every one present: an array display, a range from the literal
    /// `0`, a `Lines` input, the `CommandLine` arguments. A read that misses gives
    /// `#outOfBounds`, and the family is a list, which `flatMap` demands of each entry's result
    /// (DESIGN.md sec:grouping, "`flatMap` on `K -> V0` with body `V0 -> Seq(V)` yields
    /// `K -> rank -> V`").
    Ranks,
}

impl Dense {
    /// Whether the keys are one integer interval, every key present, so that a read that
    /// misses gives `#outOfBounds`.
    pub fn interval(self) -> bool {
        self != Dense::No
    }
}

/// A function's signature: its parameters' names and kinds, shared by its arrows, which
/// together are an intersection, and the carriers each bounded type variable ranges over.
#[derive(Clone, Eq)]
pub struct Sig {
    /// The parameters.
    pub params: Vec<SParam>,
    /// The arrows.
    pub arrows: Vec<Arrow>,
    /// Each bounded type variable, with the mask of the carriers it ranges over: one carrier,
    /// the same at each place the variable stands.
    pub bounds: BTreeMap<Arc<str>, u8>,
    /// Whether it is a family: a morphism held as data (sec:values_morphisms), shown, compared
    /// and put in a tuple as a value, and looked up through its arrows.
    pub data: bool,
    /// Whether it is a family whose keys are one integer interval, every key present
    /// ([`Dense`]). A read of it at a site whose receiver is known to be such a family misses
    /// with `#outOfBounds`, not `#notFound` (DESIGN.md sec:type_language, the `m[k]` row). Its
    /// arrows still answer `#notFound`, and are printed so, since no type text says that its
    /// keys are one interval; it fits where `int ->? V` is wanted, and a read there, or in a
    /// generic function, which the evaluator does one way for every family, misses with
    /// `#notFound`.
    pub dense: Dense,
    /// Its keys exactly, where it is a family whose keys are each int from `low` through
    /// `high` and no other, both ends known (row RANGE-literal-keys): a range `a ..< b` or
    /// `a ..= b` whose two ends the checker's read of the text fixes, as `0 ..< 3`, and what
    /// `++` and `zip` make of such families. `None` where its arrows and [`Sig::dense`] say all
    /// that is known of its keys. The empty family is `int[0..=-1]`, so that equal key sets are
    /// equal values. Its arrows stay `int ->? V` and print so, since no type text the parser
    /// takes in that place says the keys are an interval (DESIGN.md sec:type_language, the
    /// `m[k]` row, `lst : int[a..<b]`); `zip` and `++` read these keys as they read the listed
    /// keys of an array display. A family with keys fits where one with the same keys or with
    /// none is wanted, and not where other keys are ([`fits_sig`]).
    ///
    /// Complexity tradeoff: two ints, set in O(1) where the range is typed and compared in
    /// O(1). The naive way, which the row first named, lists the keys in the arrow's key type
    /// as an array display's are, `(0 | 1 | 2) -> int`: O(b - a) time and space for a text of
    /// O(log(b - a)) digits, so `0 ..< 1000000000` would type a billion keys, the cost the lazy
    /// range removed at run time (RANGE-lazy, RANGE-lazy-wide).
    pub keys: Option<WrittenRange>,
    /// The prelude word it is, if it is one: the function itself, not its arrows. `min` and
    /// `max` take two tuples, which `+`, of the same arrows, does not (DESIGN.md
    /// sec:reduction, item 5), wherever the word is called from: by name, as a method, or
    /// through a name or parameter it was passed to.
    pub word: Option<Arc<str>>,
    /// What the body needs of the values of its type variables, in the order the body met
    /// the uses: each call checks them again with the variables bound (DESIGN.md rule 4).
    pub needs: Vec<Need>,
    /// Its own type variables, which it binds: a call binds them anew, and a substitution
    /// of the variables of a type that holds it leaves them alone. The others are those of
    /// the functions around it.
    pub own: BTreeSet<Arc<str>>,
    /// Its own bounded variables a parameter holds, at any depth, on any arrow: an argument
    /// fixes their carriers. Worked out when it is built ([`Sig::note_held`]), so a comparison
    /// does not walk its parameters again at each depth.
    pub held: BTreeSet<Arc<str>>,
    /// How many of the names `var_name` gives its own type variables and those of the
    /// functions it holds take: a function around it names its own from there on. The checker
    /// writes the own variables of a signature it solved `$k`, for the class `k` each was solved
    /// from, and gives them their names when it finishes, so a function around one does not
    /// rewrite it (CHK-curried).
    pub named: usize,
    /// The hull of the ints its result can be, where its arrows' result is `int` and the
    /// checker read the ints of the body (RANGE-result-hull): printed in place of that `int`
    /// as a range, each end inclusive, so `f(x: int[0..=9]) = x + 1` is
    /// `(x: int[0..=9]) -> int[1..=10]` (DESIGN.md L1.25, and the L1.39 test row). None
    /// where nothing narrower than `int` is known. A function whose hull lies inside
    /// another's fits where that one is wanted, and not the reverse ([`fits_sig`]).
    pub hull: Option<WrittenRange>,
    /// The variables it holds at any depth, worked out when first asked ([`Sig::facts`]).
    /// Once they are read the signature is not changed in place: a change goes to a clone,
    /// whose facts are worked out again.
    pub facts: Facts,
}

/// The variables a signature holds at any depth, inside the functions it holds too: worked
/// out once for a signature held in a type, so that a substitution, or the naming of the
/// variables of a function around it, does not walk it again at each depth. It is not part
/// of the signature's value, and a clone, which may be changed, works it out again.
///
/// It also keeps the signature [`Sig::settle`] made of it, each solved class variable
/// replaced at every depth: made once, when the checker finishes, so a signature held in many
/// that the checker shows is settled once, not once for each.
///
/// And it keeps the signature's hash ([`Sig::digest`]), made from the hashes of the
/// functions it holds, so a set of functions hashes each at the cost of its outer level.
///
/// And the bits of its variables (`VarBits`), made from its facts, so a row that holds it
/// reads them in `O(1)`.
///
/// And its variables in order of first appearance ([`Sig::vars_order`]), kept once asked, so
/// the checker, which names the variables of each signature it shows, reads a signature held
/// in a later one at the cost of the length of its order.
///
/// And, for a family, the functions and kind-wide parts its entries hold ([`Entries`]), so a
/// type that holds the family reads them at the cost of its outer level.
///
/// And whether it holds no variable at any depth ([`Sig::holds_no_variable`]) and whether it or
/// a function it returns has needs ([`Sig::holds_needs`], [`Sig::may_hold_needs`]), so a nest of functions asked from
/// the outermost in is walked once, not once from each level.
///
/// And whether it holds only its own variables and those of the functions inside it
/// ([`Sig::holds_only_own_variables`]).
///
/// And whether it holds the unknown beside another member at any depth (`Sig::may_absorb`),
/// so a type printed again and again is not walked to the bottom at each print.
// Complexity tradeoff (COMPLEXITY.md row F77): the naive version works out a signature's
// variables at each depth it is met, O(n^3) for n nested tuples (106M instructions per node at
// n = 400) and O(n^2) for n nested lambdas. Used: a memo per signature, filled on first use,
// so each signature is walked once, linear in all. Tradeoffs: eleven `OnceLock`s per signature;
// a clone starts empty and works them out again, since it may be changed; equality and
// hashing ignore the memo.
#[derive(Default)]
pub struct Facts(
    std::sync::OnceLock<VarFacts>,
    std::sync::OnceLock<Arc<Sig>>,
    std::sync::OnceLock<u64>,
    std::sync::OnceLock<VarBits>,
    std::sync::OnceLock<Arc<[Arc<str>]>>,
    std::sync::OnceLock<Entries>,
    std::sync::OnceLock<bool>,
    std::sync::OnceLock<bool>,
    std::sync::OnceLock<bool>,
    std::sync::OnceLock<bool>,
    std::sync::OnceLock<bool>,
);

/// What the entries of a family hold at any depth, outside functions: a family is data only
/// when its entries are (DESIGN.md L1.17, "a value that holds a function is a type error
/// there"; row FAIL-check-family-of-functions-as-data). Its keys are left out: the checker
/// checks each key of a display and each key an `in` tests as data where it is written
/// (`display_step` and `Frame::InKey` in crates/zedc-check/src/check/walk.rs), and keys
/// computed by `group` or `rekey` are row KEYABLE-reject's.
#[derive(Default)]
pub struct Entries {
    /// The first function, not a family, that an entry holds at any depth.
    held: Option<Arc<Sig>>,
    /// The first function, not a family, that an entry holds at any depth and no tuple
    /// expression has checked as data ([`Ty::unchecked_function`]).
    unchecked: Option<Arc<Sig>>,
    /// The first kind-wide part, `(..)` or `{..}`, that an entry holds at any depth
    /// ([`Ty::held_wide`]).
    wide: Option<KType>,
}

impl Sig {
    /// What the entries of this family hold ([`Entries`]); nothing for a function, whose
    /// results are not held until it is called.
    ///
    /// The families nested in its entries' types are worked out first, each once, with an
    /// explicit stack, since families nest as deep as the text does; each entry's type is
    /// then read at its outer level, as its rows and payload shapes keep what they hold and
    /// each family nested in it now has its own [`Entries`].
    // Complexity tradeoff: the naive version walks the entries' types to the bottom at each
    // read, O(d) for d families nested one in another and O(d^2) for a program that uses each
    // of them as data. Used: a memo per family signature ([`Facts`]), filled once, so the reads
    // cost O(1) each and the fill costs the size of the outer levels of the entries' types,
    // linear in all. A family met again before its memo is filled is skipped when popped,
    // since the memo is then filled. Test:
    // `l01_26_type_resolution::bench::held_functions::nested_families_are_checked_as_data_in_linear_time`.
    fn entries(&self) -> &Entries {
        if let Some(e) = self.facts.5.get() {
            return e;
        }
        /// The families in the entries' types of `s` whose memo is not filled yet.
        fn families(s: &Sig) -> impl Iterator<Item = &Sig> {
            (s.arrows.iter())
                .flat_map(|a| a.result.fns.iter())
                .filter(|f| f.data && f.facts.5.get().is_none())
                .map(|f| &**f)
        }
        let mut stack: Vec<(&Sig, bool)> = vec![(self, false)];
        while let Some((s, ready)) = stack.pop() {
            if s.facts.5.get().is_some() {
                continue;
            }
            if !ready {
                stack.push((s, true));
                stack.extend(families(s).map(|f| (f, false)));
                continue;
            }
            // Each family nested in an entry has its memo now, so these reads do not walk.
            let results = || s.arrows.iter().map(|a| &a.result);
            let e = match s.data {
                true => Entries {
                    held: results().find_map(|t| t.held_function().cloned()),
                    unchecked: results().find_map(|t| t.unchecked_function().cloned()),
                    wide: results().find_map(Ty::held_wide),
                },
                false => Entries::default(),
            };
            let _ = s.facts.5.set(e);
        }
        self.facts.5.get().expect("filled by the walk above")
    }

    /// Whether it is a family, of no needs, whose entries or keys hold a function, not a
    /// family, at any depth outside functions: data that holds the function, as a tuple holds
    /// one, so a walk of what a value holds outside functions enters it ([`Ty::each_held_fn`],
    /// [`Ty::with_held_fns`]), and a lambda in `{"k" -> (z -> f(z))}` is met as the lambda in
    /// `(1, z -> f(z))` is (row FAIL-family-lambda-calls-param). The entries are read from
    /// their memo ([`Entries`]) and the keys at their outer level, as [`Ty::held_function`]
    /// reads them, so it costs O(1) after the memo plus the outer levels of the key types.
    /// A family with needs, if one is built, is left a function, as before this row, so the
    /// walks never enter a need's types: a need is not a part of the value.
    pub fn holds_fn_as_data(&self) -> bool {
        self.data
            && self.needs.is_empty()
            && (self.entries().held.is_some()
                || (self.arrows.iter())
                    .flat_map(|a| a.params.iter())
                    .any(|p| p.held_function().is_some()))
    }
}

impl Clone for Facts {
    fn clone(&self) -> Facts {
        Facts::default()
    }
}

impl PartialEq for Facts {
    fn eq(&self, _: &Facts) -> bool {
        true
    }
}

impl Eq for Facts {}

impl std::hash::Hash for Facts {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl fmt::Debug for Facts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("_")
    }
}

/// What [`Facts`] holds. Both sets are persistent and shared with the facts of the functions
/// it holds, so a function around one does not copy them: the larger set is kept and the
/// smaller one added to it.
#[derive(Default)]
pub struct VarFacts {
    /// The class variables.
    pub classes: imbl::OrdSet<Arc<str>>,
    /// The other variables, with its own, bounded and held ones.
    pub names: imbl::OrdSet<Arc<str>>,
    /// The first `n` such that `names` lacks the `n`th variable name (`var_name`).
    pub free: usize,
}

impl VarFacts {
    /// Whether it holds the variable `v`.
    pub fn holds(&self, v: &str) -> bool {
        self.classes.contains(v) || self.names.contains(v)
    }

    /// The facts of the arrows and needs of `s`, worked out now; for a signature not yet
    /// held in a type, which may still change.
    pub fn of(s: &Sig) -> VarFacts {
        let mut g = VarFacts::default();
        let mut added = Added::default();
        g.tys(sig_tys(s), &mut added);
        let extra = s.bounds.keys().chain(&s.own).chain(&s.held);
        extra.for_each(|v| g.add_to(false, v, &mut added));
        g.free = g.free.max(s.named);
        while g.names.contains(&*var_name(g.free)) {
            g.free += 1;
        }
        g
    }

    /// Adds the variables of the types `roots`, at any depth: the facts of each function they
    /// hold as it keeps them, and each row and payload shape that may hold a variable
    /// ([`VarBits`]) entered once. A row keeps no set of its own, which for each node of a
    /// shared DAG would be its transitive closure (question A8), so the cost is that of the
    /// rows and shapes that hold variables, as at the first walk of them.
    fn tys<'a>(&mut self, roots: impl IntoIterator<Item = &'a Ty>, added: &mut Added<'a>) {
        let mut seen = HashSet::new();
        let mut stack: Vec<&Ty> = roots.into_iter().collect();
        while let Some(t) = stack.pop() {
            for v in &t.vars {
                self.add_to(class_id(v).is_some(), v, added);
            }
            for s in &t.fns {
                self.held(s.facts());
            }
            for r in &t.tuples {
                self.free = self.free.max(r.0.bits.free);
                if !r.0.bits.is_empty() && seen.insert(r.node()) {
                    stack.extend(r.iter());
                }
            }
            for s in t.payload_shapes() {
                self.free = self.free.max(s.bits.free);
                if !s.bits.is_empty() && seen.insert(s.node()) {
                    stack.extend(s.items.iter().chain(s.fields.values()));
                }
            }
        }
    }
    /// Adds the facts of a function it holds: of each set, the larger is kept and the smaller
    /// one added to it, so each variable is copied O(log n) times over a nest of n.
    fn held(&mut self, f: &VarFacts) {
        merge(&mut self.classes, &f.classes);
        merge(&mut self.names, &f.names);
        self.free = self.free.max(f.free);
    }

    /// Adds the variable `v` to its classes (`class`) or to its names, unless this walk has
    /// added it to that set already (`added`).
    // Complexity tradeoff (FAIL-ratio-payload-renamed): naive version, each occurrence of a
    // name looked up in the persistent ordered set ([`add`]), O(log n) string comparisons per
    // occurrence. A variable of a signature is met several times over (in the arrows, as an own
    // variable, by its bound, as held): `n` bounded variables in a payload and its result made
    // 5n lookups, 92M of the 146M instructions of the facts of 16000 (callgrind), the first
    // fit of a signature paying them. Used: a hash set of the names this walk added, one O(1)
    // hash per occurrence and one ordered lookup per distinct name (115M with SipHash, whose
    // 43M is the hashing; [`AddressHasher`]'s folded multiply per byte is a few instructions
    // per byte). Given up: the hash set's memory, one entry per distinct name, for the walk
    // only, and a hash with a fixed key, which names chosen to collide could slow to a linear
    // probe per name; the result is the same. A name added by a held function's facts
    // ([`Self::held`]) is not in `added`, so [`add`] still looks for it.
    fn add_to<'a>(&mut self, class: bool, v: &'a Arc<str>, added: &mut Added<'a>) {
        if !added.insert((class, &**v)) {
            return;
        }
        match class {
            true => add(&mut self.classes, v),
            false => add(&mut self.names, v),
        }
    }
}

/// The variables a walk of [`VarFacts`] has added, each with whether it went to the classes.
type Added<'a> = HashSet<(bool, &'a str), std::hash::BuildHasherDefault<AddressHasher>>;

/// What a row or payload shape keeps of the variables it holds at any depth, inside functions
/// and payloads too, in place of their set (CK-data-memo, question A8): the smallest and the
/// largest `k` of its class variables `$k`, a bit for each class variable and one for each
/// other variable, which other variables may share, and the first variable name the functions
/// it holds leave free. Each is made from its components' in `O(1)` per row or function a
/// component holds at its outer level. A set for each row is the transitive closure of a DAG:
/// a row made from two that share no variable, `z(k) = (x(k), y(k))`, copied one of the two
/// sets, `O(n^2 log n)` over `n` rows (COMPLEXITY.md F93). The sets of a type's variables are
/// worked out by a walk ([`Ty::var_facts`]).
// Complexity tradeoff: the bits and the range of classes say only that a row may hold a
// variable, so a replacement may rebuild a row that holds none of the variables it binds: one
// that binds a class `$k` inside the row's range and on one of its bits (`$k` and `$(k + 64)`
// share one), or a name whose hash shares a bit with one of the row's names. It then costs
// the rows that may hold one, not those that do: at worst `O(rows)` per replacement, against
// `O(n^2 log n)` to keep exact sets. The classes a check binds are mostly newer or older than
// all those of the rows it meets (a call's fresh classes, a signature's own), which the range
// tells apart. Tests `replacing_in_rows_shared_on_many_paths_scales`,
// `rows_shared_on_many_paths_scale` and `rows_made_from_disjoint_variable_sets_scale`
// (l01_26); COMPLEXITY.md F93. Open: rows whose classes cover every bit and a wide range,
// or whose names cover every bit, met by `n` replacements of variables they do not hold,
// cost `O(n^2)` (test `replacing_variables_no_row_holds_in_rows_on_every_bit_scales`,
// 61.7 times the bytes for 8 times the rows, deferred to plan row CK-every-bit in
// wt/scratch/deferred-tests/CK-every-bit.rs): COMPLEXITY.md CK-every-bit, open for
// the hard-algorithm cross-review XR-algos.
#[derive(Clone, Copy, Debug)]
struct VarBits {
    /// The smallest `k` of a class variable `$k`, `usize::MAX` for none.
    lo: usize,
    /// The largest `k` of a class variable `$k`, 0 for none.
    hi: usize,
    /// Bit `k mod 64` for each class variable `$k`.
    classes: u64,
    /// A bit for each other variable, by the hash of its name.
    names: u64,
    /// The first `n` such that no function it holds holds the `n`th variable name, or more
    /// ([`VarFacts::free`]); the largest of its functions'.
    free: usize,
}

impl Default for VarBits {
    fn default() -> VarBits {
        VarBits {
            lo: usize::MAX,
            hi: 0,
            classes: 0,
            names: 0,
            free: 0,
        }
    }
}

impl VarBits {
    /// The bit of the variable `v`.
    fn of_var(v: &str) -> VarBits {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        match class_id(v) {
            Some(k) => VarBits {
                lo: k,
                hi: k,
                classes: 1 << (k % 64),
                ..VarBits::default()
            },
            None => VarBits {
                names: 1 << (BuildHasherDefault::<DefaultHasher>::default().hash_one(v) % 64),
                ..VarBits::default()
            },
        }
    }

    /// The bits of the facts `f` of a function.
    fn of_facts(f: &VarFacts) -> VarBits {
        let mut b = VarBits {
            free: f.free,
            ..VarBits::default()
        };
        (f.classes.iter().chain(&f.names)).for_each(|v| b.add(VarBits::of_var(v)));
        b
    }

    /// Adds `other`.
    fn add(&mut self, other: VarBits) {
        self.lo = self.lo.min(other.lo);
        self.hi = self.hi.max(other.hi);
        self.classes |= other.classes;
        self.names |= other.names;
        self.free = self.free.max(other.free);
    }

    /// Adds the bits of `t`, at the cost of its outer level: its rows, payload shapes and
    /// functions each keep theirs.
    fn ty(&mut self, t: &Ty) {
        t.vars.iter().for_each(|v| self.add(VarBits::of_var(v)));
        t.tuples.iter().for_each(|r| self.add(r.0.bits));
        t.payload_shapes().for_each(|s| self.add(s.bits));
        t.fns.iter().for_each(|s| self.add(s.bits()));
    }

    /// Whether it has no variable's bit.
    fn is_empty(&self) -> bool {
        self.classes == 0 && self.names == 0
    }
}

/// The variables a [`Binds`] binds, as [`VarBits`] reads them: how many are on each bit, the
/// bits on which some are, and the `k` of each class variable `$k` in order, so a row whose
/// range of classes holds none of them is found in `O(log)` of their number. Kept by the
/// binds as they change, each change in `O(log)`.
#[derive(Clone)]
struct BindKeys {
    /// How many names are on each bit of [`VarBits::names`].
    names: [u32; 64],
    /// How many class variables are on each bit of [`VarBits::classes`].
    classes: [u32; 64],
    /// The bits of the names and of the classes on which some are.
    bits: VarBits,
    /// The `k` of each class variable `$k` among them.
    ks: imbl::OrdSet<usize>,
}

impl BindKeys {
    /// The variables of `binds`.
    fn of(binds: &BindMap) -> BindKeys {
        let mut keys = BindKeys {
            names: [0; 64],
            classes: [0; 64],
            bits: VarBits::default(),
            ks: imbl::OrdSet::new(),
        };
        binds.keys().for_each(|v| keys.add(v));
        keys
    }

    /// Adds the variable `v`, which it does not hold.
    fn add(&mut self, v: &str) {
        let b = VarBits::of_var(v);
        let (counts, bit) = match class_id(v) {
            Some(k) => {
                self.ks.insert(k);
                (&mut self.classes, b.classes)
            }
            None => (&mut self.names, b.names),
        };
        counts[bit.trailing_zeros() as usize] += 1;
        self.bits.classes |= b.classes;
        self.bits.names |= b.names;
    }

    /// Removes the variable `v`, which it holds.
    fn remove(&mut self, v: &str) {
        let b = VarBits::of_var(v);
        let (counts, bits, bit) = match class_id(v) {
            Some(k) => {
                self.ks.remove(&k);
                (&mut self.classes, &mut self.bits.classes, b.classes)
            }
            None => (&mut self.names, &mut self.bits.names, b.names),
        };
        let i = bit.trailing_zeros() as usize;
        counts[i] -= 1;
        if counts[i] == 0 {
            *bits &= !bit;
        }
    }

    /// Whether a row or shape of the bits `b` may hold one of them: a name that shares a bit,
    /// or a class on one of `b`'s bits and inside its range.
    fn meets(&self, b: &VarBits) -> bool {
        if self.bits.names & b.names != 0 {
            return true;
        }
        self.bits.classes & b.classes != 0 && self.ks.range(b.lo..=b.hi).next().is_some()
    }
}

/// Adds `other` to `set`, keeping the larger of the two and adding to it what the smaller
/// holds and it lacks.
///
/// Two ways find that, run a step each in turn until either ends: inserting each variable of
/// the smaller set, `O(m log n)` for sets of `m` and `n`, and the difference of the two
/// (`imbl`'s `diff`), which steps over the nodes they share, so that a set made from the other
/// by adding a few variables costs about the depth of the tree. Either alone fails a family:
/// the insertions merge a set into one it was made from at its full size, `O(n^2 log n)` over
/// `n` rows `t(k) = (t(k-1), (t(k-1), Vk))`, and the difference walks the larger set when the
/// two share no node.
// Complexity tradeoff (COMPLEXITY.md row F93): naive version, the insertions alone,
// O(n^2 log n) over that family. Used: the two ways interleaved, at most twice the cheaper of
// the two, O(m log n) or about the depth of the tree when the sets share their nodes.
// Tradeoff: a constant factor of two on sets where only one way is fast; the row is fixed
// only in part (see it for the family that stays above n log n).
fn merge(set: &mut imbl::OrdSet<Arc<str>>, other: &imbl::OrdSet<Arc<str>>) {
    let (large, small) = match other.len() > set.len() {
        true => (other, &*set),
        false => (&*set, other),
    };
    let mut out = large.clone();
    let mut lacks = large.diff(small);
    for v in small {
        add(&mut out, v);
        match lacks.next() {
            Some(imbl::ordset::DiffItem::Add(v)) => add(&mut out, v),
            Some(imbl::ordset::DiffItem::Remove(_)) => {}
            None => break,
        }
    }
    *set = out;
}

/// Adds `v` to `set`. A set shared with the facts of another signature is copied along the
/// path to `v` by an insertion, so a variable it already holds is not inserted again.
fn add(set: &mut imbl::OrdSet<Arc<str>>, v: &Arc<str>) {
    if !set.contains(v) {
        set.insert(v.clone());
    }
}

/// A use the body of a generic function makes of a value whose type is a variable: checked
/// again at each call, on the type the call binds the variable to.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Need {
    /// The type of the value used, a variable of the signature.
    pub on: Ty,
    /// The use.
    pub kind: NeedKind,
    /// What the use gives, a variable of the signature, if it gives a value.
    pub result: Option<Ty>,
    /// The use in the body.
    pub span: Span,
}

/// The operator a fold `m >< op` folds by (DESIGN.md sec:reduction): an operator section, as
/// `(+)`, or the prelude word `max` or `min`, whose associativity, commutativity and
/// idempotence are built in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Reducer {
    /// An operator section, `(op)`.
    Op(zedc_syntax::ast::BinaryOp),
    /// The prelude word `min`.
    Min,
    /// The prelude word `max`.
    Max,
}

impl Reducer {
    /// The operator as a program writes it after `><`: `(+)`, `min`, `max`.
    pub fn written(self) -> String {
        match self {
            Reducer::Op(op) => format!("({})", op.as_str()),
            Reducer::Min => "min".into(),
            Reducer::Max => "max".into(),
        }
    }
}

/// A built-in word that reads one level of a family, recorded by a [`NeedKind::Level`] when
/// its receiver's type is a type parameter (plan row FP-ops-generic-receivers).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LevelWord {
    /// `x.count`.
    Count,
    /// `x.first`.
    First,
    /// `x.last`.
    Last,
    /// `x.any(f)`.
    Any,
    /// `x.all(f)`.
    All,
    /// `x.find(f)`.
    Find,
    /// `x.scan(op)`.
    Scan(Reducer),
    /// `x.chunkBy(f)`.
    ChunkBy,
}

impl LevelWord {
    /// The word as the checker's messages quote it: `count`'s check names it "`count`", a
    /// scan's ([`FoldForm::Scan`]) "`.scan`".
    pub fn word(self) -> &'static str {
        match self {
            LevelWord::Count => "`count`",
            LevelWord::First => "`first`",
            LevelWord::Last => "`last`",
            LevelWord::Any => "`any`",
            LevelWord::All => "`all`",
            LevelWord::Find => "`find`",
            LevelWord::Scan(_) => "`.scan`",
            LevelWord::ChunkBy => "`chunkBy`",
        }
    }
}

/// How a program wrote a fold of one level, for the messages of the checker's `fold_level`.
/// A need [`NeedKind::Reduce`] carries it, so that a fold checked again at each call of a
/// generic function names the form the program wrote (row FAIL-need-fold-form-message).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FoldForm {
    /// `x >< op`.
    Infix,
    /// `x.reduce(op)`, which DESIGN.md defines as `x >< op` (the method register's `reduce`
    /// row, `fold(m, op, ev)`).
    Reduce,
    /// `x.sum` on a family, `x >< (+)` (the method register's `sum` row).
    Sum,
    /// `x.scan(op)`, the family of the folds of `x`'s prefixes (the method register's `scan`
    /// row), each of which is checked as the fold `x >< op` is.
    Scan,
}

impl FoldForm {
    /// Whether the fold's checks record the carrier and the identity it met at its site for
    /// the checker's `finish`, which gives the fold its identity, or one per call of a generic
    /// function (`split_folds`). A scan's does not: each entry of a scan folds a prefix that
    /// holds that entry, so no prefix is empty and no scan reads an identity (the elaborator's
    /// `scan_term` takes none), and a generic scan by `max` checked at `int` and at `f64`,
    /// whose empty folds differ, needs no body per call (plan row FP-ops-generic-receivers).
    pub fn records_identity(self) -> bool {
        self != FoldForm::Scan
    }

    /// The fold as code, quoted.
    pub fn word(self) -> &'static str {
        match self {
            FoldForm::Infix => "`><`",
            FoldForm::Reduce => "`.reduce`",
            FoldForm::Sum => "`.sum`",
            FoldForm::Scan => "`.scan`",
        }
    }

    /// The fold named in a sentence, before its operator.
    pub fn fold_name(self) -> &'static str {
        match self {
            FoldForm::Infix => "a fold `><`",
            FoldForm::Reduce => "a fold `.reduce`",
            FoldForm::Sum => "a fold `.sum`",
            FoldForm::Scan => "a scan `.scan`",
        }
    }

    /// The fold by the operator written `written`, named in a sentence.
    pub fn what(self, written: &str) -> String {
        match self {
            FoldForm::Infix => format!("a fold `><` by `{written}`"),
            FoldForm::Reduce => format!("a fold `.reduce({written})`"),
            FoldForm::Sum => "a fold `.sum`".to_string(),
            FoldForm::Scan => format!("a scan `.scan({written})`"),
        }
    }

    /// The fold by `written` of a small family, as a repair writes it.
    pub fn example(self, written: &str) -> String {
        match self {
            FoldForm::Infix => format!("{{0 -> 1, 1 -> 2}} >< {written}"),
            FoldForm::Reduce => format!("{{0 -> 1, 1 -> 2}}.reduce({written})"),
            FoldForm::Sum => "{0 -> 1, 1 -> 2}.sum".to_string(),
            FoldForm::Scan => format!("{{0 -> 1, 1 -> 2}}.scan({written})"),
        }
    }
}

/// What a use that takes data does with its value ([`NeedKind::Data`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DataUse {
    /// Interpolation and `String`: the value is shown as text.
    Show,
    /// `==` and `!=`.
    Compare,
    /// A key: of a family display, of `in`, or of a read of a family.
    Key,
    /// A failure merged into `#errs`.
    Merge,
}

impl DataUse {
    /// What the use cannot do with a value that may hold a function, as the headline of its
    /// rejection says it after "Cannot".
    pub fn cannot(self) -> &'static str {
        match self {
            DataUse::Show => "show a value that may hold a function",
            DataUse::Compare => "compare a value that may hold a function",
            DataUse::Key => "use a value that may hold a function as a key",
            DataUse::Merge => "merge a failure that may hold a function into `#errs`",
        }
    }
}

/// The uses a [`Need`] records.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NeedKind {
    /// `v[i]` with a literal: a tuple's component, or a family's entry.
    Component {
        /// The component, if the literal is a component number.
        i: Option<usize>,
        /// The literal's type, a family's key.
        key: Ty,
        /// Where the bracket is written: the need keeps it as it is copied into a caller, so
        /// that a function met at a call records the bracket's meaning there (row
        /// FAIL-curried-index-untyped-param).
        site: Span,
    },
    /// `v[k]` with a key of this type: an application.
    Index(Ty),
    /// `a, b, ... = v` into `n` names: component `i` of a tuple of exactly `n`.
    Destructure {
        /// The component.
        i: usize,
        /// The number of names, the tuple's length.
        n: usize,
    },
    /// A call of `v`, named `what`, with arguments of these types.
    Call {
        /// The value's name in the call.
        what: Arc<str>,
        /// The types of the positional arguments.
        positional: Vec<Ty>,
        /// The names and types of the named arguments.
        named: Vec<(Arc<str>, Ty)>,
        /// Whether the call ends in `...`.
        curry: bool,
    },
    /// A use, `what`, that takes data: the value holds no function. The use does with the
    /// value what [`DataUse`] says, which its message names.
    Data(Arc<str>, DataUse),
    /// An argument, of `what`, at a parameter of the closed type `ty`.
    Into {
        /// The function called.
        what: Arc<str>,
        /// The parameter's type.
        ty: Ty,
    },
    /// A name a pattern binds: what the payload of an atom named `atom` holds at `slot`.
    Payload {
        /// The atom's name.
        atom: Arc<str>,
        /// The place in its payload.
        slot: Slot,
    },
    /// A test's narrowing: what is left of the value where the test fails.
    Narrow(Narrow),
    /// `min` or `max`, the word `word`, named `what`, with the value as one operand and a
    /// value of `other` as the other, which holds a tuple: the value is the first operand
    /// if `first` (DESIGN.md sec:reduction, item 5).
    Order {
        /// The function called.
        what: Arc<str>,
        /// The word, `min` or `max`.
        word: Arc<str>,
        /// The other operand's type.
        other: Ty,
        /// Whether the value is the first operand.
        first: bool,
    },
    /// A use that takes an int in its domain, as `^`'s exponent and a bit word's operand do,
    /// of a value whose ints the body shows no bound of and which is no parameter: the value
    /// holds no int, or only ints listed in the domain (CHK-need-bound).
    NoInt(IntDomain),
    /// `^` on ints with an exponent not shown to be at least 0, of its base or its exponent:
    /// the base holds no int, and the exponent holds no int or only ints listed at least 0
    /// (CHK-need-bound). The error's words are made where the `^` is.
    Power(Arc<PowerUse>),
    /// `sum` of the value: a tuple of numbers, whose sum the use gives (CHK-need-bound).
    Sum,
    /// The entries of the value, a family: what `map`, `where`, `flatMap` and `group` pass
    /// their function, the misses `#notFound` and `#outOfBounds` and the loose atoms left out,
    /// as those words leave them out. Recorded on a receiver whose type is a class before a
    /// lambda with no written parameter type is checked, so that the lambda's parameter is
    /// this use's result and is bound before any use the lambda's body makes of it (plan row
    /// FAIL-map-lambda-calls-param-entry).
    Entries,
    /// `v.sum` written at the span, on a value whose type is a type parameter: a family
    /// folds its one level by `(+)`, as [`NeedKind::Reduce`] does, and a tuple is summed as
    /// [`NeedKind::Sum`] sums it (DESIGN.md, the method register: `tot = xs.sum; // = xs >< (+)`).
    /// The span is the call's own, as at [`NeedKind::Reduce`], so that the fold's checks at
    /// every call are found together.
    SumMethod {
        /// Where the `.sum` is written.
        site: Span,
        /// The families with no entries joined with the value at the `.sum`, as `[]` in
        /// `(if b { xs } else { [] }).sum`, or the empty type: the use is met on the value's
        /// type joined with them, as the receiver is at the call's types, so an empty level
        /// takes the carrier the value gives, or none beside a tuple (DESIGN.md
        /// sec:type_resolution, rule 6). They hold no variable.
        beside: Ty,
    },
    /// `v.map(f)`, or `v.where(f)` when `filter` is set, with `f` of type `f`: the value is a
    /// family, and the use gives the family `map` or `where` makes of it (step L3.2).
    Map {
        /// The function's type.
        f: Ty,
        /// Whether the use is `where`.
        filter: bool,
    },
    /// `v.group(f)`, with `f` of type `f` and `v` written at `recv`: the value is a family of
    /// one level, and the use gives the family `group` makes of it (DESIGN.md sec:grouping).
    Group {
        /// The function's type.
        f: Ty,
        /// Where the receiver is written, for the error's words.
        recv: Span,
    },
    /// A one-level word on the value, `v.count`, `v.any(f)`, `v.scan(op)` and the rest of
    /// [`LevelWord`]: the value is a family, and the use gives what the word gives of it
    /// (plan row FP-ops-generic-receivers).
    Level {
        /// The word.
        word: LevelWord,
        /// The type of the function the word takes, or the empty type for a word that takes
        /// none.
        f: Ty,
        /// Where the word is written: a scan's fold is checked as written there, as a
        /// [`NeedKind::Reduce`]'s is.
        site: Span,
    },
    /// The remap written at `at`, of a source of type `src` that holds the value: `src` is the
    /// value's own variable where the value is the source, or a family that holds the value
    /// below known levels, as `{ 0 -> r }` holds `r`. The source, with the value's type in the
    /// place of its variable, is a family of as many levels as the remap's `as` pattern names,
    /// and the use gives the remap's family (DESIGN.md sec:remap_law). The key expressions are
    /// checked when the value's type is in hand.
    Remap {
        /// Where the remap is written.
        at: Span,
        /// The type of the remap's source, which holds the value's variable.
        src: Ty,
        /// How far the source's key types are in hand when the need is made: the first key
        /// level of `src` that holds a class not yet resolved, and the number of variables
        /// that name such classes there. A check of the need goes on only at a type that
        /// makes the source further along, a later level or fewer such variables at this one,
        /// so a chain of checks ends (the proof is at `remap_of`, crates/zedc-check).
        rank: (usize, usize),
    },
    /// `v >< (op)` at the fold written at the span: the value is a family whose entries `op`
    /// folds, and the use gives the fold (step L3.2; DESIGN.md sec:reduction). The span is the
    /// fold's own, where a need met at a call is met at the call's, so that the checks of one
    /// fold at every call are found together, as its identity needs (`Ck::finish`). The form
    /// is how the program wrote the fold, `><`, `.reduce` or `.sum`, which a message at the
    /// call names.
    Reduce(Reducer, Span, FoldForm),
    /// `v.foldl(init, f)`, or `v.foldr(f, init)` when `right` is set: the value is a rank whose
    /// entries `f` folds from `init`, and the use gives the accumulator (step L3.3; DESIGN.md
    /// sec:reduction). `tys` is the types of `init` and of `f`, in that order; with `by` set
    /// the value is `f` instead, a function not yet known that folds a receiver of known type,
    /// and `tys` is the types of `init` and of the receiver (row
    /// FAIL-fold-unknown-fn-known-family).
    Fold {
        /// The types of the start value and of the function, or with `by`, of the receiver.
        tys: Vec<Ty>,
        /// Whether the use is `foldr`.
        right: bool,
        /// Whether the value is the function, not the receiver.
        by: bool,
    },
    /// A use that takes an int in its domain, of the value of the parameter at position
    /// `param` of the function whose signature holds it: each call shows the ints of its
    /// argument in the domain, or passes on a parameter of its own, whose calls then show them
    /// (CHK-need-bound). The need is on the parameter, not on a variable, so its `on` is the
    /// empty type and its `span` the use.
    InDomain {
        /// The use and its domain.
        domain: IntDomain,
        /// The parameter's position.
        param: usize,
        /// The calls that passed the parameter on, the last first.
        via: Option<Arc<Via>>,
        /// For the `width` of a bit word curried with `...`, as `r = bitReverse(256, ...)`,
        /// the span of that call: each call of the function it gives checks every domain of
        /// the word, with the operands the curried call gave and the width the call gives,
        /// so `domain` is only the width's own `int[0..]` (FAIL-bitword-curry-domain).
        bits: Option<Span>,
    },
}

/// What the error of a [`NeedKind::Power`] need is made from: the code it quotes is kept as
/// spans of the program's text and written only when the error is.
// Complexity tradeoff (COMPLEXITY.md row POW-rat-literal-ops): naive version, the base's code
// and each repair written out where the `^` is, O(k) for a power of size k and O(n^2) for n
// nested powers, as `((2)^-1)^-1`, though most needs never fail. Used: spans and the few facts
// the repairs depend on, O(1) a need besides the exponent's steps; the words cost O(k) only
// for an error.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PowerUse {
    /// The exponent as the error shows it, for a need on the base; `None` on the exponent,
    /// whose ints are shown when they flow in.
    pub exponent: Option<Arc<str>>,
    /// The base's span.
    pub base: Option<Span>,
    /// The exponent's span.
    pub exponent_at: Option<Span>,
    /// The power's span.
    pub at: Span,
    /// Whether every value of the exponent is below 0, for a need on the base.
    pub negative: bool,
    /// The steps of the derivation of the exponent, for a need on the base.
    pub steps: Arc<[zedc_syntax::ast::Note]>,
    /// The base, if it is a parameter of the function the `^` is in, which a repair declares a
    /// float.
    pub param: Option<Arc<str>>,
    /// The exponent, if it is a name bound once, which a test narrows.
    pub tested: Option<Arc<str>>,
    /// Whether a repair tests the exponent: it may be at least 0 and holds no type variable.
    pub test: bool,
    /// Whether the exponent takes a float as it is: a literal, or of a type variable.
    pub exponent_takes_float: bool,
    /// Whether the base takes a float as it is: a literal, or of a type variable.
    pub base_takes_float: bool,
    /// Whether the base is an `int`, which widens to a `rat` with no failure.
    pub base_int: bool,
    /// The type variable of the base, if it has one alone, as a literal's class: the power's
    /// value has the base's type, so a repair that makes it a `rat` or a float is checked
    /// against the carriers that class may still take.
    pub base_var: Option<Arc<str>>,
}

/// The ints a use takes, as `^`'s exponent and a bit word's operand do: those at least 0, and
/// below `2 ^ width` for an operand read as `width` binary digits (CHK-need-bound); or, for a
/// parameter declared with a range, as `x: int[1..]`, the ints of that range (DESIGN.md L1.39).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IntDomain {
    /// The use, in words, as an error states it.
    pub what: Arc<str>,
    /// The name of the operand or parameter the use takes, as `x` of `popCount`: a repair
    /// that binds the value to a name before testing it uses this one.
    pub name: Arc<str>,
    /// The smallest width of the use, for an operand read as that many digits.
    pub below_two_pow: Option<Width>,
    /// The range a parameter is declared with, which is then the whole domain: the ints from
    /// 0 are not asked for, and `below_two_pow` is none.
    pub written: Option<WrittenRange>,
    /// For a parameter declared a partial map `K ->? V`, what its key domain takes
    /// ([`KeyUse`]); then `written` and `below_two_pow` are none and the need is on the keys
    /// of the map passed, not on an int.
    pub key: Option<Arc<KeyUse>>,
}

/// What a parameter declared a partial map `K ->? V` takes of the map a call passes it
/// (RANGE-keys): its keys inside the ranges written on its key, `m: int[5..<10] ->? int` or
/// `m: (int[0..<2], int[0..<3]) ->? int`, and, where a remap reads it, a family. A remap
/// rearranges the entries of a family, and its witness that no two keys collide reads the
/// ranges (DESIGN.md sec:grouping, the witness catalog); a function of the type has no
/// entries, and a key outside a range could collide.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct KeyUse {
    /// Each range written on the key: on the whole key (`None`), or on its tuple component
    /// at the index, in the order written.
    pub ranges: Vec<(Option<usize>, WrittenRange)>,
    /// Whether a remap reads the map, which must then be a family.
    pub family: bool,
}

/// A range written as the type of a parameter of type `int`, as `x: int[1..=9]` (DESIGN.md
/// L1.12, L1.39): its least and its greatest int, each none where that end is open, and its
/// text as a signature prints it, each end inclusive: `int[1..=9]`, `int[1..]`,
/// `int[_..=9]`. `int[0..<10]` and `int[0..=9]` are one type (L1.24) and one text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrittenRange {
    /// The least int, if the range has one.
    pub low: Option<Value>,
    /// The greatest int, if the range has one.
    pub high: Option<Value>,
    /// The text, `int[1..=9]`.
    pub text: Arc<str>,
}

impl WrittenRange {
    /// The range from `low` through `high`, either open where it is none.
    pub fn new(low: Option<Value>, high: Option<Value>) -> Self {
        let text = match (&low, &high) {
            (Some(l), Some(h)) => format!("int[{l}..={h}]"),
            (Some(l), None) => format!("int[{l}..]"),
            (None, Some(h)) => format!("int[_..={h}]"),
            (None, None) => "int[_..]".to_string(),
        };
        WrittenRange {
            low,
            high,
            text: text.into(),
        }
    }

    /// Whether it holds the int `v`.
    pub fn holds(&self, v: &Value) -> bool {
        let ge = |b: &Value| v.surface_cmp(b).is_some_and(|o| o.is_ge());
        let le = |b: &Value| v.surface_cmp(b).is_some_and(|o| o.is_le());
        self.low.as_ref().is_none_or(ge) && self.high.as_ref().is_none_or(le)
    }

    /// Whether each int it holds is held by `outer`: its least at least `outer`'s, and its
    /// greatest at most `outer`'s, an open end of `outer` holding anything on its side. O(1).
    pub fn within(&self, outer: &WrittenRange) -> bool {
        let low = match (&self.low, &outer.low) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some(a), Some(b)) => a.surface_cmp(b).is_some_and(|o| o.is_ge()),
        };
        let high = match (&self.high, &outer.high) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some(a), Some(b)) => a.surface_cmp(b).is_some_and(|o| o.is_le()),
        };
        low && high
    }
}

impl std::hash::Hash for WrittenRange {
    /// Equal ranges have one text.
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.text.hash(h);
    }
}

/// The ranges a parameter is written with ([`SParam::range`]): one on the whole of it, as
/// `d: int[1..=9]` or the key `int[5..=9] ->? V`, or one on each component of its tuple type
/// that has one, none on the others, as the key `((int[0..=1], int)) ->? V`
/// (RANGE-key-component-print).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ParamRange {
    /// A range on the whole parameter, whose type is `int`.
    Int(WrittenRange),
    /// A range on each component of a tuple type, by index, or none.
    Parts(Arc<[Option<WrittenRange>]>),
}

impl ParamRange {
    /// The range on the whole parameter, if it has one.
    pub fn int(&self) -> Option<&WrittenRange> {
        match self {
            ParamRange::Int(r) => Some(r),
            ParamRange::Parts(_) => None,
        }
    }

    /// Pushes to `parts` the text of the parameter of type `t` written with the ranges
    /// `range`, standing at `at`: a range in place of the type it is written on, each end
    /// inclusive, and the type `t` alone where `range` is none. A range on components prints
    /// as [`Row::parts`] prints the row, each ranged component's range in its place; it
    /// prints `t` alone where `t` is not one row of as many components, which
    /// [`ParamRange::Parts`] is not built for.
    fn parts<'a>(
        range: Option<&'a ParamRange>,
        t: &'a Ty,
        at: PrintAt,
        parts: &mut Vec<Print<'a>>,
    ) {
        let rs = match range {
            Some(ParamRange::Int(r)) => return parts.push(Print::Text(&r.text)),
            Some(ParamRange::Parts(rs)) => rs,
            None => return parts.push(Print::Ty(t, at)),
        };
        let Some(row) = t.lone_row().filter(|row| row.len() == rs.len()) else {
            return parts.push(Print::Ty(t, at));
        };
        let wrap = row.wraps(at);
        parts.push(Print::Text(if wrap { "((" } else { "(" }));
        let mut one = true;
        for (c, r) in row.iter().zip(rs.iter()) {
            between(parts, &mut one, ", ");
            parts.push(match r {
                Some(r) => Print::Text(&r.text),
                None => Print::Ty(c, PrintAt::Any),
            });
        }
        parts.push(Print::Text(match (row.len() == 1, wrap) {
            (true, _) => ",)",
            (false, true) => "))",
            (false, false) => ")",
        }));
    }
}

/// The width of a bit word, an int at least 0, kept as its value: `2 ^ width` is never built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Width(pub Value);

impl std::hash::Hash for Width {
    /// A machine int hashes as itself and a wider one as nothing, which equal widths agree on.
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        if let Value::Int(n) = &self.0 {
            n.hash(h);
        }
    }
}

/// A call that passed its function's parameter on as the argument of a parameter with a
/// [`NeedKind::InDomain`] need, and the calls that passed that one on before it.
///
/// Two are compared one call at a time, and the same chain at once, and only the first call is
/// hashed, so a chain of `n` calls costs O(1) to hash, not O(n) at each of its `n` links.
///
/// Complexity tradeoff: naive version, each need holds its own copy of the chain, with its
/// notes written out, so a chain of `n` wrappers costs O(n) at each wrapper and O(n²) in all
/// (built at every call, the notes took 28.4 times the bytes from 200 to 1,600 wrappers).
/// Used: each link holds the one before it shared, so a wrapper adds one link, O(1), and the
/// notes are written from the chain only for an error, O(links). Tradeoffs: a chain lives as
/// long as any need that holds a link of it. COMPLEXITY.md row F123.
#[derive(Clone, Debug)]
pub struct Via {
    /// The call.
    pub at: Span,
    /// The call, in words, as an error states it.
    pub text: Arc<str>,
    /// The call before it.
    pub next: Option<Arc<Via>>,
}

impl PartialEq for Via {
    fn eq(&self, other: &Via) -> bool {
        let (mut a, mut b) = (self, other);
        loop {
            if std::ptr::eq(a, b) {
                return true;
            }
            if a.at != b.at || a.text != b.text {
                return false;
            }
            match (&a.next, &b.next) {
                (Some(x), Some(y)) => (a, b) = (x, y),
                (None, None) => return true,
                _ => return false,
            }
        }
    }
}

impl Eq for Via {}

impl std::hash::Hash for Via {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.at.hash(h);
        self.text.hash(h);
    }
}

impl Drop for Via {
    /// Unlinks the chain one call at a time, so a chain of any length needs no stack as deep.
    fn drop(&mut self) {
        let mut next = self.next.take();
        while let Some(v) = next {
            next = match Arc::try_unwrap(v) {
                Ok(mut v) => v.next.take(),
                Err(_) => None,
            };
        }
    }
}

/// What a test leaves of a value where it fails (rule 3 of sec:type_resolution).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Narrow {
    /// `e else d`: what is not a loose atom.
    Loose,
    /// `e else #a -> d`: what is not the atom `#a`, with any payload or none.
    Atom(Arc<str>),
    /// `e is t`, where it is false: what is not in `t`. Only the scalars, atoms and tuples
    /// of `t` are subtracted, so its variables need no binding.
    Not(Ty),
}

/// A place in an atom's payload.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Slot {
    /// The field of this name.
    Field(Arc<str>),
    /// The component at this position.
    Item(usize),
}

impl Need {
    /// It with its variables replaced by `binds` at every depth.
    pub fn replace(&self, binds: &Binds) -> Need {
        self.replace_in(binds, Mode::Replace)
    }

    /// [`Need::replace`], or as `mode` says.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Need {
        let tys = rebuild_tys(&mut Replacer::new(binds, mode), self.tys());
        let mut tys = tys.into_iter();
        self.map_tys(|_| {
            tys.next()
                .expect("a walk makes one type of each type of a need")
        })
    }

    /// It with `f` applied to each of the types [`Need::tys`] gives, in that order.
    fn map_tys(&self, mut f: impl FnMut(&Ty) -> Ty) -> Need {
        Need {
            on: f(&self.on),
            kind: match &self.kind {
                NeedKind::Component { i, key, site } => NeedKind::Component {
                    i: *i,
                    key: key.clone(),
                    site: *site,
                },
                NeedKind::Index(k) => NeedKind::Index(f(k)),
                NeedKind::Map { f: g, filter } => NeedKind::Map {
                    f: f(g),
                    filter: *filter,
                },
                NeedKind::Group { f: g, recv } => NeedKind::Group {
                    f: f(g),
                    recv: *recv,
                },
                NeedKind::Level { word, f: g, site } => NeedKind::Level {
                    word: *word,
                    f: f(g),
                    site: *site,
                },
                NeedKind::Remap { at, src, rank } => NeedKind::Remap {
                    at: *at,
                    src: f(src),
                    rank: *rank,
                },
                NeedKind::Reduce(op, site, form) => NeedKind::Reduce(*op, *site, *form),
                NeedKind::Fold { tys, right, by } => NeedKind::Fold {
                    tys: tys.iter().map(&mut f).collect(),
                    right: *right,
                    by: *by,
                },
                NeedKind::Destructure { i, n } => NeedKind::Destructure { i: *i, n: *n },
                NeedKind::Call {
                    what,
                    positional,
                    named,
                    curry,
                } => NeedKind::Call {
                    what: what.clone(),
                    positional: positional.iter().map(&mut f).collect(),
                    named: named.iter().map(|(n, t)| (n.clone(), f(t))).collect(),
                    curry: *curry,
                },
                NeedKind::Data(what, does) => NeedKind::Data(what.clone(), *does),
                NeedKind::NoInt(d) => NeedKind::NoInt(d.clone()),
                NeedKind::Power(p) => NeedKind::Power(p.clone()),
                NeedKind::Sum => NeedKind::Sum,
                NeedKind::Entries => NeedKind::Entries,
                NeedKind::SumMethod { site, beside } => NeedKind::SumMethod {
                    site: *site,
                    beside: beside.clone(),
                },
                NeedKind::InDomain {
                    domain,
                    param,
                    via,
                    bits,
                } => NeedKind::InDomain {
                    domain: domain.clone(),
                    param: *param,
                    via: via.clone(),
                    bits: *bits,
                },
                NeedKind::Into { what, ty } => NeedKind::Into {
                    what: what.clone(),
                    ty: ty.clone(),
                },
                NeedKind::Payload { atom, slot } => NeedKind::Payload {
                    atom: atom.clone(),
                    slot: slot.clone(),
                },
                NeedKind::Narrow(n) => NeedKind::Narrow(n.clone()),
                NeedKind::Order {
                    what,
                    word,
                    other,
                    first,
                } => NeedKind::Order {
                    what: what.clone(),
                    word: word.clone(),
                    other: f(other),
                    first: *first,
                },
            },
            result: self.result.as_ref().map(f),
            span: self.span,
        }
    }

    /// Every variable in it, in order of first appearance.
    pub fn vars_in(&self, out: &mut Vars) {
        self.tys().for_each(|t| t.vars_in(out));
    }

    /// The types in it that [`Need::replace`] replaces in, in order.
    pub fn tys(&self) -> impl Iterator<Item = &Ty> {
        let (index, positional, named): (_, &[Ty], &[(Arc<str>, Ty)]) = match &self.kind {
            NeedKind::Component { .. }
            | NeedKind::Destructure { .. }
            | NeedKind::Data(..)
            | NeedKind::NoInt(_)
            | NeedKind::Power(_)
            | NeedKind::InDomain { .. }
            | NeedKind::Sum
            | NeedKind::Entries
            | NeedKind::SumMethod { .. }
            | NeedKind::Into { .. }
            | NeedKind::Reduce(..)
            | NeedKind::Payload { .. }
            | NeedKind::Narrow(_) => (None, &[], &[]),
            NeedKind::Index(k)
            | NeedKind::Order { other: k, .. }
            | NeedKind::Map { f: k, .. }
            | NeedKind::Group { f: k, .. }
            | NeedKind::Level { f: k, .. }
            | NeedKind::Remap { src: k, .. } => (Some(k), &[], &[]),
            NeedKind::Call {
                positional, named, ..
            } => (None, positional, named),
            NeedKind::Fold { tys, .. } => (None, tys, &[]),
        };
        std::iter::once(&self.on)
            .chain(index)
            .chain(positional)
            .chain(named.iter().map(|(_, t)| t))
            .chain(&self.result)
    }

    /// Every type in it, those [`Need::tys`] leaves out too, as its hash reads them.
    fn every_ty(&self) -> Vec<&Ty> {
        let more: Vec<&Ty> = match &self.kind {
            NeedKind::Destructure { .. }
            | NeedKind::Data(..)
            | NeedKind::NoInt(_)
            | NeedKind::Power(_)
            | NeedKind::InDomain { .. }
            | NeedKind::Sum
            | NeedKind::Entries
            | NeedKind::Reduce(..)
            | NeedKind::Payload { .. }
            | NeedKind::Narrow(Narrow::Loose | Narrow::Atom(_)) => Vec::new(),
            NeedKind::Component { key: t, .. }
            | NeedKind::Index(t)
            | NeedKind::Map { f: t, .. }
            | NeedKind::Group { f: t, .. }
            | NeedKind::Level { f: t, .. }
            | NeedKind::Remap { src: t, .. }
            | NeedKind::Into { ty: t, .. }
            | NeedKind::SumMethod { beside: t, .. }
            | NeedKind::Order { other: t, .. }
            | NeedKind::Narrow(Narrow::Not(t)) => vec![t],
            NeedKind::Call {
                positional, named, ..
            } => positional
                .iter()
                .chain(named.iter().map(|(_, t)| t))
                .collect(),
            NeedKind::Fold { tys, .. } => tys.iter().collect(),
        };
        std::iter::once(&self.on)
            .chain(more)
            .chain(&self.result)
            .collect()
    }

    /// Every type in it, its own, for [`drop_types`].
    fn into_tys(self) -> impl Iterator<Item = Ty> {
        let more: Vec<Ty> = match self.kind {
            NeedKind::Destructure { .. }
            | NeedKind::Data(..)
            | NeedKind::NoInt(_)
            | NeedKind::Power(_)
            | NeedKind::InDomain { .. }
            | NeedKind::Sum
            | NeedKind::Entries
            | NeedKind::Reduce(..)
            | NeedKind::Payload { .. }
            | NeedKind::Narrow(Narrow::Loose | Narrow::Atom(_)) => Vec::new(),
            NeedKind::Component { key: t, .. }
            | NeedKind::Index(t)
            | NeedKind::Map { f: t, .. }
            | NeedKind::Group { f: t, .. }
            | NeedKind::Level { f: t, .. }
            | NeedKind::Remap { src: t, .. }
            | NeedKind::Into { ty: t, .. }
            | NeedKind::SumMethod { beside: t, .. }
            | NeedKind::Order { other: t, .. }
            | NeedKind::Narrow(Narrow::Not(t)) => vec![t],
            NeedKind::Call {
                mut positional,
                named,
                ..
            } => {
                positional.extend(named.into_iter().map(|(_, t)| t));
                positional
            }
            NeedKind::Fold { tys, .. } => tys,
        };
        std::iter::once(self.on).chain(more).chain(self.result)
    }
}

/// A parameter of a signature.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SParam {
    /// Its name.
    pub name: Arc<str>,
    /// Whether it is passed by position.
    pub positional: bool,
    /// Its default, if it has one: the declaring function's binder, the parameter's index,
    /// and whether the default reads no name of the unit, so a call through a value can
    /// fill it.
    pub default: Option<(usize, usize, bool)>,
    /// The range it is declared with, as `d: int[1..=9]`, which the signature prints in place
    /// of its type `int` (DESIGN.md L1.39); each call is checked against it by a
    /// [`NeedKind::InDomain`] need of the signature. On the one parameter of a partial map,
    /// the ranges written on its key, the whole key's or its components'
    /// ([`ParamRange::Parts`]), which print in the key's place.
    pub range: Option<ParamRange>,
}

/// One arrow: a type for each parameter, and the result.
///
/// An arrow is exact or partial (DESIGN.md sec:type_language, "Morphism types carry two
/// domain bounds"). An exact arrow guarantees its parameter types: a function of it answers
/// at every value of them, so they are both a guarantee and a permission of the function's
/// domain. A partial arrow, `K ->? V` and the upper bound of `L .. U -> V`, only permits: a
/// key of it may be absent, and its lookup answers `#notFound` there, so `result` is its
/// lookup type, `V | #notFound`, which is what an application of it gives. A partial arrow and
/// an exact one with the same types are two types: `int ->? 1` is not `int -> 1 | #notFound`,
/// whose domain is all of `int`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Arrow {
    /// The parameters' types.
    pub params: Vec<Ty>,
    /// The result: for a partial arrow, its lookup type, its value type with `#notFound`.
    pub result: Ty,
    /// Whether it is partial: its parameter types permit keys and guarantee none.
    pub partial: bool,
}

/// A scalar carrier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Carrier {
    /// `bool`.
    Bool,
    /// `int`.
    Int,
    /// `rat`.
    Rat,
    /// `f32`.
    F32,
    /// `f64`.
    F64,
    /// `String`.
    Str,
}

impl Carrier {
    /// The six, in the order a class of values holding a literal tries them: `f64` before
    /// `f32`, so a decimal no use fixes takes `f64` (DESIGN.md L1.26a). `f32` is last so that
    /// the bits of the other five in a mask ([`Carrier::bit`]) are those they had before it.
    pub const ALL: [Carrier; 6] = [
        Carrier::Int,
        Carrier::F64,
        Carrier::Rat,
        Carrier::Str,
        Carrier::Bool,
        Carrier::F32,
    ];

    /// The numeric carriers, in the order of [`Carrier::ALL`].
    pub const NUMBERS: [Carrier; 4] = [Carrier::Int, Carrier::F64, Carrier::Rat, Carrier::F32];

    /// The bits of [`Carrier::NUMBERS`] in a mask.
    pub const NUMBER_BITS: u8 = 0b10_0111;

    /// Every value of the carrier.
    pub fn ty(self) -> KType {
        match self {
            Carrier::Bool => KType::bool(),
            Carrier::Int => KType::int(),
            Carrier::Rat => KType::rat(),
            Carrier::F32 => KType::f32(),
            Carrier::F64 => KType::f64(),
            Carrier::Str => KType::string(),
        }
    }

    /// Its place among the bases of [`zed_kernel::types::Split`].
    pub fn base(self) -> usize {
        match self {
            Carrier::Bool => 0,
            Carrier::Int => 1,
            Carrier::Rat => 2,
            Carrier::F64 => 3,
            Carrier::Str => 4,
            Carrier::F32 => 5,
        }
    }

    /// Its name.
    pub fn name(self) -> &'static str {
        match self {
            Carrier::Bool => "bool",
            Carrier::Int => "int",
            Carrier::Rat => "rat",
            Carrier::F32 => "f32",
            Carrier::F64 => "f64",
            Carrier::Str => "String",
        }
    }

    /// Whether it is a number.
    pub fn numeric(self) -> bool {
        matches!(
            self,
            Carrier::Int | Carrier::Rat | Carrier::F32 | Carrier::F64
        )
    }

    /// Its bit in a mask: its place in [`Carrier::ALL`].
    pub fn bit(self) -> u8 {
        1 << Carrier::ALL
            .iter()
            .position(|&c| c == self)
            .expect("a carrier")
    }

    /// The carriers of the mask `m`, in the order of [`Carrier::ALL`].
    pub fn of_mask(m: u8) -> impl Iterator<Item = Carrier> {
        Carrier::ALL.into_iter().filter(move |c| m & c.bit() != 0)
    }
}

/// The bit of a mask that stands for every value that is not of a carrier: a tuple, a
/// function, an atom.
pub const OTHER: u8 = 1 << 6;

/// The mask of every value.
pub const EVERY: u8 = (1 << 7) - 1;

/// The clause a message about a check that was refused ends with ([`UNDECIDED`]), and after
/// it the note that says why ([`undecided_because`]): the headline stays short, the reason in
/// a line of its own (DESIGN.md sec:diagnostics, "A short headline").
pub fn undecided(why: &str) -> String {
    format!("{UNDECIDED}{}", undecided_because(why))
}

/// The end of the headline of a message about a check that was refused: the check is not
/// proved to fail, the checker could not decide it.
pub const UNDECIDED: &str = "; the checker could not decide this, so it is not proved wrong";

/// The note after the headline of a message about a refused check: `why` the checker could
/// not decide it, and the repair the reason names.
pub fn undecided_because(why: &str) -> String {
    format!("\n  because {why}")
}

/// The mask `m` as a type, in type syntax: `_` when it holds [`OTHER`], since `int | _` is `_`
/// (DESIGN.md L1.26); otherwise its carriers joined by `|`, and `Never`, the empty type, when it
/// holds none.
pub fn mask_text(m: u8) -> String {
    if m & OTHER != 0 {
        return "_".into();
    }
    if m == 0 {
        return "Never".into();
    }
    carriers_text(Carrier::of_mask(m))
}

/// The carriers `cs` written as a type, in the order of a union (`order::cmp`, DESIGN.md
/// sec:diagnostics), each once: `int`, `f64 | rat`, `int | bool | String`.
pub fn carriers_text(cs: impl IntoIterator<Item = Carrier>) -> String {
    order::union_of_names(cs.into_iter().map(Carrier::name))
}

/// Every atom.
pub fn atoms() -> KType {
    thread_local! {
        /// Made once, so that every use is one node and compares equal to another by pointer.
        static ATOMS: KType = {
            let carriers = Carrier::ALL.iter().fold(KType::empty(), |a, c| a | c.ty());
            KType::universe(Universe::Scalar) - &carriers
        };
    }
    ATOMS.with(KType::clone)
}

/// Every tuple and every struct, the kinds that `set` holds only as the kind-wide part.
pub fn wide() -> KType {
    thread_local! {
        /// Made once: each row made asks it ([`Ty::held_wide`]), where building the union cost
        /// more than the rest of the row (PERF-deep-ops-slow).
        static WIDE: KType = &KType::universe(Universe::Tuple) | &KType::universe(Universe::Struct);
    }
    WIDE.with(KType::clone)
}

/// The atom `#errs` that two distinct failures merge into, with any payload.
pub fn errs() -> KType {
    KType::atom_with("errs", &KType::top())
}

/// The type of the failures that merge into `#errs`, each from the type `e` of the failures
/// that meet: `#errs(E ->? E)`, the family that maps each distinct failure to itself
/// (DESIGN.md sec:failure), whose exact keys are not kept. Its payload is a family, so its
/// signature is data and prints with `->?`; a lookup in it is a failure of `E` or `#notFound`,
/// as for any `K ->? V` (sec:type_language), which is how the printed type reads back.
pub fn errs_of(e: Ty) -> Ty {
    let param = SParam {
        name: "".into(),
        positional: true,
        default: None,
        range: None,
    };
    let found = e.union(&Ty::set(KType::atom("notFound")));
    let mut family = Sig::one(vec![param], vec![e], found);
    family.arrows[0].partial = true;
    family.data = true;
    let mut t = Ty::set(errs());
    let shape = Shape::new(vec![Ty::func(Arc::new(family))], BTreeMap::new());
    t.payloads.insert("errs".into(), Some(vec![shape]));
    t
}

/// Whether `set` may hold an `#errs` with a payload.
pub fn holds_errs(set: &KType) -> bool {
    holds_payload(set, "errs")
}

/// The failures the `#errs` of `t` may hold, when each of its payloads is a family that
/// [`errs_of`] built: the union of their keys. `None` when `t` holds no `#errs` or an `#errs`
/// whose payload is not known; then what it holds is not known either.
pub fn errs_members(t: &Ty) -> Option<Ty> {
    if !holds_payload(&t.set, "errs") {
        return None;
    }
    let shapes = t.payloads.get("errs")?.as_ref()?;
    let mut keys = Ty::empty();
    for s in shapes {
        let [f] = &s.items[..] else { return None };
        let sig = f.fns.only()?;
        let only_fn = f.set.is_empty() && f.tuples.is_empty() && f.vars.is_empty() && !f.dynamic;
        let [arrow] = &sig.arrows[..] else {
            return None;
        };
        let [key] = &arrow.params[..] else {
            return None;
        };
        if !s.fields.is_empty() || !only_fn || !sig.data {
            return None;
        }
        keys = keys.union(key);
    }
    Some(keys)
}

/// Whether the failures of one application's operands can merge into `#errs`, given the
/// atoms of each operand that may carry one (DESIGN.md sec:failure): whether two of them can
/// carry different failures at once. Equal failures merge into one, and a singleton is the
/// atom itself, so they cannot exactly when fewer than two operands carry atoms, or each one
/// carries only the same payload-free atom, the one value they can all be. An atom with a
/// payload has a value per payload, so two of them can differ. One pass over the operands,
/// each compared with the first: types of different digests differ in `O(1)`, and equal ones
/// are read once (`Type::cmp`), so `O(n)` comparisons for `n` operands, each linear at most in
/// the atom types the checker already built.
pub fn merges<'k>(holding: impl IntoIterator<Item = &'k KType>) -> bool {
    let mut holding = holding.into_iter();
    let Some(first) = holding.next() else {
        return false;
    };
    let mut more = false;
    for t in holding {
        if t != first {
            return true;
        }
        more = true;
    }
    more && !one_bare_atom(first)
}

/// Whether `t` is one payload-free atom: a type of one value.
fn one_bare_atom(t: &KType) -> bool {
    let Some(mut names) = t.atom_names() else {
        return false;
    };
    match (names.next(), names.next()) {
        (Some((name, true)), None) => *t == KType::atom(name),
        _ => false,
    }
}

/// A piece of a type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Piece {
    /// Scalars: the values of one carrier, the atoms, or what is neither.
    Set(KType),
    /// A tuple shape.
    Tuple(Row),
    /// A function.
    Fn(Arc<Sig>),
    /// A type variable.
    Var(Arc<str>),
    /// The unknown.
    Dyn,
}

impl Piece {
    /// The carrier of a scalar piece.
    pub fn carrier(&self) -> Option<Carrier> {
        match self {
            Piece::Set(s) => Carrier::ALL.into_iter().find(|c| s.subtype(&c.ty())),
            _ => None,
        }
    }

    /// Whether it is a piece of atoms.
    pub fn is_atoms(&self) -> bool {
        // Complexity tradeoff (PERF-deep-ops-slow): naive, the subtype check alone, which reads
        // each of the piece's a atom names, O(a); `Ck::class_beside_atoms` asks it once per
        // operator of a chain `#e0 + #e1 + …`, whose loose atoms grow by one at each, O(n²) in
        // all (2.9·10^9 instructions at 8000 atoms). The parts answer in O(1) when they list
        // atoms alone; the check runs only for a recursive type or parts listing another kind.
        // Measured by `l01_27_absences::scaling::a_chain_of_many_failure_atoms_scales`: 11.5
        // times the instructions from 1000 to 8000 atoms before, 8.4 times now.
        matches!(self, Piece::Set(s) if s.atoms_only() || s.subtype(&atoms()))
    }

    /// The type of this piece alone.
    pub fn ty(&self) -> Ty {
        match self {
            Piece::Set(s) => Ty::set(s.clone()),
            Piece::Tuple(cs) => Ty::of_row(cs.clone()),
            Piece::Fn(s) => Ty::func(s.clone()),
            Piece::Var(v) => Ty::var(v.clone()),
            Piece::Dyn => Ty::dynamic(),
        }
    }
}

/// The binding of type variables made while applying an arrow, read as the map it is, with
/// the index of its variables a replacement reads (`BindKeys`): made at the first replacement
/// and kept as the binding changes, so each replacement starts in `O(1)` and not in the size
/// of the binding, which a call of `n` needs each replaced with the call's binding of `n`
/// variables would pay `n` times.
#[derive(Clone, Default)]
pub struct Binds {
    map: BindMap,
    // Complexity tradeoff (row FAIL-bench-bounded-or-free-time): the index held inline, over
    // 512 bytes, was copied whole with every copy of the binding (one per shape a search tries,
    // two per memo entry), O(64) a copy, and made every table of bindings that much larger.
    // Behind an `Arc` a copy is O(1), and an insert or removal copies it only while it is
    // shared (`Arc::make_mut`), the same O(64) the inline copy cost, now paid only on a write.
    // The many-bounded-variables bench allocates 29% fewer bytes and runs 3% fewer instructions.
    keys: std::sync::OnceLock<Arc<BindKeys>>,
    /// The bound of each bounded variable of the signature whose arrow binds these variables,
    /// by name, when there is one: a variable is bound to a piece only where its bound holds
    /// the piece ([`accepts`]). Shared, so a copy of the binding tried for one shape and
    /// dropped copies no bound.
    bounds: Option<SortedBounds>,
    /// For the variables of an arrow of `s` compared with an arrow of `q` ([`Binds::of_arrow`]),
    /// a type each binding of some of them must stay within for the result to fit, by name, in
    /// the order of the names, when there is one: a variable is bound to a piece only where its
    /// type there may hold it ([`accepts`]). Shared, as `bounds` is.
    ceilings: Option<Ceilings>,
    /// The sum, wrapping, of the hash of each binding ([`bind_digest`]), kept as the map
    /// changes, so equal maps have equal digests, by which [`Compared`] files the binding in
    /// `O(1)`, not in its size.
    digest: u64,
}

/// The hash of the binding of `v` to `t`, a term of [`Binds`]'s digest. A sum of the terms,
/// not a hash of the whole map, so a change to one binding changes the digest by its own
/// terms only: `O(t)` for the type bound, which the change already cost.
fn bind_digest(v: &str, t: &Ty) -> u64 {
    use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
    BuildHasherDefault::<DefaultHasher>::default().hash_one((v, t))
}

/// The map of a [`Binds`]: each variable bound, by name, with its type.
///
/// Complexity tradeoff: persistent (`imbl::OrdMap`, a B-tree whose nodes copies share, as
/// [`Env`]), not a `BTreeMap`. [`Comparing::search`] gives each shape it tries a copy of the
/// binding and keeps the copy of the shape that holds the piece; a `BTreeMap` copy costs the
/// size of the binding, which holds a variable for each parameter compared so far, so n
/// parameters, each a union of two shapes, cost O(n^2) (FAIL-types-binds-copied-per-shape).
/// The copy is now O(1) and an insert into a copy O(log n), copying the nodes on its path
/// only, so they cost O(n log n). Given up: a constant factor on each lookup and insert
/// (nodes of 64 entries, reference counted), which a binding of a few variables, the usual
/// case, pays too. Not taken: undoing the bindings a failed shape made, which needs every
/// writer of the binding (`accepts`, the rows and payloads, the functions held) to log what it
/// changed, where one copy covers them all.
type BindMap = imbl::OrdMap<Arc<str>, Ty>;

/// The bounds of a signature's bounded variables, each name with its mask, in the order of the
/// names ([`Binds::bound`]).
type SortedBounds = Arc<[(Arc<str>, u8)]>;

/// The types the bindings of some variables must stay within, each name with its type, in the
/// order of the names ([`Binds::ceiling`]).
type Ceilings = Arc<[(Arc<str>, Ty)]>;

impl Binds {
    /// No binding.
    pub fn new() -> Binds {
        Binds::default()
    }

    /// No binding, of the variables of a signature whose bounded variables have the bounds
    /// `bounds`, by name.
    fn bounded(bounds: &BTreeMap<Arc<str>, u8>) -> Binds {
        Binds {
            bounds: (!bounds.is_empty())
                .then(|| bounds.iter().map(|(v, &m)| (v.clone(), m)).collect()),
            ..Binds::default()
        }
    }

    /// No binding, of the variables of the arrow `sa` of `s`, as read in `cx`, whose unbounded
    /// own variables of `s` are [`Cx::free`]: the bounds of `s`, the ceilings of its variables
    /// where its result is to be within `within`, the result of an arrow of `q` ([`ceilings`]),
    /// and each unbounded own variable of `s` in `sa`'s result bound to `Never`. A cover of
    /// several arrows ([`part_of`]) is not given `within`: each arrow there may return outside
    /// it.
    ///
    /// A variable bound to `Never` is bound to no piece yet, so the parameters bind it as an
    /// unbound one ([`accepts`]), and the result reads it as `Never` where they bind nothing:
    /// a call binds such a variable to `Never` (sec:type_resolution, "the call's type is its
    /// arrow's result with the parameter's variables bound to `Never`"), so `(x0: int | T) ->
    /// T` fits `(x0: int) -> int` (FAIL-types-first-shape-unbounded). Left unbound, `T` stayed
    /// a variable in the result, which no result of `q` holds. A bounded variable is not so
    /// bound: a call fixes it to a carrier of its bound, which `Never` is not. Cost: a walk of
    /// `sa`'s result, with a binary search of `free` for each variable in it.
    fn of_arrow(s: &Sig, sa: &Arrow, within: Option<&Ty>, cx: &Cx) -> Binds {
        let mut b = Binds::bounded(&s.bounds);
        if cx.free.is_empty() {
            return b;
        }
        let free = |v: &str| cx.free.binary_search_by(|w| (**w).cmp(v)).is_ok();
        b.ceilings = within.and_then(|qr| ceilings(&sa.result, qr, &free));
        let mut vs = Vars::default();
        sa.result.vars_in(&mut vs);
        for v in vs.order.into_iter().filter(|v| free(v)) {
            b.insert(v, Ty::empty());
        }
        b
    }

    /// The ceiling of the variable `v`, if it has one ([`ceilings`]): by binary search, as
    /// the ceilings are in the order of their names.
    fn ceiling(&self, v: &str) -> Option<&Ty> {
        let ceilings = self.ceilings.as_deref()?;
        let at = ceilings.binary_search_by(|(w, _)| (**w).cmp(v)).ok()?;
        Some(&ceilings[at].1)
    }

    /// The bound of the variable `v`, if it has one: by binary search, as the bounds are in
    /// the order of their names.
    fn bound(&self, v: &str) -> Option<u8> {
        let bounds = self.bounds.as_deref()?;
        let at = bounds.binary_search_by(|(w, _)| (**w).cmp(v)).ok()?;
        Some(bounds[at].1)
    }

    /// The index of its variables, made now if not yet.
    fn index(&self) -> &BindKeys {
        self.keys.get_or_init(|| Arc::new(BindKeys::of(&self.map)))
    }

    /// Binds `v` to `t`, giving what it was bound to.
    pub fn insert(&mut self, v: Arc<str>, t: Ty) -> Option<Ty> {
        if let Some(keys) = self.keys.get_mut()
            && !self.map.contains_key(&v)
        {
            Arc::make_mut(keys).add(&v);
        }
        self.digest = self.digest.wrapping_add(bind_digest(&v, &t));
        let old = self.map.insert(v.clone(), t);
        if let Some(o) = &old {
            self.digest = self.digest.wrapping_sub(bind_digest(&v, o));
        }
        old
    }

    /// Unbinds `v`, giving what it was bound to.
    pub fn remove(&mut self, v: &str) -> Option<Ty> {
        let out = self.map.remove(v);
        if let Some(o) = &out {
            self.digest = self.digest.wrapping_sub(bind_digest(v, o));
            if let Some(keys) = self.keys.get_mut() {
                Arc::make_mut(keys).remove(v);
            }
        }
        out
    }

    /// What `v` is bound to, bound to `f()` first if it is not bound. Read only: a change made
    /// in place would not reach the digest.
    pub fn or_insert_with(&mut self, v: Arc<str>, f: impl FnOnce() -> Ty) -> &Ty {
        if !self.map.contains_key(&v) {
            self.insert(v.clone(), f());
        }
        self.map.get(&v).expect("bound just now")
    }

    /// Binds `v` to what it is bound to, if anything, and `t`.
    pub fn unite(&mut self, v: Arc<str>, t: &Ty) {
        let u = match self.map.get(&v) {
            Some(b) => b.union(t),
            None => Ty::empty().union(t),
        };
        self.insert(v, u);
    }

    /// Changes each type bound by `f`, in the order of the names. The map is persistent and
    /// lends no mutable iterator, so it is rebuilt from its sorted entries: O(n) for n
    /// bindings, as the walk of a `BTreeMap` was, the names unchanged, and so is the digest.
    pub fn update_each(&mut self, mut f: impl FnMut(&mut Ty)) {
        let mut digest = 0u64;
        self.map = std::mem::take(&mut self.map)
            .into_iter()
            .map(|(v, mut t)| {
                f(&mut t);
                digest = digest.wrapping_add(bind_digest(&v, &t));
                (v, t)
            })
            .collect();
        self.digest = digest;
    }

    /// Keeps the bindings `f` keeps: the names to drop are found in one walk and removed
    /// after, O(n + d log n) for d dropped (the map lends no mutable walk).
    pub fn retain(&mut self, mut f: impl FnMut(&Arc<str>, &Ty) -> bool) {
        let drop: Vec<Arc<str>> = (self.map.iter())
            .filter(|(v, t)| !f(v, t))
            .map(|(v, _)| v.clone())
            .collect();
        for v in &drop {
            self.remove(v);
        }
    }

    /// The binding of `map`, its digest found.
    fn of_map(map: BindMap) -> Binds {
        let digest = (map.iter()).fold(0u64, |d, (v, t)| d.wrapping_add(bind_digest(v, t)));
        Binds {
            map,
            digest,
            ..Binds::default()
        }
    }
}

impl std::ops::Deref for Binds {
    type Target = BindMap;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl fmt::Debug for Binds {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.map.fmt(f)
    }
}

impl PartialEq for Binds {
    fn eq(&self, other: &Binds) -> bool {
        self.map == other.map
    }
}

impl Extend<(Arc<str>, Ty)> for Binds {
    fn extend<I: IntoIterator<Item = (Arc<str>, Ty)>>(&mut self, iter: I) {
        iter.into_iter().for_each(|(v, t)| {
            self.insert(v, t);
        });
    }
}

impl FromIterator<(Arc<str>, Ty)> for Binds {
    fn from_iter<I: IntoIterator<Item = (Arc<str>, Ty)>>(iter: I) -> Binds {
        Binds::of_map(iter.into_iter().collect())
    }
}

impl<const N: usize> From<[(Arc<str>, Ty); N]> for Binds {
    fn from(pairs: [(Arc<str>, Ty); N]) -> Binds {
        pairs.into_iter().collect()
    }
}

impl From<BTreeMap<Arc<str>, Ty>> for Binds {
    fn from(map: BTreeMap<Arc<str>, Ty>) -> Binds {
        Binds::of_map(map.into_iter().collect())
    }
}

/// How a comparison reads a variable of the types on one side ([`Env`]).
#[derive(Clone, Debug, PartialEq)]
enum Read {
    /// As the variable of this name: a rigid one, in [`Cx::rigid`], or an own variable given a
    /// new name as a comparison around it reads its name ([`Cx::own_name`]).
    Rigid(Arc<str>),
    /// As every value of the carriers of the mask, [`Ty::of_mask`].
    Mask(u8),
    /// As this type, already read: what the parameters of an arrow bound the variable to,
    /// read inside a function its result holds ([`Cx::bound_in_fns`]).
    Bound(Ty),
}

/// The variables of the function types around one side of a comparison that it reads as
/// something else: the own bounded variables of each expected function type around it, and
/// those of each given one that no parameter holds. Persistent, so that each function met
/// keeps the reading of its own side at the cost of a pointer.
type Env = imbl::OrdMap<Arc<str>, Read>;

/// A mask for each variable named, as `Sig::bounds` and `Cx::rigid` keep them.
type Masks = BTreeMap<Arc<str>, u8>;

/// Variable names in sorted order, found by binary search, as `Cx::free` keeps them.
type SortedNames = Arc<[Arc<str>]>;

/// The type a class variable the checker solved stands for, if it was solved to one that
/// holds no variable: a signature solved before the functions around it keeps such a
/// variable in the functions it holds, and is read through this (CHK-carrier).
pub type Solve<'s> = &'s dyn Fn(&str) -> Option<Ty>;

/// How the modes of [`Ty::replace_in`] replace.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// At every depth: [`Ty::replace`].
    Replace,
    /// At every depth, the own variables of functions too: [`Ty::renamed`].
    Rename,
    /// Outside functions: [`Ty::replace_outside`].
    Outside,
}

/// The state of one comparison of function types ([`fits_sig`], [`Ty::sub`]).
#[derive(Default)]
struct Cx<'s> {
    /// The bounded variables of the expected function types the comparison is inside, each
    /// with the mask of its bound: the caller of such a function picks one carrier of the
    /// bound for each, so a variable here stands for every carrier of its mask and is never
    /// bound.
    rigid: BTreeMap<Arc<str>, u8>,
    /// The functions of the types being compared, each put in its type as a variable of its
    /// own and kept here with the reading of its side: a function moved into the other side,
    /// as a binding of a variable there, is read as it was where it came from.
    fns: BTreeMap<Arc<str>, (Arc<Sig>, Env)>,
    /// The variables of `fns` whose function reads alike in every environment: its reading
    /// names none of the variables it holds at any depth (its [`held_reading`] is empty).
    /// [`Comparing::closed_form`] puts these back as written and the others as tokens.
    closed: HashSet<Arc<str>>,
    /// The rows [`Cx::read`] read that hold no variable at any depth, inside functions and
    /// payloads too ([`Row::holds_vars`]), by number, each with the row it read as: kept for
    /// the whole comparison, not set aside by [`Cx::open`], so a row shared by the comparisons
    /// of function types nested in each other is read once. The names made for its functions
    /// are made outside every scope, so [`Cx::forget`] keeps them (PERF-types-shared-row-each-
    /// level).
    kept_rows: HashMap<NodeId, Row>,
    /// The numbers of the rows `kept_rows` holds as read: rows whose only variables are names
    /// of `fns` made outside every scope.
    kept_read: HashSet<NodeId>,
    /// The verdict of each comparison of one row of `kept_read` within another, with why it
    /// was refused if it was, by their two numbers ([`Comparing::kept_rows_in`]): kept for the
    /// whole comparison, as `fitted` is.
    kept_compared: HashMap<(NodeId, NodeId), Fitted>,
    /// The names of `rigid` and `fns` made by the comparisons open now, last made last.
    made: Vec<Arc<str>>,
    /// The number of names made: a quote is in no name a program writes, and the count keeps
    /// the names apart.
    count: usize,
    /// The types of the solved class variables, read where a function's arrows are read.
    solve: Option<Solve<'s>>,
    /// The verdict of each comparison of a function of `fns` with another, with why it was
    /// refused if it was ([`Fitted`]), by their two names ([`Comparing::fits_read`]). A failed
    /// fit of an arrow is followed by the search for a cover, which compares the same two
    /// results again; without this, a refusal of curried function types compared each level
    /// twice for each level around it, 2^depth in all.
    // Complexity tradeoff (COMPLEXITY.md row TY-refuse-exp): naive version, each comparison
    // run again, O(2^depth). Used: the verdict kept by the pair of names, one comparison per
    // pair, linear in the depth. Tradeoff: one entry per pair compared, held until the
    // outermost comparison ends.
    fitted: HashMap<(Arc<str>, Arc<str>), Fitted>,
    /// For each function of `fns` in the result of an arrow and each binding of the own
    /// variables of the arrow's signature it holds, the name of the same function read with
    /// those variables bound ([`Cx::bound_in_fns`]). A name is never made twice
    /// ([`Cx::fresh`]), so an entry whose name [`Cx::forget`] dropped is only made again.
    // Complexity tradeoff (COMPLEXITY.md row FAIL-types-result-fn-outer-binding): naive
    // version, a new name at each comparison of a result, so `fitted` never meets the pair
    // again and a refusal of curried function types, whose cover search compares each result
    // twice, costs O(2^depth) again. Used: the name kept by the function and the binding, so
    // the second comparison of a result reads the first's verdict from `fitted`, linear in
    // the depth. Tradeoff: one entry per function and binding met, held until the outermost
    // comparison ends, as `fitted` is.
    bound_fns: HashMap<BoundFn, Arc<str>>,
    /// The verdict of each comparison of two functions as written, with no reading
    /// ([`Comparing::fits_written`]), by the two signatures' addresses, each kept with its
    /// signature so that no other takes the address while the entry is held; made in the
    /// innermost comparison of function types open now, or outside every one, and set aside
    /// and given back with [`Cx::compared`].
    // Complexity tradeoff (BENCH-closed-form-late-variable): the functions put back by
    // [`Comparing::closed_form`] are compared by [`Comparing::form_verdict`] as written, not
    // through `fitted`, and a failed fit of an arrow is followed by the search for a cover,
    // which compares the same two results again: a nest of `n` function types, each result
    // holding the next beside a closed function, was compared in O(2^n) when it did not fit
    // (n = 12 took 13 s; with `closed_form` off, 8 ms). Used: the verdict kept by the pair of
    // signatures, one comparison per pair and scope, linear in the depth, as `fitted` does
    // for functions read as variables. Tradeoff: one entry per pair compared, held until the
    // comparison of function types around ends. Test:
    // `nested_function_results_are_compared_in_linear_time`, 8.0 times at 8n both ways; with
    // this memo off, the false judgment at n 64 did not end in 60 s.
    fitted_written: FittedWritten,
    /// The verdict of each comparison of a function with another where both hold only their
    /// own variables ([`Comparing::fits_alone`]), with why it was refused if it was, by the
    /// addresses of the two signatures, kept with them so that neither address is reused while
    /// the entry lives. Unlike `fitted`, its key does not depend on the names the functions are
    /// read under, which each comparison around them makes anew.
    // Complexity tradeoff (COMPLEXITY.md row FAIL-kinds-bench-nested-deep-time): naive version,
    // the verdict kept only by `fitted`'s names: a parameter of function type is compared in
    // both directions ([`cover`] and [`permitted`]), each opening the two functions under new
    // names, so the two functions one level down are compared twice, those k levels down 2^k
    // times, 2^(n+1) - 1 comparisons in all for a nest n deep (measured 7, 15, 31, 63, 127 at
    // n = 2 to 6). Used: one comparison per pair of signatures, 2n + 1 for the nest. Tradeoff:
    // one entry per pair, and the two signatures kept alive, until the outermost comparison
    // ends.
    fitted_alone: HashMap<(*const Sig, *const Sig), FittedAlone>,
    /// When asked for, by [`why_unfit`], why the outermost comparison failed, if one of the
    /// covers rule 6 of sec:type_resolution gives is refused there: `Some(None)` until it is
    /// found. Only the outermost [`fits_in`] reads it, so a comparison inside, tried and
    /// dropped, gives no reason.
    why: Option<Option<String>>,
    /// Why the comparison was refused, if two members of one side each needed a shape that
    /// [`Choices`] could not single out ([`Comparing::search`]): the first such refusal. A
    /// refused comparison answers false, whatever else it found ([`Cx::decided`]).
    unchosen: Option<String>,
    /// The tuple and payload shapes of each component of a row or payload shape compared, filed
    /// once for the comparison ([`Filed`]), by the number of the row or shape ([`NodeId`]) and
    /// the component's place. The rows and shapes may be made during the comparison and dropped
    /// before it ends, so they are keyed by number, which no later node takes, not by address.
    filed: HashMap<(NodeId, usize), Arc<Filed>>,
    /// The own variables of the function types the open comparisons are inside that each
    /// reads as itself or, when a comparison around it already reads that name so, as a new
    /// name ([`Cx::open`]), innermost last, each with its bound, `None` when it has none: a
    /// message about the comparison prints them as the program wrote them
    /// ([`Scope::of_comparison`]).
    own: Vec<(Arc<str>, Option<u8>)>,
    /// The names of the entries of `own`. Each entry has a name no other one has: an own
    /// variable is read under a new name when its name is owned around it, or held by the other
    /// side ([`Cx::open`]).
    // Complexity tradeoff (COMPLEXITY.md F174): naive version, `own` searched for each own
    // variable opened, O(depth) each and O(depth^2) for a nest of function types that deep.
    // Used: a set of the names, O(1) expected per variable. Tradeoff: one set entry per
    // entry of `own`, dropped with it.
    owned: HashSet<Arc<str>>,
    /// The bound of each entry of `own` that has one, by name: a variable a comparison binds
    /// within that bound, whose values are of its carriers, wherever it is held as a piece
    /// ([`var_mask`]). O(1) expected per variable opened or looked up, as for `owned`.
    own_bounds: HashMap<Arc<str>, u8>,
    /// The unbounded own variables of `s` in the innermost comparison of function types open
    /// now ([`fits_in`]), by the names they are read as, in order: the variables an arrow of
    /// `s` may bind as it likes, read as `Never` where its parameters do not bind them
    /// ([`Binds::of_arrow`]).
    free: SortedNames,
    /// The own variables of `q` held by a parameter in the innermost comparison of function
    /// types open now ([`fits_in`]), by the names they are read as, each bound to every value
    /// it may stand for: a bounded one to its carriers, an unbounded one to the unknown, which
    /// as a type holds every value and is held only by the unknown ([`accepts`]). A variable
    /// whose bound has two classes or more and that stands twice in the parameters of one
    /// arrow is left out ([`repeated`]). The permission of `q` is read through it
    /// ([`permitted`], [`instance_within`]).
    wide: Binds,
    /// The parameter types of each arrow of `s`, in the innermost comparison of function types
    /// open now ([`fits_in`]), that holds a variable bounded by several carriers and of which
    /// some cover found an instance within an arrow of `q` ([`instance_within`]): the witness
    /// [`permitted`] asks of such an arrow where it cannot try each carrier.
    witnessed: HashSet<Vec<Ty>>,
    /// The arrows of `q` as read, in the innermost comparison of function types open now
    /// ([`fits_in`]): the permission an instance of an arrow of `s` is compared with where it
    /// is not within the arrow of `q` it covers alone ([`instance_within`]).
    q_arrows: Arc<[Arrow]>,
    /// For each instance compared with all of `q_arrows` ([`within_q`]), by its parameter types,
    /// whether it is within them, in the innermost comparison of function types open now.
    within_q: HashMap<Vec<Ty>, bool>,
    /// Whether the comparisons made now, in the innermost comparison of function types open,
    /// bind no variable ([`within_as_is`]): [`accepts`] then binds none, so a search goes on to
    /// a shape that holds a piece as it is, and the memo of rows ([`Cx::compared`]) keeps
    /// these answers apart ([`Compared::as_is`]). Cleared by [`fits_in`] for the comparisons
    /// of function types inside, which bind their own variables.
    bind_none: bool,
    /// The answer of each comparison of a row or payload shape with another, with the binding
    /// it gave, made in the innermost comparison of function types open now, or outside every
    /// one, by the two nodes and the binding it was given ([`Compared`]): a pair of nodes met
    /// again on another path with the same binding is not compared again
    /// ([`Comparing::rows`], [`Comparing::shape_in`]). Set aside by [`Cx::open`] and given back
    /// by [`Cx::forget`], as the names a comparison of function types reads may mean other
    /// variables there: an own variable read as itself in one comparison and in another beside
    /// it with another bound (`own_bounds`). Kept only where nothing was refused
    /// ([`Comparing::keep`]).
    //
    // Complexity tradeoff (COMPLEXITY.md row FAIL-types-sub-shared-payloads): naive version,
    // each pair compared once for each path to it: payloads or tuples `#a(t, t)` n deep, each
    // shared by both places that hold it, with a variable at the bottom, cost O(2^n) (n = 14
    // took 182 ms, n = 2,000 did not end). Used: the answer kept by the two nodes and the
    // binding in force, so each pair is compared once for each binding it is met with, there
    // one or two, and the comparison costs O(n); each comparison of a pair now costs a lookup,
    // hashed by the digest the binding keeps (`O(1)`), and the binding is compared in full
    // on a hash match only. Prior work: the memo by node of `Cx::read` (commit ced805157) and
    // the pairs of nodes met of [`Same`] and of the meet's walk, which need no binding in the
    // key, as their answers depend on the two nodes alone; `fitted`, which keeps a verdict
    // with its refusal. Tradeoff: one entry per pair and binding met, held until the
    // comparison of function types around ends, and the digest's upkeep on each change to a
    // binding, a hash of the type bound, which the change already cost. Not done: a binding
    // that differs on a variable neither node holds still misses; restricting the key to the
    // variables the two nodes hold would need their variables at hand as a set.
    // Assumption, not proved (ASSUME-documented): an answer kept here equals what the
    // comparison would give if run again on the same nodes, binds, bounds and ceilings. It
    // needs node ids that are never reused (a global counter, so true within one run), every
    // input the comparison reads to be part of the `Compared` key, and no refusal behind a
    // kept answer. `recall` checks only `unchosen`; whether that covers every refusal state is
    // open in row TYPES-compared-recall-refused. Evidence:
    // `a_shared_pair_met_again_under_other_bindings_keeps_them`,
    // `rows_compared_after_a_refusal_give_the_refusal`, and
    // `an_answer_found_after_a_refusal_is_not_read_by_a_later_attempt`; benchmarks 8.15x,
    // 8.01x and 8.02x. If false, a stale `true` accepts a type that does not fit: unsound.
    compared: HashMap<Compared, (bool, Binds)>,
}

/// A verdict kept in [`Cx::fitted`]: whether the function fits, and why the comparison was
/// refused, if it was ([`Comparing::begin_alone`]).
type Fitted = (bool, Option<String>);

/// The verdicts of [`Cx::fitted_written`]: by the addresses of the two signatures, each
/// verdict kept with the two, so that no other signature takes an address while it is held.
type FittedWritten = HashMap<(usize, usize), (Arc<Sig>, Arc<Sig>, Fitted)>;

/// An entry of [`Cx::fitted_alone`]: the two signatures compared, kept so that their addresses,
/// the key, are not reused, and the verdict.
type FittedAlone = (Arc<Sig>, Arc<Sig>, Fitted);

/// A key of [`Cx::bound_fns`]: the name of a function of [`Cx::fns`], and each own variable
/// of the signature around that it holds, with what the parameters bound it to.
type BoundFn = (Arc<str>, Vec<(Arc<str>, Ty)>);

impl Cx<'_> {
    /// `ok`, the answer of the comparison this state ran, unless the comparison was refused.
    fn decided(&self, ok: bool) -> bool {
        ok && self.unchosen.is_none()
    }

    /// A new name, from `v`.
    fn fresh(&mut self, v: &str) -> Arc<str> {
        self.count += 1;
        let w: Arc<str> = format!("{v}'{}", self.count).into();
        self.made.push(w.clone());
        w
    }

    /// A new name, made outside every scope: [`Self::forget`] does not drop it.
    fn fresh_kept(&mut self) -> Arc<str> {
        self.count += 1;
        format!("'{}", self.count).into()
    }

    /// `t` as the comparison reads it on a side read by `env`: each variable `env` maps
    /// replaced, and each function, outside other functions, replaced by a new variable that
    /// `fns` maps to it and `env`, in its tuples and in its atoms' payloads. The cost is that of
    /// `t` outside its functions, so each function type is read once for each comparison of
    /// it. A class variable `solve` gives a type is read as that type.
    ///
    /// The payloads are read as the tuples are (FAIL-types-payload-vars-unread): left as they
    /// were, `(x0: #p(C)) -> (C,) for C in int | f64` did not fit itself, as the `C` of
    /// `q`'s payload, read as its own rigid name elsewhere, kept its written name there, and
    /// [`Comparing::payloads_in`] bound the `C` of `s` to it, a variable of no known carrier,
    /// which [`bounds_hold`] refused. A shape with no variable and no function reads as itself
    /// and is not walked ([`ShapeData::fixed`]), and a shared shape is read once
    /// (`memo`, by its number), so a type of n shapes that share their payloads, nested in
    /// each other, costs O(n), not a walk of every path to each.
    ///
    /// The tuples and payloads are read on an explicit stack, each component before the type
    /// that holds it and in order, as the recursive form read them, so the new names are made
    /// in the same order, and a type nested to any depth needs no more of the thread's stack.
    fn read(&mut self, t: &Ty, env: &Env) -> Ty {
        /// A type being read: the rows read and the components read of the next row, then its
        /// payload shapes not fixed, in order, the shapes read, and the components of the next
        /// shape with those read.
        struct Reading<'t> {
            t: &'t Ty,
            /// Whether `t` is inside a row of [`Cx::kept_rows`]: it holds no variable, and the
            /// names of its functions are made outside every scope.
            kept: bool,
            rows: Vec<Row>,
            row: Vec<Ty>,
            shapes: Vec<&'t Shape>,
            read: Vec<Shape>,
            comps: Vec<&'t Ty>,
            shape: Vec<Ty>,
        }
        fn start(t: &Ty, kept: bool) -> Reading<'_> {
            Reading {
                t,
                kept,
                rows: Vec::new(),
                row: Vec::new(),
                shapes: t.payload_shapes().filter(|s| !s.fixed).collect(),
                read: Vec::new(),
                comps: Vec::new(),
                shape: Vec::new(),
            }
        }
        // By number and whether read inside a kept row: a shape read outside one holds names a
        // comparison of function types made, which [`Cx::forget`] drops, so a row kept beyond
        // that comparison may not take its reading.
        let mut memo: HashMap<(NodeId, bool), Shape> = HashMap::new();
        // Complexity tradeoff (PERF-types-shared-tuple-vars): a shared row is read once, by its
        // number, as a shared shape is. Naive, as before: each row read once per path to it,
        // so P(0) = (T,), P(k) = (P(k-1), P(k-1)), n + 1 rows in memory, was read as 2^(n+1) - 1
        // rows, O(2^n), and every memo keyed by node number after it, [`Cx::compared`] among
        // them, met each copy as a new row: the comparison walked every path too. Now O(rows in
        // memory) lookups and reads, and the rows read are shared as written. Proof that the
        // reading is the same: [`Self::read_outer`] reads a type from its own rows, shapes,
        // functions and variables and `env`, which is fixed for the walk; the only state it
        // changes is the new name made for each function met, so a row read once gives, at its
        // second path, the row the first gave with the same new names, where before it made new
        // ones. Each such name stands for the same function in the same `env` ([`Cx::fns`]),
        // and a function variable is never bound ([`holds_bindable`] passes over `fns`), so the
        // two names were read alike: compared by [`Comparing::fits_read`], which keys its
        // verdict by the pair of names and gives the same verdict for each copy, as the shapes
        // read once here already did. Cost: one map entry per row read.
        let mut rows: HashMap<NodeId, Row> = HashMap::new();
        // Complexity tradeoff (PERF-types-shared-row-each-level): a row that holds no variable
        // at any depth is read once for the whole comparison ([`Cx::kept_rows`]), not once for
        // each comparison of function types that reads it. Naive, as before: a row of n
        // functions shared by the results of n function types nested in each other was read at
        // each of the n levels, with new names, and so compared again at each (its numbers
        // were new), O(n^2). Now one read and one map entry per such row, and the names of its
        // functions, made outside every scope, live until the comparison ends. Proof that the
        // reading is the same: [`Self::read_outer`] reads a type from its own parts and `env`,
        // which it reads only to look up a variable, and the solved classes, fixed for the
        // comparison; such a row holds no variable, at any depth, so it reads alike by every
        // environment but for the new names of its functions, each kept in `fns` with the
        // empty environment, by which each of those functions reads as by any other
        // ([`held_reading`]: it holds no variable). A name kept for the whole
        // comparison stands for that function there, and no name is made twice.
        let mut stack = vec![start(t, false)];
        loop {
            let top = stack
                .last_mut()
                .expect("the type being read is on the stack");
            if let Some(cs) = top.t.tuples.get(top.rows.len()) {
                // No component read yet: the row is not started, and may be read already.
                if top.row.is_empty() {
                    let done = match cs.holds_vars() {
                        true => rows.get(&cs.node()),
                        false => self.kept_rows.get(&cs.node()),
                    };
                    if let Some(done) = done {
                        top.rows.push(done.clone());
                        continue;
                    }
                }
                match cs.get(top.row.len()) {
                    Some(c) => {
                        let kept = top.kept || !cs.holds_vars();
                        stack.push(start(c, kept));
                    }
                    None => {
                        let row: Row = std::mem::take(&mut top.row).into_iter().collect();
                        match cs.holds_vars() {
                            true => rows.insert(cs.node(), row.clone()),
                            false => {
                                self.kept_read.insert(row.node());
                                self.kept_rows.insert(cs.node(), row.clone())
                            }
                        };
                        top.rows.push(row);
                    }
                }
                continue;
            }
            if let Some(&sh) = top.shapes.get(top.read.len()) {
                // A shape not fixed has a component, so no components means not started.
                if top.comps.is_empty() {
                    if let Some(done) = memo.get(&(sh.node(), top.kept)) {
                        top.read.push(done.clone());
                        continue;
                    }
                    top.comps = sh.items.iter().chain(sh.fields.values()).collect();
                }
                match top.comps.get(top.shape.len()).copied() {
                    Some(c) => {
                        let kept = top.kept;
                        stack.push(start(c, kept));
                    }
                    None => {
                        let mut items = std::mem::take(&mut top.shape);
                        let fields = items.split_off(sh.items.len());
                        let read =
                            Shape::new(items, sh.fields.keys().cloned().zip(fields).collect());
                        memo.insert((sh.node(), top.kept), read.clone());
                        top.comps.clear();
                        top.read.push(read);
                    }
                }
                continue;
            }
            let Reading {
                t,
                kept,
                rows,
                read,
                ..
            } = stack.pop().expect("the type being read is on the stack");
            let out = self.read_outer(t, rows, read, env, kept);
            match stack.last_mut() {
                Some(up) if up.rows.len() < up.t.tuples.len() => up.row.push(out),
                Some(up) => up.shape.push(out),
                None => return out,
            }
        }
    }

    /// [`Self::read`] of `t` whose tuples read as `tuples` and whose payload shapes not fixed
    /// read as `shapes`, in order: its functions and variables. Where `kept`, `t` is inside a
    /// row of [`Cx::kept_rows`] and so holds no variable, and each function is named outside
    /// every scope and kept with the empty environment.
    fn read_outer(
        &mut self,
        t: &Ty,
        mut tuples: Vec<Row>,
        shapes: Vec<Shape>,
        env: &Env,
        kept: bool,
    ) -> Ty {
        // A variable read as the empty type leaves a row with no value.
        tuples.retain(|r| !r.0.void);
        let payloads = match shapes.is_empty() {
            true => t.payloads.clone(),
            false => {
                let mut read = shapes.into_iter();
                let mut next = |s: &Shape| match s.fixed {
                    true => s.clone(),
                    false => read.next().expect("each shape not fixed is read"),
                };
                (t.payloads.iter())
                    .map(|(n, ss)| {
                        (
                            n.clone(),
                            ss.as_ref().map(|ss| ss.iter().map(&mut next).collect()),
                        )
                    })
                    .collect()
            }
        };
        let mut out = Ty {
            set: t.set.clone(),
            tuples: tuples.into(),
            fns: Members::new(),
            vars: VarSet::new(),
            dynamic: t.dynamic,
            family: t.family.clone(),
            payloads,
        };
        for s in &t.fns {
            if kept {
                // It holds no variable, so it reads alike by every environment.
                let w = self.fresh_kept();
                self.closed.insert(w.clone());
                self.fns.insert(w.clone(), (s.clone(), Env::new()));
                out.vars.insert(w);
                continue;
            }
            let w = self.fresh("");
            let env = held_reading(s, env);
            if env.is_empty() {
                self.closed.insert(w.clone());
            }
            self.fns.insert(w.clone(), (s.clone(), env));
            out.vars.insert(w);
        }
        let mut solved = Vec::new();
        for v in &t.vars {
            match env.get(v) {
                None => match self.solve.and_then(|f| f(v)) {
                    Some(u) => solved.push(u),
                    None => {
                        out.vars.insert(v.clone());
                    }
                },
                Some(Read::Rigid(w)) => {
                    out.vars.insert(w.clone());
                }
                Some(&Read::Mask(m)) if m & OTHER != 0 => out.dynamic = true,
                Some(&Read::Mask(m)) => {
                    out.set = Carrier::of_mask(m).fold(out.set, |s, c| &s | &c.ty());
                }
                Some(Read::Bound(u)) => solved.push(u.clone()),
            }
        }
        solved.iter().fold(out, |o, u| o.union(u))
    }

    /// Forgets the names made and the own variables kept since `mark`, and the comparisons of
    /// rows and payload shapes made since, giving back those of the comparison around.
    fn forget(&mut self, mark: Mark) {
        self.compared = mark.compared;
        self.fitted_written = mark.fitted_written;
        for w in self.made.drain(mark.made..) {
            self.rigid.remove(&w);
            self.fns.remove(&w);
            self.closed.remove(&w);
        }
        for (w, bound) in self.own.drain(mark.own..) {
            if bound.is_some() {
                self.own_bounds.remove(&w);
            }
            self.owned.remove(&w);
        }
    }

    /// `t`, made by [`Self::read`], with each variable of `fns` in it put back as the function
    /// it stands for, read as its side reads it: each variable of that side's reading replaced
    /// as [`Self::read_outer`] replaces it outside functions, so that a message prints the
    /// function where the comparison holds it, in a tuple too, and not `_`. Only on the way to
    /// an error. The cost is that of `t` and of each function put back.
    fn unread<'t>(&self, t: &'t Ty) -> Cow<'t, Ty> {
        let mut vs = Vars::default();
        t.vars_in(&mut vs);
        let mut fns = Binds::new();
        for w in vs.order {
            let Some((s, env)) = self.fns.get(&w) else {
                continue;
            };
            let mut inner = Vars::default();
            for a in &s.arrows {
                a.params.iter().for_each(|p| p.vars_in(&mut inner));
                a.result.vars_in(&mut inner);
            }
            s.needs.iter().for_each(|n| n.vars_in(&mut inner));
            // The signature's own variables are its own here, and the replacement keeps them.
            let mut binds = Binds::new();
            for v in inner.order {
                let read = match env.get(&v) {
                    Some(Read::Rigid(r)) => Some(Ty::var(r.clone())),
                    Some(&Read::Mask(m)) => Some(Ty::of_mask(m)),
                    Some(Read::Bound(u)) => Some(self.unread(u).into_owned()),
                    None => self.solve.and_then(|f| f(&v)),
                };
                if let Some(u) = read {
                    binds.insert(v, u);
                }
            }
            fns.insert(w, Ty::func(Arc::new(s.replace(&binds))));
        }
        match fns.is_empty() {
            true => Cow::Borrowed(t),
            false => Cow::Owned(t.replace_outside(&fns)),
        }
    }

    /// The variables of `t` as a message prints it ([`Self::unread`]).
    fn vars_unread(&self, t: &Ty) -> Vars {
        let mut vs = Vars::default();
        self.unread(t).vars_in(&mut vs);
        vs
    }

    /// Whether each variable of `c` is one of `into`, the variables of both those a message
    /// prints ([`Self::vars_unread`]). Linear in the two and the functions put back.
    fn vars_within(&self, c: &Ty, into: &Ty) -> bool {
        let within = self.vars_unread(into);
        self.vars_unread(c).order.iter().all(|v| within.contains(v))
    }
}

/// Where [`Cx::open`] left [`Cx::made`] and [`Cx::own`], and the comparisons of rows and
/// payload shapes of the comparison around it ([`Cx::compared`]) and of functions as written
/// ([`Cx::fitted_written`]), for [`Cx::forget`].
struct Mark {
    made: usize,
    own: usize,
    compared: HashMap<Compared, (bool, Binds)>,
    fitted_written: FittedWritten,
}

/// A comparison of the row or payload shape numbered `left` with the one numbered `right`
/// ([`Comparing::rows`], [`Comparing::shape_in`]) under the binding `binds`, by which its
/// answer is kept in [`Cx::compared`]. Hashed by the two numbers and the binding's digest, in
/// `O(1)`; equal when the numbers are, and the bindings, with their bounds and ceilings, which
/// [`accepts`] reads too. The bindings are compared on a hash match only, where two copies of
/// one map are found equal at once (their roots are one node) and others in the size of the
/// map.
struct Compared {
    left: NodeId,
    right: NodeId,
    binds: Binds,
    /// [`Cx::bind_none`] when compared: with no variable bound, [`accepts`] may answer
    /// otherwise, so the two answers are kept apart.
    as_is: bool,
}

impl Compared {
    /// The comparison of `left` with `right` under `binds`, binding none where `as_is`; the
    /// copy of `binds` is `O(1)`.
    fn new(left: NodeId, right: NodeId, binds: &Binds, as_is: bool) -> Compared {
        Compared {
            left,
            right,
            as_is,
            binds: Binds {
                map: binds.map.clone(),
                keys: std::sync::OnceLock::new(),
                bounds: binds.bounds.clone(),
                ceilings: binds.ceilings.clone(),
                digest: binds.digest,
            },
        }
    }
}

impl std::hash::Hash for Compared {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        (self.left, self.right, self.binds.digest, self.as_is).hash(h);
    }
}

impl PartialEq for Compared {
    fn eq(&self, other: &Compared) -> bool {
        fn same<T: PartialEq + ?Sized>(a: &Option<Arc<T>>, b: &Option<Arc<T>>) -> bool {
            match (a, b) {
                (None, None) => true,
                (Some(a), Some(b)) => Arc::ptr_eq(a, b) || a == b,
                _ => false,
            }
        }
        let (a, b) = (&self.binds, &other.binds);
        self.left == other.left
            && self.right == other.right
            && self.as_is == other.as_is
            && a.digest == b.digest
            && a.map == b.map
            && same(&a.bounds, &b.bounds)
            && same(&a.ceilings, &b.ceilings)
    }
}

impl Eq for Compared {}

/// A comparison of function types running on an explicit stack on the heap
/// ([`zed_kernel::frames`]). The comparisons that call each other through the parts of the
/// types compared ([`Comparing::sub_in`], [`accepts`], [`fits_in`], [`every_arrow_fits`],
/// [`arrow_fits`], [`result_within`], and [`covered`], [`part_of`], [`met`], [`meet_within`]
/// and [`refused_cover`]) are `async`, awaited in the frame that calls them; a cycle among
/// them passes through [`accepts`], which starts a frame of its own ([`Comparing::fits`],
/// [`Comparing::rows`]) for a function or a tuple. So types nested to any depth are compared
/// with no more of the thread's stack than shallow ones. Calls are made in the order of the
/// recursive form, with its short-circuits, so the answers and the names made are the same.
///
/// Complexity tradeoff: each frame is a boxed future and each use of the state a check of the
/// `RefCell`, a constant factor over the recursive form, for an O(depth) heap in place of the
/// thread's stack; the order of the work is unchanged. Measured on a fit of curried types
/// 8,000 deep: 60.8 ms and 14.4 G instructions against 59.0 ms and 13.6 G recursive (both runs
/// with building and dropping the types; perf stat, TY-sub-stack, 2026-11-07).
struct Comparing<'m, 's> {
    stack: Stack<'m>,
    /// The comparison's state, borrowed by one statement at a time, never across an `await`,
    /// since the call awaited borrows it too.
    cx: &'m RefCell<Cx<'s>>,
}

/// Runs `$body`, which reads the comparison `$c`, on a stack of its own over the state `$cx`, a
/// `&mut Cx`, which it leaves as the comparison left it.
macro_rules! comparing {
    ($cx:expr, |$c:ident| $body:expr) => {{
        let cx: &mut Cx = $cx;
        let cell = RefCell::new(std::mem::take(cx));
        let v = {
            let $c = Comparing {
                stack: Stack::default(),
                cx: &cell,
            };
            $c.stack.run($body)
        };
        *cx = cell.into_inner();
        v
    }};
}

/// Where the type a comparison holds pieces against sits: a component of a row or payload shape
/// of the expected side, at its place (items, then fields), or elsewhere.
#[derive(Clone, Copy)]
enum Site<'a> {
    In(Holder<'a>, usize),
    Other,
}

/// A row or payload shape that holds the type a comparison holds pieces against.
#[derive(Clone, Copy)]
enum Holder<'a> {
    Row(&'a Row),
    Shape(&'a Shape),
}

impl Holder<'_> {
    /// Its number, a key of [`Cx::filed`] with the place.
    fn node(self) -> NodeId {
        match self {
            Holder::Row(r) => r.node(),
            Holder::Shape(s) => s.node(),
        }
    }
}

/// What a component of a shape of the expected side holds, for [`Choices`]: one value, the
/// values of one carrier, atoms of one name, or tuples of one length, and nothing else.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ShapeKey {
    /// One scalar literal, or one tuple of such values at any depth ([`Ty::point`]).
    Point(Value),
    /// The values of one carrier.
    Carrier(Carrier),
    /// Atoms named this, bare or with payloads.
    Atom(Arc<str>),
    /// Tuples of this length.
    Row(usize),
}

/// The shapes of one [`Group`] a member is tried against: those filed under a key, or every
/// shape of the group (`None`).
type Bucket = Option<Vec<ShapeKey>>;

/// Where a component of a member may be held, at a place a [`Group`] files.
enum Member {
    /// By no shape: what it holds is held by no component filed there.
    Nowhere,
    /// By any shape: it holds nothing that a component must hold, or the checker does not
    /// find what it holds.
    Anywhere,
    /// By the shapes filed under the key.
    At(ShapeKey),
}

/// The class of a scalar set: the carrier its values are all of, or the one name of its atoms;
/// none for an empty set, which has no part. It is read from the parts of `s` by universe
/// ([`KType::universes`]): a carrier's part is there only when it holds a value, and the atoms
/// and the rest only when they are not empty, so `s` is within a carrier exactly when that
/// carrier's part is its only one, and within the atoms when they are its only part, with no
/// comparison of types.
fn class_of(s: &KType) -> Option<ShapeKey> {
    let split = s.universes();
    let mut carriers = Carrier::ALL.into_iter().filter(|c| split.bases[c.base()]);
    match (carriers.next(), carriers.next(), split.atoms, split.rest) {
        (Some(c), None, false, false) => return Some(ShapeKey::Carrier(c)),
        (None, _, true, false) => {}
        _ => return None,
    }
    let mut names = s.atom_names()?;
    let (n, _) = names.next()?;
    names.next().is_none().then(|| ShapeKey::Atom(n.into()))
}

/// The class of `y`, a component of a shape of the expected side, and its value when it is one
/// value ([`Ty::point`]): a non-empty set of one class ([`class_of`]) that holds no tuple,
/// function, variable or unknown, or tuples of one length and nothing else, of the class of
/// that length. Such a component holds a component of a member only when the member's holds
/// values of its class alone ([`member`]), so the shapes can be filed by it.
fn class(y: &Ty) -> Option<(ShapeKey, Option<Value>)> {
    if y.dynamic || !y.vars.is_empty() || !y.fns.is_empty() {
        return None;
    }
    if let Some(r) = y.tuples.first() {
        let rows_only = y.set.is_empty() && y.family.is_empty();
        let one_length = y.tuples.iter().all(|s| s.len() == r.len());
        return (rows_only && one_length).then(|| (ShapeKey::Row(r.len()), y.point()));
    }
    let k = class_of(&y.set)?;
    Some((k, y.point()))
}

/// Where `x`, a component of a member, may be held at a place a [`Group`] files, by value or by
/// class, as [`accepts`] decides each piece of `x` against a component there ([`class`]):
/// - A function, the unknown or a variable not rigid is held by none, since no such component
///   holds a function or a variable. A rigid variable is held by those that hold each carrier
///   of its bound: by none of one value, and by the class of the carrier for one carrier.
/// - A set is held by the shapes of its value or class.
/// - Tuples are held by those of their length, by class, and by value by those of their value
///   when they are one value. Tuples that are not one value are looked for in every shape filed
///   by value, since a component of no value is in any.
fn member(x: &Ty, by_value: bool, rigid: &BTreeMap<Arc<str>, u8>) -> Member {
    if x.dynamic || !x.fns.is_empty() {
        return Member::Nowhere;
    }
    let mut carrier = None;
    for v in &x.vars {
        let Some(&m) = rigid.get(v) else {
            return Member::Nowhere;
        };
        let mut cs = Carrier::of_mask(m);
        match (cs.next(), cs.next()) {
            (None, _) => {}
            (Some(c), None) if !by_value && carrier.is_none_or(|d| d == c) => carrier = Some(c),
            _ => return Member::Nowhere,
        }
    }
    if let Some(r) = x.tuples.first() {
        if !x.set.is_empty() || carrier.is_some() {
            return Member::Nowhere;
        }
        return match by_value {
            true => match x.point() {
                Some(v) => Member::At(ShapeKey::Point(v)),
                None => Member::Anywhere,
            },
            false => match x.tuples.iter().all(|s| s.len() == r.len()) {
                true => Member::At(ShapeKey::Row(r.len())),
                false => Member::Nowhere,
            },
        };
    }
    if x.set.is_empty() {
        return match carrier {
            Some(c) => Member::At(ShapeKey::Carrier(c)),
            None => Member::Anywhere,
        };
    }
    if by_value {
        return match x.set.scalar() {
            Some(v) => Member::At(ShapeKey::Point(v)),
            None => Member::Nowhere,
        };
    }
    match class_of(&x.set) {
        Some(k) if carrier.is_none_or(|c| k == ShapeKey::Carrier(c)) => Member::At(k),
        _ => Member::Nowhere,
    }
}

/// The shapes of a group of [`Choices`] whose components have a class ([`class`]) at the same
/// places, and are one value at the same places of those, filed by their components there: by
/// value where they are one value, else by class. A shape filed under another key than a
/// member's holds no component of the member's there ([`member`]).
struct Group {
    /// The places filed, each with whether it is filed by value.
    places: Vec<(usize, bool)>,
    /// The shapes under each key, by their index in the list of shapes, in order.
    buckets: BTreeMap<Vec<ShapeKey>, Vec<usize>>,
    /// Every shape of the group, in order.
    all: Vec<usize>,
    /// For each bucket, and for the group whole (`None`), the shapes whose component at some
    /// place is one variable and nothing else, by that variable, with the place, made once a
    /// search needs it ([`Group::exact`]).
    exact: std::sync::OnceLock<HashMap<Bucket, Arc<ExactVars>>>,
}

/// The shapes of a bucket whose component at a place is one variable and nothing else
/// ([`Ty::as_var`]), by that variable: each shape, in written order, with the place.
type ExactVars = HashMap<Arc<str>, Vec<(usize, usize)>>;

impl Group {
    /// The bucket of the member whose components are `xs`, read with the rigid variables
    /// `rigid`: `None` when no shape of the group holds it.
    fn lookup(&self, xs: &[&Ty], rigid: &BTreeMap<Arc<str>, u8>) -> Option<Bucket> {
        let mut key = Vec::with_capacity(self.places.len());
        let mut anywhere = false;
        for &(j, by_value) in &self.places {
            match member(xs[j], by_value, rigid) {
                Member::Nowhere => return None,
                Member::Anywhere => anywhere = true,
                Member::At(k) => key.push(k),
            }
        }
        if anywhere {
            return Some(None);
        }
        self.buckets.contains_key(&key).then_some(Some(key))
    }

    /// The shapes of the bucket `id`, in order.
    fn bucket(&self, id: &Bucket) -> &[usize] {
        match id {
            None => &self.all,
            Some(k) => &self.buckets[k],
        }
    }

    /// The shapes of the bucket `id` whose component at a place is one variable, by that
    /// variable ([`ExactVars`]), `comps` giving the components of a shape. Made for every
    /// bucket at once, the first time one is asked for: O(n) in the components of the group
    /// (each shape is read twice, for its bucket and for the group whole), once for the type.
    fn exact<'t>(&self, id: &Bucket, comps: &impl Fn(usize) -> Vec<&'t Ty>) -> Arc<ExactVars> {
        let all = self.exact.get_or_init(|| {
            let file = |shapes: &[usize]| {
                let mut out = ExactVars::new();
                for &r in shapes {
                    for (j, d) in comps(r).into_iter().enumerate() {
                        if let Some(v) = d.as_var() {
                            out.entry(v.clone()).or_default().push((r, j));
                        }
                    }
                }
                Arc::new(out)
            };
            let mut all: HashMap<Bucket, Arc<ExactVars>> = (self.buckets.iter())
                .map(|(k, shapes)| (Some(k.clone()), file(shapes)))
                .collect();
            all.insert(None, file(&self.all));
            all
        });
        all[id].clone()
    }
}

/// The shapes of one group of the expected side, its tuples of one length or its payloads of one
/// atom with one length and field names, in [`Group`]s by the places where their components
/// have a class and are one value: a shape with a variable at a place leaves the place filed for
/// the others. The shapes that may hold a member are those of its bucket in each group, and
/// trying them in written order finds the shape the rule of one shape finds, with the same
/// bindings.
struct Choices {
    groups: Vec<Group>,
}

/// The shapes a member may be in: a bucket of each of some groups of [`Choices`], by the
/// group's index.
type Buckets = Vec<(usize, Bucket)>;

impl Choices {
    /// The shapes, each by its index in its list and the keys of its components ([`class`]),
    /// all of one width.
    fn new<'k>(shapes: impl IntoIterator<Item = (usize, &'k [CompKey])>) -> Choices {
        // The groups by the places where a shape's components have a class, each with whether
        // it is one value there; each group's places are set once all are filed.
        let mut by_places: BTreeMap<Vec<(usize, bool)>, Group> = BTreeMap::new();
        for (i, keys) in shapes {
            let mut places = Vec::new();
            let mut key = Vec::new();
            for (j, c) in keys.iter().enumerate() {
                if let Some((k, point)) = c {
                    places.push((j, point.is_some()));
                    key.push(point.clone().map_or_else(|| k.clone(), ShapeKey::Point));
                }
            }
            let group = by_places.entry(places).or_insert_with(|| Group {
                places: Vec::new(),
                buckets: BTreeMap::new(),
                all: Vec::new(),
                exact: std::sync::OnceLock::new(),
            });
            group.buckets.entry(key).or_default().push(i);
            group.all.push(i);
        }
        let groups = (by_places.into_iter())
            .map(|(places, group)| Group { places, ..group })
            .collect();
        Choices { groups }
    }

    /// The buckets of the member whose components are `xs`, read with the rigid variables
    /// `rigid`, one for each group that may hold it.
    fn lookup(&self, xs: &[&Ty], rigid: &BTreeMap<Arc<str>, u8>) -> Buckets {
        (self.groups.iter().enumerate())
            .filter_map(|(g, group)| Some((g, group.lookup(xs, rigid)?)))
            .collect()
    }

    /// Whether the choices hold one shape.
    fn one(&self) -> bool {
        matches!(&self.groups[..], [g] if g.all.len() == 1)
    }

    /// The shapes of the bucket `id` of the group `g`, in order.
    fn bucket(&self, g: usize, id: &Bucket) -> &[usize] {
        self.groups[g].bucket(id)
    }

    /// Why the shapes of the bucket `id` of group `g` may each hold the members found in it,
    /// for a message: the members have `items` items, then the fields `names`.
    fn apart(&self, g: usize, id: &Bucket, items: usize, names: &[&Arc<str>]) -> String {
        let places: Vec<String> = (self.groups[g].places.iter())
            .map(|&(j, _)| match j.checked_sub(items) {
                None => format!("component {}", j + 1),
                Some(f) => format!("field {}", names[f]),
            })
            .collect();
        match (id, &places[..]) {
            (_, []) => "have no component that is one value, of one carrier, of one atom name or \
                        of one tuple length"
                .to_string(),
            (None, _) => format!(
                "are told apart only at {}, where each of the two has a component that any of \
                 them may hold",
                places.join(", ")
            ),
            (Some(_), _) => format!(
                "are told apart only at {}, where they agree with both",
                places.join(", ")
            ),
        }
    }
}

/// The components of a payload shape, items then fields, as [`Comparing::shape_in`] pairs them.
fn comps(s: &Shape) -> Vec<&Ty> {
    s.items.iter().chain(s.fields.values()).collect()
}

/// The group of a payload shape: its number of items and its field names.
type ShapeGroup = (usize, Vec<Arc<str>>);

fn shape_group(s: &Shape) -> ShapeGroup {
    (s.items.len(), s.fields.keys().cloned().collect())
}

/// The tuple and payload shapes of a type of the expected side, grouped and filed ([`Choices`]):
/// the tuples by length, the payloads of each atom it lists by [`ShapeGroup`].
struct Filed {
    rows: HashMap<usize, Choices>,
    payloads: HashMap<Arc<str>, HashMap<ShapeGroup, Choices>>,
    /// The number of the first tuple of the type, in written order, with each digest its
    /// tuples have, made once a tuple piece is looked up ([`Filed::equal`]).
    equal: std::sync::OnceLock<HashMap<u64, usize>>,
    /// The same for its payload shapes, by atom name ([`Filed::equal_shapes`]).
    equal_shapes: std::sync::OnceLock<HashMap<Arc<str>, HashMap<u64, usize>>>,
}

impl Filed {
    /// In the size of `t`'s tuples and payloads. The keys of the tuples are those each row
    /// keeps ([`Row::keys`]); those of a payload shape are found here.
    fn new(t: &Ty) -> Filed {
        let mut rows: HashMap<usize, Vec<(usize, &[CompKey])>> = HashMap::new();
        for (i, r) in t.tuples.iter().enumerate() {
            rows.entry(r.len()).or_default().push((i, &r.keys().comps));
        }
        let mut payloads = HashMap::new();
        for (n, rs) in &t.payloads {
            let Some(rs) = rs else { continue };
            let mut groups: HashMap<ShapeGroup, Vec<(usize, Vec<CompKey>)>> = HashMap::new();
            for (i, r) in rs.iter().enumerate() {
                let keys = comps(r).into_iter().map(class).collect();
                groups.entry(shape_group(r)).or_default().push((i, keys));
            }
            let groups = groups.into_iter();
            payloads.insert(
                n.clone(),
                groups
                    .map(|(g, s)| (g, Choices::new(s.iter().map(|(i, k)| (*i, &k[..])))))
                    .collect(),
            );
        }
        Filed {
            rows: rows
                .into_iter()
                .map(|(n, s)| (n, Choices::new(s)))
                .collect(),
            payloads,
            equal: std::sync::OnceLock::new(),
            equal_shapes: std::sync::OnceLock::new(),
        }
    }

    /// The number of the first tuple of `t`, the type filed, with each digest a tuple of it
    /// keeps: a tuple piece equal to a shape finds it in `O(1)` expected by its own digest
    /// ([`Comparing::row_in`]). Made at the first lookup, in O(k) for `k` tuples.
    ///
    /// Complexity tradeoff: keyed by the digest alone, not by the row, which a hit would
    /// compare with the piece in full: two equal rows built apart share no node, so that took
    /// the depth of the row, at each level of a type nested `n` deep, O(n^2) in all
    /// (`bench::deep_ops::variables_of_a_deep_type_run_on_a_shallow_stack`). A shape of the
    /// same digest that is not equal to the piece is only tried by [`Comparing::held_as_is`],
    /// which asks whether it holds the piece binding nothing, a question as sound for it.
    fn equal(&self, t: &Ty) -> &HashMap<u64, usize> {
        self.equal.get_or_init(|| {
            let mut first = HashMap::with_capacity(t.tuples.len());
            for (i, r) in t.tuples.iter().enumerate() {
                first.entry(r.0.digest).or_insert(i);
            }
            first
        })
    }

    /// [`Filed::equal`] for the payload shapes of each atom `t` lists, by the atom's name.
    fn equal_shapes(&self, t: &Ty) -> &HashMap<Arc<str>, HashMap<u64, usize>> {
        self.equal_shapes.get_or_init(|| {
            let lists = t
                .payloads
                .iter()
                .filter_map(|(n, rs)| Some((n, rs.as_ref()?)));
            (lists.map(|(n, rs)| {
                let mut first = HashMap::with_capacity(rs.len());
                for (i, r) in rs.iter().enumerate() {
                    first.entry(r.0.digest).or_insert(i);
                }
                (n.clone(), first)
            }))
            .collect()
        })
    }
}

/// A component's class and its value when it is one value ([`class`]); none when it has no
/// class.
type CompKey = Option<(ShapeKey, Option<Value>)>;

/// What a component of a tuple holds, as [`near_pairs`] groups tuples by it: no class, a class
/// and more than one value, or one value.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Kind {
    Open,
    Class,
    Point,
}

fn kind(k: &CompKey) -> Kind {
    match k {
        None => Kind::Open,
        Some((_, None)) => Kind::Class,
        Some((_, Some(_))) => Kind::Point,
    }
}

/// What a row keeps to be filed ([`Row::keys`]): the keys of its components, and what each
/// filing reads from them, shared so that filing the row again copies no key.
struct Keys {
    /// The class of each component and its value where it is one value ([`class`]).
    comps: Box<[CompKey]>,
    /// The [`Kind`] of each component, by which [`near_pairs`] groups tuples.
    kinds: Box<[Kind]>,
    /// The [`Kind`] at each place as [`Holders`] groups tuples, and the key it files the tuple
    /// under in its group.
    held: (Arc<[Kind]>, HeldKey),
}

/// The key of a tuple in its group of [`Holders`]: the class at each place where the group has
/// one, with the value where it has one value.
type HeldKey = Arc<[(ShapeKey, Option<Value>)]>;

impl Keys {
    fn new(comps: Box<[CompKey]>) -> Keys {
        let kinds = comps.iter().map(kind).collect();
        let mut held = Vec::with_capacity(comps.len());
        let mut key = Vec::new();
        for c in &comps {
            match c {
                None => held.push(Kind::Open),
                // A component that is one tuple value is filed by its length only ([`Holders`]).
                Some((k @ ShapeKey::Row(_), _)) | Some((k, None)) => {
                    held.push(Kind::Class);
                    key.push((k.clone(), None));
                }
                Some((k, Some(v))) => {
                    held.push(Kind::Point);
                    key.push((k.clone(), Some(v.clone())));
                }
            }
        }
        Keys {
            comps,
            kinds,
            held: (held.into(), key.into()),
        }
    }
}

/// The tuples of one length and one [`Kind`] at each place, each by its index in its list and
/// the keys of its components, which its row keeps ([`Row::keys`]).
type Pattern<'r> = (usize, Cow<'r, [Kind]>);
type Keyed<'r> = Vec<(usize, &'r [CompKey])>;
/// One group of the right side of [`Groups`]: the kind at each place and its tuples.
type RightGroup<'r> = (Cow<'r, [Kind]>, Keyed<'r>);

/// What [`near_pairs`] files: a tuple's row, or an atom's payload shape, its items then its
/// fields.
trait Placed {
    /// How many components it has.
    fn width(&self) -> usize;
    /// The class of each component and its value where it is one value, found once and kept.
    fn keys(&self) -> &Keys;
}

impl Placed for Row {
    fn width(&self) -> usize {
        self.len()
    }
    fn keys(&self) -> &Keys {
        Row::keys(self)
    }
}

impl Placed for Shape {
    fn width(&self) -> usize {
        self.items.len() + self.fields.len()
    }
    fn keys(&self) -> &Keys {
        (self.0.keys).get_or_init(|| {
            Keys::new(
                self.items
                    .iter()
                    .chain(self.fields.values())
                    .map(class)
                    .collect(),
            )
        })
    }
}

impl<P: Placed> Placed for &P {
    fn width(&self) -> usize {
        (**self).width()
    }
    fn keys(&self) -> &Keys {
        (**self).keys()
    }
}

/// The tuples of `rows`, each with the keys of its components, by length and [`Kind`] at each
/// place, each list in written order.
fn by_pattern<'r, P: Placed + 'r>(
    rows: impl IntoIterator<Item = &'r P>,
) -> FMap<Pattern<'r>, Keyed<'r>> {
    let mut out: FMap<Pattern<'r>, Keyed<'r>> = FMap::default();
    for (i, r) in rows.into_iter().enumerate() {
        let Keys { comps, kinds, .. } = r.keys();
        let kinds = Cow::Borrowed(&kinds[..]);
        // With every place open every tuple of a length is one group, no key is read
        // ([`project`]), and every tuple of the other side of that length is near it.
        #[cfg(test)]
        let kinds = match NEAR_ALL.get() {
            true => Cow::Owned(vec![Kind::Open; r.width()]),
            false => kinds,
        };
        out.entry((r.width(), kinds)).or_default().push((i, comps));
    }
    out
}

/// For each tuple of `left`, the tuples of `right` of its length that may share a value with
/// it, by their indices, in written order ([`Near`]). A tuple of `right` left out shares no
/// value with the tuple of `left`: their meet is empty ([`Ty::meet`] gives an empty component
/// at the place), and the union of `right` holds the tuple exactly when the union of the tuples
/// given holds it.
fn near_pairs<'r, P: Placed + 'r>(
    left: impl IntoIterator<Item = &'r P, IntoIter: ExactSizeIterator>,
    right: impl IntoIterator<Item = &'r P>,
) -> Vec<Vec<usize>> {
    let left = left.into_iter();
    let n = left.len();
    let groups = Groups::new(left, right);
    let mut near = Near::new(&groups);
    let mut sorted = |l| {
        let mut is: Vec<usize> = near.of(l).collect();
        is.sort_unstable();
        is
    };
    (0..n).map(&mut sorted).collect()
}

/// An item of a payload shape as [`Comparing::shape_rest`] splits it: the type, and the
/// kernel type of its values, which decides.
type Item = (Ty, KType);

/// The rest of a payload shape less shapes ([`Comparing::shape_rest`]).
#[derive(Default)]
struct Rest {
    /// The rest as shapes, those whose items list a value ([`ShapeData::void`]).
    shapes: Vec<Shape>,
    /// The kernel type of each shape of the rest, void or not: together they hold the values
    /// of the difference and no other (proof at [`Comparing::shape_rest`]).
    parts: Vec<KType>,
}

/// Whether shapes hold a payload shape together ([`Rest::held`]).
#[derive(Clone, Copy, Debug)]
enum Held {
    /// They hold it: nothing of it is outside them.
    Yes,
    /// A value of it outside them was built and checked.
    No,
    /// Neither: a part of the rest is not proved empty and no value of it was built.
    Refused(Refusal),
}

impl Rest {
    fn push(&mut self, items: Vec<Item>) {
        let (items, kernels): (Vec<Ty>, Vec<KType>) = items.into_iter().unzip();
        let s = Shape::new(items, BTreeMap::new());
        if !s.void {
            self.shapes.push(s);
        }
        self.parts.push(KType::tuple(kernels));
    }

    /// Whether the shapes taken hold the shape whose rest this is, from the kernel's verdict on
    /// each part ([`KType::verdict`]): `No` at the first part shown to hold a value, `Yes` when
    /// each part is empty, else refused with the first part's cause.
    ///
    /// Proof: the parts hold every value of the difference and no other ([`Comparing::shape_rest`]).
    /// A value the kernel builds for a part and checks against it ([`Verdict::Inhabited`]) is
    /// then a value of the shape outside the shapes taken, so the answer is no. When each part
    /// is empty, so is the difference, and the answer is yes. A part that is neither decides
    /// nothing. This does not rest on [`KType::is_empty`] or [`Ty::is_empty`] being exact: a
    /// part that `is_empty` did not prove empty is kept, and its verdict tells. Why
    /// (PROOF-diff-exact-skip): for the 4 pigeons and 3 holes rows of
    /// `kinds::a_payload_whose_tuple_item_needs_a_split_of_many_components_is_refused`,
    /// `is_empty` does not prove the empty rest empty, and the comparison read that rest as a
    /// value outside, a definite no where the answer is yes.
    ///
    /// Complexity tradeoff: naive version, the rest read as a no when it has a part, O(1) and
    /// wrong where `is_empty` is not exact; used, the verdict of each part up to the first one
    /// shown to hold a value, one search of the kernel each, all of them only where none is.
    fn held(&self) -> Held {
        let mut refused = None;
        for p in &self.parts {
            match p.verdict() {
                Verdict::Inhabited => return Held::No,
                Verdict::Empty => {}
                Verdict::Refused(r) => {
                    refused.get_or_insert(r);
                }
            }
        }
        refused.map_or(Held::Yes, Held::Refused)
    }
}

/// The tuples of two lists `left` and `right` grouped for [`Near`]: by length and [`Kind`] at
/// each place, each with the keys of its components.
struct Groups<'r> {
    /// The groups of `right`, by length.
    right: FMap<usize, Vec<RightGroup<'r>>>,
    /// The groups of `left`, each its length and kinds.
    left: Vec<Pattern<'r>>,
    /// For each tuple of `left`, its group and the keys of its components; none when `right` has
    /// no tuple.
    of: Vec<Option<(usize, &'r [CompKey])>>,
}

impl<'r> Groups<'r> {
    fn new<P: Placed + 'r>(
        left: impl IntoIterator<Item = &'r P, IntoIter: ExactSizeIterator>,
        right: impl IntoIterator<Item = &'r P>,
    ) -> Groups<'r> {
        let (left, mut right) = (left.into_iter(), right.into_iter().peekable());
        let mut groups = Groups {
            right: FMap::default(),
            left: Vec::new(),
            of: vec![None; left.len()],
        };
        if left.len() == 0 || right.peek().is_none() {
            return groups;
        }
        for ((len, kinds), rows) in by_pattern(right) {
            groups.right.entry(len).or_default().push((kinds, rows));
        }
        for (pattern, members) in by_pattern(left) {
            for (l, keys) in members {
                groups.of[l] = Some((groups.left.len(), keys));
            }
            groups.left.push(pattern);
        }
        groups
    }
}

/// The right tuples of the groups of one length, each group filed by the keys a group of the
/// left side reads ([`Near`]).
type Filing<'g> = Vec<FMap<Vec<(&'g ShapeKey, Option<&'g Value>)>, Vec<usize>>>;

/// For each tuple of a list `left`, the tuples of a list `right` of its length that may share
/// a value with it ([`Groups`]). Two components share no value when both have a class
/// ([`class`]) and the classes differ, or both are one value and the values differ: the
/// carriers, the atoms of each name and the tuples of each length are disjoint, and two values
/// the kernel tells apart are unequal [`Value`]s. Any two other components may share one, so a
/// tuple of `right` not given for a tuple of `left` shares no value with it.
///
/// For a group of each side, a tuple of one may share a value with a tuple of the other exactly
/// when they agree at each place where both have a class: on the class, and on the value where
/// both are one value. So the tuples of each right group are filed by those keys, and each
/// tuple of the left group finds its own by one lookup. The right groups are filed for a left
/// group when the first tuple of the left group is read, so a reader that stops at the first
/// pair it wants ([`Ty::meets`]) files only the groups read before it.
///
/// Complexity tradeoff: each group of one side is filed or looked up once for each group of
/// the other of its length. What is given up: the cost is expected O((l·G + r·H)·w + l·G·log G)
/// (hash maps; the log G sorts the buckets found into one order) for `l` and `r` tuples of width `w` in `H` and `G` groups, and a reader pays for each pair it
/// reads, up to `l·r`, so `n` tuples in about `n` groups on each side cost about `n^2`. Why: a
/// tuple of points and wildcards encodes a vector of bits (1 as the point `1` on one side and
/// `0` on the other, 0 as `int`), so that two such tuples share a value exactly when the vectors
/// are orthogonal; finding whether any of `n` vectors of about `c·log n` bits is orthogonal to
/// another, which is what `meets` decides on them, takes `n^(2-o(1))` time unless the strong
/// exponential time hypothesis fails, even when no pair is found, and the groups of such tuples
/// are then as many as the tuples. In a written union the groups are few. Structure: `n` tuples
/// of width `2·log2 n`, each a different arrangement of points and `int`. Tests:
/// `tests/steps/l01_22_type_representation/kinds.rs`,
/// `meeting_and_subtracting_tuples_of_many_patterns_costs_the_patterns` and
/// `meets_of_tuples_of_many_patterns_costs_the_patterns`; COMPLEXITY.md F127 and F132. A
/// complete solution does not exist under that hypothesis; one could only refuse such unions,
/// which would change the answers of narrowing that are found today.
/// Naive version: every pair of tuples compared, O(l·r·w); used: the filing above.
struct Near<'g> {
    groups: &'g Groups<'g>,
    /// For each group of `left` once one of its tuples is read, the right groups of its length
    /// filed by its keys, in the order of `groups.right`.
    filed: Vec<Option<Filing<'g>>>,
}

impl<'g> Near<'g> {
    fn new(groups: &'g Groups<'g>) -> Near<'g> {
        Near {
            groups,
            filed: (0..groups.left.len()).map(|_| None).collect(),
        }
    }

    /// The tuples of `right` that may share a value with the tuple `l` of `left`, bucket by
    /// bucket, the buckets in the order of their first tuples, each in written order.
    fn of(&mut self, l: usize) -> impl Iterator<Item = usize> + '_ {
        let groups = self.groups;
        let mut buckets: Vec<&[usize]> = Vec::new();
        if let Some((q, keys)) = &groups.of[l] {
            let (len, kinds) = &groups.left[*q];
            let right = groups.right.get(len).map_or(&[][..], Vec::as_slice);
            let filed = self.filed[*q].get_or_insert_with(|| {
                let file = |(p, rows): &'g RightGroup<'g>| {
                    let mut f: FMap<_, Vec<usize>> = FMap::default();
                    for (i, ks) in rows {
                        f.entry(project(ks, p, kinds)).or_default().push(*i);
                    }
                    f
                };
                right.iter().map(file).collect()
            });
            for (f, (p, _)) in filed.iter().zip(right) {
                if let Some(b) = f.get(&project(keys, kinds, p)) {
                    buckets.push(b);
                }
            }
            // The groups of `right` come in no fixed order; their buckets, which hold no tuple
            // twice, are read by first tuple, so that a reader tries the pairs in one order on
            // every run.
            buckets.sort_unstable_by_key(|b| b[0]);
        }
        buckets.into_iter().flatten().copied()
    }
}

/// Whether two tuples of one length with the component keys `a` and `b` share no value by the
/// rule of [`near_pairs`]: at some place both have a class and the classes differ, or both are
/// one value and the values differ. [`near_pairs`] lists for a tuple exactly the tuples not
/// apart from it.
fn apart(a: &[CompKey], b: &[CompKey]) -> bool {
    a.iter().zip(b).any(|(x, y)| match (x, y) {
        (Some((k, v)), Some((l, w))) => k != l || matches!((v, w), (Some(v), Some(w)) if v != w),
        _ => false,
    })
}

/// The keys of the components `keys` of a tuple of the group `p` at the places where the tuples
/// of the group `q` of the other side have a class too, with the value where both are one value.
fn project<'k>(
    keys: &'k [CompKey],
    q: &[Kind],
    p: &[Kind],
) -> Vec<(&'k ShapeKey, Option<&'k Value>)> {
    (keys.iter().zip(q.iter().zip(p)))
        .filter_map(|(key, (&q, &p))| {
            let (k, v) = key.as_ref()?;
            match (q, p) {
                (Kind::Open, _) | (_, Kind::Open) => None,
                (Kind::Point, Kind::Point) => Some((k, v.as_ref())),
                _ => Some((k, None)),
            }
        })
        .collect()
}

/// The class of a value, as [`class`] gives the class of a component that holds it: the
/// carrier of a boolean, number or string, the name of an atom, the length of a tuple. None
/// for a keypath or a family, which no component with a class holds: such a component holds
/// no function, and its set is within one carrier, within the atoms of one name, or empty
/// beside its tuples.
fn value_class(x: &Value) -> Option<ShapeKey> {
    Some(match x {
        Value::Bool(_) => ShapeKey::Carrier(Carrier::Bool),
        Value::Int(_) | Value::Big(_) => ShapeKey::Carrier(Carrier::Int),
        Value::Rat(_) => ShapeKey::Carrier(Carrier::Rat),
        Value::Float(_) => ShapeKey::Carrier(Carrier::F64),
        Value::Float32(_) => ShapeKey::Carrier(Carrier::F32),
        Value::Str(_) => ShapeKey::Carrier(Carrier::Str),
        Value::Atom(a) => ShapeKey::Atom(a.name.clone()),
        Value::Tuple(xs) => ShapeKey::Row(xs.len()),
        Value::Path(_) | Value::Family(_) => return None,
    })
}

/// The tuples of one length of a type, filed for the tuple values [`Ty::contains`] looks for
/// in them ([`Pairs::contains`]): in groups by [`Kind`] at each place, and in each group by
/// their classes at the places where they have one and their values where they are one
/// scalar value. A tuple holds a value only when, at each such place, the value's component
/// is of that class ([`value_class`]) and, where the tuple's component is one value, equal to
/// it; so each group is looked up once by the value's own key, and a tuple of no group's
/// bucket does not hold the value.
///
/// A component that is one tuple value is filed by its length only: comparing a value's
/// component with it would read the two whole, and a value compared with many types would be
/// read once for each, where the walk of the pair compares them through the memo of pairs.
///
/// Complexity tradeoff: each group is looked up once for each value. What is given up: the
/// cost is expected O(l·w + G·log G) to file `l` tuples of width `w` (hash maps; the groups are
/// sorted into one order) and O(g·w + p) per value
/// for the `g` groups looked up (at most `G`, the groups) and `p` tuples found before one
/// holds the value, so `l` tuples in about `l` groups, against `r` values,
/// cost about `l·r`. Why: a tuple of points and `int` encodes a vector of bits (1 as the point
/// `0`, 0 as `int`), and a tuple value of zeros and ones holds in it exactly when the two
/// vectors are orthogonal; deciding for each of `r` vectors of about `c·log n` bits whether one
/// of `l` such vectors is orthogonal to it is the orthogonal vectors problem, `n^(2-o(1))`
/// unless the strong exponential time hypothesis fails. In a written union the groups are
/// few. Structure: `n` tuples of width `2·log2 n`, each a different arrangement of points and
/// `int`. Test: `tests/steps/l01_22_type_representation/kinds.rs`,
/// `contains_of_tuples_of_many_patterns_costs_the_patterns`; COMPLEXITY.md F133. A complete
/// solution does not exist under that hypothesis; one could only refuse such unions, which
/// would refuse values the type holds.
/// Naive version: every tuple scanned for each value, O(l·r·w); used: the lookups above.
struct Holders {
    /// Each group's kinds, and its tuples under each key, by their index in the type's tuples,
    /// in written order; the groups in the order of their first tuple.
    groups: Vec<(Arc<[Kind]>, ByKey)>,
}

/// The tuples of one group of [`Holders`] under their key ([`HeldKey`]).
type ByKey = FMap<HeldKey, Vec<usize>>;

/// A hash map of the filings of tuples ([`Holders`], [`Groups`], [`Near`]), hashed by
/// [`Digest`]: with no seed, so the same on every run, though no result depends on its order.
/// Each filing puts what it finds in written order itself.
type FMap<K, V> = HashMap<K, V, FilingHash>;

/// The hasher of [`FMap`]: [`Digest`] from no seed, or in a test from `SEED` when it is set.
#[derive(Clone, Copy, Default)]
struct FilingHash;

impl std::hash::BuildHasher for FilingHash {
    type Hasher = Digest;

    #[cfg(not(test))]
    fn build_hasher(&self) -> Digest {
        Digest::default()
    }

    #[cfg(test)]
    fn build_hasher(&self) -> Digest {
        let mut h = Digest::default();
        if SEED.get() != 0 {
            std::hash::Hasher::write_u64(&mut h, SEED.get());
        }
        h
    }
}

#[cfg(test)]
thread_local! {
    /// The seed of the hasher of the filings ([`FilingHash`]), for the test that their results do
    /// not depend on it.
    static SEED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

impl Holders {
    /// The tuples `rows` of `t`, by their indices, filed.
    fn new(t: &Ty, rows: &[usize]) -> Holders {
        // Each group's first tuple, by which the groups are put in order.
        let mut groups: FMap<Arc<[Kind]>, (usize, ByKey)> = FMap::default();
        for &i in rows {
            let (kinds, key) = &t.tuples[i].keys().held;
            let (_, filed) = (groups.entry(kinds.clone())).or_insert_with(|| (i, FMap::default()));
            filed.entry(key.clone()).or_default().push(i);
        }
        let mut groups: Vec<_> = groups.into_iter().collect();
        groups.sort_unstable_by_key(|(_, (first, _))| *first);
        Holders {
            groups: groups
                .into_iter()
                .map(|(kinds, (_, filed))| (kinds, filed))
                .collect(),
        }
    }

    /// The tuples that may hold the tuple value of `items`, group by group, each looked up
    /// only when the tuples before it have been read, so that a value held by a tuple of an
    /// early group costs the lookups up to that group only. The order is the same on every run.
    fn of<'h>(&'h self, items: &'h Items) -> impl Iterator<Item = usize> + 'h {
        let classes: Vec<Option<ShapeKey>> = items.iter().map(value_class).collect();
        let mut key = Vec::with_capacity(items.len());
        self.groups.iter().flat_map(move |(kinds, filed)| {
            // A group of one key, as each group is when every tuple is its own arrangement, is
            // compared with the value place by place, stopping at the first that differs,
            // instead of building and hashing the value's whole key: the same answer, since
            // the lookup also compares the keys for equality.
            let one = (filed.len() == 1).then(|| filed.iter().next()).flatten();
            let mut places = one.map(|(held, _)| held.iter());
            key.clear();
            for ((k, x), kind) in classes.iter().zip(items.iter()).zip(kinds.iter()) {
                if *kind == Kind::Open {
                    continue;
                }
                let Some(k) = k else {
                    return [].iter().copied();
                };
                // The group's tuples are one scalar value here ([`Keys::new`]), so a value's
                // atom or tuple, which may be large, is in none of them and is not hashed.
                if *kind == Kind::Point && !matches!(k, ShapeKey::Carrier(_)) {
                    return [].iter().copied();
                }
                let point = (*kind == Kind::Point).then_some(x);
                match places.as_mut().map(Iterator::next) {
                    Some(Some((hk, hx))) if hk == k && hx.as_ref() == point => {}
                    Some(_) => return [].iter().copied(),
                    None => key.push((k.clone(), point.cloned())),
                }
            }
            match one {
                Some((_, found)) => found.as_slice(),
                None => filed.get(&key[..]).map_or(&[][..], Vec::as_slice),
            }
            .iter()
            .copied()
        })
    }
}

/// How the tuples of one length of a type are read for the values [`Pairs::contains`] looks
/// for in them, by the number of values read so far.
enum Visits {
    /// One value read, by a scan of all the type's tuples, which lists none of them.
    Once,
    /// `n` values read, each by a scan of `rows`, the tuples of the length, which the walk of
    /// each value shares.
    Scanned { n: usize, rows: Rc<[usize]> },
    /// Filed, and each value read by lookup.
    Filed(Rc<Holders>),
}

/// The tuples of a type to compare with one tuple value ([`Pairs::tried`]): every tuple of its
/// length, found by a scan of all the type's tuples; those of its length, listed; or those
/// [`Holders`] finds, which the walk of each value shares.
enum Tried {
    Every,
    Scanned(Rc<[usize]>),
    Found(Rc<Holders>),
}

/// The tuples of each length of each type node read by one [`Ty::contains`], by the node's
/// address, which stays put while the type is borrowed: the map is made for one walk, every
/// key is a node of the type that walk borrows to its end, and the map is only read by
/// `entry`, never iterated.
type Filings = HashMap<(*const Ty, usize), Visits>;

#[cfg(test)]
thread_local! {
    /// How [`Pairs::contains`] reads the tuples of a type, for the differential test: `None`
    /// as in use, `Some(false)` by a scan of every tuple of the length for each value, as
    /// before [`Holders`], and `Some(true)` filed from the first value on.
    static FILE: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

#[cfg(test)]
thread_local! {
    /// Whether [`near_pairs`] gives every tuple of the length, as meeting and subtracting did
    /// before it: the form the differential test compares it with.
    static NEAR_ALL: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
thread_local! {
    /// Whether [`Comparing::search`] tries every shape in written order and refuses nothing, as
    /// before the index: the form the differential test compares the index with.
    static SCAN_ALL: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// What the comparison of the pieces of one type with a type `t` of the expected side keeps
/// between the pieces: where `t` sits, its shapes filed once a piece needs them, and the
/// buckets of its tuple shapes searched past their first shape, each with the tuple that did.
struct Search<'a> {
    site: Site<'a>,
    filed: Option<Arc<Filed>>,
    searched: Searched<usize, Row>,
    /// The pins of the bindings in the buckets of its tuple shapes ([`Bound`]).
    bound: BoundTable<usize>,
}

impl<'a> Search<'a> {
    fn new(site: Site<'a>) -> Search<'a> {
        Search {
            site,
            filed: None,
            searched: Searched::new(),
            bound: BoundTable::new(),
        }
    }
}

/// A bucket of [`Choices`]: its group's key `G` among the groups of one union, the group's
/// index in the [`Choices`], and the bucket.
type BucketAt<G> = (G, usize, Bucket);

/// What the members of one union keep between their searches ([`Comparing::search`]): each
/// bucket a member has searched past the first shape it tried there, with that member, and
/// each bucket's shapes pinned by the ceilings of their variables ([`Pins`]), with the ceilings
/// read, once a member has needed them.
struct Searched<G, M> {
    by: BTreeMap<BucketAt<G>, M>,
    pins: BTreeMap<BucketAt<G>, (Ceilings, Option<Rc<Pins>>)>,
}

impl<G: Ord + Clone, M> Searched<G, M> {
    fn new() -> Searched<G, M> {
        Searched {
            by: BTreeMap::new(),
            pins: BTreeMap::new(),
        }
    }

    /// The pins of the bucket `at` under the ceilings of `binds`, if made.
    fn pins(&self, at: &BucketAt<G>, binds: &Binds) -> Option<Rc<Pins>> {
        let (c, p) = self.pins.get(at)?;
        Arc::ptr_eq(c, binds.ceilings.as_ref()?).then(|| p.clone())?
    }

    /// [`Searched::pins`], made now from the shapes `bucket` (whose components `comps` gives)
    /// if not yet; none where `binds` has no ceilings.
    fn pin<'t>(
        &mut self,
        at: BucketAt<G>,
        bucket: &[usize],
        comps: &impl Fn(usize) -> Vec<&'t Ty>,
        binds: &Binds,
        cx: &Cx,
    ) -> Option<Rc<Pins>> {
        let ceilings = binds.ceilings.clone()?;
        if let Some((c, p)) = self.pins.get(&at)
            && Arc::ptr_eq(c, &ceilings)
        {
            return p.clone();
        }
        let p = Pins::of(bucket, comps, binds, cx).map(Rc::new);
        self.pins.insert(at, (ceilings, p.clone()));
        p
    }
}

/// The shapes of one bucket of [`Choices`] split by the ceilings of their variables
/// ([`ceilings`]), so that [`Comparing::search`] finds those that may hold a member by lookup.
/// A shape is pinned at the first place where its component is one variable `v` and nothing
/// else, neither rigid nor a function, whose ceiling `c` is not the unknown and holds no
/// variable that is rigid or a function. There the shape holds a member only if each variable
/// of the member's component that is neither rigid nor a function is `v` or a variable of `c`,
/// and, where `c` holds only variables, only if the component holds no scalar value
/// ([`Pins::lists`] has the proof). Each pinned shape is filed at that place under `v` and
/// under each variable of `c`, and with the shapes `open` there when `c` holds more than
/// variables; the other shapes are free.
struct Pins {
    /// The shapes pinned nowhere, in written order.
    free: Rc<[usize]>,
    /// Each place at which shapes are pinned, with those shapes, those whose ceiling holds
    /// scalars, tuples or functions (`open`), and those filed under each variable, in written
    /// order.
    at: Vec<PinnedAt>,
}

/// The shapes pinned at one place ([`Pins`]).
struct PinnedAt {
    place: usize,
    all: Rc<[usize]>,
    open: Rc<[usize]>,
    by: HashMap<Arc<str>, Rc<[usize]>>,
}

/// A list of shapes [`Comparing::search`] tries, in written order: a bucket of [`Choices`], a
/// list of its [`Pins`], the shapes of a bucket its [`Bound`] pins nowhere (`Free`, with the
/// runs of pinned places in the bucket), or a list of its [`Bound`] pins (`Set`). A list is
/// read from a shape on by its place in the list (`n`), or, for `Set`, by the shape.
enum Shapes<'c> {
    Bucket(&'c [usize]),
    Pinned(Rc<[usize]>),
    Free(&'c [usize], imbl::OrdMap<usize, usize>),
    Set(imbl::OrdSet<usize>),
}

impl Shapes<'_> {
    /// The first shape of the list after the shape `r`, or the first of all when `r` is none,
    /// with its place in the list. O(log n).
    fn after(&self, r: Option<usize>) -> Option<(usize, usize)> {
        let from = |s: &[usize]| r.map_or(0, |r| s.partition_point(|&x| x <= r));
        match self {
            Shapes::Bucket(s) => s.get(from(s)).map(|&x| (x, from(s))),
            Shapes::Pinned(s) => s.get(from(s)).map(|&x| (x, from(s))),
            Shapes::Free(s, runs) => {
                let n = free_from(runs, from(s));
                s.get(n).map(|&x| (x, n))
            }
            Shapes::Set(s) => match r {
                Some(r) => s.range(r + 1..).next(),
                None => s.iter().next(),
            }
            .map(|&x| (x, 0)),
        }
    }

    /// The shape after the shape `r`, at the place `n` of the list, with its place. O(log n)
    /// amortized: a run of pinned places is passed in one lookup.
    fn next(&self, r: usize, n: usize) -> Option<(usize, usize)> {
        match self {
            Shapes::Bucket(s) => s.get(n + 1).map(|&x| (x, n + 1)),
            Shapes::Pinned(s) => s.get(n + 1).map(|&x| (x, n + 1)),
            Shapes::Free(s, runs) => {
                let n = free_from(runs, n + 1);
                s.get(n).map(|&x| (x, n))
            }
            Shapes::Set(_) => self.after(Some(r)),
        }
    }
}

/// The first place from `n` on that no run of `runs` (start to end, the end not in it) holds.
fn free_from(runs: &imbl::OrdMap<usize, usize>, n: usize) -> usize {
    match runs.range(..=n).next_back() {
        Some((_, &end)) if end > n => end,
        _ => n,
    }
}

/// The variable `w` that the variable `v` of a shape is bound to alone, where `v`, standing
/// alone as a component, then holds no piece but itself and `Var(w)` ([`accepts`]): `v` is
/// neither rigid nor a function, is bounded ([`Binds::bound`]), and is bound to `w` and
/// nothing else, and `w` is of a known mask that is not one carrier ([`var_mask`],
/// [`mask_carrier`]), so `w` stands for one of several carriers and `v` takes nothing else
/// beside it.
fn bound_alone<'b>(v: &str, binds: &'b Binds, cx: &Cx) -> Option<&'b Arc<str>> {
    if cx.rigid.contains_key(v) || cx.fns.contains_key(v) {
        return None;
    }
    binds.bound(v)?;
    let w = binds.get(v)?.as_var()?;
    mask_carrier(var_mask(w, cx)?).is_none().then_some(w)
}

/// Whether the variable `y` of a member's component is one that [`Bound`] keys shapes by: not
/// a function, and, if rigid, of a mask that is not empty (a rigid variable of no carrier is
/// within every type).
fn keyed(y: &Arc<str>, cx: &Cx) -> bool {
    !cx.fns.contains_key(y) && cx.rigid.get(y).is_none_or(|&m| m != 0)
}

/// Whether the component `x` of a member holds a piece that the component `Var(v)` of a shape
/// does not hold, `v` bound alone to `w` ([`bound_alone`]): the unknown, a scalar value, a
/// tuple, a function, or a variable [`keyed`] that is neither `v` nor `w` ([`Bound`] has the
/// proof).
fn left_out_by(x: &Ty, v: &str, w: &str, cx: &Cx) -> bool {
    x.dynamic
        || !x.set.is_empty()
        || !x.tuples.is_empty()
        || !x.fns.is_empty()
        || (x.vars.iter()).any(|y| keyed(y, cx) && **y != *v && **y != *w)
}

/// The shapes of one bucket of [`Choices`] pinned by the bindings so far
/// ([`Comparing::search`]): a shape whose component at a place is one variable `v`, bound
/// alone to `w` ([`bound_alone`]), is pinned there under `v` and `w`, and a member whose
/// component there holds a piece [`left_out_by`] names skips it. Each shape is pinned at one
/// place at most, the first at which a binding pinned it; the shapes pinned nowhere are read
/// from the bucket past the runs of pinned places. The tables are persistent maps, so a copy
/// for the split rows of [`Comparing::row_in`], kept only when the rows are held, is O(1).
///
/// Proof that a shape left out does not hold the member: at its place `j` its component is
/// `t = Var(v)` alone, `v` bound alone to `w`, and the member's component `x` there holds a
/// piece `p` that is the unknown, a non-empty scalar part (`x.set` is not empty, and
/// [`Ty::pieces`] gives each non-empty part of it), a tuple, a function, or `Var(y)` with `y`
/// neither a function nor `v` nor `w`, nor rigid of an empty mask ([`keyed`]).
/// [`Comparing::rows`] and [`Comparing::shape_in`] hold the member only if
/// [`Comparing::sub_by_shape`] holds `x` in `t` at a site inside the shape ([`Site::In`]), which holds only if [`accepts`] holds `p`.
/// There `t` is not the unknown, and `ok` is false: `Dyn` is never; a non-empty `Set(s)` is
/// not within the empty `t.set`, and `v`, the one variable of `t`, is not rigid; a tuple is
/// not within the empty `t.set`, and [`Comparing::row_in`] finds no tuple shape of `t`, as `t`
/// has none, nor holds any row a split makes; a function, as `t.fns` is empty; `Var(y)`, as
/// `t.vars` is `{v}`, `y` is not `v`, and if `y` is rigid its mask has a carrier, which the
/// empty `t.set` does not hold. Then `v`, bindable, is bound only if `admits` holds `p`: `v`
/// is bounded and bound to `w` alone, so `admits` holds `p` only if `p` is `Var(w)`, or of
/// the one carrier of `w`'s mask, which has not one carrier; `p` is neither. At a site inside a shape nothing else is bound, so `p` is not held.
///
/// The pins hold while the bindings only grow, as they do through the members of one union:
/// a member keeps what its shape binds, a failed attempt binds nothing ([`Comparing::search`]),
/// and [`accepts`] adds to `v`'s binding only a piece `admits` holds, `Var(w)` itself, at a
/// site inside a shape. Outside every shape ([`Site::Other`]) a piece no variable admits is
/// bound to the first variable all the same, and [`accepts`] then drops the pins of the
/// search. Not proved: that nothing else shrinks or rewrites a binding while one search lives;
/// the evidence is a reading of the writes to [`Binds`] (only `unite` and `insert` within a
/// search, the removals in tests or on binds of their own) and the differential test
/// `bound_shapes_agree_with_trying_every_shape`.
#[derive(Clone, Default)]
struct Bound {
    /// The runs of places in the bucket of the shapes pinned, each from its start to its end
    /// (the end not in it), apart and not touching.
    runs: imbl::OrdMap<usize, usize>,
    /// Each place at which shapes are pinned, with those shapes.
    at: imbl::OrdMap<usize, BoundAt>,
    /// The variables whose shapes are pinned.
    done: imbl::OrdSet<Arc<str>>,
}

/// The shapes pinned at one place by [`Bound`]: all, and those under each variable, `v` or
/// `w`, in written order.
#[derive(Clone, Default)]
struct BoundAt {
    all: imbl::OrdSet<usize>,
    by: imbl::OrdMap<Arc<str>, imbl::OrdSet<usize>>,
}

/// The [`Bound`] pins of each bucket a search has needed them in, by bucket.
type BoundTable<G> = imbl::OrdMap<BucketAt<G>, Bound>;

impl Bound {
    /// Pins the shapes `exact` lists under `v` (those of the bucket `bucket` whose component at
    /// a place is `Var(v)`), each at that place, under `v` and `w`, where not pinned already.
    /// O(k log n) for k such shapes, once for each variable.
    fn pin(&mut self, bucket: &[usize], exact: &ExactVars, v: &Arc<str>, w: &Arc<str>) {
        if self.done.insert(v.clone()).is_some() {
            return;
        }
        for &(r, j) in exact.get(v).into_iter().flatten() {
            let Ok(n) = bucket.binary_search(&r) else {
                continue;
            };
            if free_from(&self.runs, n) != n {
                continue;
            }
            let start = match self.runs.range(..n).next_back() {
                Some((&s, &e)) if e == n => s,
                _ => n,
            };
            let end = self.runs.remove(&(n + 1)).unwrap_or(n + 1);
            self.runs.insert(start, end);
            let at = self.at.entry(j).or_default();
            at.all.insert(r);
            for key in [v, w] {
                at.by.entry(key.clone()).or_default().insert(r);
            }
        }
    }

    /// The pins `old` with those of the variables that the components `row` of a shape of
    /// `bucket` have bound alone in `binds` ([`bound_alone`]) added, if any is new, and whether
    /// such a variable leaves out the member whose components are `xs` ([`left_out_by`]).
    /// `exact` gives the bucket's shapes by variable, read only when a variable is new.
    fn grow(
        old: Option<&Bound>,
        bucket: &[usize],
        row: &[&Ty],
        xs: &[&Ty],
        binds: &Binds,
        exact: impl Fn() -> Arc<ExactVars>,
        cx: &Cx,
    ) -> (bool, Option<Bound>) {
        let mut pins: Option<Bound> = None;
        let mut left_out = false;
        for (j, d) in row.iter().enumerate() {
            let Some((v, w)) = d
                .as_var()
                .and_then(|v| Some((v, bound_alone(v, binds, cx)?)))
            else {
                continue;
            };
            left_out |= left_out_by(xs[j], v, w, cx);
            if pins.as_ref().or(old).is_some_and(|p| p.done.contains(v)) {
                continue;
            }
            let pins = pins.get_or_insert_with(|| old.cloned().unwrap_or_default());
            pins.pin(bucket, &exact(), v, w);
        }
        (left_out, pins)
    }

    /// The lists of shapes of the bucket `bucket` that may hold the member whose components are
    /// `xs`: those pinned nowhere, and at each place pinned, none where the member's component
    /// there holds the unknown, a scalar value, a tuple or a function, else those under its
    /// first variable [`keyed`], where it has one, else all pinned there. The lists are apart,
    /// as each shape is pinned at one place at most.
    fn lists<'c>(&self, bucket: &'c [usize], xs: &[&Ty], cx: &Cx) -> Vec<Shapes<'c>> {
        let mut out = vec![Shapes::Free(bucket, self.runs.clone())];
        for (&j, at) in &self.at {
            let x = xs[j];
            if x.dynamic || !x.set.is_empty() || !x.tuples.is_empty() || !x.fns.is_empty() {
                continue;
            }
            let shapes = match x.vars.iter().find(|y| keyed(y, cx)) {
                Some(y) => at.by.get(y).cloned().unwrap_or_default(),
                None => at.all.clone(),
            };
            if !shapes.is_empty() {
                out.push(Shapes::Set(shapes));
            }
        }
        out
    }
}

impl Pins {
    /// The pins of the shapes `bucket`, whose components `comps` gives, under the ceilings of
    /// `binds`: none when no shape is pinned. Cost: the components of the shapes, and for each
    /// shape pinned the variables of its ceiling.
    fn of<'t>(
        bucket: &[usize],
        comps: &impl Fn(usize) -> Vec<&'t Ty>,
        binds: &Binds,
        cx: &Cx,
    ) -> Option<Pins> {
        let special = |w: &Arc<str>| cx.rigid.contains_key(w) || cx.fns.contains_key(w);
        let mut free = Vec::new();
        type At = (Vec<usize>, Vec<usize>, HashMap<Arc<str>, Vec<usize>>);
        let mut at: BTreeMap<usize, At> = BTreeMap::new();
        for &r in bucket {
            let pin = comps(r).into_iter().enumerate().find_map(|(j, d)| {
                let v = d.as_var().filter(|v| !special(v))?;
                let c = (binds.ceiling(v)).filter(|c| !c.dynamic && !c.vars.iter().any(special))?;
                Some((j, v.clone(), c))
            });
            let Some((j, v, c)) = pin else {
                free.push(r);
                continue;
            };
            let (all, open, by) = at.entry(j).or_default();
            all.push(r);
            if !c.set.is_empty() || !c.tuples.is_empty() || !c.fns.is_empty() {
                open.push(r);
            }
            for w in c.vars.iter().filter(|w| **w != v).chain([&v]) {
                by.entry(w.clone()).or_default().push(r);
            }
        }
        let at = (at.into_iter())
            .map(|(place, (all, open, by))| PinnedAt {
                place,
                all: all.into(),
                open: open.into(),
                by: by.into_iter().map(|(w, rs)| (w, rs.into())).collect(),
            })
            .collect::<Vec<_>>();
        (!at.is_empty()).then(|| Pins {
            free: free.into(),
            at,
        })
    }

    /// The lists of shapes that may hold the member whose components are `xs`: the free
    /// shapes, and at each place pinned, the shorter of those filed under the first variable
    /// of the member's component there that is neither rigid nor a function, where it has one,
    /// and those `open` there, where the component holds a scalar value; all those pinned there
    /// where neither applies. The lists are apart, as each shape is pinned at one place at most.
    ///
    /// Proof that a shape left out does not hold the member: it is pinned at `j` by `v`, of
    /// ceiling `c`, and the member's component `x` there has (a) a variable `w`, neither rigid
    /// nor a function, that is neither `v` nor in `c`, or (b) a scalar value, the piece
    /// `Set(s)` with `s` not empty, while `c` holds only variables. [`Comparing::rows`] and
    /// [`Comparing::shape_in`] hold the member only if each component is held, by
    /// [`Comparing::sub_by_shape`] at a site inside the shape ([`Site::In`]), and that holds
    /// `x` only if [`accepts`] holds each piece of `x`, `Var(w)` or `Set(s)` among them. In
    /// [`accepts`] with `t` the variable `v` alone: `t` is not the unknown; `ok` is false, in
    /// (a) as `w` is no function, `t.vars` does not hold `w`, and `w` is not rigid, in (b) as
    /// `t.set` is empty, so it holds no `s` not empty, and `v` is not rigid; the one variable
    /// of `t` is `v`, bindable, and `admits` refuses it, as [`may_be_within`] is false: in (a)
    /// for `Var(w)` in `c` (`c` is not the unknown and has no rigid or function variable, `w`
    /// is neither and is not in `c`), in (b) for `Set(s)` in `c` (`s` is not within the empty
    /// `c.set`, and `c` has no tuples or functions); and at a site inside a shape nothing else
    /// is bound. So the piece is not held, whatever the bindings so far. Rigidity does not
    /// change while a name lives: the names made rigid or functions are new ones, forgotten
    /// with their scope ([`Cx::forget`]).
    fn lists(&self, xs: &[&Ty], cx: &Cx) -> Vec<Rc<[usize]>> {
        let special = |w: &Arc<str>| cx.rigid.contains_key(w) || cx.fns.contains_key(w);
        let mut out = vec![self.free.clone()];
        for p in &self.at {
            let x = xs[p.place];
            let by_var = (x.vars.iter().find(|w| !special(w)))
                .map(|w| p.by.get(w).cloned().unwrap_or_else(|| Rc::from([])));
            let by_set = (!x.set.is_empty()).then(|| p.open.clone());
            out.push(match (by_var, by_set) {
                (Some(a), Some(b)) => {
                    if a.len() <= b.len() {
                        a
                    } else {
                        b
                    }
                }
                (Some(a), None) | (None, Some(a)) => a,
                (None, None) => p.all.clone(),
            });
        }
        out
    }
}

/// A type of one payload shape or one union of payload shapes of the atom `n`, for a message
/// about a comparison, printed in `scope` ([`Scope::text`]).
fn payload_text(n: &str, shapes: Vec<Shape>, scope: &mut Scope, cx: &Cx) -> String {
    scope.text(&payload_ty(n, shapes), cx)
}

/// The type of the atoms `n` with a payload of one of the shapes `shapes`.
fn payload_ty(n: &str, shapes: Vec<Shape>) -> Ty {
    let mut t = Ty::set(KType::atom_with(n, &KType::top()));
    t.payloads.insert(n.into(), Some(shapes));
    t
}

/// Why two members, `first` and `second`, of a union were refused ([`Comparing::search`]): each
/// may be held by a later one of the shapes `bucket`, which `apart` describes
/// ([`Choices::apart`]), and the checker looks through them for one of the two only. `own`
/// is the shape of its own [`own_shape`] gives `first`, when there is one. `given` says where
/// the variables the texts name are bound ([`Scope::given_text`]).
fn unchosen_text(
    what: &str,
    first: &str,
    second: &str,
    bucket: &str,
    apart: &str,
    own: Option<(Option<String>, String)>,
    given: &str,
) -> String {
    let own = match own {
        // A shape that files `first` under a key of its own is the first shape of its bucket,
        // so only `second` searches past a first shape, and the comparison is decided.
        Some((Some(place), shape)) => format!(
            "give {first} a shape of its own, written just before the shape that should hold \
             it and the same as that shape except at {place}: `{shape}`, with that shape's \
             other components in place of each `…`; or "
        ),
        // A shape of one component has no other components, so it is written whole.
        Some((None, shape)) => format!(
            "give {first} a shape of its own, written just before the shape that should hold \
             it: `{shape}`; or "
        ),
        None => String::new(),
    };
    format!(
        "the {what} {first} and {second} may each be held by one of the shapes {bucket}, which \
         {apart}, and neither is held by the first of those shapes; which shape \
         holds each decides what the type variables are bound to, and the checker looks \
         through those shapes for one of the two only{given}; to repair it, {own}test the value \
         with `is` first, so that each test meets one of the two"
    )
}

/// A shape of its own for the member whose components are `first`, for a repair: the place of
/// the first component where `first` has a class ([`class`]) that `second` does not have
/// there, and the shape with `first`'s component there and `…` elsewhere, written by `write`
/// from its components, the component printed by `text`. Filed under that key, the shape
/// holds `first` and not `second`. The place is None when `first` has one component, as the
/// shape is then that component whole. None when no component tells the two apart so, or
/// when `bound` says the type the shape is written into does not hold each type variable of
/// the component: no signature binds it there.
fn own_shape(
    first: &[&Ty],
    second: &[&Ty],
    items: usize,
    names: &[&Arc<str>],
    bound: impl FnOnce(&Ty) -> bool,
    text: impl FnOnce(&Ty) -> String,
    write: impl FnOnce(String) -> String,
) -> Option<(Option<String>, String)> {
    let key = |c: &Ty| class(c).map(|(k, point)| point.map_or(k, ShapeKey::Point));
    let j = (0..first.len()).find(|&j| key(first[j]).is_some_and(|k| key(second[j]) != Some(k)))?;
    if !bound(first[j]) {
        return None;
    }
    let at = text(first[j]);
    let comps: Vec<String> = (0..first.len())
        .map(|i| {
            let c = if i == j {
                at.clone()
            } else {
                "…".to_string()
            };
            match i.checked_sub(items) {
                None => c,
                Some(f) => format!("{}: {c}", names[f]),
            }
        })
        .collect();
    let place = (first.len() > 1).then(|| match j.checked_sub(items) {
        None => format!("component {}, where it is {at}", j + 1),
        Some(f) => format!("field {}, where it is {at}", names[f]),
    });
    Some((place, write(comps.join(", "))))
}

impl<'m, 's> Comparing<'m, 's> {
    /// [`fits_in`] in a frame of its own.
    fn fits(&'m self, s: Arc<Sig>, se: Env, q: Arc<Sig>, qe: Env) -> Deep<'m, bool> {
        self.stack
            .call(move || async move { fits_in(&s, &se, &q, &qe, self).await })
    }

    /// Whether the function `f` as written, with no reading, fits `g` as written ([`fits_in`]):
    /// compared once for each pair in the innermost comparison of function types open now, the
    /// verdict kept in [`Cx::fitted_written`] with why it was refused, as [`Self::fits_read`]
    /// keeps it. Why the kept verdict is the one a new comparison gives: [`fits_in`] of two
    /// signatures with empty readings reads, besides them, only `solve`, fixed for the
    /// comparison; the bounds of the rigid names and own variables the two hold (`rigid`,
    /// `own_bounds`), each fixed from when it is made until the comparison of function types
    /// that made it ends ([`Cx::forget`]), and `f` and `g`, made before the first comparison,
    /// hold none made after it, while the memo ends with the scope it was made in ([`Mark`]);
    /// the rows compared and the verdicts of `fitted`, kept answers of the same comparisons;
    /// and the refusal, which this compares alone ([`Self::begin_alone`]) and gives again.
    /// `why` is read only by the outermost [`fits_in`], which is not one of these.
    async fn fits_written(&'m self, f: &Arc<Sig>, g: &Arc<Sig>) -> bool {
        let key = (Arc::as_ptr(f) as usize, Arc::as_ptr(g) as usize);
        let kept = self
            .cx
            .borrow()
            .fitted_written
            .get(&key)
            .map(|e| e.2.clone());
        if let Some((ok, why)) = kept {
            if let Some(why) = why {
                self.refuse(|| why);
            }
            return ok;
        }
        let before = self.begin_alone();
        let ok = self
            .fits(f.clone(), Env::new(), g.clone(), Env::new())
            .await;
        let why = self.end_alone(before);
        let entry = (f.clone(), g.clone(), (ok, why.clone()));
        self.cx.borrow_mut().fitted_written.insert(key, entry);
        if let Some(why) = why {
            self.refuse(|| why);
        }
        ok
    }

    /// Whether the function read as the variable `v`, `s` read by `se`, fits the one read as
    /// `w`, if `w` is one ([`fits_in`]): compared once for each pair of names, the verdict kept
    /// in `fitted`. The verdict depends on the two signatures, their readings, the bounds of
    /// the rigid variables those readings name, made before `v` and `w` and kept while they
    /// are, and `solve`, fixed for the comparison; `why` is read only by the outermost
    /// [`fits_in`], which is not one of these. A name is never made again in one state, and
    /// [`Comparing::diff`] sets this memo aside with the names, so a kept verdict is never read
    /// for other functions. The names are keys by identity: each is one function as read.
    async fn fits_read(&'m self, v: &Arc<str>, s: &Arc<Sig>, se: &Env, w: &Arc<str>) -> bool {
        let key = (v.clone(), w.clone());
        let (q, qe) = {
            let cx = self.cx.borrow();
            if let Some((ok, why)) = cx.fitted.get(&key) {
                let (ok, why) = (*ok, why.clone());
                drop(cx);
                if let Some(why) = why {
                    self.refuse(|| why);
                }
                return ok;
            }
            match cx.fns.get(w) {
                Some(f) => f.clone(),
                None => return false,
            }
        };
        if alone_in_any_scope(s) && alone_in_any_scope(&q) {
            return self.fits_alone(s, q).await;
        }
        // Compared alone, so the verdict kept, with its refusal, is the same whatever was
        // refused before it, and is given again with that refusal ([`Self::begin_alone`]).
        let before = self.begin_alone();
        let ok = self.fits(s.clone(), se.clone(), q, qe).await;
        let why = self.end_alone(before);
        self.cx.borrow_mut().fitted.insert(key, (ok, why.clone()));
        if let Some(why) = why {
            self.refuse(|| why);
        }
        ok
    }

    /// Whether the function `s` fits the function `q`, both holding only their own variables
    /// and no class variable ([`alone_in_any_scope`]): compared once for each pair of
    /// signatures, by [`fits_in`] in a state of its own, as [`fits_sig_with`] compares two
    /// signatures, and the verdict kept in [`Cx::fitted_alone`] with why it was refused, if it
    /// was, which is given again each time, as [`Self::fits_read`] gives its kept refusal.
    ///
    /// Proof that the verdict is the one for the two functions wherever they are met. (1) The
    /// state of its own holds only `solve`, the same for the whole comparison, and the count of
    /// names made, so that no name made before is made again; nothing of the comparisons
    /// around is read. (2) Those comparisons could matter only through variables `s` and `q`
    /// hold: [`Cx::open`] reads each own variable of a signature it opens by a reading it writes
    /// into the environment there (a mask, a rigid name, a new name, or the name itself with
    /// the outer reading dropped), before any type of the signature is read, and every variable
    /// a signature of either nest holds outside functions is its own, so no reading of a scope
    /// around is ever looked up, and neither are the rigid bounds, own bounds or names kept
    /// there (`rigid`, `own_bounds`, `owned`). The other state [`fits_in`] reads (`wide`,
    /// `free`, `bind_none`, `witnessed`, `q_arrows`, `within_q`, `compared`) it sets for itself
    /// and gives back; the memos `fitted` and `fitted_written` start empty in the state of its
    /// own and are dropped with it, so none of their names is read outside it. The rows read
    /// once for the whole comparison and their names (`kept_rows`, `kept_read`,
    /// `kept_compared`, `fns`, `closed`) are carried into the state of its own and back
    /// (PERF-types-shared-row-bench-2ec6b9418), which changes no verdict: (a) the comparison
    /// inside looks up `fns` and `closed` only by the variables of the types it reads, and
    /// `s` and `q` as written hold only names a program writes, with no quote in them, so of
    /// the names carried in it meets only those of the kept rows it reads; the two reads of
    /// the whole of `fns` give the same answer with names it never meets ([`closed_binds`]
    /// binds only variables it meets, so its fast path on an empty `fns` answers as its walk
    /// would; [`may_be_within`] tests membership); (b) a kept row reads alike in every state
    /// but for the names of its functions, each kept with the empty environment (the proof
    /// at [`Cx::read`]); (c) a verdict of `kept_compared` is that of two rows with no variable
    /// at any depth compared alone ([`Self::kept_rows_in`]), the same in every state, as
    /// [`Cx::kept_compared`] is already kept across the comparisons of function types nested
    /// in each other. The names made in the state of its own are dropped with it, as before,
    /// and the count is carried, so no name is made twice. What
    /// differs is the new names some own variables are read under where a scope around owns
    /// the same name, a renaming of the variables `s` and `q` bind, which sec:type_resolution's
    /// rule 4 gives no meaning (each signature binds its own). The one read of the
    /// environments before [`Cx::open`], [`read_alike`] for a signature with needs, reads the
    /// readings around of names the signature binds itself; in the state of its own it finds
    /// them alike, so two such signatures are compared as written, where a scope around that
    /// read one of those names apart on the two sides refused a signature against itself.
    /// (3) `solve` answers for class variables, and neither signature holds one at any depth,
    /// so it gives nothing in either state. (4) The verdict is kept with the refusal made inside the attempt, read as
    /// [`Self::begin_alone`] reads it, so a kept verdict is given with the same refusal, and
    /// the two signatures are kept with it, so their addresses name them while it lives. So the
    /// verdict kept is that of [`fits_in`] on `s` and `q` compared alone, the same each time.
    ///
    /// Complexity tradeoff: naive version, as before, each comparison read under the names of
    /// the scope around and kept by those names ([`Cx::fitted`]): a parameter of function type
    /// is compared in both directions, by [`cover`] (`q`'s within `s`'s) and by [`permitted`]
    /// (`s`'s within `q`'s), each opening the pair one level down under new names, so the
    /// level one down is compared twice, the level k down 2^k times, and a nest n deep
    /// 2^(n+1) - 1 times in all (measured: 7, 15, 31, 63, 127 comparisons at depths 2 to 6).
    /// Used: the verdict by the pair of signatures, so 2n + 1 comparisons for the nest, each
    /// costing its own level. Tradeoff: one entry per pair met, held until the outermost
    /// comparison ends, and a function that holds a variable of a scope around it (a curried
    /// `(x: T) -> (y: T) -> T`) is still kept by names only, and a nest of such functions in
    /// parameters is still compared a number of times exponential in its depth; row
    /// FAIL-types-fn-outer-variable-nest.
    async fn fits_alone(&'m self, s: &Arc<Sig>, q: Arc<Sig>) -> bool {
        let key = (Arc::as_ptr(s), Arc::as_ptr(&q));
        let kept = (self.cx.borrow().fitted_alone.get(&key)).map(|(_, _, f)| f.clone());
        let (ok, why) = match kept {
            Some(f) => f,
            None => {
                let mut open = std::mem::take(&mut *self.cx.borrow_mut());
                *self.cx.borrow_mut() = Cx {
                    solve: open.solve,
                    count: open.count,
                    fitted_alone: std::mem::take(&mut open.fitted_alone),
                    kept_rows: std::mem::take(&mut open.kept_rows),
                    kept_read: std::mem::take(&mut open.kept_read),
                    kept_compared: std::mem::take(&mut open.kept_compared),
                    fns: std::mem::take(&mut open.fns),
                    closed: std::mem::take(&mut open.closed),
                    ..Cx::default()
                };
                let ok = self
                    .fits(s.clone(), Env::new(), q.clone(), Env::new())
                    .await;
                let mut inner = std::mem::replace(&mut *self.cx.borrow_mut(), open);
                // A name made in the state of its own and not forgotten there is dropped
                // with it, as before; the names kept for the whole comparison stay.
                for w in &inner.made {
                    inner.fns.remove(w);
                    inner.closed.remove(w);
                }
                let why = inner.unchosen;
                let mut cx = self.cx.borrow_mut();
                cx.count = inner.count;
                cx.fitted_alone = inner.fitted_alone;
                cx.kept_rows = inner.kept_rows;
                cx.kept_read = inner.kept_read;
                cx.kept_compared = inner.kept_compared;
                cx.fns = inner.fns;
                cx.closed = inner.closed;
                cx.fitted_alone
                    .insert(key, (s.clone(), q, (ok, why.clone())));
                (ok, why)
            }
        };
        if let Some(why) = why {
            self.refuse(|| why);
        }
        ok
    }

    /// Whether each component of `cs` is in the one of `ds` at its place
    /// ([`Comparing::sub_by_shape`]), in order, stopping at the first that is not, in a frame
    /// of its own: with `b` and what it binds. Compared once for each binding the pair is met
    /// with ([`Cx::compared`]).
    fn rows(&'m self, cs: Row, ds: Row, mut b: Binds) -> Deep<'m, (bool, Binds)> {
        self.stack.call(move || async move {
            let key = Compared::new(cs.node(), ds.node(), &b, self.cx.borrow().bind_none);
            if let Some(kept) = self.recall(&key) {
                return kept;
            }
            let mut ok = true;
            for (j, (c, d)) in cs.iter().zip(&ds).enumerate() {
                if !self
                    .sub_by_shape(c, d, &mut b, Site::In(Holder::Row(&ds), j))
                    .await
                {
                    ok = false;
                    break;
                }
            }
            self.keep(key, ok, &b);
            (ok, b)
        })
    }

    /// The answer kept for the comparison `key` ([`Cx::compared`]), with the binding it gave;
    /// none once the comparison is refused, as a comparison then answers at once
    /// ([`Comparing::search`]), and the kept answer was found with nothing refused.
    fn recall(&self, key: &Compared) -> Option<(bool, Binds)> {
        let cx = self.cx.borrow();
        if cx.unchosen.is_some() {
            return None;
        }
        cx.compared.get(key).cloned()
    }

    /// Keeps the answer `ok` and the binding `b` of the comparison `key`, unless it was refused
    /// ([`Self::refuse`]): a refused comparison's answer is not its own but the refusal's.
    /// Kept, a false found after a refusal was read by a later attempt with nothing refused,
    /// and a function that fits was found not to fit
    /// (`l01_26_type_resolution::deep_ops::an_answer_found_after_a_refusal_is_not_read_by_a_later_attempt`).
    ///
    /// An answer true is kept under `b` too, the binding it gave (FAIL-types-sub-level-
    /// variables): a pair shared by both places of `#a(u, u)` is met the second time under the
    /// binding the first comparison of it gave, which binds the variables it holds, so keyed
    /// only by the binding in force before, it missed, and so did every pair below it, though
    /// each gives the same: O(n) comparisons again at each of n levels, O(n²) in all and an
    /// O(n) comparison of the bindings on each hash match, `T(8n)/T(n)` = 109 measured. Kept
    /// under `b`, the second meeting is one lookup. Why the answer under `b` is `(true, b)`:
    /// the comparison reads the binding only in [`accepts`], where the parts of the type that
    /// are not variables hold a piece or not whatever is bound (they read it only through the
    /// comparisons below, which by induction give the same), and a piece no other part holds
    /// is united with the first variable that admits it. Under `b`, each variable the first
    /// comparison bound holds the pieces it was bound to; the one chosen admits its piece
    /// again (the same bound and ceiling, a piece of carriers within the bound), one passed
    /// over does not (a piece outside the ceiling or the bound is outside them under `b`
    /// too), and [`Binds::unite`] of a piece already held is the same type ([`Ty::union`] joins
    /// the kernel sets and drops a shape, a function or a variable it holds). So the same
    /// shapes are chosen in the same order and `b` comes back unchanged. Only an answer found
    /// with nothing refused is kept, so a refusal, which may end the search of a member
    /// early, never stands behind it. The other fix weighed: keying each pair by the binding
    /// restricted to the variables the two nodes hold, which needs the set of those variables
    /// kept with each shape, O(size) memory a node and a restriction at each lookup, where
    /// this costs a second entry for each answer true, O(1) to make (a persistent map is
    /// copied by its root).
    fn keep(&self, key: Compared, ok: bool, b: &Binds) {
        // Assumption, not proved (ASSUME-documented): the comparison `key` met again under `b`, the
        // binding its true answer gave, gives `(true, b)` again, so the second entry may be read with
        // no comparison. The argument in the doc above covers pieces bound through `accepts` at
        // `Site::In`. It is not shown for the `Site::Other` fallback, which binds the first bindable
        // variable without calling `admits`, so under `b` that variable may hold a piece its bound
        // or ceiling would refuse. Evidence:
        // `deep_ops::shared_payloads_with_a_variable_a_level_bind_each_once` (n from 1 to 6),
        // `an_answer_found_after_a_refusal_is_not_read_by_a_later_attempt`, benchmark 8.00x. If
        // false, a recalled `true` stands where the comparison would give false: unsound.
        let mut cx = self.cx.borrow_mut();
        if cx.unchosen.is_none() {
            if ok {
                let out = Compared::new(key.left, key.right, b, key.as_is);
                cx.compared.insert(out, (true, b.clone()));
            }
            cx.compared.insert(key, (ok, b.clone()));
        }
    }

    /// [`Ty::sub`] of `t` and `other` inside the comparisons of function types the state holds.
    async fn sub_in(&'m self, t: &Ty, other: &Ty, binds: &mut Binds) -> bool {
        self.sub_near(t, other, None, binds).await
    }

    /// Whether `t` is within `other` where each is one tuple shape and nothing else, of rows
    /// [`Cx::read`] read and kept for the whole comparison ([`Cx::kept_read`]) and of one
    /// length: each component within the one of `other` at its place ([`Comparing::sub_in`]),
    /// compared once for each pair of rows in the comparison, the verdict kept in
    /// [`Cx::kept_compared`] with why it was refused, if it was, and given again with it, as
    /// [`Comparing::fits_read`] keeps its verdicts. Nothing where the two are not such rows, or
    /// where the components give no and a component of `t` is empty ([`Ty::is_empty`]): the
    /// comparison then goes on as before.
    ///
    /// Proof that the verdict is the one [`Comparing::sub_near`] gives, and the same each time
    /// the pair is met. A yes: a tuple whose components are each within those of another is
    /// within it. A no: each component of `t` holds a value ([`Ty::is_empty`] is false, which
    /// reads a row that lists a value at each place as holding one, as [`Ty::of_row`] makes a
    /// row with no value the empty type and as [`Comparing::rows`] reads a row when it gives
    /// no at its first component found not within), so a component `c` not within `d` puts
    /// the tuples with a value of `c` outside `d` beside values of the others outside `other`.
    /// The same each time: a row of [`Cx::kept_read`] holds no variable but the names of its
    /// functions, each made outside every scope ([`Cx::fresh_kept`]) and kept with the empty
    /// environment for the whole comparison, and not one a binding may bind (each is a name of
    /// [`Cx::fns`]). So the comparison of its components reads no variable of `binds`, `rigid`
    /// or the own variables, and its functions are compared by their names in [`Cx::fitted`],
    /// kept for the whole comparison, each read from its signature, which holds no variable,
    /// and `solve`, fixed for the comparison. It is compared alone ([`Self::begin_alone`]), so
    /// the verdict kept does not depend on what was refused before it.
    ///
    /// Complexity tradeoff (PERF-types-shared-row-each-level): naive version, as before, each
    /// comparison of such rows walked, rebuilt and formed both sides outside their functions
    /// ([`Comparing::closed_form`]): a row of n functions shared by the results of n function
    /// types nested in each other was compared again at each level, O(n^2) (52.7 times at
    /// 8n). Used: one comparison of each pair of rows, a lookup each time after, so each row
    /// pair costs its width once. Given up: rows with a payload not fixed, or a variable at
    /// any depth, go the old way; a tuple within a union of tuples, none holding it alone, is
    /// not this case (one shape on each side).
    async fn kept_rows_in(&'m self, t: &Ty, other: &Ty, binds: &Binds) -> Option<bool> {
        let one = |t: &Ty| {
            let only = t.set.lists_nothing()
                && t.fns.is_empty()
                && t.vars.is_empty()
                && !t.dynamic
                && t.payloads.is_empty()
                && t.tuples.len() == 1;
            only.then(|| t.tuples[0].clone())
        };
        let (cs, ds) = (one(t)?, one(other)?);
        let key = (cs.node(), ds.node());
        {
            let cx = self.cx.borrow();
            let kept = |r: &Row| cx.kept_read.contains(&r.node());
            if !kept(&cs) || !kept(&ds) || cs.len() != ds.len() {
                return None;
            }
            if let Some((ok, why)) = cx.kept_compared.get(&key).cloned() {
                drop(cx);
                if let Some(why) = why {
                    self.refuse(|| why);
                }
                return Some(ok);
            }
        }
        let before = self.begin_alone();
        let ok = self.components_in(cs.clone(), ds, binds.clone()).await;
        let why = self.end_alone(before);
        if !ok && cs.iter().any(Ty::is_empty) {
            return None;
        }
        self.cx
            .borrow_mut()
            .kept_compared
            .insert(key, (ok, why.clone()));
        if let Some(why) = why {
            self.refuse(|| why);
        }
        Some(ok)
    }

    /// Whether each component of `cs` is within the one of `ds` at its place
    /// ([`Comparing::sub_in`]), stopping at the first that is not, in a frame of its own.
    fn components_in(&'m self, cs: Row, ds: Row, mut b: Binds) -> Deep<'m, bool> {
        self.stack.call(move || async move {
            for (c, d) in cs.iter().zip(&ds) {
                if !self.sub_in(c, d, &mut b).await {
                    return false;
                }
            }
            true
        })
    }

    /// [`Comparing::sub_in`]. When `t` is one tuple, `near` may give the part of `other` that
    /// may share a value with it ([`near_pairs`]), what is read once of `other` ([`Whole`]) and
    /// its shapes filed: the kernel then decides on that part ([`Comparing::near_form`]), and
    /// the rule of one shape reads `other` through the shapes filed.
    async fn sub_near(
        &'m self,
        t: &Ty,
        other: &Ty,
        near: Option<(&Ty, &Whole, &Arc<Filed>)>,
        binds: &mut Binds,
    ) -> bool {
        if near.is_none()
            && let Some(ok) = self.kept_rows_in(t, other, binds).await
        {
            return ok;
        }
        // The scalars, atoms with their payloads, kind-wide part and tuples of `t` are decided
        // together, once, by the kernel on their normal forms ([`Comparing::by_form`]), which
        // sees shapes that hold a piece only together. Trying each shape of `other` in turn
        // cost every shape times the components; the kernel splits the components once. Where
        // the normal form is not made (a variable, which a shape of `other` may bind) or the
        // kernel refused, each piece is tried by the rule of one shape, which is sound.
        let mut form: Option<Option<bool>> = None;
        let mut search = Search::new(Site::Other);
        if let Some((_, _, filed)) = near {
            search.filed = Some(filed.clone());
        }
        for p in t.pieces() {
            // A set piece with no kind-wide part, of a `t` that lists no payload, is decided by
            // the set alone ([`accepts`]): building both sides' kernel types for it cost each
            // comparison of a large set its size again, with a value built when it fails.
            let plain = |s: &KType| t.payloads.is_empty() && (s & &wide()).is_empty();
            let decided = match &p {
                Piece::Set(s) if plain(s) => None,
                Piece::Set(_) | Piece::Tuple(_) => match form {
                    Some(d) => d,
                    None => {
                        let d = match near {
                            Some((near, whole, _)) => self.near_form(t, near, whole).await,
                            None => self.by_form(t, other, None).await,
                        };
                        let d = match d {
                            Some(d) => Some(d),
                            None => self.closed_form(t, other).await,
                        };
                        *form.insert(d)
                    }
                },
                _ => None,
            };
            let ok = match decided {
                Some(ok) => ok,
                None => accepts(other, &p, t, binds, &mut search, self).await,
            };
            if !ok {
                return false;
            }
        }
        true
    }

    /// Whether the scalars, atoms with their payloads, kind-wide part and tuples of `t` are all
    /// in `other`, decided by the kernel on the normal forms of the two sides ([`Forms`]), or
    /// nothing where the forms are not made or the kernel refused. False, with no pair tried,
    /// for the class [`Forms::tie`] names. `named` gives the variables the functions stand for,
    /// where they were put in place of them ([`Comparing::closed_form`]).
    async fn by_form(&'m self, t: &Ty, other: &Ty, named: Option<&Named>) -> Option<bool> {
        if other.dynamic {
            return Some(true);
        }
        // A variable of `other` may be bound to a piece, which the forms do not do.
        if !other.vars.is_empty() {
            return None;
        }
        let verdict = match (t.exact_data(), other.exact_data()) {
            (Some(a), Some(b)) => a.subtype_verdict(&b),
            _ => {
                let right = Right::of(other)?;
                self.form_verdict(t, other, &right.fns, &right, named)
                    .await?
            }
        };
        held(verdict)
    }

    /// [`Comparing::by_form`] of `t` and `other` with each variable outside their functions
    /// that stands for a function ([`Cx::fns`]) replaced: by that function where it reads alike
    /// in every environment ([`held_reading`] empty, kept in [`Cx::closed`] by [`Cx::read`]),
    /// else by a token of its own ([`fn_token`]) that [`Comparing::fits_named`] compares by the
    /// variable; nothing where there is no such variable.
    ///
    /// Proof that a yes is sound (FAIL-closed-form-outer-variable). Write `S(x)` for the set of
    /// functions a variable `x` of [`Cx::fns`] stands for: its signature read by its
    /// environment. Put back, each function at a place of the forms is either a function `s`
    /// of a variable in [`Cx::closed`], or the token of a variable `x` not in it; write `S(f)`
    /// for `S(x)` of the variable `named` keeps for `f`. For a closed `s`, `S(s)` is `s` read
    /// by the empty environment, since its reading names none of the variables it holds
    /// ([`held_reading`]); so two variables put back as one equal `s` stand for one
    /// set, and a token, named by a variable whose name holds a quote, which no name a program
    /// writes does, equals no written function and no other token. [`Forms`] reads of a
    /// function only its equality and hash: each function of `t` is a mark `i` of its own, and
    /// each function `g` of `other` at a place holds the marks of the functions of `t` there
    /// that equal it or that fit it by [`Comparing::fits_named`]. Each of those gives yes only
    /// where `S(f)` is within `S(g)`: [`Comparing::fits_written`] compares two closed
    /// functions as written, which reads each by the empty environment, and
    /// [`Comparing::fits_read`] compares the two variables as each is read, as [`accepts`]
    /// does. Let `γ` take a form to values, a mark `i` to `S(f)` of its function and every
    /// other part to itself. The form of `t` is made of the marks and parts with no function by
    /// union, tuples and payloads, and a difference only of a part that holds no function (a
    /// row or shape holding a function has no exact kernel type, [`RowData::exact`]), so `γ`
    /// of it is `t`. The form of `other` is made the same way, each `g` replaced by its marks,
    /// and `γ` of those is within `S(g)`, so `γ` of it is within `other`: union, tuples and
    /// payloads keep the order of their parts, and a difference whose part taken away holds no
    /// mark is `γ` of the first part without that part. The kernel takes distinct marks to
    /// share no value; where two sets `S` share some, a form of tuples and unions within
    /// another with the marks apart is still within it with each mark read as its set, since
    /// each value of the first is in the set of some tuple of marks of the first, a tuple of
    /// the second too, whose sets hold that value. So `form(t)` within `form(other)` gives `t`
    /// within `other`. What is given up: a function of `t` within the union of two functions
    /// of `other` and within neither alone is found not to fit, as at a place of one shape.
    ///
    /// Why (TEST-nested-marks-struct-parts): inside a comparison of function types, each
    /// function that a parameter or result holds is read as a variable, so the forms were not
    /// made, and each piece was tried by the rule of one shape ([`accepts`]), which finds a set
    /// piece only in the other side's set, not in its shapes: `int -> (#_, 1) \ (#a, 1)` did
    /// not fit `int -> (#_, 1) | (1, int -> int)`, a definite no, though `(#_, 1) \ (#a, 1)` is
    /// within `(#_, 1)`. A function that reads alike in every environment, compared as
    /// written, as [`Comparing::form_verdict`] compares its functions, gives what
    /// [`Comparing::fits_read`] gives for the variable read in its place. Since
    /// TEST-nested-marks-fn-vars that covers a function holding variables of its own only, as
    /// `(T -> T for T in int)` beside a set of every atom
    /// (`a_set_of_every_atom_beside_a_function_holding_a_variable_is_compared_as_a_set`), not
    /// only one with no variable; until FAIL-closed-form-outer-variable one holding a variable
    /// of the function type around it, as `T -> T` in `T -> (D | (1, T -> T)) for T in int`,
    /// was left as its variable, so its comparison fell to the rule of one shape and the set
    /// `D` was not found within `(#_, 1)`. Such a function is now a token.
    ///
    /// Complexity tradeoff: no walk at all while no function is read ([`Cx::fns`] is empty),
    /// as in every comparison outside function types; else one walk of
    /// each side outside its functions, entering only the rows and payloads that hold a
    /// variable, that stops at the first variable which leaves [`Comparing::by_form`] with no
    /// form ([`closed_binds`]), a lookup of each variable found, and a rebuild of the part
    /// holding them ([`Ty::replace_outside`]). The naive walk, every variable outside the
    /// functions of both sides collected first, O(size) at each comparison whose forms were
    /// not made, cost O(n^2) on a type of n rows compared at each of its n levels
    /// (FAIL-closed-form-shared-rows-scaling: `rows_shared_on_many_paths_scale_in_a_function`,
    /// over 300 s at n 25600 where 3.4 s before). Its own cost, a walk of each side outside
    /// its functions, is of the order of the [`Cx::read`] of those sides that made the
    /// variables, so it adds no order to the comparison (BENCH-closed-form-late-variable:
    /// `results_with_a_variable_late_beside_closed_functions_are_compared_in_linear_time`,
    /// 8.2 times at 8n). A nest of n function types, each result holding the next beside a
    /// shared row of n functions, cost O(n^2), 52.9 times at 8n, and 53.0 times with this
    /// step left out: each of the n comparisons read and compared the shared row again.
    /// Since PERF-types-shared-row-each-level such a row, holding no variable, is read once
    /// ([`Cx::kept_rows`]) and its tuples are compared by [`Comparing::kept_rows_in`] before
    /// this step is reached: 7.7 times at 8n. A token costs O(1) to make and is compared by
    /// [`Comparing::fits_read`], whose verdict is kept by the pair of names, as the rule of one
    /// shape compares it.
    async fn closed_form(&'m self, t: &Ty, other: &Ty) -> Option<bool> {
        let (binds, named) = closed_binds(&self.cx.borrow(), t, other)?;
        let (t, other) = (t.replace_outside(&binds), other.replace_outside(&binds));
        self.by_form(&t, &other, Some(&named)).await
    }

    /// Whether the function `f` fits `g`, in the forms of [`Comparing::form_verdict`]: by the
    /// variables they stand for ([`Comparing::fits_read`]) where either is the token of a
    /// variable that does not read alike in every environment (`named`, [`closed_binds`]), and
    /// as written ([`Comparing::fits_written`]) otherwise; nothing where a token meets a
    /// function that stands for no variable, which [`Cx::read`] leaves none of.
    async fn fits_named(
        &'m self,
        f: &Arc<Sig>,
        g: &Arc<Sig>,
        named: Option<&Named>,
    ) -> Option<bool> {
        let (vf, vg) = match named {
            Some(n) => (n.get(f), n.get(g)),
            None => (None, None),
        };
        let token = |v: Option<&(Arc<str>, bool)>| v.is_some_and(|v| !v.1);
        if !token(vf) && !token(vg) {
            return Some(self.fits_written(f, g).await);
        }
        let ((v, _), (w, _)) = (vf?, vg?);
        let (s, se) = self.cx.borrow().fns.get(v)?.clone();
        Some(self.fits_read(v, &s, &se, w).await)
    }

    /// [`Comparing::by_form`] of the tuple `t` and the type `whole` reads, from `near`: `whole`
    /// with only its tuples that may share a value with `t` ([`near_pairs`]). The kernel holds
    /// `t` in `near` exactly when it holds it in `whole`; which way is taken, and which
    /// functions are compared, is read from `whole`, as [`Comparing::by_form`] reads it.
    async fn near_form(&'m self, t: &Ty, near: &Ty, whole: &Whole) -> Option<bool> {
        if near.dynamic {
            return Some(true);
        }
        if !near.vars.is_empty() {
            return None;
        }
        let verdict = match (t.exact_data(), &whole.rest) {
            (Some(a), Some(rest)) => {
                let rows = near.tuples.iter().map(|r| r.0.exact.clone());
                let rows = rows.collect::<Option<Vec<_>>>()?;
                a.subtype_verdict(&KType::union_all(std::iter::once(rest.clone()).chain(rows)))
            }
            _ => {
                let right = whole.right.as_ref()?;
                let near_fns = Forms::fns(near, false, &mut HashSet::new())?;
                self.form_verdict(t, near, &near_fns, right, None).await?
            }
        };
        held(verdict)
    }

    /// The kernel's verdict on the normal forms of `t` and `other` ([`Forms`]), or nothing
    /// where they are not made; [`Verdict::Inhabited`], with no pair tried, for the class
    /// [`Forms::tied`] names. `other` is the type compared with, or the part of it that may
    /// share a value with `t`, whose functions at each place are `fns`; `whole` reads the type
    /// compared with. Two functions are compared by [`Comparing::fits_named`], with `named`.
    async fn form_verdict(
        &'m self,
        t: &Ty,
        other: &Ty,
        fns: &PlaceFns,
        whole: &Right,
        named: Option<&Named>,
    ) -> Option<Verdict> {
        let mut forms = Forms::default();
        let left = Forms::fns(t, true, &mut forms.fields)?;
        forms.fields.extend(whole.fields.iter().cloned());
        let starred = left.starred(fns, &whole.fns);
        if forms.tied(&left, &whole.fns, &starred).is_some() {
            return Some(Verdict::Inhabited);
        }
        for f in left.all() {
            forms.id(f);
        }
        forms.number_marks();
        // At a spot where either side has one function, each function of `t` is compared with
        // each of `other`. Elsewhere each function of `t` not among those of `other` there is
        // compared with each of `other`: by [`Forms::tied`], one side has at most one. Either
        // way the pairs are as many as the functions. A function of `other` met at several
        // spots holds the functions of `t` it fits at any of them.
        //
        // Before (FAIL-types-tuple-subtype), a function of `t` equal to one of `other` at a
        // spot was compared with no other function there, so `(f, 1) <: (g, 1) | (f, 2)`, with
        // `f` fitting `g`, was false; where both sides have two or more functions it still is
        // not compared (it is skipped), and a false verdict is then checked again with every
        // skipped pair taken to fit ([`Merged`]): still false, it is a definite no; true, the
        // comparison is refused.
        //
        // Before (FAIL-types-equal-functions-subset-no), the refusal was read from the two
        // types alone (`Forms::loose`), only where some function of `other` at the spot equals
        // none of `t`'s, so where those of `other` were all among `t`'s the false verdict stood:
        // `(f, #a) | (g, #b) <: (g, #a) | (f, #b) | (g, #b)`, with `f` fitting `g`, was a
        // definite no, though it holds; and a false verdict that no skipped pair could change
        // was refused, though it is a definite no.
        //
        // Complexity tradeoff (COMPLEXITY.md F124): the skipped pairs are not compared. What
        // is given up: a comparison whose verdict a skipped pair could change is refused, with
        // the clause of [`Forms::tie`], though comparing the pairs could decide it. Why: the
        // skipped pairs are the product of the functions at the spot, `n^2` comparisons of
        // functions for a union of `n` shapes on each side, each with its own function there.
        // Structure: two or more functions on each side at one place, one of `t`'s equal to
        // one of `other`'s, the pairs of tuples that meet there more than the functions there
        // ([`PlaceFns::starred`]), and the verdict false only for want of a skipped pair.
        // Tests: `tests/steps/l01_23_groups_and_refusals/judgments.rs`,
        // `functions_at_one_place_are_refused_only_where_a_pairing_could_make_it_true`,
        // `equal_functions_on_the_right_all_held_on_the_left_are_no_definite_no`,
        // `random_unions_of_tuples_with_functions_agree_with_pairing_every_function`. Naive
        // version: every pair at the spot compared, O(n^2) comparisons of functions; used: the
        // pairs as many as the functions, and a second kernel verdict, on forms of the same
        // size, when the first is false and a pair was skipped. A complete solution would
        // order the functions at a place, as for [`Forms::tied`].
        //
        // Since FAIL-types-loose-pairing-decided, a spot where both sides have two or more
        // functions and the pairs of nodes that may share a value form stars
        // ([`PlaceFns::starred`]) has those pairs compared, as many as the functions, and none
        // skipped, so it is decided there: `(f, 1) | (h, 2) <: (g, 1) | (f, 2) | (h, 3)`, with
        // `f` fitting `g` and `h` fitting `f`, was refused. Since
        // FAIL-types-loose-pairing-non-star, so is a spot whose pairs of nodes that may share a
        // value are no more than its functions, though they form no stars:
        // `(f, 1) | (h, 1 | 2) <: (g, 1 | 2) | (f, 1 | 2) | (h, 3)` was refused.
        let mut skipped = Merged::default();
        for (spot, fs) in left.spots(&whole.fns) {
            if let Some(pairs) = starred.get(&spot) {
                for (f, g) in pairs {
                    let fit = f == g || self.fits_named(f, g, named).await?;
                    if fit {
                        let i = forms.id(f);
                        forms.hold(g, i);
                    }
                }
                continue;
            }
            let Some(gs) = fns.get(&spot) else { continue };
            let all = whole.fns.get(&spot).unwrap_or(gs);
            let every = fs.len() == 1 || gs.len() == 1;
            let compared: Vec<&Arc<Sig>> =
                fs.iter().filter(|f| every || !all.contains(*f)).collect();
            // Each function of `t` here not compared is skipped against every function of
            // `other` here but itself, of which there are one or more, as `gs` has two or more.
            if compared.len() < fs.len() {
                (skipped.left).extend(fs.iter().filter(|f| all.contains(*f)).map(|f| forms.ids[f]));
                skipped.right.extend(gs.iter().cloned());
            }
            for g in gs {
                let mut fit = Vec::new();
                if fs.contains(g) {
                    fit.push(forms.id(g));
                }
                for f in compared.iter().filter(|f| **f != g) {
                    if self.fits_named(f, g, named).await? {
                        fit.push(forms.id(f));
                    }
                }
                for i in fit {
                    forms.hold(g, i);
                }
            }
        }
        let a = forms.form(t, true)?;
        let b = forms.form(other, false)?;
        let verdict = a.subtype_verdict(&b);
        if !matches!(verdict, Verdict::Inhabited) || skipped.left.is_empty() {
            return Some(verdict);
        }
        // Assumption, not proved: the forms made below are the renaming `φ` of [`Merged`]
        // applied to the plain ones, at every kind of spot: a `_` of the other side, which
        // holds every mark, holds [`MERGED`] too; functions nested in payloads or tuples inside
        // tuples are renamed as those at the top; and the memo `cuts`, kept from the first
        // forms, is still right, since [`MERGED`] is among the marks in both, and so is `levels`,
        // since [`MERGED`] is among every function's marks in both. Evidence: the
        // random test `random_unions_of_tuples_with_functions_agree_with_pairing_every_function`
        // (3000 cases a run, seeds 1 to 8, no wrong yes and no wrong definite no; its types hold
        // functions at the top of a tuple only, with no `_` and no named fields), and the tests
        // of `l01_22`, `l01_23` and `l01_26`, unchanged.
        forms.made.clear();
        forms.merged = Some(skipped);
        let a = forms.form(t, true)?;
        let b = forms.form(other, false)?;
        if !matches!(a.subtype_verdict(&b), Verdict::Inhabited) {
            self.refuse(|| UNPAIRED.to_string());
        }
        Some(Verdict::Inhabited)
    }

    /// [`Self::diff`] on the explicit stack, for a difference inside a difference
    /// ([`Self::shape_rest`]): a payload nested 20,000 deep would otherwise take 20,000 native
    /// frames.
    fn diff_deep(&'m self, t: Ty, u: Ty, solve: Option<Solve<'s>>) -> Deep<'m, Ty> {
        self.stack
            .call(move || async move { self.diff(&t, &u, solve).await })
    }

    /// The rest of the payload shape `s` once the shapes `cut` are taken from it, as shapes,
    /// with the kernel type of each ([`Rest`]). `s` and `cut` have kernel types, so they have
    /// items and no fields, each item with a kernel type ([`ShapeData::exact`]), and
    /// [`near_pairs`] lists only shapes of as many items. The shapes are built item by item.
    /// At item i, below a prefix of items already fixed, the values of `s`'s item i are split
    /// by which shapes of `cut` (of those still holding the prefix) hold them at item i: the
    /// parts of a Venn diagram of those items. A part held by no shape of `cut` gives a shape,
    /// the prefix, the part and `s`'s items after i; a part held by some is carried on to item
    /// i + 1 with them, and at the last item nothing of it is left. This is the difference of
    /// products: for one shape of `cut`, `(A1, A2) \ (B1, B2)` is `(A1 \ B1, A2)` with
    /// `(A1 & B1, A2 \ B2)`, as before.
    ///
    /// Two reductions keep the shapes few. Of the shapes of `cut` holding a part, one whose
    /// items after i are each within those of another of them is dropped ([`Self::widest`]):
    /// what it would take from the rest, the other takes. Then parts held by the same shapes
    /// are joined into one, so a prefix goes on once for each set of shapes, not once for each
    /// part.
    ///
    /// Each part is made twice, as a [`Ty`] and as a kernel type, and every choice (a shape
    /// of `cut` that misses `s`, a part met or left, a shape dropped by [`Self::widest`]) is
    /// made on the kernel types: by kernel `&` and `-`, which are the meet and difference of
    /// the sets, by [`KType::is_empty`], whose yes is proved, and by [`KType::subtype`], whose
    /// yes is proved. Proof that the kernel types of the shapes left hold every value of the
    /// difference and no other (PROOF-diff-exact-skip): the parts at item i are disjoint and
    /// cover `s`'s item i. Each item of the prefix of a part held by the set H of shapes is
    /// within the items of each shape of H at its place. So a value of that part, followed by
    /// a tail t, is in some shape of `cut` exactly when t is in the items after i of a shape
    /// of H: a shape not in H was found to miss a part of the prefix, or dropped because its
    /// tail lies in the tail of a shape that is kept and holds the same prefix. A part is left
    /// out only where `is_empty` proves it empty, so none of its values is lost; at the last
    /// item a part held by some shape of H is in that shape, so all of it is taken. Hence a
    /// shape left holds only values of `s` outside `cut`, and together they hold all of them.
    /// A part that `is_empty` does not prove empty is kept, so a shape left may hold no value
    /// ([`Rest::held`] tells). Each [`Ty`] shape holds at least the values of its kernel type
    /// where [`Ty::meet`] and [`Ty::diff`] lose no value of the meet and the difference, their
    /// own promise; the choices above do not rest on it.
    ///
    /// Cost: before (FAIL-types-shape-rest-many-cuts) each shape of `cut` split every shape
    /// left that it met into up to w shapes, so k shapes of `cut` left up to w^k shapes, and
    /// k nested shapes `#a(0..j, …, 0..j)` with w items left C(k + w - 1, w - 1) shapes where
    /// w are enough (969 for w = 4, k = 16, measured); now they leave w. With k shapes of `cut`
    /// meeting the prefix and r parts at an item, the split costs O(k·r) meets and
    /// differences of items, and the reduction compares each held shape with the widest ones
    /// kept, O(k·a) for a kept, each comparison of two items done once ([`Self::widest`]).
    /// For one shape of `cut` this is the old O(w) operations and w shapes. Some inputs need
    /// w^k shapes in any answer kept as a union of shapes: for `cut` the k shapes
    /// `#a(B_j, …, B_j)` with B_j the numbers below 2^k with bit j set, each choice of one
    /// item lacking bit j for every j gives a value of the rest, w^k of them, and no shape
    /// holds two, since it would also hold a value whose items all have the bit at which the
    /// two choices differ; that answer is the one left here. For k shapes of `cut` in a chain,
    /// each meeting the next, the work grows about 8.4 times at 8 times k
    /// (`kinds::bench::the_difference_of_a_wide_payload_and_many_overlapping_cuts_scales`;
    /// 54 times before).
    async fn shape_rest(&'m self, s: &Shape, cut: &[Shape], solve: Option<Solve<'s>>) -> Rest {
        let w = s.items.len();
        let own: Vec<KType> = (s.items.iter().map(Ty::exact_kernel))
            .collect::<Option<_>>()
            .expect("the items of an exact shape have kernel types");
        // The shapes of `cut` as far as they meet `s`; one that misses `s` at an item is
        // dropped, as it takes nothing.
        let mut cuts: Vec<Vec<Item>> = Vec::with_capacity(cut.len());
        'cut: for c in cut {
            let mut met = Vec::with_capacity(w);
            for ((x, xk), y) in s.items.iter().zip(&own).zip(&c.items) {
                let yk = (y.exact_kernel()).expect("the items of an exact shape have kernel types");
                let mk = xk & &yk;
                if mk.is_empty() {
                    continue 'cut;
                }
                met.push((x.meet(y), mk));
            }
            cuts.push(met);
        }
        let mut within = HashMap::new();
        let mut rest = Rest::default();
        let mut work: Vec<(Vec<Item>, Vec<usize>)> = vec![(Vec::new(), (0..cuts.len()).collect())];
        while let Some((prefix, held)) = work.pop() {
            let i = prefix.len();
            if i == w {
                // Only for a shape of no items: each shape of `cut` met it, and one takes it.
                if held.is_empty() {
                    rest.push(prefix);
                }
                continue;
            }
            if i + 1 == w {
                // At the last item a part some shape of `held` holds is all taken, so only the
                // part held by none is left: `s`'s item less the union of their items.
                // Complexity tradeoff: naive version, the split by `parts` into the regions of
                // a Venn diagram of the k held items, which costs O(k log k) meets and
                // differences for few regions but one per region, up to 2^k regions for
                // overlapping items (the pigeonhole rows of
                // `kinds::a_payload_whose_tuple_item_needs_a_split_of_many_components_is_refused`
                // ran past 60 s); used, one union of k items and one difference.
                let uk = KType::union_all(held.iter().map(|&c| cuts[c][i].1.clone()));
                let rk = &own[i] - &uk;
                if !rk.is_empty() {
                    let u = Ty::union_all(held.iter().map(|&c| &cuts[c][i].0));
                    let r = self.diff_deep(s.items[i].clone(), u, solve).await;
                    let mut items = prefix;
                    items.push((r, rk));
                    rest.push(items);
                }
                continue;
            }
            let x = (s.items[i].clone(), own[i].clone());
            let parts = self.parts(&cuts, &held, i, x, solve).await;
            let mut joined: BTreeMap<Vec<usize>, Vec<Item>> = BTreeMap::new();
            for (r, h) in parts {
                let h = if h.is_empty() {
                    h
                } else {
                    Self::widest(&cuts, h, i + 1, &mut within)
                };
                joined.entry(h).or_default().push(r);
            }
            for (h, rs) in joined {
                let mut items = prefix.clone();
                let u = Ty::union_all(rs.iter().map(|r| &r.0));
                items.push((u, KType::union_all(rs.into_iter().map(|r| r.1))));
                if h.is_empty() {
                    let after = s.items[i + 1..].iter().cloned();
                    items.extend(after.zip(own[i + 1..].iter().cloned()));
                    rest.push(items);
                } else {
                    work.push((items, h));
                }
            }
        }
        rest
    }

    /// The values of `x` split by which shapes of `held` (indices into `cuts`, in increasing
    /// order) hold them at item `i`: each part with the shapes holding it, in increasing order,
    /// the parts disjoint and covering `x` ([`Self::shape_rest`]).
    ///
    /// The shapes of `held` are halved over and over into a balanced tree, each node with the
    /// union of its shapes' items `i`. A part meets a node: what it has outside the node's
    /// union is held by none of the node's shapes and goes on to the next node; what it has
    /// inside goes into the node's two halves in turn, or, at a single shape, is held by it.
    /// Complexity tradeoff: meeting every part with every shape, as the first version of this
    /// split did, costs O(k·r) meets for k shapes and r parts, quadratic for a chain of k
    /// shapes each meeting the next (35 times the instructions at 8 times the shapes,
    /// measured); here a part goes down only the nodes whose union it meets, O(log k) nodes
    /// for a part met by few shapes, and each node's union is formed once, O(k log k) items
    /// in all.
    ///
    /// Each part is split as a [`Ty`] and as its kernel type, and only the kernel type decides
    /// whether a part is empty, so that the split is exact whatever [`Ty::meet`] and
    /// [`Ty::diff`] give ([`Rest`]).
    async fn parts(
        &'m self,
        cuts: &[Vec<Item>],
        held: &[usize],
        i: usize,
        x: Item,
        solve: Option<Solve<'s>>,
    ) -> Vec<(Item, Vec<usize>)> {
        let mut unions: HashMap<(usize, usize), Item> = HashMap::new();
        let mut out = Vec::new();
        // Each task: a part, the shapes holding it so far, and the nodes still to meet, the
        // next last.
        type Task = (Item, Vec<usize>, Vec<(usize, usize)>);
        let mut work: Vec<Task> = vec![(x, Vec::new(), vec![(0, held.len())])];
        while let Some((r, h, mut nodes)) = work.pop() {
            let Some((lo, hi)) = nodes.pop() else {
                out.push((r, h));
                continue;
            };
            if hi == lo {
                work.push((r, h, nodes));
                continue;
            }
            let (u, uk) = (unions.entry((lo, hi)))
                .or_insert_with(|| {
                    let node = || held[lo..hi].iter().map(|&c| &cuts[c][i]);
                    let u = Ty::union_all(node().map(|p| &p.0));
                    (u, KType::union_all(node().map(|p| p.1.clone())))
                })
                .clone();
            let mk = &r.1 & &uk;
            if mk.is_empty() {
                work.push((r, h, nodes));
                continue;
            }
            let m = (r.0.meet(&u), mk);
            let ok = &r.1 - &uk;
            if !ok.is_empty() {
                let o = self.diff_deep(r.0, u, solve).await;
                work.push(((o, ok), h.clone(), nodes.clone()));
            }
            if hi - lo == 1 {
                let mut h = h;
                h.push(held[lo]);
                work.push((m, h, nodes));
            } else {
                let mid = lo + (hi - lo) / 2;
                nodes.push((mid, hi));
                nodes.push((lo, mid));
                work.push((m, h, nodes));
            }
        }
        out
    }

    /// The shapes of `held` (indices into `cuts`, in increasing order) whose items from `from`
    /// on are not each within those of another shape of `held`; of shapes with the same such
    /// items, the first. [`Self::shape_rest`] takes the rest of the tails less these, the same
    /// set as less all of `held`. `within` keeps, for shapes `a` and `b` and an item `j`,
    /// whether `a`'s item `j` is within `b`'s, so each pair of items is compared once.
    ///
    /// Cost: each shape of `held` is compared with the shapes kept so far, at most a of them,
    /// O(k·a) comparisons of tails for k shapes. Complexity tradeoff: comparing every pair
    /// would be O(k²) for a chain of k nested shapes, where a stays 1.
    fn widest(
        cuts: &[Vec<Item>],
        held: Vec<usize>,
        from: usize,
        within: &mut HashMap<(usize, usize, usize), bool>,
    ) -> Vec<usize> {
        let mut kept: Vec<usize> = Vec::with_capacity(held.len());
        for c in held {
            if (kept.iter()).any(|&d| Self::tail_within(cuts, c, d, from, within)) {
                continue;
            }
            let mut wider = Vec::with_capacity(kept.len() + 1);
            for d in kept {
                if !Self::tail_within(cuts, d, c, from, within) {
                    wider.push(d);
                }
            }
            wider.push(c);
            kept = wider;
        }
        kept.sort_unstable();
        kept
    }

    /// Whether each item of `cuts[a]` from `from` on is within the item of `cuts[b]` at its
    /// place, each pair of items compared once ([`Self::widest`]). The kernel types are
    /// compared ([`KType::subtype`], whose yes is proved), so a shape is dropped only where its
    /// tail is within the other's.
    fn tail_within(
        cuts: &[Vec<Item>],
        a: usize,
        b: usize,
        from: usize,
        within: &mut HashMap<(usize, usize, usize), bool>,
    ) -> bool {
        for (j, (x, y)) in cuts[a].iter().zip(&cuts[b]).enumerate().skip(from) {
            let held = *(within.entry((a, b, j))).or_insert_with(|| x.1.subtype(&y.1));
            if !held {
                return false;
            }
        }
        true
    }

    /// Whether each component and field of the payload `a` is in the one of `b` at its place
    /// ([`Comparing::sub_by_shape`]), `b` of as many items and the same field names, in a
    /// frame of its own: with `b` and what it binds. Compared once for each binding the pair
    /// is met with ([`Cx::compared`]).
    fn shape_in(&'m self, a: Shape, b: Shape, mut binds: Binds) -> Deep<'m, (bool, Binds)> {
        self.stack.call(move || async move {
            let key = Compared::new(a.node(), b.node(), &binds, self.cx.borrow().bind_none);
            if let Some(kept) = self.recall(&key) {
                return kept;
            }
            let pairs =
                (a.items.iter().zip(&b.items)).chain(a.fields.values().zip(b.fields.values()));
            let mut ok = true;
            for (j, (x, y)) in pairs.enumerate() {
                if !self
                    .sub_by_shape(x, y, &mut binds, Site::In(Holder::Shape(&b), j))
                    .await
                {
                    ok = false;
                    break;
                }
            }
            self.keep(key, ok, &binds);
            (ok, binds)
        })
    }

    /// The tuple and payload shapes of `t`, the type `search` compares pieces with, filed
    /// ([`Filed`]): once for the pieces of one type, and once for the whole comparison where `t`
    /// is a component of a row or payload shape, which a comparison may meet once for each
    /// member of a union on the other side.
    fn filed(&self, t: &Ty, search: &mut Search<'_>) -> Arc<Filed> {
        if let Some(f) = &search.filed {
            return f.clone();
        }
        let f = match search.site {
            Site::Other => Arc::new(Filed::new(t)),
            Site::In(h, j) => {
                let mut cx = self.cx.borrow_mut();
                (cx.filed.entry((h.node(), j)))
                    .or_insert_with(|| Arc::new(Filed::new(t)))
                    .clone()
            }
        };
        search.filed = Some(f.clone());
        f
    }

    /// Records why the comparison is refused, the first time; `why` is made only then.
    fn refuse(&self, why: impl FnOnce() -> String) {
        // `why` reads the state, to print the types as the comparison names them.
        if self.cx.borrow().unchosen.is_none() {
            let why = why();
            self.cx.borrow_mut().unchosen = Some(why);
        }
    }

    /// Opens an attempt of its own: the refusal made before it, if any, set aside until
    /// [`Self::end_alone`] puts it back. A refusal made inside the attempt is not kept, so an
    /// attempt tried and dropped leaves the comparison as it found it. Without this, a refusal
    /// inside an arrow of `s` tried for an arrow of `q` and not fitting refused the whole
    /// comparison, though a later arrow fits, and the verdict depended on the order of the
    /// arrows (`same_in_every_order`). Two calls around the attempt's `await`, not a wrapper
    /// future: a wrapper moved each attempt's future through one more frame of the thread's
    /// stack, about 25 KB at each depth of function types, which overflowed
    /// `bench::deep_ops::signatures_of_deep_types_run_on_a_shallow_stack`.
    fn begin_alone(&self) -> Option<String> {
        self.cx.borrow_mut().unchosen.take()
    }

    /// Closes the attempt [`Self::begin_alone`] opened, putting back `before`, what it set
    /// aside: why the attempt was refused ([`Self::refuse`]), if it was.
    fn end_alone(&self, before: Option<String>) -> Option<String> {
        std::mem::replace(&mut self.cx.borrow_mut().unchosen, before)
    }

    /// The search for the shape of `choices`'s group that holds the member `member.1`, of the
    /// group `member.0`, whose components are `xs`: the shapes of its buckets
    /// ([`Choices::lookup`]), merged in written order, each tried by `fit` with the bindings so
    /// far, the first that holds it keeping what it binds. The rule of one shape tries every
    /// shape of the group in order; a shape outside the buckets holds no member of them, and a
    /// shape a bucket's [`Pins`] leave out holds no member of the lists they give
    /// ([`Pins::lists`]), so the shape found and the bindings are the same. `comps` gives the
    /// components of a shape. `Ok(false)` when none holds it, and at once when the comparison
    /// was refused, since it then answers false.
    ///
    /// Complexity tradeoff: a member tries the shapes of a bucket until one holds it, but once
    /// it has failed one there, it goes on past it for one member of a union only; the next
    /// member of the same union that fails one shape of the bucket and needs another is refused
    /// (`Err`, with the member that searched it, the group of [`Choices`] and the bucket), and
    /// the comparison answers false ([`Cx::decided`]) with the reason [`Ty::refused`] gives.
    /// Where the bindings have ceilings ([`ceilings`]), the first shape a member fails in a
    /// bucket has the bucket's shapes pinned by those ceilings ([`Pins`]), once for the union,
    /// and the member and those after it try only the shapes the pins give: a shape whose
    /// variable's ceiling is a variable of the other side is found by a lookup on that variable,
    /// not by trying it, and a member with a scalar value there skips the shapes whose ceiling
    /// holds only variables. So `(X,) | (W,) | (Y,)` in `(T,) | (U,) | (V,)`, with `T`'s
    /// ceiling `X`, binds `T` to `X` and `U` to `W | Y`, as the rule of one shape does, where
    /// before the pins `(W,)` and `(Y,)` each failed `(T,)` and the second was refused
    /// (FAIL-types-three-variable-shapes); and `(int,) | (1,)` skip `(T,)` likewise. Where the
    /// ceilings pin no shape of the bucket, a shape a member is held by or fails whose
    /// component at a place is one variable bound alone to a variable `w` of several carriers
    /// ([`bound_alone`]) has the bucket's shapes of that variable pinned by the binding
    /// ([`Bound`]); a member that the binding leaves out skips them by lookup, and passes
    /// without failing it a shape it tried before the pin. So `(Y0,) | (Y1,) | (Y2,)` in
    /// `(X0,) | (X1,) | (X2,)`, every variable bounded to several carriers, binds `X0` to `Y0`,
    /// which pins `(X0,)`, then `(Y1,)` skips it and binds `X1`, and `(Y2,)` skips both, where
    /// before `(Y1,)` and `(Y2,)` both failed `(X0,)` and the second was refused
    /// (FAIL-types-bounded-shapes-renamed-refused).
    /// Naive version: every member tries every shape in written order, the members times the
    /// shapes, the n² of `#a(String, 1) | … <: #a(T, 1) | …` before the index, and of n shapes
    /// `(T_i,)` each with the ceiling `X_i` for the members `(X_i,)`. Chosen: a member costs a
    /// lookup in each group, the first shape it tries in each of its buckets, the lists of the
    /// pins at each place pinned (a hash lookup each) and, for one member of the union per
    /// bucket, the shapes past the first it fails; the pins cost the bucket's components and the
    /// variables of the ceilings of its pinned shapes, once for the union; the pins of the
    /// bindings cost, for each variable bound alone, the shapes of the bucket with that variable
    /// at a place (an index made once for the type, [`Group::exact`]), O(log n) each, once for
    /// the search, and each step through their lists O(log n). The members and shapes then cost
    /// n log n times the groups. What is given up: the verdict of the rule of one shape where
    /// two members each fail a shape of one bucket that no pin leaves out and need a later one,
    /// such as `#a(3, 5) | #a(4, 6) <: #a(1 | 2, T) | #a(int, U)`, where component 1 files both
    /// shapes under `int` and `1 | 2` holds neither payload, or shapes whose variables have no
    /// ceiling and are not bound alone, or whose ceiling holds scalars, tuples or functions
    /// where the members have scalars there, or bound alone in a bucket the ceilings pin (the
    /// two pins are not taken together). A shape pinned by a binding at one place that leaves
    /// a member out at another is tried by each member keyed to it there, a fit each. The
    /// proposal was to count, for shapes of one canonical form, the members of each form and
    /// compare the counts; not taken, as a variable with no ceiling takes the union of every
    /// member it holds, so counts of shapes say nothing of whether the result holds the
    /// bindings. The groups are the sets of places at which shapes have a class and are one
    /// value, a few in a written union; shapes with variables or values at many different sets
    /// of places make as many groups, up to the shapes, and then each member costs a lookup in
    /// each. Measured: the same verdict and bindings as the rule of one shape wherever not
    /// refused, on random comparisons of unions of shapes of width two
    /// (`shapes_found_by_the_index_are_those_of_the_rule_of_one_shape`) and of signatures whose
    /// unions of variable shapes meet ceilings
    /// (`pinned_shapes_are_those_of_the_rule_of_one_shape`). Prior work: clause indexing on the
    /// first argument in Prolog (Warren, "An Abstract Prolog Instruction Set", SRI 1983), which
    /// tries only the clauses whose head may match the call; here the key of a shape pinned by a
    /// ceiling is each variable the ceiling holds. Tests:
    /// `tests/steps/l01_22_type_representation/kinds.rs`,
    /// `payloads_with_a_variable_are_searched_by_their_keys` and the tests after it, and the
    /// tests after `a_union_of_three_shapes_of_variables_fits_itself_renamed`; COMPLEXITY.md
    /// F124. A complete solution would search a bucket once for all its members, by keys of
    /// the components that are not one value too (a tuple of a carrier, a payload), at any
    /// depth, as the kernel files its rows (`RowIndex`), and would find the groups that may
    /// hold a member by a partial-match index rather than one lookup in each.
    #[allow(clippy::too_many_arguments)]
    async fn search<'t, G: Ord + Clone, M: Clone>(
        &'m self,
        choices: &Choices,
        xs: &[&Ty],
        member: (G, &M),
        searched: &mut Searched<G, M>,
        bound: &mut BoundTable<G>,
        comps: impl Fn(usize) -> Vec<&'t Ty>,
        binds: &mut Binds,
        fit: impl Fn(usize, Binds) -> Deep<'m, (bool, Binds)>,
    ) -> Result<bool, (M, usize, Bucket)> {
        use std::cmp::Reverse;
        let buckets = {
            let cx = self.cx.borrow();
            if cx.unchosen.is_some() {
                return Ok(false);
            }
            choices.lookup(xs, &cx.rigid)
        };
        #[cfg(test)]
        let (buckets, scan_all) = match SCAN_ALL.get() {
            true => ((0..choices.groups.len()).map(|g| (g, None)).collect(), true),
            false => (buckets, false),
        };
        #[cfg(not(test))]
        let scan_all = false;
        let (group, m) = member;
        let at = |k: usize| (group.clone(), buckets[k].0, buckets[k].1.clone());
        // The lists of shapes to try, each with its bucket: a bucket whole, or the lists its
        // pins give the member where they are made; `pinned` marks the buckets read by the pins
        // of the ceilings, which then take no pins of the bindings.
        let mut lists: Vec<(usize, Shapes)> = Vec::new();
        let mut pinned = vec![false; buckets.len()];
        {
            let cx = self.cx.borrow();
            for (k, (g, id)) in buckets.iter().enumerate() {
                let shapes = choices.bucket(*g, id);
                if scan_all {
                    lists.push((k, Shapes::Bucket(shapes)));
                    continue;
                }
                match searched.pins(&at(k), binds) {
                    Some(p) => {
                        pinned[k] = true;
                        lists.extend(p.lists(xs, &cx).into_iter().map(|l| (k, Shapes::Pinned(l))));
                    }
                    None => match bound.get(&at(k)) {
                        Some(pins) => {
                            lists.extend(pins.lists(shapes, xs, &cx).into_iter().map(|l| (k, l)));
                        }
                        None => lists.push((k, Shapes::Bucket(shapes))),
                    },
                }
            }
        }
        // Each list's next shape, by the shape first, so the heap yields written order; a list
        // replaced by new pins of its bucket is no longer `live`.
        let mut heads: std::collections::BinaryHeap<Reverse<(usize, usize, usize)>> =
            (lists.iter().enumerate())
                .filter_map(|(i, (_, l))| {
                    let (r, n) = l.after(None)?;
                    Some(Reverse((r, i, n)))
                })
                .collect();
        let mut live = vec![true; lists.len()];
        // The lists of the bucket `k` from past the shape `r` on put in place of those read so
        // far, which are no longer live.
        type Heads = std::collections::BinaryHeap<Reverse<(usize, usize, usize)>>;
        fn replace<'c>(
            k: usize,
            r: usize,
            new: Vec<Shapes<'c>>,
            lists: &mut Vec<(usize, Shapes<'c>)>,
            live: &mut Vec<bool>,
            heads: &mut Heads,
        ) {
            for (j, live) in live.iter_mut().enumerate() {
                if lists[j].0 == k {
                    *live = false;
                }
            }
            for l in new {
                if let Some((first, n)) = l.after(Some(r)) {
                    heads.push(Reverse((first, lists.len(), n)));
                }
                lists.push((k, l));
                live.push(true);
            }
        }
        // The buckets in which this member has failed a shape, and those it has searched past
        // that shape.
        let mut failed = vec![false; buckets.len()];
        let mut past = vec![false; buckets.len()];
        while let Some(Reverse((r, i, n))) = heads.pop() {
            if !live[i] {
                continue;
            }
            let k = lists[i].0;
            if let Some((next, n)) = lists[i].1.next(r, n) {
                heads.push(Reverse((next, i, n)));
            }
            if failed[k] && !past[k] && !scan_all {
                match searched.by.entry(at(k)) {
                    Entry::Occupied(e) => {
                        return Err((e.get().clone(), buckets[k].0, buckets[k].1.clone()));
                    }
                    Entry::Vacant(e) => e.insert(m.clone()),
                };
                past[k] = true;
            }
            let (ok, b) = fit(r, binds.clone()).await;
            if ok {
                *binds = b;
                // The shapes of the variables `r` has now bound alone are pinned at once, so the
                // later members skip them without a failed fit each.
                if !pinned[k] && !scan_all {
                    let (g, id) = &buckets[k];
                    let shapes = choices.bucket(*g, id);
                    let cx = self.cx.borrow();
                    let exact = || choices.groups[*g].exact(id, &comps);
                    let old = bound.get(&at(k));
                    if let (_, Some(pins)) =
                        Bound::grow(old, shapes, &comps(r), xs, binds, exact, &cx)
                    {
                        bound.insert(at(k), pins);
                    }
                }
                return Ok(true);
            }
            if pinned[k] || scan_all {
                failed[k] = true;
                continue;
            }
            let (g, id) = &buckets[k];
            let shapes = choices.bucket(*g, id);
            // The first shape the member fails in a bucket not yet pinned: the bucket is pinned by
            // the ceilings where they pin a shape, and the rest of it is read from the lists the
            // pins give, from past `r` on.
            if !failed[k] {
                let pins = {
                    let cx = self.cx.borrow();
                    (searched.pin(at(k), shapes, &comps, binds, &cx)).map(|p| p.lists(xs, &cx))
                };
                if let Some(pins) = pins {
                    pinned[k] = true;
                    let pins = pins.into_iter().map(Shapes::Pinned).collect();
                    replace(k, r, pins, &mut lists, &mut live, &mut heads);
                    continue;
                }
            }
            // Else the shapes of the variables `r` has bound alone ([`bound_alone`]) are pinned
            // by those bindings ([`Bound`]), and a shape so pinned that leaves the member out is
            // passed, not failed: the member would not have tried it had it been pinned before.
            let (left_out, new) = {
                let cx = self.cx.borrow();
                let exact = || choices.groups[*g].exact(id, &comps);
                let (left_out, pins) =
                    Bound::grow(bound.get(&at(k)), shapes, &comps(r), xs, binds, exact, &cx);
                let new = pins.map(|pins| {
                    let lists = pins.lists(shapes, xs, &cx);
                    bound.insert(at(k), pins);
                    lists
                });
                (left_out, new)
            };
            if !left_out {
                failed[k] = true;
            }
            if let Some(new) = new {
                replace(k, r, new, &mut lists, &mut live, &mut heads);
            }
        }
        Ok(false)
    }

    /// Whether the shape `r`, the one equal to the member compared if there is one, holds the
    /// member by `fit` binding nothing: the search for its shape ([`Comparing::search`]) then
    /// need not run. `(X1,)` in `(X0,) | (X1,)` is in `(X1,)` as it is, where the first shape
    /// in written order holds it by binding `X0` to `X1`. Before
    /// (FAIL-types-singleton-tuple-union-match), the search took `(X0,)`, so
    /// `(X0,) | (X1,) <: (X0,) | (X1,)` bound `X0`, and `(x0: (T,)) -> (T,)` did not fit
    /// `(x0: ((X0,),) | ((X1,),)) -> ((X0,) | (X1,),)`, whose result must hold `T`'s binding
    /// with nothing bound ([`result_within`]); payload shapes the same. A refusal inside the
    /// attempt is dropped, as the search then decides. Where `choices` holds one shape, the
    /// search takes that shape with the same bindings, so the attempt would only repeat the
    /// search's comparison, and is not made.
    ///
    /// Complexity tradeoff (COMPLEXITY.md F203): naive version, every shape tried for one that
    /// binds nothing before the first that binds, O(k) comparisons a member for `k` shapes.
    /// Used: the equal shape found by a hash lookup on the digest each row and shape keeps
    /// ([`Filed::equal`], [`Filed::equal_shapes`]), one comparison more a member at most, the
    /// table made once for the type in O(k). What is given up: a shape that holds the member
    /// binding nothing but is not equal to it, such as `(X1 | int,)` for `(X1,)`, is still
    /// passed over for an earlier shape that binds.
    async fn held_as_is(
        &'m self,
        choices: &Choices,
        r: Option<usize>,
        binds: &Binds,
        fit: impl Fn(usize, Binds) -> Deep<'m, (bool, Binds)>,
    ) -> bool {
        let Some(r) = r.filter(|_| !choices.one()) else {
            return false;
        };
        let before = self.begin_alone();
        let (ok, b) = fit(r, binds.clone()).await;
        self.end_alone(before);
        ok && b == *binds
    }

    /// Whether the payloads `of` gives the atoms of `s` are in those `t` gives them, where the
    /// normal forms were not made ([`Comparing::by_form`]): a payload not known is in a payload
    /// not known only, and each payload shape is in one of `t`'s shapes of the same length and
    /// field names, by the rule of one shape, binding `t`'s variables. The shapes tried for each
    /// are found by [`Comparing::search`], which refuses where the rule would search one bucket
    /// for two payloads.
    async fn payloads_in(
        &'m self,
        s: &KType,
        of: &Ty,
        t: &Ty,
        binds: &mut Binds,
        search: &mut Search<'_>,
    ) -> bool {
        // Called once `s` is in `t`'s set, with no carrier holding an atom: an atom of `s`
        // whose payloads `t` does not list is one whose payloads `t` holds all of. So only the
        // names `t` lists are read, not each name of `s`, which may be many more.
        for (n, rs) in &t.payloads {
            // A payload `t` does not know holds any payload.
            let Some(rs) = rs else { continue };
            if !holds_payload(s, n) {
                continue;
            }
            let Some(ls) = of.shapes(n) else { return false };
            if ls.is_empty() {
                continue;
            }
            let filed = self.filed(t, search);
            let groups = (filed.payloads.get(n)).expect("each payload union `t` lists is filed");
            let mut searched = Searched::new();
            let mut bound = BoundTable::new();
            // The shapes of `rs` near each of `ls` ([`near_pairs`]), made the first time a
            // shape no one shape holds is tried against them together ([`Self::held_together`]).
            let mut nears = None;
            for (i, l) in ls.iter().enumerate() {
                let g = shape_group(l);
                let Some(choices) = groups.get(&g) else {
                    return false;
                };
                let fit = |r: usize, b| self.shape_in(l.clone(), rs[r].clone(), b);
                let equal =
                    (filed.equal_shapes(t).get(n)).and_then(|e| e.get(&l.0.digest).copied());
                if self.held_as_is(choices, equal, binds, &fit).await {
                    continue;
                }
                let xs = comps(l);
                let shapes = |r: usize| comps(&rs[r]);
                let found = (self).search(
                    choices,
                    &xs,
                    (g, l),
                    &mut searched,
                    &mut bound,
                    shapes,
                    binds,
                    fit,
                );
                let found = found.await;
                if matches!(found, Ok(true)) {
                    continue;
                }
                let held = self.held_together(l, i, ls, rs, t, &mut nears).await;
                match held {
                    Some(Held::Yes) => continue,
                    Some(Held::No) => return false,
                    Some(Held::Refused(_)) | None => {}
                }
                match found {
                    Ok(_) => {
                        // The rule of one shape found no shape holding `l`, and the shapes
                        // near it hold it together or not, undecided: a refusal, not a no.
                        if let Some(Held::Refused(r)) = held {
                            self.refuse(|| r.message());
                        }
                        return false;
                    }
                    Err((first, k, id)) => {
                        self.refuse(|| {
                            let cx = self.cx.borrow();
                            let mut scope = Scope::of_comparison(&cx, None);
                            let shapes = choices.bucket(k, &id).iter().map(|&r| rs[r].clone());
                            let names: Vec<&Arc<str>> = l.fields.keys().collect();
                            let apart = choices.apart(k, &id, l.items.len(), &names);
                            let own = own_shape(
                                &comps(&first),
                                &comps(l),
                                l.items.len(),
                                &names,
                                |c| cx.vars_within(c, t),
                                |c| scope.text(c, &cx),
                                |cs| format!("#{n}({cs})"),
                            );
                            let first = payload_text(n, vec![first], &mut scope, &cx);
                            let second = payload_text(n, vec![l.clone()], &mut scope, &cx);
                            let bucket = payload_text(n, shapes.collect(), &mut scope, &cx);
                            let given = scope.given_text();
                            unchosen_text("payloads", &first, &second, &bucket, &apart, own, &given)
                        });
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Whether the payload shape `l`, number `i` of `ls`, held by no one shape of `rs` (the
    /// shapes `t` lists for its atom), is held by the shapes of `rs` near it together, where
    /// `l`, those shapes and `t` are exact (no variable, unknown or function; [`ShapeData::exact`]):
    /// the answer of [`Rest::held`] on the rest of `l` less them ([`Self::shape_rest`]), and
    /// none where they are not exact. `nears` keeps the shapes of `rs` near each of `ls`
    /// ([`near_pairs`]), made on the first call.
    ///
    /// Why (FAIL-types-shape-union-sub-incomplete): `#a(int, int, int)` was not found within
    /// the union of the cuts `#a(B_j, B_j, B_j)` (B_j the numbers below 8 with bit j set) and
    /// the rest of `#a(int, int, int)` less them. Both sides are exact, so
    /// [`Comparing::by_form`] asks the kernel, which refuses: it would have to split more than
    /// one item into cases at once (`TupleSplit`). The rule of one shape then failed, since no
    /// one shape holds `l`, though [`Ty::diff`] found the difference empty.
    ///
    /// Proof: the values of `l` outside every shape of `rs` are those outside the shapes near
    /// it, as a shape [`near_pairs`] leaves out shares no value with `l` (proof at [`Near`]).
    /// The kernel types of the rest hold exactly those values (proof at [`Self::shape_rest`],
    /// which makes its choices on kernel types, not on [`Ty::meet`], [`Ty::diff`] or
    /// [`Ty::is_empty`]), so [`Rest::held`] answers for `rs`. With no shape near `l`, the rest
    /// is `l` itself, and the answer is whether `l` holds a value. Before
    /// (PROOF-diff-exact-skip), a rest with a part was read as deciding nothing, and the
    /// search's no stood: where `is_empty` does not prove an empty part empty, that no was
    /// wrong (`kinds::a_payload_whose_tuple_item_needs_a_split_of_many_components_is_refused`).
    ///
    /// Complexity tradeoff: naive version, the rest made for every shape before the search,
    /// which costs each shape held by one shape a rest it does not need. Used: the rest only
    /// for a shape the search did not find held, the near shapes listed once for all of `ls`
    /// at the first such shape, O((l·G + r·H)·w + p) as for [`Self::diff`], and the rest at the
    /// cost [`Self::shape_rest`] states, at most w^k shapes for k near shapes of w items, which
    /// some inputs need. Prior work: the decomposition of a product type into a union of
    /// products in semantic subtyping (Frisch, Castagna and Benzaken, "Semantic subtyping",
    /// JACM 2008), here item by item with the parts held by the same shapes joined.
    async fn held_together(
        &'m self,
        l: &Shape,
        i: usize,
        ls: &[Shape],
        rs: &[Shape],
        t: &Ty,
        nears: &mut Option<Vec<Vec<usize>>>,
    ) -> Option<Held> {
        if t.dynamic || !t.vars.is_empty() || l.0.exact.is_none() {
            return None;
        }
        let near = nears.get_or_insert_with(|| near_pairs(ls.iter(), rs.iter()));
        let cut: Vec<Shape> = near[i].iter().map(|&j| rs[j].clone()).collect();
        if cut.iter().any(|c| c.0.exact.is_none()) {
            return None;
        }
        let solve = self.cx.borrow().solve;
        Some(self.shape_rest(l, &cut, solve).await.held())
    }

    /// Whether the tuple piece `cs` of a type is in the tuple shapes of `t` of its length: in
    /// one of them ([`Comparing::row_in_one`]), else, where a component of `cs` has two or more
    /// pieces ([`Ty::pieces`]), split at one ([`Comparing::split_at`]) into one row for each
    /// piece, each row in turn held in the same way, with the bindings the rows before it gave.
    /// `search` holds `t`'s shapes filed and the buckets the other tuple pieces of the type
    /// searched.
    ///
    /// A tuple type is the set of its tuples, so `(A | B, C)` holds what `(A, C) | (B, C)`
    /// holds, and the split rows are in `t` exactly when `cs` is. Before
    /// (FAIL-types-joined-one-tuple-in-split-shapes), only one shape could hold `cs`:
    /// `(x0: (X0 | X1,)) -> int` did not fit `(x0: (X0,) | (X1,)) -> int` with `X0` and `X1`
    /// bounded to several carriers, where each stands for one carrier and so holds `X0'` or
    /// `X1'` of the other side, not both; unbounded, `X0` was bound to `X0' | X1'`. Now the
    /// joined row is read as the split rows, as if written so.
    ///
    /// The rows of one split are the members of one union, so they share a [`Searched`] of
    /// their own, new for each split: the one the type's pieces share already holds the bucket
    /// `cs` searched past its first shape, and the first split row to need a second shape of
    /// that bucket would be refused. A row a split makes that no shape holds is split in turn
    /// in the same way; one of a single piece at each component that no shape holds makes the
    /// answer false, and a refusal ends the walk with the refusal's answer. The bindings are
    /// kept only when every row is held, so a false leaves `binds` as it was, as
    /// [`Comparing::search`] does.
    ///
    /// Complexity tradeoff: naive version, the product of the components' pieces as rows, each
    /// searched, exponential in the width. Used: a split only where the row is held by no one
    /// shape, at the component a shape it was tried in fails it ([`Comparing::split_at`]), the
    /// rows walked depth first from an explicit stack, stopping at the first row of single
    /// pieces held by no shape. A split is never undone to try another component, so each row
    /// is searched once: the rows split form a tree whose leaves are the rows held, and a tree
    /// of two or more rows at each split has fewer inner rows than leaves, so the rows
    /// searched are fewer than twice the rows held. Before, the split was at the first
    /// component of two or more pieces, and a row of k joined components that the shapes split
    /// at the last made 2^k rows held for 2 shapes (PERF-types-joined-split-many-components).
    /// Measured, not proved: that the rows held are about the shapes of `t` of the length,
    /// one shape each. A shape that holds two rows differing at one component holds their
    /// union there too unless the bindings made between them stand in the way, and a shape
    /// tried may differ from the row at a component where the shapes that hold its rows do
    /// not ([`Comparing::split_at`] names the case). Each inner row is tried in every shape of
    /// its bucket the pins leave it before it is split, which for m shapes that differ on
    /// log m components is m log m fits. Evidence:
    /// `bench::fits::k_joined_components_split_where_the_shapes_differ_scales` (k = 2, 3, 4
    /// joined components, two shapes each, ratios 8.93, 8.94 and 9.00 at 100 and 800),
    /// `k_joined_components_cost_at_most_twice_the_rows_written_out` (1.70 the work of the rows
    /// written out at k = 4, 8.2 before), a probe of 2, 4, 8, 16 and 32 shapes for each row
    /// that differ on 1 to 5 components (1.2 to 1.7, 1.9 to 2.1, 2.4, 2.8 and 3.5 times the rows
    /// written out, 2.4 to 15.4 before for 2 shapes), and
    /// `bench::fits::a_joined_component_split_across_shapes_scales` (one joined component split
    /// across two of 2n shapes); tests:
    /// `k_joined_components_fit_shapes_that_differ_on_some_of_them` and the tests after
    /// `a_joined_one_element_tuple_fits_split_shapes_for_every_bound`. Prior work: the
    /// distribution of a union over a product in semantic subtyping (Frisch, Castagna and
    /// Benzaken, "Semantic subtyping", JACM 2008), which decomposes a product type into the
    /// union of products and checks each; here only where one shape does not hold the row.
    async fn row_in(
        &'m self,
        cs: &Row,
        t: &Ty,
        search: &mut Search<'_>,
        binds: &mut Binds,
    ) -> bool {
        let filed = self.filed(t, search);
        // The shapes each row was tried in and failed, in the order tried, for
        // [`Comparing::split_at`].
        let tried = RefCell::new(Vec::new());
        if self
            .row_in_one(
                cs,
                t,
                &filed,
                &mut search.searched,
                &mut search.bound,
                &tried,
                binds,
            )
            .await
        {
            return true;
        }
        // The rows of one split: each made from its parent at the component `j` of two or more
        // pieces ([`Comparing::split_at`]), in written order.
        let split = |r: &Row, j: usize| -> Vec<Row> {
            let pieces = r[j].pieces();
            (pieces.iter().rev())
                .map(|p| {
                    let mut comps: Vec<Ty> = r.iter().cloned().collect();
                    comps[j] = r[j].of_piece(p);
                    r.replaced(comps)
                })
                .collect()
        };
        if self.cx.borrow().unchosen.is_some() {
            return false;
        }
        let Some(j) = self.split_at(cs, t, &tried.take(), binds).await else {
            return false;
        };
        let first = split(cs, j);
        let mut b = binds.clone();
        // The pins of the bindings, as `b` grows from `binds`: kept with `b`.
        let mut bound = search.bound.clone();
        // Each split's own [`Searched`], and the rows still to hold with the split each is of,
        // the next on top.
        let mut unions: Vec<Searched<usize, Row>> = vec![Searched::new()];
        let mut todo: Vec<(Row, usize)> = first.into_iter().map(|r| (r, 0)).collect();
        while let Some((r, u)) = todo.pop() {
            let held = self.row_in_one(&r, t, &filed, &mut unions[u], &mut bound, &tried, &mut b);
            if held.await {
                tried.take();
                continue;
            }
            if self.cx.borrow().unchosen.is_some() {
                return false;
            }
            let Some(j) = self.split_at(&r, t, &tried.take(), &b).await else {
                return false;
            };
            let rows = split(&r, j);
            unions.push(Searched::new());
            todo.extend(rows.into_iter().map(|r| (r, unions.len() - 1)));
        }
        *binds = b;
        search.bound = bound;
        true
    }

    /// The component at which [`Comparing::row_in`] splits the row `cs`, held by no one tuple
    /// shape of `t` under `binds`: the first component of two or more pieces ([`Ty::pieces`])
    /// at which a shape of `tried`, those [`Comparing::row_in_one`] tried `cs` in, all failed,
    /// first does not hold it, the shapes taken in the order tried; else the first component of
    /// two or more pieces; none if there is no such component.
    ///
    /// Any component of two or more pieces gives the same answer: the rows of a split are the
    /// set of `cs`, at whichever component. The choice sets the cost only. Splitting at the
    /// first component of two or more pieces, a row `(A | B, C | D)` against the shapes
    /// `(A | B, C) | (A | B, D)` made 4 rows for 2 shapes, and with k such components 2^k rows
    /// for 2 shapes (PERF-types-joined-split-many-components: 2.4, 4.4, 8.2 and 15.4 times the
    /// work of the rows written out, for k = 2 to 5). Splitting where a shape tried fails, the
    /// component the shapes differ on, makes 2 rows, each held whole. The shapes tried, not the
    /// first of the bucket: after a split, a row whose binding leaves out the first shape
    /// ([`Bound`]) fails it at a component of one piece, and the search has skipped it for the
    /// shape whose failure names the next component the shapes differ on.
    ///
    /// Complexity tradeoff: naive version, try each component of two or more pieces as the
    /// split and keep the one that makes the fewest rows, which searches the rows of every
    /// choice. Used: the shapes tried compared again with `cs`, component by component, each
    /// stopping at the first that fails, until one fails at a component of two or more pieces:
    /// at most one more fit for each shape the search tried, and only for a row that is split.
    /// Given up: a shape tried may differ from `cs` at a component where the shapes that hold
    /// its rows do not, and the split is then no better than at the first component.
    async fn split_at(&'m self, cs: &Row, t: &Ty, tried: &[usize], binds: &Binds) -> Option<usize> {
        let many = |c: &Ty| c.pieces_lazily().nth(1).is_some();
        let first = cs.iter().position(many)?;
        for &r in tried {
            let ds = t.tuples[r].clone();
            let at = self.failing_component(cs.clone(), ds, binds.clone()).await;
            if let Some(j) = at.filter(|&j| many(&cs[j])) {
                return Some(j);
            }
        }
        Some(first)
    }

    /// The first component of `cs` not in the one of `ds` at its place, as
    /// [`Comparing::rows`] compares them, under `b`, in an attempt of its own
    /// ([`Self::begin_alone`]), so a refusal inside it is dropped and what it binds is
    /// discarded; none if each is.
    fn failing_component(&'m self, cs: Row, ds: Row, mut b: Binds) -> Deep<'m, Option<usize>> {
        self.stack.call(move || async move {
            let before = self.begin_alone();
            let mut at = None;
            for (j, (c, d)) in cs.iter().zip(&ds).enumerate() {
                if !(self.sub_by_shape(c, d, &mut b, Site::In(Holder::Row(&ds), j))).await {
                    at = Some(j);
                    break;
                }
            }
            self.end_alone(before);
            at
        })
    }

    /// Whether the tuple piece `cs` of a type is in one of the tuple shapes of `t` of its
    /// length: a shape equal to it that holds it binding nothing, else the first in written
    /// order that holds it, binding `t`'s variables, of those [`Comparing::search`] tries;
    /// `filed` holds `t`'s shapes filed and `searched` the buckets the other members of the
    /// union `cs` is of searched, and `tried` gets each shape tried, in order.
    #[allow(clippy::too_many_arguments)]
    async fn row_in_one(
        &'m self,
        cs: &Row,
        t: &Ty,
        filed: &Filed,
        searched: &mut Searched<usize, Row>,
        bound: &mut BoundTable<usize>,
        tried: &RefCell<Vec<usize>>,
        binds: &mut Binds,
    ) -> bool {
        let Some(choices) = filed.rows.get(&cs.len()) else {
            return false;
        };
        let fit = |r: usize, b| {
            tried.borrow_mut().push(r);
            self.rows(cs.clone(), t.tuples[r].clone(), b)
        };
        if self
            .held_as_is(
                choices,
                filed.equal(t).get(&cs.0.digest).copied(),
                binds,
                &fit,
            )
            .await
        {
            return true;
        }
        let xs: Vec<&Ty> = cs.iter().collect();
        let found = self.search(
            choices,
            &xs,
            (cs.len(), cs),
            searched,
            bound,
            |r: usize| t.tuples[r].iter().collect(),
            binds,
            fit,
        );
        let found = found.await;
        match found {
            Ok(ok) => ok,
            Err((first, k, id)) => {
                self.refuse(|| {
                    let cx = self.cx.borrow();
                    let mut scope = Scope::of_comparison(&cx, None);
                    let shapes = choices.bucket(k, &id).iter();
                    let bucket = Ty {
                        tuples: shapes.map(|&r| t.tuples[r].clone()).collect(),
                        ..Ty::empty()
                    };
                    let apart = choices.apart(k, &id, cs.len(), &[]);
                    let xs: Vec<&Ty> = first.iter().collect();
                    let ys: Vec<&Ty> = cs.iter().collect();
                    // A tuple of one component is written `(T,)`, as `(T)` reads as `T`.
                    let one = cs.len() == 1;
                    let text = |c: &Ty| scope.text(c, &cx);
                    let own = own_shape(
                        &xs,
                        &ys,
                        cs.len(),
                        &[],
                        |c| cx.vars_within(c, t),
                        text,
                        |s| {
                            if one {
                                format!("({s},)")
                            } else {
                                format!("({s})")
                            }
                        },
                    );
                    let first = scope.text(&Ty::of_row(first.clone()), &cx);
                    let second = scope.text(&Ty::of_row(cs.clone()), &cx);
                    let bucket = scope.text(&bucket, &cx);
                    let given = scope.given_text();
                    unchosen_text("tuples", &first, &second, &bucket, &apart, own, &given)
                });
                false
            }
        }
    }

    /// [`Comparing::sub_in`] with each tuple piece held by one tuple shape of `other`: the rule
    /// for the components of a tuple, whose joint check is the kernel's on the whole tuple.
    /// `other` sits at `site`.
    async fn sub_by_shape(&'m self, t: &Ty, other: &Ty, binds: &mut Binds, site: Site<'_>) -> bool {
        let mut search = Search::new(site);
        for p in t.pieces_lazily() {
            if !accepts(other, &p, t, binds, &mut search, self).await {
                return false;
            }
        }
        true
    }

    /// [`Ty::diff`] of `t` and `u`, a tuple compared with `u` as [`Ty::sub_with`] compares, with
    /// the resolver `solve`, if any: each comparison a new one, on this stack, the state of
    /// the comparisons open set aside meanwhile.
    async fn diff(&'m self, t: &Ty, u: &Ty, solve: Option<Solve<'s>>) -> Ty {
        let open = std::mem::take(&mut *self.cx.borrow_mut());
        // The atoms whose payloads `u` lists are left out of what is taken from the sets: the
        // kernel type of `u` holds such an atom with any payload, and `#a(bool) \ #a(int)` was
        // read as empty (READ-atom-meet). Their payloads are taken shape by shape below.
        let listed: Vec<(&Arc<str>, &[Shape])> = (u.payloads.iter())
            .filter_map(|(n, us)| Some((n, us.as_deref()?)))
            .collect();
        let paid =
            KType::union_all((listed.iter()).map(|(n, _)| KType::atom_with(n, &KType::top())));
        let tk = u.kernel().map(|k| &k - &paid);
        let mut out = t.clone();
        out.set = &t.set - &(tk.clone()).unwrap_or_else(|| &u.set - &paid);
        out.family = &t.family - &(&u.set - &paid);
        out.prune_payloads();
        let w = &u.set & &wide();
        let within = Ty {
            set: w.clone(),
            ..u.clone()
        };
        // What each tuple is compared with is read once: its tuples that may share a value with
        // the tuple ([`near_pairs`]), its other parts and its shapes filed. Each comparison then
        // costs the tuples found, not all of `u`'s.
        let rows = std::mem::take(&mut out.tuples);
        let nears = near_pairs(&rows, &within.tuples);
        let whole = Whole::of(&within);
        let filed = Arc::new(Filed::new(&within));
        let bare = Ty {
            tuples: Members::new(),
            ..within.clone()
        };
        let mut rest = Vec::new();
        let mut kept = Vec::with_capacity(rows.len());
        for (a, near) in rows.into_iter().zip(nears) {
            *self.cx.borrow_mut() = Cx {
                solve,
                ..Cx::default()
            };
            let row = Ty::of_row(a.clone());
            let near = Ty {
                tuples: near.into_iter().map(|j| within.tuples[j].clone()).collect(),
                ..bare.clone()
            };
            // A row that `u` holds in part leaves the rest in the set, where the kernel holds it
            // exactly, keeping the shape's payloads, as in `Self::meet_rest`. Before
            // (FIX-ty-diff-wide-row), only a row that met `u`'s kind-wide part did, and a row
            // that `u`'s tuples held in part was kept whole: `((..), (..)) \ ((..), (int, int))`
            // was read as `((..), (..))`, and a parameter of that type took `((1, 2), (3, 4))`.
            // A row with no kernel type, or beside a tuple of `u` with none, is still kept whole
            // when `u` holds it in part, so the type may hold more than the difference.
            let k = a.0.exact.clone().or_else(|| a.kernel());
            // What of `u` may share a value with the row: its kind-wide part and the kernel
            // types, payloads read, of its tuples near the row. None when one of those tuples
            // has no kernel type (it holds a function, a variable or the unknown), or `u` holds
            // a variable or the unknown, which may be any tuple. The tuples near the row are
            // those not [`apart`] from it, which are those [`near_pairs`] lists, so the cut is
            // the same however many more it lists (the test of every pair lists them all); the
            // test reads the keys the row keeps, O(w) a pair.
            let cut = match (&k, u.dynamic || !u.vars.is_empty()) {
                (Some(_), false) => (near.tuples.iter())
                    .filter(|r| !apart(&a.keys().comps, &r.keys().comps))
                    .map(|r| r.0.exact.clone())
                    .collect::<Option<Vec<_>>>()
                    .map(|ks| KType::union_all(std::iter::once(w.clone()).chain(ks))),
                _ => None,
            };
            // Complexity tradeoff (PERF-deep-ops-slow): a row with a cut is tested against the
            // cut before it is compared with `u`. A row that `u` holds is within the cut, as
            // `u`'s tuples apart from it and its parts of other kinds share no value with it; so
            // a row whose kernel type has a value and misses the cut is kept whole with no
            // comparison. Comparing first, as FIX-ty-diff-wide-row did, ran the kernel's search
            // twice for such a row (a tuple nested 20,000 deep less one that differs at the
            // bottom: 462k instructions a level, 188k before that fix); now the meet's search is
            // the one search, and a row that meets the cut pays both, as before.
            let met = match (&k, &cut) {
                (Some(k), Some(cut)) => Some(!(k & cut).is_empty()),
                _ => None,
            };
            if met == Some(false) && !k.as_ref().is_some_and(KType::is_empty) {
                kept.push(a);
                continue;
            }
            let mut b = Binds::new();
            // A refused comparison keeps the row, as a failed one does.
            let held = (self.sub_near(&row, &within, Some((&near, &whole, &filed)), &mut b)).await;
            if self.cx.borrow().decided(held) && b.is_empty() {
                continue;
            }
            match (k, &cut, &tk) {
                (Some(k), Some(cut), _) if met == Some(true) => rest.push(&k - cut),
                (Some(k), None, Some(tk)) if !(&k & &w).is_empty() => rest.push(&k - tk),
                _ => kept.push(a),
            }
        }
        // A payload shape of an atom `u` lists is dropped when `u`'s shapes of that atom that
        // may share a value with it ([`near_pairs`]) hold it, as a tuple is above; an atom left
        // with no shape is taken from the sets. A refused comparison keeps the shape.
        // Complexity tradeoff (COMPLEXITY.md F144): comparing each shape with all of `u`'s
        // shapes of the atom costs O(l·r) for l and r shapes (70.2 times the bytes at 8 times
        // the shapes in the negative control); the shapes that may share a value with it are
        // found as for the meet, O((l·G + r·H)·w + p).
        //
        // A shape that `u`'s shapes near it hold only in part leaves its rest as shapes
        // ([`Self::shape_rest`]), as a tuple's rest is left above. Before
        // (FAIL-kernel-terms-seed) the shape was kept whole, and `#a(int | String) \ #a(int)`
        // read as `#a(int | String)`, which holds `#a(1)`. The rest is kept as shapes, not in
        // the set as a tuple's is: the set holds a listed atom with any payload, which every
        // other operation on the shapes relies on, and the kernel's test of whether a meet of
        // two unions of n tuples is empty grows as n^2.3 (10 s at n = 1,024), where the shapes
        // are met through `near_pairs`. A shape with no kernel type, or near a shape of `u`
        // with none, or a `u` that holds a variable or the unknown, is still kept whole, so
        // the type may hold more than the difference, as for tuples.
        let exact_u = !u.dynamic && u.vars.is_empty();
        let mut gone = Vec::new();
        for (n, us) in &listed {
            let Some(Some(ts)) = t.payloads.get(*n) else {
                continue;
            };
            if !holds_payload(&out.set, n) {
                continue;
            }
            let mut left = Vec::with_capacity(ts.len());
            let mut changed = false;
            for (s, near) in ts.iter().zip(near_pairs(ts.iter(), us.iter())) {
                if !near.is_empty() {
                    *self.cx.borrow_mut() = Cx {
                        solve,
                        ..Cx::default()
                    };
                    let cut: Vec<Shape> = near.into_iter().map(|j| us[j].clone()).collect();
                    // Where both are exact the rest is made first, and the kernel's verdict on
                    // its parts decides whether `u` holds the shape ([`Rest::held`]): yes drops
                    // the shape, no leaves the rest. Only where it is undecided is the shape
                    // compared with its near shapes, and a yes of that comparison, which is
                    // sound, drops it; otherwise the rest stands. Proof that the rest holds the
                    // difference: [`Self::shape_rest`], whose choices are made on kernel
                    // types. Complexity tradeoff: the comparison first for every shape goes to
                    // the kernel's test of whether a set of tuples is empty, which grew past n^2
                    // for n shapes each meeting the next (FAIL-types-shape-rest-many-cuts,
                    // sampled); the rest's verdict is one search of the kernel for each part.
                    // Before (PROOF-diff-exact-skip), the rest was taken as the answer where
                    // both were exact, and a part [`Ty::is_empty`] did not prove empty stayed
                    // as a shape: for the empty rest of
                    // `kinds::a_payload_whose_tuple_item_needs_a_split_of_many_components_is_refused`
                    // the difference was not empty, and the comparison said no where the answer
                    // is yes. Checked against the comparison on 1,000 random payloads a run
                    // (`kinds::a_payload_shape_is_within_a_union_exactly_when_its_rest_is_empty`).
                    let exact = s.0.exact.is_some() && cut.iter().all(|c| c.0.exact.is_some());
                    let mut rest = None;
                    if exact_u && exact {
                        let r = self.shape_rest(s, &cut, solve).await;
                        match r.held() {
                            Held::Yes => {
                                changed = true;
                                continue;
                            }
                            Held::No => {
                                left.extend(r.shapes);
                                changed = true;
                                continue;
                            }
                            Held::Refused(_) => rest = Some(r.shapes),
                        }
                    }
                    let one = payload_ty(n, vec![s.clone()]);
                    let near = payload_ty(n, cut.clone());
                    let mut b = Binds::new();
                    let held = self.sub_near(&one, &near, None, &mut b).await;
                    if self.cx.borrow().decided(held) && b.is_empty() {
                        changed = true;
                        continue;
                    }
                    if let Some(rest) = rest {
                        left.extend(rest);
                        changed = true;
                        continue;
                    }
                }
                left.push(s.clone());
            }
            if left.is_empty() {
                out.payloads.remove(*n);
                gone.push(KType::atom_with(n, &KType::top()));
            } else if changed {
                out.payloads.insert((*n).clone(), Some(left));
            }
        }
        if !gone.is_empty() {
            let gone = KType::union_all(gone);
            out.set = &out.set - &gone;
            out.family = &out.family - &gone;
        }
        *self.cx.borrow_mut() = open;
        out.tuples = kept.into();
        out.set = KType::union_all(std::iter::once(out.set).chain(rest));
        out
    }
}

/// Where a component sits in the tuple or payload that holds it: the kernel compares a
/// component only with those at the same place, so a function is compared only with the
/// functions of the other side at its place ([`Forms`]).
#[derive(Clone, PartialEq, Eq, Hash)]
enum Place {
    /// Component `.1` of a row of `.0` components.
    Row(usize, usize),
    /// Component `.3`, items then fields, of a payload of the atom `.0` with `.1` items and
    /// fields whose names hash to `.2`.
    Payload(Arc<str>, usize, u64, usize),
}

/// Where the functions of the two sides are paired ([`PlaceFns::spots`]): a place at one depth
/// of nesting, or a place at every depth.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Spot {
    At(usize, Place),
    Any(Place),
}

/// The functions met at each place of a type's rows and payloads, each once: at each depth of
/// nesting, the rows and payloads of the type itself at depth 0, and at every depth together.
/// A row or payload met at two depths, which a shared node may be, is at no one depth: its
/// places are `shared`, and their functions are under `any` only.
///
/// Before (FAIL-types-tuple-subtype), a place was its length and index alone, so the functions
/// of `(f, (g, int))` at `Place::Row(2, 0)` were `f` and `g`: compared with `(f2, (g2, int))`,
/// two functions of one side, unlike two of the other, met at one place and the comparison
/// was refused ([`Forms::tied`]), and in `(f2, (f, int))` the inner `f` stood beside the
/// outer `f2`, so the `f` of the other side was taken as equal to a function there and not
/// compared with `f2` ([`Comparing::form_verdict`]).
#[derive(Default)]
struct PlaceFns {
    at: HashMap<(usize, Place), HashSet<Arc<Sig>>>,
    any: HashMap<Place, HashSet<Arc<Sig>>>,
    shared: HashSet<Place>,
    /// The rows met with functions at each `Place::Row`, as [`Met`]s ([`PlaceFns::starred`]).
    rows: HashMap<Place, Vec<Met<Row>>>,
    /// The payload shapes met with functions at each `Place::Payload`, as [`Met`]s.
    shapes: HashMap<Place, Vec<Met<Shape>>>,
}

/// A row or payload shape met by [`Forms::fns`] with functions at a place: its depth, none
/// when met at two, and the functions of its component there. A node met at two depths is
/// listed twice, once with each.
struct Met<P> {
    depth: Option<usize>,
    node: P,
    fns: Vec<Arc<Sig>>,
}

/// The node of a [`Met`] by address, so that a node listed twice is read once.
trait Addressed {
    fn address(&self) -> *const ();
}

impl Addressed for Row {
    fn address(&self) -> *const () {
        Arc::as_ptr(&self.0).cast()
    }
}

impl Addressed for Shape {
    fn address(&self) -> *const () {
        self.as_ptr().cast()
    }
}

/// The nodes of `met` at `spot`, each once, with their functions there.
fn met_at<'a, P: Addressed>(
    met: Option<&'a Vec<Met<P>>>,
    spot: &Spot,
) -> Vec<(&'a P, &'a [Arc<Sig>])> {
    let met = met.map_or(&[][..], Vec::as_slice);
    match spot {
        Spot::At(d, _) => (met.iter())
            .filter(|m| m.depth == Some(*d))
            .map(|m| (&m.node, &m.fns[..]))
            .collect(),
        Spot::Any(_) => {
            let mut seen = HashSet::new();
            (met.iter())
                .filter(|m| seen.insert(m.node.address()))
                .map(|m| (&m.node, &m.fns[..]))
                .collect()
        }
    }
}

/// The pairs of functions, one of a node of `left` and one of a node of `right` that may share
/// a value with it ([`Near`]), each pair once, when there are no more of them than functions of
/// the two sides there. None otherwise. Where the pairs form stars (in each pair, the function
/// of one side meets no other function of the other side there) they are never more; so are
/// they where, say, each of two functions of one side meets each of two of the other
/// (FAIL-types-loose-pairing-non-star: before, a spot not starred was paired by
/// [`Forms::tied`] and refused).
///
/// Why the pairs of nodes that may share a value are enough, at a spot where they are found:
/// a function `g` of the expected side holds the mark of a function `f` of the side compared
/// in the form so that a value with that mark at `g`'s place is held there. Such a value of the
/// form compared has the mark at that place through a node holding `f` there; it is held by
/// `g`'s node only if the two nodes share a value, and [`Near`] lists every node that may.
/// So the forms made with only those pairs compared hold the form compared exactly when the
/// forms made with every pair compared do: fewer marks are held only at places no value of the
/// side compared reaches with them. Proof, at every kind of spot (rows and payloads, nested,
/// shared, `_` on either side, marks a set of every name holds nested): COMPLEXITY.md,
/// PROOF-star-pairs, direction 2, which rests on the place lemma ([`Forms::comp`]), the depth
/// of a node ([`Forms::fns`]) and `Near` listing every node not [`apart`]; it uses only that
/// every pair of nodes that may share a value is an edge, not the shape of the edges. The early
/// return on `most` never fires where the edges form stars (the same section, "The pair
/// count"). Tests: `star_pairs_decide_as_every_pair_in_each_kind_of_spot`,
/// `random_unions_of_tuples_with_functions_agree_with_pairing_every_function`,
/// `functions_at_one_place_whose_tuples_meet_two_each_are_decided`.
///
/// Complexity tradeoff (COMPLEXITY.md F124): the pairs are counted as they are found, and more
/// of them than the functions of the two sides ends the search with no more read, so a spot
/// costs O(n) comparisons of functions. What is given up: where the near pairs outnumber the
/// functions, as where each of three functions of one side meets each of three of the other,
/// the spot is paired as before ([`Forms::tied`], [`Comparing::form_verdict`]). Why: pairing
/// every function that meets every function of the other side, `(f_i, int)` against
/// `(g_j, int)`, compares `n^2` pairs,
/// and deciding whether each `f_i` fits some `g_j` is a containment join, which takes about
/// `n^2` unless the Hitting Set conjecture fails (as for [`every_arrow_fits`]). Naive version:
/// every pair at the spot compared, O(n^2); used: the nodes filed by their keys ([`Near`],
/// expected O((l·G + r·H)·w) for groups `G`, `H` of widths `w`, a few in a written union) and at
/// most as many pairs read as functions, O(n) comparisons of functions.
fn star_pairs<P: Placed>(
    left: &[(&P, &[Arc<Sig>])],
    right: &[(&P, &[Arc<Sig>])],
) -> Option<Vec<(Arc<Sig>, Arc<Sig>)>> {
    let most: usize = (left.iter().chain(right)).map(|(_, fs)| fs.len()).sum();
    let groups = Groups::new(left.iter().map(|(p, _)| *p), right.iter().map(|(p, _)| *p));
    let mut near = Near::new(&groups);
    let (mut edges, mut pairs) = (Vec::new(), 0);
    for (l, (_, fs)) in left.iter().enumerate() {
        for r in near.of(l) {
            pairs += fs.len() * right[r].1.len();
            if pairs > most {
                return None;
            }
            edges.push((l, r));
        }
    }
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for (l, r) in edges {
        for f in left[l].1 {
            for g in right[r].1 {
                if seen.insert((f.clone(), g.clone())) {
                    out.push((f.clone(), g.clone()));
                }
            }
        }
    }
    Some(out)
}

/// The pairs of functions to compare at each spot whose pairs of nodes that may share a value
/// are no more than its functions ([`PlaceFns::starred`]).
type Starred = HashMap<Spot, Vec<(Arc<Sig>, Arc<Sig>)>>;

impl PlaceFns {
    /// For each spot where the side compared, `self`, and `whole`, the type compared with,
    /// both have two or more functions, the pairs [`star_pairs`] finds between the nodes of
    /// `self` there and those of `near`, `whole` or the part of it [`Comparing::near_form`]
    /// reads, where they are no more than the functions there (as where they form stars).
    /// Such a spot is decided by comparing those pairs; at the
    /// others with two or more functions a side, [`Forms::tied`] and the skipping of
    /// [`Comparing::form_verdict`] apply.
    fn starred(&self, near: &PlaceFns, whole: &PlaceFns) -> Starred {
        let mut out = HashMap::new();
        for (spot, fs) in self.spots(whole) {
            if fs.len() < 2 || whole.get(&spot).is_none_or(|gs| gs.len() < 2) {
                continue;
            }
            let (Spot::At(_, place) | Spot::Any(place)) = &spot;
            let pairs = match place {
                Place::Row(..) => star_pairs(
                    &met_at(self.rows.get(place), &spot),
                    &met_at(near.rows.get(place), &spot),
                ),
                Place::Payload(..) => star_pairs(
                    &met_at(self.shapes.get(place), &spot),
                    &met_at(near.shapes.get(place), &spot),
                ),
            };
            if let Some(pairs) = pairs {
                out.insert(spot, pairs);
            }
        }
        out
    }

    /// The functions at `spot`.
    fn get(&self, spot: &Spot) -> Option<&HashSet<Arc<Sig>>> {
        match spot {
            Spot::At(d, p) => self.at.get(&(*d, p.clone())),
            Spot::Any(p) => self.any.get(p),
        }
    }

    /// Each function of the type, once for each place it is at.
    fn all(&self) -> impl Iterator<Item = &Arc<Sig>> {
        self.any.values().flatten()
    }

    /// The spots at which the functions of `self`, the side compared, are paired with those of
    /// `other`, each with those functions: each place at each depth, or at every depth where
    /// either side meets a place at two depths. Read from the whole type compared with, so
    /// that a part of it pairs as the whole does ([`Comparing::near_form`]).
    fn spots<'a>(
        &'a self,
        other: &'a PlaceFns,
    ) -> impl Iterator<Item = (Spot, &'a HashSet<Arc<Sig>>)> + 'a {
        let shared = |p: &Place| self.shared.contains(p) || other.shared.contains(p);
        let at = (self.at.iter())
            .filter(move |((_, p), _)| !shared(p))
            .map(|((d, p), fs)| (Spot::At(*d, p.clone()), fs));
        let any = (self.any.iter())
            .filter(move |(p, _)| shared(p))
            .map(|(p, fs)| (Spot::Any(p.clone()), fs));
        at.chain(any)
    }
}

/// Whether the kernel's verdict on a difference says the one side is in the other, or nothing
/// when it refused.
fn held(verdict: Verdict) -> Option<bool> {
    match verdict {
        Verdict::Empty => Some(true),
        Verdict::Inhabited => Some(false),
        Verdict::Refused(_) => None,
    }
}

/// The variables outside the functions of `t` and `other` that stand for a function of
/// `cx.fns`, each bound to that function where it reads alike in every environment
/// ([`Cx::closed`]) and to a token of its own otherwise ([`fn_token`]), with the variable of
/// each function so put ([`Named`]), for [`Comparing::closed_form`]: none where there is no
/// such variable, where [`Comparing::by_form`] makes no form of the two with them put back,
/// or where a token equals a function put back for another variable.
///
/// Why stopping at the first other variable gives what `by_form` of the types put back gives
/// (unless `other` holds the unknown, where `by_form` answers true whatever it holds, and the
/// walk goes on): [`Ty::replace_outside`] keeps a variable that `binds` does not bind where it
/// was, so a variable of `other` at its top is still there and `by_form` stops at its first
/// test; and one in a component of a row or payload shape, at any depth outside functions,
/// leaves that row or shape, and every one holding it, with no exact kernel type
/// (`RowData::exact`), so [`Ty::exact_data`] of its side is none, and [`Forms::fns`] of its
/// side is none, which leaves `by_form` with none on either side: through [`Right::of`] for
/// `other`, through [`Comparing::form_verdict`] for `t`. A variable at the top of `t` stops
/// nothing, as neither reads it. The walk follows [`Ty::vars_outside`]: it enters a row or
/// payload shape only if it holds a variable or the unknown outside functions (`open`), and
/// each once (by number).
///
/// Why `Forms::fns` meets every component this walk reads (BENCH-closed-form-late-variable,
/// the claim FAIL-closed-form-shared-rows-scaling left unproved): a row or shape is `open`
/// exactly when a component is not [`Ty::closed`]; an open row has no kernel type, so no exact
/// one ([`Row::made`]), and an open shape has no exact one ([`Shape::new`]), so
/// [`Node::kept`] is none for each, and [`Node::below`] yields every open row and payload
/// shape of a type (it filters only on `kept`, over the same shapes as
/// [`Ty::payload_shapes`]). `Forms::fns` walks the components of each node it yields, and
/// meets each node at least once with its components walked (a node met again is skipped only
/// after a first visit that walked them), so by induction on depth it reaches every component
/// this walk reaches, and returns none at the first that holds a variable.
///
/// Complexity tradeoff: O(1) while `cx` holds no function ([`Cx::fns`]); else the nodes
/// entered before the first variable that stops it, O(size)
/// at most. The naive walk, every variable of both sides collected before any is looked up,
/// cost O(size) at each comparison whose forms were not made: O(n^2) for a type of n rows
/// compared at each of its n levels (FAIL-closed-form-shared-rows-scaling). What is given
/// up: nothing; the answer is the naive one. Where `cx` holds such a function, a type whose
/// first other variable lies at the end of the walk still costs its size at each comparison,
/// as its [`Cx::read`] did: the order of the comparison is unchanged (8.2 times at 8n for n
/// such levels, `results_with_a_variable_late_beside_closed_functions_are_compared_in_linear_time`).
/// A memo per node within one comparison was not added here: a row read with names made in
/// a scope is a new node at each comparison of function types, so a memo by node would not
/// hit. A row that holds no variable is instead read once with names made outside every
/// scope ([`Cx::kept_rows`]) and compared by [`Comparing::kept_rows_in`] before this walk
/// (PERF-types-shared-row-each-level).
fn closed_binds(cx: &Cx, t: &Ty, other: &Ty) -> Option<(Binds, Named)> {
    if cx.fns.is_empty() {
        return None;
    }
    enum Walk<'a> {
        Row(&'a Row),
        Shape(&'a Shape),
    }
    /// The rows and payload shapes of `c` that hold a variable outside functions, in order.
    fn below<'a>(c: &'a Ty) -> impl Iterator<Item = Walk<'a>> {
        let rows = c.tuples.iter().filter(|r| r.open()).map(Walk::Row);
        rows.chain(c.payload_shapes().filter(|s| s.open).map(Walk::Shape))
    }
    let mut binds = Binds::new();
    let mut named = Named::new();
    // Binds each variable of `c` that stands for a function: to that function where it reads
    // alike in every environment, else to a token of its own ([`fn_token`]). False at the
    // first other variable, when `stops`, and at a token equal to the function or token of
    // another variable (`named`), which only a function written as a token could be.
    let mut look = |c: &Ty, stops: bool| {
        for v in &c.vars {
            match cx.fns.get(v) {
                Some(_) if binds.map.contains_key(v) => {}
                Some((s, _)) => {
                    let closed = cx.closed.contains(v);
                    let f = match closed {
                        true => s.clone(),
                        false => fn_token(v),
                    };
                    use std::collections::hash_map::Entry as At;
                    match named.entry(f.clone()) {
                        At::Occupied(e) if !(closed && e.get().1) => return false,
                        At::Occupied(_) => {}
                        At::Vacant(e) => {
                            e.insert((v.clone(), closed));
                        }
                    }
                    binds.insert(v.clone(), Ty::func(f));
                }
                None if stops => return false,
                None => {}
            }
        }
        true
    };
    let stop = !other.dynamic;
    if !look(other, stop) || !look(t, false) {
        return None;
    }
    let mut entered: HashSet<NodeId> = HashSet::new();
    let mut stack: Vec<Walk> = below(t).chain(below(other)).collect();
    stack.reverse();
    while let Some(w) = stack.pop() {
        let from = stack.len();
        // The components of a row or shape not entered before, in order.
        let (row, shape): (&[Ty], Option<&Shape>) = match w {
            Walk::Row(r) if entered.insert(r.node()) => (&r.0.cs, None),
            Walk::Shape(s) if entered.insert(s.node()) => (&s.items, Some(s)),
            _ => continue,
        };
        let fields = shape.into_iter().flat_map(|s| s.fields.values());
        for c in row.iter().chain(fields) {
            if !look(c, stop) {
                return None;
            }
            stack.extend(below(c));
        }
        stack[from..].reverse();
    }
    (!binds.is_empty()).then_some((binds, named))
}

/// The functions [`closed_binds`] puts in place of the variables read as functions, each with
/// its variable and whether that variable reads alike in every environment ([`Cx::closed`]).
/// Two variables share an entry only where both read alike everywhere and were read from one
/// function.
type Named = HashMap<Arc<Sig>, (Arc<str>, bool)>;

/// A function that stands for the variable `v`, read as a function that does not read alike
/// in every environment, in the forms of [`Comparing::closed_form`]: one arrow of no
/// parameters, named by `v`, so it equals no other variable's token. [`Forms`] reads of a
/// function only its equality and hash, and [`Comparing::form_verdict`] compares a token by
/// the variable it stands for ([`Comparing::fits_named`]), so its arrow is never read.
fn fn_token(v: &Arc<str>) -> Arc<Sig> {
    let mut s = Sig::one(Vec::new(), Vec::new(), Ty::empty());
    s.word = Some(v.clone());
    Arc::new(s)
}

/// What [`Forms`] reads of the type of the expected side: the functions at each place of its
/// rows and payloads, and the marks of the field names of its payloads.
struct Right {
    fns: PlaceFns,
    fields: HashSet<String>,
}

impl Right {
    /// None when `t` holds a variable outside functions ([`Forms::fns`]).
    fn of(t: &Ty) -> Option<Right> {
        let mut fields = HashSet::new();
        let fns = Forms::fns(t, false, &mut fields)?;
        Some(Right { fns, fields })
    }
}

/// What [`Comparing::diff`] reads once of the type each tuple is compared with, for
/// [`Comparing::near_form`].
struct Whole {
    /// Its scalars, atoms with their payloads and kind-wide part as one kernel type, when it
    /// and each of its tuples have an exact kernel type ([`Ty::exact_data`]).
    rest: Option<KType>,
    /// What [`Forms`] reads of it, when it makes its form.
    right: Option<Right>,
}

impl Whole {
    fn of(t: &Ty) -> Whole {
        let rows_exact = t.tuples.iter().all(|r| r.0.exact.is_some());
        Whole {
            rest: rows_exact
                .then(|| payload_set(&t.set, &t.payloads, |_, s| s.0.exact.clone()))
                .flatten(),
            right: Right::of(t),
        }
    }
}

/// A row, or a payload shape of the atom named, met by [`Forms`].
#[derive(Clone, Copy)]
enum Node<'a> {
    Row(&'a Row),
    Shape(&'a Arc<str>, &'a Shape),
}

impl<'a> Node<'a> {
    /// The rows and payload shapes of `c` whose form is not their exact kernel type
    /// ([`Node::kept`]).
    fn below(c: &'a Ty) -> impl Iterator<Item = Node<'a>> {
        let rows = c.tuples.iter().map(Node::Row);
        let shapes = (c.payloads.iter())
            .flat_map(|(n, ss)| ss.iter().flatten().map(move |s| Node::Shape(n, s)));
        rows.chain(shapes).filter(|n| n.kept().is_none())
    }

    /// Its exact kernel type, when that is its form: none when it holds a function, a variable,
    /// the unknown or a payload with fields at any depth, which a form marks, or a set that
    /// holds the atoms of every name it does not list, from which a form cuts the marks.
    fn kept(self) -> Option<&'a KType> {
        let (exact, open_atoms) = match self {
            Node::Row(r) => (&r.0.exact, r.0.open_atoms),
            Node::Shape(_, s) => (&s.exact, s.open_atoms),
        };
        exact.as_ref().filter(|_| !open_atoms)
    }

    /// The node on the side `left`, as [`Forms::made`] keeps it: a shape with the name of its
    /// atom, since its places name it.
    fn key(self, left: bool) -> (*const (), bool, Option<Arc<str>>) {
        match self {
            Node::Row(r) => (Arc::as_ptr(&r.0).cast(), left, None),
            Node::Shape(n, s) => (s.as_ptr().cast(), left, Some(n.clone())),
        }
    }

    /// Its components, each with its place.
    fn comps(self) -> Vec<(Place, &'a Ty)> {
        match self {
            Node::Row(r) => (r.iter().enumerate())
                .map(|(i, c)| (Place::Row(r.len(), i), c))
                .collect(),
            Node::Shape(n, s) => {
                use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
                let names = BuildHasherDefault::<DefaultHasher>::default()
                    .hash_one(s.fields.keys().collect::<Vec<_>>());
                let len = s.items.len();
                (s.items.iter().chain(s.fields.values()).enumerate())
                    .map(|(i, c)| (Place::Payload(n.clone(), len, names, i), c))
                    .collect()
            }
        }
    }
}

/// The normal forms of the two sides of a comparison of scalars, atoms with their payloads
/// and tuples, which hold functions or the unknown: kernel types the kernel decides in the
/// size of the two sides, in place of trying each tuple shape and payload of one side against
/// each of the other.
///
/// Each function of the side compared is a mark of its own ([`mark`]), one for equal
/// functions; each function of the other side holds the marks of the functions at its place
/// that are equal to it or fit it, found before the forms are made ([`Comparing::by_form`]);
/// the unknown of the side compared is every value but the marks of field names; each kernel
/// type a form holds, at every depth, holds a function's mark exactly where it holds every
/// function ([`Forms::level`]), so no mark stands for a value the type does not hold. A payload
/// with fields is its items and fields in name order, then a mark of the names
/// ([`payload_form`]). A variable on either side, or the unknown on the other, is not put in a
/// form: a shape may bind a variable, and the unknown holds any value.
#[derive(Default)]
struct Forms {
    /// The number of each function of the side compared, by equality.
    ids: HashMap<Arc<Sig>, usize>,
    /// The functions of the side compared that each function of the other side holds, by
    /// number, of those it was compared with: a function fits another wherever the two are.
    fits: HashMap<Arc<Sig>, Vec<usize>>,
    /// Each pair of `fits`, so that a number is put in a list once ([`Forms::hold`]).
    held: HashSet<(Arc<Sig>, usize)>,
    /// The form of each node of the rows and shapes met, by [`Node::key`], an address. A
    /// `Forms` lives within one call ([`Comparing::form_verdict`], [`Forms::tie`]) whose two
    /// borrowed types hold every node met, so no key names a freed node; the map is only read
    /// by key, never iterated. So is the visited set of [`Forms::fns`].
    made: HashMap<(*const (), bool, Option<Arc<str>>), KType>,
    /// The names of the marks of the field names of the payloads met on either side.
    fields: HashSet<String>,
    /// Every mark the two forms may hold: of each function of the side compared, [`MERGED`]
    /// and of each set of field names met; none until the functions are numbered.
    marks: Option<KType>,
    /// The marks of the functions of the side compared and [`MERGED`]: every function's mark;
    /// none until the functions are numbered.
    fn_marks: Option<KType>,
    /// Each set that holds the atoms of every name it does not list, with the marks cut out.
    cuts: RefCell<HashMap<KType, KType>>,
    /// Each kernel type met, at any depth, as [`Forms::level`] makes it, or none where it is
    /// not made ([`KType::rewrite_levels`]).
    levels: RefCell<HashMap<KType, Option<KType>>>,
    /// The form of the unknown of the side compared, and of the other side as the last item of
    /// a payload with no fields: every value but the marks of field names ([`Forms::comp`]);
    /// none until the marks are numbered.
    unknown: Option<KType>,
    /// The functions skipped, when the forms are made with every skipped pair taken to fit.
    merged: Option<Merged>,
}

/// The clause of a comparison refused because functions at one place were not all paired
/// ([`Forms::tie`], [`Comparing::form_verdict`]).
const UNPAIRED: &str = "two or more functions at one place of a tuple or an atom's payload meet \
                        two or more functions at that place of the type expected, not all \
                        equal, and the checker does not try every way of pairing them; give the \
                        functions at that place one function type";

/// The pairs of functions [`Comparing::form_verdict`] skips: each function of the side compared
/// equal to one of the other side's at a spot where both sides have two or more is compared
/// with no other there. Forms made with a `Merged` take every skipped pair to fit: each skipped
/// function of the side compared is the one mark [`MERGED`], in place of its own, wherever it
/// is, and each function of the other side at a spot where one was skipped holds that mark.
///
/// Why a false verdict on those forms is a definite no. Let `φ` rename the mark of each skipped
/// function to [`MERGED`], on values. The forms of the side compared made with `Merged` are `φ`
/// of the plain ones (a component's form outside its marks holds no mark, as [`Forms::cut`]
/// takes them from sets of all atoms). If the true forms, with every pair compared, give
/// `A <: B`, then `φ(A) <: φ(B)`, as `φ` is a function on values. A function `g` of the other
/// side holds, in `B`, the marks of the functions that fit it; those compared are in the plain
/// form, and `φ` maps them as the `Merged` form does; those not compared were skipped at a spot
/// where `g` is, whose marks `φ` maps to [`MERGED`], which `g` holds. So `φ(B)` is within the
/// `Merged` form of the other side, and `A <: B` gives the `Merged` verdict true. One mark for
/// every spot, not one each, so that a function skipped at two spots is mapped one way; what is
/// given up is only that a function holding the mark takes skipped functions of other spots
/// too, which can turn a definite no into a refusal, never the reverse.
///
/// Cost: as many functions as the spots list, each kept once, and one more mark in each
/// component of a function; the forms are made once more, the same size.
#[derive(Default)]
struct Merged {
    /// The numbers of the skipped functions of the side compared.
    left: HashSet<usize>,
    /// The functions of the other side at a spot where one was skipped.
    right: HashSet<Arc<Sig>>,
}

/// The name of the mark of every skipped function in forms made with a [`Merged`].
const MERGED: &str = "\u{0}fn skipped";

impl Forms {
    /// The number of the function `f` of the side compared.
    fn id(&mut self, f: &Arc<Sig>) -> usize {
        let next = self.ids.len();
        *self.ids.entry(f.clone()).or_insert(next)
    }

    /// Puts the function numbered `i` among those `g` holds, once.
    ///
    /// Complexity tradeoff: before (FAIL-types-loose-pairing-decided), each number was looked
    /// for in `g`'s list, O(k) for a list of `k`, so a function of the other side holding `n`
    /// functions cost `n^2`; used: a set of the pairs, O(1) expected each, at the cost of a
    /// hash of the signature.
    fn hold(&mut self, g: &Arc<Sig>, i: usize) {
        if self.held.insert((g.clone(), i)) {
            self.fits.entry(g.clone()).or_default().push(i);
        }
    }

    /// The functions at each place of the rows and payloads of `t` and of `other`, or none
    /// when either holds a variable outside functions.
    fn places(&mut self, t: &Ty, other: &Ty) -> Option<(PlaceFns, PlaceFns)> {
        let left = Forms::fns(t, true, &mut self.fields)?;
        Some((left, Forms::fns(other, false, &mut self.fields)?))
    }

    /// The functions at each place of the rows and payloads of `t`, at each depth of nesting
    /// ([`PlaceFns`]): none when it holds a variable outside functions. The names of the marks
    /// of the field names of its payloads go to `fields`.
    ///
    /// Complexity tradeoff (COMPLEXITY.md F201): a row or payload is met at its depth once, and
    /// once more if it is met at a second depth, after which it and every node below it are met
    /// at every depth and not again: O(size) node visits, as with one visit a node. The naive refinement, each
    /// node met once for each depth it is at, costs a shared node its subtree at each depth,
    /// O(size · depth) for `(e, (e, (e, …)))`; what is given up is the depth of a place where a
    /// shared node is, whose functions are then paired at every depth, as all were before.
    fn fns(t: &Ty, left: bool, fields: &mut HashSet<String>) -> Option<PlaceFns> {
        let mut out = PlaceFns::default();
        // Each node met, with its depth, or none once met at two.
        let mut depth_of: HashMap<_, Option<usize>> = HashMap::new();
        let mut stack: Vec<(Node, Option<usize>)> = Node::below(t).map(|n| (n, Some(0))).collect();
        while let Some((n, d)) = stack.pop() {
            let key = n.key(left);
            let d = match (depth_of.get(&key), d) {
                (None, d) => d,
                (Some(None), _) => continue,
                (Some(Some(was)), Some(d)) if *was == d => continue,
                (Some(Some(_)), _) => None,
            };
            depth_of.insert(key, d);
            if let Node::Shape(_, s) = n
                && !s.fields.is_empty()
            {
                fields.insert(fields_mark(&s.fields));
            }
            for (place, c) in n.comps() {
                if !c.vars.is_empty() {
                    return None;
                }
                if !c.fns.is_empty() {
                    match d {
                        Some(d) => (out.at.entry((d, place.clone())).or_default())
                            .extend(c.fns.iter().cloned()),
                        None => {
                            out.shared.insert(place.clone());
                        }
                    }
                    let fns = c.fns.iter().cloned().collect();
                    match n {
                        Node::Row(r) => (out.rows.entry(place.clone()).or_default()).push(Met {
                            depth: d,
                            node: r.clone(),
                            fns,
                        }),
                        Node::Shape(_, s) => {
                            (out.shapes.entry(place.clone()).or_default()).push(Met {
                                depth: d,
                                node: s.clone(),
                                fns,
                            })
                        }
                    }
                    (out.any.entry(place))
                        .or_default()
                        .extend(c.fns.iter().cloned());
                }
                stack.extend(Node::below(c).map(|n| (n, d.map(|d| d + 1))));
            }
        }
        Some(out)
    }

    /// A spot ([`PlaceFns::spots`]) where two or more functions of the side compared, equal to
    /// none of the other side's there, meet two or more of the other side's.
    ///
    /// Complexity tradeoff: which of those fits which is not tried. What is given up: such a
    /// comparison is refused with its own clause ([`Ty::refused`]), though each pair could be
    /// compared. Why: the pairs are the product of the two sides' functions at the place, and
    /// a union of `n` shapes on each side, each with its own function there, would cost `n^2`
    /// comparisons of functions. Structure: `(f, 1) | (g, "a") <: ((int) -> int, int) |
    /// ((String) -> String, String)` with `f` and `g` of other types than those written. Test:
    /// `tests/steps/l01_22_type_representation/kinds.rs`,
    /// `functions_unlike_on_both_sides_at_one_place_are_refused`; COMPLEXITY.md F124. A
    /// complete solution would order the functions at a place by their parameters and results,
    /// so that those a function fits are found by a search in that order, not by trying each.
    /// Naive version: every pair of functions at the place compared, O(n^2) comparisons; used: the
    /// comparison refused at that place, with no function compared there.
    ///
    /// Since FAIL-types-loose-pairing-decided, a spot whose pairs of nodes that may share a
    /// value form stars ([`PlaceFns::starred`], `starred`) is not tied: those pairs are
    /// compared, as many as the functions. Since FAIL-types-loose-pairing-non-star, neither
    /// is a spot where those pairs are no more than the functions, stars or not.
    fn tied(&self, left: &PlaceFns, right: &PlaceFns, starred: &Starred) -> Option<Spot> {
        // The spots of the side compared are looked up, since the other side may be a whole
        // union whose places are many ([`Comparing::near_form`]).
        left.spots(right).find_map(|(spot, fs)| {
            let gs = right.get(&spot)?;
            let unlike = fs.iter().filter(|f| !gs.contains(*f)).count();
            (unlike >= 2 && gs.len() >= 2 && !starred.contains_key(&spot)).then_some(spot)
        })
    }

    /// Why `t <: other`, found false, was refused, if it was for the class [`Forms::tied`]
    /// names and some pairing of the functions could make it true. A false verdict that a
    /// function skipped where one side's functions equal the other's could change is refused
    /// with the same clause, by [`Comparing::form_verdict`].
    ///
    /// The forms are made with each function of `other` holding the mark of every function of
    /// `t`, as if each fit each. A mark more only widens the form of `other`, so when even
    /// those forms give false, every pairing gives false: the comparison is
    /// decided, and false, with no pair tried. Before (FAIL-types-loose-over-refusal), every
    /// comparison of the class was refused, as `(f, 1) | (h, 9) <: (g, 1) | (k, 2)`, with `f`, `h`
    /// unlike `g`, `k`, which no pairing makes true, since no tuple of the type expected holds a
    /// `9`. (The same comparison with `f` written on both sides, where `loose` refused, is now
    /// decided by the second verdict of [`Comparing::form_verdict`].)
    ///
    /// Complexity tradeoff (COMPLEXITY.md F124): one kernel comparison of the two forms, in the
    /// size of the two sides, and no function compared. What is given up: where those forms
    /// give true, the comparison is still refused, though one pairing may make it true, as
    /// `(f, int) | (h, int) | (e, int) <: (g, int) | (k, int) | (m, int)` with `f` fitting
    /// `g`, `h` fitting `k` and `e` fitting `m`; deciding it compares each function at the
    /// spot with each of the other side's there, O(n^2) for `n` shapes a side.
    /// (`(f, 1) | (h, 2) <: (g, 1) | (k, 2)`, whose tuples meet one by one, is not of the
    /// class since FAIL-types-loose-pairing-decided: its pairs form stars; nor, since
    /// FAIL-types-loose-pairing-non-star, is `(f, 1) | (h, 1 | 2) <: (g, 1 | 2) | (k, 1 | 2)`,
    /// whose 4 pairs are no more than its 4 functions, [`PlaceFns::starred`].) Naive version:
    /// those pairs compared,
    /// O(n^2) comparisons of functions; used: one comparison of forms, O(size).
    fn tie(t: &Ty, other: &Ty) -> Option<&'static str> {
        if other.dynamic || !other.vars.is_empty() {
            return None;
        }
        let mut forms = Forms::default();
        let (left, right) = forms.places(t, other)?;
        forms.tied(&left, &right, &left.starred(&right, &right))?;
        // One mark for every function of `t`, which every function of `other` holds: a
        // component of `t` meets only the components of `other` at its place, so this is the
        // form in which each function at a spot fits each of the other side's there, made
        // with one mark in place of the product of the two sides' functions. Proof that a
        // false verdict here is false for every pairing, marks a set of every name holds
        // nested included: COMPLEXITY.md, PROOF-star-pairs, `Forms::tie`.
        forms.ids = left.all().map(|f| (f.clone(), 0)).collect();
        forms.number_marks();
        forms.fits = right.all().map(|g| (g.clone(), vec![0])).collect();
        let a = forms.form(t, true)?;
        let b = forms.form(other, false)?;
        (held(a.subtype_verdict(&b)) != Some(false)).then_some(UNPAIRED)
    }

    /// The normal form of the scalars, atoms with their payloads, kind-wide part and tuples of
    /// `t`, on the side compared if `left`. Its rows and shapes are made bottom up, each once,
    /// on a stack of its own, since they nest as deep as the program.
    fn form(&mut self, t: &Ty, left: bool) -> Option<KType> {
        let mut stack: Vec<(Node, bool)> = Node::below(t).map(|n| (n, false)).collect();
        while let Some((n, ready)) = stack.pop() {
            let key = n.key(left);
            if self.made.contains_key(&key) {
                continue;
            }
            if !ready {
                stack.push((n, true));
                for (_, c) in n.comps() {
                    stack.extend(Node::below(c).map(|n| (n, false)));
                }
                continue;
            }
            // The last item of a payload with no fields sits where a payload with fields of one
            // item fewer has the mark of its field names ([`payload_form`]).
            let end = match n {
                Node::Shape(_, s) if s.fields.is_empty() => s.items.len().checked_sub(1),
                _ => None,
            };
            let ks: Vec<KType> = (n.comps().into_iter().enumerate())
                .map(|(i, (_, c))| self.comp(c, left, end == Some(i)))
                .collect::<Option<_>>()?;
            // A component of no value, as a function of the other side that no function fits,
            // leaves the tuple or payload no value: built as empty, not as a row the kernel
            // would prove empty again in each comparison.
            let k = match n {
                _ if ks.contains(&KType::empty()) => KType::empty(),
                Node::Row(_) => KType::tuple(ks),
                Node::Shape(_, s) => payload_form(ks, &s.fields),
            };
            self.made.insert(key, k);
        }
        self.data(t, left)
    }

    /// The form of `t`'s scalars, atoms with their payloads, kind-wide part and tuples, its
    /// rows and shapes made; each kernel type of `t` read, its set and the exact kernel types
    /// of the rows and shapes kept ([`Node::kept`]), made by [`Forms::level`] at every depth.
    /// None where one is not made.
    fn data(&self, t: &Ty, left: bool) -> Option<KType> {
        let form = |n: Node| match n.kept() {
            Some(k) => self.deep(k),
            None => Some(self.made[&n.key(left)].clone()),
        };
        let shape = |n: &Arc<str>, s: &Shape| form(Node::Shape(n, s));
        let set = payload_set(&self.deep(&t.set)?, &t.payloads, shape)?;
        let rows = (t.tuples.iter().map(|r| form(Node::Row(r)))).collect::<Option<Vec<_>>>()?;
        Some(KType::union_all(std::iter::once(set).chain(rows)))
    }

    /// Numbers the marks ([`Forms::marks`]), once the functions of the side compared are.
    fn number_marks(&mut self) {
        let fns = (0..self.ids.len()).map(|i| format!("\u{0}fn {i}"));
        let fns: Vec<KType> = fns.chain([MERGED.to_string()]).map(|n| mark(&n)).collect();
        self.fn_marks = Some(KType::union_all(fns.iter().cloned()));
        let fields = KType::union_all(self.fields.iter().map(|n| mark(n)));
        self.marks = Some(KType::union_all(fns.into_iter().chain([fields.clone()])));
        self.unknown = Some(&KType::top() - &fields);
    }

    /// The kernel type `k` of a type of either side, made by [`Forms::level`] at every depth
    /// outside functions ([`KType::rewrite_levels`]), each node once per comparison; none where
    /// a node is not made.
    fn deep(&self, k: &KType) -> Option<KType> {
        let mut levels = self.levels.borrow_mut();
        k.rewrite_levels(&mut levels, &mut |n| self.level(n))
    }

    /// The node `n` of a kernel type of either side, the nodes below it made, as its form holds
    /// it: the marks cut from it where it holds the atoms of every name it does not list
    /// ([`Forms::cut`]), and every function's mark ([`Forms::fn_marks`]) put in it where it holds
    /// every function. None where it holds some functions and not others,
    /// which no type written has (a decidable type holds every function or none,
    /// [`KType::functions`]), so the comparison goes shape by shape (`accepts`).
    ///
    /// Why the verdict on forms so made is the verdict on the types (FAIL-forms-nested-marks).
    /// Let `σ` map a value of the side compared to its form: each function to its mark (to
    /// [`MERGED`] when skipped), each payload with fields to its items and fields then the mark
    /// of their names, and the rest as it is. For a kernel type `k` of either side, and every
    /// value `w` of the side compared, `σ(w)` is in `level`'s `k` exactly when `w` is in `k`:
    /// by induction on `k`'s nodes, below first. At an atom name `k` lists, `σ` maps the
    /// payload, made below. At a tuple type `k`'s parts are made of, `σ` maps each component,
    /// made below; a tuple part is its connectives applied to its tuple types, so the part made
    /// again, of the tuple types made again, holds `σ(w)` exactly when the part holds `w`
    /// ([`KType::rewrite_levels`]). A mark is `σ(w)` only for `w` a function of the side
    /// compared, at a place where its form puts it: `k` holds it exactly when `k` holds every
    /// function, and so does the node made, by the marks cut from it and every function's put
    /// in; no value has a mark of field names at a place `k` stands for, since a payload with
    /// fields is never a value of a kernel type ([`Node::kept`]); a value of `k` that is no
    /// mark is `σ` of itself. So a node of every value is made every value but the marks of
    /// field names, as [`Forms::unknown`]: kept whole, a right one would hold the mark of a
    /// payload's field names where a payload with no fields has its last item (the place
    /// lemma of PROOF-star-pairs). So the form of each side holds `σ` of its values,
    /// and the other side's form holds `σ(w)` only for its values `w`: true on the forms is
    /// true on the types. Before, a set of every atom nested in a tuple or a payload kept the
    /// marks, so `((int) -> int, 1) <: (#_, 1) \ (#a, 1)` held, the function's mark in `#_`.
    ///
    /// Complexity tradeoff: each node is made once per comparison ([`Forms::levels`]): a
    /// type of `n` nodes costs `O(n)` nodes read, plus `O(m)` per node cut for `m` marks
    /// ([`Forms::cut`]) and the tuple parts made again where a component changed
    /// (`Part::map_atoms` in the kernel, a union or meet per block). Before, only the outer
    /// set was cut, O(1) more per comparison, and a nested set kept the marks, which made a
    /// wrong yes. Test: `tests/steps/l01_23_groups_and_refusals/judgments.rs`,
    /// `marks_nested_in_sets_of_every_atom_stand_for_no_function`; COMPLEXITY.md F124.
    fn level(&self, n: &KType) -> Option<KType> {
        let every = n.functions_leaf()?;
        let cut = self.cut(n);
        Some(match (every, &self.fn_marks) {
            (true, Some(fns)) => &cut | fns,
            _ => cut,
        })
    }

    /// `set` without the marks, when it holds the atoms of every name it does not list: a
    /// set written `#_` holds no function, so its form holds no mark ([`mark`]).
    ///
    /// Complexity tradeoff: each such set is cut once per comparison, at the cost of the
    /// marks. What is given up: `k` distinct sets of that kind against `m` marks cost `k m`.
    /// Why: the kernel has no set of all atoms whose names start with a NUL, so the marks are
    /// taken out by name, and each set keeps the names it leaves out. Structure: a union of `n`
    /// tuples `(#_ - #a_i, f_i)` against one of `n` functions. Test:
    /// `tests/steps/l01_22_type_representation/kinds.rs`,
    /// `marks_are_cut_from_sets_of_all_atoms`; COMPLEXITY.md F124. A complete solution would
    /// give the kernel a part for marks, which no type written holds.
    /// Naive version, which is the one used: each set cut by each mark by name, O(k·m); with a
    /// kernel part for marks, each set would be cut once, O(k) (inferred).
    fn cut(&self, set: &KType) -> KType {
        let Some(marks) = &self.marks else {
            return set.clone();
        };
        if set.atom_names().is_some() {
            return set.clone();
        }
        (self.cuts.borrow_mut().entry(set.clone()))
            .or_insert_with(|| set - marks)
            .clone()
    }

    /// The form of the component `c`; `end` when it is the last item of a payload with no
    /// fields, where a payload with fields has the mark of their names. None where a kernel
    /// type of it is not made ([`Forms::level`]).
    fn comp(&self, c: &Ty, left: bool, end: bool) -> Option<KType> {
        // The unknown holds any value ([`Ty::sub`]). On the side compared it is every value but
        // the marks of field names ([`Forms::unknown`]): every function's mark among them, so
        // it is held only where every function is. Before (FAIL-forms-nested-marks) it was a
        // mark of its own, which only the unknown of the other side held, and a set of every
        // atom too: so `(_, 1) <: (..) \ (#a, 1)` held, though `(#a, 1)` is a value of `_`.
        // On the other side it is every value, but at `end` not the marks of field names,
        // which there stand for no value but for where a payload's fields end. Before
        // (PROOF-star-pairs) it held them there too, so `#n(1, x: 2) <: #n(1, 2, _)` held: the
        // payload of one item and a field, `(1, 2, fields x)`, met the three items' `(1, 2,
        // _)`. Now a node's form shares no value with that of a node at another place
        // (COMPLEXITY.md, PROOF-star-pairs, the place lemma).
        if c.dynamic {
            return Some(match end || left {
                true => (self.unknown.clone()).expect("the marks are numbered first"),
                false => KType::top(),
            });
        }
        let mut ks = vec![self.data(c, left)?];
        let merged = self.merged.as_ref();
        let fn_mark = |i: &usize| match merged.is_some_and(|m| m.left.contains(i)) {
            true => mark(MERGED),
            false => mark(&format!("\u{0}fn {i}")),
        };
        for f in &c.fns {
            let ids = match left {
                true => std::slice::from_ref(&self.ids[f]),
                false => self.fits.get(f).map_or(&[][..], Vec::as_slice),
            };
            ks.extend(ids.iter().map(fn_mark));
            if !left && merged.is_some_and(|m| m.right.contains(f)) {
                ks.push(mark(MERGED));
            }
        }
        Some(KType::union_all(ks))
    }
}

/// Type variables, each once, in order of first appearance.
// Complexity tradeoff (COMPLEXITY.md F28): the naive collection searches the variables found
// before for each new one, O(v²); a hash set beside the order costs O(1) expected per
// variable, at a second copy of each name's reference.
#[derive(Default)]
pub struct Vars {
    seen: HashSet<Arc<str>>,
    /// The rows and payload shapes [`Ty::vars_outside`] entered, by number: a shared one is
    /// entered once. The set lasts over several walks, whose types may be dropped between
    /// them, so it is keyed by number, which no later node takes, not by address.
    outside: HashSet<NodeId>,
    /// The variables, in order.
    pub order: Vec<Arc<str>>,
}

impl Vars {
    /// Whether `v` is one of them.
    pub fn contains(&self, v: &str) -> bool {
        self.seen.contains(v)
    }
}

impl Ty {
    /// No value.
    pub fn empty() -> Ty {
        Ty {
            set: KType::empty(),
            tuples: Members::new(),
            fns: Members::new(),
            vars: VarSet::new(),
            dynamic: false,
            family: KType::empty(),
            payloads: BTreeMap::new(),
        }
    }

    /// The values of `s`: scalars, atoms, and a kind-wide part.
    pub fn set(s: KType) -> Ty {
        Ty {
            set: s,
            ..Ty::empty()
        }
    }

    /// Every value of `c`.
    pub fn carrier(c: Carrier) -> Ty {
        Ty::set(c.ty())
    }

    /// The values a variable bounded by the mask `m` may stand for when nothing fixes its
    /// carrier: those of each carrier of `m`, and any value with [`OTHER`].
    pub fn of_mask(m: u8) -> Ty {
        if m & OTHER != 0 {
            return Ty::dynamic();
        }
        Ty::set(Carrier::of_mask(m).fold(KType::empty(), |s, c| &s | &c.ty()))
    }

    /// The type of a scalar literal.
    pub fn lit(v: &Value) -> Ty {
        Ty::set(KType::lit(v).expect("a scalar literal"))
    }

    /// The tuple shape `(cs…)`.
    pub fn tuple(cs: Vec<Ty>) -> Ty {
        Ty::of_row(Row::new(cs))
    }

    /// The tuple shape of `row`, or the empty type when a component lists no value.
    pub fn of_row(row: Row) -> Ty {
        if row.0.void {
            return Ty::empty();
        }
        Ty {
            tuples: Members::from(vec![row]),
            ..Ty::empty()
        }
    }

    /// The atom `#name(items, fields)`, or the empty type when a component lists no value.
    pub fn atom_of(name: &str, items: Vec<Ty>, fields: BTreeMap<Arc<str>, Ty>) -> Ty {
        let shape = Shape::new(items, fields);
        if shape.void {
            return Ty::empty();
        }
        let mut t = Ty::set(KType::atom_with(name, &KType::top()));
        t.payloads.insert(name.into(), Some(vec![shape]));
        t
    }

    /// The function `s`.
    pub fn func(s: Arc<Sig>) -> Ty {
        Ty {
            fns: Members::from(vec![s]),
            ..Ty::empty()
        }
    }

    /// The type variable `v`.
    pub fn var(v: Arc<str>) -> Ty {
        let mut t = Ty::empty();
        t.vars.insert(v);
        t
    }

    /// The variable it is, when it is one type variable and nothing else.
    pub fn as_var(&self) -> Option<&Arc<str>> {
        let mut vs = self.vars.iter();
        let v = vs.next()?;
        (vs.next().is_none() && *self == Ty::var(v.clone())).then_some(v)
    }

    /// The unknown.
    pub fn dynamic() -> Ty {
        Ty {
            dynamic: true,
            ..Ty::empty()
        }
    }

    /// Whether it lists no value: the form of [`Ty::empty`], read in O(1). A type for which
    /// this is false may still be empty ([`Ty::is_empty`]).
    pub fn lists_nothing(&self) -> bool {
        self.set.lists_nothing()
            && self.tuples.is_empty()
            && self.fns.is_empty()
            && self.vars.is_empty()
            && !self.dynamic
    }

    /// Whether it is shown to hold no value. A yes is proved; a no is not: the kernel's test
    /// ([`KType::is_empty`]) counts a set it does not prove empty as holding a value, and a
    /// tuple whose components are such sets is kept. Where the answer must be exact, ask the
    /// kernel's verdict on the type's kernel type ([`KType::verdict`]), as the comparison of
    /// payload shapes does (PROOF-diff-exact-skip).
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
            && self.tuples.is_empty()
            && self.fns.is_empty()
            && self.vars.is_empty()
            && !self.dynamic
    }

    /// The union.
    // Complexity tradeoff (COMPLEXITY.md F17): the naive union searches the list built so far
    // for each tuple and function by deep equality, O(T²) for T shapes. The lists are
    // persistent ([`Members`]): `self`'s is shared by the copy, and each shape of `other` is
    // looked up in the set of members `self`'s list keeps, made once for the list and shared
    // with its copies, and pushed if new, O(m log n) for `m` shapes of `other`, so a union with
    // a scalar or a variable costs no walk of `self`'s, and a variable bound to n distinct
    // tuple shapes or functions one at a time costs O(n log n), not O(n^2)
    // (FAIL-types-binding-tuple-shapes-copied). The variables are a persistent set
    // ([`VarSet`]): the smaller set's names go into a copy of the larger, O(m log n)
    // (FAIL-types-binding-union-copied). Kept: an `if`/`else if` chain of n branches of
    // distinct tuple types still builds types of total size Θ(n²), since each `if` holds the
    // union of the branches below it; the cost is the size of the types.
    pub fn union(&self, other: &Ty) -> Ty {
        let mut out = self.clone();
        out.set = &out.set | &other.set;
        out.family = &out.family | &other.family;
        if !self.payloads.is_empty() || !other.payloads.is_empty() {
            out.payloads = join_payloads(&[self, other]);
        }
        for t in &other.tuples {
            out.tuples.insert_new(t.clone());
        }
        for f in &other.fns {
            out.fns.insert_new(f.clone());
        }
        out.vars.add_all(&other.vars);
        out.dynamic |= other.dynamic;
        out
    }

    /// The union of `ts`, built once: joining them one at a time copied the union so far each
    /// time, `O(n²)` in the tuple shapes.
    // Complexity tradeoff (COMPLEXITY.md F22): the naive fold of `union` copies the union so
    // far at each member, O(n²) in the shapes; here the shapes are collected once into lists
    // that keep a set of their members ([`Members::insert_new`]), O(n log n), and the kernel
    // sets are joined in pairs by `KType::union_all`, whose diagrams would be rebuilt n times
    // one at a time. Memory: the sets of the shapes, kept with the lists.
    pub fn union_all<'t>(ts: impl IntoIterator<Item = &'t Ty>) -> Ty {
        let ts: Vec<&Ty> = ts.into_iter().collect();
        let mut out = Ty::empty();
        out.set = KType::union_all(ts.iter().map(|t| t.set.clone()));
        out.family = KType::union_all(ts.iter().map(|t| t.family.clone()));
        if ts.iter().any(|t| !t.payloads.is_empty()) {
            out.payloads = join_payloads(&ts);
        }
        for t in ts {
            for c in &t.tuples {
                out.tuples.insert_new(c.clone());
            }
            for f in &t.fns {
                out.fns.insert_new(f.clone());
            }
            out.vars.add_all(&t.vars);
            out.dynamic |= t.dynamic;
        }
        out
    }

    /// Its atoms.
    pub fn atoms(&self) -> KType {
        &self.set & &atoms()
    }

    /// It without its atoms.
    pub fn without_atoms(&self) -> Ty {
        Ty {
            set: &self.set - &atoms(),
            family: KType::empty(),
            ..self.clone()
        }
    }

    /// It with every atom it holds made a member of a named family, as a `type` declaration
    /// names a union.
    pub fn named(&self) -> Ty {
        Ty {
            family: self.atoms(),
            ..self.clone()
        }
    }

    /// It as a written type reads it: every atom loose, the ascription being the visible act
    /// of re-classifying (sec:failure).
    pub fn written(&self) -> Ty {
        Ty {
            family: KType::empty(),
            ..self.clone()
        }
    }

    /// Its loose atoms: those of no named family.
    pub fn loose(&self) -> KType {
        &self.atoms() - &self.family
    }

    /// What `_` would drop of a value of it (DESIGN.md sec:tour_methods): its loose atoms,
    /// less `named`, the atoms that an `else` in the bound expression writes as its default.
    /// A family's atoms are data, and `_` drops data freely.
    pub fn dropped(&self, named: &KType) -> KType {
        &self.loose() - named
    }

    /// The type of its loose atoms, with their payloads.
    pub fn loose_ty(&self) -> Ty {
        self.of_piece(&Piece::Set(self.loose()))
    }

    /// It without its loose atoms, as `e else d` narrows `e`: what is not an atom, and the
    /// family's atoms. Each step complements only a set that lists no atom names or the
    /// family's, so it costs `O(f log n)` for `f` family atoms of `n`, where `set − loose`
    /// would complement every loose atom.
    // Complexity tradeoff (COMPLEXITY.md F21): the naive `set − loose` builds the complement
    // of every loose atom so far, O(n) per binary operator and O(n²) on a chain of n failure
    // atoms; `(set − atoms) ∪ (set ∩ family)` equals it and complements only the fixed set of
    // all atoms, O(f log n) for f family atoms. Precondition: the family is small beside the
    // loose atoms, as in the chains the checker builds; a large family costs its size.
    pub fn without_loose(&self) -> Ty {
        // A set that holds no atom loses none.
        let set = match self.set.may_hold_atoms() {
            true => &(&self.set - &atoms()) | &(&self.set & &self.family),
            false => self.set.clone(),
        };
        let mut out = Ty {
            set,
            ..self.clone()
        };
        out.prune_payloads();
        out
    }

    /// It without the atoms `k`, as a call passes them by (rule 6 of sec:type_resolution).
    pub fn without(&self, k: &KType) -> Ty {
        let mut out = Ty {
            set: &self.set - k,
            ..self.clone()
        };
        out.prune_payloads();
        out
    }

    /// Drops the payloads of the atoms its set no longer holds (L29-print: a type narrowed to
    /// `String` kept the payload of the `#ioError` it lost, so it differed from `String`).
    fn prune_payloads(&mut self) {
        let set = &self.set;
        self.payloads.retain(|n, _| holds_payload(set, n));
    }

    /// Its pieces: the scalars split by carrier, then the atoms, the other scalars, the
    /// kind-wide part, the tuples, the functions, the variables and the unknown.
    pub fn pieces(&self) -> Vec<Piece> {
        self.pieces_lazily().collect()
    }

    /// [`Ty::pieces`], the tuples, functions and variables read one at a time, so a comparison
    /// that fails at its second piece does not pay for the rest: a component `(Y0 | … | Yn)`
    /// tried against each of n shapes `(X_i,)` and failing at `Y1` costs O(1) a shape, not O(n)
    /// (PERF-types-joined-split-many-components). The scalars are split at once, as
    /// the split of the set makes them together.
    pub fn pieces_lazily(&self) -> impl Iterator<Item = Piece> + '_ {
        let mut out = Vec::new();
        let mut split = self.set.split();
        for c in Carrier::ALL {
            out.extend(split.bases[c.base()].take().map(Piece::Set));
        }
        out.extend(split.atoms.map(Piece::Set));
        // The kind-wide part follows the other scalars, as its own piece.
        if let Some(rest) = split.rest {
            let w = &rest & &wide();
            let rest = &rest - &w;
            if !rest.is_empty() {
                out.push(Piece::Set(rest));
            }
            if !w.is_empty() {
                out.push(Piece::Set(w));
            }
        }
        (out.into_iter())
            .chain(self.tuples.iter().cloned().map(Piece::Tuple))
            .chain(self.fns.iter().cloned().map(Piece::Fn))
            .chain(self.vars.iter().cloned().map(Piece::Var))
            .chain(self.dynamic.then_some(Piece::Dyn))
    }

    /// The numeric carrier a generic literal takes where a value of this type is expected, and
    /// the one a plain literal of another is rejected at: the one carrier its numbers are of,
    /// when it holds numbers of one carrier and no variable or unknown, which could stand for
    /// numbers of another. Its other members (atoms, strings, booleans, tuples, functions) do
    /// not count, so `1n` at `f64 | String` is `1.0`; a type with numbers of two carriers, as
    /// `f64 | rat`, gives none (`check::expected`; DESIGN.md L1.26: the carrier "an operator or
    /// a parameter expects").
    pub fn numeric_carrier(&self) -> Option<Carrier> {
        if !self.vars.is_empty() || self.dynamic {
            return None;
        }
        // Its numbers are those of one numeric carrier: read off one split, where a meet and
        // a subtype test per carrier would build each part anew.
        let s = self.set.split();
        let mut present = Carrier::NUMBERS
            .into_iter()
            .filter(|c| s.bases[c.base()].is_some());
        match (present.next(), present.next()) {
            (Some(c), None) => Some(c),
            _ => None,
        }
    }

    /// Whether it holds no variable and no unknown, outside functions, at any depth, in its
    /// tuples and its atoms' payloads: read at its outer level, since each row and payload
    /// shape keeps whether it holds one.
    pub fn closed(&self) -> bool {
        self.vars.is_empty()
            && !self.dynamic
            && self.tuples.iter().all(|r| !r.open())
            && self.payload_shapes().all(|s| !s.open)
    }

    /// Whether it holds the unknown, outside functions, at any depth, in its tuples and its
    /// atoms' payloads: read at its outer level, as [`Self::closed`] is.
    fn holds_unknown(&self) -> bool {
        self.dynamic
            || self.tuples.iter().any(Row::dynamic)
            || self.payload_shapes().any(|s| s.dynamic)
    }

    /// Whether it holds no function at any depth (a variable or the unknown may still stand
    /// for one): a type whose values the differential oracle compares (step L1.37). A
    /// kind-wide part, `(..)` or `{..}`, holds tuples and structs that hold functions.
    pub fn first_order(&self) -> bool {
        self.held_function().is_none() && self.held_wide().is_none()
    }

    /// A function it may hold, at any depth, in its tuples, its atoms' payloads and its
    /// families' entries; a family is not itself a function, but it holds the functions its
    /// entries hold.
    pub fn held_function(&self) -> Option<&Arc<Sig>> {
        self.function_in(
            |r| r.0.held.as_ref(),
            |s| s.held.as_ref(),
            |e| e.held.as_ref(),
        )
    }

    /// Whether a value of this type may hold a function with needs, one whose folds a later
    /// call decides (`Info::escaping_calls` in zedc-check): a function in it with needs, or one
    /// reached from it at any depth through a tuple's components, an atom's payload (a
    /// struct's fields are one) or a function's results. A family's type is an arrow from key
    /// to value, so its values are a function's results. The results are read as types, not
    /// as [`Sig::holds_needs`] reads them, which looks only at the functions a result holds
    /// directly: `hz` in `hz(f, y) = (f(y), z -> (z, f))` returns a lambda whose result is a
    /// tuple holding `f`, and `h5` in `h5(f, y) = (f(y), [(1, f)])` a family whose values hold
    /// it (row REDUCE-identity-escaping-values). A part that does not say what it holds is
    /// taken as holding such a function: the unknown `_` (`dynamic`), a type variable (`vars`;
    /// `close` leaves the class variables and those of an enclosing function), the kind-wide
    /// part of `set`, every tuple or struct (`k(positional t: (..)) = t` hides `f` in
    /// `k((1, f))`), and a payload listed as not known. Those are every part of a [`Ty`] that
    /// may hold a function, with one gap: an atom of `set` whose name `payloads` does not list
    /// has a payload that is not known, and is taken as holding none. Not proved that it holds
    /// none; no function in a payload can run after the call while this zedc compiles no read
    /// of a payload (`match` and `is #a(x)` are refused as not compiled yet).
    ///
    /// It reads the outer level: each row and payload shape keeps the answer for its
    /// components, and each function the answer for its results ([`Sig::may_hold_needs`]).
    // Complexity tradeoff (FAIL-l01-26-deep-bench-bytes, FAIL-power-returned-n-deep-ratio):
    // the naive version, the checker's `type_holds_needs` walking every type and function
    // reachable from a call's result with sets of those seen at each call, O(v) per call, is
    // Θ(n^2) for n nested calls that each hold the last result in a tuple, or that each return
    // a function returning the one before. Used: the answer kept on each row and shape when
    // made and on each signature when first asked, so this reads the outer level, O(width).
    // Tradeoffs: every row and shape pays for its answer when made, read or not; a ninth
    // `OnceLock` per signature.
    pub fn may_hold_needs(&self) -> bool {
        self.may_hold_needs_outside_fns() || self.fns.iter().any(|s| s.may_hold_needs())
    }

    /// Whether it holds, at any depth, inside functions and payloads too, the unknown beside
    /// another member: a union that [`Absorb`] writes as `_` alone, as the reader reads it.
    /// When it does not, printing it as the reader reads it leaves it as it is.
    // Complexity tradeoff (FAIL-print-absorbed-members-twice): the naive version, the walk of
    // [`Absorb`] to the bottom of the type at each print, is Θ(n^2) for a check that prints
    // each of n nested tuples (33.1 times the bytes at 8n against 7.4 without the walk, on
    // `a_part_held_twice_at_each_level_gives_a_message_of_linear_length`). Used: the answer
    // kept on each row and shape when made and on each signature when first asked
    // ([`Sig::may_absorb`]), so this reads the outer level, O(width), and the walk enters only
    // the parts that answer yes. Tradeoffs: every row and shape pays for its answer when made,
    // read or not; an eleventh `OnceLock` per signature.
    fn may_absorb(&self) -> bool {
        self.may_absorb_outside_fns() || self.fns.iter().any(|s| s.may_absorb())
    }

    /// Whether it is the unknown beside another member at its outer level: a union the reader
    /// reads as `_` alone, unlike `_` itself.
    fn absorbs_here(&self) -> bool {
        self.dynamic
            && !(self.set.lists_nothing()
                && self.tuples.is_empty()
                && self.fns.is_empty()
                && self.vars.is_empty()
                && self.payloads.is_empty())
    }

    /// [`Ty::may_absorb`] for the parts of it other than its functions: its outer level, and
    /// what its rows and payload shapes keep.
    fn may_absorb_outside_fns(&self) -> bool {
        self.absorbs_here()
            || self.tuples.iter().any(|r| r.0.absorbs)
            || self.payload_shapes().any(|s| s.absorbs)
    }

    /// [`Ty::may_hold_needs`] for the parts of it other than its functions: its outer level,
    /// and what its rows and payload shapes keep.
    fn may_hold_needs_outside_fns(&self) -> bool {
        self.dynamic
            || !self.vars.is_empty()
            || !(&self.set & &wide()).is_empty()
            || self.tuples.iter().any(|r| r.0.needs)
            || self.payloads.values().any(|p| match p {
                None => true,
                Some(shapes) => shapes.iter().any(|s| s.needs),
            })
    }

    /// Whether it holds exactly one value that its text writes as that value: one scalar
    /// literal, one bare atom, `#a`, one atom whose payload is one value, `#a(1)`, or one
    /// tuple of such values, `(#a(1), 2)`. A message writes such a type with no article: `x`
    /// is `true`, not `x` is a `true`. It reads the outer level only: each row and payload
    /// shape keeps whether its components are such values, and at most two atom names are read.
    pub fn is_one_value(&self) -> bool {
        if self.dynamic || !self.vars.is_empty() || !self.fns.is_empty() {
            return false;
        }
        match (self.tuples.len(), self.tuples.first()) {
            (1, Some(r)) => {
                self.set.is_empty() && self.payloads.is_empty() && self.family.is_empty() && r.0.one
            }
            (0, _) => self.point().is_some() || self.is_one_atom(),
            _ => false,
        }
    }

    /// Whether its set is one atom and nothing else: the bare atom `#a`, or the atom of one
    /// name whose one listed payload shape is one value, `#a(1)` ([`Ty::is_one_value`]).
    fn is_one_atom(&self) -> bool {
        // Complexity tradeoff (PERF-deep-ops-slow): the set is read by `KType::one_atom` with
        // no type built; building `#a` or `#a(_)` and comparing it cost about 3k
        // instructions for each component of every row made.
        match self.set.one_atom() {
            Some((_, true)) => true,
            Some((n, false)) => {
                let one = matches!(self.payloads.get(n), Some(Some(ss)) if matches!(&ss[..], [s] if s.one));
                one && self.payloads.len() == 1
            }
            None => false,
        }
    }

    /// Its one value, when it is one scalar literal, or one tuple shape each of whose
    /// components is one value, and nothing else: no variable, function, unknown or payload
    /// listed. Each row keeps its own, so this reads the outer level.
    fn point(&self) -> Option<Value> {
        if self.dynamic
            || !self.vars.is_empty()
            || !self.fns.is_empty()
            || !self.payloads.is_empty()
            || !self.family.is_empty()
        {
            return None;
        }
        match (self.set.is_empty(), self.tuples.len(), self.tuples.first()) {
            (false, 0, _) => self.set.scalar(),
            (true, 1, Some(r)) => r.0.point.clone(),
            _ => None,
        }
    }

    /// Its one tuple shape, when it is that shape and nothing else: no set, variable,
    /// function, unknown or payload. O(1).
    pub fn lone_row(&self) -> Option<&Row> {
        let alone = self.set.is_empty()
            && self.vars.is_empty()
            && self.fns.is_empty()
            && !self.dynamic
            && self.payloads.is_empty()
            && self.family.is_empty();
        match (alone, self.tuples.len(), self.tuples.first()) {
            (true, 1, Some(r)) => Some(r),
            _ => None,
        }
    }

    /// A function it may hold, at any depth, that no tuple expression has checked as data, so
    /// that no error has reported it yet.
    pub fn unchecked_function(&self) -> Option<&Arc<Sig>> {
        self.function_in(
            |r| r.0.unchecked.as_ref(),
            |s| s.unchecked.as_ref(),
            |e| e.unchecked.as_ref(),
        )
    }

    /// The first function, not a family, that it holds itself, that `row` gives of one of its
    /// tuples, that `shape` gives of the payload of one of its atoms (DESIGN.md, `#atom(t)`:
    /// a payload may hold a function), or that `entry` gives of the entries of one of its
    /// families ([`Entries`]).
    ///
    /// A row, a payload shape and a family each keep what they hold at any depth, so the walk
    /// reads them and does not enter them: it costs the size of the outer level, however deep
    /// or shared the payloads and entries are.
    fn function_in<'a>(
        &'a self,
        row: impl Fn(&'a Row) -> Option<&'a Arc<Sig>>,
        shape: impl Fn(&'a ShapeData) -> Option<&'a Arc<Sig>>,
        entry: impl Fn(&'a Entries) -> Option<&'a Arc<Sig>>,
    ) -> Option<&'a Arc<Sig>> {
        let own = self.fns.iter().find(|s| !s.data);
        own.or_else(|| self.tuples.iter().find_map(row))
            .or_else(|| self.payload_shapes().find_map(|s| shape(&s.0)))
            .or_else(|| (self.fns.iter().filter(|s| s.data)).find_map(|s| entry(s.entries())))
    }

    /// Whether every value of `self` is in `other`, binding `other`'s variables as needed.
    pub fn sub(&self, other: &Ty, binds: &mut Binds) -> bool {
        let mut cx = Cx::default();
        let ok = comparing!(&mut cx, |c| c.sub_in(self, other, binds));
        cx.decided(ok)
    }

    /// Why `self <: other` was refused, if two members of a union of `self` each needed a
    /// shape of `other` the checker does not single out ([`Comparing::search`]).
    fn unchosen(&self, other: &Ty) -> Option<String> {
        let mut cx = Cx::default();
        comparing!(&mut cx, |c| async {
            c.sub_in(self, other, &mut Binds::new()).await;
        });
        cx.unchosen
    }

    /// [`Self::sub`], each class variable `solve` gives a type read as that type inside the
    /// functions compared.
    pub fn sub_with(&self, other: &Ty, binds: &mut Binds, solve: Solve) -> bool {
        let mut cx = Cx {
            solve: Some(solve),
            ..Cx::default()
        };
        let ok = comparing!(&mut cx, |c| c.sub_in(self, other, binds));
        cx.decided(ok)
    }

    /// [`Self::subtype`], read as [`Self::sub_with`] reads.
    pub fn subtype_with(&self, other: &Ty, solve: Solve) -> bool {
        let mut b = Binds::new();
        self.sub_with(other, &mut b, solve) && b.is_empty()
    }

    /// The kernel type of its values, when it holds no function, variable or unknown at any
    /// depth: its scalars and atoms, and its tuple shapes. A tuple piece that no one shape of
    /// a union holds may still be in the union (boxes that cover a box only together); the
    /// kernel decides that, or refuses with its cause.
    pub fn kernel(&self) -> Option<KType> {
        if !self.fns.is_empty() || !self.vars.is_empty() || self.dynamic {
            return None;
        }
        // A row and a payload shape know whether they hold a variable, the unknown or a
        // function at any depth, so a type that does is refused at its outer level, not at the
        // bottom of its tuples and payloads.
        if (self.tuples.iter()).any(|r| r.open() || r.0.held.is_some())
            || self.payload_shapes().any(|s| s.open || s.held.is_some())
        {
            return None;
        }
        // Each row's kernel type is made once and kept in the row ([`Row::kernel`]).
        // Complexity tradeoff (COMPLEXITY.md K38): the naive version tries each shape in turn
        // against a tuple piece, O(shapes × components) a piece and n² for n shapes, and misses
        // a piece the shapes hold only together; adding the shapes to the union one at a time
        // costs the size of the union so far for each, also n². Used: the shapes joined in pairs
        // (`union_all`), O(n log n), and the kernel decides the piece. Given up: a piece the
        // kernel cannot decide is refused with its cause.
        let shapes = self.tuples.iter().map(Row::kernel);
        let shapes = shapes.collect::<Option<Vec<_>>>()?;
        Some(KType::union_all(
            std::iter::once(self.set.clone()).chain(shapes),
        ))
    }

    /// [`Self::kernel`] with the payloads of its atoms read: `#a(String)` is not in
    /// `#a(int, int)`, where [`Self::kernel`] holds every `#a` with a payload.
    pub fn exact_kernel(&self) -> Option<KType> {
        if !self.fns.is_empty() || !self.vars.is_empty() || self.dynamic {
            return None;
        }
        self.exact_data()
    }

    /// The kernel type of its scalars, atoms with their payloads read, kind-wide part and
    /// tuples, leaving out its own functions, variables and unknown: none when a tuple or
    /// payload holds a function, a variable, the unknown or a payload with fields at any
    /// depth, which only the normal forms of a comparison compare. Each row and shape keeps
    /// its own, so this costs the outer level.
    pub fn exact_data(&self) -> Option<KType> {
        let rows = (self.tuples.iter().map(|r| r.0.exact.clone())).collect::<Option<Vec<_>>>()?;
        let set = payload_set(&self.set, &self.payloads, |_, s| s.0.exact.clone())?;
        Some(KType::union_all(std::iter::once(set).chain(rows)))
    }

    /// A kind-wide part, `(..)` or `{..}`, it holds at any depth outside functions, in its
    /// tuples and its atoms' payloads: every tuple or struct, those that hold a function among
    /// them. Read at its outer level, since each row and shape keeps the one it holds; the
    /// set's own tuples are walked ([`KType::function_part`]), since a meet or difference
    /// with a kind-wide part leaves there the part of a written shape it holds, whose values
    /// hold only what the shape holds (FIX-held-wide-partial-tuples).
    pub fn held_wide(&self) -> Option<KType> {
        let own = &self.set & &wide();
        if !own.is_empty()
            && let Some(w) = own.function_part()
        {
            return Some(w);
        }
        (self.tuples.iter().find_map(|r| r.0.wide.clone()))
            .or_else(|| self.payload_shapes().find_map(|s| s.wide.clone()))
            .or_else(|| (self.fns.iter().filter(|s| s.data)).find_map(|s| s.entries().wide.clone()))
    }

    /// Whether its set, or a row or payload shape at any depth outside functions, holds the
    /// atoms of every name it does not list, as `#_` does: such a set holds the marks of a
    /// normal form ([`mark`]) unless they are cut out ([`Forms::cut`]). Read at its outer level,
    /// since each row and shape keeps its own.
    fn open_atoms(&self) -> bool {
        self.set.atom_names().is_none()
            || self.tuples.iter().any(|r| r.0.open_atoms)
            || self.payload_shapes().any(|s| s.open_atoms)
    }

    /// Whether every value of `self` is in `other`, with no variable bound.
    pub fn subtype(&self, other: &Ty) -> bool {
        if self.var_outside(other) {
            return false;
        }
        let mut b = Binds::new();
        self.sub(other, &mut b) && b.is_empty()
    }

    /// Whether `self` holds a variable with no quote in its name that `other` neither holds
    /// nor reads as anything (`other` is not the unknown), found among the first `m + 1`
    /// variables of `self` for the `m` of `other`, and only when `self` has more than `m`: then
    /// `self <: other` binds a variable or fails, so [`Ty::subtype`] is false.
    ///
    /// Why: [`Comparing::sub_near`] tries each piece of `self` in turn, and the piece `Var(v)`
    /// reaches [`accepts`], which, `other` not being the unknown, holds it without a binding
    /// only where `other.vars` holds `v` (it does not), or `v` is a name of `cx.rigid` or
    /// `cx.fns`. Every name of those two is made by [`Cx::fresh`], `{w}'{count}`, which holds a
    /// quote, and `v` holds none. Otherwise `accepts` unites a variable of `other` with the
    /// piece, or refuses it: the binding is then not empty, or the comparison false. A binding
    /// made is never undone within one comparison: its writers ([`Binds::insert`] and
    /// [`Binds::unite`]) only add, and the two places that replace it ([`Comparing::search`],
    /// [`Comparing::row_in`]) put in a copy of it with more added; [`Binds::remove`],
    /// [`Binds::retain`] and [`Binds::update_each`] are called by no comparison. A piece before
    /// `Var(v)` that fails makes the answer false as well, and [`Cx::decided`] only turns a
    /// true into a false.
    ///
    /// Complexity tradeoff (FAIL-if-chain-params-quadratic): naive version, the comparison
    /// made in full, which lists every piece of `self` and unites each variable of `self` into
    /// the binding of a variable of `other`, O(k log k) for the `k` variables of `self`: an
    /// `if` at depth `k` of a chain of `if`s, each arm a type parameter of its own, asks
    /// whether its `else` type, `k` variables, is within its `then` type, one, so the chain of
    /// `n` cost O(n² log n). Used: the first `m + 1` variables of `self` read, O(m log m),
    /// which is no more than the comparison would read of `other`, and nothing when `self`
    /// has no more variables than `other`. Given up: a variable named with a quote is not
    /// taken, so such a comparison is made in full, as before.
    fn var_outside(&self, other: &Ty) -> bool {
        let m = other.vars.len();
        !other.dynamic
            && self.vars.len() > m
            && (self.vars.iter().take(m + 1)).any(|v| !v.contains('\'') && !other.vars.contains(v))
    }

    /// The kernel's verdict on `self <: other`, on what of `self` is outside `other`: `Empty`
    /// when it holds, `Inhabited` when a value outside was built. On kernel types, or on the
    /// scalar sets when either holds a function, variable, unknown or payload with fields at
    /// any depth; `Empty` when `other` is the unknown.
    pub fn verdict(&self, other: &Ty) -> Verdict {
        if other.dynamic {
            return Verdict::Empty;
        }
        match (self.exact_kernel(), other.exact_kernel()) {
            (Some(a), Some(b)) => a.subtype_verdict(&b),
            _ => self.set.subtype_verdict(&other.set),
        }
    }

    /// When `self <: other` failed: the clause that says why it was not decided, if the check of
    /// its kernel types (its scalar sets, when either holds a function, variable or unknown)
    /// was refused, or, for a function, the clause that names the cover of rule 6 the checker
    /// refuses ([`why_unfit`]), and nothing if it was decided. A refusal claims nothing about
    /// the types, so a message that reads as a counterexample would be wrong.
    pub fn refused(&self, other: &Ty) -> String {
        if let Some(why) = Forms::tie(self, other) {
            return undecided(why);
        }
        if let Some(why) = self.unchosen(other) {
            return undecided(&why);
        }
        match self.verdict(other) {
            Verdict::Refused(r) => self.refused_in_group(other, r),
            // A function that a cover the checker refuses would take ([`why_unfit`]).
            _ => self
                .fns
                .iter()
                .find_map(|s| other.fns.iter().find_map(|q| why_unfit(s, q)))
                .map_or_else(String::new, |why| format!(": {why}")),
        }
    }

    /// The clause for a check of `self <: other` refused for `cause`. When the check rests on a
    /// recursive group (`KType::refusal_site`), a second line names the definition it was
    /// deciding and lists the group's definitions; for a refusal by the group's decider the
    /// reason names the definitions, the cycles, the tuple and a repair (DESIGN.md L1.23). The
    /// definitions carry no source place until recursive `type` declarations reach the
    /// compiler (L2.5), so they are written out.
    fn refused_in_group(&self, other: &Ty, cause: Refusal) -> String {
        let site = match (self.exact_kernel(), other.exact_kernel()) {
            (Some(a), Some(b)) => a.subtype_refusal_site(&b, cause),
            _ => self.set.subtype_refusal_site(&other.set, cause),
        };
        let Some(site) = site else {
            return undecided(&cause.message());
        };
        let why = site.detail.unwrap_or_else(|| cause.message());
        let mut out = undecided(&why);
        out += &format!(
            "\n  the check reads the recursive type `{}`, defined by:",
            site.head
        );
        for d in &site.defs {
            out += &format!("\n    {d}");
        }
        out
    }

    /// The meet with `t`, as an `is` test narrows: what of `self` is also in `t`.
    pub fn meet(&self, t: &Ty) -> Ty {
        if !self.meets_parts(t) {
            return self.meet_rest(t, Vec::new(), BTreeMap::new());
        }
        let memo = RefCell::default();
        let pairs = Pairs {
            stack: Stack::default(),
            memo: &memo,
        };
        pairs.stack.run(pairs.meet(self, t))
    }

    /// Whether its meet with `t` meets parts of the two side by side: when both have tuples,
    /// or both list the payloads of an atom of one name ([`Self::listed_with`]).
    fn meets_parts(&self, t: &Ty) -> bool {
        (!self.tuples.is_empty() && !t.tuples.is_empty()) || self.listed_with(t).next().is_some()
    }

    /// The atom names whose payloads both it and `t` list, each with the two lists of shapes,
    /// in name order. A lookup in `t` per name it lists.
    fn listed_with<'a>(
        &'a self,
        t: &'a Ty,
    ) -> impl Iterator<Item = (&'a Arc<str>, &'a [Shape], &'a [Shape])> + 'a {
        (self.payloads.iter()).filter_map(|(n, xs)| match (xs, t.payloads.get(n)) {
            (Some(xs), Some(Some(ys))) => Some((n, &xs[..], &ys[..])),
            _ => None,
        })
    }

    /// [`Self::meet`] with `met`, the meets of the pairs of its tuples and `t`'s, and `shapes`,
    /// for each atom name both list the payloads of ([`Self::listed_with`]), the meets of the
    /// pairs of their shapes.
    fn meet_rest(
        &self,
        t: &Ty,
        mut met: Vec<Row>,
        mut shapes: BTreeMap<Arc<str>, Vec<Shape>>,
    ) -> Ty {
        // A side holding `_` is every value, whatever it holds beside it (A92), so the meet is
        // the other side. Before (FAIL-types-meet-key-arrows-not-within), only `t` was read so;
        // `(_ | F) & G` was `(F & G) | G`, and where `F` and `G` take the same parameters,
        // `F & G` is their overload, which is not within `G`.
        if t.dynamic {
            return self.clone();
        }
        if self.dynamic {
            return t.clone();
        }
        let mut out = Ty::set(&self.set & &t.set);
        // The payloads of an atom name: met shape by shape where both list them, so that
        // `#a(bool) & #a(int)` has no `#a` with a payload; one side's where only it lists
        // them, since the other holds that atom with any payload or not at all (and then the
        // set has lost it). Before (READ-atom-meet), its own payloads were kept whatever `t`
        // listed, and `#a(bool) & #a(int)` was read as `#a(bool)`.
        let mut gone = BTreeSet::new();
        for (a, b) in [(self, t), (t, self)] {
            for (n, xs) in &a.payloads {
                if out.payloads.contains_key(n) || gone.contains(n) {
                    continue;
                }
                let made = match (xs, b.payloads.get(n)) {
                    (Some(_), Some(Some(_))) => {
                        let m = shapes
                            .remove(n)
                            .expect("the shapes both sides list are met");
                        if m.is_empty() {
                            gone.insert(n);
                            continue;
                        }
                        Some(m)
                    }
                    (Some(xs), _) => Some(xs.clone()),
                    (None, Some(Some(ys))) => Some(ys.clone()),
                    (None, _) => None,
                };
                out.payloads.insert(n.clone(), made);
            }
        }
        if !gone.is_empty() {
            let gone = gone.into_iter().map(|n| KType::atom_with(n, &KType::top()));
            out.set = &out.set - &KType::union_all(gone);
        }
        out.family = &self.family & &out.set;
        // A kind-wide part of one side keeps the other's shapes it holds whole; of a shape it
        // holds in part, the part goes to the set, where the kernel holds it exactly. A shape
        // with no kernel type is kept, which may be more than the meet. The shape's kernel type
        // is the one with its atoms' payloads read, where it has one, so that the part in the
        // set holds `#a(1)` and not `#a(..)`, which may hold a function (`Self::held_wide`).
        for (a, b) in [(self, t), (t, self)] {
            let w = &b.set & &wide();
            if w.is_empty() {
                continue;
            }
            for cs in &a.tuples {
                match cs.0.exact.clone().or_else(|| cs.kernel()) {
                    Some(k) if k.subtype(&w) => met.push(cs.clone()),
                    Some(k) => out.set = &out.set | &(&k & &w),
                    None => met.push(cs.clone()),
                }
            }
        }
        // Complexity tradeoff (COMPLEXITY.md F17): repeated shapes dropped through a hash set,
        // O(m) expected for m met shapes, where a search of the kept list was O(m²).
        let mut have = HashSet::new();
        let first: Vec<bool> = met.iter().map(|cs| have.insert(cs)).collect();
        out.tuples.extend(
            met.into_iter()
                .zip(first)
                .filter_map(|(cs, f)| f.then_some(cs)),
        );
        out.fns = self.fns_met(t).into();
        out.prune_payloads();
        if !self.vars.is_empty() {
            out = out.union(t);
        }
        out
    }

    /// The functions of its meet with `t`: for each of its functions and each of `t`'s that
    /// takes the same parameters, their meet ([`Domains::meet`]), or the one function where the
    /// two are equal. A function of one parameter list and a function of another share no value
    /// ([`fits_sig`]), so such a pair gives nothing. Before (FAIL-types-meet-function-union),
    /// its own functions were kept whenever `t` had any, and `(rat -> #b) & ((bool -> ()) |
    /// String)` was read as `rat -> #b`.
    // Complexity tradeoff (COMPLEXITY.md F200): `t`'s functions are filed by parameter list in
    // a hash map, O(m) expected for m functions, and each of the n functions of `self` is paired
    // with those of its list only, so the cost is O(n + m) plus the pairs made, which are the
    // meet itself. The naive method compares each of the n·m pairs, O(n·m) also where no two
    // functions take the same parameters and the meet has no function. What each function's
    // arrows say of its domain ([`Domains`]) is worked out once for each function, not once for
    // each pair.
    fn fns_met(&self, t: &Ty) -> Vec<Arc<Sig>> {
        if self.fns.is_empty() || t.fns.is_empty() {
            return Vec::new();
        }
        let mut by_params: HashMap<ParamList, Vec<(&Arc<Sig>, Domains)>> = HashMap::new();
        for q in &t.fns {
            let entry = (q, Domains::of(q));
            by_params.entry(q.param_list()).or_default().push(entry);
        }
        let mut have = HashSet::new();
        let mut out = Vec::new();
        for s in &self.fns {
            let Some(qs) = by_params.get(&s.param_list()) else {
                continue;
            };
            let ds = Domains::of(s);
            for (q, dq) in qs {
                let m = match s == *q {
                    true => Some(s.clone()),
                    false => Domains::meet((s, &ds), (q, dq)).map(Arc::new),
                };
                if let Some(m) = m
                    && have.insert(m.clone())
                {
                    out.push(m);
                }
            }
        }
        out
    }

    /// What of `self` is not in `t`, as `is not` narrows: scalars are subtracted, and so is
    /// all of `t` from the kind-wide part when `t` has a kernel type; tuples wholly inside `t`
    /// are dropped, a tuple that `t` holds in part leaves its rest in the set, less `t`'s
    /// kind-wide part and the tuples of `t` near it, and the other tuples are kept. The
    /// payload shapes of an atom whose payloads `t` lists are dropped as tuples are, and the
    /// atom with them when none is left.
    pub fn diff(&self, t: &Ty) -> Ty {
        self.diff_in(t, None)
    }

    /// [`Self::diff`], a tuple compared with `t` as [`Self::sub_with`] compares: each class
    /// variable `solve` gives a type read as that type inside the functions it holds.
    pub fn diff_with(&self, t: &Ty, solve: Solve) -> Ty {
        self.diff_in(t, Some(solve))
    }

    /// [`Self::diff`], with the resolver of the comparisons, if any.
    fn diff_in(&self, t: &Ty, solve: Option<Solve>) -> Ty {
        comparing!(&mut Cx::default(), |c| c.diff(self, t, solve))
    }

    /// `self` with its variables replaced by their bindings.
    pub fn subst(&self, binds: &Binds) -> Ty {
        match binds.is_empty() {
            true => self.clone(),
            false => {
                let made = Made::default();
                rebuild_ty(&mut Subst { binds, made }, self)
            }
        }
    }

    /// `self` with its variables replaced by `binds` at every depth, inside the functions it
    /// holds too; not inside the types it puts in their place, which may hold the variables
    /// themselves.
    pub fn replace(&self, binds: &Binds) -> Ty {
        self.replace_in(binds, Mode::Replace)
    }

    /// `self` with the variables `names` gives other names, at every depth, inside the
    /// functions it holds too, their own variables among them: each value of `names` is one
    /// variable, and no two keys share one.
    pub fn renamed(&self, names: &Binds) -> Ty {
        self.replace_in(names, Mode::Rename)
    }

    /// `self` with its variables replaced by `binds` outside the functions it holds: the
    /// functions are kept as they are, and so is a tuple that holds no variable outside them.
    pub fn replace_outside(&self, binds: &Binds) -> Ty {
        self.replace_in(binds, Mode::Outside)
    }

    /// [`Ty::replace`], or as `mode` says.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Ty {
        match binds.is_empty() {
            true => self.clone(),
            false => rebuild_ty(&mut Replacer::new(binds, mode), self),
        }
    }

    /// The type of its piece `p` alone, with the payloads of the atoms `p` holds.
    pub fn of_piece(&self, p: &Piece) -> Ty {
        let mut out = p.ty();
        if let Piece::Set(s) = p {
            out.payloads = self
                .payloads
                .iter()
                .filter(|(n, _)| holds_payload(s, n))
                .map(|(n, ss)| (n.clone(), ss.clone()))
                .collect();
        }
        out
    }

    /// Its payloads with each shape replaced by what `f` makes of it.
    fn map_payloads(
        &self,
        mut f: impl FnMut(&Shape) -> Shape,
    ) -> BTreeMap<Arc<str>, Option<Vec<Shape>>> {
        self.payloads
            .iter()
            .map(|(n, ss)| {
                let ss = ss.as_ref().map(|ss| ss.iter().map(&mut f).collect());
                (n.clone(), ss)
            })
            .collect()
    }

    /// The shapes of its atoms' payloads.
    fn payload_shapes(&self) -> impl Iterator<Item = &Shape> {
        self.payloads.values().flatten().flatten()
    }

    /// What the payloads of its known atoms named `n` hold: their shapes, or `None` where that
    /// is not known. Its type variables and the unknown are not looked at, so the caller adds
    /// what they hold. The shapes are borrowed: a pattern asks once for each of its fields, and
    /// a copy of a payload with as many fields made the pattern quadratic in them.
    pub fn shapes(&self, n: &str) -> Option<&[Shape]> {
        match self.payloads.get(n) {
            Some(s) => s.as_deref(),
            None if holds_payload(&self.set, n) => None,
            None => Some(&[]),
        }
    }

    /// Every variable in it at any depth, as sets: at the cost of the rows and payload shapes
    /// that hold one, each entered once, since each function keeps its own.
    pub fn var_facts(&self) -> VarFacts {
        let mut f = VarFacts::default();
        f.tys([self], &mut Added::default());
        f
    }

    /// Whether it holds a variable at any depth, inside functions and payloads too: at the cost
    /// of its outer level, since each row, payload shape and function keeps whether it holds
    /// one.
    pub fn holds_vars(&self) -> bool {
        !self.vars.is_empty()
            || self.tuples.iter().any(Row::holds_vars)
            || self.payload_shapes().any(Shape::holds_vars)
            || self.fns.iter().any(|s| !s.bits().is_empty())
    }

    /// Every variable in it, in order of first appearance.
    ///
    /// A type nests as deep as the program, so the walk keeps its own stack; rows and payload
    /// shapes are shared, so it enters each once. The address of a row or shape only tells
    /// whether it was entered, and each is marked when it is entered, in the order a recursive
    /// walk would enter it: one entered once more adds no variable, so the order does not
    /// depend on the sharing. A function it holds is entered once as well, and one whose order
    /// of variables is already kept ([`Sig::vars_order`]) gives that order in place of being
    /// entered.
    pub fn vars_in(&self, out: &mut Vars) {
        vars_of(std::iter::once(self), out);
    }

    /// It with each scalar it holds, at every depth outside the functions it holds, widened to
    /// every value of its carrier: `1 | 2.5` is `int | f64`, and `(1, "a")` is `(int, String)`.
    /// Atoms, payloads, functions, variables and the kind-wide part stay as they are. Two
    /// types have a common carrier where their widenings meet ([`Ty::meets`]). Each row and
    /// payload shape is widened once, on the walk's own stack (`rebuild`), so the cost is
    /// the number of distinct rows and shapes, however many paths lead to them.
    pub fn carriers(&self) -> Ty {
        rebuild_ty(&mut Widen::default(), self)
    }

    /// It with each function it holds outside functions, itself or at any depth in its tuples
    /// and its atoms' payloads, replaced by what `each` makes of it; the functions are not
    /// entered, so one a function returns is left to that function. A family that holds a
    /// function in its keys or entries ([`Sig::holds_fn_as_data`]) is data that holds it, as a
    /// tuple is: it is entered and made anew, and is not given to `each` (row
    /// FAIL-family-lambda-calls-param); another family is a function here. A row or payload
    /// shape that holds no function is kept whole, and each other, and each family entered, is
    /// made once, on the walk's own stack (`rebuild`), so the cost is the number of distinct
    /// rows, shapes and families that hold a function, plus one call of `each` for each
    /// function met (one shared by two rows is met twice).
    pub fn with_held_fns(&self, each: impl FnMut(&Arc<Sig>) -> Arc<Sig>) -> Ty {
        let made = Made::default();
        let families = HashMap::new();
        rebuild_ty(
            &mut HeldFns {
                each,
                made,
                families,
            },
            self,
        )
    }

    /// Each function it holds outside functions, as [`Ty::with_held_fns`] meets them: itself,
    /// or at any depth in its tuples, its atoms' payloads and the keys and entries of the
    /// families that hold a function ([`Sig::holds_fn_as_data`]), which are entered and not
    /// given to `each`; another family is given to `each` and not entered. Only rows and
    /// payload shapes that hold a function are entered, each once (by number, as
    /// [`Ty::vars_outside`] does), and each family once (by address, within this call, which
    /// borrows `self`, so no address names a freed family), on the walk's own stack, so the
    /// cost is the number of distinct such rows, shapes and families, plus one call of `each`
    /// per function met.
    pub fn each_held_fn<'a>(&'a self, each: impl FnMut(&'a Arc<Sig>)) {
        self.walk_held(each, |_| {});
    }

    /// [`Ty::vars_outside`] of it and of each key and entry type of the families
    /// [`Ty::each_held_fn`] enters: the variables a value of it holds outside the functions
    /// that walk meets, which no one of them owns.
    pub fn vars_outside_held(&self, out: &mut Vars) {
        self.vars_outside(out);
        self.walk_held(|_| {}, |t| t.vars_outside(out));
    }

    /// [`Ty::each_held_fn`], with `part` given each key and entry type of each family entered.
    fn walk_held<'a>(&'a self, mut each: impl FnMut(&'a Arc<Sig>), mut part: impl FnMut(&'a Ty)) {
        enum Walk<'a> {
            Ty(&'a Ty),
            Row(&'a Row),
            Shape(&'a Shape),
        }
        let mut entered: HashSet<NodeId> = HashSet::new();
        let mut families: HashSet<*const Sig> = HashSet::new();
        let mut stack = vec![Walk::Ty(self)];
        while let Some(w) = stack.pop() {
            match w {
                Walk::Row(r) => {
                    if entered.insert(r.node()) {
                        stack.extend(r.iter().map(Walk::Ty));
                    }
                }
                Walk::Shape(s) => {
                    if entered.insert(s.node()) {
                        stack.extend(s.items.iter().chain(s.fields.values()).map(Walk::Ty));
                    }
                }
                Walk::Ty(t) => {
                    for s in &t.fns {
                        if !s.holds_fn_as_data() {
                            each(s);
                        } else if families.insert(Arc::as_ptr(s)) {
                            let parts = (s.arrows.iter())
                                .flat_map(|a| a.params.iter().chain(std::iter::once(&a.result)));
                            for p in parts {
                                part(p);
                                stack.push(Walk::Ty(p));
                            }
                        }
                    }
                    stack.extend(
                        t.tuples
                            .iter()
                            .filter(|r| r.0.held.is_some())
                            .map(Walk::Row),
                    );
                    let holding = t.payload_shapes().filter(|s| s.held.is_some());
                    stack.extend(holding.map(Walk::Shape));
                }
            }
        }
    }

    /// It with each class variable `solve` gives a type replaced by that type at every depth,
    /// each signature it holds settled once ([`Sig::settle`]). A tuple that holds no variable
    /// and no function is kept whole.
    pub fn settle(&self, solve: Solve) -> Ty {
        let made = vec![Made::default()];
        rebuild_ty(&mut Settle { solve, made }, self)
    }

    /// Every variable in it outside the functions it holds, in order of first appearance: a
    /// tuple or payload that holds none there is not entered, nor is one `out` has entered.
    ///
    /// A type nests as deep as the program, so the walk keeps its own stack, and marks each
    /// row and shape when it enters it, in the order a recursive walk would.
    pub fn vars_outside(&self, out: &mut Vars) {
        enum Walk<'a> {
            Ty(&'a Ty),
            Row(&'a Row),
            Shape(&'a Shape),
        }
        let mut stack = vec![Walk::Ty(self)];
        while let Some(w) = stack.pop() {
            let from = stack.len();
            match w {
                Walk::Row(r) => {
                    if out.outside.insert(r.node()) {
                        stack.extend(r.iter().map(Walk::Ty));
                    }
                }
                Walk::Shape(s) => {
                    if out.outside.insert(s.node()) {
                        stack.extend(s.items.iter().chain(s.fields.values()).map(Walk::Ty));
                    }
                }
                Walk::Ty(t) => {
                    for v in &t.vars {
                        if out.seen.insert(v.clone()) {
                            out.order.push(v.clone());
                        }
                    }
                    stack.extend(t.tuples.iter().filter(|r| r.open()).map(Walk::Row));
                    let open = t.payload_shapes().filter(|s| s.open);
                    stack.extend(open.map(Walk::Shape));
                }
            }
            stack[from..].reverse();
        }
    }

    /// Whether the value `v` is in it; a variable or the unknown holds every value.
    pub fn contains(&self, v: &Value) -> bool {
        self.contains_here(v).unwrap_or_else(|items| {
            let memo = RefCell::default();
            let filed = RefCell::default();
            let pairs = Pairs {
                stack: Stack::default(),
                memo: &memo,
            };
            pairs.stack.run(pairs.contains(self, items, &filed))
        })
    }

    /// Whether the value `v` is in it, when that is known without reading its tuples: unless
    /// `v` is a tuple outside its set and it has a tuple of `v`'s length, whose components
    /// are given to be read.
    fn contains_here<'v>(&self, v: &'v Value) -> Result<bool, &'v Items> {
        if self.dynamic || !self.vars.is_empty() {
            return Ok(true);
        }
        Ok(match v {
            Value::Tuple(items) => {
                let here = self.set.contains(v);
                if !here && self.tuples.iter().any(|cs| cs.len() == items.len()) {
                    return Err(items);
                }
                here
            }
            Value::Family(_) => self.fns.iter().any(|s| s.data),
            Value::Path(_) => !self.fns.is_empty() || self.set.contains(v),
            _ => self.set.contains(v),
        })
    }

    /// Whether `self` and `other` may share a value.
    pub fn meets(&self, other: &Ty) -> bool {
        self.meets_here(other).unwrap_or_else(|| {
            let memo = RefCell::default();
            let pairs = Pairs {
                stack: Stack::default(),
                memo: &memo,
            };
            pairs.stack.run(pairs.meets(self, other))
        })
    }

    /// Whether `self` and `other` may share a value, when that is known without reading their
    /// tuples, which it is unless each has a tuple of a length the other has and nothing else
    /// of them meets.
    fn meets_here(&self, other: &Ty) -> Option<bool> {
        if !self.closed() || !other.closed() {
            return Some(true);
        }
        // A shape meets the other side's kind-wide part when the kernel finds a common value;
        // a shape with no kernel type may.
        let wide_meets = |a: &Ty, b: &Ty| {
            let w = &b.set & &wide();
            !w.is_empty()
                && a.tuples
                    .iter()
                    .any(|cs| cs.kernel().is_none_or(|k| !(&k & &w).is_empty()))
        };
        if !(&self.set & &other.set).is_empty()
            || wide_meets(self, other)
            || wide_meets(other, self)
            || (!self.fns.is_empty() && !other.fns.is_empty())
        {
            return Some(true);
        }
        if self.tuples.is_empty() || other.tuples.is_empty() {
            return Some(false);
        }
        let lengths: HashSet<usize> = other.tuples.iter().map(|b| b.len()).collect();
        match self.tuples.iter().any(|a| lengths.contains(&a.len())) {
            true => None,
            false => Some(false),
        }
    }
}

/// A walk of the tuples of two types, or of a type and a value, side by side: [`Ty::meet`],
/// [`Ty::meets`] and [`Ty::contains`]. Tuples nest as deep as the program, and each recursed
/// once a level (100,000 levels overflowed a 2 MiB stack), so a pair of components whose
/// answer needs their own tuples is walked in a frame of its own ([`Stack`]), in the order the
/// recursion took. A pair of nodes shared at many places is walked once: its answer is kept
/// by the addresses of the two, which stay put while both are borrowed, so a type with `2^n`
/// paths through `n` tuples costs `O(n)` pairs, not `2^n`.
///
/// Complexity tradeoff: naive version, plain recursion over both types as trees, O(paths),
/// `2^n` for `n` shared tuples (n = 2,000 did not finish in 60 s), and a stack overflow at
/// 100,000 levels. Used: a heap frame per pair of components that both hold tuples, and the
/// memo by the pair's addresses, O(distinct pairs of nodes) frames and lookups. Tradeoffs:
/// the memo's memory, one entry per pair walked, for the whole walk; keying by address is
/// sound only because both operands stay borrowed until the walk ends, so no recorded node is
/// freed or its address reused; each frame is a boxed future, a constant factor over a stack
/// frame, as measured at [`Comparing`]. COMPLEXITY.md row F128.
struct Pairs<'m, K, V> {
    stack: Stack<'m>,
    /// The answer for each pair walked, by the addresses of the two, both borrowed until the
    /// walk ends (above); only read by key, never iterated.
    memo: &'m RefCell<HashMap<K, V>>,
}

impl<'m, K: std::hash::Hash + Eq + Copy + 'm, V: Clone + Unpin + 'm> Pairs<'m, K, V> {
    /// The answer kept for `key`, or the one `walk` makes in a frame of its own, then kept.
    fn kept<F: Future<Output = V> + 'm>(
        &'m self,
        key: K,
        walk: impl FnOnce() -> F + 'm,
    ) -> Deep<'m, V> {
        if let Some(v) = self.memo.borrow().get(&key) {
            return Stack::ready(v.clone());
        }
        self.stack.call(move || async move {
            let v = walk().await;
            self.memo.borrow_mut().insert(key, v.clone());
            v
        })
    }
}

impl<'m> Pairs<'m, (*const Ty, *const Ty), Ty> {
    /// [`Ty::meet`] of `a` and `t`, which both hold tuples or both list the payloads of an atom
    /// of one name ([`Ty::meets_parts`]).
    async fn meet(&'m self, a: &'m Ty, t: &'m Ty) -> Ty {
        // A side holding `_` is every value, so the meet is the other side ([`Ty::meet_rest`]).
        if t.dynamic {
            return a.clone();
        }
        if a.dynamic {
            return t.clone();
        }
        let mut met = Vec::new();
        // Only the pairs of tuples that may share a value are met ([`near_pairs`]): the meet of
        // any other pair has an empty component and is left out, so the tuples and their order
        // are those of meeting every pair of one length.
        for (r, near) in a.tuples.iter().zip(near_pairs(&a.tuples, &t.tuples)) {
            for s in near.into_iter().map(|j| &t.tuples[j]) {
                if let Some(cs) = self.components(r.iter().zip(s.iter())).await {
                    met.push(Row::new(cs));
                }
            }
        }
        // The payloads of each atom name both list, met the same way: only shapes with as
        // many items and the same field names share a value, so they are grouped by those
        // first, and in each group only the pairs [`near_pairs`] gives are met.
        // Complexity tradeoff (COMPLEXITY.md F144): the naive meet tries each pair of shapes,
        // O(l·r) for l and r shapes of the name (60.9 times the bytes at 8 times the shapes in
        // the negative control); grouping in a hash map and filing each group as tuples are
        // filed (F127) meets only the pairs that may share a value, O((l·G + r·H)·w + p) as
        // for rows, at the cost of the group index and of the class keys each shape keeps.
        let mut shapes = BTreeMap::new();
        for (n, xs, ys) in a.listed_with(t) {
            let key = |s: &'m Shape| (s.items.len(), s.fields.keys().collect::<Vec<_>>());
            let mut index: FMap<(usize, Vec<&Arc<str>>), usize> = FMap::default();
            // Each group's shapes of `xs` and of `ys`.
            let mut groups: Vec<(Vec<&Shape>, Vec<&Shape>)> = Vec::new();
            for y in ys {
                let g = *index.entry(key(y)).or_insert_with(|| {
                    groups.push((Vec::new(), Vec::new()));
                    groups.len() - 1
                });
                groups[g].1.push(y);
            }
            // For each shape of `xs`, its group and its place in the group.
            let mut of = Vec::with_capacity(xs.len());
            for x in xs {
                of.push(index.get(&key(x)).map(|&g| {
                    groups[g].0.push(x);
                    (g, groups[g].0.len() - 1)
                }));
            }
            let near: Vec<Vec<Vec<usize>>> = (groups.iter())
                .map(|(left, right)| near_pairs(left, right))
                .collect();
            let mut m = Vec::new();
            for (x, at) in xs.iter().zip(of) {
                let Some((g, i)) = at else { continue };
                let right = &groups[g].1;
                for y in near[g][i].iter().map(|&j| right[j]) {
                    let named = std::cell::Cell::new(true);
                    let Some(mut cs) = self.components(x.pairs(y, &named)).await else {
                        continue;
                    };
                    let fields = (x.fields.keys().cloned()).zip(cs.split_off(x.items.len()));
                    m.push(Shape::new(cs, fields.collect()));
                }
            }
            // Complexity tradeoff (COMPLEXITY.md F17): repeated shapes dropped through a hash
            // set, as repeated rows are below.
            let mut have = HashSet::new();
            let first: Vec<bool> = m.iter().map(|s| have.insert(s)).collect();
            let m = (m.iter().zip(first))
                .filter(|&(_, f)| f)
                .map(|(s, _)| s.clone());
            shapes.insert(n.clone(), m.collect());
        }
        a.meet_rest(t, met, shapes)
    }

    /// The meets of the pairs of components `pairs`, in order, or none when one is empty: a
    /// row or a payload with an empty component has no value, whatever the rest meet to.
    async fn components(
        &'m self,
        pairs: impl Iterator<Item = (&'m Ty, &'m Ty)>,
    ) -> Option<Vec<Ty>> {
        let mut cs = Vec::new();
        for (x, y) in pairs {
            let c = match x.meets_parts(y) {
                false => x.meet_rest(y, Vec::new(), BTreeMap::new()),
                true => self.kept((x, y), move || self.meet(x, y)).await,
            };
            if c.is_empty() {
                return None;
            }
            cs.push(c);
        }
        Some(cs)
    }
}

impl<'m> Pairs<'m, (*const Ty, *const Ty), bool> {
    /// [`Ty::meets`] of `a` and `b`, whose tuples decide it. Only the pairs of tuples that may
    /// share a value are compared ([`Near`]), found by key lookup, not every pair of one length.
    /// When each side has one tuple, that one pair is compared, with the same answer.
    async fn meets(&'m self, a: &'m Ty, b: &'m Ty) -> bool {
        // Complexity tradeoff: `l` and `r` tuples are compared pair by pair, with no keys, when
        // `l·r ≤ 1`: one tuple on each side. What is given up: nothing in order, since that is
        // one pair. Why: filing costs about 20k instructions plus 10k for each tuple on a side
        // of two components and 16k of five (the classes of the components are read once per
        // tuple and kept, `Row::keys`; the rest is hashing), and a pair about 24k, so filing is
        // already cheaper at one tuple against two. Measured 2026-11-09 in instructions per
        // walk, fresh types each walk, on unions of tuples of 2 to 5 components with one point
        // each and the other components `int`, `String` or `(int, bool)`, in one pattern or
        // four, filed against by pairs, no pair meeting: (1, 1) 41k against 46k, and 53k
        // against 50k for five components; (1, 2) 50k against 70k; (2, 2) 58k against 118k;
        // (1, 16) 190k against 407k; (8, 8) 170k against 1,550k; (32, 32) 613k against 24.57M.
        // Over 72 such cases the bound 1 costs at worst 6.75 times the cheaper path (geometric
        // mean 1.12), against 6.75 (1.23) for the old `l + r`, and over the 58 where no pair
        // meets at worst 1.13 (1.006) against 2.14 (1.16). The worst case is a pair that meets
        // found among the first, (32, 32) 886k against 131k: filing reads every tuple first,
        // and no bound on `l` and `r` alone can tell which pairs meet. Both give the same
        // answer, which `tuples_compared_by_meets_through_the_index_are_those_of_every_pair`
        // checks; the crossover is measured again at the Zed port.
        // Tests: `tests/steps/l01_22_type_representation/kinds.rs`, `meets_of_many_tuples_
        // scales`; COMPLEXITY.md F132.
        let (l, r) = (a.tuples.len(), b.tuples.len());
        let few = l.saturating_mul(r) <= 1;
        let groups = (!few).then(|| Groups::new(&a.tuples, &b.tuples));
        let mut near = groups.as_ref().map(Near::new);
        for (l, r) in a.tuples.iter().enumerate() {
            let near = near.as_mut().map(|n| n.of(l));
            let every = few.then(|| (0..b.tuples.len()).filter(|&j| b.tuples[j].len() == r.len()));
            let near = near
                .into_iter()
                .flatten()
                .chain(every.into_iter().flatten());
            'pair: for s in near.map(|j| &b.tuples[j]) {
                for (x, y) in r.iter().zip(s) {
                    let met = match x.meets_here(y) {
                        Some(m) => m,
                        None => self.kept((x, y), move || self.meets(x, y)).await,
                    };
                    if !met {
                        continue 'pair;
                    }
                }
                return true;
            }
        }
        false
    }
}

impl<'m> Pairs<'m, (*const Ty, *const Value), bool> {
    /// [`Ty::contains`] of `t` and a tuple of `items`, which its tuples decide. Only the
    /// tuples of `t` that may hold the value are compared with it, found by key lookup
    /// ([`Holders`]), once `t`'s tuples of its length have been read for enough values; until
    /// then every tuple of the length is, with the same answer. `filed` keeps each type node's
    /// tuples, filed or not, for the whole walk.
    async fn contains(&'m self, t: &'m Ty, items: &'m Items, filed: &'m RefCell<Filings>) -> bool {
        let (every, scanned, found) = match self.tried(t, items, filed) {
            Tried::Every => (Some(()), None, None),
            Tried::Scanned(rows) => (None, Some(rows), None),
            Tried::Found(holders) => (None, None, Some(holders)),
        };
        let every = every
            .into_iter()
            .flat_map(|()| (0..t.tuples.len()).filter(|&i| t.tuples[i].len() == items.len()));
        let scanned = scanned
            .into_iter()
            .flat_map(|rows| (0..rows.len()).map(move |k| rows[k]));
        let found = found.as_deref().into_iter().flat_map(|h| h.of(items));
        let rows = every.chain(scanned).chain(found);
        'row: for r in rows.map(|i| &t.tuples[i]) {
            for (c, x) in r.iter().zip(items) {
                let held = match c.contains_here(x) {
                    Ok(h) => h,
                    Err(inner) => {
                        self.kept((c, x), move || self.contains(c, inner, filed))
                            .await
                    }
                };
                if !held {
                    continue 'row;
                }
            }
            return true;
        }
        false
    }

    /// The tuples of `t` to compare with the tuple value of `items`, by their indices: every
    /// tuple of its length in written order, or those [`Holders`] finds, group by group. A tuple
    /// left out does not hold the value.
    fn tried(&self, t: &Ty, items: &Items, filed: &RefCell<Filings>) -> Tried {
        // Complexity tradeoff: the `l` tuples of one length of a node are scanned for each of
        // its first `v` values and filed at the first `v` with `l·v > 16·(l + v)`: never for 16
        // tuples or fewer, at the 22nd value for 64 tuples and the 17th for 1,024. What is
        // given up: nothing in order, since the scans before filing cost at most about
        // `16·(l + v)` tuples, linear in the node and its values. Why: filing costs about 8k
        // instructions a tuple of two components and 14k of five (the classes of the
        // components, read once per tuple and kept, `Row::keys`, and hashing), where a scan
        // costs about 440 a tuple for each value; so filing pays off only for many tuples read
        // for many values, from fewer than 16 to 64 values whatever `l`. Measured 2026-11-09 in
        // instructions per walk, max(2, 256/l) walks of a union of `l` tuples of 2 to 5
        // components (one point each, the others `int`, `String` or `(int, bool)`, in one
        // pattern or four) read for `v` values each, held by tuples spread over the union,
        // filed from the start against every tuple scanned: two components, one pattern,
        // l = 1,024, v = 16 8.80M against 3.35M, v = 64 9.56M against 12.05M, v = 1,024 24.68M
        // against 229.66M; five components, four patterns, l = 1,024, v = 16 14.59M against
        // 16.30M, v = 32 15.02M against 26.64M. Over 240 such cases the constant 16 costs at
        // worst 2.25 times the cheaper of the two (geometric mean 1.033), against 2.18 (1.035)
        // for 32, 4.14 (1.064) for 8 and 3.17 (1.096) for 64; with the scans before filing
        // counted, at worst 2.50 (1.080) against 2.36 (1.083) for 32 and 2.81 (1.101) for 24.
        // The two families cross at different `v`, so no constant suits both better. The
        // constant is measured again at the Zed port. Both give the same answer, which
        // `tuples_that_hold_a_value_through_the_index_are_those_of_every_tuple` checks. Tests:
        // `tests/steps/l01_22_type_representation/kinds.rs`, `contains_of_many_tuples_scales`;
        // COMPLEXITY.md F133.
        let len = items.len();
        let mut filed = filed.borrow_mut();
        let entry = filed.entry((t, len));
        let first = matches!(entry, std::collections::hash_map::Entry::Vacant(_));
        let visits = entry.or_insert(Visits::Once);
        #[cfg(test)]
        match FILE.get() {
            Some(false) => return Tried::Every,
            Some(true) if !matches!(visits, Visits::Filed(_)) => {
                let rows: Vec<usize> = (0..t.tuples.len())
                    .filter(|&i| t.tuples[i].len() == len)
                    .collect();
                *visits = Visits::Filed(Rc::new(Holders::new(t, &rows)));
            }
            _ => {}
        }
        match visits {
            Visits::Once if first => Tried::Every,
            Visits::Once => {
                let rows: Rc<[usize]> = (0..t.tuples.len())
                    .filter(|&i| t.tuples[i].len() == len)
                    .collect();
                *visits = Visits::Scanned {
                    n: 2,
                    rows: Rc::clone(&rows),
                };
                Tried::Scanned(rows)
            }
            Visits::Scanned { n, rows } => {
                *n += 1;
                let l = rows.len();
                if l.saturating_mul(*n) <= 16 * (l + *n) {
                    return Tried::Scanned(Rc::clone(rows));
                }
                let holders = Rc::new(Holders::new(t, rows));
                *visits = Visits::Filed(Rc::clone(&holders));
                Tried::Found(holders)
            }
            Visits::Filed(holders) => Tried::Found(Rc::clone(holders)),
        }
    }
}

/// Whether the piece `p` of `of` is in `t`, binding a variable of `t` to it when nothing else
/// of `t` holds it. A variable of `cx.rigid` stands for each carrier of its mask in turn: as
/// `p`, `t` must hold each; in `t`, it holds what each carrier, with the rest of `t`, holds. A
/// variable of `cx.fns` is the function it stands for.
///
/// A tuple shape and a function are compared in a frame of their own ([`Comparing::rows`],
/// [`Comparing::fits`]), through which every cycle of the comparisons passes. The tuple and
/// payload shapes of `t` that may hold a piece are found by `search` ([`Comparing::row_in`],
/// [`Comparing::payloads_in`]), which holds them filed for all the pieces of `of`.
async fn accepts<'m>(
    t: &Ty,
    p: &Piece,
    of: &Ty,
    binds: &mut Binds,
    search: &mut Search<'_>,
    c: &'m Comparing<'m, '_>,
) -> bool {
    if t.dynamic {
        return true;
    }
    let ok =
        match p {
            Piece::Dyn => false,
            Piece::Set(s) => {
                let held = {
                    let cx = c.cx.borrow();
                    s.subtype(&t.set)
                        || t.vars.iter().any(|w| {
                            cx.rigid.get(w).is_some_and(|&m| {
                                Carrier::of_mask(m).all(|c| s.subtype(&(&t.set | &c.ty())))
                            })
                        })
                };
                held && c.payloads_in(s, of, t, binds, search).await
            }
            // A kind-wide part that holds every tuple of the length holds it, whatever it holds.
            Piece::Tuple(cs) if KType::tuple(vec![KType::top(); cs.len()]).subtype(&t.set) => true,
            Piece::Tuple(cs) => c.row_in(cs, t, search, binds).await,
            // A type outside every comparison of function types holds its functions as written.
            Piece::Fn(s) => {
                let mut ok = false;
                for q in &t.fns {
                    if c.fits(s.clone(), Env::new(), q.clone(), Env::new()).await {
                        ok = true;
                        break;
                    }
                }
                ok
            }
            Piece::Var(v) => {
                let fns = c.cx.borrow().fns.get(v).cloned();
                match fns {
                    Some((s, se)) => {
                        let mut ok = false;
                        for w in &t.vars {
                            if c.fits_read(v, &s, &se, w).await {
                                ok = true;
                                break;
                            }
                        }
                        ok
                    }
                    None => {
                        t.vars.contains(v)
                            || c.cx.borrow().rigid.get(v).is_some_and(|&m| {
                                Carrier::of_mask(m).all(|c| c.ty().subtype(&t.set))
                            })
                    }
                }
            }
        };
    if ok {
        return true;
    }
    // A variable whose bound does not hold the piece is not bound to it (FAIL-types-overload-
    // bounded-tuple): bound so, it would fail [`bounds_hold`] once the parameters are compared,
    // so the shape that holds the piece only by that binding holds it in no comparison that
    // succeeds. Refused here, the shape does not hold the piece, and [`Comparing::search`] goes
    // on to the next shape, which may hold it: `(U,)` in `(B,) | (U,)` for `B in int | f64`
    // is held by `(U,)`, not by `(B,)`. Bound first and checked at the end, the search had
    // committed to the first shape. The check is the one [`bounds_hold`] makes, on the piece
    // with what the variable is bound to so far. Outside every tuple shape ([`Site::Other`])
    // no other shape is searched, so a piece no variable admits is bound as before, to the
    // first variable, and the message on [`bounds_hold`] names that binding. Cost: a binary
    // search of the bounds of the signature ([`Binds::bound`]) and a check of the piece alone
    // ([`var_mask`], O(log n) and O(1) expected), as what the variable is bound to was checked
    // when bound; so the binding keeps the cost of a union.
    // Assumption, not proved (ASSUME-documented): `admits` never refuses a piece that
    // `bounds_hold` would accept for the same variable once the search ends, so the early
    // refusal only skips bindings that would fail later. It needs each variable's mask
    // (`var_mask`, from `cx.rigid` or `cx.own_bounds`) to be known when `admits` runs: a
    // `Var(w)` with no mask goes to `piece_within`, which asks for `OTHER`, while `bounds_hold`
    // with the mask known tests `mq & !m == 0`. The masks are set at `Cx::open`, before any
    // parameter is compared. Evidence: the ty.rs tests,
    // `a_bounded_variable_beside_a_free_one_takes_only_what_its_bound_holds` (n from 2 to 5),
    // and 1,326 test pieces passing. If false, a fit is missed and a correct program is
    // rejected: precision only.
    let cx = c.cx.borrow();
    let admits = |v: &Arc<str>| {
        // A piece outside the variable's ceiling is not bound to it either: bound so, the result
        // would not be within the result of `q` ([`ceilings`]).
        if binds
            .ceiling(v)
            .is_some_and(|ceil| !may_be_within(p, ceil, &cx))
        {
            return false;
        }
        let Some(m) = binds.bound(v) else {
            return true;
        };
        match binds.get(v).filter(|b| !b.is_empty()) {
            None => match p {
                Piece::Var(w) => match var_mask(w, &cx) {
                    Some(mw) => mw & !m == 0,
                    None => piece_within(p, m, &cx),
                },
                _ => piece_within(p, m, &cx),
            },
            // A variable of several carriers stands for one carrier; with anything else beside
            // it, for one carrier and something else at once, which [`bounds_hold`] refuses,
            // unless its mask is one carrier, of which the piece is ([`carrier_of`]).
            Some(b) => match b.as_var().and_then(|w| Some((w, var_mask(w, &cx)?))) {
                Some((w, mw)) => {
                    matches!(p, Piece::Var(x) if x == w)
                        || mask_carrier(mw).is_some_and(|c| carrier_of(p, &cx) == Some(c))
                }
                None => piece_within(p, m, &cx),
            },
        }
    };
    let bindable =
        |v: &&Arc<str>| !cx.bind_none && !cx.rigid.contains_key(*v) && !cx.fns.contains_key(*v);
    let found = t.vars.iter().filter(bindable).find(|v| admits(v));
    // Outside every shape a piece no variable admits is bound to the first variable all the
    // same: that binding may hold more than `Var(w)` beside a variable bound alone to `w`, so
    // the pins of the bindings ([`Bound`]) no longer hold and are dropped.
    let found = found.or_else(|| match search.site {
        Site::Other => {
            let v = t.vars.iter().find(bindable)?;
            search.bound = BoundTable::new();
            Some(v)
        }
        Site::In(..) => None,
    });
    match found {
        Some(v) => {
            binds.unite(v.clone(), &of.of_piece(p));
            true
        }
        None => false,
    }
}

/// Whether a function of signature `s` is a function of signature `q`: the same parameter
/// names and kinds, and on each arrow of `q`, an arrow of `s` that takes its parameters and
/// returns within its result, or arrows of `s` that do so together (`covered`).
pub fn fits_sig(s: &Sig, q: &Sig) -> bool {
    let env = Env::new();
    let mut cx = Cx::default();
    let ok = comparing!(&mut cx, |c| fits_in(s, &env, q, &env, &c));
    cx.decided(ok)
}

/// [`fits_sig`], read as [`Ty::sub_with`] reads.
pub fn fits_sig_with(s: &Sig, q: &Sig, solve: Solve) -> bool {
    let mut cx = Cx {
        solve: Some(solve),
        ..Cx::default()
    };
    let env = Env::new();
    let ok = comparing!(&mut cx, |c| fits_in(s, &env, q, &env, &c));
    cx.decided(ok)
}

/// [`fits_sig`] inside the expected function types whose bounded variables `cx.rigid` holds,
/// `s` read by `se` and `q` by `qe`. `q`'s own bounded variables that a parameter holds join
/// `cx.rigid`: the caller of a function of type `q` picks one carrier of each bound, so `s`
/// must take every carrier of it. Each gets a new name, since `s` may use the same name for a
/// variable of its own. A bounded variable no parameter holds, of `q` or of `s`, is fixed by
/// no argument, so it stands for any carrier of its bound, as at a call ([`Sig::unheld`]).
///
/// The two sides are read through their environments, not rewritten: rewriting `q` at each
/// depth cost the size of `q` at each, the square of the depth for a function type nested
/// that deep. Each depth now costs its own parameters and bounds, and a lookup for each
/// variable (COMPLEXITY.md F60).
async fn fits_in<'m>(s: &Sig, se: &Env, q: &Sig, qe: &Env, c: &'m Comparing<'m, '_>) -> bool {
    let explain = c.cx.borrow_mut().why.take().is_some();
    if !s.needs.is_empty() {
        // Compared as written: the same signature, each variable read alike on both sides,
        // each solved class variable read as its type at every depth. That walk costs what
        // the comparison of the two as written costs.
        let solved;
        let solve = c.cx.borrow().solve;
        let (s, q) = match solve {
            Some(f) => {
                solved = (s.solved_with(f), q.solved_with(f));
                (&solved.0, &solved.1)
            }
            None => (s, q),
        };
        if s != q {
            return false;
        }
        return read_alike(s, se, qe);
    }
    // A signature fits itself, read alike on both sides (FAIL-types-sig-reflexive): each
    // variable of `s` bound to itself. Compared arrow by arrow instead, a tuple piece is held
    // by the first shape in written order that holds it, which may bind a variable that the
    // result then does not keep (`(x0: (T,) | (U,)) -> (T,)`, whose `(U,)` binds `T` in
    // `(T,)`), and a bounded variable of `q` is read under a new name, so no arrow of `s` is
    // equal to its arrow as read. The ceilings the result puts on the variables
    // ([`ceilings`]) and the pins of [`Comparing::search`] now steer a tuple piece past such a
    // shape, but not where a variable has no ceiling or is bounded and bound already, so the
    // signature as a whole is still taken here first. Cost: the
    // digests, kept with each signature, and where they agree a walk of both as written, which
    // the comparison would have cost.
    // Assumption, not proved (ASSUME-documented): a signature equal to `q` (same digest, and
    // `==` by `Same::sig`) and read alike in `se` and `qe` fits `q`, so `true` is returned with
    // no comparison. This needs fit to be reflexive for every signature, overloads, bounded
    // variables and class variables included, and needs `read_alike` to catch every way the two
    // environments could read the same text differently. Evidence: `a_signature_fits_itself`,
    // `signatures_with_a_variable_bound_in_a_tuple_fit_themselves_and_their_overloads`, and the
    // ty.rs tests for outer variables, function types and class variables. With this line off,
    // `a_bounded_variable_is_bound_only_to_what_its_bound_holds` and others fail, so the full
    // comparison is not itself reflexive in every case. If false, a function that does not fit
    // is accepted: unsound.
    if s.digest() == q.digest() && s == q && read_alike(s, se, qe) {
        return true;
    }
    // The hull of the results (row RANGE-result-hull): a function whose ints lie in a narrower
    // range fits where a wider one is expected, and one with none, any int, fits only where
    // none is expected. O(1), two comparisons of the ends.
    let hull_fits = match (&s.hull, &q.hull) {
        (_, None) => true,
        (None, Some(_)) => false,
        (Some(a), Some(b)) => a.within(b),
    };
    if !hull_fits {
        return false;
    }
    // The exact keys of a family (row RANGE-literal-keys): wanted, they are a promise the
    // value must make too, so only a family of the same keys fits; not wanted, any fits, as
    // the keys only add to what the arrows say. O(1), two comparisons of the ends.
    if q.keys.as_ref().is_some_and(|k| s.keys.as_ref() != Some(k)) {
        return false;
    }
    let same_params = s.params.len() == q.params.len()
        && s.params
            .iter()
            .zip(&q.params)
            .all(|(a, b)| a.positional == b.positional && (a.positional || a.name == b.name));
    if !same_params {
        return false;
    }
    let (mark, sas, qas, renamed, free, wide) = c.cx.borrow_mut().open(s, se, q, qe);
    let qas: Arc<[Arrow]> = qas.into();
    let outer = std::mem::replace(&mut c.cx.borrow_mut().free, free);
    let outer_wide = std::mem::replace(&mut c.cx.borrow_mut().wide, wide);
    let outer_bind_none = std::mem::replace(&mut c.cx.borrow_mut().bind_none, false);
    let outer_witnessed = std::mem::take(&mut c.cx.borrow_mut().witnessed);
    let outer_q_arrows = std::mem::replace(&mut c.cx.borrow_mut().q_arrows, qas.clone());
    let outer_within_q = std::mem::take(&mut c.cx.borrow_mut().within_q);
    // The bounds of `s` by the names its arrows are read with: a function type inside another
    // whose bounded variable has the name of one the comparison around it reads as itself is
    // read under a new name, and its bound, kept under the name written, was not checked
    // ([`bounds_hold`], [`Binds::bound`]): `(x0: (B,)) -> (B,)` for `B in int | f64`, returned
    // by a signature with its own `B`, fit where `(x0: (String,)) -> (String,)` is returned.
    // Cost: a copy of `s` only where so read, of the size reading its arrows already cost; the
    // functions that check bounds take them from the signature, which keeps them by name.
    let mut read;
    let s = match renamed {
        Some(bounds) => {
            // A clone starts with no memo ([`Facts`]), so none is kept for the old bounds.
            read = s.clone();
            read.bounds = bounds;
            &read
        }
        None => s,
    };
    let fits = every_arrow_fits(s, &sas, &qas, c).await;
    if explain && !fits {
        // The first arrow of `q` not covered, compared again alone: only on the way to an
        // error, at the cost of one more comparison of each arrow of `q`. Where each is
        // covered, `s` takes a key `q` does not ([`permitted`]), a plain reason; so too where
        // the permission, exact at one parameter, fails, which the verdict was decided by
        // before any cover, so no refusal of a cover tried here is kept.
        let mut why = None;
        let plain = s.params.len() == 1 && !permitted(s, &sas, &qas, Pass::Keys, c).await;
        for (k, qa) in qas.iter().enumerate().filter(|_| !plain) {
            if !covers(s, &sas, std::slice::from_ref(qa), c).await {
                why = refused_cover(s, q, &sas, qa, k, c).await;
                break;
            }
        }
        c.cx.borrow_mut().why = Some(why);
    }
    let mut cx = c.cx.borrow_mut();
    cx.free = outer;
    cx.wide = outer_wide;
    cx.bind_none = outer_bind_none;
    cx.witnessed = outer_witnessed;
    cx.q_arrows = outer_q_arrows;
    cx.within_q = outer_within_q;
    cx.forget(mark);
    fits
}

/// The part of `env` that the function `s` can read: its entries for the variables `s` holds
/// at any depth ([`Sig::facts`]). [`fits_in`] of `s` by it gives what it gives by `env`, so
/// [`Cx::read`] keeps each function with this part only; where it is empty, `s` reads as it
/// does by an empty environment (TEST-nested-marks-fn-vars), and is closed ([`Cx::closed`]).
///
/// Why: [`fits_in`] reads its environment only by looking up a variable the signature holds
/// at any depth: [`read_alike`] those of its arrows and needs, [`Cx::open`] its own (which it
/// then reads anew, whatever the environment held), [`Cx::read`] those of its arrows, and the
/// functions it holds are kept with the environment so made and read the same way when
/// compared ([`Comparing::fits_read`]), their variables among those `s` holds at any depth.
/// A lookup that misses reads the variable through `solve` or as itself, which does not
/// depend on the environment. `facts` holds more than the lookups read (the bounded, own and
/// held variables), which can only keep an entry that is never read.
///
/// Complexity tradeoff: the smaller of `env` and the facts is walked, each name looked up in
/// the other, O(min · log max), once for each function [`Cx::read`] reads; the facts are
/// worked out once for each signature. The naive test, a reading of the whole signature by
/// both environments, costs its size at each read. The test before it, "holds no variable"
/// ([`Sig::vars_order`] empty), put back no function with a type variable of its own, such as
/// `T -> T for T in int`, and each comparison beside one fell to the rule of one shape.
/// Until PERF-types-env-held-part this only said whether the part was empty, and each
/// function was kept with the whole `env`: in a nest of n generic function types, each
/// result holding a function of the level's variable, the environment at level k held an
/// entry for each of the k levels around and the function there n - k names, so the walks
/// cost O(n^2) in all (16.7 times at 8n, 26.3 with the bindings of
/// FAIL-types-result-fn-outer-binding, `a_refusal_of_generic_function_types_nested_deep_is_
/// linear`). Kept with its part only, a function passes on no entry for a variable it does
/// not hold, so each environment holds only entries for variables of the function read.
fn held_reading(s: &Sig, env: &Env) -> Env {
    if env.is_empty() {
        return Env::new();
    }
    let f = s.facts();
    let held: Env = if env.len() <= f.classes.len() + f.names.len() {
        (env.iter())
            .filter(|(v, _)| f.holds(v))
            .map(|(v, r)| (v.clone(), r.clone()))
            .collect()
    } else {
        (f.classes.iter().chain(&f.names))
            .filter_map(|v| env.get(v).map(|r| (v.clone(), r.clone())))
            .collect()
    };
    if held.len() == env.len() {
        env.clone()
    } else {
        held
    }
}

/// Whether `s` reads the same in any comparison it is met in: it holds only its own variables
/// and those of functions inside it ([`Sig::holds_only_own_variables`]), and no class
/// variable at any depth, so neither the readings of a scope around it nor the solved class
/// variables reach it ([`Comparing::fits_alone`]). Both facts are kept with the signature, so
/// this costs O(1) after the first ask of each signature.
fn alone_in_any_scope(s: &Sig) -> bool {
    s.facts().classes.is_empty() && s.holds_only_own_variables()
}

/// Whether each variable of `s`, as written, reads alike by `se` and by `qe`.
fn read_alike(s: &Sig, se: &Env, qe: &Env) -> bool {
    let mut vs = Vars::default();
    for a in &s.arrows {
        a.params.iter().for_each(|p| p.vars_in(&mut vs));
        a.result.vars_in(&mut vs);
    }
    s.needs.iter().for_each(|n| n.vars_in(&mut vs));
    vs.order.iter().all(|v| se.get(v) == qe.get(v))
}

impl Cx<'_> {
    /// Opens the comparison of [`fits_in`] of `s`, read by `se`, with `q`, read by `qe`: the
    /// mark of the names made and the own variables kept for it ([`Self::forget`]), the arrows
    /// of each as read, and the bounds of `s` by the names its variables are read as, where a
    /// bounded variable of `s` is read under a new name ([`Self::own_name`]), and the unbounded
    /// own variables of `s` by the names they are read as, in order ([`Cx::free`]), and the own
    /// variables of `q` a parameter holds, each bound to what it may stand for ([`Cx::wide`]).
    fn open(
        &mut self,
        s: &Sig,
        se: &Env,
        q: &Sig,
        qe: &Env,
    ) -> (
        Mark,
        Vec<Arrow>,
        Vec<Arrow>,
        Option<Masks>,
        SortedNames,
        Binds,
    ) {
        let cx = self;
        let mark = Mark {
            made: cx.made.len(),
            own: cx.own.len(),
            compared: std::mem::take(&mut cx.compared),
            fitted_written: std::mem::take(&mut cx.fitted_written),
        };
        // Each own variable names its own binder here, so the reading of the same name around it
        // is dropped, or replaced by a new name. An own variable of `s` whose name `q` holds, as
        // an unbounded own variable or as one of an enclosing scope, is read under a new name too
        // (FAIL-types-own-same-name): the two are different variables, and met by name, a piece
        // `T` of `q` was held by the `T` of `s` with no binding, so `(x0: T) -> T` fit
        // `(x0: T | int) -> int`, its `T` bound to `int` alone. A bounded own variable of `q` is
        // read as rigid under a new name or as its mask, so it needs none. The names `q` holds
        // are those at any depth ([`Sig::facts`]): a name held only inside a function of `q`
        // that binds it again, or that `qe` reads as something else, is renamed as well, which
        // is sound and binds as before. Cost: a lookup in those names, made once for each
        // signature, and one in `owned`, for each own variable of `s`.
        let mut qe = qe.clone();
        let mut wide = Binds::new();
        // The bounded variables of `q` whose bound has two classes or more, by the names they
        // are read as: each is widened only where it stands once in an arrow ([`repeated`]).
        let mut several = HashSet::new();
        // A bounded own variable of either side whose bound is one carrier and no values of no
        // carrier is read as that carrier, held by a parameter or not
        // (FAIL-fn-domain-bindable-variable). Proof that this is exact: a call fixes a bounded
        // variable to one carrier of its bound (rule 6 of sec:type_resolution), so such a
        // variable is that carrier at every instance, and the signature is the one with the
        // carrier written for it. Read as a variable instead, it was compared as itself
        // wherever the comparison does not bind it: inside a function type of a parameter,
        // where the two sides change places, `(h: (x: V) -> int) -> int for V in int` asked
        // whether `(x: int) -> int` is a `(x: V) -> int`, `int` within `V`, which no
        // comparison binding nothing holds, so it did not fit `(h: (x: int) -> int) -> int`,
        // its only instance. A bound of several carriers, or with values of no carrier, is
        // read as before. Cost: a test of the mask per own variable.
        let one = |m: u8| m.count_ones() == 1 && m & OTHER == 0;
        for v in &q.own {
            match q.bounds.get(v) {
                Some(&m) if q.held.contains(v) && !one(m) => {
                    let w = cx.fresh(v);
                    cx.rigid.insert(w.clone(), m);
                    wide.insert(w.clone(), Ty::of_mask(m));
                    if m.count_ones() > 1 || m & OTHER != 0 {
                        several.insert(w.clone());
                    }
                    qe.insert(v.clone(), Read::Rigid(w));
                }
                Some(&m) => {
                    qe.insert(v.clone(), Read::Mask(m));
                }
                None => {
                    let w = cx.own_name(v, &mut qe, false);
                    wide.insert(w.clone(), Ty::dynamic());
                    cx.keep_own(w, None);
                }
            }
        }
        let mut se = se.clone();
        let mut renamed = None;
        let mut free = Vec::new();
        for v in &s.own {
            match s.bounds.get(v) {
                Some(&m) if !s.held.contains(v) || one(m) => {
                    se.insert(v.clone(), Read::Mask(m));
                }
                bound => {
                    let apart =
                        q.facts().holds(v) && !(q.own.contains(v) && q.bounds.contains_key(v));
                    let w = cx.own_name(v, &mut se, apart);
                    if bound.is_some() && w != *v {
                        let bounds: &mut BTreeMap<_, _> =
                            renamed.get_or_insert_with(|| s.bounds.clone());
                        let m = bounds.remove(v).expect("a bounded variable has its bound");
                        bounds.insert(w.clone(), m);
                    }
                    if bound.is_none() {
                        free.push(w.clone());
                    }
                    cx.keep_own(w, bound.copied());
                }
            }
        }
        let read = |a: &Arrow, env: &Env, cx: &mut Cx| Arrow {
            params: a.params.iter().map(|p| cx.read(p, env)).collect(),
            result: cx.read(&a.result, env),
            partial: a.partial,
        };
        let sas: Vec<Arrow> = s.arrows.iter().map(|a| read(a, &se, cx)).collect();
        let qas: Vec<Arrow> = q.arrows.iter().map(|a| read(a, &qe, cx)).collect();
        if !several.is_empty() {
            for v in repeated(&qas, &several) {
                wide.remove(&v);
            }
        }
        free.sort();
        (mark, sas, qas, renamed, free.into(), wide)
    }

    /// For each function of `fns` in `result`, the result of an arrow of `s` as read, that
    /// holds an own variable of `s` that `b` binds, the binding of its name to a new name of
    /// the same function read with each such variable read as what `b` binds it to
    /// ([`Read::Bound`]): what [`Ty::subst`] does outside functions, carried into them
    /// (FAIL-types-result-fn-outer-binding). Kept with the reading of `s`'s side, such a
    /// variable read as itself inside the function, where a comparison of the function binds
    /// it afresh ([`accepts`]), so `(T -> (T -> T) for T in int | f64)` fit `(T -> (int ->
    /// int) for T in int | f64)`, the inner `T` bound to `int` while the parameter bound it to
    /// the rigid `T` of the other side.
    ///
    /// The name of each variable is found from the reading the function was kept with, the
    /// one `Cx::open` gave `s`'s side: no entry reads it as itself, `Rigid(w)` as `w`, and a
    /// mask is no variable to bind. Cost: for each function in `result`, a lookup of each own
    /// variable of `s` in the function's facts and the reading, and one in `bound_fns`.
    fn bound_in_fns(&mut self, s: &Sig, result: &Ty, b: &Binds) -> Binds {
        let mut out = Binds::new();
        if b.is_empty() {
            return out;
        }
        let mut vs = Vars::default();
        result.vars_in(&mut vs);
        for f in vs.order {
            let Some((sig, env)) = self.fns.get(&f).cloned() else {
                continue;
            };
            let facts = sig.facts();
            let mut bound = Vec::new();
            for v in s.own.iter().filter(|v| facts.holds(v)) {
                let r = match env.get(v) {
                    None => v,
                    Some(Read::Rigid(w)) => w,
                    Some(Read::Mask(_) | Read::Bound(_)) => continue,
                };
                if let Some(t) = b.get(r) {
                    bound.push((v.clone(), t.clone()));
                }
            }
            if bound.is_empty() {
                continue;
            }
            let key = (f.clone(), bound);
            let w = match self.bound_fns.get(&key) {
                Some(w) if self.fns.contains_key(w) => w.clone(),
                _ => {
                    let mut env = env;
                    for (v, t) in &key.1 {
                        env.insert(v.clone(), Read::Bound(t.clone()));
                    }
                    let w = self.fresh("");
                    self.fns.insert(w.clone(), (sig, env));
                    self.bound_fns.insert(key, w.clone());
                    w
                }
            };
            out.insert(f, Ty::var(w));
        }
        out
    }

    /// The name an own variable `v` of a function type opened is read as, in `env`, the
    /// reading of its side: `v` itself, or, when a comparison around this one already reads
    /// `v` as itself (`owned`) or `apart` (the other side holds `v`), a new name made from `v`.
    /// Without the new name, the two variables, bound by different signatures, would be one
    /// variable in the types compared, and a message would print them as one.
    fn own_name(&mut self, v: &Arc<str>, env: &mut Env, apart: bool) -> Arc<str> {
        if apart || self.owned.contains(v) {
            let w = self.fresh(v);
            env.insert(v.clone(), Read::Rigid(w.clone()));
            w
        } else {
            env.remove(v);
            v.clone()
        }
    }

    /// Keeps the own variable read as `w`, with its bound if it has one, until [`Self::forget`].
    fn keep_own(&mut self, w: Arc<str>, bound: Option<u8>) {
        let new = self.owned.insert(w.clone());
        debug_assert!(new, "an own variable is read under a name no other one has");
        if let Some(m) = bound {
            self.own_bounds.insert(w.clone(), m);
        }
        self.own.push((w, bound));
    }
}

/// Why a function of signature `s` is not a function of signature `q`, when the cover of an
/// arrow of `q` that rule 6 of sec:type_resolution may give is one the checker refuses
/// (`refused_cover`): the clause a message adds after what it rejects. `None` when `s`
/// fits, or does not for a plain reason, a value no arrow takes or a result outside.
pub fn why_unfit(s: &Sig, q: &Sig) -> Option<String> {
    why_unfit_in(s, q, Cx::default())
}

/// [`why_unfit`], read as [`fits_sig_with`] reads.
pub fn why_unfit_with(s: &Sig, q: &Sig, solve: Solve) -> Option<String> {
    why_unfit_in(
        s,
        q,
        Cx {
            solve: Some(solve),
            ..Cx::default()
        },
    )
}

fn why_unfit_in(s: &Sig, q: &Sig, mut cx: Cx) -> Option<String> {
    cx.why = Some(None);
    let env = Env::new();
    let ok = comparing!(&mut cx, |c| fits_in(s, &env, q, &env, &c));
    if cx.decided(ok) {
        return None;
    }
    cx.why.flatten().or(cx.unchosen)
}

#[cfg(test)]
thread_local! {
    /// How [`every_arrow_fits`] decides, when not by the index: the forms the differential
    /// tests compare the index with.
    static REFERENCE: std::cell::Cell<tests::Reference> =
        const { std::cell::Cell::new(tests::Reference::None) };
}

/// Whether a function whose arrows are `sas`, those of `s` as read, is a function whose arrows
/// are `qas`, those of `q` as read. A morphism type is `(L ⊆ dom ⊆ U) -> V`, and `s <: q`
/// holds iff `L_q <: L_s`, `U_s <: U_q` and `V_s <: V_q` (DESIGN.md sec:type_language). Here
/// the guarantee `L` of a signature is the union of the parameter types of its exact arrows,
/// and its permission `U` the union of those of all its arrows ([`Arrow`]). So:
///
/// - each exact arrow of `q` is covered by exact arrows of `s` ([`cover`]): its keys are in
///   the guarantee of `s`, and their answers are within its result;
/// - each partial arrow of `q` is covered by any arrows of `s`, or, failing that, each arrow
///   of `s` that may take one of its keys answers within its result ([`answers_within`]): a key
///   of a partial arrow need not be in the domain of `s`, and where it is, its answer is one
///   the partial arrow allows, `#notFound` among them;
/// - each arrow of `s` takes only keys some arrow of `q` permits ([`permitted`]).
///
/// The variables of the two sides are read apart. `s` is instantiated at the use (rule 2 of
/// sec:type_resolution): an arrow of `s` that holds a variable the comparison binds, its own or
/// one of a scope around it ([`holds_bindable`]), is compared at the binding its cover gave
/// ([`instance_within`]). `q` is all its instances together: a bounded variable
/// is one carrier at each call, so a bounded signature is the overload of one arrow per
/// carrier (rule 6, "fixing a bounded variable to each carrier of its bound multiplies the
/// arrows"), and an overload's permission is the union of its arrows' (sec:type_language,
/// "Relation to semantic subtyping", (2)). So an own variable of `q` that a parameter holds is
/// read, for the permission, as every value it may stand for ([`Cx::wide`]): `(x: int | f64)
/// -> bool` fits `(x: T) -> bool for T in int | f64`, and `(x: (T,) | (int,)) -> (T,)` fits
/// `(x: (U,) | (1,)) -> (U,)`. Only the top level of a parameter is so read; a variable of `q`
/// inside a function type there is compared as itself.
///
/// Before the exact domain (FAIL-types-fn-param-exact-domain), only the first was checked,
/// with every arrow of `s`, so a function type was contravariant in its domain: `int -> int`
/// was a `(1 | 2) -> int`, and `int ->? 1` an `int -> 1 | #notFound`.
async fn every_arrow_fits<'m>(
    s: &Sig,
    sas: &[Arrow],
    qas: &[Arrow],
    c: &'m Comparing<'m, '_>,
) -> bool {
    // The permission is checked first where it is exact, one parameter ([`permitted`]): a
    // function that takes a key `q` does not fails, whatever the cover finds, so the verdict
    // is a plain no and not a refusal the cover may make (`(x0: f64) -> ...` beside an arrow
    // whose cover is refused, where `q` takes no `f64`). It binds nothing and reads only
    // `Cx::wide`, so the cover is the same after it. With more parameters a false from it may
    // be wrong, and a refusal of the cover, which names the repair, is kept. An arrow whose
    // permission needs an instance a cover found ([`Pass::Witnessed`]) is checked after the
    // cover, which finds it.
    let exact_permission = s.params.len() == 1;
    if exact_permission && !permitted(s, sas, qas, Pass::Keys, c).await {
        return false;
    }
    let after = match exact_permission {
        true => Pass::Witnessed,
        false => Pass::All,
    };
    covers(s, sas, qas, c).await && permitted(s, sas, qas, after, c).await
}

/// The first two conditions of [`every_arrow_fits`]: each exact arrow of `qas` is covered by
/// exact arrows of `sas`, and each partial one by any arrows or by answers within its result.
/// Apart from the permission so that the explanation of an unfit signature ([`fits_in`]) can
/// ask it of each arrow of `q` alone: the permission against one arrow of `q` alone is
/// stricter than against all of them, and would name an arrow that is covered.
async fn covers<'m>(s: &Sig, sas: &[Arrow], qas: &[Arrow], c: &'m Comparing<'m, '_>) -> bool {
    if !sas.iter().chain(qas).any(|a| a.partial) {
        if !cover(s, sas, qas, c).await {
            return false;
        }
    } else {
        // A copy of the exact arrows of each side, only where a side has a partial arrow,
        // which a family or a bounded morphism has one or two of.
        let exact = |xs: &[Arrow]| {
            xs.iter()
                .filter(|a| !a.partial)
                .cloned()
                .collect::<Vec<_>>()
        };
        if !cover(s, &exact(sas), &exact(qas), c).await {
            return false;
        }
        for qa in qas.iter().filter(|a| a.partial) {
            let before = c.begin_alone();
            let ok = cover(s, sas, std::slice::from_ref(qa), c).await;
            let why = c.end_alone(before);
            if ok && why.is_none() {
                continue;
            }
            if !answers_within(s, sas, qa, c).await {
                uncovered(why, c);
                return false;
            }
        }
    }
    true
}

/// Whether each arrow of `sas` of `s` that may take a key of the partial arrow `qa` answers
/// within `qa`'s result, binding nothing ([`every_arrow_fits`]). Rule 6 of sec:type_resolution
/// gives a key the first arrow that takes it, which is one of these, so each key of `qa` that
/// `s` takes is answered within. An arrow is left out only where, at some parameter, its type
/// and `qa`'s share no value ([`Ty::meets`] false).
///
/// An arrow that holds a variable the comparison binds in a parameter ([`holds_bindable`]) is
/// taken at every instance at once (FAIL-fn-domain-bindable-variable): where its result holds
/// no such variable, the result is compared as it is, and the arrow is never left out, whatever
/// its parameter types. Proof that this is sound. `s` is used at some instance `σ` (rule 2 of
/// sec:type_resolution), the one the permission ([`permitted`]) and the covers of the other
/// arrows of `q` take; this function must hold at that `σ`, which it is not told. A result
/// that holds no variable the comparison binds is the same type `R` at every instance, so the
/// check that `R` is within `qa`'s result is the check at `σ`, whichever `σ` is. Leaving no
/// such arrow out asks more than the keys need, never less: an arrow that takes no key of `qa`
/// at `σ` needs no check, and one more check that passes changes nothing. So a yes here holds
/// at `σ`. Where the result holds such a variable, which `σ` the use takes is not worked out
/// here, and the arrow is refused (the safe path: a wrong no, never a wrong yes). What is
/// given up: such an arrow whose result is within at the `σ` taken, and an arrow that holds a
/// variable the comparison binds, takes no key of `qa` at `σ`, and returns outside `qa`'s
/// result; both are refused. Before, every arrow that held such a variable and might take a key
/// was refused, so `(x: (T,)) -> int` did not fit `(x: (int,) | String) ->? int`. A variable of
/// a bound of one carrier is read as that carrier ([`Cx::open`]), so it is in no arrow here.
///
/// Cost: one [`Ty::meets`] per parameter of an arrow that holds no such variable, a walk of
/// the parameter and result types of one that does ([`types_hold_bindable`]), and one
/// comparison of results per arrow of `s`; the naive form, each instance compared, is not
/// available, since an unbounded variable has infinitely many.
async fn answers_within<'m>(s: &Sig, sas: &[Arrow], qa: &Arrow, c: &'m Comparing<'m, '_>) -> bool {
    for sa in sas {
        if holds_bindable(s, sa, &c.cx.borrow()) {
            if types_hold_bindable(s, std::slice::from_ref(&sa.result), &c.cx.borrow()) {
                return false;
            }
        } else if !sa.params.iter().zip(&qa.params).all(|(x, y)| x.meets(y)) {
            continue;
        }
        if !within_as_is(&sa.result, &qa.result, c).await {
            return false;
        }
    }
    true
}

/// Whether a variable the comparison may bind stands in a parameter type of the arrow `sa` of
/// `s`, as read, at any depth: an own variable of `s`, unbounded ([`Cx::free`]) or bounded
/// (`s.bounds`, by the names its arrows are read with, [`fits_in`]), or one of a scope around
/// `s` that the comparison does not read as itself (not in [`Cx::rigid`] or [`Cx::fns`]), as
/// the `$9` of `(z: $9) -> $9`, the type of an inner lambda whose parameter's type is that of
/// an outer one's, not yet known. The cover of an arrow of `q` binds such a variable, so the
/// permission of `sa` is that of its instance under that binding ([`instance_within`]); read
/// unbound, `$9` was within no parameter of `q`, and the lambda did not fit
/// (`l01_26_type_resolution::bounds::a_lambda_uses_its_bounded_parameters_as_a_declared_function_does`).
/// Cost: for an arrow whose parameters hold no variable, the outer level of each
/// ([`Ty::holds_vars`]); otherwise a walk of the parameter types and a lookup per variable.
fn holds_bindable(s: &Sig, sa: &Arrow, cx: &Cx) -> bool {
    types_hold_bindable(s, &sa.params, cx)
}

/// Whether a variable the comparison may bind, as [`holds_bindable`] reads it, stands in one
/// of the types `ts` of `s`, at any depth.
fn types_hold_bindable(s: &Sig, ts: &[Ty], cx: &Cx) -> bool {
    if !ts.iter().any(Ty::holds_vars) {
        return false;
    }
    let mut vs = Vars::default();
    ts.iter().for_each(|p| p.vars_in(&mut vs));
    vs.order.iter().any(|v| {
        s.bounds.contains_key(v)
            || cx.free.binary_search_by(|w| (**w).cmp(v)).is_ok()
            || (!cx.rigid.contains_key(v) && !cx.fns.contains_key(v))
    })
}

/// Whether the arrow `sa` of `s`, its variables bound by `b`, takes only values of `qa`'s
/// parameter types, binding nothing: the permission of the instance of `sa` that fits `qa`
/// ([`every_arrow_fits`]). Only an arrow that holds a variable the comparison binds in a
/// parameter ([`holds_bindable`]) is compared; one that holds none is compared with every
/// arrow of `q` together
/// ([`permitted`]). An unbounded variable `b` leaves unbound is bound to `Never`: no key of
/// `qa` needed it, and its instance at `Never` fits as well, as a call binds such a variable
/// (sec:type_resolution). Not proved: a bounded variable left unbound stays a variable, which
/// no parameter of `q` holds without binding, so the arrow is refused (the safe path).
///
/// The instance is compared first with `qa`'s parameters, and where it is not within them,
/// with the permission of all of `q`'s arrows ([`within_q`]), as [`permitted`] compares an
/// arrow that holds no variable the comparison binds (FAIL-types-generic-arrow-overload-cover:
/// `(x0: #k0 | #k1, x1: T) -> int for T in int` was refused beside `(x0: #k0, x1: int) ->
/// int` and `(x0: #k1, x1: int) -> int`, though `T` can only be `int`, and the same arrow
/// with `int` written for `T` fit). Proof that this is the permission asked: the arrow's
/// permission holds where the keys its instance takes are keys some arrow of `q` takes
/// ([`every_arrow_fits`]); `qa` is one of those arrows, so the first comparison is a
/// sufficient test, and the second is [`arrow_permitted`]'s test of the union, exact for one
/// parameter and sound for more. Neither binds a variable ([`within_as_is`]). Which arrow of
/// `s` answers a key is the cover's question, asked of each arrow of `q` apart, not this one's.
///
/// Complexity tradeoff: naive version, each instance compared with the union of `q`'s arrows,
/// an index of `q` built per fit, O(m) for each of up to n·m fits, O(n·m²). Used: `qa` first,
/// one comparison per parameter, which most instances pass, and the union only where that
/// fails, kept by the instance's parameter types for the comparison of function types around
/// ([`Cx::within_q`]), so a generic arrow that covers each of `m` arrows of `q` at the same
/// instance builds one index: O(m) in all. Distinct instances that each fail `qa` still cost
/// an index each, O(m) per instance. Test:
/// `a_generic_arrow_covering_many_arrows_is_compared_in_linear_time`, 8.19 and 7.58 times at
/// 8n; with the memo off, 63.1 times.
///
/// A bounded variable is an instance only where it is bound to whole carriers
/// ([`whole_carriers`]): a call fixes it to one carrier of its bound (rule 6), so `(x0: B) ->
/// int` for `B in int | f64`, bound to `1` by the cover of `(x0: 1) -> int`, is called at
/// `int` and takes every `int`, keys `q` does not take. Such a binding is refused (FAIL-types-
/// bindable-arrow-permission): the instance compared at it is no instance, and passed where
/// none was. Refused, not made whole and compared again: the cover took `qa`'s parameters and
/// answered within its result at the piece, not at the carrier, so a whole binding would need
/// the cover again. What is given up: a cover whose first fit binds a piece where another
/// fit binds the whole carrier, as in a parameter that holds the carrier at the variable's
/// place in one member and a piece in another, is a wrong no; none is known.
///
/// An instance found within `qa` is a witness that the arrow takes only keys of `q`
/// ([`Cx::witnessed`]), kept for an arrow that holds a variable bounded by several carriers,
/// whose permission [`permitted`] cannot decide alone.
async fn instance_within<'m>(
    s: &Sig,
    sa: &Arrow,
    qa: &Arrow,
    b: &Binds,
    c: &'m Comparing<'m, '_>,
) -> bool {
    if !holds_bindable(s, sa, &c.cx.borrow()) {
        return true;
    }
    if !s.bounds.keys().all(|v| b.get(v).is_none_or(whole_carriers)) {
        return false;
    }
    let several = s
        .bounds
        .values()
        .any(|&m| m.count_ones() > 1 || m & OTHER != 0);
    let b = rest_bound(s, b.clone(), c);
    let wide = c.cx.borrow().wide.clone();
    // The instance holds the variables of `q` its cover bound the variables of `s` to, and
    // these are widened as on `q`'s side: for each instance `σ` of `q`, the instance of `sa`
    // at `σ` is within `x.subst(&b).subst(&wide)` (the widening replaces each variable by a
    // type that holds every value it may take, outside functions, where a type is monotone in
    // its variables), and that is within `y.subst(&wide)`, which is the union of `q`'s
    // instances of `y` ([`Cx::wide`], [`repeated`]). Compared as variables of their own, the
    // `X0` of `(X0,) | (X1,)`, bound by `X0 in int` and read as rigid, was not within the
    // `int` its own variable was widened to on `q`'s side.
    let params: Vec<Ty> = sa.params.iter().map(|x| x.subst(&b).subst(&wide)).collect();
    let mut alone = true;
    for (x, y) in params.iter().zip(&qa.params) {
        if !within_as_is(x, &y.subst(&wide), c).await {
            alone = false;
            break;
        }
    }
    if !alone && !within_q(params, sa, s.params.len(), c).await {
        return false;
    }
    let mut cx = c.cx.borrow_mut();
    if several && cx.unchosen.is_none() {
        cx.witnessed.insert(sa.params.clone());
    }
    true
}

/// Whether the parameter types `params` of an instance of the arrow `sa`, of `width`
/// parameters, take only keys some arrow of `q` takes ([`Cx::q_arrows`], read with `q`'s own
/// variables widened as [`permitted`] reads them): [`arrow_permitted`] of the instance. Kept by
/// `params` in [`Cx::within_q`] for the comparison of function types around, which fixes the
/// arrows of `q`, their widening and the reading of every variable; a verdict found after a
/// refusal ([`Cx::unchosen`]) is not kept, as a refusal decides the comparison anyway.
async fn within_q<'m>(params: Vec<Ty>, sa: &Arrow, width: usize, c: &'m Comparing<'m, '_>) -> bool {
    if let Some(&ok) = c.cx.borrow().within_q.get(&params) {
        return ok;
    }
    let (qas, wide) = {
        let cx = c.cx.borrow();
        (cx.q_arrows.clone(), cx.wide.clone())
    };
    let widened: Vec<Arrow> = qas
        .iter()
        .map(|a| Arrow {
            params: a.params.iter().map(|p| p.subst(&wide)).collect(),
            result: a.result.clone(),
            partial: a.partial,
        })
        .collect();
    let instance = Arrow {
        params,
        result: sa.result.clone(),
        partial: sa.partial,
    };
    let mut index = None;
    let ok = arrow_permitted(&instance, &widened, width, &mut index, c).await;
    let mut cx = c.cx.borrow_mut();
    if cx.unchosen.is_none() {
        cx.within_q.insert(instance.params, ok);
    }
    ok
}

/// Whether the scalars of `t`, what a bounded variable is bound to, hold every value of each
/// carrier they hold a value of: a binding a call may give, as it fixes the variable to whole
/// carriers (rule 6 of sec:type_resolution; [`instance_within`]). Its variables, rows,
/// shapes and functions are not read: a rigid variable of `q` is one whole carrier at each
/// call of `q`, and values of no carrier are what a bound of other values takes as they are.
/// Cost: a split of the kernel set and a comparison per carrier it holds.
fn whole_carriers(t: &Ty) -> bool {
    let split = t.set.split();
    Carrier::ALL
        .into_iter()
        .filter(|c| split.bases[c.base()].is_some())
        .all(|c| c.ty().subtype(&t.set))
}

/// `b` with each variable of `s` it leaves unbound bound as an instance of `s` binds it where
/// no key needs it ([`instance_within`], [`permitted`]): an unbounded variable to `Never`, as
/// a call binds such a variable (sec:type_resolution), and a bounded variable of one carrier
/// to that carrier: a call fixes the variable to one carrier of its bound (rule 6), and its
/// bound has one, so this is the only instance there is. The cover of `(Y0 | Y1,)` by `(X0,) |
/// (X1,)` binds `X0` to `Y0 | Y1` and leaves `X1`, bounded by `int`, unbound; as a variable
/// it was within no parameter of `q`. Not proved for a bound of several carriers: which one a
/// call fixes is not worked out here, so such a variable stays a variable, within no
/// parameter of `q`, and the arrow does not fit (the safe path).
fn rest_bound(s: &Sig, mut b: Binds, c: &Comparing<'_, '_>) -> Binds {
    let free = c.cx.borrow().free.clone();
    for v in free.iter() {
        if b.get(v).is_none() {
            b.insert(v.clone(), Ty::empty());
        }
    }
    for (v, &m) in &s.bounds {
        if b.get(v).is_none() && m.count_ones() == 1 && m & OTHER == 0 {
            b.insert(v.clone(), Ty::of_mask(m));
        }
    }
    b
}

/// How the arrow `sa` of `s`, which holds a variable the comparison binds in a parameter
/// ([`holds_bindable`]), is taken by [`permitted`]: the instances whose permission decides
/// its own, or none where only a witness does ([`Cx::witnessed`]).
///
/// Each variable is bound as a call binds it where no key needs it: an unbounded variable to
/// `Never` (sec:type_resolution), a variable bounded by one carrier to that carrier (rule 6).
/// A variable bounded by several carriers, `B in int | f64`, is fixed by a call to one of them
/// (rule 6): it has no least instance, one per carrier. So the arrow is taken at each carrier
/// of the one such variable it holds, the others bound as above, and its permission holds
/// where that of one of them does.
///
/// Proof. Write `P(σ)` for the parameter types at the instance `σ`; the arrow's permission
/// holds where some instance `σ` (one per arrow, [`Binds::of_arrow`]) has `P(σ)` within the
/// permission `U` of `q`. Outside function types a type is monotone in its variables, and
/// `Never` is within every type and each carrier of a one-carrier bound is the only instance
/// of its variable, so with `B` fixed to the carrier `k`, `P` at the instances above is within
/// `P(σ)` for every `σ` with `B = k`: if it is outside `U`, every such `σ` is. Each `σ` fixes
/// `B` to some `k`, so the permission holds iff it holds at one of the instances given. Where
/// a variable bound to `Never` stands inside a function type in a parameter, `Never` is not
/// the least there (an exact domain is invariant), and the instance may be outside `U` where
/// another is not: a wrong no, never a wrong yes. `B` itself is fixed exactly, wherever it
/// stands.
///
/// A bound that takes values of no carrier ([`OTHER`]) takes them as they are, as an unbounded
/// variable does, so `Never` is one more least instance of its variable, beside its carriers.
///
/// A bounded variable of `q` that its arrow repeats is read as rigid ([`repeated`]), one
/// carrier the caller of `q` picks, and an instance of `s` may bind `B` to it: `(x0: #a(B, B))
/// -> B` is within `(x0: #a(C, C)) -> C` at `B = C`, though at neither `B = int` nor `B = f64`.
/// The proof above is for `σ` that bind to carriers; one that binds to such a variable is not
/// tried here. So a yes from the instances given is exact (each is a real instance) and a no
/// is not: an arrow of several least instances, none permitted, passes where a cover found an
/// instance of it within an arrow of `q` ([`instance_within`], [`Cx::witnessed`]), and is
/// refused otherwise.
///
/// Not decided here, so `None`: two variables or more of several least instances each, whose
/// instances combine (`6^v` of them). Such an arrow passes only on a witness of the cover.
/// What is given up, for these and for the rigid case above: an arrow that takes part in no
/// cover, none of whose instances tried is permitted, though one that binds to a rigid
/// variable of `q`, or a combination of carriers, would be. A wrong no, never a wrong yes.
/// Before (FAIL-types-bindable-arrow-permission), such a variable was bound to `Never` too,
/// which takes no key, so `(x0: (B,)) -> int` passed beside `(x0: int) -> int` though each
/// instance takes keys `q` lacks.
///
/// Complexity tradeoff: naive version, every combination of the carriers of the variables
/// tried, exact, `6^v` comparisons for `v` variables; used: at most one comparison for each
/// carrier of one variable (6), and a hash lookup for the rest, which the cover paid for.
/// Cost: a walk of the parameter types and one replacement per instance.
fn instances(s: &Sig, sa: &Arrow, cx: &Cx) -> Option<Vec<Arrow>> {
    let mut vs = Vars::default();
    sa.params.iter().for_each(|p| p.vars_in(&mut vs));
    let mut b = Binds::new();
    let mut several = None;
    for v in vs.order.iter() {
        let bindable = s.bounds.contains_key(v)
            || cx.free.binary_search_by(|w| (**w).cmp(v)).is_ok()
            || (!cx.rigid.contains_key(v) && !cx.fns.contains_key(v));
        if !bindable {
            continue;
        }
        // The least instances of `v`: each carrier of its bound, and `Never` for the values of
        // no carrier a bound with `OTHER` takes as they are, as for an unbounded variable.
        let mut least: Vec<Ty> = match s.bounds.get(v) {
            Some(&m) => Carrier::of_mask(m).map(Ty::carrier).collect(),
            None => vec![],
        };
        if least.is_empty() || s.bounds.get(v).is_some_and(|&m| m & OTHER != 0) {
            least.push(Ty::empty());
        }
        match least.len() {
            1 => {
                b.insert(v.clone(), least.pop().expect("one"));
            }
            _ if several.is_none() => several = Some((v.clone(), least)),
            _ => return None,
        }
    }
    let at = |b: &Binds| Arrow {
        params: sa.params.iter().map(|p| p.subst(b)).collect(),
        result: sa.result.clone(),
        partial: sa.partial,
    };
    Some(match several {
        None => vec![at(&b)],
        Some((v, least)) => least
            .into_iter()
            .map(|t| {
                let mut b = b.clone();
                b.insert(v.clone(), t);
                at(&b)
            })
            .collect(),
    })
}

/// Which arrows of `s` [`permitted`] checks: in [`every_arrow_fits`], those of one least
/// instance before the cover where the permission is exact, those of several after it, where
/// a witness of the cover may pass them, or all after the cover.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Pass {
    /// The arrows of one least instance ([`instances`]), or of no variable it binds.
    Keys,
    /// The arrows of several least instances, or of more than [`instances`] tries.
    Witnessed,
    /// Every arrow.
    All,
}

/// Whether `x` is within `y` with no variable bound: each variable on either side is compared
/// as itself ([`Cx::bind_none`]). The permission of an arrow ([`permitted`],
/// [`instance_within`], [`answers_within`]) asks whether its values are within `q`'s as they
/// are; a comparison that may bind finds `(X0 | X1,)` within `(Y0,) | (Y1,)` only by binding
/// `Y0`, which is then refused, where with nothing bound the search goes on and splits the
/// member at the union `(X0,) | (X1,)` that it is. Cost: the comparison; the memo of rows
/// ([`Cx::compared`]) keeps its answers apart from those found with binding allowed
/// ([`Compared::as_is`]), so a shared row is compared once in each mode. Inside a function
/// type, [`fits_in`] binds as before.
async fn within_as_is<'m>(x: &Ty, y: &Ty, c: &'m Comparing<'m, '_>) -> bool {
    // An equal type is within, binding nothing: an instance is built apart from `q`'s
    // parameter, so it is seldom the same node, and `==` costs a walk of the shallower side.
    if x == y {
        return true;
    }
    let outer = std::mem::replace(&mut c.cx.borrow_mut().bind_none, true);
    let mut rb = Binds::new();
    let ok = c.sub_in(x, y, &mut rb).await;
    c.cx.borrow_mut().bind_none = outer;
    ok && rb.is_empty()
}

/// The variables of `vs` that stand twice or more in the parameter types of some arrow of
/// `qas`, outside the functions those hold, or may: [`Cx::wide`] leaves them out.
///
/// Proof that the rest may be widened. A variable bounded by two classes or more is one of
/// them at each call (DESIGN.md sec:type_resolution rule 6: "a call fixes the variable to one
/// carrier"), so `q`'s arrow at `T` is the union of its instances at each class. Where `T`
/// stands once in the arrow's parameters, outside functions, the parameters are monotone in
/// `T` and depend on it at one place, so the union of the instances is the parameters with
/// `T` replaced by the union of its classes: a union distributes over one component of a
/// product (a tuple, a payload, the parameters of an arrow). Where it stands twice, as in
/// `(T, T)`, that replacement holds `(int, f64)`, which no instance does, so the widening is
/// too wide, and the variable is compared as itself, rigid, which is sound: `x <: y` with `T`
/// rigid gives `x <: y` at each instance. An unbounded variable stands for every type (rule 4,
/// universally quantified), the type of all values among them, and a variable of one carrier
/// may be that carrier, so for these the widening is the instance at the widest type, and
/// exact however often they stand.
///
/// Counted as twice, which only leaves a variable rigid: two members of one union, as in `(T,)
/// | (T, T)`'s first member and `T | (T,)`, though there the widening is exact.
///
/// Complexity tradeoff: each tuple and payload shape is walked at most twice for each arrow,
/// so a shared one is not walked once per path; a variable met on a second walk counts again,
/// and a third arrival adds nothing a variable below it did not reach (it was counted twice
/// already). O(size of the parameters) per arrow, and only for signatures with such a
/// variable. A walk per path costs 2^depth on a type that holds each tuple twice.
fn repeated(qas: &[Arrow], vs: &HashSet<Arc<str>>) -> HashSet<Arc<str>> {
    enum Walk<'a> {
        Ty(&'a Ty),
        Row(&'a Row),
        Shape(&'a Shape),
    }
    let mut out = HashSet::new();
    for a in qas {
        let mut count: HashMap<&Arc<str>, u8> = HashMap::new();
        let mut walked: HashMap<NodeId, u8> = HashMap::new();
        let mut stack: Vec<Walk> = a.params.iter().map(Walk::Ty).collect();
        while let Some(w) = stack.pop() {
            match w {
                Walk::Row(r) => {
                    let k = walked.entry(r.node()).or_default();
                    if *k < 2 {
                        *k += 1;
                        stack.extend(r.iter().map(Walk::Ty));
                    }
                }
                Walk::Shape(s) => {
                    let k = walked.entry(s.node()).or_default();
                    if *k < 2 {
                        *k += 1;
                        stack.extend(s.items.iter().chain(s.fields.values()).map(Walk::Ty));
                    }
                }
                Walk::Ty(t) => {
                    for v in t.vars.iter().filter(|v| vs.contains(*v)) {
                        let n = count.entry(v).or_default();
                        *n = n.saturating_add(1);
                        if *n == 2 {
                            out.insert(v.clone());
                        }
                    }
                    stack.extend(t.tuples.iter().filter(|r| r.open()).map(Walk::Row));
                    stack.extend(t.payload_shapes().filter(|s| s.open).map(Walk::Shape));
                }
            }
        }
    }
    out
}

/// Whether each arrow of `sas` of `s` takes only keys some arrow of `qas` takes: the
/// permission of `s` within that of `q` ([`every_arrow_fits`]). An arrow that holds a variable
/// the comparison binds is taken at its least instance ([`rest_bound`]), and compared again at
/// each fit it takes part in ([`instance_within`]).
/// The parameter types of an arrow are a product, and those of `q` a union of products, so
/// `sa` is within them where, for some parameter `j`, the arrows of `q` that hold each of its
/// other parameter types hold its type at `j` together; that is exact for one parameter and
/// sound for more. Taken first: an arrow of `q` of equal parameter types, found by hash.
///
/// Complexity tradeoff: naive, each arrow of `s` compared with each arrow of `q` at each
/// parameter, n·m·p comparisons. Here the arrows of `q` that may hold `sa` at all but one
/// parameter come from an index of their keys ([`ArrowIndex::covering`]), and an arrow of `q`
/// equal at every parameter is found by hash, so equal overloads cost one lookup per arrow; in
/// the worst case it is still n·m, the containment join of [`cover`], for which no n^(2-e)
/// algorithm is expected (the Hitting Set conjecture there). Scaling test
/// `l01_26_type_resolution::bench::scaling::the_permission_of_an_overload_is_checked_in_linear_time`.
async fn permitted<'m>(
    s: &Sig,
    sas: &[Arrow],
    qas: &[Arrow],
    pass: Pass,
    c: &'m Comparing<'m, '_>,
) -> bool {
    // The pass after the cover takes only arrows of several least instances, or of none that
    // [`instances`] gives. Where no bound of `s` has two least instances, there is no such
    // arrow, and the pass is skipped before the hash set and index of `q` and a walk of each
    // arrow of `s`.
    //
    // Proof. [`instances`] lists the least instances of each variable it binds: the carriers
    // of its bound (`Carrier::of_mask`), and `Never` where that list is empty or the bound
    // has [`OTHER`]; an unbounded variable has `Never` alone. It gives two instances or more,
    // or `None`, only at a variable whose list has two entries or more, so only at a bound
    // with two carriers or more, or with one carrier and `OTHER`: `several_least` below, the
    // same count. Without such a bound every arrow that holds a bindable variable gets one
    // instance, and every other arrow is taken alone, so `several` is false for each arrow,
    // none is wanted in this pass, and the loop below returns `true`: the answer is the same.
    //
    // Complexity tradeoff: before, this pass built the hash set of `q`'s parameters, the
    // widened copy of `q`, and an instance of each arrow of `s` on every comparison, to want
    // none of them: 1.4G of 7.5G instructions at 1x in
    // `n_shapes_of_variables_one_pinned_one_variable_takes_the_rest_in_linear_time`
    // (PERF-shapes-one-pinned-time). Now one look at each bound of `s`, O(bounds).
    let several_least = |m: u8| {
        let carriers = Carrier::of_mask(m).count();
        carriers > 1 || (carriers == 1 && m & OTHER != 0)
    };
    if pass == Pass::Witnessed && !s.bounds.values().any(|&m| several_least(m)) {
        return true;
    }
    let equal: HashSet<&[Ty]> = qas.iter().map(|a| &a.params[..]).collect();
    // The parameters of `q` read with its own variables widened ([`Cx::wide`]); a copy only
    // where `q` has such a variable.
    let wide = c.cx.borrow().wide.clone();
    let widened: Vec<Arrow>;
    let qas = if wide.is_empty() {
        qas
    } else {
        widened = qas
            .iter()
            .map(|a| Arrow {
                params: a.params.iter().map(|p| p.subst(&wide)).collect(),
                result: a.result.clone(),
                partial: a.partial,
            })
            .collect();
        &widened
    };
    let mut index: Option<ArrowIndex> = None;
    for sa in sas {
        if equal.contains(&sa.params[..]) {
            continue;
        }
        // An arrow that holds a variable the comparison binds is taken at the instances that
        // decide its permission ([`instances`]): `(x0: (T,) | String) -> ...` at `T = Never`
        // still takes `String`, and `(x0: (B,)) -> ...` for `B in int | f64` takes `(int,)` or
        // `(f64,)`. The arrows that take part in a cover are also compared at the binding the
        // cover made ([`instance_within`]). An arrow of several least instances, or of more
        // than [`instances`] tries, passes where one of them is permitted or where a cover
        // found an instance of it within an arrow of `q` ([`Cx::witnessed`]), and the cover
        // runs first ([`Pass`]).
        let taken;
        let alone = match holds_bindable(s, sa, &c.cx.borrow()) {
            true => {
                taken = instances(s, sa, &c.cx.borrow());
                taken.as_deref()
            }
            false => Some(std::slice::from_ref(sa)),
        };
        let several = alone.is_none_or(|v| v.len() > 1);
        let wanted = match pass {
            Pass::Keys => !several,
            Pass::Witnessed => several,
            Pass::All => true,
        };
        if !wanted || (several && c.cx.borrow().witnessed.contains(&sa.params)) {
            continue;
        }
        let mut any = false;
        for sa in alone.unwrap_or_default() {
            if arrow_permitted(sa, qas, s.params.len(), &mut index, c).await {
                any = true;
                break;
            }
        }
        if !any {
            return false;
        }
    }
    true
}

/// Whether the arrow `sa`, of `width` parameters and holding no variable the comparison binds
/// or taken at an instance ([`instances`]), takes only keys some arrow of `qas` takes
/// ([`permitted`]), `index` the index of `qas`, made at the first arrow that needs it.
async fn arrow_permitted<'m, 'q>(
    sa: &Arrow,
    qas: &'q [Arrow],
    width: usize,
    index: &mut Option<ArrowIndex<'q>>,
    c: &'m Comparing<'m, '_>,
) -> bool {
    // An empty parameter: the parameters are a product, so the arrow takes no key, and the
    // index of `q` offers no arrow for a type with no key. `(x0: Never) -> ...` was refused.
    if sa.params.iter().any(Ty::is_empty) {
        return true;
    }
    let index = index.get_or_insert_with(|| ArrowIndex::new(qas, width));
    // The parameter types at `j` of the arrows of `q` that hold `sa`'s at every other.
    let mut at: BTreeMap<usize, Vec<&Ty>> = BTreeMap::new();
    let mut whole = false;
    'qas: for k in index.covering(sa, false) {
        let mut miss = None;
        for (j, (x, y)) in sa.params.iter().zip(&qas[k].params).enumerate() {
            if !within_as_is(x, y, c).await {
                if miss.is_some() {
                    continue 'qas;
                }
                miss = Some(j);
            }
        }
        match miss {
            None => {
                whole = true;
                break;
            }
            Some(j) => at.entry(j).or_default().push(&qas[k].params[j]),
        }
    }
    if whole {
        return true;
    }
    for (j, ps) in at {
        if within_as_is(&sa.params[j], &Ty::union_all(ps), c).await {
            return true;
        }
    }
    false
}

/// Whether each arrow `qa` of `qas`, those of `q` as read, is covered by arrows of `sas`, those
/// of `s` as read: by one arrow that takes its parameters and returns within its result
/// ([`arrow_fits`]), or, at one parameter `j`, by arrows whose parameter types there together
/// hold `qa`'s, each taking `qa`'s other parameters and returning within its result
/// ([`covered`]). Rule 6 of sec:type_resolution types an application region by region, so a
/// call of `qa` at any value of its parameters reaches an arrow of `s` that returns within
/// `qa`'s result.
async fn cover<'m>(s: &Sig, sas: &[Arrow], qas: &[Arrow], c: &'m Comparing<'m, '_>) -> bool {
    #[cfg(test)]
    if REFERENCE.get() != tests::Reference::None {
        return tests::reference(s, sas, qas, c).await;
    }
    // Each arrow of `q` is tried first on an arrow of `s` equal to it, found by hash, so that
    // an overload passed where the same overload is expected costs one comparison per arrow.
    let mut equal: HashMap<&Arrow, &Arrow> = HashMap::with_capacity(sas.len());
    for sa in sas {
        equal.entry(sa).or_insert(sa);
    }
    // Then on the arrows of `s` the index leaves, in order, until one fits: the arrows whose
    // parameter types offer, at each parameter, each carrier and bare atom that `qa`'s holds,
    // and those whose parameter type there is open, and whose result types need no key that
    // `qa`'s closed result does not offer. An arrow it leaves out does not fit, so the verdict
    // is that of trying every arrow of `s`. The index is built at the first arrow of `q` that
    // no arrow of `s` equals, in the size of the parameter and result types of `s`.
    //
    // Complexity tradeoff: none is given up for one arrow, every arrow of `q` gets the verdict
    // of comparing it with every arrow of `s`, but the comparisons are bounded by the
    // candidates, not below n·m in the worst case: the candidates come from the shortest of
    // the lists, by parameter key or by result key, and an arrow of `s` that offers every key
    // `qa` needs at each parameter and in its result and does not fit, or is open there, is
    // still compared. So `s` and `q` of n arrows that all share one parameter piece and one
    // result piece, and differ in pieces of both, cost n^2/2 comparisons; arrows that share a
    // parameter piece and differ in their results cost n (scaling test
    // l01_26_type_resolution::bench::scaling::passing_an_overload_whose_arrows_share_a_parameter_piece_scales;
    // COMPLEXITY.md F82). A tuple, a kind-wide part, a payload-only atom or a cofinite set of
    // atoms in `qa`'s parameter needs no key, since a parameter type may hold it without
    // offering one piece of it; a result that is open (a variable, the unknown, a cofinite set
    // of atoms) filters nothing. Why no complete bound: the question "each arrow of `q` has an
    // arrow of `s` whose parameters hold its parameters and whose result its result holds" is
    // a containment join between two families of sets, quantified for all and then exists;
    // with parameter and result types unions of many distinct members it is the complement of
    // Hitting Set, for which no n^(2-e) algorithm is expected (Abboud, Vassilevska Williams and
    // Wang, SODA 2016, the Hitting Set conjecture; a conjecture, not a theorem).
    let mut index: Option<ArrowIndex> = None;
    'qas: for qa in qas {
        let mut refused = None;
        if let Some(sa) = equal.get(qa) {
            // An arrow fits the arrow equal to it, each variable of `s` bound to the one of
            // the same name in `q` (FAIL-types-sig-reflexive), so it is taken without
            // comparing, unless it holds a bounded variable of `s` whose bound the variable
            // of `q` does not keep. Comparing would bind in written order and could miss
            // that binding where a variable has no ceiling from the result ([`ceilings`]) or is
            // bounded and bound already; where each has one, the ceilings and the pins of
            // [`Comparing::search`] find it. Cost: the size of `sa`, once per
            // arrow of `q`, and nothing when `s` has no bounded variable.
            if equal_fits(s, sa, &c.cx.borrow())
                || arrow_fits_alone(s, sa, qa, c, &mut refused).await
            {
                continue;
            }
        }
        let index = index.get_or_insert_with(|| ArrowIndex::new(sas, s.params.len()));
        for i in index.may_fit(qa) {
            if arrow_fits_alone(s, &sas[i], qa, c, &mut refused).await {
                continue 'qas;
            }
        }
        let before = c.begin_alone();
        let ok = covered(s, sas, index, qa, c).await;
        let why = c.end_alone(before);
        if !ok || why.is_some() {
            uncovered(refused.or(why), c);
            return false;
        }
    }
    true
}

/// Whether the arrow `sa` of `s` fits the arrow of `q` equal to it with no comparison: each
/// variable of `s` bound to the one of the same name in `q`. That holds where each bounded
/// variable of `s` in `sa` is bound so within its bound ([`bounds_hold`]): the variable of `q`
/// is bounded within it, as when `q` is `s`.
fn equal_fits(s: &Sig, sa: &Arrow, cx: &Cx) -> bool {
    // Assumption, not proved (ASSUME-documented): binding each variable of `s` to the variable
    // of the same name in `q` is a valid fit whenever `bounds_hold` accepts that binding, so an
    // arrow equal to the one of `q` needs no comparison. It needs `Cx::open` to have renamed
    // every own variable of `s` whose name `q` also holds, so that a name shared by the two
    // sides means one variable only where it should. Used by `every_arrow_fits` and the test
    // search `reference`. Evidence: the tests named at the equal-signature line of `fits_in`.
    // If false, an arrow that does not fit is accepted: unsound.
    if s.bounds.is_empty() {
        return true;
    }
    let mut vs = Vars::default();
    for t in sa.params.iter().chain([&sa.result]) {
        t.vars_in(&mut vs);
    }
    let mut b = Binds::new();
    for v in vs.order.into_iter().filter(|v| s.bounds.contains_key(v)) {
        b.insert(v.clone(), Ty::var(v));
    }
    bounds_hold(s, sa, &b, cx)
}

/// [`arrow_fits`] as an attempt of its own ([`Comparing::begin_alone`]): an arrow whose
/// comparison is refused does not fit, and the first such refusal is kept in `refused`.
async fn arrow_fits_alone<'m>(
    s: &Sig,
    sa: &Arrow,
    qa: &Arrow,
    c: &'m Comparing<'m, '_>,
    refused: &mut Option<String>,
) -> bool {
    let before = c.begin_alone();
    let ok = arrow_fits(s, sa, qa, c).await;
    match c.end_alone(before) {
        Some(why) => {
            refused.get_or_insert(why);
            false
        }
        None => ok,
    }
}

/// Records that an arrow of `q` is covered by no arrows of `s`: the comparison is refused for
/// the first refusal met in trying it, if any, so that it answers false with that reason
/// ([`Cx::decided`], [`why_unfit`]).
fn uncovered(refused: Option<String>, c: &Comparing<'_, '_>) {
    if let Some(why) = refused {
        c.refuse(|| why);
    }
}

/// Why the arrow `qa` of `q`, its `k`th, as read, is covered neither by one arrow of `s`, of
/// `sas` as read, nor by its arrows together ([`covered`]), when the reason is a cover the
/// checker refuses, though rule 6 of sec:type_resolution may give it: the clause a message
/// adds. In order: an arrow that takes `qa`'s parameters only with a bounded variable bound
/// to values of several carriers that it does not stand for alone ([`one_place`]); an arrow
/// that would take part only by binding a variable ([`binds_nothing`], case (2) of
/// [`covered`]); two or more arrows that take parts and return outside `qa`'s result, whose
/// intersection the checker does not build (case (3)); an arrow that takes values at every
/// parameter but misses more than one (case (1)). `None` for a plain reason: a value no arrow
/// takes, or one arrow that returns outside. One pass over the arrows, on the way to an error.
async fn refused_cover<'m>(
    s: &Sig,
    q: &Sig,
    sas: &[Arrow],
    qa: &Arrow,
    k: usize,
    c: &'m Comparing<'m, '_>,
) -> Option<String> {
    let mut shared = None;
    let mut free = None;
    let mut outside = Vec::new();
    let mut split = None;
    for (i, sa) in sas.iter().enumerate() {
        let mut b = Binds::of_arrow(s, sa, None, &c.cx.borrow());
        let mut miss = Vec::new();
        for (j, (x, y)) in qa.params.iter().zip(&sa.params).enumerate() {
            if !c.sub_in(x, y, &mut b).await {
                miss.push(j);
            }
        }
        // An arrow that takes no value of `qa` at some parameter takes no part.
        if !miss.iter().all(|&j| qa.params[j].meets(&sa.params[j])) {
            continue;
        }
        // In the order of the cases, each read off the state before a comparison borrows it.
        let binds = match miss[..] {
            [j] => !binds_nothing(&sa.params[j], &c.cx.borrow()),
            _ => false,
        };
        if let [_, _, ..] = miss[..] {
            split.get_or_insert(i);
        } else if binds {
            free.get_or_insert((i, miss[0]));
        } else if !bounds_hold(s, sa, &b, &c.cx.borrow()) {
            let cx = c.cx.borrow();
            let several = s
                .bounds
                .keys()
                .filter_map(|v| Some((v, b.get(v)?)))
                .find(|(v, t)| !one_carrier(t, &cx) && !one_place(sa, v, &cx));
            if let Some((v, t)) = several {
                shared.get_or_insert((i, v.clone(), t.clone(), Places::of(sa, v, &cx)));
            }
        } else if !result_within(s, sa, qa, &b, c).await {
            outside.push((i, miss.is_empty().then(|| result_bound(s, sa, &b, c))));
        }
    }
    let slot = arrow_text(q, &q.arrows[k]);
    let result = text_at(&q.arrows[k].result, q, &c.cx.borrow());
    let reason = if let Some((i, v, t, places)) = shared {
        let place = match places {
            Places { taken: 1.., .. } => format!(
                "`{v}` stands where the arrow takes values of it inside a function type, which \
                 need not be of the carrier its argument fixes"
            ),
            Places { given: 0, .. } => format!(
                "no argument gives values of `{v}` outside a function type, so none fixes its \
                 carrier"
            ),
            Places { given, .. } => format!(
                "`{v}` stands at {given} places the arguments give, which could be given values \
                 of two carriers"
            ),
        };
        format!(
            "the arrow `{}` takes it only with `{v}` bound to `{}`, values of more than one \
             carrier, but a call fixes `{v}` to one carrier, and {place}",
            arrow_text(s, &s.arrows[i]),
            text_at(&t, q, &c.cx.borrow())
        )
    } else if let Some((i, j)) = free {
        format!(
            "the arrow `{}` would take part of `{}` only by binding its type variable there, \
             and arrows that cover a parameter together bind no variable: which part each \
             takes is a choice per arrow, and fixing a bounded variable to each carrier of \
             its bound multiplies the arrows by the product of the bounds",
            arrow_text(s, &s.arrows[i]),
            s.params[j].name
        )
    } else if outside.len() >= 2 {
        let arrows: Vec<String> = outside
            .iter()
            .map(|&(i, _)| format!("`{}`", arrow_text(s, &s.arrows[i])))
            .collect();
        // When each takes all of `qa`, the intersection is the result at every value: a plain
        // reason, not a refused cover, with the intersection when the results have kernel types.
        let whole: Option<Vec<&Ty>> = outside.iter().map(|(_, r)| r.as_ref()).collect();
        if let Some(whole) = whole {
            let kernels: Option<Vec<KType>> = whole.iter().map(|r| r.kernel()).collect();
            let meet = match kernels.and_then(|ks| ks.into_iter().reduce(|a, b| &a & &b)) {
                Some(k) => format!(", `{}`,", Ty::set(k)),
                // Not built value by value ([`meet_within`]): the message says how.
                None => ", as the checker builds it (a function in one result is left out where \
                          another holds no function, and a variable bounded by carriers where \
                          each carrier of its bound is missing from some other result; every \
                          other piece that holds a function, a variable or the unknown is kept \
                          whole),"
                    .into(),
            };
            return Some(format!(
                "at `{slot}`, the arrows {} each take all of it, and the intersection of their \
                 results{meet} is not within `{result}`",
                arrows.join(", "),
            ));
        }
        format!(
            "the arrows {} each return outside `{result}`; where several take one value, the \
             result is what their results share, and the checker works that out only for \
             arrows that each take all that the arrows returning within `{result}` leave of one \
             parameter, since finding the values each group of arrows shares takes time that \
             grows with the product of their number; to repair it, write the arrows so that \
             each returns within `{result}`",
            arrows.join(", ")
        )
    } else {
        let i = split?;
        format!(
            "the arrow `{}` takes a part of more than one parameter, and arrows are combined \
             only when they differ at one parameter: telling whether arrows that each split \
             several parameters cover them all can take time exponential in the number of \
             parameters, so the checker does not try; to repair it, write the arrows so that \
             they differ at one parameter",
            arrow_text(s, &s.arrows[i])
        )
    };
    Some(format!("at `{slot}`, {reason}"))
}

/// `t` as a message about a comparison with `q` prints it ([`Scope::of_comparison`]): the
/// variables `q` bounds by carriers by their names, and the rigid variables made from them
/// ([`Cx::fresh`]) by the names they were made from, not as `_`; the other variables of the
/// comparison as the program wrote them too. Only on the way to an error.
fn text_at(t: &Ty, q: &Sig, cx: &Cx) -> String {
    Scope::of_comparison(cx, Some(q)).text(t, cx)
}

/// The arrow `a` of `s`, as a function type of one arrow is written, with the bounds of the
/// variables it holds: at the cost of `a`, not of the other arrows of `s` (a message names each
/// arrow of an overload of `n`).
fn arrow_text(s: &Sig, a: &Arrow) -> String {
    let mut vs = Vars::default();
    a.params.iter().for_each(|p| p.vars_in(&mut vs));
    a.result.vars_in(&mut vs);
    let mut one = Sig {
        params: s.params.clone(),
        arrows: vec![a.clone()],
        bounds: (vs.order.iter())
            .filter_map(|v| Some((v.clone(), *s.bounds.get(v)?)))
            .collect(),
        data: s.data,
        dense: s.dense,
        keys: s.keys.clone(),
        word: None,
        needs: Vec::new(),
        own: vs
            .order
            .iter()
            .filter(|v| s.own.contains(*v))
            .cloned()
            .collect(),
        held: BTreeSet::new(),
        named: s.named,
        hull: s.hull.clone(),
        facts: Facts::default(),
    };
    one.note_held();
    Ty::func(Arc::new(one)).to_string()
}

/// Whether arrows of `sas` together cover `qa`, as rule 6 of sec:type_resolution types a call:
/// at each value of `qa`'s parameters, the arrows that take it are not none, and the
/// intersection of their results is within `qa`'s result. Two forms are built, each from the
/// candidates of the index ([`ArrowIndex::covering`]), each arrow compared once, its
/// parameters in one pass ([`part_of`]), so the cost is linear in the width, not its square.
///
/// By union: at some parameter `j`, the arrows that take `qa`'s other parameters and return
/// within its result together hold `qa`'s parameter type at `j`. Each value reaches one of
/// them, which gives a result within `qa`'s, whatever other arrows it reaches.
///
/// By intersection ([`met`]): the arrows that return within `qa`'s result take a part of
/// `qa`'s parameter at `j`, and every arrow of a set `H` takes all that they leave (or all of
/// `qa`'s parameters), and the intersection of the results of `H` is within `qa`'s. A value
/// outside the part reaches every arrow of `H`, so its result is within that intersection.
///
/// A parameter type at `j` that would bind a variable takes part in neither: one that holds a
/// type variable of `s` at any depth, as `(T,)`, since the union would bind it with no check
/// of its bound. A function type (read as a variable of `cx.fns`), a rigid variable and the
/// unknown bind nothing, and take part.
///
/// Complexity tradeoff: some overloads whose arrows together cover `qa` are refused, each
/// with its own reason ([`refused_cover`]). (1) Arrows that cover `qa` only by splitting two
/// or more parameters at once: `((x: int, y: int) -> R) & ((x: bool, y: bool) -> R) & ((x:
/// int, y: bool) -> R) & ((x: bool, y: int) -> R)` covers `(x: int | bool, y: int | bool) ->
/// R`, and is refused. Whether a union of products covers a product is DNF tautology when
/// each parameter has two values, coNP-complete, so a complete check is exponential in the
/// number of parameters. (2) An arrow whose parameter type at `j` holds a type variable of
/// `s`: which part of `qa`'s parameter the variable would be bound to is a choice per arrow,
/// and fixing a bounded variable to each carrier of its bound multiplies the arrows by the
/// product of the bounds, exponential in the variables. (3) Arrows that return outside `qa`'s
/// result, overlapping so that no one set of them takes every value the arrows within leave:
/// `((x: int | bool) -> String | #a) & ((x: int) -> String | #b) & ((x: bool) -> String |
/// #c)` covers `(x: int | bool) -> String`, the intersection `String` at `int` from the first
/// two and at `bool` from the first and third, and is refused. Deciding that is the
/// all-subsets condition of semantic subtyping on arrows (Frisch, Castagna and Benzaken, J.
/// ACM 2008); it is as hard as Orthogonal Vectors even with one parameter of atoms (each
/// arrow a coordinate, each atom of the parameter a vector of the arrows that take it, each
/// atom outside the result a vector of the arrows whose results leave it out), so no
/// n^(2-e) algorithm is expected under the Strong Exponential Time Hypothesis (Williams,
/// TCS 2005; a conjecture). Tests: l01_26_type_resolution::fits (each case, its message and a
/// near miss), and the differential tests below, against every subset of arrows and against
/// the values of small types; COMPLEXITY.md F82. A complete solution would split `qa`'s
/// parameters into the regions the arrows' parameter types cut, and intersect the results per
/// region.
///
/// Complexity tradeoff: the candidates, as those of one arrow ([`every_arrow_fits`]), are not
/// below n·m in the worst case. Arrows that all offer one piece of the slot's parameter are
/// each compared with each arrow of the slot: `(x: #c | #ai) -> String` for i below n, passed
/// where `(x: #c | #ak | #a(k+1)) -> String | #zk` is expected for each k, cost n·m
/// comparisons (63.3 times the bytes at n = 100 and 800). Covering together includes fitting
/// by one arrow, so the containment join of [`every_arrow_fits`] bounds it from below; stopping
/// at the first arrow that holds each key is not exact, since a key (a carrier, an atom's name)
/// does not decide which values of it an arrow holds. The intersection takes the candidates
/// whatever their results, since the arrows of `H` return outside `qa`'s.
async fn covered<'m>(
    s: &Sig,
    sas: &[Arrow],
    index: &ArrowIndex<'_>,
    qa: &Arrow,
    c: &'m Comparing<'m, '_>,
) -> bool {
    // The parts at each parameter, by parameter; a BTreeMap, so the parameters are tried in
    // order, and only those some arrow misses are held.
    let mut parts: BTreeMap<usize, Vec<&Ty>> = BTreeMap::new();
    let mut refused = None;
    for i in index.covering(qa, true) {
        if let Some((Part::At(j, true), _)) = part_of_alone(s, &sas[i], qa, c, &mut refused).await {
            parts.entry(j).or_default().push(&sas[i].params[j]);
        }
    }
    for (j, ps) in parts {
        if c.sub_in(&qa.params[j], &Ty::union_all(ps), &mut Binds::new())
            .await
        {
            return true;
        }
    }
    if met(s, sas, &index.covering(qa, false), qa, c).await {
        return true;
    }
    uncovered(refused, c);
    false
}

/// [`part_of`] as an attempt of its own ([`Comparing::begin_alone`]): an arrow whose
/// comparison is refused takes no part, and the first such refusal is kept in `refused`, for
/// the caller to give as the reason where the cover fails ([`uncovered`]). Leaving an arrow
/// out only shrinks what [`covered`] and [`met`] find: the union of the parts at a parameter
/// holds less, and in [`met`] fewer results are intersected and the rest left at a parameter
/// is larger, so the answer may go from yes to no, never the other way. Before, a refusal
/// inside one arrow's attempt was kept by the comparison though other arrows covered `qa`,
/// and the cover answered no: the index and the search of every set of arrows, which try
/// different arrows, disagreed (seed 2929246812783321450 of
/// `bench::the_index_of_arrows_gives_the_verdict_on_large_overloads`).
async fn part_of_alone<'m>(
    s: &Sig,
    sa: &Arrow,
    qa: &Arrow,
    c: &'m Comparing<'m, '_>,
    refused: &mut Option<String>,
) -> Option<(Part, Binds)> {
    let before = c.begin_alone();
    let part = part_of(s, sa, qa, c).await;
    match c.end_alone(before) {
        Some(why) => {
            refused.get_or_insert(why);
            None
        }
        None => part,
    }
}

/// How the arrow `sa` of `s` takes `qa`'s parameters ([`part_of`]).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Part {
    /// It takes all of them; it returns outside `qa`'s result, or it would fit alone.
    Whole,
    /// It takes all but the parameter `j`, at which its type binds nothing, and returns within
    /// `qa`'s result or not.
    At(usize, bool),
}

/// How the arrow `sa` of `s` takes the parameters of `qa`: all of them, or all but one `j`,
/// at which its type binds nothing ([`binds_nothing`]), each bounded variable of `s` it binds
/// bound as [`bounds_hold`] requires, with what it binds. [`arrow_fits`] with `j` left out: a type that binds
/// nothing, so the pass over every parameter binds what the pass without `j` binds.
async fn part_of<'m>(
    s: &Sig,
    sa: &Arrow,
    qa: &Arrow,
    c: &'m Comparing<'m, '_>,
) -> Option<(Part, Binds)> {
    let mut b = Binds::of_arrow(s, sa, None, &c.cx.borrow());
    let mut miss = None;
    for (j, (x, y)) in qa.params.iter().zip(&sa.params).enumerate() {
        if !c.sub_in(x, y, &mut b).await {
            if miss.is_some() || !binds_nothing(y, &c.cx.borrow()) {
                return None;
            }
            miss = Some(j);
        }
    }
    if !bounds_hold(s, sa, &b, &c.cx.borrow()) {
        return None;
    }
    // The permission of the instance that takes part: within `qa`'s parameter types, the one
    // at `j` included, which binds nothing ([`instance_within`]). An arrow of `s` that would take
    // keys of another arrow of `q` beside a part of `qa`'s is refused (the safe path).
    if !instance_within(s, sa, qa, &b, c).await {
        return None;
    }
    let part = match miss {
        None => Part::Whole,
        Some(j) => Part::At(j, result_within(s, sa, qa, &b, c).await),
    };
    Some((part, b))
}

/// Whether comparing a type with `t` binds nothing: each variable it holds outside functions,
/// at any depth, is a rigid variable or a function read as one ([`Cx::read`]). The unknown
/// binds nothing; a type variable of the given side would be bound. The tuples are walked on
/// an explicit stack, each type's variables before its components and the components in
/// order, as the recursive form walked them, stopping at the first variable that binds.
fn binds_nothing(t: &Ty, cx: &Cx) -> bool {
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        if !t
            .vars
            .iter()
            .all(|v| cx.rigid.contains_key(v) || cx.fns.contains_key(v))
        {
            return false;
        }
        stack.extend(t.tuples.iter().rev().flat_map(|r| r.iter().rev()));
    }
    true
}

/// Whether the candidates `cands` of `sas` cover `qa` by intersection ([`covered`]): with
/// `U` the union of the parameter types at `j` of the arrows that take a part there and
/// return within `qa`'s result, and `H` the arrows that take all of `qa`'s parameters with
/// those that take, at `j`, all of `qa`'s type there outside `U`, `H` is not empty and the
/// intersection of its results is within `qa`'s; or `H` is the arrows that take all of `qa`.
/// [`Ty::diff`] keeps a part it cannot subtract, so `H` takes at least what the arrows within
/// leave. The results are intersected by [`meet_within`]. The cost is one comparison of each
/// candidate and, for each `j`, one of each arrow that takes a part there with what the others
/// leave.
async fn met<'m>(
    s: &Sig,
    sas: &[Arrow],
    cands: &[usize],
    qa: &Arrow,
    c: &'m Comparing<'m, '_>,
) -> bool {
    // An arrow of `q` that takes no value is left to one arrow and the union, as before this
    // form: the index leaves out arrows of `s` that take part of no parameter of it.
    if qa.params.iter().any(Ty::is_empty) {
        return false;
    }
    // The results of the arrows that take all of `qa`, and, at each parameter, the parameter
    // types of the arrows within and of those outside, with their results.
    let mut whole: Vec<Ty> = Vec::new();
    let mut within: BTreeMap<usize, Vec<&Ty>> = BTreeMap::new();
    let mut outside: BTreeMap<usize, Vec<(&Ty, Ty)>> = BTreeMap::new();
    let mut refused = None;
    for &i in cands {
        let sa = &sas[i];
        match part_of_alone(s, sa, qa, c, &mut refused).await {
            Some((Part::Whole, b)) => whole.push(result_bound(s, sa, &b, c)),
            Some((Part::At(j, true), _)) => within.entry(j).or_default().push(&sa.params[j]),
            Some((Part::At(j, false), b)) => outside
                .entry(j)
                .or_default()
                .push((&sa.params[j], result_bound(s, sa, &b, c))),
            None => {}
        }
    }
    if !whole.is_empty() && meet_within(&whole, &qa.result, c).await {
        return true;
    }
    // At a parameter no arrow outside takes a part of, `H` is the arrows that take all of `qa`.
    for (&j, parts) in &outside {
        let left = match within.get(&j) {
            Some(ps) => {
                c.diff(&qa.params[j], &Ty::union_all(ps.iter().copied()), None)
                    .await
            }
            None => qa.params[j].clone(),
        };
        let mut h = whole.clone();
        for (p, r) in parts {
            if c.sub_in(&left, p, &mut Binds::new()).await {
                h.push(r.clone());
            }
        }
        if !h.is_empty() && meet_within(&h, &qa.result, c).await {
            return true;
        }
    }
    uncovered(refused, c);
    false
}

/// Whether the intersection of `results` is within `result`. Each result is split into its
/// kernel part, its scalars and atoms and the tuple shapes that hold no function, variable or
/// unknown at any depth, and the rest. The kernel parts are intersected exactly. A value in
/// every result outside that intersection is outside the kernel part of some result `i`, so
/// in a piece of the rest of `i` and in every other result: each such piece must be within
/// `result`, unless no value of it is in every other result. That is known of a function,
/// when another result holds no function, and of a rigid variable bounded by carriers, when
/// each carrier of its bound is missing from some other result, since a call fixes it to one
/// carrier. Linear in the results: the carriers every result but one may hold are read off a
/// pass from each end.
///
/// Complexity tradeoff: a piece of the rest is not intersected value by value, so some
/// intersections within `result` are refused: `(U,) | String` and `(bool,) | String` meet
/// only on `String`, but the tuple piece `(U,)` is not within `String`. Such a fit gets the
/// error [`refused_cover`] writes, "the intersection of their results, as the checker builds
/// it (...), is not within", which states the rule above (test
/// `l01_26_type_resolution::fits::results_that_hold_a_function_or_a_variable_are_intersected`,
/// COMPLEXITY.md F82). Intersecting rigid variables value by value would fix each to each
/// carrier of its bound, the product of the bounds in the variables; the tuple pieces would
/// need the intersection per component of each pair of shapes of one width, quadratic in the
/// shapes.
async fn meet_within<'m>(results: &[Ty], result: &Ty, c: &'m Comparing<'m, '_>) -> bool {
    if results.is_empty() {
        return false;
    }
    let (kernels, rest) = {
        let cx = c.cx.borrow();
        let masks: Vec<u8> = results.iter().map(|r| carriers_of(r, &cx)).collect();
        let mut after = vec![EVERY; masks.len() + 1];
        for (i, &m) in masks.iter().enumerate().rev() {
            after[i] = after[i + 1] & m;
        }
        let no_function = results.iter().any(|r| holds_no_function(r, &cx));
        let mut before = EVERY;
        let mut kernels = Vec::with_capacity(results.len());
        let mut rest = Ty::empty();
        for (i, r) in results.iter().enumerate() {
            let others = before & after[i + 1];
            before &= masks[i];
            let mut shapes = Vec::new();
            for row in &r.tuples {
                match row.iter().map(Ty::kernel).collect::<Option<Vec<_>>>() {
                    Some(cs) => shapes.push(KType::tuple(cs)),
                    None => rest.tuples.push(row.clone()),
                }
            }
            kernels.push(KType::union_all(
                std::iter::once(r.set.clone()).chain(shapes),
            ));
            if !no_function {
                rest.fns.extend(r.fns.iter().cloned());
            }
            for v in &r.vars {
                let missed = match cx.rigid.get(v) {
                    Some(&m) => m & OTHER == 0 && m & others == 0,
                    None => no_function && cx.fns.contains_key(v),
                };
                if !missed {
                    rest.vars.insert(v.clone());
                }
            }
            rest.dynamic |= r.dynamic;
        }
        (kernels, rest)
    };
    let Some(k) = kernels.into_iter().reduce(|a, b| &a & &b) else {
        return false;
    };
    let mut b = Binds::new();
    let kernel_within = match result.kernel() {
        Some(r) => k.subtype(&r),
        None => c.sub_in(&Ty::set(k), result, &mut b).await && b.is_empty(),
    };
    kernel_within && (rest.is_empty() || c.sub_in(&rest, result, &mut b).await && b.is_empty())
}

/// Results [`meet_within`] intersects and the result their intersection must be within, built
/// before a scaling test so that the test times the intersection alone and not the check of
/// the overload around it, which costs about 160,000 instructions a result: a quadratic in the
/// results that allocates nothing shows only here (COMPLEXITY.md F82, F85).
#[doc(hidden)]
pub struct Meet {
    results: Vec<Ty>,
    result: Ty,
    rigid: BTreeMap<Arc<str>, u8>,
}

impl Meet {
    /// `results` and `result`, inside expected function types whose bounded variables are
    /// `rigid`, each with the carriers of its bound.
    #[doc(hidden)]
    pub fn new(results: Vec<Ty>, result: Ty, rigid: &[(&str, &[Carrier])]) -> Self {
        let rigid = rigid
            .iter()
            .map(|&(v, cs)| (Arc::from(v), cs.iter().fold(0, |m, c| m | c.bit())))
            .collect();
        Meet {
            results,
            result,
            rigid,
        }
    }

    /// Whether the intersection of the results is within the result ([`meet_within`]).
    #[doc(hidden)]
    pub fn within(&self) -> bool {
        let mut cx = Cx {
            rigid: self.rigid.clone(),
            ..Cx::default()
        };
        let ok = comparing!(&mut cx, |c| meet_within(&self.results, &self.result, &c));
        cx.decided(ok)
    }
}

/// The carriers a value of `t`, as a comparison reads it, may be of, and [`OTHER`] if it may
/// be another value: a rigid variable stands for its bound, and a function read as a variable
/// for no carrier.
fn carriers_of(t: &Ty, cx: &Cx) -> u8 {
    if t.dynamic {
        return EVERY;
    }
    let split = t.set.split();
    let set = Carrier::ALL
        .into_iter()
        .filter(|c| split.bases[c.base()].is_some())
        .fold(0, |m, c| m | c.bit());
    t.vars.iter().fold(set, |m, v| match cx.rigid.get(v) {
        Some(&bound) => m | bound,
        None if cx.fns.contains_key(v) => m | OTHER,
        None => EVERY,
    })
}

/// Whether no value of `t`, as a comparison reads it, is a function: it holds no function, no
/// function read as a variable, no unknown, and only rigid variables bounded by carriers.
fn holds_no_function(t: &Ty, cx: &Cx) -> bool {
    t.fns.is_empty()
        && !t.dynamic
        && t.vars
            .iter()
            .all(|v| cx.rigid.get(v).is_some_and(|&m| m & OTHER == 0))
}

/// What a parameter type of an arrow must hold to hold a piece of a parameter type: the
/// values of one carrier, by [`Carrier::base`], or the bare atom of one name.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Key<'t> {
    Carrier(usize),
    Atom(&'t str),
}

/// The keys every type that holds `t` offers, unless it is open ([`offered_keys`]): the
/// carriers of its scalars and its bare atoms, of a set of atoms that lists its names. A piece
/// of `t` a key does not decide, a tuple, a kind-wide part, a function, a variable or the
/// unknown, adds none.
fn needed_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) {
    let split = t.set.split();
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    if let Some(names) = t.set.atom_names() {
        out.extend(names.filter(|&(_, bare)| bare).map(|(n, _)| Key::Atom(n)));
    }
}

/// The keys the parameter type `t` offers, and whether it is closed: it holds no variable and
/// no unknown, and lists the names of its atoms. A closed type holds a scalar or bare atom only
/// if it offers its key ([`accepts`]: a set piece is held by the set alone, unless `t` has a
/// variable or the unknown). An open one may hold any piece. It may offer a key it holds no
/// value of, an atom name listed with an empty payload, which makes only a candidate more.
fn offered_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) -> bool {
    let Some(names) = t
        .set
        .atom_names()
        .filter(|_| !t.dynamic && t.vars.is_empty())
    else {
        return false;
    };
    out.extend(names.map(|(n, _)| Key::Atom(n)));
    let split = t.set.split();
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    true
}

/// The keys of every piece of `t`, when each piece has one: the carriers of its scalars and the
/// names of its atoms. A parameter type that holds a value of `t` and is closed
/// ([`offered_keys`]) offers that value's key. False when `t` has a piece no key decides: a
/// tuple, a kind-wide part, a function, a variable, the unknown or a cofinite set of atoms.
fn piece_keys<'t>(t: &'t Ty, out: &mut Vec<Key<'t>>) -> bool {
    if t.dynamic || !t.vars.is_empty() || !t.tuples.is_empty() || !t.fns.is_empty() {
        return false;
    }
    let split = t.set.split();
    let Some(names) = t.set.atom_names().filter(|_| split.rest.is_none()) else {
        return false;
    };
    out.extend(names.map(|(n, _)| Key::Atom(n)));
    out.extend(
        Carrier::ALL
            .into_iter()
            .filter(|c| split.bases[c.base()].is_some())
            .map(|c| Key::Carrier(c.base())),
    );
    true
}

/// What the arrows of a signature say of its domain, for its meet with a signature of the same
/// parameters ([`Ty::fns_met`]). The domain of a function of the signature holds the parameter
/// types of each exact arrow, its guarantee, and lies within those of all its arrows, its
/// permission (DESIGN.md sec:type_language, "Morphism types carry two domain bounds", as
/// [`every_arrow_fits`] reads a signature); the arrows of several parameters are read as
/// tuples of their parameter types, in order.
struct Domains {
    /// The kernel type of its permission, the union of the tuples of each arrow's parameter
    /// types, where each of those has a kernel type ([`Ty::exact_kernel`]); none where one
    /// holds a function, a variable or the unknown.
    permission: Option<KType>,
    /// The union of the tuples of the parameter types of each exact arrow whose parameter
    /// types each have a kernel type; none where no exact arrow has.
    guaranteed: Option<KType>,
    /// Parameter types whose product is its permission, where its permission has a kernel
    /// type: for one parameter, the union of its arrows' types there; for several, the types
    /// of its one arrow. None for several arrows of several parameters.
    within: Option<Vec<Ty>>,
}

impl Domains {
    /// What the arrows of `s` say of its domain. Cost: one kernel type for each parameter
    /// type of each arrow, and their union joined in pairs.
    fn of(s: &Sig) -> Domains {
        let tuple = |a: &Arrow| {
            let ks = a.params.iter().map(Ty::exact_kernel);
            Some(KType::tuple(ks.collect::<Option<Vec<_>>>()?))
        };
        let tuples: Vec<Option<KType>> = s.arrows.iter().map(tuple).collect();
        let guaranteed: Vec<KType> = (s.arrows.iter().zip(&tuples))
            .filter(|(a, _)| !a.partial)
            .filter_map(|(_, k)| k.clone())
            .collect();
        let guaranteed = (!guaranteed.is_empty()).then(|| KType::union_all(guaranteed));
        let permission = tuples.into_iter().collect::<Option<Vec<_>>>();
        let within = match (&permission, s.params.len(), s.arrows.as_slice()) {
            (None, ..) => None,
            (Some(_), 1, arrows) => Some(vec![Ty::union_all(arrows.iter().map(|a| &a.params[0]))]),
            (Some(_), _, [a]) => Some(a.params.clone()),
            (Some(_), ..) => None,
        };
        Domains {
            permission: permission.map(KType::union_all),
            guaranteed,
            within,
        }
    }

    /// Whether a value of its guarantee was built outside the permission of `other`: then no
    /// function is of both signatures, since its domain would hold the value and lie within
    /// that permission. `Inhabited` is the kernel's proof, the value built and checked
    /// ([`KType::subtype_verdict`]); `Empty` and a refusal claim no such value, and the meet
    /// is kept. The guarantee is compared as one union: a value of the union outside the
    /// permission is a value of one of its exact arrows' tuples outside it, so the answer is
    /// that of comparing each tuple alone, where the kernel decides both.
    // Complexity tradeoff: one comparison for each exact arrow, made first, cost O(a) kernel
    // comparisons against a permission of O(a) rows, O(a^2) (measured: 5.5 s for 2048 arrows
    // each side, 9 times that of 1024). Used: one comparison of the union of the guarantees,
    // made once for each function, whose cost is that of the kernel's comparison of two unions
    // of O(a) rows. Given up: where the kernel refuses the union but would decide one tuple,
    // no value is proved outside and the meet is kept, which is sound.
    fn outside(&self, other: &Domains) -> bool {
        let (Some(g), Some(p)) = (&self.guaranteed, &other.permission) else {
            return false;
        };
        g.subtype_verdict(p) == Verdict::Inhabited
    }

    /// The meet of `s` and `q`, two signatures of the same parameters with what their arrows
    /// say of their domains: none where it is proved empty, two exact arrows over different
    /// domains among them (DESIGN.md sec:type_language, "two exact arrows over different
    /// domains share no value and their intersection is empty"); otherwise the arrows of both,
    /// each partial arrow's parameter types met with those of the other side's permission.
    ///
    /// Proof that a function `f` of both signatures is of the meet. Its domain holds both
    /// guarantees, which are the exact arrows of both, kept; its values on each arrow's
    /// parameter types are those the arrow allows, and each kept arrow is unchanged. Its domain
    /// lies within both permissions, `U_s` and `U_q`. A partial arrow of `s`, over `P`, allows
    /// `f`'s values only at keys in `U_q`, so the arrow over `P & U_q` bounds every value it
    /// bounded; where `U_q` is the product of `within` (one parameter: the union of its
    /// arrows' types; several, with one arrow: that arrow's types), `P & U_q` is the product of
    /// the meets of the parameter types, and [`Ty::meet`] holds each of those. The meet's
    /// permission is the union of its arrows' parameter types, and holds `U_s & U_q`: `U_s` is
    /// `s`'s guarantee and partial arrows `P_s`, so `U_s & U_q` lies within `s`'s guarantee and
    /// each `P_s & U_q`, which the meet's arrows hold; so `f`'s domain is permitted.
    ///
    /// It is within both sides exactly when each guarantee lies within the other side's
    /// permission and each partial arrow was met. Where that is not proved, a refusal, a
    /// variable, a function in a parameter type, or several arrows of several parameters, the
    /// arrows are kept as they are: a meet holding every function of both, as an `is` test
    /// needs, but not within each side.
    // Complexity tradeoff: the overload of both, made before (FAIL-types-meet-exact-arrows-
    // differing-domains), cost the arrows copied, O(a) for a arrows, and its permission was the
    // union of the two, so it was within neither side where the domains differ. Used: one
    // kernel comparison of each side's guarantee with the other side's permission
    // ([`Domains::outside`]), and one meet for each parameter type of each partial arrow, O(a)
    // meets of the sizes of the types; each side's guarantee and permission are made once for
    // each function ([`Ty::fns_met`]). Given up: a guarantee the kernel refuses is not proved
    // outside, and the meet is kept (COMPLEXITY.md F222).
    fn meet((s, ds): (&Sig, &Domains), (q, dq): (&Sig, &Domains)) -> Option<Sig> {
        if ds.outside(dq) || dq.outside(ds) {
            return None;
        }
        let mut m = s.clone();
        let n = m.arrows.len();
        m.add_arrows_of(q);
        let (own, other) = m.arrows.split_at_mut(n);
        for (arrows, within) in [(own, &dq.within), (other, &ds.within)] {
            let Some(within) = within else {
                continue;
            };
            for a in arrows.iter_mut().filter(|a| a.partial) {
                for (p, u) in a.params.iter_mut().zip(within) {
                    *p = p.meet(u);
                }
            }
        }
        // Two arrows over equal parameter types are one arrow whose result is the meet of
        // theirs, exact where either is: a function of both has its values there in both
        // results, and [`Ty::meet`] holds those. The signature's guarantee and permission are
        // unchanged, since each holds those parameter types before as after: the guarantee
        // through the exact arrow, if any, and the permission through either. The comparison
        // of a signature takes each arrow it is given alone, so `(int ->? int) & (int ->? int |
        // #a)` was not found within `int ->? int`, nor `(#b -> int | f64) & (#b ->? int)`
        // within `#b -> int`. Cost: one hash lookup for each arrow, and the meets of the
        // results merged.
        let mut at: HashMap<&[Ty], usize> = HashMap::new();
        let mut merged: Vec<Arrow> = Vec::with_capacity(m.arrows.len());
        for a in &m.arrows {
            match at.entry(&a.params) {
                std::collections::hash_map::Entry::Occupied(e) => {
                    let kept = &mut merged[*e.get()];
                    kept.result = kept.result.meet(&a.result);
                    kept.partial &= a.partial;
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(merged.len());
                    merged.push(a.clone());
                }
            }
        }
        drop(at);
        m.arrows = merged;
        Some(m)
    }
}

/// The arrows of a signature, as read, by what their parameter types offer and their result
/// types need: for the arrows of an expected signature, the arrows that may fit each, found
/// from the keys of its parameter and result types ([`every_arrow_fits`], [`covered`]).
struct ArrowIndex<'t> {
    /// The number of arrows.
    n: usize,
    /// For each parameter and each key, the arrows whose parameter type there is closed and
    /// offers the key, in order.
    post: HashMap<(usize, Key<'t>), Vec<usize>>,
    /// For each parameter, whether each arrow's type there is open (or missing).
    open: Vec<Vec<bool>>,
    /// For each parameter, the arrows whose type there is open, in order.
    always: Vec<Vec<usize>>,
    /// For each arrow, the keys its result type needs ([`needed_keys`]): a closed type that
    /// holds the result offers each.
    result_needs: Vec<Vec<Key<'t>>>,
    /// The arrows whose result type needs a key, each under one of them, the one the fewest
    /// results need, in order.
    by_result: HashMap<Key<'t>, Vec<usize>>,
    /// The arrows whose result type needs no key, in order.
    any_result: Vec<usize>,
}

impl<'t> ArrowIndex<'t> {
    /// The index of `sas`, arrows of `width` parameters, in the size of their parameter and
    /// result types.
    fn new(sas: &'t [Arrow], width: usize) -> ArrowIndex<'t> {
        let mut post: HashMap<(usize, Key<'t>), Vec<usize>> = HashMap::new();
        let mut open = vec![vec![false; sas.len()]; width];
        let mut keys = Vec::new();
        for (i, sa) in sas.iter().enumerate() {
            for (j, row) in open.iter_mut().enumerate() {
                keys.clear();
                match sa.params.get(j) {
                    Some(t) if offered_keys(t, &mut keys) => {
                        for &k in &keys {
                            post.entry((j, k)).or_default().push(i);
                        }
                    }
                    _ => row[i] = true,
                }
            }
        }
        let always = open
            .iter()
            .map(|row| {
                (0..)
                    .zip(row)
                    .filter(|&(_, &o)| o)
                    .map(|(i, _)| i)
                    .collect()
            })
            .collect();
        let result_needs: Vec<Vec<Key<'t>>> = sas
            .iter()
            .map(|sa| {
                let mut keys = Vec::new();
                needed_keys(&sa.result, &mut keys);
                keys
            })
            .collect();
        let mut count: HashMap<Key<'t>, usize> = HashMap::new();
        for k in result_needs.iter().flatten() {
            *count.entry(*k).or_default() += 1;
        }
        let mut by_result: HashMap<Key<'t>, Vec<usize>> = HashMap::new();
        let mut any_result = Vec::new();
        for (i, keys) in result_needs.iter().enumerate() {
            match keys.iter().min_by_key(|k| count[*k]) {
                Some(&k) => by_result.entry(k).or_default().push(i),
                None => any_result.push(i),
            }
        }
        ArrowIndex {
            n: sas.len(),
            post,
            open,
            always,
            result_needs,
            by_result,
            any_result,
        }
    }

    /// For each key `qa`'s parameters need, at each parameter: the parameter and the arrows
    /// whose closed type there offers the key.
    fn needed(&self, qa: &'t Arrow) -> Vec<(usize, &[usize])> {
        let mut need = Vec::new();
        let mut keys = Vec::new();
        for (j, t) in qa.params.iter().enumerate().take(self.open.len()) {
            keys.clear();
            needed_keys(t, &mut keys);
            need.extend(
                keys.iter()
                    .map(|k| (j, self.post.get(&(j, *k)).map_or(&[][..], Vec::as_slice))),
            );
        }
        need
    }

    /// The keys `qa`'s result type offers, when it is closed: an arrow whose result needs a
    /// key outside them returns outside it.
    fn result_keys(qa: &'t Arrow) -> Option<HashSet<Key<'t>>> {
        let mut keys = Vec::new();
        offered_keys(&qa.result, &mut keys).then(|| keys.into_iter().collect())
    }

    /// The arrows whose results may be within a closed type that offers `keys`: those filed
    /// under one of them, and those whose results need no key.
    fn by_results(&self, keys: &HashSet<Key<'t>>) -> Vec<&[usize]> {
        let mut lists: Vec<&[usize]> = keys
            .iter()
            .filter_map(|k| self.by_result.get(k).map(Vec::as_slice))
            .collect();
        lists.push(&self.any_result);
        lists
    }

    /// The arrows of the shortest of `sources`, each the union of its lists, in order, kept
    /// when, at each parameter of `need`, the arrow is open or offers the key, and when
    /// `result` is given, it offers every key the arrow's result needs. Every arrow when there
    /// is no source. The cost is the shortest source's length times its logarithm, with the
    /// filter's cost ([`Self::keep_missing`]).
    fn candidates(
        &self,
        need: &[(usize, &[usize])],
        result: Option<&HashSet<Key<'t>>>,
        sources: Vec<Vec<&[usize]>>,
    ) -> Vec<usize> {
        let mut out: Vec<usize> = match sources
            .into_iter()
            .min_by_key(|lists| lists.iter().map(|l| l.len()).sum::<usize>())
        {
            Some(lists) => lists.into_iter().flatten().copied().collect(),
            None => (0..self.n).collect(),
        };
        out.sort_unstable();
        out.dedup();
        self.keep_missing(&mut out, need, result, 0);
        out
    }

    /// Keeps the arrows of `out`, in order without repeats, that miss at most `misses`
    /// parameters of `need` and, when `result` is given, offer every key their results need.
    /// An arrow misses a parameter when it is not open there and lacks a key `need` lists
    /// there.
    fn keep_missing(
        &self,
        out: &mut Vec<usize>,
        need: &[(usize, &[usize])],
        result: Option<&HashSet<Key<'t>>>,
        misses: usize,
    ) {
        // Complexity tradeoff (PERF-deep-ops-slow): naive, test each of the c arrows against
        // each of the e needed keys by a binary search in the key's list, O(c·e·log l),
        // quadratic when the arrows offer one key each of a parameter that needs one per
        // arrow (3200 arrows `(x: #ai | #a(i+1)) -> …` covering `(x: #a0 | … | #a3200)`:
        // 2.5·10^9 instructions). Here each key's list is walked against the arrows from the
        // shorter side, counting the keys each arrow offers at each parameter: O(Σ min(l·log c,
        // c·log l) + c·p) for p parameters with a key, at most the naive cost. Measured by
        // `l01_26_type_resolution::bench::scaling::many_arrows_whose_results_meet_only_on_different_sets_are_refused_in_linear_time`:
        // 12.3 times the instructions from 400 to 3200 arrows before, 8.3 times now.
        let mut params: Vec<usize> = need.iter().map(|e| e.0).collect();
        params.sort_unstable();
        params.dedup();
        let c = out.len();
        let mut wanted = vec![0usize; params.len()];
        let mut offered = vec![0usize; params.len() * c];
        for &(k, l) in need {
            let p = params.binary_search(&k).expect("a parameter of `need`");
            wanted[p] += 1;
            let row = &mut offered[p * c..(p + 1) * c];
            if l.len() <= c {
                // `l` is in order and may repeat an arrow that offers the key twice.
                for (at, &i) in l.iter().enumerate() {
                    if at > 0 && l[at - 1] == i {
                        continue;
                    }
                    if let Ok(x) = out.binary_search(&i) {
                        row[x] += 1;
                    }
                }
            } else {
                for (x, i) in out.iter().enumerate() {
                    row[x] += usize::from(l.binary_search(i).is_ok());
                }
            }
        }
        let mut x = 0;
        out.retain(|&i| {
            let missed = (0..params.len())
                .filter(|&p| !self.open[params[p]][i] && offered[p * c + x] < wanted[p])
                .count();
            x += 1;
            missed <= misses
                && result.is_none_or(|r| self.result_needs[i].iter().all(|k| r.contains(k)))
        });
    }

    /// The arrows that may fit `qa`, in order, to be tried until one fits. The candidates come
    /// from the shortest list: the arrows that offer one key `qa`'s parameters need, with the
    /// arrows open at that parameter, or the arrows whose results may be within `qa`'s closed
    /// result. Each is kept if, at every parameter, it is open or offers every key `qa` needs
    /// there, and its result needs no key `qa`'s closed result lacks.
    fn may_fit(&self, qa: &'t Arrow) -> Vec<usize> {
        let need = self.needed(qa);
        let result = Self::result_keys(qa);
        let mut sources: Vec<Vec<&[usize]>> = need
            .iter()
            .map(|&(j, l)| vec![l, &self.always[j][..]])
            .collect();
        if let Some(r) = &result {
            sources.push(self.by_results(r));
        }
        self.candidates(&need, result.as_ref(), sources)
    }

    /// The arrows that offer one key of `qa`'s parameter at `j` there, or are open there, when
    /// each piece of it has a key ([`piece_keys`]): an arrow outside them holds no value of it.
    fn pieces_at(&self, qa: &'t Arrow, j: usize) -> Option<Vec<&[usize]>> {
        let mut keys = Vec::new();
        piece_keys(&qa.params[j], &mut keys).then(|| {
            let mut lists: Vec<&[usize]> = keys
                .iter()
                .map(|k| self.post.get(&(j, *k)).map_or(&[][..], Vec::as_slice))
                .collect();
            lists.push(&self.always[j]);
            lists
        })
    }

    /// The arrows that may take part in covering `qa` at some parameter ([`covered`]): those
    /// that, at every parameter but at most one, are open or offer every key `qa` needs there,
    /// and whose results need no key `qa`'s closed result lacks. They come from the shortest
    /// source that holds every such arrow: the arrows whose results may be within `qa`'s; or
    /// the arrows that offer the key of the shortest list, at parameter `a`, or are open there,
    /// which hold each arrow that misses another parameter, with, for the arrows that miss
    /// `a`, the shortest list at another parameter or the arrows that offer a piece of `qa`'s
    /// parameter at `a`; or, when `qa` needs no key at any parameter, the arrows that offer a
    /// piece at some parameter. Every arrow when there is no source. With `by_result` false, the
    /// results filter nothing: the arrows that may take part in covering `qa` by intersection,
    /// whose results are outside `qa`'s ([`met`]).
    fn covering(&self, qa: &'t Arrow, by_result: bool) -> Vec<usize> {
        let need = self.needed(qa);
        let result = Self::result_keys(qa).filter(|_| by_result);
        let len = |lists: &[&[usize]]| lists.iter().map(|l| l.len()).sum::<usize>();
        let mut sources: Vec<Vec<&[usize]>> = Vec::new();
        if let Some(r) = &result {
            sources.push(self.by_results(r));
        }
        // The shortest source of one needed key, at a parameter `at` admits, with its parameter.
        let shortest = |at: &dyn Fn(usize) -> bool| {
            need.iter()
                .filter(|e| at(e.0))
                .map(|&(k, l)| (k, vec![l, &self.always[k][..]]))
                .min_by_key(|(_, lists)| len(lists))
        };
        if let Some((a, first)) = shortest(&|_| true) {
            let other = [shortest(&|k| k != a).map(|e| e.1), self.pieces_at(qa, a)]
                .into_iter()
                .flatten()
                .min_by_key(|lists| len(lists));
            if let Some(other) = other {
                sources.push(first.into_iter().chain(other).collect());
            }
        } else {
            let width = qa.params.len().min(self.open.len());
            let pieces: Option<Vec<Vec<&[usize]>>> =
                (0..width).map(|j| self.pieces_at(qa, j)).collect();
            if let Some(pieces) = pieces.filter(|p| !p.is_empty()) {
                sources.push(pieces.into_iter().flatten().collect());
            }
        }
        let mut out: Vec<usize> = match sources.into_iter().min_by_key(|lists| len(lists)) {
            Some(lists) => lists.into_iter().flatten().copied().collect(),
            None => (0..self.n).collect(),
        };
        out.sort_unstable();
        out.dedup();
        self.keep_missing(&mut out, &need, result.as_ref(), 1);
        out
    }
}

impl PartialEq for Sig {
    /// Compares the types of the arrows with a `Same`, which needs no stack as deep as they
    /// are: a function type nests functions as deep as the program.
    fn eq(&self, other: &Sig) -> bool {
        let mut same = Same::default();
        same.sig(self, other) && same.rest()
    }
}

impl std::hash::Hash for Sig {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        h.write_u64(self.digest());
    }
}

/// Whether the arrow `sa` of `s` takes the parameters of the arrow `qa` and returns within its
/// result, each bounded variable of `s` bound to carriers of its bound ([`fits_in`]).
///
/// Where the result puts ceilings on the variables ([`ceilings`]), the parameters are compared
/// first within them, as an attempt of its own ([`Comparing::begin_alone`]), and, where that
/// fails, again with no ceiling, first-fit as before. So the ceilings only add fits: a fit
/// found with no ceiling is still found. A loop, not a second call of a helper, so that each
/// depth of function types puts one future on the stack, as before.
///
/// Complexity tradeoff: at most two comparisons of the parameters per arrow, the second only
/// where the first fails; a function type nested in a parameter is compared once for each
/// pair of names ([`Comparing::fits_read`]), so the second attempt reads its verdict, and the
/// attempts do not multiply with the depth.
async fn arrow_fits<'m>(s: &Sig, sa: &Arrow, qa: &Arrow, c: &'m Comparing<'m, '_>) -> bool {
    // Assumption, not proved (ASSUME-documented): the ceilings only remove fits that would fail
    // anyway, and the retry with `Binds::of_arrow(s, sa, None, ..)` finds every fit that the
    // comparison with no ceiling finds, even though the first attempt leaves `fitted`, the
    // `compared` entries keyed with ceilings, and the pins behind it. The ceilings do reject
    // pieces by design; what is assumed is only the final verdict. Evidence: the l01_26 groups
    // and the others affected, 323 to 325 pieces with 0 failures; benchmark 8.61x. If false, a
    // function that fits is found not to fit and a correct program is rejected: precision,
    // unless a caller reads a false here as proof that the function does not fit.
    let mut b = Binds::of_arrow(s, sa, Some(&qa.result), &c.cx.borrow());
    // Why the attempt within the ceilings was refused, if it was: then it may have found a fit
    // the attempt with no ceiling does not, so where that one fails too, the comparison is
    // refused, not decided false.
    let mut refused = None;
    loop {
        let before = b.ceilings.is_some().then(|| c.begin_alone());
        let mut ok = true;
        for (x, y) in qa.params.iter().zip(&sa.params) {
            if !c.sub_in(x, y, &mut b).await {
                ok = false;
                break;
            }
        }
        ok = ok && bounds_hold(s, sa, &b, &c.cx.borrow());
        ok = ok && result_within(s, sa, qa, &b, c).await;
        ok = ok && instance_within(s, sa, qa, &b, c).await;
        let Some(before) = before else {
            if let Some(why) = refused.filter(|_| !ok) {
                c.refuse(|| why);
            }
            return ok;
        };
        refused = c.end_alone(before);
        if refused.is_none() && ok {
            return true;
        }
        b = Binds::of_arrow(s, sa, None, &c.cx.borrow());
    }
}

/// Whether each bounded variable of `s` that `b` binds is bound to carriers of its bound, and,
/// when bound to values of more than one carrier, stands where the arrow `sa` may take them
/// ([`one_place`]). A call fixes the variable to one carrier, so `(x: T, y: T) -> T for T in
/// int | f64` bound to `int | f64` would be called with an `int` and an `f64`, which no call
/// of it is.
fn bounds_hold(s: &Sig, sa: &Arrow, b: &Binds, cx: &Cx) -> bool {
    s.bounds.iter().all(|(v, &m)| {
        b.get(v)
            .is_none_or(|t| match t.as_var().and_then(|w| var_mask(w, cx)) {
                // Each carrier the caller of `q` may pick, or the comparison that binds the
                // variable may bind it to, is one `s` takes.
                Some(mq) => mq & !m == 0,
                // `v` is one carrier at a call, so it cannot be a variable of several carriers
                // and something else at once.
                None => {
                    t.pieces().iter().all(|p| piece_within(p, m, cx))
                        && (one_carrier(t, cx) || one_place(sa, v, cx))
                }
            })
    })
}

/// Whether the piece `p` of what a variable of bound `m` is bound to, with other pieces or
/// alone, is within the bound ([`bounds_hold`]): of a carrier of it ([`carrier_of`]), or of
/// none where `m` holds [`OTHER`], neither the unknown nor a variable of a known mask of
/// several carriers ([`var_mask`]), which with other pieces stands for one carrier and
/// something else at once.
fn piece_within(p: &Piece, m: u8, cx: &Cx) -> bool {
    match carrier_of(p, cx) {
        Some(c) => m & c.bit() != 0,
        None => {
            m & OTHER != 0
                && !matches!(p, Piece::Dyn)
                && !matches!(p, Piece::Var(w) if var_mask(w, cx).is_some())
        }
    }
}

/// The ceilings of the variables `free` holds that the result `sr` of an arrow of `s` names,
/// compared with the result `qr` of an arrow of `q` ([`Binds::of_arrow`]): for each, a type
/// that holds every piece of its binding wherever `sr`, so bound, is within `qr`
/// ([`result_within`]), when the two results give one. `sr` is the variable: `qr`. A component
/// of a tuple shape of `sr` of length k is the variable, and `qr` holds no kind-wide part,
/// `(..)` or `{..}`, only tuple shapes: the union of the component at that place of `qr`'s
/// shapes of length k, as a tuple of `sr` is within `qr` only in one of them. Otherwise none.
///
/// A ceiling only tells [`accepts`] which variable not to bind to a piece the ceiling cannot
/// hold, so that the search goes on to the next shape ([`Comparing::search`]): `(X,) | (W,)`
/// in `(T,) | (U,)`, for `(x0: (T,) | (U,)) -> (T,)` compared with `(x0: (X,) | (W,)) ->
/// (X,)`, binds `T` to `X` and `U` to `W` in either order of the members, where the first shape
/// took both (FAIL-types-first-shape-unbounded); and `(T, V)` with each variable in a
/// parameter of its own. A ceiling is a necessary condition only where the tuple holds a
/// value: `(T, V)` with `V` bound to `Never` holds none, whatever `T` is. So [`arrow_fits`]
/// compares again with no ceiling where the comparison within them fails, and no fit found
/// first-fit is lost.
///
/// Complexity tradeoff: naive version, each shape of the parameter tried for each piece with
/// the result compared at the end, backtracking over the shapes: exponential in the members
/// of a union. Used: the condition the result puts on each variable read once, from the two
/// results, before the parameters are compared, and checked on each piece as it is bound
/// (`may_be_within`, O(1) for a variable or a set of scalars), so first-fit stays first-fit
/// on the shapes the result leaves; one walk of `sr` and of `qr`'s shapes per arrow compared,
/// each place of `qr`'s shapes of one length joined once, not once per variable there.
/// What is given up: a variable whose ceiling holds two shapes alike, or with no ceiling, is
/// still bound first-fit; [`Comparing::search`] refuses where two members of one union each
/// fail a shape no pin leaves out. Prior work: the upper bounds that local type inference
/// propagates from the expected type into the arguments (Pierce and Turner, "Local Type
/// Inference", TOPLAS 2000), here only one level deep.
fn ceilings(sr: &Ty, qr: &Ty, free: &impl Fn(&str) -> bool) -> Option<Ceilings> {
    if qr.dynamic {
        return None;
    }
    let mut out: BTreeMap<Arc<str>, Ty> = BTreeMap::new();
    if let Some(v) = sr.as_var() {
        if free(v) {
            out.insert(v.clone(), qr.clone());
        }
    } else if (&qr.set & &wide()).is_empty() {
        // `qr`'s shapes by length, and the union at each place read once: each shape of `qr`
        // is walked once whatever the shapes of `sr`.
        let mut by_len: HashMap<usize, Vec<&Row>> = HashMap::new();
        for q in &qr.tuples {
            by_len.entry(q.len()).or_default().push(q);
        }
        let mut at: HashMap<(usize, usize), Ty> = HashMap::new();
        for r in &sr.tuples {
            for (i, c) in r.iter().enumerate() {
                let Some(v) = c.as_var().filter(|v| free(v) && !out.contains_key(*v)) else {
                    continue;
                };
                let ceil = at.entry((r.len(), i)).or_insert_with(|| {
                    let shapes = by_len.get(&r.len()).map_or(&[][..], Vec::as_slice);
                    Ty::union_all(shapes.iter().map(|q| &q[i]))
                });
                out.insert(v.clone(), ceil.clone());
            }
        }
    }
    (!out.is_empty()).then(|| out.into_iter().collect())
}

/// Whether the piece `p` may be within the ceiling `ceil` of a variable ([`ceilings`]): false
/// only where it surely is not, as [`result_within`] compares, where no variable of the
/// result of `q` may be bound. Cost: O(1) for a variable, a check of the sets for scalars.
fn may_be_within(p: &Piece, ceil: &Ty, cx: &Cx) -> bool {
    let special = |w: &Arc<str>| cx.rigid.contains_key(w) || cx.fns.contains_key(w);
    // Complexity tradeoff (FAIL-types-binding-union-copied): naive version, each variable of
    // the ceiling looked up among the rigid and function variables, O(c log r) per piece, so
    // a variable taking n members within a ceiling of n variables cost O(n^2 log n). Used: the
    // smaller of the two sides walked and looked up in the other, O(min(c, r) log max(c, r));
    // the answer is the same either way.
    let specials = cx.rigid.len() + cx.fns.len();
    let holds_special = match ceil.vars.len() <= specials {
        true => ceil.vars.iter().any(special),
        false => (cx.rigid.keys().chain(cx.fns.keys())).any(|w| ceil.vars.contains(w)),
    };
    if ceil.dynamic || holds_special {
        return true;
    }
    match p {
        Piece::Var(w) => special(w) || ceil.vars.contains(w),
        Piece::Set(s) => s.subtype(&ceil.set) || !ceil.tuples.is_empty() || !ceil.fns.is_empty(),
        Piece::Tuple(_) | Piece::Fn(_) | Piece::Dyn => true,
    }
}

/// The mask of the carriers the variable `w` is of, where the comparison knows it: a rigid
/// variable's ([`Cx::rigid`]), or the bound of a bounded own variable of a comparison open now
/// ([`Cx::own_bounds`]), which that comparison binds within its bound. A variable of no known
/// mask, free or unbounded, may be of any type.
fn var_mask(w: &str, cx: &Cx) -> Option<u8> {
    (cx.rigid.get(w).copied()).or_else(|| cx.own_bounds.get(w).copied())
}

/// The carrier of the piece `p`: its own ([`Piece::carrier`]), or, for a variable whose mask
/// ([`var_mask`]) is one carrier, that carrier, which each value it stands for is of. `V` of
/// `for V in int` beside `int` is then one carrier, as `int` beside `int` is; read as a
/// variable of no carrier, `T` bound to `V | int` failed [`bounds_hold`] though it is one
/// carrier.
fn carrier_of(p: &Piece, cx: &Cx) -> Option<Carrier> {
    match p {
        Piece::Var(w) => var_mask(w, cx).and_then(mask_carrier),
        _ => p.carrier(),
    }
}

/// The one carrier the mask `m` holds, if it holds one and nothing else.
fn mask_carrier(m: u8) -> Option<Carrier> {
    let mut carriers = Carrier::of_mask(m);
    match (carriers.next(), carriers.next()) {
        (Some(c), None) if m & OTHER == 0 => Some(c),
        _ => None,
    }
}

/// Whether the values of `t` are of one carrier, or of none, a rigid variable of one carrier
/// read as that carrier ([`carrier_of`]).
fn one_carrier(t: &Ty, cx: &Cx) -> bool {
    let mut carriers = t.pieces().into_iter().map(|p| carrier_of(&p, cx));
    let first = carriers.next().flatten();
    carriers.all(|c| c == first)
}

/// Whether the variable `v` stands in the arrow `sa`, as read, at one place where an argument
/// gives its values, outside every function type, and elsewhere only where the arrow gives
/// values of it: in its result, or in a parameter of a function type a parameter takes. Then
/// `v` bound to values of several carriers takes, at each value of that place, the arrow at
/// that value's carrier, which returns within the arrow at all of them. A second place an
/// argument fixes, or a place the arrow takes values at inside a function type (a parameter of
/// a function it returns, the result of a function it takes), would need one carrier at both.
/// The cost is a walk of `sa`.
fn one_place(sa: &Arrow, v: &str, cx: &Cx) -> bool {
    let places = Places::of(sa, v, cx);
    places.given == 1 && places.taken == 0
}

/// The places of a variable in an arrow ([`one_place`]).
#[derive(Default)]
struct Places {
    /// Those where an argument gives its values, outside every function type.
    given: usize,
    /// Those where the arrow takes values of it, inside a function type.
    taken: usize,
}

impl Places {
    /// The places of `v` in the arrow `sa`, as read.
    fn of(sa: &Arrow, v: &str, cx: &Cx) -> Places {
        let mut places = Places::default();
        let mut stack: Vec<(&Ty, bool, bool)> =
            sa.params.iter().map(|p| (p, false, true)).collect();
        stack.push((&sa.result, true, true));
        places.walk(stack, v, cx);
        places
    }

    /// Counts the places of `v` in each type `t` of `stack`, with `(t, out, top)`: the arrow
    /// gives values of `t` when `out` and takes values of it when not, outside every function
    /// type when `top`. A function type read as a variable ([`Cx::read`]) is walked as its
    /// signature; one that binds `v` itself does not hold this `v`. The parts are walked on an
    /// explicit stack, so a type nested to any depth needs no more of the thread's stack; the
    /// counts do not depend on the order.
    fn walk<'t>(&mut self, mut stack: Vec<(&'t Ty, bool, bool)>, v: &str, cx: &'t Cx) {
        while let Some((t, out, top)) = stack.pop() {
            if !out && t.vars.contains(v) {
                match top {
                    true => self.given += 1,
                    false => self.taken += 1,
                }
            }
            for c in t.tuples.iter().flat_map(|r| r.iter()) {
                stack.push((c, out, top));
            }
            let read = t.vars.iter().filter_map(|w| cx.fns.get(w).map(|e| &e.0));
            for s in t.fns.iter().chain(read) {
                if s.own.contains(v) {
                    continue;
                }
                for a in &s.arrows {
                    for p in &a.params {
                        stack.push((p, !out, false));
                    }
                    stack.push((&a.result, out, false));
                }
            }
        }
    }
}

/// Whether the result of `sa`, an arrow of `s`, its variables bound by `b`, is within `qa`'s,
/// binding nothing.
async fn result_within<'m>(
    s: &Sig,
    sa: &Arrow,
    qa: &Arrow,
    b: &Binds,
    c: &'m Comparing<'m, '_>,
) -> bool {
    let mut rb = Binds::new();
    let r = result_bound(s, sa, b, c);
    c.sub_in(&r, &qa.result, &mut rb).await && rb.is_empty()
}

/// The result of `sa`, an arrow of `s`, with its variables bound by `b`: outside functions by
/// [`Ty::subst`], and inside the functions it holds by reading them anew
/// ([`Cx::bound_in_fns`]).
fn result_bound(s: &Sig, sa: &Arrow, b: &Binds, c: &Comparing) -> Ty {
    let fns = c.cx.borrow_mut().bound_in_fns(s, &sa.result, b);
    sa.result.subst(&fns).subst(b)
}

impl Sig {
    /// Sets [`Sig::held`] from its parameters, at any depth, on any arrow: for a signature
    /// built from parts, at the cost of a walk of its parameters.
    pub fn note_held(&mut self) {
        debug_assert!(
            self.facts.0.get().is_none() && self.facts.2.get().is_none(),
            "a signature is changed after its facts were read"
        );
        self.held.clear();
        if self.bounds.is_empty() {
            return;
        }
        let mut vs = Vars::default();
        for a in &self.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut vs));
        }
        self.held = vs
            .order
            .into_iter()
            .filter(|v| self.own.contains(v) && self.bounds.contains_key(v))
            .collect();
    }

    /// It with each class variable `solve` gives a type replaced by that type at every depth.
    pub fn solved_with(&self, solve: Solve) -> Sig {
        let mut vs = Vars::default();
        for a in &self.arrows {
            a.params.iter().for_each(|p| p.vars_in(&mut vs));
            a.result.vars_in(&mut vs);
        }
        self.needs.iter().for_each(|n| n.vars_in(&mut vs));
        let binds: Binds = (vs.order.into_iter())
            .filter_map(|v| solve(&v).map(|t| (v, t)))
            .collect();
        self.replace(&binds)
    }

    /// Its own bounded variables no parameter holds, each bound to [`Ty::of_mask`] of its
    /// bound: no argument fixes its carrier, so a call returns a value of some carrier of it.
    pub fn unheld(&self) -> Binds {
        self.bounds
            .iter()
            .filter(|(v, _)| self.own.contains(*v) && !self.held.contains(*v))
            .map(|(v, &m)| (v.clone(), Ty::of_mask(m)))
            .collect()
    }

    /// Its hash, made at the first call from its parts, each function it holds by its own
    /// hash: so it is asked of a signature held in a type, which no longer changes. Hashed
    /// whole, a set of the functions of `g(0)(1)…(n)` cost the depth of each (CHK-carrier).
    pub fn digest(&self) -> u64 {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let hash = |s: &Sig| {
            *s.facts.2.get_or_init(|| {
                let parts = (&s.params, &s.arrows, &s.bounds, s.data, s.dense, &s.word);
                let more = (&s.needs, &s.own, &s.held, s.named, &s.hull, &s.keys);
                BuildHasherDefault::<DefaultHasher>::default().hash_one((parts, more))
            })
        };
        if let Some(&d) = self.facts.2.get() {
            return d;
        }
        // The hashes of the functions it holds that lack one are made first, deepest first, as
        // for its facts ([`Sig::facts`]).
        for s in self.held_without(true, |s| s.facts.2.get().is_none()) {
            hash(s);
        }
        hash(self)
    }

    /// The variables it holds at any depth: worked out at the first call, so it is asked of
    /// a signature held in a type, which no longer changes.
    pub fn facts(&self) -> &VarFacts {
        if let Some(f) = self.facts.0.get() {
            return f;
        }
        // The facts of a signature are made from those of the functions it holds, so those
        // that lack them are worked out first, deepest first, on a stack of its own: asked of
        // the outermost of a nest of n functions, the facts would otherwise recurse n deep.
        for s in self.held_without(false, |s| s.facts.0.get().is_none()) {
            s.facts.0.get_or_init(|| VarFacts::of(s));
        }
        self.facts.0.get_or_init(|| VarFacts::of(self))
    }

    /// Its variables in order of first appearance, as [`Ty::vars_in`] gives those of the
    /// types of its arrows and then of its needs ([`Need::tys`]): worked out by one walk at
    /// the first call and kept, so it is asked of a signature held in a type, which no longer
    /// changes. A later walk that meets this signature reads the order in place of entering it
    /// (`vars_of`); the functions it holds keep none of their own unless asked.
    pub fn vars_order(&self) -> &[Arc<str>] {
        self.facts.4.get_or_init(|| {
            let mut out = Vars::default();
            vars_of(sig_tys(self), &mut out);
            out.order.into()
        })
    }

    /// Whether it holds no variable at any depth, functions it holds included: whether
    /// [`Sig::vars_order`] is empty. Worked out at the first call, for it and for each function
    /// it holds that lacks the answer, innermost first, and kept, as the other facts are: a
    /// signature is not changed once made, and a clone starts with no facts.
    ///
    /// The walk is that of `vars_of`: the types `sig_tys` gives, entering each row that is
    /// not fixed and each payload shape that may hold a variable, once each; a function met is
    /// read by its own answer (or its kept order) in place of being entered. It holds no
    /// variable when none of those types does and each function met holds none, as `vars_of`
    /// then adds nothing (`found_in_nest`).
    // Complexity tradeoff (FAIL-l01-26-deep-bench-bytes): the naive version, `vars_order()`
    // and a test for empty, keeps an order only for the signature asked, so asked of each of n
    // nested functions from the outermost in, as a comparison reads them (`Cx::read_outer`),
    // each walk enters every function below it: Θ(n^2) time and bytes, 2,051,638,488 bytes on
    // the first comparison of `(int) -> …` 8,000 deep against 48,546,152 at 1,000 (42.3 times).
    // Keeping the order at each function met is O(n^2) in memory for nested lambdas that each
    // hold all n variables (FAIL-returned-chain-quadratic, at `vars_of`). Used: one answer per
    // signature, filled innermost first, so the types of each signature outside functions are
    // walked once in all, O(size) for a nest asked in any order. Tradeoffs: a seventh
    // `OnceLock` per signature, which keeps whether it holds a variable.
    pub fn holds_no_variable(&self) -> bool {
        /// Whether it holds a variable, if known: kept, or read from its kept order.
        fn known(s: &Sig) -> Option<bool> {
            (s.facts.6.get().copied()).or_else(|| s.facts.4.get().map(|o| !o.is_empty()))
        }
        !found_in_nest(
            self,
            known,
            |s, b| {
                let _ = s.facts.6.set(b);
            },
            |s| fns_outside(s, |_| false),
        )
    }

    /// Whether each variable it holds, at any depth, is an own variable of the signature that
    /// holds it outside functions, or of a function around that one within it: whether it
    /// holds only its own variables and those of the functions inside it. Each signature of
    /// the nest is asked whether every variable its types hold outside functions is its own
    /// ([`Sig::own`]); a variable of a function around it within the nest is not taken, so the
    /// answer is false for `(x: T) -> (y: T) -> T for T in int`, whose inner function holds the
    /// `T` of the outer one. Such a signature reads the same in any comparison: every variable
    /// it holds is bound by a signature within it. Worked out at the first call, for it and for
    /// each function it holds that lacks the answer, innermost first, and kept, as
    /// [`Sig::holds_no_variable`] is (`found_in_nest`), so a nest asked from the outermost
    /// in costs its size once.
    pub fn holds_only_own_variables(&self) -> bool {
        !found_in_nest(
            self,
            |s| s.facts.9.get().map(|own_only| !own_only),
            |s, b| {
                let _ = s.facts.9.set(!b);
            },
            |s| fns_outside(s, |v| s.own.contains(v)),
        )
    }

    /// Whether it has needs, or a function its arrows return at any depth has: such a
    /// function is checked by its calls, not as a type alone. Only the functions each result
    /// holds at its top are read, not those in its tuples or payloads. Worked out at the first
    /// call, for it and each function so returned that lacks the answer, innermost first, and
    /// kept, as [`Sig::holds_no_variable`] is.
    // Complexity tradeoff (FAIL-power-returned-n-deep-ratio): the naive version walks the
    // functions returned below it at each ask, with a set of those seen, so a call through each
    // of n nested returned functions walks the n below it: Θ(n^2) (31 times the work at 8n for
    // `2 ^ k` returned through n arrows). Used: one answer per signature, filled innermost
    // first ([`found_in_nest`]), so each signature's arrows are read once in all. Tradeoffs:
    // an eighth `OnceLock` per signature.
    pub fn holds_needs(&self) -> bool {
        found_in_nest(
            self,
            |s| s.facts.7.get().copied(),
            |s, b| {
                let _ = s.facts.7.set(b);
            },
            |s| {
                let fns = s.arrows.iter().flat_map(|a| a.result.fns.iter());
                s.needs.is_empty().then(|| fns.map(|f| &**f).collect())
            },
        )
    }

    /// Whether it has needs, or a value one of its results describes may hold a function with
    /// needs ([`Ty::may_hold_needs`]): its results are read as types, through their tuples,
    /// payloads and functions at any depth. Worked out at the first call, for it and each
    /// function its results hold that lacks the answer, innermost first, and kept, as
    /// [`Sig::holds_needs`] is.
    // Complexity tradeoff (FAIL-power-returned-n-deep-ratio): as in [`Sig::holds_needs`], the
    // naive walk of the results below it at each ask is Θ(n^2) for a call through each of n
    // nested returned functions. Used: one answer per signature ([`found_in_nest`]); each
    // result's outer level is read once, its rows and shapes keeping their own answers.
    // Tradeoffs: a ninth `OnceLock` per signature.
    pub fn may_hold_needs(&self) -> bool {
        found_in_nest(
            self,
            |s| s.facts.8.get().copied(),
            |s, b| {
                let _ = s.facts.8.set(b);
            },
            |s| {
                let results = || s.arrows.iter().map(|a| &a.result);
                let here = !s.needs.is_empty() || results().any(Ty::may_hold_needs_outside_fns);
                let fns = results().flat_map(|r| r.fns.iter());
                (!here).then(|| fns.map(|f| &**f).collect())
            },
        )
    }

    /// Whether a type of its arrows or needs ([`sig_tys`]), at any depth, inside the functions
    /// it holds too, holds the unknown beside another member ([`Ty::may_absorb`]). Worked out
    /// at the first call, for it and each function below it that lacks the answer, innermost
    /// first, and kept, as [`Sig::may_hold_needs`] is; the complexity tradeoff is
    /// [`Ty::may_absorb`]'s.
    fn may_absorb(&self) -> bool {
        found_in_nest(
            self,
            |s| s.facts.10.get().copied(),
            |s, b| {
                let _ = s.facts.10.set(b);
            },
            |s| {
                let here = sig_tys(s).any(Ty::may_absorb_outside_fns);
                let fns = sig_tys(s).flat_map(|t| t.fns.iter());
                (!here).then(|| fns.map(|f| &**f).collect())
            },
        )
    }

    /// The bits of its variables, made from its facts at the first call.
    fn bits(&self) -> VarBits {
        *self.facts.3.get_or_init(|| VarBits::of_facts(self.facts()))
    }

    /// The signatures of the functions it holds at any depth for which `lacks` holds, each
    /// after those it holds and once: the walk stops at a signature for which `lacks` fails,
    /// so it costs the signatures returned and their parts. It looks in the types of the
    /// arrows and in those of the needs that [`Need::tys`] gives, or in every type of each
    /// need if `whole`. A row or payload keeps what it holds worked out when it is built.
    fn held_without<'s>(&'s self, whole: bool, lacks: impl Fn(&Sig) -> bool) -> Vec<&'s Sig> {
        let fns = |s: &'s Sig| -> Vec<&'s Sig> {
            let arrows = s
                .arrows
                .iter()
                .flat_map(|a| a.params.iter().chain([&a.result]));
            let needs = s.needs.iter().flat_map(|n| match whole {
                true => n.every_ty(),
                false => n.tys().collect(),
            });
            arrows
                .chain(needs)
                .flat_map(|t| t.fns.iter().map(|f| &**f))
                .collect()
        };
        // `seen` by address: every signature is borrowed from `self` for the whole walk, so no
        // key names a freed one, and the set is only read by insert, never iterated; `order`
        // keeps the order.
        let (mut seen, mut order) = (HashSet::new(), Vec::new());
        // Each signature is entered with the signatures it holds still to visit, and left
        // once they are done.
        let mut stack: Vec<(&Sig, Vec<&Sig>)> = vec![(self, fns(self))];
        while let Some((_, todo)) = stack.last_mut() {
            match todo.pop() {
                Some(s) if lacks(s) && seen.insert(s as *const Sig) => stack.push((s, fns(s))),
                Some(_) => {}
                None => order.extend(stack.pop().map(|(s, _)| s)),
            }
        }
        order.pop(); // `self`, left last.
        order
    }

    /// It with each class variable `solve` gives a type replaced by that type at every depth:
    /// made at the first call and kept, so it is asked only when no class changes after,
    /// as the checker finishes. A signature that holds no class variable is itself.
    pub fn settle(self: &Arc<Sig>, solve: Solve) -> Arc<Sig> {
        if self.facts().classes.is_empty() {
            return self.clone();
        }
        let made = Vec::new();
        rebuild_held(&mut Settle { solve, made }, self)
    }

    /// The class variables of `want` that its arrows and needs hold, in the order in which
    /// [`Ty::vars_in`] meets them. The walk enters no function whose facts hold none of those
    /// still unseen, and it stops once all are seen, so it costs no more than replacing them.
    /// A row or payload shape met again is shared and was walked whole the first time, so it
    /// is entered once.
    pub fn first_seen(&self, want: &HashSet<Arc<str>>) -> Vec<Arc<str>> {
        enum Item<'a> {
            Ty(&'a Ty),
            Row(&'a Row),
            Shape(&'a Shape),
            Sig(&'a Sig),
        }
        let mut out = Vec::new();
        let mut left = want.clone();
        // By address: every row and shape is borrowed from `self` for the whole walk, so no key
        // names a freed node, and the set is only read by insert, never iterated.
        let mut entered: HashSet<*const ()> = HashSet::new();
        let mut stack = vec![Item::Sig(self)];
        while let Some(item) = stack.pop()
            && !left.is_empty()
        {
            let at = stack.len();
            match item {
                Item::Sig(s) => {
                    // `self` may still change, so its facts are not kept; it is entered.
                    if !std::ptr::eq(s, self) {
                        let classes = &s.facts().classes;
                        let any = match classes.len() < left.len() {
                            true => classes.iter().any(|v| left.contains(v)),
                            false => left.iter().any(|v| classes.contains(v)),
                        };
                        if !any {
                            continue;
                        }
                    }
                    let tys = s
                        .arrows
                        .iter()
                        .flat_map(|a| a.params.iter().chain([&a.result]));
                    let needs = s.needs.iter().flat_map(Need::tys);
                    stack.extend(tys.chain(needs).map(Item::Ty));
                }
                Item::Row(r) => {
                    if entered.insert(r.addr()) {
                        stack.extend(r.iter().map(Item::Ty));
                    }
                }
                Item::Shape(s) => {
                    if entered.insert(s.as_ptr().cast()) {
                        stack.extend(s.items.iter().chain(s.fields.values()).map(Item::Ty));
                    }
                }
                Item::Ty(t) => {
                    out.extend(t.vars.iter().filter(|v| left.remove(*v)).cloned());
                    stack.extend(t.tuples.iter().map(Item::Row));
                    stack.extend(t.payloads.values().flatten().flatten().map(Item::Shape));
                    stack.extend(t.fns.iter().map(|s| Item::Sig(s)));
                }
            }
            stack[at..].reverse();
        }
        out
    }

    /// The signature `s` holds, to be changed: moved out when `s` is its only holder, else
    /// cloned, and either way with its facts ([`Facts`]) dropped, since they may have been
    /// read while it was held. A signature put in a type has its hash read at once
    /// ([`Members::push`]), so `Arc::unwrap_or_clone` alone gives back a signature whose kept
    /// hash no longer matches it once changed, and two equal types then compare unequal.
    pub fn unwrap_to_change(s: Arc<Sig>) -> Sig {
        let mut s = Arc::unwrap_or_clone(s);
        s.facts = Facts::default();
        s
    }

    /// One arrow over `params` and `result`, with no bounded variable.
    pub fn one(params: Vec<SParam>, tys: Vec<Ty>, result: Ty) -> Sig {
        Sig {
            params,
            arrows: vec![Arrow {
                params: tys,
                result,
                partial: false,
            }],
            bounds: BTreeMap::new(),
            data: false,
            dense: Dense::No,
            keys: None,
            word: None,
            needs: Vec::new(),
            own: BTreeSet::new(),
            held: BTreeSet::new(),
            named: 0,
            hull: None,
            facts: Default::default(),
        }
    }

    /// Its parameter list as a comparison of signatures sees it: for each parameter, whether
    /// it is passed by position, and its name where it is not. A function is a function of
    /// another signature only where the two lists are equal ([`fits_sig`]).
    pub fn param_list(&self) -> ParamList {
        (self.params.iter())
            .map(|p| (p.positional, (!p.positional).then(|| p.name.clone())))
            .collect()
    }

    /// Adds the arrows of `q` after its own, and `q`'s bounded and own variables and needs:
    /// it becomes the intersection of the two function types, as `s & q` is read when the two
    /// take the same parameters.
    pub fn add_arrows_of(&mut self, q: &Sig) {
        self.arrows.extend(q.arrows.iter().cloned());
        (self.bounds).extend(q.bounds.iter().map(|(v, m)| (v.clone(), *m)));
        self.own.extend(q.own.iter().cloned());
        self.held.extend(q.held.iter().cloned());
        self.needs.extend(q.needs.iter().cloned());
    }

    /// It with its variables replaced by `binds` at every depth; a bounded variable replaced
    /// by another variable keeps its bound under the new name.
    pub fn replace(&self, binds: &Binds) -> Sig {
        self.replace_in(binds, Mode::Replace)
    }

    /// It with the variables `names` gives other names, as [`Ty::renamed`] does.
    pub fn renamed(&self, names: &Binds) -> Sig {
        self.replace_in(names, Mode::Rename)
    }

    /// It with its variables replaced by `binds` in its arrows and needs, outside the functions
    /// they hold ([`Ty::replace_outside`]).
    pub fn replace_outside(&self, binds: &Binds) -> Sig {
        self.replace_in(binds, Mode::Outside)
    }

    /// [`Sig::replace`], or as `mode` says: renamed, its own and held variables take their new
    /// names.
    fn replace_in(&self, binds: &Binds, mode: Mode) -> Sig {
        Replacer::new(binds, mode).sig(self)
    }

    /// Its arrows with each bounded variable fixed to each carrier of its bound: the product
    /// of the bounds, as long as that product is.
    pub fn expand(&self) -> Vec<Arrow> {
        let mut out = self.arrows.clone();
        for (v, m) in &self.bounds {
            out = out
                .iter()
                .flat_map(|a| {
                    Carrier::of_mask(*m).map(move |c| {
                        let b: Binds = [(v.clone(), Ty::carrier(c))].into();
                        Arrow {
                            params: a.params.iter().map(|p| p.replace(&b)).collect(),
                            result: a.result.replace(&b),
                            partial: a.partial,
                        }
                    })
                })
                .collect();
        }
        out
    }

    /// For each parameter, whether every value it takes on every arrow is an `int`: its type
    /// on each arrow is `int` or a refinement of it, and each type variable it holds ranges
    /// over `int` alone. A parameter of a variable bounded by `int | f64 | rat`, of `f64` or of
    /// `rat` is not, and neither is one that may hold an atom, a tuple, a function or the
    /// unknown. Rung 2 reads `+`, `-`, `*`, `div`, `mod`, `-x` and the comparisons as integer
    /// arithmetic, so its callers pass it only these parameters (RUNG2-carrier). Without
    /// [`Sig::expand`]'s product of the bounds: O(arrows × parameters), each type's scalar set
    /// tested once.
    pub fn int_params(&self) -> Vec<bool> {
        let int = KType::int();
        let only_int = Carrier::Int.bit();
        let is_int = |p: &Ty| {
            !p.dynamic
                && p.fns.is_empty()
                && p.tuples.is_empty()
                && (p.vars.iter()).all(|v| self.bounds.get(v) == Some(&only_int))
                && p.set.subtype(&int)
        };
        (0..self.params.len())
            .map(|i| {
                !self.arrows.is_empty()
                    && (self.arrows.iter()).all(|a| a.params.get(i).is_some_and(is_int))
            })
            .collect()
    }

    /// The parameters a call may pass as `name:`, each by its index and name, in order: every
    /// parameter not passed by position, and the one parameter of a signature that has one,
    /// either way (DESIGN.md sec:values_morphisms, "A function with one parameter takes its
    /// argument in either form"). A name that is not a name a call can write is left out: the
    /// text `(a, b)` of a tuple-destructuring parameter (`ast::Param::name`) and the empty
    /// name of a function type's unnamed parameter. These names are part of an exported
    /// function's interface, so its content address keeps them (DESIGN.md sec:units, "Imports
    /// pin hashes"). O(parameters × name length).
    // The rule is that of the resolver's overload index (`zedc_resolve::resolve::pick::arm`),
    // where each parameter of a function with one is entered as named whatever its mark, and
    // any other only when it is neither `positional` nor a tuple; here a tuple parameter is
    // told by its name, which `ast::Param::name` makes its text and so never a name.
    pub fn callable_names(&self) -> Vec<(u32, Arc<str>)> {
        let one = self.params.len() == 1;
        let written = |n: &str| zedc_syntax::lex::name_end(n, 0) == Some(n.len());
        (self.params.iter().enumerate())
            .filter(|(_, p)| (one || !p.positional) && written(&p.name))
            .map(|(i, p)| (i as u32, p.name.clone()))
            .collect()
    }

    /// Whether it has the same parameter names and kinds as `other`.
    pub fn same_kinds(&self, other: &Sig) -> bool {
        self.params.len() == other.params.len()
            && self
                .params
                .iter()
                .zip(&other.params)
                .all(|(a, b)| a.positional == b.positional && a.name == b.name)
    }
}

/// The digests of the parameter names a call may write inside types (ADDR-nested-param-names):
/// for a signature or a type, a BLAKE3-256 hash of [`Sig::callable_names`] of every function it
/// holds at any depth, in the arrows' parameters and results and through tuples and atom
/// payloads, each at its place. An importer may call a function a definition returns, as
/// `p(k: 1.0)(z: 2.0)`, or pass one whose parameters must be named as a parameter's function
/// type says, as `apply(f: h)` for `apply(f: (x: f64) -> f64)` (a function fits another only
/// with the same names, [`Sig::param_list`]), so these names are part of the definition's
/// interface and its content address keeps them (DESIGN.md sec:units, "Imports pin hashes").
///
/// Hashed: for a signature, its callable names (count, then each index and name), its arrows'
/// count, and for each arrow its parameters' count, each parameter's type and the result's;
/// for a row, its components' count and each component's type; for a payload shape, its items
/// and its fields, each field with its name; for a type, its functions, rows and payloads, each
/// list with its count and each function, row or shape by its own digest, each payload with its
/// atom's name. Type variables, carriers and atoms are not hashed: they are no name a call
/// writes, and a change to them changes the definition's value, whose address the export's
/// holds already. A signature's needs are not hashed either: they are what its body asks of
/// its type variables, not names a call writes.
///
/// Each signature, row and shape is hashed once, from the digests of those it holds, which are
/// kept in a map for as long as the borrow `'a` of the types lasts. One `NameDigests` serves
/// every definition of a unit, so a type shared by many places and many definitions costs its
/// distinct nodes once: O(nodes + edges + bytes of names) for the unit (P207).
// Complexity tradeoff: naive version, a walk of each type as a tree, hashing a shared
// signature, row or shape once for each path to it: O(2^n) for n definitions each holding the
// one before twice (`doubled_types` in the l02_08 benchmarks), and O(depth²) for function
// types nested depth deep (`nested_fn_types`); both measured with that walk (the first ran
// past the benchmark's 20 s limit, the second gave T(8n)/T(n) = 31.6). Used: a post-order walk on an
// explicit stack (a function type nests as deep as the program) with each node's digest kept
// by address, as `Sig::first_seen` and `Sig::held_without` keep the nodes they entered: every
// node is borrowed for `'a`, so no key names a freed node, and the map is only read by key,
// never iterated, so its order changes nothing. Given up: a map entry of 40 bytes per distinct
// node, and the hashing of the types of signatures and rows that hold no function (each such
// node hashes a few counts).
pub struct NameDigests<'a> {
    done: HashMap<*const (), [u8; 32]>,
    held: std::marker::PhantomData<&'a Ty>,
}

/// A node [`NameDigests`] hashes once.
#[derive(Clone, Copy)]
enum NameNode<'a> {
    Sig(&'a Sig),
    Row(&'a Row),
    Shape(&'a Shape),
}

impl<'a> NameNode<'a> {
    /// Its address, the key of its digest.
    fn key(self) -> *const () {
        match self {
            NameNode::Sig(s) => (s as *const Sig).cast(),
            NameNode::Row(r) => r.addr(),
            NameNode::Shape(s) => s.as_ptr().cast(),
        }
    }

    /// The types it holds directly, in the order they are hashed.
    fn tys(self) -> Vec<&'a Ty> {
        match self {
            NameNode::Sig(s) => (s.arrows.iter())
                .flat_map(|a| a.params.iter().chain([&a.result]))
                .collect(),
            NameNode::Row(r) => r.iter().collect(),
            NameNode::Shape(s) => s.items.iter().chain(s.fields.values()).collect(),
        }
    }
}

/// The signatures, rows and shapes `t` holds at its outer level.
fn name_nodes(t: &Ty) -> impl Iterator<Item = NameNode<'_>> {
    (t.fns.iter().map(|s| NameNode::Sig(s)))
        .chain(t.tuples.iter().map(NameNode::Row))
        .chain(t.payloads.values().flatten().flatten().map(NameNode::Shape))
}

impl<'a> Default for NameDigests<'a> {
    fn default() -> Self {
        NameDigests {
            done: HashMap::new(),
            held: std::marker::PhantomData,
        }
    }
}

impl<'a> NameDigests<'a> {
    /// The digest of the names a call may write in `s`: its own and those inside the types of
    /// its arrows.
    pub fn sig(&mut self, s: &'a Sig) -> [u8; 32] {
        self.enter([NameNode::Sig(s)]);
        self.done[&NameNode::Sig(s).key()]
    }

    /// The digest of the names a call may write inside the type `t`.
    pub fn ty(&mut self, t: &'a Ty) -> [u8; 32] {
        self.enter(name_nodes(t));
        let mut h = blake3::Hasher::new();
        h.update(b"zed-names-ty\0");
        self.hash_ty(&mut h, t);
        *h.finalize().as_bytes()
    }

    /// Hashes each of `roots` not yet hashed, and each node it holds, those it holds first.
    // Each node is entered with a mark that it is still to be hashed; when that entry is met
    // again its children are done, since a type holds no cycle. Proof: the walk follows only a
    // signature's `arrows`, a row's `cs` and a shape's `items` and `fields`, plain `Vec`s and
    // `BTreeMap`s with no cell or lock, so they are written only through a unique owner (an
    // `Arc` is written only by `Arc::make_mut`, which copies a shared node first), and a node
    // written while it is uniquely owned cannot be given an `Arc` of itself, which would make
    // it shared: a node holds only nodes made before it. A node pushed again before it is hashed is
    // pushed only along another edge to it, so the pushes are bounded by the edges.
    fn enter(&mut self, roots: impl IntoIterator<Item = NameNode<'a>>) {
        let mut stack: Vec<(NameNode<'a>, bool)> = roots.into_iter().map(|n| (n, false)).collect();
        while let Some((n, ready)) = stack.pop() {
            if self.done.contains_key(&n.key()) {
                continue;
            }
            if ready {
                let d = self.hash_node(n);
                self.done.insert(n.key(), d);
                continue;
            }
            stack.push((n, true));
            for t in n.tys() {
                let new = name_nodes(t).filter(|c| !self.done.contains_key(&c.key()));
                stack.extend(new.map(|c| (c, false)));
            }
        }
    }

    /// The digest of `n`, whose nodes are all hashed.
    fn hash_node(&self, n: NameNode<'_>) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        let count = |h: &mut blake3::Hasher, k: usize| {
            h.update(&(k as u64).to_le_bytes());
        };
        match n {
            NameNode::Sig(s) => {
                h.update(b"zed-names-fn\0");
                let names = s.callable_names();
                count(&mut h, names.len());
                for (i, name) in &names {
                    h.update(&i.to_le_bytes());
                    count(&mut h, name.len());
                    h.update(name.as_bytes());
                }
                count(&mut h, s.arrows.len());
                for a in &s.arrows {
                    count(&mut h, a.params.len());
                    a.params.iter().for_each(|t| self.hash_ty(&mut h, t));
                    self.hash_ty(&mut h, &a.result);
                }
            }
            NameNode::Row(r) => {
                h.update(b"zed-names-row\0");
                let cs: Vec<&Ty> = r.iter().collect();
                count(&mut h, cs.len());
                cs.into_iter().for_each(|t| self.hash_ty(&mut h, t));
            }
            NameNode::Shape(s) => {
                h.update(b"zed-names-shape\0");
                count(&mut h, s.items.len());
                s.items.iter().for_each(|t| self.hash_ty(&mut h, t));
                count(&mut h, s.fields.len());
                for (name, t) in &s.fields {
                    count(&mut h, name.len());
                    h.update(name.as_bytes());
                    self.hash_ty(&mut h, t);
                }
            }
        }
        *h.finalize().as_bytes()
    }

    /// Adds `t` to `h`: its functions, rows and payloads, each node by its digest.
    fn hash_ty(&self, h: &mut blake3::Hasher, t: &Ty) {
        let digest = |n: NameNode<'_>| self.done[&n.key()];
        h.update(&(t.fns.len() as u64).to_le_bytes());
        for s in &t.fns {
            h.update(&digest(NameNode::Sig(s)));
        }
        h.update(&(t.tuples.len() as u64).to_le_bytes());
        for r in &t.tuples {
            h.update(&digest(NameNode::Row(r)));
        }
        h.update(&(t.payloads.len() as u64).to_le_bytes());
        for (atom, shapes) in &t.payloads {
            h.update(&(atom.len() as u64).to_le_bytes());
            h.update(atom.as_bytes());
            let Some(shapes) = shapes else {
                h.update(&[0]);
                continue;
            };
            h.update(&[1]);
            h.update(&(shapes.len() as u64).to_le_bytes());
            for s in shapes {
                h.update(&digest(NameNode::Shape(s)));
            }
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        self.write(&mut text, &mut Scope::default());
        #[cfg(feature = "printed-types")]
        printed::record(self, &text);
        f.write_str(&text)
    }
}

/// The type variables the signatures around a place being printed bind: each by its name in
/// the type, with the way it is printed. A variable bounded by carriers is printed by its name,
/// with its bounds clause. Any other variable a signature binds is fixed to one type at each
/// call, and is printed by a name of its own where it stands in two places or more of the
/// printed type and `_` where it stands in one ([`write_parts`]; DESIGN.md sec:diagnostics,
/// "Types in a message"). A variable no signature around it binds is printed `_`.
// Complexity tradeoff (COMPLEXITY.md F68): naive, each fresh name tried from `T` again at
// each rename, O(renames²) tries; used, a map from each variable to its stack of printed
// names, a set of the names in use and one counter that only grows, O(size of the type) plus O(renames) fresh names.
// Memory: one entry per open variable; a fresh name skipped once is never reused in the type.
#[derive(Default)]
struct Scope {
    /// Each variable's printed names, innermost signature last.
    names: HashMap<Arc<str>, Vec<VarSlot>>,
    /// The printed names in scope, so a signature inside another that bounds a name already
    /// printed takes a fresh one: a bounds clause inside another's may not bound its name again.
    printed: HashSet<Arc<str>>,
    /// The index in `T`, `U`, … of the next fresh name to try. It only grows, so each name is
    /// tried once however many signatures take a fresh one.
    fresh: usize,
    /// Every name a bounds clause of the text writes, which a name given to an unbounded
    /// variable skips.
    bound: HashSet<Arc<str>>,
    /// The unbounded variables opened so far, each by its number in order of opening: the
    /// parent of each in a union-find forest whose trees are the variables printed as one.
    /// Each tree's root is its smallest number, so the roots do not depend on the order of
    /// the joins.
    same: Vec<usize>,
    /// The variables of a comparison bounded by carriers in a signature outside the texts a
    /// message prints ([`Scope::of_comparison`]), by their printed names: each with the name
    /// the program wrote, its bound, and whether a text has written it, so that the message can
    /// say where each one it writes is bound ([`Scope::given_text`]).
    given: BTreeMap<Arc<str>, (Arc<str>, u8, Cell<bool>)>,
    /// The bounds the member signatures of the unions being written opened and left to the
    /// end of their union ([`PrintAt::Member`]), innermost union last; [`Print::Closes`]
    /// writes and closes each union's.
    hoisted: Vec<Vec<(Arc<str>, u8)>>,
    /// For each union being written that leaves a bounds clause to its end, innermost last,
    /// the names the clauses inside it have written so far ([`Print::Opens`]): its own clause
    /// bounds all of its members, so it may take none of them.
    unions: Vec<HashSet<Arc<str>>>,
}

/// How a variable a signature binds is printed ([`Scope`]).
#[derive(Clone)]
enum VarSlot {
    /// By this name, with the bounds clause of its signature.
    Name(Arc<str>),
    /// By a name only where it stands in two places or more: the variable's number in
    /// [`Scope::same`].
    Free(usize),
}

impl Scope {
    /// How the variable `v` is printed here, or `None` if no signature around binds it.
    fn slot(&self, v: &Arc<str>) -> Option<&VarSlot> {
        self.names.get(v)?.last()
    }

    /// A new unbounded variable, alone in its tree.
    fn free(&mut self) -> VarSlot {
        let k = self.same.len();
        self.same.push(k);
        VarSlot::Free(k)
    }

    /// The root of the tree of the unbounded variable `k`, halving the path to it.
    fn root(&mut self, mut k: usize) -> usize {
        while self.same[k] != k {
            self.same[k] = self.same[self.same[k]];
            k = self.same[k];
        }
        k
    }

    /// Opens the variables `sig` binds, giving each bounded one a printed name, and returns
    /// them with their masks, in the order of `sig.bounds`. A name not printed around the
    /// signature is kept; otherwise the next of `T`, `U`, … not yet tried that is neither
    /// printed around it nor a name of its own nor one the program binds ([`fresh_name`]).
    /// What a failed test leaves of an unbounded variable (`r else 0`, [`Narrow`]) is printed
    /// as that variable: it holds no value the variable does not, so `g(r) = r else 0` is
    /// `(r: T) -> 0 | T`.
    fn open(&mut self, sig: &Sig, hoisted: bool) -> Vec<(Arc<str>, u8)> {
        let mut out = Vec::new();
        for (v, &m) in &sig.bounds {
            if m & OTHER != 0 {
                let slot = self.free();
                self.names.entry(v.clone()).or_default().push(slot);
                continue;
            }
            // A clause left to the end of its union ([`PrintAt::Member`]) also bounds the
            // members before its signature, so it skips each name a clause inside them wrote.
            let printed = &self.printed;
            let union = self.unions.last().filter(|_| hoisted);
            let taken =
                |name: &str| printed.contains(name) || union.is_some_and(|u| u.contains(name));
            let name = if taken(v) {
                fresh_name(Names::Variables, &mut self.fresh, |name| {
                    taken(name) || sig.bounds.contains_key(name)
                })
            } else {
                v.clone()
            };
            if let Some(u) = self.unions.last_mut() {
                u.insert(name.clone());
            }
            self.printed.insert(name.clone());
            self.bound.insert(name.clone());
            self.names
                .entry(v.clone())
                .or_default()
                .push(VarSlot::Name(name.clone()));
            out.push((name, m));
        }
        for v in sig.own.iter().filter(|v| !sig.bounds.contains_key(*v)) {
            let slot = self.free();
            self.names.entry(v.clone()).or_default().push(slot);
        }
        for need in &sig.needs {
            let (NeedKind::Narrow(_), Some(left)) = (&need.kind, &need.result) else {
                continue;
            };
            let free = |t: &Ty| match t.as_var().and_then(|v| self.slot(v)) {
                Some(&VarSlot::Free(k)) => Some(k),
                _ => None,
            };
            if let (Some(a), Some(b)) = (free(&need.on), free(left)) {
                let (a, b) = (self.root(a), self.root(b));
                self.same[a.max(b)] = a.min(b);
            }
        }
        out
    }

    /// Closes the variables `sig` binds, which [`Scope::open`] opened.
    fn close(&mut self, sig: &Sig) {
        let own = sig.own.iter().filter(|v| !sig.bounds.contains_key(*v));
        for v in sig.bounds.keys().chain(own) {
            let names = self.names.get_mut(v).expect("opened");
            if let Some(VarSlot::Name(name)) = names.pop() {
                self.printed.remove(&name);
            }
        }
    }

    /// The scope a message about the comparison `cx` prints its types in, with the own
    /// variables of `q`, the expected signature, when one is given. Each variable bounded by
    /// carriers is printed by name ([`Scope::give`]); a rigid one ([`Cx::fresh`]) made from a
    /// variable of `q` so bounded is that variable, and shares its name. Each other own
    /// variable of the open comparisons is unbounded, printed by name where it stands twice or
    /// more in one text and `_` where once (DESIGN.md sec:diagnostics, "Types in a message").
    /// The functions the comparison put in its types as variables ([`Cx::fns`]) have no slot:
    /// [`Scope::text`] prints each as the function it stands for.
    fn of_comparison(cx: &Cx, q: Option<&Sig>) -> Scope {
        let carriers = |m: u8| m & OTHER == 0;
        let in_q = |v: &str| q.is_some_and(|q| q.bounds.get(v).is_some_and(|&m| carriers(m)));
        // Each variable, the name the program wrote, its bound, and whether it is one of `q`'s
        // named already; outermost first.
        let qs = q.into_iter().flat_map(|q| {
            let own = q.own.iter().filter(|v| !q.bounds.contains_key(*v));
            (q.bounds
                .iter()
                .map(|(v, &m)| (v.clone(), v.clone(), Some(m), false)))
            .chain(own.map(|v| (v.clone(), v.clone(), None, false)))
        });
        let rigid = cx.made.iter().filter_map(|w| {
            let m = *cx.rigid.get(w)?;
            let (v, _) = w.rsplit_once('\'')?;
            Some((w.clone(), Arc::from(v), Some(m), in_q(v)))
        });
        // An own variable given a new name ([`Cx::own_name`]) prints as the name it was made
        // from.
        let own = cx.own.iter().map(|(v, m)| {
            let written = v.rsplit_once('\'').map_or(v.as_ref(), |(w, _)| w);
            (v.clone(), Arc::from(written), *m, false)
        });
        let mut scope = Scope::default();
        for (v, written, bound, shared) in qs.chain(rigid).chain(own) {
            let slot = match bound {
                Some(_) if shared => VarSlot::Name(written),
                Some(m) if carriers(m) => VarSlot::Name(scope.give(written, m)),
                _ => scope.free(),
            };
            scope.names.entry(v).or_default().push(slot);
        }
        scope
    }

    /// The printed name of a variable the program wrote `written`, bounded by the carriers of
    /// `m` in a signature outside the texts ([`Scope::given`]): `written`, or the next fresh
    /// name ([`fresh_name`]) when another such variable took it, so that two variables of one
    /// name, one in each signature compared, print apart.
    fn give(&mut self, written: Arc<str>, m: u8) -> Arc<str> {
        let name = if self.printed.contains(&written) {
            fresh_name(Names::Variables, &mut self.fresh, |name| {
                self.printed.contains(name)
            })
        } else {
            written.clone()
        };
        self.printed.insert(name.clone());
        self.bound.insert(name.clone());
        self.given
            .insert(name.clone(), (written, m, Cell::new(false)));
        name
    }

    /// `t`'s text in this scope, each variable of `cx` that stands for a function ([`Cx::fns`])
    /// printed as that function ([`Cx::unread`]). A variable no slot names belongs to no
    /// signature the comparison opened, and is printed as an unbounded one. Linear in `t` and
    /// the functions put back, as [`Cx::unread`], [`Ty::vars_in`] and [`Ty::write`] are.
    fn text(&mut self, t: &Ty, cx: &Cx) -> String {
        let t = cx.unread(t);
        let mut vs = Vars::default();
        t.vars_in(&mut vs);
        for v in vs.order {
            if self.slot(&v).is_none() {
                let slot = self.free();
                self.names.entry(v).or_default().push(slot);
            }
        }
        let mut out = String::new();
        t.write(&mut out, self);
        out
    }

    /// Where each variable of [`Scope::given`] that a text has written is bound, for the end
    /// of a message's sentence: "; here `U` is the type variable of `for U in int`", or
    /// nothing when the texts write none.
    fn given_text(&self) -> String {
        let said: Vec<String> = (self.given.iter())
            .filter(|(_, (_, _, written))| written.get())
            .map(|(name, (v, m, _))| {
                let clause = format!("for {v} in {}", mask_text(*m));
                match name == v {
                    true => format!("`{name}` is the type variable of `{clause}`"),
                    false => format!("`{name}` is the type variable `{v}` of `{clause}`"),
                }
            })
            .collect();
        match said.is_empty() {
            true => String::new(),
            false => format!("; here {}", said.join(", and ")),
        }
    }
}

impl Ty {
    /// Writes its text, in type syntax, to `out`. Each part is written in place, not built as a
    /// string and copied into the whole: copying cost the depth of each part, so O(n^2) for a
    /// function type n deep. A variable `scope` does not name is printed `_`, once.
    fn write(&self, out: &mut String, scope: &mut Scope) {
        write_parts(Print::Ty(self, PrintAt::Any), out, scope, None);
    }

    /// Its text, in type syntax, as its Display writes it, or as one operand of a union with
    /// `union` (a function in it then parenthesized, as in `(int -> int) | String`, since
    /// `->` binds looser than `|`), each literal value that `spell` spells written as the
    /// program wrote it, as a message prints a literal (DESIGN.md sec:diagnostics), and any
    /// other in canonical form.
    pub fn text_spelled(&self, union: bool, spell: Spell<'_>) -> String {
        let at = if union { PrintAt::Union } else { PrintAt::Any };
        let mut out = String::new();
        write_parts(
            Print::Ty(self, at),
            &mut out,
            &mut Scope::default(),
            Some(spell),
        );
        #[cfg(feature = "printed-types")]
        if !union {
            printed::record(self, &out);
        }
        out
    }

    /// Pushes the parts of its text to `parts`, in order, its kernel sets as holes that
    /// [`write_parts`] fills; with `found`, without its atom `#notFound`, as
    /// the value type of a morphism type is written ([`Sig::morphism`]). It stands at `at`, which
    /// decides its parentheses; of two members or more, each stands as an operand of `|`.
    fn parts<'a>(&'a self, parts: &mut Vec<Print<'a>>, found: bool, at: PrintAt) {
        // An atom whose payloads are known prints each payload's type, `#ioError(op: String,
        // path: String, why: String)` (L29-print); the kernel set holds it with any payload.
        let shaped: Vec<(&Arc<str>, &Vec<Shape>)> = self
            .payloads
            .iter()
            .filter_map(|(n, ss)| Some((n, ss.as_ref()?)))
            .filter(|(n, _)| holds_payload(&self.set, n))
            .collect();
        // Complexity tradeoff (COMPLEXITY.md F57): naive, the whole set printed or narrowed
        // once per payload atom, O(p · n) for p payload atoms in a set of n atoms (37.3 times for
        // 8 times the size, per the row); used, the payload atoms taken out in one difference
        // with their union, O(p log n), and each payload printed once.
        let rest = (!shaped.is_empty()).then(|| {
            let listed = shaped
                .iter()
                .map(|(n, _)| KType::atom_with(n, &KType::top()));
            &self.set - &KType::union_all(listed)
        });
        let set = rest.as_ref().unwrap_or(&self.set);
        let kept = found.then(|| set - &KType::atom("notFound"));
        let set = kept.as_ref().unwrap_or(set);
        // The members print in the order of a union (`order::cmp`, DESIGN.md
        // sec:diagnostics): the kernel set's numbers, booleans and string literals; `String`
        // among the type variables by name; the set's tuples, then the tuple shapes; the set's
        // functions, then the functions; the atoms by name, each atom with a known payload
        // after the set's atoms up to its name; `_` last. A set alone is ordered by the kernel.
        let others = !shaped.is_empty()
            || !self.tuples.is_empty()
            || !self.fns.is_empty()
            || !self.vars.is_empty()
            || self.dynamic;
        let cuts: Vec<&str> = shaped.iter().map(|(n, _)| &***n).collect();
        let groups = match others && !set.is_empty() {
            true => set.print_groups(&cuts),
            false => None,
        };
        // A set that prints as one text whatever stands beside it, a recursive type's name
        // or `_ \ c`, stands first, as a set alone does.
        let whole = match (&groups, set.is_empty()) {
            (None, false) => Some(set.clone()),
            _ => None,
        };
        let holes = groups.as_ref().map_or(0, |g| {
            [&g.low, &g.string, &g.tuples, &g.morphisms]
                .into_iter()
                .chain(&g.atoms)
                .filter(|t| !t.is_empty())
                .count()
        });
        let members = holes
            + usize::from(whole.is_some())
            + shaped.iter().map(|(_, ss)| ss.len()).sum::<usize>()
            + self.tuples.len()
            + self.fns.len()
            + usize::from(!self.vars.is_empty() || self.dynamic);
        // A union standing where a whole `Type` stands writes the bounds clause of each member
        // intersection of arrows once, after its last member: `TypeBounds` ends the `Type`
        // (`Type = Arrow TypeFacet* TypeWhere? TypeBounds?`), so `rat | (T -> T) & (f64 -> _)
        // for T in int | f64` reads as `rat | ((T -> T) & (f64 -> _) for T in int | f64)`, one
        // pair fewer (P191). So does a union as an arrow's key or a bound: it is parenthesized
        // there, and inside the pair a whole `Type` stands (`GroupType = '(' nest(Type) ')'`),
        // so `(rat | (T -> T) & (f64 -> _) for T in int | f64) -> int` writes the clause before
        // the `)` ([`Print::Closes`]) (FAIL-parens-wrong-is-empty-seed). Elsewhere the clause
        // would bound the arrow around the union.
        let hoist = members >= 2 && matches!(at, PrintAt::Any | PrintAt::Key | PrintAt::Bound);
        let hoisting = hoist && self.fns.iter().any(|s| s.hoists());
        let inside = hoisting && at != PrintAt::Any;
        if hoisting {
            parts.push(Print::Opens);
        }
        let at = match members {
            0 | 1 => at,
            _ if hoist => PrintAt::Member,
            _ => PrintAt::Union,
        };
        let place = match at {
            PrintAt::Any | PrintAt::Result => TextPlace::Any,
            PrintAt::Key => TextPlace::Key,
            PrintAt::Bound => TextPlace::Bound,
            PrintAt::Union | PrintAt::Member => TextPlace::Union,
        };
        // Each kernel set is written once the rest is, with the other kernel sets of the text
        // ([`write_parts`]); here its place is kept. A set split into two holes or more is
        // written out in each, never as a whole by a name of its own, since its parts would not
        // be in one hole (`KType::surfaces_apart`).
        let apart = holes >= 2;
        let hole = |parts: &mut Vec<Print<'a>>, t: &KType| {
            if !t.is_empty() {
                parts.push(Print::Sep);
                parts.push(Print::Set(t.clone(), place, apart));
            }
        };
        if let Some(t) = &whole {
            hole(parts, t);
        }
        let string = groups.as_ref().and_then(|g| {
            hole(parts, &g.low);
            (!g.string.is_empty()).then(|| (g.string.clone(), place, apart))
        });
        parts.push(Print::Vars(self, string));
        if let Some(g) = &groups {
            hole(parts, &g.tuples);
        }
        for cs in &self.tuples {
            parts.push(Print::Sep);
            // A row whose kernel type is the whole of it is written as a kernel set, with the
            // others of the text ([`write_parts`]), so a part it holds in two places or more is
            // written once, as `type Tk = …;`: `t_i = (t_{i-1}, t_{i-1})` over n levels writes
            // n definitions, not 2^n components (MSG-derive-type-size).
            if let (Some(k), false) = (&cs.0.kernel, cs.0.listed) {
                parts.push(Print::Set(k.clone(), place, false));
                continue;
            }
            parts.push(Print::Row(cs, at));
        }
        if let Some(g) = &groups {
            hole(parts, &g.morphisms);
        }
        for s in &self.fns {
            parts.push(Print::Sep);
            parts.push(Print::Sig(s, at));
        }
        let mut atoms = groups.as_ref().map(|g| g.atoms.iter());
        for (n, ss) in shaped {
            if let Some(t) = atoms.as_mut().and_then(Iterator::next) {
                hole(parts, t);
            }
            for s in ss {
                parts.push(Print::Sep);
                s.parts(n, parts);
            }
        }
        for t in atoms.into_iter().flatten() {
            hole(parts, t);
        }
        let others = members > usize::from(!self.vars.is_empty() || self.dynamic);
        parts.push(Print::End(self, others, inside));
        if hoisting {
            parts.push(Print::Closes(self, inside));
        }
    }

    /// Writes its type variables to `out`, those printed by name in code-point order, with
    /// `string`, the kernel set `String` or what is left of it, among them by its name (the
    /// order of a union, `order::cmp`), and keeps in `walk` what [`Ty::write_end`] needs. On
    /// the first pass of `walk` each unbounded variable is recorded and left to be printed `_`;
    /// on the second, one that stands in two places or more is written as a mark that
    /// [`defs::name_vars`] names, in one union with the names after `String`: a mark is named by
    /// [`fresh_name`], from `T` on, which comes after `String`.
    fn write_vars(
        &self,
        string: Option<(KType, TextPlace, bool)>,
        out: &mut String,
        scope: &Scope,
        walk: &mut Walk,
        kernel: &mut Kernel,
    ) {
        let mut names: Vec<&Arc<str>> = Vec::new();
        let mut marks = Vec::new();
        let mut blank = self.dynamic;
        let at = walk.occ.len();
        for v in &self.vars {
            match (scope.slot(v), &walk.plan) {
                (Some(VarSlot::Name(name)), _) => {
                    if let Some((_, _, written)) = scope.given.get(name) {
                        written.set(true);
                    }
                    names.push(name);
                }
                (Some(&VarSlot::Free(k)), None) => walk.occ.push(k),
                (Some(&VarSlot::Free(k)), Some(plan)) => match plan.count[plan.root[k]] >= 2 {
                    true => marks.push(plan.root[k]),
                    false => blank = true,
                },
                (None, _) => blank = true,
            }
        }
        let end = walk
            .ends
            .last_mut()
            .expect("a type's variables are in the type");
        end.named = !names.is_empty();
        end.blank = blank;
        end.occ = at..walk.occ.len();
        names.sort_unstable();
        // The names before `String`, then `String`, then the others with the marks.
        let split = match string {
            Some(_) => names.partition_point(|n| {
                order::cmp(&order::Member::Named(n), &order::Member::Named("String")).is_lt()
            }),
            None => 0,
        };
        let (before, after) = names.split_at(split);
        for name in before {
            walk.sep(out);
            out.push_str(name);
        }
        if let Some(s) = string {
            walk.sep(out);
            let (set, place, apart) = s;
            kernel.at.push(out.len());
            kernel.sets.push((set, place));
            kernel.apart.push(apart);
        }
        match marks.is_empty() {
            true => {
                for name in after {
                    walk.sep(out);
                    out.push_str(name);
                }
            }
            false => {
                walk.sep(out);
                marks.sort_unstable();
                marks.dedup();
                let marks_len = marks.len();
                out.push(defs::UNION);
                for name in after {
                    out.push_str(name);
                    out.push(defs::NEXT);
                }
                for r in marks {
                    out.push(defs::VAR);
                    out.push_str(&r.to_string());
                    out.push(defs::NEXT);
                }
                out.pop();
                out.push(defs::UNION_END);
                // The group is one member written so far ([`Walk::sep`]), but [`defs::name_vars`]
                // writes each of its distinct names as a member.
                let end = walk
                    .ends
                    .last_mut()
                    .expect("a type's variables are in the type");
                end.members += after.len() + marks_len - 1;
            }
        }
    }

    /// Writes the end of its text to `out`, which closes it as the type `walk` last entered:
    /// `_` for the variables printed so and the unknown, or `Never` if nothing of it is
    /// written and nothing is to be. With `others` its union holds members that are not type
    /// variables. A union of two members or more written as an arrow's key or a bound is closed
    /// with `)`, and where its `(` goes is given back, to be put in with the kernel sets
    /// ([`write_parts`]): the members are counted only as they are written, since a type
    /// variable may be written by several names or as `_` with others (author P222). With
    /// `inside` the union is such a key or bound that leaves a bounds clause to its end, and
    /// [`Print::Closes`] writes the `)`.
    fn write_end(
        &self,
        others: bool,
        inside: bool,
        out: &mut String,
        scope: &Scope,
        walk: &mut Walk,
    ) -> Option<usize> {
        let node = walk
            .open
            .pop()
            .expect("a type's end closes the type walk entered");
        let end = walk
            .ends
            .pop()
            .expect("a type's end closes the type walk entered");
        let mut blank = end.blank;
        if walk.plan.is_none() {
            walk.nodes[node] = PrintNode {
                end: walk.nodes.len(),
                inst_end: scope.same.len(),
                others: others || end.named,
                blank,
                occ: end.occ.clone(),
            };
            blank |= !end.occ.is_empty();
        }
        let members = match (blank, end.members) {
            (true, 0) => {
                out.push('_');
                1
            }
            (true, n) => {
                out.push_str(" | _");
                n + 1
            }
            (false, 0) => {
                out.push_str("Never");
                1
            }
            (false, n) => n,
        };
        // A union that leaves a bounds clause to its end as a key or a bound (`inside`) is
        // parenthesized whatever the members written, since the clause and a lone intersection
        // of arrows each need the pair there, and [`Print::Closes`] writes its `)` after the
        // clause.
        if inside {
            return Some(end.wrap.expect("a key or a bound is entered at its place"));
        }
        let open = end.wrap.filter(|_| members >= 2);
        if open.is_some() {
            out.push(')');
        }
        open
    }
}

/// A type in the text being written, as the first pass of a [`Walk`] finds it.
#[derive(Clone, Default)]
struct PrintNode {
    /// The number of the first type after it and the types inside it.
    end: usize,
    /// The number of unbounded variables opened once it is written ([`Scope::same`]).
    inst_end: usize,
    /// Whether its union holds a member that is not `_`: a set, a tuple, a function or a
    /// variable bounded by carriers.
    others: bool,
    /// Whether its union holds `_` whatever the names: the unknown, or a variable no
    /// signature around it binds.
    blank: bool,
    /// Its unbounded variables, in [`Walk::occ`].
    occ: std::ops::Range<usize>,
}

/// The walks of one text by [`write_parts`]. The first writes it as if every unbounded
/// variable stood once, numbering the types it holds in the order it enters them and
/// recording where each unbounded variable stands. If one stands in two places or more, or a
/// union holds `_` beside other members, which then prints `_` alone, a [`Plan`] is made and
/// the text is written again by it; else the first text stands.
#[derive(Default)]
struct Walk {
    plan: Option<Plan>,
    nodes: Vec<PrintNode>,
    /// The types entered and not yet closed, innermost last.
    open: Vec<usize>,
    /// The unbounded variables of each type, by its [`PrintNode::occ`]: numbers of [`Scope::same`]
    /// on the first pass, the roots of their trees once the plan is made.
    occ: Vec<usize>,
    /// The number of the next type the second pass enters.
    next: usize,
    /// For each type of [`Walk::open`], what its end is written by ([`Ty::write_end`]).
    ends: Vec<OpenEnd>,
}

/// What the end of a type entered and not yet closed is written by ([`Ty::write_end`]).
#[derive(Default)]
struct OpenEnd {
    /// The number of members of its union written so far, so that the next is written after
    /// ` | `, and a union of two or more as a key or a bound is parenthesized.
    members: usize,
    /// Where its text begins in the output, if it stands as an arrow's key or a bound of
    /// `L .. U -> V`, where a union is parenthesized ([`PrintAt::Key`]).
    wrap: Option<usize>,
    /// Whether a type variable of it is printed by name.
    named: bool,
    /// Whether its union holds `_` whatever the names ([`PrintNode::blank`]).
    blank: bool,
    /// Its unbounded variables, in [`Walk::occ`].
    occ: std::ops::Range<usize>,
}

/// What the second walk of a text writes ([`Walk`]).
struct Plan {
    /// For each type, whether its union is written `_` alone, with nothing inside it.
    absorbed: Vec<bool>,
    /// For each unbounded variable, the root of its tree.
    root: Vec<usize>,
    /// For each root, the number of types whose union it stands in, outside the unions
    /// written `_`.
    count: Vec<usize>,
}

impl Walk {
    /// Writes ` | ` to `out` before a member of the type last entered, unless it is the first.
    fn sep(&mut self, out: &mut String) {
        let end = self.ends.last_mut().expect("a member is in a type");
        if end.members > 0 {
            out.push_str(" | ");
        }
        end.members += 1;
    }

    /// Enters a type at `out`: whether its parts are to be written. On the second pass a type
    /// whose union is written `_` is written so here, and the walk steps over the types and
    /// variables inside it.
    fn enter(&mut self, out: &mut String, scope: &mut Scope) -> bool {
        let Some(plan) = &self.plan else {
            self.open.push(self.nodes.len());
            self.nodes.push(PrintNode::default());
            self.ends.push(OpenEnd::default());
            return true;
        };
        let k = self.next;
        if plan.absorbed[k] {
            let node = &self.nodes[k];
            out.push('_');
            self.next = node.end;
            let opened = scope.same.len();
            scope.same.extend(opened..node.inst_end);
            return false;
        }
        self.next += 1;
        self.open.push(k);
        self.ends.push(OpenEnd::default());
        true
    }

    /// The plan of the second pass, after the first, or `None` if the first text stands.
    ///
    /// A union that holds `_` beside other members is written `_` alone, since `_` holds every
    /// value (DESIGN.md sec:diagnostics, "Types in a message"), and so are the types inside
    /// it. A variable that stood in two places then may stand in one, which makes it `_`, so
    /// the unions are written `_` from a work list: each type is taken out once, by the
    /// outermost union that takes it, and each variable's count reaches one at most once,
    /// when the unions it is left in are looked at again.
    // Complexity tradeoff: naive, a variable's places counted again after each union written
    // `_`, and the variables named by scanning the text once per name, O(n²) in the size n of
    // the type; used, one count per variable, lowered as the types inside a union written `_`
    // are taken out, each type and each place once, a union-find over the variables that are
    // printed as one, the places of each union sorted once to count a variable once in it, and a
    // hash map from each variable to its name ([`defs::name_vars`]), so the two walks and the
    // naming are O(n log n) (COMPLEXITY.md F169). Memory: one node per type of
    // the text and one entry per place of a variable.
    fn plan(&mut self, scope: &mut Scope) -> Option<Plan> {
        let root: Vec<usize> = (0..scope.same.len()).map(|k| scope.root(k)).collect();
        // Each variable counts once in a union: `x` and what `x else 0` leaves of it are one.
        let mut occ = Vec::with_capacity(self.occ.len());
        for node in &mut self.nodes {
            let start = occ.len();
            occ.extend(self.occ[node.occ.clone()].iter().map(|&k| root[k]));
            occ[start..].sort_unstable();
            let mut kept = start;
            for i in start..occ.len() {
                if i == start || occ[i] != occ[kept - 1] {
                    occ[kept] = occ[i];
                    kept += 1;
                }
            }
            occ.truncate(kept);
            node.occ = start..kept;
        }
        self.occ = occ;
        let mut count = vec![0; root.len()];
        let mut places: Vec<Vec<usize>> = vec![Vec::new(); root.len()];
        for (k, node) in self.nodes.iter().enumerate() {
            for &r in &self.occ[node.occ.clone()] {
                count[r] += 1;
                places[r].push(k);
            }
        }
        let absorbs = |node: &PrintNode, count: &[usize]| {
            let vars = &self.occ[node.occ.clone()];
            (node.blank || vars.iter().any(|&r| count[r] == 1))
                && (node.others || vars.iter().any(|&r| count[r] >= 2))
        };
        let mut work: Vec<usize> = (0..self.nodes.len())
            .filter(|&k| absorbs(&self.nodes[k], &count))
            .collect();
        if work.is_empty() && count.iter().all(|&c| c < 2) {
            return None;
        }
        let mut gone = vec![false; self.nodes.len()];
        let mut absorbed = vec![false; self.nodes.len()];
        while let Some(k) = work.pop() {
            if gone[k] || !absorbs(&self.nodes[k], &count) {
                continue;
            }
            absorbed[k] = true;
            let mut m = k;
            while m < self.nodes[k].end {
                // A type already taken out is the outermost of a union written `_` before,
                // so the types inside it are taken out too.
                if gone[m] {
                    m = self.nodes[m].end;
                    continue;
                }
                gone[m] = true;
                for &r in &self.occ[self.nodes[m].occ.clone()] {
                    count[r] -= 1;
                    if count[r] == 1 {
                        work.extend(places[r].iter().filter(|&&j| !gone[j]));
                    }
                }
                m += 1;
            }
        }
        // A union written `_` inside another is marked too, but the second pass never enters
        // it: it steps over the outer one whole.
        Some(Plan {
            absorbed,
            root,
            count,
        })
    }
}

/// A part of the text of a type still to be written, on the stack [`write_parts`] keeps.
#[derive(Clone)]
enum Print<'a> {
    Text(&'a str),
    Ty(&'a Ty, PrintAt),
    Sig(&'a Sig, PrintAt),
    /// A tuple shape of a type ([`Row::parts`]).
    Row(&'a Row, PrintAt),
    /// The value type of a morphism type, which stands as a result: a type without its atom
    /// `#notFound`.
    Found(&'a Ty),
    /// A signature written as a family ([`Sig::family_parts`]), standing as a payload.
    Family(&'a Sig),
    /// The type variables of a type, with the kernel set `String` it holds, to be written
    /// among them ([`Ty::write_vars`]).
    Vars(&'a Ty, Option<(KType, TextPlace, bool)>),
    /// The end of a type's text ([`Ty::write_end`]), whether its union holds members other
    /// than type variables, and whether it is a key or a bound whose `)` comes after the
    /// bounds clause [`Print::Closes`] writes.
    End(&'a Ty, bool, bool),
    /// A kernel set, written once the rest of the text is ([`write_parts`]), at its place, and
    /// whether it is printed apart from the rest of its set ([`Kernel`]).
    Set(KType, TextPlace, bool),
    /// ` | ` before a member of the union being written, but its first.
    Sep,
    /// The bounds clause of a signature, which closes the variables it opened.
    Bounds(&'a Sig, Vec<(Arc<str>, u8)>),
    /// The start of a union that leaves a bounds clause to its end ([`Scope::unions`]).
    Opens,
    /// One bounds clause for the member signatures of a union that left theirs to its end
    /// ([`PrintAt::Member`]), which closes the variables they opened, and whether the union is a
    /// key or a bound, whose `)` the clause is then written before.
    Closes(&'a Ty, bool),
}

/// Where the text of a type stands, which decides the parentheses it needs to read back as one
/// type (DESIGN.md sec:grammar, `Type`, `Arrow`, `TypeUnion`). A text is parenthesized exactly
/// where the grammar needs it (author P191): where the rule that produces it is not reachable
/// from the rule the place expects through `~` alternatives alone, or where PEG ordered choice
/// would read it otherwise. tests/steps/l01_29_repairs_and_printing/parens.rs checks both, the
/// kernel's places against the grammar's rules and the printed text by deleting each pair in
/// turn.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PrintAt {
    /// Where a whole `Type` stands: the top, a component of a tuple, a parameter, a payload.
    /// A function with a bounds clause needs no pair before a comma, `(T -> T for T in int,
    /// int)`: `TypeBounds = 'for' (Name 'in' TypeUnion) % ','` gives back a comma that no
    /// `Name 'in'` follows.
    Any,
    /// An arrow's result, an `Arrow`: a function with a bounds clause is parenthesized, since
    /// its clause would bound the variables of the arrow around it.
    Result,
    /// The key of `K -> V` or `K ->? V`, a `TypeNot`: a function, a union, an intersection and a
    /// difference are parenthesized, `(int | #a) -> int`, since the bare `int | #a -> int` is
    /// rejected (author P222); and so is a tuple of other than one component, which would read
    /// as the parameters.
    Key,
    /// A bound of `L .. U -> V`, a `TypeNot`: a function, a union, an intersection and a
    /// difference are parenthesized, `#a .. (#a | #b) -> int`.
    Bound,
    /// An operand of `|`: a function is parenthesized.
    Union,
    /// An operand of `|` in a union that stands where a whole `Type` stands, or inside the pair
    /// of a key or a bound (`GroupType`): as at [`PrintAt::Union`], but an intersection of arrows
    /// leaves its bounds clause to the end of the union ([`Sig::hoists`], [`Print::Closes`]) and
    /// needs no pair.
    Member,
}

/// A signature written as a morphism type ([`Sig::morphism`]).
enum Morphism<'a> {
    /// `K ->? V`: the key type, the ranges written on the key, printed in its place or its
    /// components' where it has them (`int[5..=9] ->? int`, RANGE-keys;
    /// `((int[0..=1], int)) ->? int`, RANGE-key-component-print), and the result,
    /// `V | #notFound`.
    Partial {
        key: &'a Ty,
        range: Option<&'a ParamRange>,
        value: &'a Ty,
    },
    /// `L .. U -> V`: the guarantee, the permission and the value type.
    Bounded {
        lower: &'a Ty,
        upper: &'a Ty,
        value: &'a Ty,
    },
}

impl<'a> Morphism<'a> {
    /// Pushes the parts of its text to `parts`, in order. The key stands at [`PrintAt::Key`],
    /// so that `((int, int)) ->? V` is not read as two parameters.
    fn parts(&self, parts: &mut Vec<Print<'a>>) {
        match *self {
            Morphism::Partial { key, range, value } => {
                ParamRange::parts(range, key, PrintAt::Key, parts);
                parts.extend([Print::Text(" ->? "), Print::Found(value)]);
            }
            Morphism::Bounded {
                lower,
                upper,
                value,
            } => {
                parts.extend([
                    Print::Ty(lower, PrintAt::Bound),
                    Print::Text(" .. "),
                    Print::Ty(upper, PrintAt::Bound),
                ]);
                parts.extend([Print::Text(" -> "), Print::Ty(value, PrintAt::Result)]);
            }
        }
    }
}

/// Writes `start` to `out`. A type nests as deep as the program, so the writing keeps its own
/// stack: each part expands to the parts it is made of, which are put on the stack so that they
/// pop in order. The time is that of the text; a signature opens its variables when it is
/// reached and closes them after its arrows, so `scope` is as a recursive walk would have it.
///
/// An unbounded variable is written `_` where it stands once in the text and by a name where it
/// stands in two places or more, and a union that holds `_` is `_` ([`Walk`]): when the first
/// walk finds either, the text is written again with the names, and they are given last
/// ([`defs::name_vars`]).
///
/// The kernel sets in the text are written last, all together by name
/// ([`KType::surfaces_by_name`]), each where it stands. Printed alone, the text is then finished
/// by [`defs::lift`]: a part the sets name, and a tuple written more than once, once inside
/// another part, as [`defs::lift`] gives, gets a definition `type Tk = …;`, declared on a line
/// of its own before the whole text ([`defs::declare`]), so the text stays linear in the sets'
/// graph. In a message the message finishes it.
///
/// A function or a tuple the type holds in two places or more, which holds no type variable,
/// is written once, as a part of the table ([`Shared`]), and referred to where it stands.
fn write_parts<'a>(
    start: Print<'a>,
    out: &mut String,
    scope: &mut Scope,
    spell: Option<Spell<'_>>,
) {
    // Outside a message the text is finished here as a message's are ([`defs::lift`]), so a
    // type printed alone writes the parts it repeats as a message writes them
    // (MSG-derive-type-size).
    let alone = defs::local();
    let base = out.len();
    // The type is written as the reader reads its text, each union that holds `_` as `_`
    // alone and the members that leaves equal as one ([`Absorb`]).
    let (ty, sig) = match &start {
        Print::Ty(t, _) => (Absorb::ty(t), None),
        Print::Sig(s, _) => (None, Absorb::sig(s)),
        _ => (None, None),
    };
    let start = match (start, &ty, &sig) {
        (Print::Ty(_, at), Some(t), _) => Print::Ty(t, at),
        (Print::Sig(_, at), _, Some(s)) => Print::Sig(s, at),
        (start, ..) => start,
    };
    let shared = Shared::of(&start, spell);
    let (marked, sets) = write_text(start, out, scope, spell, &shared);
    // Inside a message the marks and references stay, and the message names them with its own
    // words, so that a variable is never named as another type of the message is.
    if alone.is_some() && (marked || sets || defs::holds_reference(&out[base..])) {
        let mut text = out.split_off(base);
        let lifted = defs::lift(&mut [&mut text], &|w| scope.bound.contains(w));
        for (name, body) in &lifted {
            defs::declare(out, name, body).expect("a String takes any text");
        }
        out.push_str(&text);
    }
}

/// The functions and tuples a text holds in two places or more and that hold no type variable,
/// each with the reference to its body in the table of definitions ([`defs::add_soft`]): a text
/// writes such a part by reference, and the message names it by the rule [`defs::lift`] gives
/// a part that holds others, or writes it in full.
///
/// A part with no type variable reads the same wherever it stands, so its body is written once,
/// alone, with a scope of its own. A function or a tuple with variables is still written in
/// full each time: its variables are named by the whole text ([`Walk`]).
///
/// A part none of whose places is below another row or function, other than those on top (the
/// ones the whole type holds directly, written in full), is not placed: [`defs::lift`] names a
/// soft part only when a use of it lies in another part's body, so such a part would be
/// written in full at each place anyway, and placing it would count the unions in its body
/// once where the text writes them at each place, so that a union the text writes twice would
/// not be named (`f(m: (int .. (int | String) -> bool, int)) = m` must read
/// `type Part1 = int | String;`, and so must `int .. (int | String) -> (int .. (int | String)
/// -> bool)`, whose two arrows share their result). Such a part stands only where the parts
/// on top hold it, so it is written as often as they write it, and the shared parts below it
/// are placed as any others.
// Complexity tradeoff (FAIL-nested-display-headline-type-growth): naive, the text written as a
// tree, each shared part in full at each place it stands, O(2^d) for a part held twice at each
// of d levels, as a set display nested d deep types each level `{f, (inner)}` with the inner
// set's function twice (2,165,352 message bytes at depth 16 against 325 at 2). Used: one walk
// over the type's graph, each row, function and payload shape entered once by address, counts
// the places of each, and each shared closed part's body is written once, innermost first,
// with the parts inside it by reference: O(n) in the size n of the graph, with a hash lookup
// per part. A part shared only through a family's key, which [`Sig::family_parts`] writes
// twice, is not counted twice; such a key holds no function or tuple ([`Sig::is_family`]).
// Tradeoff: one more walk and two hash maps per print, and the parts are placed as soft
// parts, not counted ones as the kernel places its unions: a short part such as `int -> int`
// is still written in full where it stands, as the tuples the kernel places are.
#[derive(Default)]
struct Shared {
    /// Each shared function, by address, with its reference.
    sigs: HashMap<*const Sig, String>,
    /// Each shared tuple, by its number, with its reference.
    rows: HashMap<NodeId, String>,
}

impl Shared {
    /// The shared closed parts of the text from `start`, their bodies placed in the table, and
    /// those an earlier print for the table placed ([`Settled`]).
    fn of(start: &Print<'_>, spell: Option<Spell<'_>>) -> Shared {
        #[derive(Clone, Copy)]
        enum Node<'a> {
            Ty(&'a Ty),
            Row(&'a Row),
            // With its `Arc` where the type holds it by one, so that it can be kept.
            Sig(&'a Sig, Option<&'a Arc<Sig>>),
            Shape(&'a Shape),
        }
        let mut shared = Shared::default();
        let first = match *start {
            Print::Ty(t, _) | Print::Found(t) => Node::Ty(t),
            Print::Sig(s, _) | Print::Family(s) => Node::Sig(s, None),
            Print::Row(r, _) => Node::Row(r),
            _ => return shared,
        };
        let spelled = spell.is_some();
        // By address: every node is borrowed from `start` for the whole walk, so no key names
        // a freed node. The places of each row and function, and the rows and functions in
        // the order left, each after those inside it. A node is on top when no row or
        // function holds it in this text; a part on top is entered even if settled, so a type
        // written on its own is written as before, not as one reference. A node is below a
        // part when a row or function not on top holds it, at any depth: a part on top is
        // written in full, never by reference, so what it holds is not below a part by it. A
        // part none of whose places is below another is not placed (`placed` below).
        let (mut rows, mut sigs, mut shapes) = (HashMap::new(), HashMap::new(), HashSet::new());
        let mut order: Vec<Node<'_>> = Vec::new();
        // Each node with whether it is left, on top and below a part.
        let mut stack: Vec<(Node<'_>, bool, bool, bool)> = vec![(first, false, true, false)];
        defs::with_kept_of(|settled: &mut Settled| {
            while let Some((node, left, top, below)) = stack.pop() {
                if left {
                    order.push(node);
                    continue;
                }
                // What a row or function holds is below a part unless that row or function
                // is on top.
                let inside = !top;
                // A row or a function is left, below the nodes it holds on the stack, after
                // them; the order among those is not read.
                match node {
                    Node::Ty(t) => {
                        let rows = t
                            .tuples
                            .iter()
                            .filter(|r| r.0.kernel.is_none() || r.0.listed);
                        stack.extend(rows.map(|r| (Node::Row(r), false, top, below)));
                        let fns =
                            (t.fns.iter()).map(|s| (Node::Sig(s, Some(s)), false, top, below));
                        stack.extend(fns);
                        let shapes = t.payload_shapes();
                        stack.extend(shapes.map(|s| (Node::Shape(s), false, false, below)));
                    }
                    Node::Row(r) => {
                        let found = settled.rows.get(&(r.node(), spelled)).filter(|_| !top);
                        if let Some(name) = found {
                            shared.rows.insert(r.node(), name.clone());
                            continue;
                        }
                        let (places, held) = rows.entry(r.node()).or_insert((0usize, false));
                        *places += 1;
                        *held |= below;
                        if *places == 1 {
                            stack.push((node, true, top, below));
                            stack.extend(r.iter().map(|t| (Node::Ty(t), false, false, inside)));
                        }
                    }
                    Node::Sig(s, _) => {
                        let key = (s as *const Sig, spelled);
                        if let Some((_, name)) = settled.sigs.get(&key).filter(|_| !top) {
                            shared.sigs.insert(key.0, name.clone());
                            continue;
                        }
                        let (places, held) = sigs.entry(key.0).or_insert((0usize, false));
                        *places += 1;
                        *held |= below;
                        if *places == 1 {
                            stack.push((node, true, top, below));
                            let tys = s
                                .arrows
                                .iter()
                                .flat_map(|a| a.params.iter().chain([&a.result]));
                            stack.extend(tys.map(|t| (Node::Ty(t), false, false, inside)));
                        }
                    }
                    Node::Shape(s) => {
                        if shapes.insert(Arc::as_ptr(&s.0)) {
                            let tys = s.items.iter().chain(s.fields.values());
                            stack.extend(tys.map(|t| (Node::Ty(t), false, false, below)));
                        }
                    }
                }
            }
        })
        .expect("a printed text has a table of definitions (defs::local)");
        // Each body is written with the parts inside it placed already, by reference.
        let place = |start: Print<'_>, shared: &Shared| {
            let mut body = String::new();
            write_text(start, &mut body, &mut Scope::default(), spell, shared);
            defs::soft_reference(defs::add_soft(body))
        };
        let mut placed: Vec<(Node<'_>, String)> = Vec::new();
        for node in order {
            match node {
                Node::Row(r) if matches!(rows[&r.node()], (2.., true)) && !r.holds_vars() => {
                    let name = place(Print::Row(r, PrintAt::Any), &shared);
                    shared.rows.insert(r.node(), name.clone());
                    placed.push((node, name));
                }
                Node::Sig(s, _)
                    if matches!(sigs[&(s as *const Sig)], (2.., true)) && s.closed() =>
                {
                    let name = place(Print::Sig(s, PrintAt::Any), &shared);
                    shared.sigs.insert(s as *const Sig, name.clone());
                    placed.push((node, name));
                }
                _ => {}
            }
        }
        defs::with_kept_of(|settled: &mut Settled| {
            for (node, name) in placed {
                match node {
                    Node::Row(r) => {
                        settled.rows.insert((r.node(), spelled), name);
                    }
                    // A function the type holds by no `Arc` is the text's start, on top, which
                    // is never read from here.
                    Node::Sig(s, Some(arc)) => {
                        let key = (s as *const Sig, spelled);
                        settled.sigs.insert(key, (Arc::clone(arc), name));
                    }
                    _ => {}
                }
            }
        });
        shared
    }
}

/// The parts [`Shared::of`] placed in the table of definitions, kept with the table
/// ([`defs::with_kept_of`]) for each later print, by the row's number or the function's address
/// and whether the program's spellings were used. A later text holding such a part inside a row
/// or a function writes its reference without entering it, so the steps of a message that each
/// print the next of a chain `t2 = (t1, t1); t3 = (t2, t2); …` print each part once.
///
/// A function is kept alive here with its reference, so its address names no other function
/// while the table lives. A part's body was written for the text that placed it: a part inside
/// it written once there is in full in the body, even where a later text holds that part
/// elsewhere too and would have placed it. The message is still linear in what it writes.
// Complexity tradeoff (FAIL-nested-display-headline-type-growth): naive, each print walks its
// type's whole graph, O(m) for m parts, so a message of n steps that each print the next of
// such a chain costs O(n²) (measured: 50 and 400 levels, 28.4 times the instructions). Used:
// each part placed once per table, O(1) expected per later use, so the message is O(m) in the
// parts it prints in all. Tradeoff: a part's text may depend on the first type that placed it,
// as the kernel's tuples do not (`Printer::remember` in zed-kernel's print.rs), since a
// function or tuple here is placed only when shared, not always as the kernel places tuples.
#[derive(Default)]
struct Settled {
    rows: HashMap<(NodeId, bool), String>,
    sigs: HashMap<(*const Sig, bool), (Arc<Sig>, String)>,
}

/// Writes the text from `start` to `out`, as [`write_parts`] describes, each part of `shared`
/// but `start` by reference; gives whether it marked its variables to be named and whether it
/// holds a kernel set.
fn write_text<'a>(
    start: Print<'a>,
    out: &mut String,
    scope: &mut Scope,
    spell: Option<Spell<'_>>,
    shared: &Shared,
) -> (bool, bool) {
    let base = out.len();
    let (fresh, opened) = (scope.fresh, scope.same.len());
    let mut walk = Walk::default();
    let mut kernel = walk_parts(start.clone(), out, scope, &mut walk, shared);
    let mut marked = false;
    if let Some(plan) = walk.plan(scope) {
        out.truncate(base);
        scope.fresh = fresh;
        scope.same.truncate(opened);
        marked = plan.count.iter().any(|&c| c >= 2);
        if marked {
            out.push(defs::VARS);
        }
        walk.plan = Some(plan);
        kernel = walk_parts(start, out, scope, &mut walk, shared);
        if marked {
            out.push(defs::VARS_END);
        }
    }
    if !kernel.sets.is_empty() || !kernel.opens.is_empty() {
        let roots = match (kernel.sets.is_empty(), spell) {
            (true, _) => Vec::new(),
            (false, spell) => {
                let texts = KType::surfaces_apart(&kernel.sets, &kernel.apart, spell);
                debug_assert!(texts.defs.is_empty(), "the table holds the definitions");
                texts.roots
            }
        };
        // The `(` of each union written as a key or a bound ([`Ty::write_end`]) goes in with
        // the kernel sets. At one place a `(` comes first: a set there is the union's first
        // member, written after the union began. A stable sort of k places, O(k log k).
        let mut put: Vec<(usize, &str)> = (kernel.opens.iter().map(|&at| (at, "(")))
            .chain(
                kernel
                    .at
                    .iter()
                    .copied()
                    .zip(roots.iter().map(String::as_str)),
            )
            .collect();
        put.sort_by_key(|&(at, _)| at);
        let rest = out.split_off(base);
        let mut from = 0;
        for (at, text) in put {
            let at = at - base;
            out.push_str(&rest[from..at]);
            out.push_str(text);
            from = at;
        }
        out.push_str(&rest[from..]);
    }
    (marked, !kernel.sets.is_empty())
}

/// One walk of [`write_parts`] from `start`, which writes the text to `out` with its kernel
/// sets left out, and gives them with their places. Each part of `shared` but `start` is
/// written by its reference.
fn walk_parts<'a>(
    start: Print<'a>,
    out: &mut String,
    scope: &mut Scope,
    walk: &mut Walk,
    shared: &Shared,
) -> Kernel {
    let mut kernel = Kernel::default();
    let mut stack = vec![start];
    let mut first = true;
    while let Some(part) = stack.pop() {
        let from = stack.len();
        let root = std::mem::take(&mut first);
        match part {
            Print::Row(r, at) => match shared.rows.get(&r.node()).filter(|_| !root) {
                Some(name) if r.wraps(at) => out.push_str(&defs::wrapped(name)),
                Some(name) => out.push_str(name),
                None => r.parts(at, &mut stack),
            },
            Print::Sig(s, at) => match shared.sigs.get(&(s as *const Sig)).filter(|_| !root) {
                // As [`Sig::parts`] writes it, with no variables to open: a closed part has
                // no bounds clause, and one left to the end of its union is empty.
                Some(name) => {
                    let several = s.hoists();
                    if at == PrintAt::Member && several {
                        scope.hoisted.push(Vec::new());
                    }
                    match Sig::wraps(at, several, false) {
                        true => out.push_str(&defs::wrapped(name)),
                        false => out.push_str(name),
                    }
                }
                None => s.parts(scope, &mut stack, at),
            },
            Print::Text(text) => out.push_str(text),
            Print::Ty(t, at) => {
                if walk.enter(out, scope) {
                    if matches!(at, PrintAt::Key | PrintAt::Bound) {
                        let end = walk.ends.last_mut().expect("entered");
                        end.wrap = Some(out.len());
                    }
                    t.parts(&mut stack, false, at);
                }
            }
            Print::Found(t) => {
                if walk.enter(out, scope) {
                    t.parts(&mut stack, true, PrintAt::Result);
                }
            }
            Print::Family(s) => s.family_parts(scope, &mut stack),
            Print::Vars(t, string) => t.write_vars(string, out, scope, walk, &mut kernel),
            Print::End(t, others, inside) => {
                if let Some(at) = t.write_end(others, inside, out, scope, walk) {
                    kernel.opens.push(at);
                }
            }
            Print::Set(set, place, apart) => {
                kernel.at.push(out.len());
                kernel.sets.push((set, place));
                kernel.apart.push(apart);
            }
            Print::Sep => walk.sep(out),
            Print::Bounds(s, bounds) => {
                for (i, (v, m)) in bounds.iter().enumerate() {
                    out.push_str(if i == 0 { " for " } else { ", " });
                    out.push_str(v);
                    out.push_str(" in ");
                    out.push_str(&mask_text(*m));
                }
                scope.close(s);
            }
            Print::Closes(t, inside) => {
                let sigs = t.fns.iter().filter(|s| s.hoists());
                let own = scope.hoisted.len() - sigs.clone().count();
                let mut first = true;
                for (v, m) in scope.hoisted.drain(own..).flatten() {
                    out.push_str(if first { " for " } else { ", " });
                    first = false;
                    out.push_str(&v);
                    out.push_str(" in ");
                    out.push_str(&mask_text(m));
                }
                // A key's or a bound's pair closes after the clause ([`Ty::write_end`]).
                if inside {
                    out.push(')');
                }
                for s in sigs.rev() {
                    scope.close(s);
                }
                // The names written inside this union are inside the union around it too.
                // Complexity tradeoff: naive, each name added to every open union, O(n·d) for
                // n names under d nested unions; used, the smaller set merged into the larger
                // when a union ends, so each name moves O(log n) times, O(n log n) in all.
                let mut names = scope.unions.pop().expect("opened by Print::Opens");
                if let Some(u) = scope.unions.last_mut() {
                    if u.len() < names.len() {
                        std::mem::swap(u, &mut names);
                    }
                    u.extend(names);
                }
            }
            Print::Opens => scope.unions.push(HashSet::new()),
        }
        stack[from..].reverse();
    }
    kernel
}

/// The kernel sets of a text still to be written ([`write_parts`]): where each stands in the
/// text, the set with its place, and whether it is printed apart from the rest of its set,
/// written out where it stands and never by a name of its own ([`KType::surfaces_apart`]).
#[derive(Default)]
struct Kernel {
    at: Vec<usize>,
    sets: Vec<(KType, TextPlace)>,
    apart: Vec<bool>,
    /// Where a `(` goes before a union written as an arrow's key or a bound ([`Ty::write_end`]).
    opens: Vec<usize>,
}

/// Pushes `sep` to `parts` before every item but the first, which `first` tells.
fn between<'a>(parts: &mut Vec<Print<'a>>, first: &mut bool, sep: &'a str) {
    if !*first {
        parts.push(Print::Text(sep));
    }
    *first = false;
}

impl fmt::Display for Sig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        self.write(&mut text, &mut Scope::default());
        #[cfg(feature = "printed-types")]
        printed::record(&Ty::func(Arc::new(self.clone())), &text);
        f.write_str(&text)
    }
}

impl Sig {
    /// How a message names the function of this signature: the prelude word it is, as
    /// `bitReverse`, else its type, as `(int, width: int) -> int`.
    pub fn who(&self) -> String {
        match &self.word {
            Some(w) => w.to_string(),
            None => self.to_string(),
        }
    }

    /// Writes its text, in type syntax, to `out`: its variables bounded by carriers by name, in
    /// a bounds clause after the arrows, and the others `_`.
    fn write(&self, out: &mut String, scope: &mut Scope) {
        write_parts(Print::Sig(self, PrintAt::Any), out, scope, None);
    }

    /// Opens its variables in `scope` and pushes the parts of its text to `parts`, in order. It
    /// stands at `at`: a text with a bounds clause is parenthesized anywhere but where a whole
    /// type stands, and an arrow also as a key, a bound or an operand of `|`; an intersection
    /// of arrows, each parenthesized, binds tighter than `|` and needs nothing more.
    fn parts<'a>(&'a self, scope: &mut Scope, parts: &mut Vec<Print<'a>>, at: PrintAt) {
        let morphism = self.morphism();
        let several = morphism.is_none() && self.arrows.len() != 1;
        let hoisted = at == PrintAt::Member && several;
        let bounds = scope.open(self, hoisted);
        let wrap = Sig::wraps(at, several, !bounds.is_empty());
        if wrap {
            parts.push(Print::Text("("));
        }
        if let Some(m) = morphism {
            m.parts(parts);
        } else {
            // A function of one positional parameter is written `K -> V`, its key a `TypeNot`
            // (`Arrow = … | TypeNot '->' Arrow`): `(K) -> V` would read the same, the pair a
            // `GroupType`, which the printer does not write where the grammar does not need it
            // (P191). The key stands at [`PrintAt::Key`], parenthesized only where it is a
            // function, a union, an intersection, a difference, or a tuple of other than one
            // component.
            //
            // A partial arrow is written with `->?` and its result without `#notFound`, which
            // `->?` adds back on reading (DESIGN.md sec:type_language: `K ->? V` has an empty
            // guarantee, its lookup `V | #notFound`), so that it reads back partial and not as
            // the exact arrow `K -> V | #notFound`, another type (FAIL-main-red-exact-domain).
            let bare = matches!(&self.params[..], [p] if p.positional);
            let result = |a: &'a Arrow| match a.partial {
                true => [Print::Text(" ->? "), Print::Found(&a.result)],
                false => [Print::Text(" -> "), self.result_part(a)],
            };
            let mut first = true;
            for a in &self.arrows {
                between(parts, &mut first, " & ");
                if let ([key], true) = (&a.params[..], bare) {
                    if several {
                        parts.push(Print::Text("("));
                    }
                    ParamRange::parts(self.params[0].range.as_ref(), key, PrintAt::Key, parts);
                    parts.extend(result(a));
                    if several {
                        parts.push(Print::Text(")"));
                    }
                    continue;
                }
                parts.push(Print::Text(if several { "((" } else { "(" }));
                let mut one = true;
                for (p, t) in self.params.iter().zip(&a.params) {
                    between(parts, &mut one, ", ");
                    if !p.positional {
                        parts.push(Print::Text(&p.name));
                        parts.push(Print::Text(": "));
                    }
                    ParamRange::parts(p.range.as_ref(), t, PrintAt::Any, parts);
                }
                parts.push(Print::Text(")"));
                parts.extend(result(a));
                if several {
                    parts.push(Print::Text(")"));
                }
            }
        }
        match hoisted {
            true => scope.hoisted.push(bounds),
            false => parts.push(Print::Bounds(self, bounds)),
        }
        if wrap {
            parts.push(Print::Text(")"));
        }
    }

    /// The part of the result of its arrow `a`: the hull of its ints, as a range each end
    /// inclusive (`int[1..=10]`, row RANGE-result-hull), where it has one and `a`'s result is
    /// `int`, which reads back as that range; the result's type otherwise.
    fn result_part<'a>(&'a self, a: &'a Arrow) -> Print<'a> {
        match &self.hull {
            Some(h) if a.result == Ty::carrier(Carrier::Int) => Print::Text(&h.text),
            _ => Print::Ty(&a.result, PrintAt::Result),
        }
    }

    /// Whether a signature's text written at `at` is parenthesized, given whether it is an
    /// intersection of several arrows and whether it writes a bounds clause there.
    fn wraps(at: PrintAt, several: bool, bounded: bool) -> bool {
        match at {
            PrintAt::Any => false,
            PrintAt::Result => bounded,
            // A key or a bound is a `TypeNot`, so an intersection of arrows is parenthesized
            // there as one arrow is (author P222).
            PrintAt::Key | PrintAt::Bound => true,
            PrintAt::Member if several => false,
            PrintAt::Union | PrintAt::Member => bounded || !several,
        }
    }

    /// Whether its text reads the same wherever it stands, but for parentheses: it binds no
    /// variable and holds none ([`Shared`]).
    fn closed(&self) -> bool {
        self.bounds.is_empty() && self.own.is_empty() && self.holds_no_variable()
    }

    /// Whether, as a member of a union that stands where a whole `Type` stands, it leaves its
    /// bounds clause to the end of the union ([`PrintAt::Member`]): an intersection of arrows,
    /// each in its own parentheses, which the clause after the union bounds as it would
    /// inside a pair of its own.
    fn hoists(&self) -> bool {
        self.morphism().is_none() && self.arrows.len() != 1
    }

    /// The morphism type it is written as, if it is one: a function of one unnamed positional
    /// parameter whose one arrow is partial is `K ->? V`, and one whose arrows are `(L) -> V`,
    /// exact, and `(U) -> V | #notFound`, partial, with `L` within `U` and not equal to it, is
    /// `L .. U -> V` (DESIGN.md sec:type_language: a message prints a morphism type in that
    /// form when its bounds differ). Each reads back to the arrows the checker denotes it by.
    /// An exact arrow that may answer `#notFound` is written as an arrow, `K -> V | #notFound`.
    fn morphism(&self) -> Option<Morphism<'_>> {
        let [p] = &self.params[..] else {
            return None;
        };
        if !p.positional || !p.name.is_empty() {
            return None;
        }
        let miss = KType::atom("notFound");
        match &self.arrows[..] {
            // A result of `#notFound` alone is written as it is, `(K) -> #notFound`.
            [a] if a.partial
                && (&miss - &a.result.set).is_empty()
                && a.result != Ty::set(miss.clone()) =>
            {
                Some(Morphism::Partial {
                    key: &a.params[0],
                    range: p.range.as_ref(),
                    value: &a.result,
                })
            }
            [a, b] => {
                let (lower, upper) = (&a.params[0], &b.params[0]);
                let set_only = |t: &Ty| {
                    t.tuples.is_empty() && t.fns.is_empty() && t.vars.is_empty() && !t.dynamic
                };
                (!a.partial
                    && b.partial
                    && set_only(lower)
                    && set_only(upper)
                    && *lower != Ty::empty()
                    && lower != upper
                    && lower.union(upper) == *upper
                    && b.result == a.result.union(&Ty::set(miss)))
                .then_some(Morphism::Bounded {
                    lower,
                    upper,
                    value: &a.result,
                })
            }
            _ => None,
        }
    }

    /// Whether it is a family that maps each key of one key type to itself, its lookup that
    /// key type or `#notFound`, as [`errs_of`] builds, with no tuple or function in that type,
    /// so that [`Sig::family_parts`] can write it bare.
    fn is_family(&self) -> bool {
        matches!((&self.params[..], &self.arrows[..]), ([p], [a])
            if self.data && a.partial && p.positional && a.params[0].tuples.is_empty() && a.params[0].fns.is_empty()
                && a.result == a.params[0].union(&Ty::set(KType::atom("notFound"))))
    }

    /// Opens its variables in `scope` and pushes the parts of its text as a family, a partial
    /// map `K ->? K` (DESIGN.md sec:values_morphisms), to `parts`, in order: its key type, bare,
    /// as [`Sig::is_family`] leaves none that could be read as parameters, twice, since `->?`
    /// adds the `#notFound` of its lookup (sec:type_language). It stands as a payload, where a
    /// whole type stands, so it needs no parentheses, a bounds clause and all ([`PrintAt::Any`]).
    fn family_parts<'a>(&'a self, scope: &mut Scope, parts: &mut Vec<Print<'a>>) {
        let bounds = scope.open(self, false);
        let key = &self.arrows[0].params[0];
        parts.push(Print::Ty(key, PrintAt::Key));
        parts.push(Print::Text(" ->? "));
        parts.push(Print::Ty(key, PrintAt::Result));
        parts.push(Print::Bounds(self, bounds));
    }
}

/// The class a type variable names: `$k` is class `k`.
pub fn class_id(v: &str) -> Option<usize> {
    v.strip_prefix('$')?.parse().ok()
}

/// The `n`th name of a signature's own type variables: `T`, `U`, `V`, `W`, `T5`, ….
pub fn var_name(n: usize) -> Arc<str> {
    Names::Variables.nth(n)
}

/// The types printed on a thread while recording is on, each with the text printed (feature
/// `printed-types`, OSP-diag): a test parses each text back and compares.
#[cfg(feature = "printed-types")]
pub mod printed {
    use std::cell::RefCell;

    use super::Ty;

    thread_local! {
        static SEEN: RefCell<Option<Vec<(Ty, String, String)>>> = const { RefCell::new(None) };
    }

    /// Starts recording on this thread, dropping what was recorded.
    pub fn start() {
        SEEN.set(Some(Vec::new()));
    }

    /// What was recorded since `start`, in printed order; recording stops.
    pub fn take() -> Vec<(Ty, String)> {
        take_raw()
            .into_iter()
            .map(|(t, text, _)| (t, text))
            .collect()
    }

    /// As [`take`], each also with its text as printed, which in a message holds references
    /// to the definitions the message writes apart.
    pub fn take_raw() -> Vec<(Ty, String, String)> {
        SEEN.take().unwrap_or_default()
    }

    /// Records that `t` was printed as `text`, if recording is on. A text of a message, which names
    /// definitions the message writes apart, is recorded with them before it, as it reads alone.
    pub fn record(t: &Ty, text: &str) {
        SEEN.with_borrow_mut(|seen| {
            if let Some(seen) = seen {
                let alone = zed_kernel::types::defs::plain(text);
                seen.push((t.clone(), alone, text.to_string()));
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod bench;

    /// A list of members shared by a copy is changed in the copy only; a push keeps the set
    /// of members a union reads, a removal drops it, and equal lists hash alike whatever
    /// operations built them (FAIL-types-binding-tuple-shapes-copied).
    #[test]
    fn a_list_of_members_is_shared_by_copies_and_kept_by_each() {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let hash = |m: &Members<u32>| BuildHasherDefault::<DefaultHasher>::default().hash_one(m);
        let mut a: Members<u32> = Members::new();
        assert!(a.is_empty() && a.first().is_none() && a.only().is_none());
        assert!(a.insert_new(1) && a.insert_new(2) && !a.insert_new(1));
        assert_eq!(a.to_vec(), [1, 2]);
        let mut b = a.clone();
        assert!(b.insert_new(3) && !b.insert_new(2));
        assert_eq!((a.to_vec(), b.to_vec()), (vec![1, 2], vec![1, 2, 3]));
        assert!(!a.contains(&3) && b.contains(&3));
        // A list of the same members in the same order is equal and hashes alike, however it
        // was built; in another order it is not equal.
        let c: Members<u32> = vec![1, 2, 3].into();
        assert!(b == c && hash(&b) == hash(&c));
        let d: Members<u32> = vec![2, 1, 3].into();
        assert!(b != d);
        // A removal drops the set; the next lookup makes it again from what is left.
        assert_eq!(b.pop(), Some(3));
        assert!(!b.contains(&3) && b == a && hash(&b) == hash(&a));
        assert!(b.insert_new(3));
        b.retain(|&x| x != 1);
        assert_eq!(b.to_vec(), [2, 3]);
        assert!(!b.contains(&1) && b.insert_new(1));
        assert_eq!((b.len(), b[2], b.last()), (3, 1, Some(&1)));
        assert_eq!(b.iter().rev().copied().collect::<Vec<_>>(), [1, 3, 2]);
        while b.pop().is_some() {}
        assert!(b.is_empty() && b == Members::new() && hash(&b) == hash(&Members::new()));
        assert_eq!(a.clone().into_vec(), [1, 2]);
        // A list that is a duplicate of a member at two places keeps both.
        let mut e: Members<u32> = vec![4, 4].into();
        assert_eq!(e.len(), 2);
        assert!(!e.insert_new(4));
        e.push(4);
        assert_eq!(e.to_vec(), [4, 4, 4]);
    }

    /// Two types of 60 levels `t(k + 1) = (t(k), t(k))`, and the same through functions, built
    /// apart, compare in the size of their graphs, not their 2^60 paths: a row or function
    /// held through a list two copies share is recorded as shared ([`Same`]), though the list
    /// is its one owner (FAIL-types-binding-tuple-shapes-copied).
    #[test]
    fn types_doubled_through_a_shared_list_compare_once_a_node() {
        let int = Ty::carrier(Carrier::Int);
        let doubled = || (0..60).fold(int.clone(), |t, _| Ty::tuple(vec![t.clone(), t]));
        assert!(doubled() == doubled());
        // Each level a function `() -> (t, t)`, held in the list of its type's functions.
        let pair = |t: Ty| Ty::tuple(vec![t.clone(), t]);
        let fns = || {
            (0..60).fold(int.clone(), |t, _| {
                Ty::func(Arc::new(Sig::one(Vec::new(), Vec::new(), pair(t))))
            })
        };
        assert!(fns() == fns());
    }

    /// A union of tuple shapes, or of payload shapes, of free variables is within itself with
    /// nothing bound: each member is held by the shape equal to it, not by the first in
    /// written order, which holds it only by binding a variable (`(X1,)` in `(X0,)` binds `X0`
    /// to `X1`) (FAIL-types-singleton-tuple-union-match).
    #[test]
    fn shapes_of_free_variables_are_within_themselves_binding_nothing() {
        let xs: Vec<Ty> = (0..3).map(|i| Ty::var(format!("X{i}").into())).collect();
        for n in 1..=3 {
            let rows = Ty::union_all(
                &xs[..n]
                    .iter()
                    .map(|x| Ty::tuple(vec![x.clone()]))
                    .collect::<Vec<_>>(),
            );
            assert!(rows.subtype(&rows), "{n} tuple shapes");
            let last = &xs[n - 1];
            let pairs = xs[..n]
                .iter()
                .map(|x| Ty::tuple(vec![x.clone(), last.clone()]));
            let pairs = Ty::union_all(&pairs.collect::<Vec<_>>());
            assert!(pairs.subtype(&pairs), "{n} pairs");
            let shapes = (xs[..n].iter()).map(|x| Shape::new(vec![x.clone()], BTreeMap::new()));
            let payloads = payload_ty("a", shapes.collect());
            assert!(payloads.subtype(&payloads), "{n} payload shapes");
        }
    }

    /// The carrier masks: `NUMBER_BITS` holds exactly the numbers, `f32` among them; each
    /// carrier has its own bit below [`OTHER`] and its own base, and the five carriers that came
    /// before `f32` keep the bits they had (FLOAT-f32).
    #[test]
    fn every_carrier_has_its_own_bit_and_the_numbers_are_the_number_bits() {
        let numbers = Carrier::ALL.into_iter().filter(|c| c.numeric());
        assert_eq!(numbers.clone().collect::<Vec<_>>(), Carrier::NUMBERS);
        assert_eq!(numbers.fold(0, |m, c| m | c.bit()), Carrier::NUMBER_BITS);
        assert_ne!(Carrier::NUMBER_BITS & Carrier::F32.bit(), 0);
        let bits = Carrier::ALL.map(Carrier::bit);
        assert_eq!(bits, [1, 2, 4, 8, 16, 32]);
        assert_eq!(bits.iter().fold(OTHER, |m, b| m | b), EVERY);
        let mut bases = Carrier::ALL.map(Carrier::base);
        bases.sort_unstable();
        assert_eq!(bases, [0, 1, 2, 3, 4, 5]);
        assert_eq!(Carrier::of_mask(Carrier::NUMBER_BITS).count(), 4);
    }

    /// How [`every_arrow_fits`] decides in a differential test.
    #[derive(Clone, Copy, PartialEq, Eq)]
    pub(super) enum Reference {
        /// By the index.
        None,
        /// By every pair of arrows, as before the index, with no arrows covering together.
        Pairs,
        /// By every pair, then, at each parameter, by every set of arrows ([`together`]).
        Subsets,
    }

    /// The most arrows whose every subset [`together`] tries.
    const SUBSETS: usize = 10;

    /// The search with no index (COMPLEXITY.md F82): each arrow of `q` on an arrow of `s`
    /// equal to it, then on every arrow of `s` in order, then, under [`Reference::Subsets`],
    /// on every set of arrows of `s` ([`together`]).
    pub(super) async fn reference<'m>(
        s: &Sig,
        sas: &[Arrow],
        qas: &[Arrow],
        c: &'m Comparing<'m, '_>,
    ) -> bool {
        let wide = REFERENCE.get() == Reference::Subsets;
        let mut equal: HashMap<&Arrow, &Arrow> = HashMap::with_capacity(sas.len());
        for sa in sas {
            equal.entry(sa).or_insert(sa);
        }
        'qas: for qa in qas {
            let mut refused = None;
            if let Some(sa) = equal.get(qa)
                && (equal_fits(s, sa, &c.cx.borrow())
                    || arrow_fits_alone(s, sa, qa, c, &mut refused).await)
            {
                continue;
            }
            for sa in sas {
                if arrow_fits_alone(s, sa, qa, c, &mut refused).await {
                    continue 'qas;
                }
            }
            if wide {
                let all = (0..sas.len()).collect::<Vec<_>>();
                let before = c.begin_alone();
                let ok = together(s, sas, qa, c).await || met(s, sas, &all, qa, c).await;
                let why = c.end_alone(before);
                if ok && why.is_none() {
                    continue;
                }
                refused = refused.or(why);
            }
            uncovered(refused, c);
            return false;
        }
        true
    }

    /// [`arrow_fits`] with the parameter `skip` left out.
    async fn fits_but<'m>(
        s: &Sig,
        sa: &Arrow,
        qa: &Arrow,
        skip: usize,
        c: &'m Comparing<'m, '_>,
    ) -> bool {
        let mut b = Binds::of_arrow(s, sa, None, &c.cx.borrow());
        for (j, (x, y)) in qa.params.iter().zip(&sa.params).enumerate() {
            if j != skip && !c.sub_in(x, y, &mut b).await {
                return false;
            }
        }
        let held = bounds_hold(s, sa, &b, &c.cx.borrow());
        held && result_within(s, sa, qa, &b, c).await && instance_within(s, sa, qa, &b, c).await
    }

    /// Whether, at some parameter, a set of arrows of `sas` covers `qa`: each arrow of the set
    /// has a parameter type there that binds nothing ([`binds_nothing`]), takes `qa`'s other parameters and returns within its
    /// result, and the union of their parameter types there holds `qa`'s. Every nonempty set is
    /// tried when there are at most [`SUBSETS`] arrows; with more, the set of every arrow that
    /// qualifies, which holds what any of its subsets holds.
    async fn together<'m>(s: &Sig, sas: &[Arrow], qa: &Arrow, c: &'m Comparing<'m, '_>) -> bool {
        for j in 0..qa.params.len().min(s.params.len()) {
            let mut ok = Vec::with_capacity(sas.len());
            for sa in sas {
                let p = &sa.params[j];
                let free = binds_nothing(p, &c.cx.borrow());
                ok.push(free && fits_but(s, sa, qa, j, c).await);
            }
            let holds = async |set: &dyn Fn(usize) -> bool| {
                let u = Ty::union_all(
                    (0..sas.len())
                        .filter(|&i| set(i))
                        .map(|i| &sas[i].params[j]),
                );
                c.sub_in(&qa.params[j], &u, &mut Binds::new()).await
            };
            if sas.len() <= SUBSETS {
                for m in 1u32..1 << sas.len() {
                    let has = |i: usize| m & (1 << i) != 0;
                    if (0..sas.len()).all(|i| !has(i) || ok[i]) && holds(&has).await {
                        return true;
                    }
                }
            } else if ok.contains(&true) && holds(&|i| ok[i]).await {
                return true;
            }
        }
        false
    }

    /// splitmix64 from a seed of [`crate::seed::seed`], new on each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (z ^ (z >> 31)) % n
        }
    }

    /// The bound of the variable `B` of the signatures below: `int | f64`.
    const B_MASK: u8 = 0b11;

    /// A random member: an atom of eight, a carrier, a literal, an atom with a payload, or,
    /// when `open`, a type variable, the bounded variable `B`, the unknown or a function.
    fn member(rng: &mut Rng, open: bool) -> Ty {
        match rng.below(if open { 14 } else { 10 }) {
            0..=4 => Ty::set(KType::atom(&format!("a{}", rng.below(8)))),
            5 => Ty::carrier(Carrier::Int),
            6 => Ty::carrier(Carrier::Str),
            7 => Ty::carrier(Carrier::Bool),
            8 => Ty::lit(&Value::Int(rng.below(3) as i64)),
            9 => Ty::set(KType::atom_with("p", &KType::tuple(vec![KType::int()]))),
            10 => Ty::var("T".into()),
            11 => Ty::var("B".into()),
            12 => Ty::dynamic(),
            _ => {
                let a = Arrow {
                    params: vec![Ty::set(KType::atom("a0"))],
                    result: Ty::set(KType::atom(&format!("a{}", rng.below(2)))),
                    partial: false,
                };
                Ty::func(Arc::new(sig(vec![a], 1, false)))
            }
        }
    }

    /// A union of one to three random members.
    fn union(rng: &mut Rng, open: bool) -> Ty {
        let k = 1 + rng.below(3);
        (0..k).fold(Ty::empty(), |t, _| t.union(&member(rng, open)))
    }

    /// A signature of `width` named parameters with `arrows`, its own variables `T` and `B`,
    /// `B` bounded by `int | f64` when `bounded`.
    fn sig(arrows: Vec<Arrow>, width: usize, bounded: bool) -> Sig {
        let mut s = Sig {
            params: (0..width)
                .map(|j| SParam {
                    name: format!("x{j}").into(),
                    positional: false,
                    default: None,
                    range: None,
                })
                .collect(),
            arrows,
            bounds: BTreeMap::new(),
            data: false,
            dense: Dense::No,
            keys: None,
            word: None,
            needs: Vec::new(),
            own: ["T".into(), "B".into()].into_iter().collect(),
            held: BTreeSet::new(),
            named: 0,
            hull: None,
            facts: Facts::default(),
        };
        if bounded {
            s.bounds.insert("B".into(), B_MASK);
        }
        s.note_held();
        s
    }

    /// An arrow of `q` near `sa`: each parameter type narrowed to some of its members or
    /// widened by one, the result widened or narrowed alike, so that about half fit.
    fn near(rng: &mut Rng, sa: &Arrow) -> Arrow {
        let mut vary = |t: &Ty| match rng.below(3) {
            0 => t.clone(),
            1 => t.union(&member(rng, false)),
            _ => {
                let ps = t.pieces();
                ps[rng.below(ps.len() as u64) as usize].ty()
            }
        };
        Arrow {
            params: sa.params.iter().map(&mut vary).collect(),
            result: vary(&sa.result),
            partial: sa.partial,
        }
    }

    /// An arrow of `q` that two arrows of `s` may cover only together: at one parameter the
    /// union of theirs, at the others a piece of `a`'s, and the union of their results.
    fn joined(rng: &mut Rng, a: &Arrow, b: &Arrow) -> Arrow {
        let at = rng.below(a.params.len() as u64) as usize;
        let params = (0..a.params.len())
            .map(|j| {
                let ps = a.params[j].pieces();
                if j == at || ps.is_empty() {
                    a.params[j].union(&b.params[j])
                } else {
                    ps[rng.below(ps.len() as u64) as usize].ty()
                }
            })
            .collect();
        Arrow {
            params,
            result: a.result.union(&b.result),
            partial: a.partial,
        }
    }

    /// One arrow of `q` for the arrows `sas` of `s`: random, near an arrow of `s`, or joined
    /// from two.
    fn arrow_of_q(rng: &mut Rng, sas: &[Arrow], width: usize, wider: bool, open: bool) -> Arrow {
        let pick = |rng: &mut Rng| &sas[rng.below(sas.len() as u64) as usize];
        match rng.below(6) {
            0 if wider => Arrow {
                params: (0..width).map(|_| wider_union(rng, open)).collect(),
                result: wider_union(rng, false),
                partial: false,
            },
            0 => Arrow {
                params: (0..width).map(|_| union(rng, false)).collect(),
                result: union(rng, false),
                partial: false,
            },
            1 | 2 => {
                let (a, b) = (pick(rng), pick(rng));
                joined(rng, a, b)
            }
            _ => {
                let sa = pick(rng);
                if wider {
                    wider_near(rng, sa)
                } else {
                    near(rng, sa)
                }
            }
        }
    }

    /// `fits_sig` by the index, by every pair and by every set of arrows, on one pair of
    /// signatures.
    fn three(s: &Sig, q: &Sig) -> (bool, bool, bool) {
        let new = fits_sig(s, q);
        REFERENCE.set(Reference::Pairs);
        let pairs = fits_sig(s, q);
        REFERENCE.set(Reference::Subsets);
        let subsets = fits_sig(s, q);
        REFERENCE.set(Reference::None);
        (new, pairs, subsets)
    }

    /// Counts of verdicts: fit, do not fit, and fit only by arrows together.
    #[derive(Default)]
    struct Counts {
        fit: usize,
        unfit: usize,
        together: usize,
    }

    impl Counts {
        /// Compares the index with every set of arrows on `q` in `s`, and counts the verdict.
        fn compare(&mut self, s: &Sig, q: &Sig, what: &str) {
            let (new, pairs, subsets) = three(s, q);
            assert_eq!(new, subsets, "{what}: {q} in {s}");
            assert!(subsets || !pairs, "{what}: a fit by one arrow is a fit");
            match (new, pairs) {
                (true, false) => self.together += 1,
                (true, true) => self.fit += 1,
                _ => self.unfit += 1,
            }
        }

        /// The counts, as `fit`, `unfit`, `together`.
        fn get(&self) -> [usize; 3] {
            [self.fit, self.unfit, self.together]
        }
    }

    /// Each verdict of [`Counts`] on a built overload of one parameter, so that the comparison
    /// could fail with each on every run: `s` has the arrows `(a) -> a` and `(b) -> b`. `s`
    /// itself fits by each arrow's own; `(c) -> c` fits by none, since no arrow of `s` takes
    /// `c`; `(a | b) -> a | b` fits by no one arrow, since each takes only part of `a | b`,
    /// but by the two together, each part going to its arrow and each result inside `a | b`.
    /// `(a) -> a` does not fit: a domain is exact (FAIL-types-fn-param-exact-domain), and `s`
    /// also takes `b`, which it does not.
    fn built_verdicts(a: Ty, b: Ty, c: Ty, what: &str) {
        let arrow = |p: &Ty, r: &Ty| Arrow {
            params: vec![p.clone()],
            result: r.clone(),
            partial: false,
        };
        let s = sig(vec![arrow(&a, &a), arrow(&b, &b)], 1, false);
        let ab = a.union(&b);
        let one = |q: &Ty| sig(vec![arrow(q, q)], 1, false);
        let mut counts = Counts::default();
        for (q, verdict) in [
            (s.clone(), [1, 0, 0]),
            (one(&a), [0, 1, 0]),
            (one(&c), [0, 1, 0]),
            (one(&ab), [0, 0, 1]),
        ] {
            let before = counts.get();
            counts.compare(&s, &q, what);
            let got: Vec<usize> = (0..3).map(|i| counts.get()[i] - before[i]).collect();
            assert_eq!(got, verdict, "{what}: {q} in {s}: [fit, unfit, together]");
        }
    }

    /// The index of a binding's variables ([`BindKeys`]), kept as the binding changes after a
    /// replacement made it, lets each replacement and substitution replace exactly what one
    /// with an index made anew does: a row whose variable is bound is entered, and one whose
    /// variable was unbound, by `remove` or `retain`, is kept whole. The variables are classes
    /// on the same bit (`$1`, `$65`), classes far apart and names.
    #[test]
    fn the_index_of_a_binding_follows_its_changes() {
        let vars = ["$1", "$65", "$3", "$700", "a", "b", "c"];
        let t = Ty::tuple(
            vars.iter()
                .map(|v| {
                    let one = Ty::lit(&Value::int(1.into()));
                    Ty::tuple(vec![Ty::tuple(vec![Ty::var((*v).into()), one])])
                })
                .collect(),
        );
        let int = Ty::carrier(Carrier::Int);
        let check = |b: &Binds| {
            let fresh = Binds::from(
                b.iter()
                    .map(|(v, t)| (v.clone(), t.clone()))
                    .collect::<BTreeMap<_, _>>(),
            );
            assert_eq!(t.replace(b), t.replace(&fresh), "{b:?}");
            assert_eq!(t.subst(b), t.subst(&fresh), "{b:?}");
            assert_eq!(b.digest, fresh.digest, "the digest kept as made: {b:?}");
        };
        let mut b: Binds = [("$1".into(), int.clone()), ("a".into(), int.clone())].into();
        check(&b);
        b.insert("$65".into(), int.clone());
        b.insert("b".into(), int.clone());
        check(&b);
        b.remove("$1");
        b.remove("a");
        check(&b);
        b.or_insert_with("$700".into(), || int.clone());
        b.or_insert_with("$65".into(), Ty::empty);
        b.extend([("c".into(), int.clone()), ("$3".into(), int.clone())]);
        check(&b);
        // A binding united with more, one made by uniting, and one bound again.
        b.unite("c".into(), &Ty::carrier(Carrier::F64));
        b.unite("d".into(), &int);
        check(&b);
        b.insert("c".into(), int.clone());
        check(&b);
        b.retain(|v, _| !v.starts_with('$') || &**v == "$3");
        check(&b);
        b.retain(|_, _| false);
        assert_eq!(t.replace(&b), t);
        b.insert("$1".into(), int.clone());
        check(&b);
        // `update_each` changes the types and keeps the names; a copy made before keeps its
        // own types (the map is persistent: the copy shares nodes, not changes).
        b.insert("a".into(), int.clone());
        let before = b.clone();
        b.update_each(|t| *t = Ty::empty());
        check(&b);
        assert!(b.values().all(|t| *t == Ty::empty()));
        assert_eq!(
            b.keys().collect::<Vec<_>>(),
            before.keys().collect::<Vec<_>>()
        );
        assert!(before.values().all(|t| *t == int));
        check(&before);
    }

    /// A set of variables keeps the sum of its names' hashes as it changes: sets of the same
    /// names, however made, are equal and hash alike; a copy keeps its names when the
    /// original changes; and a union takes the names of both sides, the larger side first or
    /// not (FAIL-types-binding-union-copied).
    #[test]
    fn variable_sets_keep_their_digest_as_they_change() {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let hash = |s: &VarSet| BuildHasherDefault::<DefaultHasher>::default().hash_one(s);
        let names = |ns: &[&str]| -> VarSet { ns.iter().map(|&n| Arc::from(n)).collect() };
        let fresh = |s: &VarSet| -> VarSet { s.iter().cloned().collect() };
        let check = |s: &VarSet| {
            assert_eq!(*s, fresh(s), "{s:?}");
            assert_eq!(hash(s), hash(&fresh(s)), "{s:?}");
            assert_eq!(s.digest, fresh(s).digest, "{s:?}");
        };
        let mut a = names(&["c", "a", "b"]);
        assert_eq!(a, names(&["a", "b", "c"]));
        assert_eq!(a.first().map(|v| &**v), Some("a"));
        assert!(
            !a.insert("a".into()),
            "a name already there is not added again"
        );
        check(&a);
        let copy = a.clone();
        assert!(a.remove("b"));
        assert!(!a.remove("b"), "a name not there is not removed");
        check(&a);
        assert_eq!(copy, names(&["a", "b", "c"]), "the copy keeps its names");
        assert_ne!(a, copy);
        assert_ne!(names(&["a", "b"]), names(&["a", "c"]));
        a.retain(|v| &**v != "a");
        assert_eq!(a, names(&["c"]));
        check(&a);
        // Union from either side: the smaller into a copy of the larger.
        let big = names(&["p", "q", "r", "s"]);
        let mut small = names(&["a", "q"]);
        small.add_all(&big);
        let mut large = big.clone();
        large.add_all(&names(&["a", "q"]));
        assert_eq!(small, names(&["a", "p", "q", "r", "s"]));
        assert_eq!(small, large);
        check(&small);
        assert_eq!(
            big,
            names(&["p", "q", "r", "s"]),
            "a union leaves its operands"
        );
        // As part of a type: a variable bound to one more member at a time.
        let mut b = Binds::new();
        for v in ["x", "y", "x", "z"] {
            b.unite("T".into(), &Ty::var(v.into()));
        }
        let t = b.get("T").expect("bound");
        assert_eq!(t.vars, names(&["x", "y", "z"]));
        assert_eq!(
            *t,
            Ty::union_all(&[
                Ty::var("z".into()),
                Ty::var("x".into()),
                Ty::var("y".into())
            ])
        );
    }

    /// The number of cases of [`the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows`],
    /// one at each size of [`INDEX_SIZES`] in turn.
    const INDEX_CASES: usize = 12;

    /// The sizes of `s` in [`the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows`]:
    /// one arrow, two, a few, more than [`SUBSETS`] (where the reference tries one
    /// set, not every set) and many. The overloads of 300 arrows are
    /// `bench::the_index_of_arrows_gives_the_verdict_on_large_overloads`.
    const INDEX_SIZES: [usize; 6] = [1, 2, 5, 8, 20, 40];

    #[test]
    fn the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows() {
        // Over random overloads, with unions of atoms and carriers and some open parameter
        // types, each arrow of `q` alone and `q` whole get the verdict of comparing with every
        // arrow of `s` and then with every set of arrows of `s` (every subset of at most
        // SUBSETS arrows), every arrow of `s` that fits an arrow of `q` is a candidate, and
        // every arrow that may take part in covering one together is a candidate for it.
        let carrier = |c| Ty::carrier(c);
        built_verdicts(
            carrier(Carrier::Int),
            carrier(Carrier::Str),
            carrier(Carrier::Bool),
            "built carriers",
        );
        let mut rng = Rng(crate::seed::seed(
            "the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows",
        ));
        let mut counts = Counts::default();
        for case in 0..INDEX_CASES {
            index_case(
                &mut rng,
                INDEX_SIZES[case % INDEX_SIZES.len()],
                case,
                &mut counts,
            );
        }
        let [fit, unfit, together] = counts.get();
        println!("{fit} fit, {unfit} do not, {together} fit only together");
    }

    /// One case of [`the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows`]: an
    /// overload `s` of `n` arrows, each arrow of `q` alone and `q` whole compared in `s`.
    /// Whether the parameter types may be open (two times in three) and whether `s` holds
    /// `B` (one time in two) are drawn apart from `n`.
    fn index_case(rng: &mut Rng, n: usize, case: usize, counts: &mut Counts) {
        let width = 1 + rng.below(2) as usize;
        let open = rng.below(3) != 0;
        let sas: Vec<Arrow> = (0..n)
            .map(|_| {
                let params = (0..width).map(|_| union(rng, open)).collect();
                let wide = open && rng.below(4) == 0;
                Arrow {
                    params,
                    result: union(rng, wide),
                    partial: false,
                }
            })
            .collect();
        let qas: Vec<Arrow> = (0..n.min(60))
            .map(|_| arrow_of_q(rng, &sas, width, false, false))
            .collect();
        let s = sig(sas.clone(), width, rng.below(2) == 0);
        let order = rng.below(u64::MAX);
        for qa in &qas {
            let q = sig(vec![qa.clone()], width, false);
            counts.compare(&s, &q, &format!("case {case}"));
            same_in_every_order(&s, &q, order, &format!("case {case}"));
        }
        let q = sig(qas.clone(), width, false);
        counts.compare(&s, &q, &format!("case {case}, the whole of q"));
        same_in_every_order(&s, &q, order, &format!("case {case}"));
        index_keeps(&s, &qas, width, &format!("case {case}"));
    }

    /// Every pair and every arrow, on the arrows as written: the index never leaves out an
    /// arrow of `s` that fits an arrow of `qas`, or one that may cover one together with
    /// others, whichever key list or result list it draws from.
    fn index_keeps(s: &Sig, qas: &[Arrow], width: usize, what: &str) {
        let index = ArrowIndex::new(&s.arrows, width);
        comparing!(&mut Cx::default(), |c| async {
            let c = &c;
            for qa in qas {
                let candidates = index.may_fit(qa);
                for (i, sa) in s.arrows.iter().enumerate() {
                    if arrow_fits(s, sa, qa, c).await {
                        assert!(
                            candidates.binary_search(&i).is_ok(),
                            "{what}: arrow {i} fits but is no candidate"
                        );
                    }
                }
                let covering = index.covering(qa, true);
                let meeting = index.covering(qa, false);
                for (i, sa) in s.arrows.iter().enumerate() {
                    // An arrow that misses a parameter takes part only where it meets it there,
                    // and one that takes a parameter of no value takes no value.
                    let part = part_of(s, sa, qa, c).await.map(|p| p.0);
                    let meets = |j: usize| sa.params[j].meets(&qa.params[j]);
                    if (part == Some(Part::Whole) && qa.params.iter().all(|t| !t.is_empty()))
                        || matches!(part, Some(Part::At(j, _)) if meets(j))
                    {
                        assert!(
                            meeting.binary_search(&i).is_ok(),
                            "{what}: arrow {i} takes part of an arrow of q but is no candidate: {part:?} {:?} {:?} {:?}",
                            sa.params.iter().map(|t| t.to_string()).collect::<Vec<_>>(),
                            qa.params.iter().map(|t| t.to_string()).collect::<Vec<_>>(),
                            (sa.result.to_string(), qa.result.to_string())
                        );
                    }
                }
                for j in 0..width {
                    for (i, sa) in s.arrows.iter().enumerate() {
                        let p = &sa.params[j];
                        let free = binds_nothing(p, &c.cx.borrow());
                        if free && p.meets(&qa.params[j]) && fits_but(s, sa, qa, j, c).await {
                            assert!(
                                covering.binary_search(&i).is_ok(),
                                "{what}: arrow {i} may cover at {j} but is no candidate"
                            );
                        }
                    }
                }
            }
        })
    }

    /// The verdict on `q` in `s` is the same with the arrows of `s` reversed, rotated by one
    /// and shuffled, and with the arrows of `q` reversed: the index and the cover try arrows
    /// in their order, and the verdict must not depend on it.
    fn same_in_every_order(s: &Sig, q: &Sig, seed: u64, what: &str) {
        let verdict = fits_sig(s, q);
        let mut rng = Rng(seed ^ 0x0bde_5eed);
        let n = s.arrows.len();
        let mut shuffled = s.arrows.clone();
        for i in (1..n).rev() {
            shuffled.swap(i, rng.below(i as u64 + 1) as usize);
        }
        let mut rotated = s.arrows.clone();
        rotated.rotate_left(1.min(n));
        let reversed: Vec<Arrow> = s.arrows.iter().rev().cloned().collect();
        for (how, arrows) in [
            ("reversed", reversed),
            ("rotated", rotated),
            ("shuffled", shuffled),
        ] {
            let mut p = s.clone();
            p.arrows = arrows;
            assert_eq!(fits_sig(&p, q), verdict, "{what}: s {how}: {q} in {s}");
        }
        let mut q_reversed = q.clone();
        q_reversed.arrows.reverse();
        assert_eq!(
            fits_sig(s, &q_reversed),
            verdict,
            "{what}: q reversed: {q} in {s}"
        );
    }

    /// A random member of the wider family: those of [`member`], and a cofinite set of atoms,
    /// every atom, an atom whose payload type is empty, a `bool` literal, every `rat`
    /// and `f64`, tuples of carriers and atoms, a kind-wide part, and, when `open`, a tuple
    /// holding the variable `T` or the bounded variable `B`.
    fn wider_member(rng: &mut Rng, open: bool) -> Ty {
        match rng.below(if open { 13 } else { 12 }) {
            0..=1 => member(rng, open),
            2 => Ty::set(&atoms() - &KType::atom(&format!("a{}", rng.below(8)))),
            3 => Ty::set(atoms()),
            4 => Ty::set(KType::atom_with("e", &KType::empty())),
            5 => Ty::lit(&Value::Bool(rng.below(2) == 0)),
            6 => Ty::carrier(Carrier::Rat),
            7 => Ty::carrier(Carrier::F64),
            8 => Ty::tuple(vec![
                Ty::carrier(Carrier::Int),
                Ty::set(KType::atom(&format!("a{}", rng.below(3)))),
            ]),
            9 => Ty::tuple(vec![
                Ty::carrier(Carrier::Int).union(&Ty::carrier(Carrier::Str)),
            ]),
            10 => Ty::set(KType::tuple(vec![KType::top(); 2])),
            11 => Ty::set(wide()),
            _ => Ty::tuple(vec![Ty::var(
                if rng.below(2) == 0 { "T" } else { "B" }.into(),
            )]),
        }
    }

    /// A union of one to three members of the wider family, sometimes with a member of the
    /// first family.
    fn wider_union(rng: &mut Rng, open: bool) -> Ty {
        let k = 1 + rng.below(3);
        (0..k).fold(Ty::empty(), |t, _| t.union(&wider_member(rng, open)))
    }

    /// [`near`] with the members of the wider family, a type of no piece kept as it is.
    fn wider_near(rng: &mut Rng, sa: &Arrow) -> Arrow {
        let mut vary = |t: &Ty| match (rng.below(3), t.pieces()) {
            (1, _) => t.union(&wider_member(rng, false)),
            (2, ps) if !ps.is_empty() => ps[rng.below(ps.len() as u64) as usize].ty(),
            _ => t.clone(),
        };
        Arrow {
            params: sa.params.iter().map(&mut vary).collect(),
            result: vary(&sa.result),
            partial: sa.partial,
        }
    }

    /// [`sig`] with `B` bounded by `mask` when given.
    fn sig_mask(arrows: Vec<Arrow>, width: usize, mask: Option<u8>) -> Sig {
        let mut s = sig(arrows, width, false);
        if let Some(m) = mask {
            s.bounds.insert("B".into(), m);
            s.note_held();
        }
        s
    }

    /// The number of cases of
    /// [`the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes`], one at
    /// each size of [`WIDER_SIZES`] in turn.
    const WIDER_CASES: usize = 15;

    /// The sizes of `s` in
    /// [`the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes`]. The
    /// overloads of 90 arrows are `bench::the_index_of_arrows_gives_the_verdict_on_large_overloads`.
    const WIDER_SIZES: [usize; 5] = [1, 3, 6, 10, 30];

    #[test]
    fn the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes() {
        // As above, on cofinite and empty-payload atoms, tuples, kind-wide parts and literals,
        // with `B` of each side bounded or not: `B` of `q` that a parameter holds is a rigid
        // variable, a bound with OTHER reads `B` of `s` unheld as the unknown.
        // Each verdict on tuples of the wider family: `(int, a0)`, `(int, a1)` and `(int, a2)`
        // are tuples of one carrier and three different atoms, so no two share a value.
        let pair = |a: &str| Ty::tuple(vec![Ty::carrier(Carrier::Int), Ty::set(KType::atom(a))]);
        built_verdicts(pair("a0"), pair("a1"), pair("a2"), "built tuples");
        let mut rng = Rng(crate::seed::seed(
            "the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes",
        ));
        let mut counts = Counts::default();
        for case in 0..WIDER_CASES {
            wider_case(
                &mut rng,
                WIDER_SIZES[case % WIDER_SIZES.len()],
                case,
                &mut counts,
            );
        }
        let [fit, unfit, together] = counts.get();
        println!("{fit} fit, {unfit} do not, {together} fit only together");
    }

    /// One case of
    /// [`the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes`], on an
    /// overload `s` of `n` arrows. Whether the parameter types may be open (two times in three)
    /// is drawn apart from `n`.
    fn wider_case(rng: &mut Rng, n: usize, case: usize, counts: &mut Counts) {
        let (s, qas, width, qm, order) = wider_input(rng, n);
        for qa in &qas {
            let q = sig_mask(vec![qa.clone()], width, qm);
            counts.compare(&s, &q, &format!("case {case}"));
            same_in_every_order(&s, &q, order, &format!("case {case}"));
        }
        index_keeps(&s, &qas, width, &format!("wider case {case}"));
        let q = sig_mask(qas, width, qm);
        counts.compare(&s, &q, &format!("case {case}, the whole of q"));
        same_in_every_order(&s, &q, order, &format!("case {case}, the whole of q"));
    }

    /// The input of one [`wider_case`] of `n` arrows: `s`, the arrows of `q`, their width, the
    /// bound of `B` in `q`, and the seed of the orders of the arrows.
    fn wider_input(rng: &mut Rng, n: usize) -> (Sig, Vec<Arrow>, usize, Option<u8>, u64) {
        let masks = [None, Some(B_MASK), Some(0b1001), Some(OTHER | 0b1)];
        let width = 1 + rng.below(2) as usize;
        let open = rng.below(3) != 0;
        let sas: Vec<Arrow> = (0..n)
            .map(|_| {
                let params = (0..width).map(|_| wider_union(rng, open)).collect();
                let wide = open && rng.below(4) == 0;
                Arrow {
                    params,
                    result: wider_union(rng, wide),
                    partial: false,
                }
            })
            .collect();
        let qas: Vec<Arrow> = (0..n.min(30))
            .map(|_| arrow_of_q(rng, &sas, width, true, open))
            .collect();
        let s = sig_mask(sas, width, masks[rng.below(4) as usize]);
        let qm = masks[rng.below(4) as usize];
        let order = rng.below(u64::MAX);
        (s, qas, width, qm, order)
    }

    /// An arrow of `s` tried for an arrow of `q` whose comparison is refused (two tuples each
    /// needing a later shape of one bucket, [`Comparing::search`]) does not refuse the whole
    /// comparison when another arrow fits: the verdict is the same in every order of the
    /// arrows. Before the fix, a refusal inside an arrow tried and dropped made `fits_sig`
    /// answer false, so `q` fitted `s` with its arrows in one order and not in another. Found
    /// at seed 158393 of the test above, case 4, `B` of `q` bounded by `OTHER | 1`; reduced,
    /// `s` = `((x0: _ \ (int | f32 | f64 | rat | false | String | (_ ->? _))) -> #a1) &
    /// ((x0: T | (..) | {..}) -> (int, #a1)) & ((x0: _ \ (int | f32 | f64 | rat | bool |
    /// String | (_ ->? _))) -> (_,) | (T,) | (#_ \ #a6))` and `q` = `((x0: false | (T,)) ->
    /// (_, _)) & ((x0: _ \ (int | f32 | f64 | rat | bool | String | (_ ->? _))) -> (T,) |
    /// (_,) | (#_ \ #a6))`, which fitted only with the first arrow of `s` tried first for
    /// the second of `q`. The cases up to 4 of that seed are run again, since the generator
    /// makes them.
    #[test]
    fn a_refused_arrow_tried_and_dropped_leaves_the_verdict_to_the_other_arrows() {
        let mut rng = Rng(158393);
        let mut counts = Counts::default();
        for case in 0..5 {
            wider_case(
                &mut rng,
                WIDER_SIZES[case % WIDER_SIZES.len()],
                case,
                &mut counts,
            );
        }
    }

    /// Every function type is a subtype of itself (subtyping is a preorder): for each arrow of
    /// `q` the same arrow of `s` takes its parameters and returns within its result, each type
    /// variable of `s` bound to the one of the same name in `q` (FAIL-types-sig-reflexive).
    /// `(x0: (T,) | (U,)) -> (T,)` was a plain false: the one-tuple `(U,)` of `q`'s parameter was
    /// found in the first one-tuple of `s`'s, `(T,)`, in written order, which binds `T` to `U`,
    /// and the result read so, `(U,)`, is not in `(T,)`. Arrow 18 of seed 250, case 4 of the
    /// generator of [`wider_case`],
    /// `(x0: (int | String,) | (T,) | (U,) | (int, #a2) | #a6) -> rat | (_, _) | (int, #a2) |
    /// #_`, was refused against itself by the cover rule ("would take part of `x0` only by
    /// binding its type variable there").
    #[test]
    fn a_signature_fits_itself() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let mut a = sig(
            vec![Arrow {
                params: vec![tup(v("T")).union(&tup(v("U")))],
                result: tup(v("T")),
                partial: false,
            }],
            1,
            false,
        );
        a.own.insert("U".into());
        a.note_held();
        assert!(fits_sig(&a, &a), "{a} in itself");
        assert_eq!(why_unfit(&a, &a), None, "{a} in itself");

        let mut rng = Rng(250);
        let mut input = None;
        for c in 0..=4 {
            input = Some(wider_input(&mut rng, WIDER_SIZES[c % WIDER_SIZES.len()]));
        }
        let (_, qas, width, qm, _) = input.unwrap();
        let q = sig_mask(vec![qas[18].clone()], width, qm);
        assert_eq!(why_unfit(&q, &q), None, "{q} in itself");
        assert!(fits_sig(&q, &q), "{q} in itself");
    }

    /// The signature of one parameter `x0: p` returning `r`, with `arrows` after it, its own
    /// variables `T`, `B` and `U`, `B` bounded by `int | f64` when `bounded`.
    fn one_param(p: Ty, r: Ty, more: &[Arrow], bounded: bool) -> Sig {
        let mut arrows = vec![Arrow {
            params: vec![p],
            result: r,
            partial: false,
        }];
        arrows.extend_from_slice(more);
        let mut s = sig(arrows, 1, bounded);
        s.own.insert("U".into());
        s.note_held();
        s
    }

    /// Neighbors of [`a_signature_fits_itself`]: with a bounded variable, whose variable in
    /// `q` is read under a new name, and with arrows that need no binding beside the one that
    /// does; and an overload passed where one of its arrows is expected, which takes its arrow
    /// of `s` equal to it ([`equal_fits`]).
    #[test]
    fn signatures_with_a_variable_bound_in_a_tuple_fit_themselves_and_their_overloads() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let tu = tup(v("T")).union(&tup(v("U")));
        let bu = tup(v("B")).union(&tup(v("U")));
        let string = Arrow {
            params: vec![Ty::carrier(Carrier::Str)],
            result: Ty::carrier(Carrier::Str),
            partial: false,
        };
        let int_to_u = Arrow {
            params: vec![Ty::carrier(Carrier::Int)],
            result: tup(v("U")),
            partial: false,
        };
        for a in [
            one_param(bu.clone(), tup(v("B")), &[], true),
            one_param(tu.clone(), tup(v("T")), &[int_to_u], false),
            one_param(
                tu.clone(),
                tup(v("U")),
                std::slice::from_ref(&string),
                false,
            ),
        ] {
            assert!(fits_sig(&a, &a), "{a} in itself");
            assert_eq!(why_unfit(&a, &a), None, "{a} in itself");
        }
        // A function type's domain is exact (FAIL-types-fn-param-exact-domain): the overload
        // takes `String`, which `one` does not, so it does not fit there, a plain no.
        let one = one_param(tu.clone(), tup(v("T")), &[], false);
        let both = one_param(tu.clone(), tup(v("T")), &[string], false);
        assert!(!fits_sig(&both, &one), "{one} in {both}");
        assert_eq!(why_unfit(&both, &one), None, "{one} in {both}");
    }

    /// What fits itself still does not fit a signature that takes more or returns less: a
    /// parameter that takes `(T,)` only where `(T,) | (U,)` is expected, a variable bounded
    /// by `int | f64` where an unbounded one is expected, and a result `(T,) | (U,)` where
    /// `(T,)` is expected.
    #[test]
    fn a_signature_does_not_fit_one_that_takes_more_or_returns_less() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let tu = tup(v("T")).union(&tup(v("U")));
        let bu = tup(v("B")).union(&tup(v("U")));
        let q = one_param(tu.clone(), tup(v("T")), &[], false);
        for s in [
            one_param(tup(v("T")), tup(v("T")), &[], false),
            one_param(bu, tup(v("B")), &[], true),
            one_param(tu.clone(), tu.clone(), &[], false),
        ] {
            assert!(!fits_sig(&s, &q), "{q} in {s}");
        }
    }

    /// An arrow that holds a variable of `s` and covers no arrow of `q` still takes keys at
    /// every binding: `(x0: (T,) | String) -> int` takes `String` whatever `T` is, so beside
    /// `(x0: int) -> int` it does not fit `(x0: int) -> int`, a function type's domain being
    /// exact (FAIL-types-fn-param-exact-domain). With `T` alone it takes `(T,)`, no key at
    /// `T = Never`, and fits.
    #[test]
    fn an_arrow_with_a_variable_that_covers_nothing_still_takes_its_keys() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let int = Ty::carrier(Carrier::Int);
        let string = Ty::carrier(Carrier::Str);
        let extra = |p: Ty| Arrow {
            params: vec![p],
            result: int.clone(),
            partial: false,
        };
        let q = one_param(int.clone(), int.clone(), &[], false);
        let s = one_param(
            int.clone(),
            int.clone(),
            &[extra(tup(v("T")).union(&string))],
            false,
        );
        assert!(!fits_sig(&s, &q), "{q} in {s}");
        let s = one_param(int.clone(), int.clone(), &[extra(tup(v("T")))], false);
        assert!(fits_sig(&s, &q), "{q} in {s}");
        // `B in int | f64` has no least instance; at `Never`, within each, it still takes
        // `String`, so every instance does.
        let s = one_param(
            int.clone(),
            int.clone(),
            &[extra(tup(v("B")).union(&string))],
            true,
        );
        assert!(!fits_sig(&s, &q), "{q} in {s}");
    }

    /// FAIL-types-bindable-arrow-permission. A function type's domain is exact (DESIGN
    /// sec:type_language), so `s` fits `q` only where every key `s` takes is one `q` takes; a
    /// call fixes a bounded variable to one carrier of its bound (sec:type_resolution rule 6).
    /// `(x0: (B,)) -> int` for `B in int | f64` takes `(int,)` at one instance and `(f64,)` at
    /// the other; `q = (x0: int) -> int` takes neither, so `s` does not fit. The permission took
    /// the arrow at `B = Never`, which takes no key, and the arrow covers no arrow of `q`, so
    /// nothing compared it again: `fits_sig` answered true.
    #[test]
    fn an_arrow_with_a_variable_of_several_carriers_takes_the_keys_of_each() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let int = Ty::carrier(Carrier::Int);
        let extra = |p: Ty| Arrow {
            params: vec![p],
            result: int.clone(),
            partial: false,
        };
        let q = one_param(int.clone(), int.clone(), &[], false);
        let s = one_param(int.clone(), int.clone(), &[extra(tup(v("B")))], true);
        assert!(!fits_sig(&s, &q), "{q} in {s}");
    }

    /// A bounded variable is fixed by a call to one whole carrier (rule 6), so an arrow of it is
    /// no instance within an arrow of `q` that takes a piece of the carrier: `B -> int` for `B
    /// in int | f64` is called at `int` and takes every `int`, not only `1`. The cover bound
    /// `B` to `1` and passed (FAIL-types-bindable-arrow-permission). At the whole carrier the
    /// instance is within: `B -> B` fits `int -> int`, at `B = int`.
    #[test]
    fn a_bounded_variable_is_an_instance_only_at_whole_carriers() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let int = Ty::carrier(Carrier::Int);
        let one = Ty::lit(&Value::int(1.into()));
        let s = one_param(tup(v("B")), int.clone(), &[], true);
        let q = one_param(tup(one.clone()), int.clone(), &[], false);
        assert!(!fits_sig(&s, &q), "{q} in {s}");
        let s = one_param(v("B"), int.clone(), &[], true);
        let q = one_param(one.clone(), int.clone(), &[], false);
        assert!(!fits_sig(&s, &q), "{q} in {s}");
        let s = one_param(v("B"), v("B"), &[], true);
        let q = one_param(int.clone(), int.clone(), &[], false);
        assert!(fits_sig(&s, &q), "{q} in {s}");
        let q = one_param(tup(int.clone()), int.clone(), &[], false);
        let s = one_param(tup(v("B")), int.clone(), &[], true);
        assert!(fits_sig(&s, &q), "{q} in {s}");
    }

    /// A row shared by two paths is read once, under the comparison's names, and stays shared
    /// (PERF-types-shared-tuple-vars): read once per path, `P(k) = (P(k-1), P(k-1))` became
    /// 2^(k+1) - 1 rows, each of a number of its own, and the comparisons after it, kept by
    /// those numbers, walked every path. A function a shared row holds is read as one new name.
    #[test]
    fn a_shared_row_is_read_once_under_the_comparison_s_names() {
        let int = Ty::carrier(Carrier::Int);
        let f = Ty::func(Arc::new(one_param(int.clone(), int, &[], false)));
        let p0 = Ty::tuple(vec![Ty::var("T".into()), f]);
        let p = Ty::tuple(vec![p0.clone(), p0]);
        let mut cx = Cx::default();
        let mut env = Env::new();
        env.insert("T".into(), Read::Rigid("T'1".into()));
        let read = cx.read(&p, &env);
        let row = read.tuples.iter().next().expect("one row");
        let cs = row.to_vec();
        let (a, b) = (cs[0].tuples.iter().next(), cs[1].tuples.iter().next());
        assert_eq!(a.map(Row::node), b.map(Row::node), "{read}");
        assert_eq!(cx.fns.len(), 1, "{read}");
        let mut vs = Vars::default();
        read.vars_in(&mut vs);
        assert!(vs.contains("T'1") && !vs.contains("T"), "{read}");
    }

    /// An overload with a bounded variable fits where one of its arrows is expected
    /// (FAIL-types-overload-bounded-tuple): `(x0: (B,) | (U,)) -> (B,)` for `B in int | f64`,
    /// with `(x0: String) -> String` beside it. The arrow of `q` is read with `B` under a new
    /// name, so no arrow of `s` is equal to it, and the comparison finds the piece `(U,)` of
    /// `q`'s parameter in the shapes of `s`'s. `(B,)`, the first in written order, held it
    /// by binding `B` to `U`, which its bound does not hold, and the search kept that shape;
    /// now `B` is bound only to what its bound holds, and `(U,)` is found in `(U,)`.
    ///
    /// A function type's domain is exact (FAIL-types-fn-param-exact-domain), so the overload
    /// fits where `q` takes `String` too: `q` here is the overload, and `s` is its two arrows in
    /// the other order, the same function (their keys do not meet) but not equal to `q` as
    /// written, so the comparison is made. Where `q` takes no `String`, `s` does not fit.
    #[test]
    fn an_overload_with_a_bounded_variable_fits_where_one_of_its_arrows_is_expected() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let bu = tup(v("B")).union(&tup(v("U")));
        let string = Arrow {
            params: vec![Ty::carrier(Carrier::Str)],
            result: Ty::carrier(Carrier::Str),
            partial: false,
        };
        let b_arrow = Arrow {
            params: vec![bu.clone()],
            result: tup(v("B")),
            partial: false,
        };
        let q = one_param(bu.clone(), tup(v("B")), std::slice::from_ref(&string), true);
        let s = one_param(
            string.params[0].clone(),
            string.result.clone(),
            &[b_arrow],
            true,
        );
        assert!(fits_sig(&s, &q), "{q} in {s}");
        assert_eq!(why_unfit(&s, &q), None, "{q} in {s}");
        let q = one_param(bu, tup(v("B")), &[], true);
        assert!(!fits_sig(&s, &q), "{q} in {s}");
        assert_eq!(why_unfit(&s, &q), None, "{q} in {s}");
    }

    /// `s` with its own variables `own` only, and the bound of `B` given to `to` instead.
    fn owning(mut s: Sig, own: &[&str], to: &str) -> Sig {
        s.own = own.iter().map(|&v| v.into()).collect();
        if let Some(m) = s.bounds.remove("B") {
            s.bounds.insert(to.into(), m);
        }
        s.note_held();
        s
    }

    /// Neighbors of [`an_overload_with_a_bounded_variable_fits_where_one_of_its_arrows_is_expected`]:
    /// a bounded variable is bound only to what its bound holds, so a piece its shape could
    /// hold only by such a binding is found in a later shape, under any name of the expected
    /// variables; and a binding the bound does hold is still made, and still checked against
    /// the result. The last pair is the signature that fits itself only as a whole
    /// ([`read_alike`]): its piece `(U,)` binds the unbounded `T` in `(T,)`.
    #[test]
    fn a_bounded_variable_is_bound_only_to_what_its_bound_holds() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let int = Ty::carrier(Carrier::Int);
        let string = Ty::carrier(Carrier::Str);
        let bu = tup(v("B")).union(&tup(v("U")));
        let bt = tup(v("B")).union(&tup(v("T")));
        let cw = tup(v("C")).union(&tup(v("W")));
        let btu = bt.union(&tup(v("U")));
        let strings = tup(int.clone()).union(&tup(string.clone()));
        let cases = [
            (
                one_param(bu.clone(), tup(v("B")), &[], true),
                owning(one_param(cw, tup(v("C")), &[], true), &["C", "W"], "C"),
                true,
            ),
            (
                one_param(tup(v("B")), tup(v("B")), &[], true),
                owning(one_param(tup(v("C")), tup(v("C")), &[], true), &["C"], "C"),
                true,
            ),
            (
                one_param(bt.clone(), tup(v("B")), &[], true),
                one_param(strings.clone(), tup(int.clone()), &[], false),
                true,
            ),
            // `B` stands for one carrier of its bound in each instance, so the instance that
            // takes `(String,)` at `(T,)` also takes `(int,)` or `(f64,)` at `(B,)`, which `q`
            // does not: a function type's domain is exact (FAIL-types-fn-param-exact-domain).
            (
                one_param(bt.clone(), tup(v("T")), &[], true),
                one_param(tup(string.clone()), tup(string.clone()), &[], false),
                false,
            ),
            (
                one_param(bt, tup(v("B")), &[], true),
                one_param(strings, tup(string), &[], false),
                false,
            ),
            (
                one_param(btu.clone(), tup(v("T")), &[], true),
                one_param(btu, tup(v("T")), &[], true),
                true,
            ),
        ];
        for (s, q, fits) in cases {
            assert_eq!(fits_sig(&s, &q), fits, "{q} in {s}");
            assert_eq!(why_unfit(&s, &q), None, "{q} in {s}");
        }
    }

    /// Bounded variables beside variables of an enclosing scope (`V`, not own), inside the
    /// function types a signature takes or returns, and beside class variables solved while
    /// comparing ([`fits_sig_with`]). The outer `V` is the same variable on both sides, and
    /// `B`, bound to the expected `B`, is not within it. A function type is compared as a
    /// signature of its own, with its own bounded variable read under a new name where the
    /// signature around it owns one of the same name, and checked against its bound under that
    /// name: `(x0: (B,)) -> (B,)` for `B in int | f64` does not fit `(x0: (String,)) -> (String,)`
    /// there either. A class variable reads as the type it is solved to, so `(C,)` holds
    /// `(String,)` where `C` is `String`, and not where it is `int`.
    #[test]
    fn bounded_variables_beside_outer_variables_function_types_and_class_variables() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let int = Ty::carrier(Carrier::Int);
        let string = Ty::carrier(Carrier::Str);
        let to_string = Arrow {
            params: vec![string.clone()],
            result: string.clone(),
            partial: false,
        };
        let bu = tup(v("B")).union(&tup(v("U")));
        let bv = tup(v("B")).union(&tup(v("V")));
        // `p -> r` after `String -> String`: the same function as `p -> r` with `String ->
        // String` after it, where `p` takes no `String`, but not equal to it as written, so the
        // comparison is made. A function type's domain is exact
        // (FAIL-types-fn-param-exact-domain), so an overload that takes `String` fits only
        // where `String` is expected too.
        let after_string = |p: Ty, r: Ty| {
            let arrow = Arrow {
                params: vec![p],
                result: r,
                partial: false,
            };
            one_param(string.clone(), string.clone(), &[arrow], true)
        };
        let outer = [
            (
                after_string(bv.clone(), tup(v("B"))),
                one_param(
                    bv.clone(),
                    tup(v("B")),
                    std::slice::from_ref(&to_string),
                    true,
                ),
                true,
            ),
            (
                after_string(bv.clone(), tup(v("B"))),
                one_param(bv.clone(), tup(v("B")), &[], true),
                false,
            ),
            (
                one_param(
                    bv.clone(),
                    tup(v("B")),
                    std::slice::from_ref(&to_string),
                    true,
                ),
                one_param(bv.clone(), tup(v("V")), &[], true),
                false,
            ),
        ];
        let func = |t: Sig| Ty::func(Arc::new(t));
        let inner = one_param(bu.clone(), tup(v("B")), &[], true);
        let inner_both = one_param(
            bu.clone(),
            tup(v("B")),
            std::slice::from_ref(&to_string),
            true,
        );
        let ints = one_param(tup(v("B")), tup(v("B")), &[], true);
        let strings = one_param(tup(string.clone()), tup(string.clone()), &[], false);
        let fns = [
            (
                one_param(
                    tup(v("B")),
                    func(after_string(bu.clone(), tup(v("B")))),
                    &[],
                    true,
                ),
                one_param(tup(v("B")), func(inner_both.clone()), &[], true),
                true,
            ),
            (
                one_param(tup(v("B")), func(inner_both.clone()), &[], true),
                one_param(tup(v("B")), func(inner.clone()), &[], true),
                false,
            ),
            (
                one_param(tup(v("B")), func(inner.clone()), &[], true),
                one_param(tup(v("B")), func(inner_both), &[], true),
                false,
            ),
            (
                one_param(tup(v("B")), func(ints.clone()), &[], true),
                one_param(tup(v("B")), func(strings.clone()), &[], true),
                false,
            ),
            (
                one_param(tup(v("T")), func(ints), &[], false),
                one_param(tup(v("T")), func(strings), &[], false),
                false,
            ),
            (
                after_string(func(inner.clone()), int.clone()),
                one_param(
                    func(inner.clone()),
                    int.clone(),
                    std::slice::from_ref(&to_string),
                    true,
                ),
                true,
            ),
            (
                after_string(func(inner.clone()), int.clone()),
                one_param(func(inner), int.clone(), &[], true),
                false,
            ),
        ];
        for (s, q, fits) in outer.into_iter().chain(fns) {
            assert_eq!(fits_sig(&s, &q), fits, "{q} in {s}");
            if fits {
                assert_eq!(why_unfit(&s, &q), None, "{q} in {s}");
            }
        }
        let bc = tup(v("B")).union(&tup(v("C")));
        let s = after_string(bc.clone(), tup(v("B")));
        let wants = one_param(bc, tup(v("B")), std::slice::from_ref(&to_string), true);
        let takes_string = one_param(
            tup(v("B")).union(&tup(string.clone())),
            tup(v("B")),
            std::slice::from_ref(&to_string),
            true,
        );
        for (c, q, fits) in [
            (string.clone(), &wants, true),
            (int.clone(), &wants, true),
            (string, &takes_string, true),
            (int, &takes_string, false),
        ] {
            let solve = |x: &str| (x == "C").then(|| c.clone());
            assert_eq!(fits_sig_with(&s, q, &solve), fits, "{q} in {s}, C = {c}");
            if fits {
                assert_eq!(why_unfit_with(&s, q, &solve), None, "{q} in {s}, C = {c}");
            }
        }
    }

    #[test]
    fn an_unbounded_variable_in_the_first_shape_does_not_take_every_piece() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let int = Ty::carrier(Carrier::Int);
        let one = Ty::lit(&Value::int(1.into()));
        let s = owning(
            one_param(tup(v("T")).union(&tup(v("U"))), tup(v("T")), &[], false),
            &["T", "U"],
            "T",
        );
        let q = owning(
            one_param(tup(v("X")).union(&tup(v("W"))), tup(v("X")), &[], false),
            &["X", "W"],
            "X",
        );
        assert!(fits_sig(&s, &q), "{q} in {s}");
        let s = owning(
            one_param(
                tup(v("T")).union(&tup(int.clone())),
                tup(v("T")),
                &[],
                false,
            ),
            &["T"],
            "T",
        );
        let q = owning(
            one_param(tup(v("U")).union(&tup(one)), tup(v("U")), &[], false),
            &["U"],
            "U",
        );
        assert!(fits_sig(&s, &q), "{q} in {s}");
        let s = owning(
            one_param(int.union(&v("T")), v("T"), &[], false),
            &["T"],
            "T",
        );
        let q = owning(one_param(int.clone(), int.clone(), &[], false), &[], "T");
        assert!(fits_sig(&s, &q), "{q} in {s}");
        // The members in the other order, and the variable returned bound to the second.
        let tx = |x: &str| tup(v(x));
        let s = owning(
            one_param(tx("T").union(&tx("U")), tx("T"), &[], false),
            &["T", "U"],
            "T",
        );
        let q = owning(
            one_param(tx("W").union(&tx("X")), tx("X"), &[], false),
            &["X", "W"],
            "X",
        );
        assert!(fits_sig(&s, &q), "{q} in {s}");
        let q = owning(
            one_param(tx("X").union(&tx("W")), tx("W"), &[], false),
            &["X", "W"],
            "X",
        );
        assert!(fits_sig(&s, &q), "{q} in {s}");
        // Neither variable may take `(String,)` where the result must be `(U,)`.
        let string = Ty::carrier(Carrier::Str);
        let s = owning(
            one_param(tx("T").union(&tup(int.clone())), tx("T"), &[], false),
            &["T"],
            "T",
        );
        let q = owning(
            one_param(tx("U").union(&tup(string.clone())), tx("U"), &[], false),
            &["U"],
            "U",
        );
        assert!(!fits_sig(&s, &q), "{q} in {s}");
        // A variable beside another in the result, each in a parameter of its own: the ceiling
        // of each is the place it stands at in `q`'s result.
        let pair = |a: &str, b: &str, k: &Ty| {
            let p = |x: &str| tx(x).union(&tup(k.clone()));
            let result = Ty::tuple(vec![v(a), v(b)]);
            let mut s = sig(
                vec![Arrow {
                    params: vec![p(a), p(b)],
                    result,
                    partial: false,
                }],
                2,
                false,
            );
            s.own = [a.into(), b.into()].into_iter().collect();
            s.note_held();
            s
        };
        let s = pair("T", "V", &int);
        for (q, fits) in [
            (pair("U", "W", &int), true),
            (pair("U", "W", &Ty::lit(&Value::int(1.into()))), true),
            (pair("U", "W", &string), false),
        ] {
            assert_eq!(fits_sig(&s, &q), fits, "{q} in {s}");
        }
        // Where a variable beside it is bound to `Never`, the tuple holds no value and the
        // ceiling does not hold: compared again first-fit, `T` takes `(String,)` and the
        // result `(String, Never)` is within any result.
        let mut s = one_param(
            tx("T").union(&tx("V")),
            Ty::tuple(vec![v("T"), v("V")]),
            &[],
            false,
        );
        s.own = ["T".into(), "V".into()].into_iter().collect();
        s.note_held();
        let q = one_param(tup(string), Ty::tuple(vec![int.clone(), int]), &[], false);
        let q = owning(q, &[], "T");
        assert!(fits_sig(&s, &q), "{q} in {s}");
    }

    #[test]
    fn a_union_of_three_shapes_of_variables_fits_itself_renamed() {
        let v = |x: &str| Ty::var(x.into());
        let tx = |x: &str| Ty::tuple(vec![v(x)]);
        let s = owning(
            one_param(tx("T").union(&tx("U")).union(&tx("V")), tx("T"), &[], false),
            &["T", "U", "V"],
            "T",
        );
        let q = owning(
            one_param(tx("X").union(&tx("W")).union(&tx("Y")), tx("X"), &[], false),
            &["X", "W", "Y"],
            "X",
        );
        assert!(fits_sig(&s, &q), "{q} in {s}");
        // Control: two shapes fit (FAIL-types-first-shape-unbounded).
        let s = owning(
            one_param(tx("T").union(&tx("U")), tx("T"), &[], false),
            &["T", "U"],
            "T",
        );
        let q = owning(
            one_param(tx("X").union(&tx("W")), tx("X"), &[], false),
            &["X", "W"],
            "X",
        );
        assert!(fits_sig(&s, &q), "{q} in {s}");
    }

    /// Why `fits_sig(s, q)` was refused, if a member needed a shape of a bucket past one failed
    /// fit after another member had ([`Comparing::search`]).
    fn sig_unchosen(s: &Sig, q: &Sig) -> Option<String> {
        let env = Env::new();
        let mut cx = Cx::default();
        comparing!(&mut cx, |c| async {
            fits_in(s, &env, q, &env, &c).await;
        });
        cx.unchosen
    }

    /// `fits_sig(s, q)`, checked against the search of every shape in written order
    /// (`SCAN_ALL`): the same verdict, and no refusal.
    fn fits_both(s: &Sig, q: &Sig) -> bool {
        let ok = fits_sig(s, q);
        SCAN_ALL.set(true);
        let want = fits_sig(s, q);
        SCAN_ALL.set(false);
        assert_eq!(ok, want, "{q} in {s}: the index and the full search differ");
        assert_eq!(sig_unchosen(s, q), None, "{q} in {s}: refused");
        ok
    }

    /// The tuple of the variables `names`.
    fn vars_tuple(names: &[&str]) -> Ty {
        Ty::tuple(names.iter().map(|&x| Ty::var(x.into())).collect())
    }

    /// `(x0: (T0,) | … | (Tn-1,)) -> (T0,)` fits itself renamed to `X0 … Xn-1`, for `n` from 1
    /// to 8: each member after the first is found in its shape by its own name ([`Pins`]),
    /// which FAIL-types-three-variable-shapes refused from three shapes on.
    #[test]
    fn n_shapes_of_variables_fit_themselves_renamed() {
        for n in 1..=8 {
            let ts: Vec<String> = (0..n).map(|i| format!("T{i}")).collect();
            let xs: Vec<String> = (0..n).map(|i| format!("X{i}")).collect();
            let make = |names: &[String]| {
                let p = Ty::union_all(&names.iter().map(|x| vars_tuple(&[x])).collect::<Vec<_>>());
                let own: Vec<&str> = names.iter().map(String::as_str).collect();
                owning(
                    one_param(p, vars_tuple(&[&names[0]]), &[], false),
                    &own,
                    "B",
                )
            };
            let (s, q) = (make(&ts), make(&xs));
            assert!(fits_both(&s, &q), "{q} in {s}");
        }
    }

    /// Pinned and free shapes in one bucket: in `(x0: (T, int) | (U, int) | (V, int)) -> (T,)`
    /// only `T` has a ceiling, so `(T, int)` is pinned and the other two are free; and with the
    /// result `(T, U, V)` all three are pinned, each by its own variable.
    #[test]
    fn pinned_and_free_shapes_of_one_bucket_fit_themselves_renamed() {
        let int = Ty::carrier(Carrier::Int);
        let with_int = |x: &str| Ty::tuple(vec![Ty::var(x.into()), int.clone()]);
        let make = |names: [&str; 3], r: Ty| {
            let p = Ty::union_all(&names.map(with_int));
            owning(one_param(p, r, &[], false), &names, "B")
        };
        let s = make(["T", "U", "V"], vars_tuple(&["T"]));
        let q = make(["X", "W", "Y"], vars_tuple(&["X"]));
        assert!(fits_both(&s, &q), "{q} in {s}");
        let s = make(["T", "U", "V"], vars_tuple(&["T", "U", "V"]));
        let q = make(["X", "W", "Y"], vars_tuple(&["X", "W", "Y"]));
        assert!(fits_both(&s, &q), "{q} in {s}");
        // The result names the variables in another order: `T`'s ceiling is `W` and `U`'s is
        // `X`, so `T` takes `W`'s member and `U` takes `X`'s, and the result `(U, T, V)` is
        // `(X, W, Y)`.
        let s = make(["T", "U", "V"], vars_tuple(&["U", "T", "V"]));
        assert!(fits_both(&s, &q), "{q} in {s}");
        // A result that names `T` twice still fits, with `T` bound to nothing and `U` taking
        // both `X`'s and `W`'s members: the result is then empty.
        let s = make(["T", "U", "V"], vars_tuple(&["T", "T", "V"]));
        assert!(fits_both(&s, &q), "{q} in {s}");
        // A fourth member `(Z, int)` is within no ceiling, so the attempt within the ceilings
        // fails; with no ceiling the first shape takes every member, `T` is `X | W | Y | Z` and
        // `U` and `V` are bound to nothing, so the result is empty and within any.
        let s = make(["T", "U", "V"], vars_tuple(&["T", "U", "V"]));
        let p = Ty::union_all(&["X", "W", "Y", "Z"].map(with_int));
        let q = owning(
            one_param(p, vars_tuple(&["X", "W", "Y"]), &[], false),
            &["X", "W", "Y", "Z"],
            "B",
        );
        assert!(fits_both(&s, &q), "{q} in {s}");
    }

    /// Two shapes where three members need three: `(x0: (T, int) | (U, bool)) -> (T, U)` is not
    /// a function of type `(x0: (X, int) | (W, bool) | (Y, bool)) -> (X, W)`, as its `U` would
    /// be `W | Y`, which the result `W` does not hold; with the result `(X, W | Y)` it is.
    #[test]
    fn shapes_that_take_more_members_than_the_result_holds_do_not_fit() {
        let (int, bool) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool));
        let at = |x: &str, c: &Ty| Ty::tuple(vec![Ty::var(x.into()), c.clone()]);
        let s = owning(
            one_param(
                at("T", &int).union(&at("U", &bool)),
                vars_tuple(&["T", "U"]),
                &[],
                false,
            ),
            &["T", "U"],
            "B",
        );
        let p = at("X", &int).union(&at("W", &bool)).union(&at("Y", &bool));
        let q = owning(
            one_param(p.clone(), vars_tuple(&["X", "W"]), &[], false),
            &["X", "W", "Y"],
            "B",
        );
        assert!(!fits_both(&s, &q), "{q} in {s}");
        let wy = Ty::var("W".into()).union(&Ty::var("Y".into()));
        let r = Ty::tuple(vec![Ty::var("X".into()), wy]);
        let q = owning(one_param(p, r, &[], false), &["X", "W", "Y"], "B");
        assert!(fits_both(&s, &q), "{q} in {s}");
    }

    /// Shapes that share a variable: `(x0: (T, int) | (T, bool)) -> (T,)` takes `(X, int)` and
    /// `(W, bool)` only with `T` bound to `X | W`, so it is not a function of type
    /// `(x0: (X, int) | (W, bool)) -> (X,)`, and is one of type `… -> (X | W,)`. Both shapes are
    /// pinned at `T`, filed under the variable `X` of its ceiling.
    #[test]
    fn shapes_that_share_a_variable_take_the_union_of_their_members() {
        let (int, bool) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool));
        let at = |x: &str, c: &Ty| Ty::tuple(vec![Ty::var(x.into()), c.clone()]);
        let s = owning(
            one_param(
                at("T", &int).union(&at("T", &bool)),
                vars_tuple(&["T"]),
                &[],
                false,
            ),
            &["T"],
            "B",
        );
        let p = at("X", &int).union(&at("W", &bool));
        let q = owning(
            one_param(p.clone(), vars_tuple(&["X"]), &[], false),
            &["X", "W"],
            "B",
        );
        assert!(!fits_both(&s, &q), "{q} in {s}");
        let xw = Ty::tuple(vec![Ty::var("X".into()).union(&Ty::var("W".into()))]);
        let q = owning(one_param(p, xw, &[], false), &["X", "W"], "B");
        assert!(fits_both(&s, &q), "{q} in {s}");
    }

    /// A random component of a shape for [`pinned_shapes_are_those_of_the_rule_of_one_shape`]:
    /// one of the variables `names`, now and then with `int` beside it, `int`, `Bool`, a
    /// literal of two, or the tuple `(int,)`, which has neither a variable nor a scalar.
    fn sig_component(rng: &mut Rng, names: &[&str]) -> Ty {
        let var = |rng: &mut Rng| Ty::var(names[rng.below(names.len() as u64) as usize].into());
        match rng.below(8) {
            0..=2 => var(rng),
            3 => var(rng).union(&Ty::carrier(Carrier::Int)),
            4 => Ty::carrier(Carrier::Int),
            5 => Ty::carrier(Carrier::Bool),
            6 => Ty::lit(&Value::Int(rng.below(2) as i64)),
            _ => Ty::tuple(vec![Ty::carrier(Carrier::Int)]),
        }
    }

    /// The members of a random parameter: one to five tuples of one or two components.
    fn sig_members(rng: &mut Rng, names: &[&str]) -> Vec<Vec<Ty>> {
        (0..1 + rng.below(5))
            .map(|_| {
                (0..1 + rng.below(2))
                    .map(|_| sig_component(rng, names))
                    .collect()
            })
            .collect()
    }

    /// `(x0: members) -> result`, each a union of the tuples of the components given, with its own
    /// variables `names`.
    fn random_shapes_sig(names: &[&str], members: &[Vec<Ty>], result: &[Vec<Ty>]) -> Sig {
        let p = Ty::union_all(
            &members
                .iter()
                .map(|m| Ty::tuple(m.clone()))
                .collect::<Vec<_>>(),
        );
        let r = Ty::union_all(
            &result
                .iter()
                .map(|m| Ty::tuple(m.clone()))
                .collect::<Vec<_>>(),
        );
        owning(one_param(p, r, &[], false), names, "B")
    }

    /// The components `cs` with each variable `from[i]` renamed `to[i]`: each component is one
    /// variable, a variable with `int` beside it ([`sig_result`]), or has no variable.
    fn renamed(cs: &[Vec<Ty>], from: &[&str], to: &[&str]) -> Vec<Vec<Ty>> {
        let int = Ty::carrier(Carrier::Int);
        let name = |t: &Ty| {
            let Some(v) = t.vars.iter().next() else {
                return t.clone();
            };
            let new = Ty::var(to[from.iter().position(|f| **f == **v).unwrap()].into());
            match t.as_var() {
                Some(_) => new,
                None => {
                    assert_eq!(*t, Ty::var(v.clone()).union(&int));
                    new.union(&int)
                }
            }
        };
        cs.iter().map(|m| m.iter().map(name).collect()).collect()
    }

    /// Members of scalar values are not tried against a shape pinned by a ceiling of
    /// variables only: in `(x0: (T,) | (U,) | (int,)) -> (T, T)` compared with
    /// `(x0: (Y,) | (int,) | (1,) | (X,)) -> (X, X)`, `T`'s ceiling is `X`, so `(int,)` and `(1,)`
    /// go to `(U,)` without failing `(T,)`. Tried there, each failed `(T,)`, and the second was
    /// refused; the attempt with no ceiling then failed and its false was taken as the verdict,
    /// though the rule of one shape finds the fit. Both are fixed: the lookup leaves `(T,)` out,
    /// and a refusal within the ceilings is kept where the attempt with no ceiling fails
    /// ([`arrow_fits`]).
    #[test]
    fn scalar_members_skip_shapes_pinned_by_ceilings_of_variables() {
        let v = |x: &str| vec![Ty::var(x.into())];
        let vv = |x: &str| vec![vec![Ty::var(x.into()), Ty::var(x.into())]];
        let int = vec![Ty::carrier(Carrier::Int)];
        let one = vec![Ty::lit(&Value::Int(1))];
        let s = random_shapes_sig(&["T", "U"], &[v("T"), v("U"), int.clone()], &vv("T"));
        let q = random_shapes_sig(&["X", "Y"], &[v("Y"), int, one, v("X")], &vv("X"));
        assert!(fits_both(&s, &q), "{q} in {s}");
    }

    /// A case the search still gives up (F124), from the sweep below: `(x0: (bool, T) | (int | T,)
    /// | (int | T, T) | (U,) | (V,)) -> (T,) | (T, T)` compared with itself renamed, members
    /// shuffled. Three of its shapes are pinned by no ceiling: `(int | T,)`, whose component is
    /// not one variable, and `(U,)` and `(V,)`, whose variables have none; the search gives the
    /// comparison up, though every shape tried in order finds the fit. Kept so that a change
    /// that decides it shows here.
    #[test]
    fn a_signature_the_pins_do_not_separate_is_still_refused() {
        let v = |x: &str| Ty::var(x.into());
        let (int, bool) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::Bool));
        let make = |t: &str, u: &str, w: &str, order: [usize; 5]| {
            let shapes = [
                vec![bool.clone(), v(t)],
                vec![v(t).union(&int)],
                vec![v(t).union(&int), v(t)],
                vec![v(u)],
                vec![v(w)],
            ];
            let members: Vec<Vec<Ty>> = order.iter().map(|&i| shapes[i].clone()).collect();
            random_shapes_sig(&[t, u, w], &members, &[vec![v(t)], vec![v(t), v(t)]])
        };
        let s = make("T", "U", "V", [0, 1, 2, 3, 4]);
        let q = make("X", "W", "Y", [1, 2, 3, 0, 4]);
        assert!(!fits_sig(&s, &q), "{q} in {s}");
        assert!(sig_unchosen(&s, &q).is_some(), "{q} in {s}: not refused");
        SCAN_ALL.set(true);
        let want = fits_sig(&s, &q);
        SCAN_ALL.set(false);
        assert!(want, "{q} in {s}: the full search finds no fit");
    }

    /// The result of a random signature for [`pinned_shapes_are_those_of_the_rule_of_one_shape`]:
    /// one or two tuples of one or two of the variables `names`, now and then with `int` beside
    /// one, so that some ceilings hold scalars (the shapes `open` of [`Pins`]).
    fn sig_result(rng: &mut Rng, names: &[&str]) -> Vec<Vec<Ty>> {
        let one = |rng: &mut Rng| {
            let v = Ty::var(names[rng.below(names.len() as u64) as usize].into());
            match rng.below(4) {
                0 => v.union(&Ty::carrier(Carrier::Int)),
                _ => v,
            }
        };
        (0..1 + rng.below(2))
            .map(|_| (0..1 + rng.below(2)).map(|_| one(rng)).collect())
            .collect()
    }

    /// The members pinned to their shapes by the ceilings ([`Pins`]) are matched as the rule of
    /// one shape matches them, trying every shape in written order (`SCAN_ALL`): the same
    /// verdict on random signatures of tuple shapes wherever the comparison is not refused.
    /// Half the cases compare a signature with itself renamed, members shuffled and one
    /// component changed now and then, so that many hold. The count of refusals is printed:
    /// each is a case given up (see [`Comparing::search`]).
    #[test]
    fn pinned_shapes_are_those_of_the_rule_of_one_shape() {
        let mut rng = Rng(crate::seed::seed(
            "pinned_shapes_are_those_of_the_rule_of_one_shape",
        ));
        let (ts, xs) = (["T", "U", "V"], ["X", "W", "Y"]);
        built_shape_verdicts(&ts, &xs, &|s, _| s);
        let (mut cases, mut held, mut failed, mut refused) = (0, 0, 0, 0);
        for i in 0..3000 {
            let sm = sig_members(&mut rng, &ts);
            let sr = sig_result(&mut rng, &ts);
            let s = random_shapes_sig(&ts, &sm, &sr);
            let (mut qm, qr) = if i % 2 == 0 {
                let mut qm = renamed(&sm, &ts, &xs);
                for k in (1..qm.len()).rev() {
                    qm.swap(k, rng.below(k as u64 + 1) as usize);
                }
                (qm, renamed(&sr, &ts, &xs))
            } else {
                let qr = sig_result(&mut rng, &xs);
                (sig_members(&mut rng, &xs), qr)
            };
            if rng.below(4) == 0 {
                let m = rng.below(qm.len() as u64) as usize;
                let j = rng.below(qm[m].len() as u64) as usize;
                qm[m][j] = sig_component(&mut rng, &xs);
            }
            let q = random_shapes_sig(&xs, &qm, &qr);
            cases += 1;
            match one_shape_agrees(&s, &q) {
                Some(true) => held += 1,
                Some(false) => failed += 1,
                None => refused += 1,
            }
        }
        println!("{cases} cases: {held} held, {failed} failed, {refused} refused");
    }

    /// `q` in `s` by the pins and by the rule of one shape (`SCAN_ALL`): the same verdict,
    /// given as `Some`, wherever the comparison is not refused, and no fit where it is (`None`).
    fn one_shape_agrees(s: &Sig, q: &Sig) -> Option<bool> {
        let ok = fits_sig(s, q);
        SCAN_ALL.set(true);
        let want = fits_sig(s, q);
        SCAN_ALL.set(false);
        if sig_unchosen(s, q).is_some() {
            assert!(!ok, "{q} in {s}: refused, but held");
            return None;
        }
        assert_eq!(ok, want, "{q} in {s}");
        Some(ok)
    }

    /// Both verdicts of [`one_shape_agrees`] on built signatures of the variables `ts` and
    /// `xs`, each made by `make` (which may bound them), so that the comparison could fail
    /// either way on every run. `(x0: (T,)) -> (T,)` holds itself renamed `X`. It does not hold
    /// `(x0: (X,) | (W,)) -> (X,)`, which takes `(W,)` too: `s` would have to take every
    /// value of `(W,)` for each `W`, but it takes only `(T,)` and returns `(T,)` for it, so a
    /// value of `(W,)` with `W` apart from `X` gets no result of `(X,)`.
    fn built_shape_verdicts(ts: &[&str], xs: &[&str], make: &dyn Fn(Sig, &[&str]) -> Sig) {
        let v = |x: &str| vec![Ty::var(x.into())];
        let s = make(random_shapes_sig(ts, &[v(ts[0])], &[v(ts[0])]), ts);
        let same = make(random_shapes_sig(xs, &[v(xs[0])], &[v(xs[0])]), xs);
        let more = make(
            random_shapes_sig(xs, &[v(xs[0]), v(xs[1])], &[v(xs[0])]),
            xs,
        );
        assert_eq!(one_shape_agrees(&s, &same), Some(true), "{same} in {s}");
        assert_eq!(one_shape_agrees(&s, &more), Some(false), "{more} in {s}");
    }

    /// The members found or passed by the pins of the bindings ([`Bound`]) are matched as the
    /// rule of one shape matches them, trying every shape in written order (`SCAN_ALL`): on
    /// random signatures of tuple shapes whose own variables are all bounded to several
    /// carriers, half compared with themselves renamed and shuffled, the result `int` (no
    /// ceilings) or random, the same verdict wherever not refused, and no refusal where it
    /// holds. Then `n` shapes `(T_i,)` of such variables fit themselves renamed and shuffled,
    /// which FAIL-types-bounded-shapes-renamed-refused refused from three shapes on.
    #[test]
    fn bound_shapes_agree_with_trying_every_shape() {
        let mut rng = Rng(crate::seed::seed(
            "bound_shapes_agree_with_trying_every_shape",
        ));
        let (ts, xs) = (["T", "U", "V"], ["X", "W", "Y"]);
        let bounded = |mut s: Sig, names: &[&str]| {
            s.bounds = names.iter().map(|&v| (v.into(), EVERY)).collect();
            s.note_held();
            s
        };
        let int = vec![vec![Ty::carrier(Carrier::Int)]];
        built_shape_verdicts(&ts, &xs, &bounded);
        let (mut held, mut failed, mut refused) = (0, 0, 0);
        for i in 0..3000 {
            let sm = sig_members(&mut rng, &ts);
            let sr = match rng.below(2) {
                0 => int.clone(),
                _ => sig_result(&mut rng, &ts),
            };
            let (qm, qr) = if i % 2 == 0 {
                let mut qm = renamed(&sm, &ts, &xs);
                for k in (1..qm.len()).rev() {
                    qm.swap(k, rng.below(k as u64 + 1) as usize);
                }
                (qm, renamed(&sr, &ts, &xs))
            } else {
                (sig_members(&mut rng, &xs), int.clone())
            };
            let s = bounded(random_shapes_sig(&ts, &sm, &sr), &ts);
            let q = bounded(random_shapes_sig(&xs, &qm, &qr), &xs);
            match one_shape_agrees(&s, &q) {
                Some(true) => held += 1,
                Some(false) => failed += 1,
                None => refused += 1,
            }
        }
        println!("{held} held, {failed} failed, {refused} refused");
        for n in 1..=8 {
            let names: Vec<String> = (0..n).map(|i| format!("T{i}")).collect();
            let renames: Vec<String> = (0..n).map(|i| format!("X{i}")).collect();
            let make = |names: &[String], order: &[usize]| {
                let own: Vec<&str> = names.iter().map(String::as_str).collect();
                let members: Vec<Vec<Ty>> = (order.iter())
                    .map(|&i| vec![Ty::var(own[i].into())])
                    .collect();
                bounded(random_shapes_sig(&own, &members, &int), &own)
            };
            let mut order: Vec<usize> = (0..n).collect();
            let s = make(&names, &order);
            for k in (1..n).rev() {
                order.swap(k, rng.below(k as u64 + 1) as usize);
            }
            let q = make(&renames, &order);
            assert!(fits_both(&s, &q), "{q} in {s}");
        }
    }

    #[test]
    fn own_variables_of_the_same_name_on_both_sides_are_apart() {
        let v = |x: &str| Ty::var(x.into());
        let int = Ty::carrier(Carrier::Int);
        let s = owning(one_param(v("T"), v("T"), &[], false), &["T"], "T");
        for name in ["T", "U"] {
            let q = owning(
                one_param(v(name).union(&int), int.clone(), &[], false),
                &[name],
                name,
            );
            assert!(!fits_sig(&s, &q), "{q} in {s}");
        }
        // Controls: the same signature with its own `T`, and the one carrier it may return.
        let same = owning(one_param(v("T"), v("T"), &[], false), &["T"], "T");
        assert!(fits_sig(&s, &same), "{same} in {s}");
        let ints = owning(one_param(int.clone(), int.clone(), &[], false), &[], "T");
        assert!(fits_sig(&s, &ints), "{ints} in {s}");
        // A bounded own `B` of `s` against an unbounded own `B` of `q`: given `(String,)`, `s`
        // returns a `(B,)` of `int | f64`, not the `(String,)` `q` returns.
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let s = one_param(tup(v("B")).union(&tup(v("U"))), tup(v("B")), &[], true);
        let q = owning(one_param(tup(v("B")), tup(v("B")), &[], false), &["B"], "B");
        assert!(!fits_sig(&s, &q), "{q} in {s}");
    }

    #[test]
    fn a_variable_in_a_payload_is_read_as_elsewhere() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let p = |t: Ty| Ty::atom_of("p", vec![t], BTreeMap::new());
        let s = owning(one_param(p(v("B")), tup(v("B")), &[], true), &["B"], "B");
        let q = owning(one_param(p(v("C")), tup(v("C")), &[], true), &["C"], "C");
        assert!(fits_sig(&s, &q), "{q} in {s}");
        // Unbounded own variables in payloads are apart too: a piece `#p(T)` of `q` is not held
        // by the `T` of `s` by its name (FAIL-types-own-same-name by a payload).
        let int = Ty::carrier(Carrier::Int);
        let s = owning(one_param(p(v("T")), v("T"), &[], false), &["T"], "T");
        let q = owning(
            one_param(p(v("T")).union(&p(int.clone())), int.clone(), &[], false),
            &["T"],
            "T",
        );
        assert!(!fits_sig(&s, &q), "{q} in {s}");
        let q = owning(one_param(p(int.clone()), int, &[], false), &[], "T");
        assert!(fits_sig(&s, &q), "{q} in {s}");
        // A bounded variable in a payload against an unbounded one: `s` returns `(B,)` of
        // `int | f64`, not the `(C,)` of any `C` that `q` returns.
        let s = owning(one_param(p(v("B")), tup(v("B")), &[], true), &["B"], "B");
        let q = owning(one_param(p(v("C")), tup(v("C")), &[], false), &["C"], "C");
        assert!(!fits_sig(&s, &q), "{q} in {s}");
    }

    /// A bound that holds [`OTHER`] (written `_`) holds a piece of no carrier: the tuple
    /// `(int,)` binds `B` in the first shape `(B,)`, where without `OTHER` it is held only by
    /// `(U,)`, and the result `(B,)` then holds nothing of it. And a variable of several
    /// carriers beside a tuple is refused even by such a bound ([`piece_within`]): `V` of
    /// `for V in int | f64` stands for one carrier, so `V | (int,)` given to `B` stands for one
    /// carrier and something else at once, which `B`, one type at a call, is not.
    #[test]
    fn a_bound_that_holds_other_values_takes_a_tuple_but_not_beside_a_variable_of_carriers() {
        let v = |x: &str| Ty::var(x.into());
        let tup = |t: Ty| Ty::tuple(vec![t]);
        let int = Ty::carrier(Carrier::Int);
        let bounded = |m: u8, p: Ty, r: Ty| {
            let mut s = one_param(p, r, &[], true);
            s.bounds.insert("B".into(), m);
            s
        };
        let q = sig(
            vec![Arrow {
                params: vec![tup(tup(int.clone()))],
                result: tup(tup(int.clone())),
                partial: false,
            }],
            1,
            false,
        );
        let bu = tup(v("B")).union(&tup(v("U")));
        let s = bounded(B_MASK | OTHER, bu.clone(), tup(v("B")));
        assert!(fits_sig(&s, &q), "{q} in {s}");
        assert_eq!(why_unfit(&s, &q), None, "{q} in {s}");
        let s = bounded(B_MASK, bu, tup(v("B")));
        assert!(!fits_sig(&s, &q), "{q} in {s}");
        let s = bounded(B_MASK | OTHER, v("B"), int.clone());
        let q = owning(
            one_param(v("V").union(&tup(int.clone())), int, &[], true),
            &["V"],
            "V",
        );
        assert!(!fits_sig(&s, &q), "{q} in {s}");
    }

    /// A refusal with no arrow left that fits refuses the whole comparison, and the same
    /// comparison with an arrow added to `s` that takes the parameters of `q` and returns none
    /// is decided with no refusal. Seed 59, case 0, arrow 0 of `q`: the one arrow of `s` would
    /// take part of the parameter only by binding its variable. Seed 41, case 0, arrow 0: it
    /// takes a part of more than one parameter. Seed 24, case 3, arrow 0: no arrow alone is
    /// refused, the cover of the arrows together is. The arrow added takes `q`'s parameters
    /// and no more: a function type's domain is exact (sec:type_resolution, `K -> V`), so an
    /// arrow that takes every value (the `(_) -> Never` this test added before
    /// FAIL-types-fn-param-exact-domain) makes `s` take keys `q` does not, and `s` does not
    /// fit. Found by a sweep of seeds 0 to 299, cases 0 to 4, of the generator of
    /// [`wider_case`], each arrow of `q` that `s` was refused at (2026-11-15); one of each kind
    /// of refusal, the smallest. The arrow added is not the arrow of `q` itself, which would
    /// fit as the arrow equal to it with no comparison ([`equal_fits`]) and test nothing of
    /// the refusal.
    #[test]
    fn a_refusal_with_no_arrow_that_fits_refuses_the_comparison() {
        // The last field: whether `q` takes every value, so that `(_) -> Never` added to `s`
        // takes no key `q` does not (seed 24, `(x0: _) -> f64`).
        for (seed, case, arrow, q_takes_all) in
            [(59, 0, 0, false), (41, 0, 0, false), (24, 3, 0, true)]
        {
            let mut rng = Rng(seed);
            let mut input = None;
            for c in 0..=case {
                input = Some(wider_input(&mut rng, WIDER_SIZES[c % WIDER_SIZES.len()]));
            }
            let (s, qas, width, qm, _) = input.unwrap();
            let q = sig_mask(vec![qas[arrow].clone()], width, qm);
            let what = format!("seed {seed}, case {case}, arrow {arrow}: {q} in {s}");
            assert!(!fits_sig(&s, &q), "{what}");
            assert!(why_unfit(&s, &q).is_some(), "{what}: refused");
            let mut t = s.clone();
            t.arrows.push(Arrow {
                params: qas[arrow].params.clone(),
                result: Ty::empty(),
                partial: false,
            });
            t.note_held();
            let added = "with an arrow from q's parameters to Never added to s";
            assert!(fits_sig(&t, &q), "{what}, {added}");
            assert_eq!(why_unfit(&t, &q), None, "{what}, {added}");
            // Taking every value instead, `s` takes keys `q` does not, a plain no.
            let mut u = s.clone();
            u.arrows.push(Arrow {
                params: vec![Ty::set(KType::top()); width],
                result: Ty::empty(),
                partial: false,
            });
            u.note_held();
            let every = "with `(_) -> Never` added to s";
            assert_eq!(fits_sig(&u, &q), q_takes_all, "{what}, {every}");
            assert_eq!(why_unfit(&u, &q), None, "{what}, {every}");
        }
    }

    /// The values of the small types below, one for each class no type of them splits: `int`,
    /// `bool`, `String`, `f64` and the atoms `#v0` to `#v2`, a bit each.
    const VALUES: usize = 7;

    /// The type of the values of the mask `m`.
    fn of_values(m: u8) -> Ty {
        let carriers = [Carrier::Int, Carrier::Bool, Carrier::Str, Carrier::F64];
        (0..VALUES)
            .filter(|&b| m & (1 << b) != 0)
            .fold(Ty::empty(), |t, b| match carriers.get(b) {
                Some(&c) => t.union(&Ty::carrier(c)),
                None => t.union(&Ty::set(KType::atom(&format!("v{}", b - carriers.len())))),
            })
    }

    /// The bits of `int` and `f64`, the bound of `B` below.
    const B_VALUES: u8 = 0b1001;

    /// A place of a small arrow: the values of a mask, alone or with the variable `B` bounded by
    /// `int | f64`.
    #[derive(Clone, Copy)]
    enum Small {
        Values(u8),
        B(u8),
    }

    impl Small {
        fn ty(self) -> Ty {
            match self {
                Small::Values(m) => of_values(m),
                Small::B(m) => Ty::var("B".into()).union(&of_values(m)),
            }
        }

        /// The mask at `B` fixed to the carrier of the bit `c`.
        fn at(self, c: u8) -> u8 {
            match self {
                Small::Values(m) => m,
                Small::B(m) => m | c,
            }
        }
    }

    /// Whether arrows of the places `arrows` cover the arrow of masks `params -> result` as
    /// rule 6 of sec:type_resolution types a call, by the values: at each value of the
    /// parameters, some arrow takes it, and the intersection of the results of every arrow
    /// that takes it is within `result`. An arrow that holds `B` is each arrow it is at a
    /// carrier of its bound ([`Sig::expand`]).
    fn covers_by_values(arrows: &[(Vec<Small>, Small)], params: &[u8], result: u8) -> bool {
        let fixed: Vec<(Vec<u8>, u8)> = arrows
            .iter()
            .flat_map(|(ps, r)| {
                let held = ps.iter().chain([r]).any(|p| matches!(p, Small::B(_)));
                let cs: Vec<u8> = match held {
                    true => (0..VALUES)
                        .map(|b| 1 << b)
                        .filter(|c| B_VALUES & c != 0)
                        .collect(),
                    false => vec![0],
                };
                cs.into_iter()
                    .map(move |c| (ps.iter().map(|p| p.at(c)).collect(), r.at(c)))
            })
            .collect();
        // Every value of the parameters, one bit at each.
        let mut values: Vec<Vec<u8>> = vec![Vec::new()];
        for &m in params {
            values = values
                .into_iter()
                .flat_map(|v| {
                    (0..VALUES)
                        .filter(move |&b| m & (1 << b) != 0)
                        .map(move |b| {
                            let mut v = v.clone();
                            v.push(1 << b);
                            v
                        })
                })
                .collect();
        }
        values.iter().all(|v| {
            let mut met: Option<u8> = None;
            for (ps, r) in &fixed {
                if ps.iter().zip(v).all(|(p, x)| p & x != 0) {
                    met = Some(met.map_or(*r, |m| m & r));
                }
            }
            met.is_some_and(|m| m & !result == 0)
        })
    }

    /// A random mask of [`VALUES`], not empty.
    fn mask(rng: &mut Rng) -> u8 {
        loop {
            let m = rng.below(1 << VALUES) as u8;
            if m != 0 {
                break m;
            }
        }
    }

    /// `B` one time in eight, else the values of a random mask; when `narrow`, of the meet of
    /// two and one of the first three values, so that results outside a slot's are common.
    fn small(rng: &mut Rng, narrow: bool) -> Small {
        if rng.below(8) == 0 {
            return Small::B(0);
        }
        Small::Values(match narrow {
            true => mask(rng) & mask(rng) | 1 << rng.below(3),
            false => mask(rng),
        })
    }

    #[test]
    fn a_fit_of_small_types_is_a_cover_of_their_values() {
        // Over random overloads of one or two parameters whose types are unions of the values
        // of [`VALUES`], some arrows with `B`: every fit `fits_sig` gives holds at every value,
        // as rule 6 types a call there, whether by one arrow, by a union at one parameter or
        // by the intersection of results ([`covered`]). The checker refuses some covers
        // (cases (1) to (3) of [`covered`]), so a cover it does not take is counted, not
        // asserted, and the counts show each form of fit occurs.
        let mut rng = Rng(crate::seed::seed(
            "a_fit_of_small_types_is_a_cover_of_their_values",
        ));
        // Each kind on a built case, on every run. `int`, `bool` and `String` are the bits 1, 2
        // and 4. `(int) -> int` holds `(x0: int) -> int` by its one arrow. `(int) -> int`
        // beside `(bool) -> int` holds `(x0: int | bool) -> int` only together: each value of
        // `int | bool` is taken by one arrow, which returns `int`, and neither arrow takes
        // both. `(int) -> int` alone takes no `bool`, so it holds no `(x0: bool) -> int`.
        let v = Small::Values;
        let int_to_int = vec![(vec![v(1)], v(1))];
        let two = vec![(vec![v(1)], v(1)), (vec![v(2)], v(1))];
        let built = [
            (&int_to_int, 1, Cover::Fit),
            (&two, 0b11, Cover::Together),
            (&int_to_int, 2, Cover::Neither),
        ];
        for (case, (arrows, param, kind)) in built.into_iter().enumerate() {
            let got = small_cover(arrows, &[param], 1, &format!("built case {case}"));
            assert_eq!(got, kind, "built case {case}");
        }
        let (mut fit, mut cover, mut refused, mut neither) = (0, 0, 0, 0);
        for case in 0..2000 {
            let width = 1 + case % 2;
            let n = 1 + rng.below(4) as usize;
            let mut arrows: Vec<(Vec<Small>, Small)> = Vec::new();
            for _ in 0..n {
                let ps = (0..width).map(|_| small(&mut rng, false)).collect();
                arrows.push((ps, small(&mut rng, true)));
            }
            let params: Vec<u8> = (0..width)
                .map(|_| (mask(&mut rng) & mask(&mut rng)).max(1))
                .collect();
            let result = mask(&mut rng) | 1 << rng.below(3);
            match small_cover(&arrows, &params, result, &format!("case {case}")) {
                Cover::Fit => fit += 1,
                Cover::Together | Cover::ByFns => cover += 1,
                Cover::Refused => refused += 1,
                Cover::Neither => neither += 1,
            }
        }
        println!("{fit} fit by one arrow, {cover} together, {refused} refused, {neither} no cover");
    }

    /// How a fit of one arrow in an overload compares with a cover by the values.
    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Cover {
        /// A fit by one arrow ([`Reference::Pairs`]).
        Fit,
        /// A fit by the arrows together.
        Together,
        /// A fit by the arrows together, with functions or `T` in their results.
        ByFns,
        /// A cover the checker does not take.
        Refused,
        /// No fit and no cover.
        Neither,
    }

    /// `(x0: params) -> result` in the overload `arrows` of [`Small`] places, `B` bounded by
    /// `int | f64`: the kind of verdict, after asserting that a fit is a cover by the values.
    fn small_cover(arrows: &[(Vec<Small>, Small)], params: &[u8], result: u8, what: &str) -> Cover {
        let width = params.len();
        let sas = arrows
            .iter()
            .map(|(ps, r)| Arrow {
                params: ps.iter().map(|p| p.ty()).collect(),
                result: r.ty(),
                partial: false,
            })
            .collect();
        let mut s = sig(sas, width, false);
        s.bounds
            .insert("B".into(), Carrier::Int.bit() | Carrier::F64.bit());
        s.note_held();
        let qa = Arrow {
            params: params.iter().map(|&m| of_values(m)).collect(),
            result: of_values(result),
            partial: false,
        };
        let q = sig(vec![qa], width, false);
        let truth = covers_by_values(arrows, params, result);
        let pairs = {
            REFERENCE.set(Reference::Pairs);
            let v = fits_sig(&s, &q);
            REFERENCE.set(Reference::None);
            v
        };
        match (fits_sig(&s, &q), truth) {
            (true, false) => panic!("{what}: {q} in {s} is no cover of the values"),
            (true, true) if pairs => Cover::Fit,
            (true, true) => Cover::Together,
            (false, true) => Cover::Refused,
            (false, false) => Cover::Neither,
        }
    }

    #[test]
    fn a_fit_at_a_bounded_variable_is_a_cover_of_its_values() {
        // As above, with the slot generic: `U`, bounded by `int | f64`, stands at some of its
        // parameters and in its result, and the arrows hold `B`, alone or with other values,
        // at parameters and in results, so a result may hold the rigid `U` (by `B` bound to
        // it) beside values ([`meet_within`]). A fit holds at each carrier the caller may fix
        // `U` to, at every value, as rule 6 types a call there, and the verdict is the same in
        // every order of the arrows.
        let mut rng = Rng(crate::seed::seed(
            "a_fit_at_a_bounded_variable_is_a_cover_of_its_values",
        ));
        let (mut fit, mut refused, mut neither) = (0, 0, 0);
        let place = |rng: &mut Rng, narrow: bool| match small(rng, narrow) {
            Small::B(_) if narrow && rng.below(2) == 0 => Small::B(1 << rng.below(VALUES as u64)),
            p => p,
        };
        for case in 0..1200 {
            let width = 1 + case % 2;
            let n = 1 + rng.below(4) as usize;
            let mut arrows: Vec<(Vec<Small>, Small)> = Vec::new();
            for _ in 0..n {
                let ps = (0..width).map(|_| place(&mut rng, false)).collect();
                arrows.push((ps, place(&mut rng, true)));
            }
            // A slot's place: `U`, alone or with values, one time in three, else values.
            let slot = |rng: &mut Rng, m: u8| match rng.below(3) {
                0 => (true, m & mask(rng) & mask(rng)),
                _ => (false, m.max(1)),
            };
            let params: Vec<(bool, u8)> = (0..width)
                .map(|_| {
                    let m = mask(&mut rng) & mask(&mut rng);
                    slot(&mut rng, m)
                })
                .collect();
            let m = mask(&mut rng) | 1 << rng.below(3);
            let result = slot(&mut rng, m);
            match bounded_cover(
                &arrows,
                &params,
                result,
                case as u64,
                &format!("case {case}"),
            ) {
                Cover::Neither => neither += 1,
                Cover::Refused => refused += 1,
                _ => fit += 1,
            }
        }
        println!("{fit} fit, {refused} refused, {neither} no cover");
    }

    #[test]
    fn a_fit_at_a_bounded_variable_has_each_verdict_on_built_cases() {
        // Both verdicts of [`bounded_cover`], whatever the draws of the test above. `(B) -> B`
        // holds `(x0: U) -> U`: at each carrier the caller fixes `U` to, `int` or `f64`, `B`
        // bound to it takes the value and returns it. It holds no `(x0: bool) -> int`, since
        // `B` is bounded by `int | f64` and takes no `bool` (bit 2).
        let b = vec![(vec![Small::B(0)], Small::B(0))];
        let got = bounded_cover(&b, &[(true, 0)], (true, 0), 0, "built fit");
        assert_eq!(got, Cover::Fit, "built fit");
        let got = bounded_cover(&b, &[(false, 2)], (false, 1), 0, "built no fit");
        assert_eq!(got, Cover::Neither, "built no fit");
    }

    /// `(x0: params) -> result` in the overload `arrows`, each place of the arrow `U` bounded
    /// by `int | f64` with the values of a mask, or the mask alone: the kind of verdict, after
    /// asserting that a fit holds at each carrier the caller may fix `U` to, at every value,
    /// and that the verdict is the same in every order of the arrows. Every fit is
    /// [`Cover::Fit`]: the test does not tell fits by one arrow from fits together.
    fn bounded_cover(
        arrows: &[(Vec<Small>, Small)],
        params: &[(bool, u8)],
        result: (bool, u8),
        seed: u64,
        what: &str,
    ) -> Cover {
        let width = params.len();
        let u = |(held, m): (bool, u8)| match held {
            true => Ty::var("U".into()).union(&of_values(m)),
            false => of_values(m),
        };
        let sas = arrows
            .iter()
            .map(|(ps, r)| Arrow {
                params: ps.iter().map(|p| p.ty()).collect(),
                result: r.ty(),
                partial: false,
            })
            .collect();
        let mut s = sig(sas, width, false);
        s.bounds
            .insert("B".into(), Carrier::Int.bit() | Carrier::F64.bit());
        s.note_held();
        let qa = Arrow {
            params: params.iter().map(|&p| u(p)).collect(),
            result: u(result),
            partial: false,
        };
        let mut q = sig(vec![qa], width, false);
        q.own.insert("U".into());
        q.bounds
            .insert("U".into(), Carrier::Int.bit() | Carrier::F64.bit());
        q.note_held();
        let at = |(held, m): (bool, u8), c: u8| if held { m | c } else { m };
        // `U` that no parameter holds is no carrier a caller fixes: it is read as its bound.
        let fixed: &[u8] = match params.iter().any(|&(held, _)| held) {
            true => &[1, 1 << 3],
            false => &[1 | 1 << 3],
        };
        let truth = fixed.iter().all(|&c| {
            let ps: Vec<u8> = params.iter().map(|&p| at(p, c)).collect();
            covers_by_values(arrows, &ps, at(result, c))
        });
        let kind = match (fits_sig(&s, &q), truth) {
            (true, false) => panic!("{what}: {q} in {s} is no cover of the values"),
            (true, true) => Cover::Fit,
            (false, true) => Cover::Refused,
            (false, false) => Cover::Neither,
        };
        same_in_every_order(&s, &q, seed, what);
        kind
    }

    /// The values of the types of [`Place`]: `int`, `bool`, `String`, `f64`, the atoms `#v0` and
    /// `#v1`, a function of `(x0: int) -> #v0` alone, one of `(x0: int) -> #v1` alone, and one
    /// of both (it returns no value), a bit each.
    const FN_VALUES: usize = 9;

    /// A place of an arrow over [`FN_VALUES`]: the values of a mask of the first six, the
    /// function types `(x0: int) -> #v0` and `(x0: int) -> #v1`, and the own unbounded variable
    /// `T` of the arrow's signature, which a comparison binds to the slot's type there.
    #[derive(Clone, Copy, Default)]
    struct Place {
        m: u8,
        f1: bool,
        f2: bool,
        t: bool,
    }

    impl Place {
        /// The function type returning `#v<i>`.
        fn f(i: usize) -> Ty {
            let a = Arrow {
                params: vec![Ty::carrier(Carrier::Int)],
                result: Ty::set(KType::atom(&format!("v{i}"))),
                partial: false,
            };
            Ty::func(Arc::new(sig(vec![a], 1, false)))
        }

        fn ty(self) -> Ty {
            let carriers = [Carrier::Int, Carrier::Bool, Carrier::Str, Carrier::F64];
            let mut t = (0..6)
                .filter(|&b| self.m & (1 << b) != 0)
                .fold(Ty::empty(), |t, b| match carriers.get(b) {
                    Some(&c) => t.union(&Ty::carrier(c)),
                    None => t.union(&Ty::set(KType::atom(&format!("v{}", b - 4)))),
                });
            for (held, i) in [(self.f1, 0), (self.f2, 1)] {
                if held {
                    t = t.union(&Place::f(i));
                }
            }
            if self.t {
                t = t.union(&Ty::var("T".into()));
            }
            t
        }

        /// Its values but those of `T`.
        fn values(self) -> u16 {
            let mut v = u16::from(self.m);
            if self.f1 {
                v |= 1 << 6 | 1 << 8;
            }
            if self.f2 {
                v |= 1 << 7 | 1 << 8;
            }
            v
        }

        /// A random place of values, not empty: functions one time in `f` each.
        fn random(rng: &mut Rng, narrow: bool, f: u64) -> Place {
            let m = match narrow {
                true => (rng.below(64) & rng.below(64)) as u8,
                false => rng.below(64) as u8,
            };
            let mut p = Place {
                m,
                f1: rng.below(f) == 0,
                f2: rng.below(f) == 0,
                t: false,
            };
            if p.values() == 0 {
                p.m = 1 << rng.below(6);
            }
            p
        }
    }

    /// [`covers_by_values`] over [`FN_VALUES`]: at each value of the parameters, some arrow
    /// takes it, and the intersection of the results of every arrow that takes it is within
    /// `result`. `T`, alone at a parameter, takes every value there, and in the result stands
    /// for the value it took: what an arrow generic in `T` returns at it.
    fn covers_with_fns(arrows: &[(Vec<Place>, Place)], params: &[u16], result: u16) -> bool {
        let mut values: Vec<Vec<u16>> = vec![Vec::new()];
        for &m in params {
            values = values
                .into_iter()
                .flat_map(|v| {
                    (0..FN_VALUES)
                        .filter(move |&b| m & (1 << b) != 0)
                        .map(move |b| {
                            let mut v = v.clone();
                            v.push(1 << b);
                            v
                        })
                })
                .collect();
        }
        values.iter().all(|v| {
            let mut met: Option<u16> = None;
            for (ps, r) in arrows {
                if ps.iter().zip(v).all(|(p, &x)| p.t || p.values() & x != 0) {
                    let at_t = ps.iter().zip(v).find(|(p, _)| p.t).map_or(0, |(_, &x)| x);
                    let r = r.values() | if r.t { at_t } else { 0 };
                    met = Some(met.map_or(r, |m| m & r));
                }
            }
            met.is_some_and(|m| m & !result == 0)
        })
    }

    #[test]
    fn a_fit_with_functions_in_the_results_is_a_cover_of_their_values() {
        // As above, with two function types among the values, at parameters and in results,
        // and arrows generic in their own unbounded `T`, alone at a parameter, so a result
        // holds the slot's functions by `T` bound to them ([`meet_within`]): a function piece
        // is left out of the intersection only where another result holds no function. Each
        // fit holds at every value, and the verdict is the same in every order of the arrows.
        let mut rng = Rng(crate::seed::seed(
            "a_fit_with_functions_in_the_results_is_a_cover_of_their_values",
        ));
        let (mut fit, mut cover, mut by_fns, mut refused, mut neither) = (0, 0, 0, 0, 0);
        for case in 0..600 {
            let width = 1 + case % 2;
            let n = 2 + rng.below(3) as usize;
            let mut arrows: Vec<(Vec<Place>, Place)> = Vec::new();
            for _ in 0..n {
                let tj = (rng.below(3) == 0).then(|| rng.below(width as u64) as usize);
                let ps = (0..width)
                    .map(|j| match tj == Some(j) {
                        true => Place {
                            t: true,
                            ..Place::default()
                        },
                        false => Place::random(&mut rng, false, 3),
                    })
                    .collect();
                let mut r = Place::random(&mut rng, true, 2);
                r.t = tj.is_some() && rng.below(2) == 0;
                arrows.push((ps, r));
            }
            let params: Vec<Place> = (0..width)
                .map(|_| Place::random(&mut rng, true, 3))
                .collect();
            let mut result = Place::random(&mut rng, false, 3);
            result.m |= 1 << rng.below(3);
            match fn_cover(
                &arrows,
                &params,
                result,
                case as u64,
                &format!("case {case}"),
            ) {
                Cover::Fit => fit += 1,
                Cover::ByFns => by_fns += 1,
                Cover::Together => cover += 1,
                Cover::Refused => refused += 1,
                Cover::Neither => neither += 1,
            }
        }
        println!(
            "{fit} fit by one arrow, {cover} together, {by_fns} together with functions in \
             the results, {refused} refused, {neither} no cover"
        );
    }

    #[test]
    fn a_fit_with_functions_in_the_results_has_each_verdict_on_built_cases() {
        // Each kind of [`fn_cover`], whatever the draws of the test above; `int` is bit 1,
        // `bool` bit 2 and `String` bit 4, and `f1` the function returning `#v0`.
        // `(int) -> int` holds `(x0: int) -> int` by one arrow. `(int) -> int | f1` beside
        // `(int) -> bool | f1` holds `(x0: int) -> f1` only together: both take every `int`,
        // and the intersection of their results is `f1`; neither result alone is within `f1`.
        // `(int) -> int` holds no `(x0: bool) -> int`: it takes no `bool`.
        let p = |m: u8, f1: bool| Place {
            m,
            f1,
            ..Place::default()
        };
        let fit = fn_cover(
            &[(vec![p(1, false)], p(1, false))],
            &[p(1, false)],
            p(1, false),
            0,
            "built fit",
        );
        assert_eq!(fit, Cover::Fit, "built fit");
        let by_fns = fn_cover(
            &[
                (vec![p(1, false)], p(1, true)),
                (vec![p(1, false)], p(2, true)),
            ],
            &[p(1, false)],
            p(0, true),
            0,
            "built fit with functions",
        );
        assert_eq!(by_fns, Cover::ByFns, "built fit with functions");
        let neither = fn_cover(
            &[(vec![p(1, false)], p(1, false))],
            &[p(2, false)],
            p(1, false),
            0,
            "built no fit",
        );
        assert_eq!(neither, Cover::Neither, "built no fit");
    }

    /// `(x0: params) -> result` in the overload `arrows` of [`Place`]s: the kind of verdict,
    /// after asserting that a fit is a cover by the values and that the verdict is the same in
    /// every order of the arrows.
    fn fn_cover(
        arrows: &[(Vec<Place>, Place)],
        params: &[Place],
        result: Place,
        seed: u64,
        what: &str,
    ) -> Cover {
        let width = params.len();
        let sas = arrows
            .iter()
            .map(|(ps, r)| Arrow {
                params: ps.iter().map(|p| p.ty()).collect(),
                result: r.ty(),
                partial: false,
            })
            .collect();
        let s = sig(sas, width, false);
        let qa = Arrow {
            params: params.iter().map(|p| p.ty()).collect(),
            result: result.ty(),
            partial: false,
        };
        let q = sig(vec![qa], width, false);
        let ps: Vec<u16> = params.iter().map(|p| p.values()).collect();
        let truth = covers_with_fns(arrows, &ps, result.values());
        let pairs = {
            REFERENCE.set(Reference::Pairs);
            let v = fits_sig(&s, &q);
            REFERENCE.set(Reference::None);
            v
        };
        let fns_met = arrows.iter().any(|(_, r)| r.f1 || r.f2 || r.t);
        let kind = match (fits_sig(&s, &q), truth) {
            (true, false) => panic!("{what}: {q} in {s} is no cover of the values"),
            (true, true) if pairs => Cover::Fit,
            (true, true) if fns_met => Cover::ByFns,
            (true, true) => Cover::Together,
            (false, true) => Cover::Refused,
            (false, false) => Cover::Neither,
        };
        same_in_every_order(&s, &q, seed, what);
        kind
    }

    /// A row shared by two shapes of a union, and nested inside the first, gives its variables
    /// where a recursive walk first meets it, inside the first shape, not after it.
    #[test]
    fn vars_in_gives_a_shared_row_s_variables_where_it_first_appears() {
        let shared = Row::new(vec![Ty::var("$5".into())]);
        let first = Ty::tuple(vec![
            Ty::tuple(vec![Ty::of_row(shared.clone())]),
            Ty::var("$7".into()),
        ]);
        let t = first.union(&Ty::of_row(shared));
        let mut vars = Vars::default();
        t.vars_in(&mut vars);
        let order: Vec<&str> = vars.order.iter().map(|v| &**v).collect();
        assert_eq!(order, ["$5", "$7"]);
    }

    /// The variables of `t` in order, as [`Ty::vars_in`] gives them.
    fn order_of(t: &Ty) -> Vec<String> {
        let mut vars = Vars::default();
        t.vars_in(&mut vars);
        vars.order.iter().map(|v| v.to_string()).collect()
    }

    /// A function held at two places, and inside another, gives its variables where a walk
    /// of its arrows would first meet them, after the variables met before it, and each once,
    /// whether it is entered or gives the order it keeps; only a signature asked for its order
    /// keeps one, so a walk leaves none on the functions it meets (FAIL-returned-chain-quadratic).
    #[test]
    fn vars_in_gives_a_held_function_s_variables_where_it_first_appears() {
        let v = |n: &str| Ty::var(n.into());
        let f = Arc::new(Sig::one(vec![], vec![], Ty::tuple(vec![v("B"), v("A")])));
        let g = Arc::new(Sig::one(
            vec![],
            vec![],
            Ty::tuple(vec![Ty::func(f.clone()), v("C")]),
        ));
        let t = Ty::tuple(vec![
            v("A"),
            Ty::func(g.clone()),
            Ty::func(f.clone()),
            v("D"),
        ]);
        assert_eq!(order_of(&t), ["A", "B", "C", "D"]);
        assert_eq!(g.vars_order(), ["B", "A", "C"].map(Arc::<str>::from));
        let u = Ty::tuple(vec![v("C"), Ty::func(g), v("A")]);
        assert_eq!(order_of(&u), ["C", "B", "A"]);
        assert!(
            f.facts.4.get().is_none(),
            "a function only met keeps no order"
        );
    }

    /// A function holds needs when it, or a function returned at the top of a result at any
    /// depth below it, has needs; a type holds needs when such a function lies in it or in a
    /// tuple in it at any depth, not in a tuple a result holds. Asked from either end of a
    /// nest, each level gives the same answer (FAIL-power-returned-n-deep-ratio).
    #[test]
    fn a_function_holds_needs_when_one_returned_at_any_depth_has_them() {
        let int = || Ty::carrier(Carrier::Int);
        let need = || Need {
            on: Ty::var("A".into()),
            kind: NeedKind::Index(int()),
            result: None,
            span: Span { start: 0, end: 1 },
        };
        // `n` functions, each returning the one below; the one at depth `at` has needs.
        let nest = |n: usize, at: usize| {
            let mut out: Vec<Arc<Sig>> = Vec::new();
            let mut result = int();
            for d in (0..n).rev() {
                let mut s = Sig::one(vec![], vec![int()], result);
                if d == at {
                    s.needs = vec![need()];
                }
                let s = Arc::new(s);
                result = Ty::func(s.clone());
                out.push(s);
            }
            out.reverse();
            out
        };
        for at in [0, 3, 5, 99] {
            for outermost_first in [true, false] {
                let sigs = nest(6, at);
                let mut order: Vec<usize> = (0..6).collect();
                if !outermost_first {
                    order.reverse();
                }
                for d in order {
                    assert_eq!(
                        sigs[d].holds_needs(),
                        d <= at && at < 6,
                        "at {at}, depth {d}"
                    );
                }
            }
        }
        let with_needs = nest(2, 1)[1].clone();
        let in_tuples = Ty::tuple(vec![int(), Ty::tuple(vec![Ty::func(with_needs.clone())])]);
        assert!(in_tuples.may_hold_needs());
        assert!(!Ty::tuple(vec![int(), Ty::tuple(vec![int()])]).may_hold_needs());
        // A function returning a tuple that holds one with needs: not by its own results'
        // functions, but a value it returns may hold one; so may a payload or a function
        // returning such a payload, `hz` and `h5` of REDUCE-identity-escaping-values.
        let returns_a_tuple = Arc::new(Sig::one(vec![], vec![], in_tuples.clone()));
        assert!(!returns_a_tuple.holds_needs());
        assert!(returns_a_tuple.may_hold_needs());
        assert!(Ty::func(returns_a_tuple.clone()).may_hold_needs());
        let in_payload = Ty::atom_of("a", vec![int(), in_tuples], BTreeMap::new());
        assert!(in_payload.may_hold_needs());
        let returns_payload = Arc::new(Sig::one(vec![], vec![], in_payload));
        let returns_returns = Arc::new(Sig::one(vec![], vec![], Ty::func(returns_payload)));
        assert!(Ty::tuple(vec![Ty::func(returns_returns)]).may_hold_needs());
        let plain = Ty::atom_of("a", vec![int()], BTreeMap::new());
        let returns_plain = Arc::new(Sig::one(vec![], vec![int()], plain.clone()));
        assert!(!Ty::tuple(vec![plain, Ty::func(returns_plain)]).may_hold_needs());
        // A part that does not say what it holds: the unknown, a type variable, `(..)`, and a
        // payload not known, each in a tuple or a result.
        let unknown_payload = {
            let mut t = Ty::atom_of("b", vec![int()], BTreeMap::new());
            t.payloads.insert("b".into(), None);
            t
        };
        for open in [
            Ty::dynamic(),
            Ty::var("A".into()),
            Ty::set(wide()),
            unknown_payload,
        ] {
            assert!(Ty::tuple(vec![int(), open.clone()]).may_hold_needs());
            let returns = Arc::new(Sig::one(vec![], vec![], open));
            assert!(Ty::func(returns.clone()).may_hold_needs());
            assert!(!returns.holds_needs());
        }
    }

    /// A signature holds no variable exactly when its order of variables is empty, for nests
    /// of functions that hold a variable at the top, at the bottom, in a row or in none, asked
    /// from the outermost in or the innermost out, and a nest asked from the outermost in is
    /// answered at each level without keeping an order (FAIL-l01-26-deep-bench-bytes).
    #[test]
    fn a_signature_holds_no_variable_exactly_when_its_order_is_empty() {
        /// `n` functions, each returning the one below; the innermost returns `bottom`, and
        /// the one at depth `at` takes `extra` as well.
        fn nest(n: usize, bottom: Ty, at: usize, extra: Ty) -> Vec<Arc<Sig>> {
            let mut out: Vec<Arc<Sig>> = Vec::new();
            let mut result = bottom;
            for d in (0..n).rev() {
                let params = if d == at { vec![extra.clone()] } else { vec![] };
                let s = Arc::new(Sig::one(vec![], params, result));
                result = Ty::func(s.clone());
                out.push(s);
            }
            out.reverse();
            out
        }
        let int = || Ty::carrier(Carrier::Int);
        let in_row = Ty::tuple(vec![int(), Ty::var("R".into())]);
        let cases = [
            (int(), 99, int()),
            (Ty::var("B".into()), 99, int()),
            (int(), 0, Ty::var("T".into())),
            (int(), 3, in_row),
        ];
        for (bottom, at, extra) in cases {
            for outermost_first in [true, false] {
                let sigs = nest(6, bottom.clone(), at, extra.clone());
                let mut asked: Vec<&Arc<Sig>> = sigs.iter().collect();
                if !outermost_first {
                    asked.reverse();
                }
                let answers: Vec<bool> = asked.iter().map(|s| s.holds_no_variable()).collect();
                assert!(sigs.iter().all(|s| s.facts.4.get().is_none()));
                let fresh = nest(6, bottom.clone(), at, extra.clone());
                let mut want: Vec<bool> = fresh.iter().map(|s| s.vars_order().is_empty()).collect();
                if !outermost_first {
                    want.reverse();
                }
                assert_eq!(answers, want, "bottom {bottom:?}, at {at}");
            }
        }
    }

    /// Signatures renamed and replaced through one [`Renamings`] are those `renamed` and then
    /// `replace` give, and two given the same maps share the function they both hold.
    #[test]
    fn renamings_share_a_function_two_signatures_hold() {
        let v = |n: &str| Ty::var(n.into());
        let f = Arc::new(Sig::one(vec![], vec![], Ty::tuple(vec![v("$1"), v("$2")])));
        let s1 = Arc::new(Sig::one(vec![], vec![], Ty::func(f.clone())));
        let s2 = Arc::new(Sig::one(
            vec![],
            vec![],
            Ty::tuple(vec![Ty::func(f), v("$2")]),
        ));
        let to: Binds = [("$1".into(), v("T"))].into();
        let b: Binds = [("$2".into(), Ty::set(KType::int()))].into();
        let mut made = Renamings::default();
        let o1 = made.renamed_replaced(&s1, to.clone(), b.clone());
        let o2 = made.renamed_replaced(&s2, to.clone(), b.clone());
        assert_eq!(*o1, s1.renamed(&to).replace(&b));
        assert_eq!(*o2, s2.renamed(&to).replace(&b));
        let held1 = &o1.arrows[0].result.fns[0];
        let row = &o2.arrows[0].result.tuples[0];
        let held2 = &row.iter().next().expect("a row of two").fns[0];
        assert!(
            Arc::ptr_eq(held1, held2),
            "the shared function is made once"
        );
        let other: Binds = [("$1".into(), v("U"))].into();
        let o3 = made.renamed_replaced(&s1, other.clone(), b.clone());
        assert_eq!(*o3, s1.renamed(&other).replace(&b));
    }

    /// The atom `#a` with `inner` as its one payload component.
    fn atom_of(inner: Ty) -> Ty {
        let mut t = Ty::set(KType::atom_with("a", &KType::top()));
        (t.payloads).insert(
            "a".into(),
            Some(vec![Shape::new(vec![inner], BTreeMap::new())]),
        );
        t
    }

    /// A tuple whose first component is an atom whose payload holds `inner`, the second `int`.
    fn row_of_atom(inner: Ty) -> Ty {
        Ty::tuple(vec![atom_of(inner), Ty::set(KType::int())])
    }

    /// A variable or the unknown in an atom's payload, inside a tuple, is held by the tuple at
    /// any depth, as one in a component is (ATOM-payload-open): the row is open, the type is
    /// not closed and has no kernel type, and a walk outside functions reaches the variable.
    #[test]
    fn a_variable_in_a_payload_inside_a_tuple_is_held_by_the_tuple() {
        let x: Arc<str> = "$3".into();
        for t in [
            row_of_atom(Ty::var(x.clone())),
            row_of_atom(row_of_atom(Ty::var(x.clone()))),
        ] {
            assert!(t.tuples[0].open(), "{t}");
            assert!(!t.tuples[0].dynamic(), "{t}");
            assert!(!t.closed(), "{t}");
            assert!(t.kernel().is_none(), "{t}");
            let mut vars = Vars::default();
            t.vars_outside(&mut vars);
            assert_eq!(vars.order, std::slice::from_ref(&x), "{t}");
            let int = Ty::set(KType::int());
            let binds: Binds = [(x.clone(), int.clone())].into_iter().collect();
            for done in [
                t.replace_outside(&binds),
                t.settle(&|v| (v == &*x).then(|| int.clone())),
            ] {
                assert!(done.closed(), "{done}");
                assert!(done.var_facts().classes.is_empty(), "{done}");
            }
        }
        let unknown = row_of_atom(Ty::dynamic());
        assert!(
            unknown.tuples[0].open() && unknown.tuples[0].dynamic(),
            "{unknown}"
        );
        assert!(!unknown.closed() && unknown.kernel().is_none(), "{unknown}");
        let data = row_of_atom(Ty::set(KType::int()));
        assert!(!data.tuples[0].open() && data.closed() && data.kernel().is_some());
    }

    /// One [`Vars`] read over several types, each dropped before the next is made, finds the
    /// variables of each: a row or payload shape made after one is dropped may take its
    /// address, so the rows and shapes entered are kept by number (PTR-keys-ty).
    #[test]
    fn variables_of_types_made_after_others_are_dropped_are_all_found() {
        for (what, make) in [
            (
                "a tuple",
                (|x| Ty::tuple(vec![Ty::var(x)])) as fn(Arc<str>) -> Ty,
            ),
            ("a payload", |x| atom_of(Ty::var(x))),
        ] {
            let mut vars = Vars::default();
            let names: Vec<Arc<str>> = (0..64).map(|i| format!("$x{i}").into()).collect();
            for x in &names {
                make(x.clone()).vars_outside(&mut vars);
            }
            assert_eq!(vars.order, names, "{what}");
        }
    }

    /// A function in a payload is held at any depth, so the type has no kernel type.
    #[test]
    fn a_function_in_a_payload_leaves_no_kernel_type() {
        let s = Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::set(KType::int())));
        assert!(atom_of(Ty::func(s.clone())).kernel().is_none());
        assert!(row_of_atom(Ty::func(s)).kernel().is_none());
    }

    /// A random component of a shape: a literal of three, `int`, `String`, a tuple of a
    /// literal and a component, or, when `open`, the variable `T` or `U`.
    fn component(rng: &mut Rng, open: bool, depth: u32) -> Ty {
        match rng.below(if open { 8 } else { 6 }) {
            0..=2 => Ty::lit(&Value::Int(rng.below(3) as i64)),
            3 => Ty::carrier(Carrier::Int),
            4 => Ty::carrier(Carrier::Str),
            5 if depth > 0 => Ty::carrier(Carrier::Int),
            5 => Ty::tuple(vec![
                Ty::lit(&Value::Int(rng.below(2) as i64)),
                component(rng, open, depth + 1),
            ]),
            6 => Ty::var("T".into()),
            _ => Ty::var("U".into()),
        }
    }

    /// A union of one to four random members of width two: tuples, or payloads of the atom
    /// `#p`.
    fn shapes(rng: &mut Rng, open: bool, payloads: bool) -> Ty {
        let k = 1 + rng.below(4);
        let mut ms = Vec::new();
        for _ in 0..k {
            let cs = vec![component(rng, open, 0), component(rng, open, 0)];
            ms.push(match payloads {
                false => Ty::tuple(cs),
                true => {
                    let mut t = Ty::set(KType::atom_with("p", &KType::top()));
                    let shape = Shape::new(cs, BTreeMap::new());
                    t.payloads.insert("p".into(), Some(vec![shape]));
                    t
                }
            });
        }
        Ty::union_all(&ms)
    }

    /// The shapes found through the index (COMPLEXITY.md F124) are those the rule of one shape
    /// finds by trying every shape in written order: the same verdict and the same bindings
    /// wherever the index does not refuse.
    #[test]
    fn shapes_found_by_the_index_are_those_of_the_rule_of_one_shape() {
        let mut rng = Rng(crate::seed::seed(
            "shapes_found_by_the_index_are_those_of_the_rule_of_one_shape",
        ));
        // A built case that holds by binding, whatever the draws: `(int, int)` is in
        // `(T, int) | (String, String)` by its first shape with `T` bound to `int`; the second
        // shape takes no `int`.
        let int = Ty::carrier(Carrier::Int);
        let s = Ty::tuple(vec![int.clone(), int.clone()]);
        let t = Ty::tuple(vec![Ty::var("T".into()), int.clone()]).union(&Ty::tuple(vec![
            Ty::carrier(Carrier::Str),
            Ty::carrier(Carrier::Str),
        ]));
        assert_eq!(
            index_shape_agrees(&s, &t),
            Some((true, true)),
            "built: {s} <: {t}"
        );
        let (mut cases, mut held, mut refused, mut bound) = (0, 0, 0, 0);
        for i in 0..2000 {
            let payloads = i % 2 == 1;
            let s = shapes(&mut rng, false, payloads);
            let t = shapes(&mut rng, true, payloads);
            cases += 1;
            match index_shape_agrees(&s, &t) {
                None => refused += 1,
                Some((ok, binding)) => {
                    held += usize::from(ok);
                    bound += usize::from(binding);
                }
            }
        }
        println!("{cases} cases: {held} held ({bound} binding), {refused} refused");
    }

    /// `s <: t` through the index and by trying every shape: the same verdict and, where it
    /// holds, the same bindings, given as `Some((held, bound anything))`, wherever the index
    /// does not refuse; no hold where it does (`None`).
    fn index_shape_agrees(s: &Ty, t: &Ty) -> Option<(bool, bool)> {
        let mut by_index = Binds::new();
        let ok = s.sub(t, &mut by_index);
        SCAN_ALL.set(true);
        let mut by_scan = Binds::new();
        let want = s.sub(t, &mut by_scan);
        SCAN_ALL.set(false);
        if s.unchosen(t).is_some() {
            assert!(!ok, "{s} <: {t}: refused, but held");
            return None;
        }
        assert_eq!(ok, want, "{s} <: {t}");
        if ok {
            assert_eq!(by_index, by_scan, "{s} <: {t}");
        }
        Some((ok, ok && !by_index.is_empty()))
    }

    /// A random component of a tuple for [`near_pairs`]: literals of three integers, of two
    /// floats and of `true`, `int`, `String`, a bare atom of two names, a tuple of a literal and
    /// a component, a union of no class, a function of three, and, when `open`, the variable
    /// `T` or the unknown.
    fn near_component(rng: &mut Rng, open: bool, depth: u32, fns: &[Arc<Sig>]) -> Ty {
        match rng.below(if open { 15 } else { 13 }) {
            0..=2 => Ty::lit(&Value::Int(rng.below(3) as i64)),
            3 => Ty::carrier(Carrier::Int),
            4 => Ty::carrier(Carrier::Str),
            5 => Ty::lit(&Value::float([0.0, -0.0][rng.below(2) as usize])),
            6 => Ty::lit(&Value::Bool(true)),
            7 => Ty::set(KType::atom(["a", "b"][rng.below(2) as usize])),
            8 if depth == 0 => Ty::tuple(vec![
                Ty::lit(&Value::Int(rng.below(2) as i64)),
                near_component(rng, open, depth + 1, fns),
            ]),
            8 => Ty::carrier(Carrier::Int),
            9 => Ty::lit(&Value::Int(1)).union(&Ty::carrier(Carrier::Str)),
            10..=12 => Ty::func(fns[rng.below(3) as usize].clone()),
            13 => Ty::var("T".into()),
            _ => Ty::dynamic(),
        }
    }

    /// A union of one to six random tuples of one to three components, with, now and then, a
    /// kind-wide part, `int`, and when `open` the variable `T`.
    fn near_union(rng: &mut Rng, open: bool, fns: &[Arc<Sig>]) -> Ty {
        let mut ms = Vec::new();
        for _ in 0..1 + rng.below(6) {
            let width = [1, 2, 2, 2, 3][rng.below(5) as usize];
            let cs = (0..width)
                .map(|_| near_component(rng, open, 0, fns))
                .collect();
            ms.push(Ty::tuple(cs));
        }
        match rng.below(12) {
            0 => ms.push(Ty::set(KType::tuple(vec![KType::int(), KType::top()]))),
            1 => ms.push(Ty::set(wide())),
            2 => ms.push(Ty::carrier(Carrier::Int)),
            3 if open => ms.push(Ty::var("T".into())),
            _ => {}
        }
        Ty::union_all(&ms)
    }

    /// Meeting and subtracting through [`near_pairs`] gives exactly what meeting and
    /// subtracting every pair of tuples of one length gives (COMPLEXITY.md F127), on random
    /// unions of tuples of points, classes, unions, functions, variables and the unknown.
    #[test]
    fn tuples_met_and_subtracted_through_the_index_are_those_of_every_pair() {
        let int = Ty::carrier(Carrier::Int);
        let fns = [
            Arc::new(Sig::one(Vec::new(), Vec::new(), int.clone())),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::lit(&Value::Int(1)))),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::carrier(Carrier::Str))),
        ];
        let mut rng = Rng(crate::seed::seed(
            "tuples_met_and_subtracted_through_the_index_are_those_of_every_pair",
        ));
        // A built case of both kinds, whatever the draws: `(int,) | (String,)` meets `(int,)` in
        // the tuple `(int,)`, and less `(int,)` it is `(String,)`, one tuple fewer.
        let one = |t: Ty| Ty::tuple(vec![t]);
        let s = one(int.clone()).union(&one(Ty::carrier(Carrier::Str)));
        let t = one(int.clone());
        assert_eq!(
            near_meet_diff_agree(&s, &t),
            (true, true),
            "built: {s} and {t}"
        );
        let (mut cases, mut met, mut dropped) = (0, 0, 0);
        for i in 0..1000 {
            let s = near_union(&mut rng, i % 3 == 0, &fns);
            let t = near_union(&mut rng, i % 2 == 0, &fns);
            for (a, b) in [(&s, &t), (&t, &s)] {
                let (m, d) = near_meet_diff_agree(a, b);
                cases += 1;
                met += usize::from(m);
                dropped += usize::from(d);
            }
        }
        println!("{cases} cases: {met} meets with a tuple, {dropped} differences dropping one");
    }

    /// `a meet b` and `a \ b` through the index and over every pair are the same; whether the
    /// meet holds a tuple, and whether the difference drops one of `a`'s.
    fn near_meet_diff_agree(a: &Ty, b: &Ty) -> (bool, bool) {
        let (meet, diff) = (a.meet(b), a.diff(b));
        NEAR_ALL.set(true);
        let (want_meet, want_diff) = (a.meet(b), a.diff(b));
        NEAR_ALL.set(false);
        assert_eq!(meet, want_meet, "({a}) meet ({b})");
        assert_eq!(diff, want_diff, "({a}) \\ ({b})");
        (!meet.tuples.is_empty(), diff.tuples.len() < a.tuples.len())
    }

    /// Whether two types share a value, decided on the pairs of tuples [`Near`] finds, is what
    /// comparing every pair of tuples of one length decides (COMPLEXITY.md F132), on random
    /// unions of tuples of points, classes, unions, functions, variables and the unknown, and
    /// on the same unions with each tuple of the other side nested as a component of a pair, so
    /// that the tuples' own tuples are compared too. Pairs of sides of more than one pair go
    /// through [`Near`]; the count of those decided by tuples is checked.
    #[test]
    fn tuples_compared_by_meets_through_the_index_are_those_of_every_pair() {
        let int = Ty::carrier(Carrier::Int);
        let fns = [
            Arc::new(Sig::one(Vec::new(), Vec::new(), int.clone())),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::lit(&Value::Int(1)))),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::carrier(Carrier::Str))),
        ];
        let mut rng = Rng(crate::seed::seed(
            "tuples_compared_by_meets_through_the_index_are_those_of_every_pair",
        ));
        // Built cases decided by tuples, through [`Near`], whatever the draws: each side is
        // two tuples, so there are four pairs. `(int,) | (String,)` meets `(int,) | (true,)` in
        // `(int,)`; `(int,) | (String,)` and `(true,) | (1.5,)` share no value, a `bool` and an
        // `f64` being neither `int` nor `String`.
        let one = |t: Ty| Ty::tuple(vec![t]);
        let s = one(int.clone()).union(&one(Ty::carrier(Carrier::Str)));
        let yes = one(int.clone()).union(&one(Ty::lit(&Value::Bool(true))));
        let no = one(Ty::lit(&Value::Bool(true))).union(&one(Ty::lit(&Value::float(1.5))));
        assert_eq!(
            near_meets_agree(&s, &yes),
            Some((true, true)),
            "built: {s} and {yes}"
        );
        assert_eq!(
            near_meets_agree(&s, &no),
            Some((false, true)),
            "built: {s} and {no}"
        );
        let (mut cases, mut meet, mut apart, mut filed) = (0, 0, 0, 0);
        for i in 0..4000 {
            let s = near_union(&mut rng, i % 3 == 0, &fns);
            let t = near_union(&mut rng, i % 2 == 0, &fns);
            let nest = |u: &Ty| Ty::tuple(vec![Ty::lit(&Value::Int(0)), u.clone()]);
            let (ns, nt) = (nest(&s), nest(&t));
            for (a, b) in [(&s, &t), (&t, &s), (&ns, &nt)] {
                cases += 1;
                if let Some((m, f)) = near_meets_agree(a, b) {
                    filed += usize::from(f);
                    match m {
                        true => meet += 1,
                        false => apart += 1,
                    }
                }
            }
        }
        println!("{cases} cases; decided by tuples: {meet} meet, {apart} apart, {filed} filed");
    }

    /// `a meets b` through the index and over every pair agree. Where tuples decide it
    /// (neither side open, and nothing but tuples meets), `Some((meets, through Near))`, the
    /// second true where the sides have more than one pair of tuples.
    fn near_meets_agree(a: &Ty, b: &Ty) -> Option<(bool, bool)> {
        let by_index = a.meets(b);
        NEAR_ALL.set(true);
        let want = a.meets(b);
        NEAR_ALL.set(false);
        assert_eq!(by_index, want, "({a}) meets ({b})");
        a.meets_here(b)
            .is_none()
            .then(|| (by_index, a.tuples.len() * b.tuples.len() > 1))
    }

    /// A random value for [`near_component`]'s tuples: integers 0 to 2, the floats 0, -0 and
    /// 1.5, both booleans, two strings, two bare atoms, an atom with a payload, a tuple of an
    /// integer and a value, a path, an integer outside 64 bits and a rational.
    fn near_value(rng: &mut Rng, depth: u32) -> Value {
        match rng.below(14) {
            0..=2 => Value::Int(rng.below(3) as i64),
            3 => Value::float([0.0, -0.0, 1.5][rng.below(3) as usize]),
            4 => Value::Bool(rng.below(2) == 0),
            5 => Value::str(["s", "t"][rng.below(2) as usize]),
            6 => Value::atom(["a", "b"][rng.below(2) as usize]),
            7 => Value::atom_with("a", vec![Value::Int(rng.below(2) as i64)]),
            8 | 9 if depth == 0 => Value::tuple(vec![
                Value::Int(rng.below(2) as i64),
                near_value(rng, depth + 1),
            ]),
            8 | 9 => Value::Int(1),
            10 => Value::path(vec![Value::str("k")]),
            11 => Value::int_text("123456789012345678901234567890", 10)
                .expect("an integer")
                .expect("an integer"),
            12 => Value::rat(
                zed_kernel::Rat::decimal("0.5")
                    .expect("a rat")
                    .expect("a rat"),
            ),
            _ => Value::tuple(Vec::new()),
        }
    }

    /// Whether a type holds a tuple value, decided on the tuples [`Holders`] finds, is what
    /// comparing the value with every tuple of its length decides (COMPLEXITY.md F133), on
    /// random unions of tuples of points, classes, unions, functions, variables and the unknown,
    /// and random tuple values of points of every kind, alone, nested as the second component
    /// of `(0, _)`, and as `k` values `(x)` in a tuple of `k` copies of `(t)`: a copy of a type copies
    /// its outer level, so through the one row of `(t)` the union is one node, read for each of
    /// the `k` values in one walk, and filed in its own course.
    #[test]
    fn tuples_that_hold_a_value_through_the_index_are_those_of_every_tuple() {
        let int = Ty::carrier(Carrier::Int);
        let fns = [
            Arc::new(Sig::one(Vec::new(), Vec::new(), int.clone())),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::lit(&Value::Int(1)))),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::carrier(Carrier::Str))),
        ];
        let mut rng = Rng(crate::seed::seed(
            "tuples_that_hold_a_value_through_the_index_are_those_of_every_tuple",
        ));
        // Both verdicts on a built case, whatever the draws: `(int,) | (String,)` holds `(1,)`
        // and not `(true,)`, a `bool` being neither `int` nor `String`.
        let one = |t: Ty| Ty::tuple(vec![t]);
        let t = one(int.clone()).union(&one(Ty::carrier(Carrier::Str)));
        let yes = Value::tuple(vec![Value::Int(1)]);
        let no = Value::tuple(vec![Value::Bool(true)]);
        assert!(holders_agree(&t, &yes), "built: ({t}) holds {yes:?}");
        assert!(!holders_agree(&t, &no), "built: ({t}) holds {no:?}");
        let (mut cases, mut held, mut apart) = (0, 0, 0);
        for i in 0..8000 {
            let t = near_union(&mut rng, i % 3 == 0, &fns);
            // A value of a length that `t` has most of the time: that of one of its tuples.
            let width = match t.tuples.is_empty() || rng.below(5) == 0 {
                true => 1 + rng.below(3) as usize,
                false => t.tuples[rng.below(t.tuples.len() as u64) as usize].len(),
            };
            let tuple =
                |rng: &mut Rng| Value::tuple((0..width).map(|_| near_value(rng, 0)).collect());
            let v = tuple(&mut rng);
            let k = 1 + rng.below(12) as usize;
            let vs = Value::tuple(
                (0..k)
                    .map(|_| Value::tuple(vec![tuple(&mut rng)]))
                    .collect(),
            );
            let nest = |u: &Ty| Ty::tuple(vec![Ty::lit(&Value::Int(0)), u.clone()]);
            let nv = Value::tuple(vec![Value::Int(0), v.clone()]);
            let wide = Ty::tuple(vec![Ty::tuple(vec![t.clone()]); k]);
            for (a, x) in [(&t, &v), (&nest(&t), &nv), (&wide, &vs)] {
                cases += 1;
                match holders_agree(a, x) {
                    true => held += 1,
                    false => apart += 1,
                }
            }
        }
        println!("{cases} cases: {held} held, {apart} not");
    }

    /// Whether `a` holds `x` through the index, through the index filed at once and by every
    /// tuple: the same verdict, given.
    fn holders_agree(a: &Ty, x: &Value) -> bool {
        let by_index = a.contains(x);
        FILE.set(Some(true));
        let filed = a.contains(x);
        FILE.set(Some(false));
        let want = a.contains(x);
        FILE.set(None);
        assert_eq!(by_index, want, "({a}) holds {x:?}");
        assert_eq!(filed, want, "({a}) holds {x:?}, filed at once");
        want
    }

    /// [`class_of`], read from the parts of a set, is what comparing the set with each carrier
    /// and with the atoms gives, on random unions and differences of carriers, literals, atoms
    /// with and without payloads, atoms of no value, all atoms but one, and tuples, some empty; and
    /// [`KType::universes`] gives the parts [`KType::split`] gives.
    #[test]
    fn class_of_read_from_the_parts_is_that_of_comparing_types() {
        let by_subtype = |s: &KType| {
            if let Some(c) = Carrier::ALL.into_iter().find(|c| s.subtype(&c.ty())) {
                return Some(ShapeKey::Carrier(c));
            }
            if !s.subtype(&atoms()) {
                return None;
            }
            let mut names = s.atom_names()?;
            let (n, _) = names.next()?;
            names.next().is_none().then(|| ShapeKey::Atom(n.into()))
        };
        let piece = |rng: &mut Rng| match rng.below(15) {
            0 => KType::int(),
            1 => KType::lit(&Value::Int(rng.below(3) as i64)).expect("a literal"),
            2 => KType::f64(),
            3 => KType::lit(&Value::float(1.5)).expect("a literal"),
            4 => KType::rat(),
            5 => KType::string(),
            6 => KType::bool(),
            7 => KType::lit(&Value::Bool(false)).expect("a literal"),
            8 => KType::atom(["a", "b"][rng.below(2) as usize]),
            9 => KType::atom_with("a", &KType::int()),
            10 => KType::atom_with("c", &KType::empty()),
            11 => &atoms() - &KType::atom("a"),
            12 => KType::tuple(vec![KType::int(), KType::top()]),
            13 => KType::tuple(vec![KType::empty()]),
            _ => KType::atom_with("a", &KType::tuple(vec![KType::empty()])),
        };
        // Each class on a built set, whatever the draws: `int` is of the carrier `int`, `#a` of
        // the one name `a`, and `int | String` of none, being within no one carrier and no atoms.
        assert!(
            matches!(
                class_agrees(&KType::int(), &by_subtype),
                Some(ShapeKey::Carrier(Carrier::Int))
            ),
            "built: int"
        );
        assert!(
            matches!(
                class_agrees(&KType::atom("a"), &by_subtype),
                Some(ShapeKey::Atom(_))
            ),
            "built: #a"
        );
        let mixed = &KType::int() | &KType::string();
        assert!(
            class_agrees(&mixed, &by_subtype).is_none(),
            "built: int | String"
        );
        let mut rng = Rng(crate::seed::seed(
            "class_of_read_from_the_parts_is_that_of_comparing_types",
        ));
        let (mut carriers, mut names, mut none) = (0, 0, 0);
        for _ in 0..20_000 {
            let mut s = piece(&mut rng);
            for _ in 0..rng.below(3) {
                let p = piece(&mut rng);
                s = match rng.below(4) {
                    0 => &s - &p,
                    _ => &s | &p,
                };
            }
            if s.is_empty() {
                assert!(class_of(&s).is_none(), "the class of {s:?}, empty");
                continue;
            }
            match class_agrees(&s, &by_subtype) {
                Some(ShapeKey::Carrier(_)) => carriers += 1,
                Some(_) => names += 1,
                None => none += 1,
            }
        }
        println!("{carriers} of a carrier, {names} of one name, {none} of none");
    }

    /// The class [`class_of`] reads from the parts of the set `s`, not empty, after asserting
    /// that it is the one `by_subtype` finds and that [`KType::universes`] gives the parts
    /// [`KType::split`] gives.
    fn class_agrees(
        s: &KType,
        by_subtype: &dyn Fn(&KType) -> Option<ShapeKey>,
    ) -> Option<ShapeKey> {
        let split = s.split();
        let universes = zed_kernel::types::Universes {
            bases: split.bases.each_ref().map(Option::is_some),
            atoms: split.atoms.is_some(),
            rest: split.rest.is_some(),
        };
        assert!(s.universes() == universes, "the universes of {s:?}");
        let class = class_of(s);
        assert!(class == by_subtype(s), "the class of {s:?}");
        class
    }

    /// What the filings find ([`Near`], [`Holders`]) does not depend on the hash or on the order
    /// the tuples are filed in: with another seed of their hasher ([`SEED`]) the tuples come out
    /// the same and in the same order, and with the tuples of the filed side given in reverse
    /// the same tuples come out, on random unions and tuple values as in the tests above.
    #[test]
    fn filings_find_the_same_tuples_whatever_the_hash_and_the_order() {
        let int = Ty::carrier(Carrier::Int);
        let fns = [
            Arc::new(Sig::one(Vec::new(), Vec::new(), int.clone())),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::lit(&Value::Int(1)))),
            Arc::new(Sig::one(Vec::new(), Vec::new(), Ty::carrier(Carrier::Str))),
        ];
        // The tuples found for each tuple of `left` among `right`, under the seed `seed`.
        let near = |left: &[Row], right: &[Row], seed: u64| {
            SEED.set(seed);
            let groups = Groups::new(left, right);
            let mut near = Near::new(&groups);
            let found: Vec<Vec<usize>> = (0..left.len()).map(|l| near.of(l).collect()).collect();
            SEED.set(0);
            found
        };
        // The tuples of `t` among `rows` found for the tuple value of `items`.
        let holders = |t: &Ty, rows: &[usize], items: &Items, seed: u64| {
            SEED.set(seed);
            let found: Vec<usize> = Holders::new(t, rows).of(items).collect();
            SEED.set(0);
            found
        };
        let sorted = |mut is: Vec<usize>| {
            is.sort_unstable();
            is
        };
        // The tuples of `t` near each tuple of `s`, after asserting they are the same under
        // the seeds 0 and `1 + i`, and with `t`'s tuples in reverse under `7 + i`.
        let near_agrees = |s: &Ty, t: &Ty, i: u64| {
            let want = near(&s.tuples.to_vec(), &t.tuples.to_vec(), 0);
            assert_eq!(
                near(&s.tuples.to_vec(), &t.tuples.to_vec(), 1 + i),
                want,
                "({s}) near ({t})"
            );
            let back: Vec<Row> = t.tuples.iter().rev().cloned().collect();
            let last = t.tuples.len().saturating_sub(1);
            for (got, want) in near(&s.tuples.to_vec(), &back, 7 + i)
                .into_iter()
                .zip(&want)
            {
                let got = sorted(got.into_iter().map(|j| last - j).collect());
                assert_eq!(&got, &sorted(want.clone()), "({s}) near ({t}) in reverse");
            }
            want
        };
        // The tuples of `t` of the length of `v` that may hold it, after asserting the same.
        let holders_agree = |t: &Ty, v: &Value, i: u64| {
            let Value::Tuple(items) = v else {
                unreachable!("a tuple value")
            };
            let rows: Vec<usize> = (0..t.tuples.len())
                .filter(|&j| t.tuples[j].len() == items.len())
                .collect();
            let want = holders(t, &rows, items, 0);
            assert_eq!(holders(t, &rows, items, 1 + i), want, "{t} holds {v:?}");
            let back: Vec<usize> = rows.iter().rev().copied().collect();
            assert_eq!(
                sorted(holders(t, &back, items, 7 + i)),
                sorted(want.clone()),
                "{t} holds {v:?} in reverse"
            );
            want
        };
        // Built cases where a lookup finds more than one tuple, whatever the draws: `(int,)`
        // may meet both `(int,)` and `(1,)` of `(int,) | (1,) | (String,)`, and `(1,)` is a
        // value of both; neither meets `(String,)`.
        let one = |t: Ty| Ty::tuple(vec![t]);
        let s = one(int.clone());
        let t = one(int.clone())
            .union(&one(Ty::lit(&Value::Int(1))))
            .union(&one(Ty::carrier(Carrier::Str)));
        let found = near_agrees(&s, &t, 0);
        assert!(
            found[0].len() > 1,
            "built: ({s}) near ({t}) finds {found:?}"
        );
        let v = Value::tuple(vec![Value::Int(1)]);
        let found = holders_agree(&t, &v, 0);
        assert!(found.len() > 1, "built: {t} holds {v:?} by {found:?}");
        let mut rng = Rng(crate::seed::seed(
            "filings_find_the_same_tuples_whatever_the_hash_and_the_order",
        ));
        let (mut found, mut several) = (0, 0);
        for i in 0..5_000 {
            let s = near_union(&mut rng, i % 3 == 0, &fns);
            let t = near_union(&mut rng, i % 2 == 0, &fns);
            let want = near_agrees(&s, &t, i);
            found += want.iter().filter(|w| !w.is_empty()).count();
            several += want.iter().filter(|w| w.len() > 1).count();

            let width = match t.tuples.is_empty() {
                true => 1 + rng.below(3) as usize,
                false => t.tuples[rng.below(t.tuples.len() as u64) as usize].len(),
            };
            let v = Value::tuple((0..width).map(|_| near_value(&mut rng, 0)).collect());
            let want = holders_agree(&t, &v, i);
            found += usize::from(!want.is_empty());
            several += usize::from(want.len() > 1);
        }
        println!("{found} lookups found a tuple, {several} more than one");
    }

    /// Two chains of calls built apart are equal link by link, and differ where a call, its
    /// text or the length differs; only the first call is hashed. The checker compares two
    /// chains only when it compares two signatures that each hold one (`Same::sig`), which
    /// no program in the tests makes it do, so the comparison and the hash are read here
    /// (item TEST-types-unreached-paths).
    #[test]
    fn two_chains_of_calls_are_equal_link_by_link() {
        use std::hash::{BuildHasher, RandomState};
        let link = |at: usize, text: &str, next: Option<Via>| Via {
            at: Span {
                start: at,
                end: at + 1,
            },
            text: text.into(),
            next: next.map(Arc::new),
        };
        let chain =
            |last: &str, n: usize| (1..n).fold(link(0, last, None), |v, i| link(i, "w", Some(v)));
        assert_eq!(chain("f", 3), chain("f", 3));
        assert_ne!(chain("f", 3), chain("g", 3));
        assert_ne!(chain("f", 3), chain("f", 2));
        assert_ne!(chain("f", 2), chain("f", 3));
        assert_ne!(link(0, "w", None), link(1, "w", None));
        // Equal first links, then one chain ends: they differ by their length.
        assert_ne!(link(0, "w", Some(link(1, "f", None))), link(0, "w", None));
        let one = chain("f", 3);
        assert_eq!(one, one.clone());
        let s = RandomState::new();
        assert_eq!(s.hash_one(chain("f", 3)), s.hash_one(chain("g", 3)));
        assert_ne!(
            s.hash_one(link(0, "w", None)),
            s.hash_one(link(0, "v", None))
        );
    }

    /// [`Ty::subtype`], which answers false at once where `self` holds a variable with no
    /// quote that `other` does not ([`Ty::var_outside`]), gives what the comparison made in
    /// full gives, on every pair of types made of a subset of four variables (one named with
    /// a quote, which the early answer does not take) and one of five other parts: nothing,
    /// `int`, a tuple of a variable, the variable alone in a tuple of `int`, and the unknown.
    #[test]
    fn subtype_answers_as_the_full_comparison_with_variables_outside() {
        let names = ["T", "U", "V", "W'"];
        let extra = [
            Ty::empty(),
            Ty::carrier(Carrier::Int),
            Ty::tuple(vec![Ty::var("T".into())]),
            Ty::tuple(vec![Ty::carrier(Carrier::Int)]),
            Ty::dynamic(),
        ];
        let types: Vec<Ty> = (0..1u32 << names.len())
            .flat_map(|mask| {
                let vars = (names.iter().enumerate())
                    .filter(|(i, _)| mask >> i & 1 == 1)
                    .fold(Ty::empty(), |t, (_, v)| t.union(&Ty::var((*v).into())));
                extra.iter().map(move |e| vars.union(e))
            })
            .collect();
        let mut early = 0;
        for a in &types {
            for b in &types {
                let mut binds = Binds::new();
                let full = a.sub(b, &mut binds) && binds.is_empty();
                assert_eq!(a.subtype(b), full, "{a:?} <: {b:?}");
                early += usize::from(a.var_outside(b));
            }
        }
        // The early answer is taken on some pairs, so the check above covers it.
        assert!(early > 0);
    }

    /// The early answer of [`Ty::subtype`] on a union of many variables against one: false
    /// where the one is not among them or is one of several, true for one variable against
    /// itself, and true against the unknown.
    #[test]
    fn many_variables_are_not_within_one() {
        let many = (0..64).fold(Ty::empty(), |t, i| {
            t.union(&Ty::var(format!("X{i}").into()))
        });
        let one = Ty::var("X0".into());
        assert!(!many.subtype(&one));
        assert!(!many.subtype(&Ty::var("Y".into())));
        assert!(one.subtype(&many));
        assert!(one.subtype(&one));
        assert!(many.subtype(&many));
        assert!(many.subtype(&Ty::dynamic()));
    }
}
