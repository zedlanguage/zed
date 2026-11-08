//! Kernel values: scalars, atoms with their payloads, tuples, keypaths and families
//! (step L1.17), the operations that follow their nesting, and the errors that hold them.
//!
//! Values are totally ordered by the natural order of DESIGN.md sec:order: kinds in the order
//! atoms, `bool`, numbers, strings, tuples, keypaths, families; numbers by value across
//! `int`, `rat` and floats, an `int` before a `rat` before a float of equal value. Rust's `==`
//! on values is the ties of that order: the bitwise identity that keys and the law catalog
//! read. The language's `==` is [`Value::surface_eq`], which differs only at floats.
//!
//! Families are finite keyed trees, the values the Tier-1 calculus computes over. A family
//! maps each key of one level to a value; a value that is itself a family is the next level
//! down. A *leaf* is a non-family value, and its *keypath* is the sequence of keys that reaches
//! it (sec:keypaths). Two rules of (sec:values_morphisms) hold by construction: every keypath
//! has exactly one writer, and an outer key over an empty level has no keypath, so it is
//! dropped.
//!
//! The operations on a [`Value`] that follow its nesting (drop, compare, copy and show) each
//! keep their own stack on the heap, so a value's depth is limited by the machine's memory
//! alone (DESIGN.md sec:kernel, "Reference semantics"), and each costs O(size).
//!
//! [`KernelError`] is the ways a kernel evaluation stops without a value. Failure atoms such as
//! `#empty` are values, not errors (sec:failure). These errors are the cases the checker rejects
//! statically, which the reference evaluator detects when it meets them, plus the divergence
//! that fuel bounds.
//!
//! A value, a family, the parts a drop queues and an error that names a keypath hold one
//! another, so they are one recursive type and share this file: Zed forbids an import cycle
//! between files (step S.1f).

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::mem;
use std::ops::Deref;
use std::slice;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

use imbl::OrdMap;
use imbl::ordmap::{DiffItem, Iter};
use imbl::shared_ptr::DefaultSharedPtr;
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

use crate::deep::{self, Queue};
use crate::num::{Exact, Rat, TooLarge, bytes_of, read_decimal, room, sign_of};
use crate::text::{Text, TooLong};
use crate::types::KeyHasher;

/// `minimum(a, b)` (`min` true) or `maximum(a, b)` of IEEE 754-2019 (DESIGN.md sec:reduction,
/// item 5): a NaN in either position gives a NaN, and `-0.0` is below `0.0`, so
/// `min(-0.0, 0.0)` is `-0.0` and `max(-0.0, 0.0)` is `0.0` in both orders. Rust's
/// `f64::minimum` is not stable, and `f64::min` returns the other operand of a NaN.
pub(crate) fn ieee_min_max(min: bool, a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        return f64::NAN;
    }
    // On equal values only the zeros differ, by sign: min takes the negative one.
    let a_first = if a == b {
        a.is_sign_negative() == min
    } else {
        (a < b) == min
    };
    if a_first { a } else { b }
}

/// A 64-bit float that compares bitwise after NaN canonicalization, as every kernel equation
/// on a float-bearing value does (sec:kernel, the law catalog): `-0.0` and `0.0` are different
/// values, and every NaN is the one canonical NaN.
#[derive(Clone, Copy)]
pub struct F64(f64);

impl F64 {
    /// Wraps `x`, replacing any NaN by the canonical NaN.
    pub fn new(x: f64) -> Self {
        if x.is_nan() { F64(f64::NAN) } else { F64(x) }
    }

    /// The wrapped float.
    pub fn get(self) -> f64 {
        self.0
    }
}

impl PartialEq for F64 {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for F64 {}

impl Ord for F64 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl PartialOrd for F64 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for F64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// An atom such as `#empty`, `#ioError("disk full")` or `#err(code: 3)`. Failure is data
/// (sec:failure): an atom is an ordinary value that flows through the kernel like any other.
/// A payload is a tuple, by position, or a struct, by name (sec:lexical, the `#name(args)`
/// row); a struct payload keeps its fields in the code point order of their names, so the
/// written order of a construction is not part of the value.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Atom {
    /// The name, without the leading `#`.
    pub name: Arc<str>,
    /// The field names of a struct payload, sorted; empty for a tuple payload. Shared, so a
    /// copy of the atom is O(1).
    pub fields: Fields,
    /// The payload's values, one per field of a struct payload; empty for a bare atom.
    pub args: Items,
}

/// The field names of a struct payload, shared, with the [`Id`] of the list as it was built, so
/// a walk can read a list shared by many atoms once. It is one pointer wide, and `None` for no
/// fields, which keeps an [`Atom`] at 48 bytes and a [`Value`] at 56 next to the id in
/// [`Items`].
#[derive(Clone, Default)]
pub struct Fields(Option<Arc<Names>>);

struct Names {
    id: Id,
    names: Box<[Arc<str>]>,
}

impl Fields {
    /// The id of the list: copies share it, and no other list has it. Empty lists have id 0.
    pub(crate) fn id(&self) -> Id {
        self.0.as_ref().map_or(0, |n| n.id)
    }
}

impl Deref for Fields {
    type Target = [Arc<str>];

    fn deref(&self) -> &[Arc<str>] {
        self.0.as_ref().map_or(&[], |n| &n.names)
    }
}

impl From<Vec<Arc<str>>> for Fields {
    fn from(names: Vec<Arc<str>>) -> Self {
        match names.is_empty() {
            true => Fields::default(),
            false => Fields(Some(Arc::new(Names {
                id: fresh_id(),
                names: names.into(),
            }))),
        }
    }
}

impl FromIterator<Arc<str>> for Fields {
    fn from_iter<I: IntoIterator<Item = Arc<str>>>(names: I) -> Self {
        Fields::from(names.into_iter().collect::<Vec<_>>())
    }
}

impl PartialEq for Fields {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id() || **self == **other
    }
}

impl Eq for Fields {}

impl Ord for Fields {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.id() == other.id() {
            true => Ordering::Equal,
            false => (**self).cmp(&**other),
        }
    }
}

impl PartialOrd for Fields {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Fields {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

/// The values inside a tuple, a keypath or a payload, shared: a copy is a reference count, so
/// reading a variable that holds a tuple of any size is O(1). It owns its drop, comparison and
/// `Debug` form so that each runs on the heap, whatever the depth (see `crate::deep`).
///
/// The second field is the sequence's [`Id`], drawn when the sequence is built: copies share
/// it, no other sequence has it, and the sequence is never changed in place, so a walk that
/// meets a shared sequence again knows it by its id (memo keys are ids or structure, never
/// addresses). Empty sequences have id 0.
#[derive(Clone, Default)]
pub struct Items(Arc<[Value]>, Id);

impl Items {
    /// The values, in order.
    pub fn as_slice(&self) -> &[Value] {
        &self.0
    }

    /// Whether `self` and `other` are one shared sequence, so equal without reading them.
    pub(crate) fn same(&self, other: &Items) -> bool {
        self.1 == other.1
    }

    /// The id of the sequence.
    pub(crate) fn id(&self) -> Id {
        self.1
    }

    /// Whether another holder shares the sequence, so a walk of a value can meet it twice. A
    /// sequence held once is reached by one path only, through its one holder.
    pub(crate) fn is_shared(&self) -> bool {
        Arc::strong_count(&self.0) > 1
    }

    /// The ids of `a` and `b` when a walk over both can meet the pair again: when either is
    /// shared. Empty sequences are read at once.
    pub(crate) fn pair(a: &Items, b: &Items) -> Option<Pair> {
        let again = (a.is_shared() || b.is_shared()) && !(a.is_empty() && b.is_empty());
        again.then_some((a.1, b.1))
    }

    /// The values, as a vector: moved out when this is their only holder, and each copied by
    /// a reference count otherwise.
    pub fn into_vec(mut self) -> Vec<Value> {
        match Arc::get_mut(&mut self.0) {
            // A placeholder takes each value's place; what is left is a slice of scalars.
            Some(only) => only
                .iter_mut()
                .map(|v| mem::replace(v, Value::Bool(false)))
                .collect(),
            None => self.0.to_vec(),
        }
    }
}

impl Deref for Items {
    type Target = [Value];

    fn deref(&self) -> &[Value] {
        &self.0
    }
}

impl From<Vec<Value>> for Items {
    fn from(values: Vec<Value>) -> Self {
        // The empty slice is one static allocation; `Arc::from` would allocate per call.
        match values.is_empty() {
            true => Items::default(),
            false => Items(values.into(), fresh_id()),
        }
    }
}

impl FromIterator<Value> for Items {
    fn from_iter<I: IntoIterator<Item = Value>>(values: I) -> Self {
        Items::from(values.into_iter().collect::<Vec<_>>())
    }
}

impl IntoIterator for Items {
    type Item = Value;
    type IntoIter = std::vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<'a> IntoIterator for &'a Items {
    type Item = &'a Value;
    type IntoIter = slice::Iter<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl Drop for Items {
    fn drop(&mut self) {
        if !self.0.is_empty() {
            free(Part::Items(mem::take(&mut self.0)));
        }
    }
}

impl PartialEq for Items {
    fn eq(&self, other: &Self) -> bool {
        items_eq(self, other)
    }
}

impl Eq for Items {}

impl Ord for Items {
    fn cmp(&self, other: &Self) -> Ordering {
        items_cmp(self, other)
    }
}

impl PartialOrd for Items {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A kernel value. Values are totally ordered, so any value can be a key; the order of keys
/// is the order a family's entries are visited in.
#[derive(Clone)]
pub enum Value {
    /// `true` or `false`.
    Bool(bool),
    /// An integer in the 64-bit range.
    Int(i64),
    /// An integer outside the 64-bit range, never one inside it: a [`Rat`] that is an integer,
    /// which may hold its prime powers unbuilt.
    Big(Arc<Rat>),
    /// A rational, `3r` or `1r/3r`.
    Rat(Arc<Rat>),
    /// A float, compared bitwise.
    Float(F64),
    /// A string.
    Str(Text),
    /// A failure atom.
    Atom(Atom),
    /// A tuple, such as a composite key.
    Tuple(Items),
    /// A keypath as a value: what a `reindex` key map reads and returns (sec:keypaths).
    Path(Items),
    /// A family: one level of keys, whose values may be families in turn.
    Family(Family),
}

/// Which shared sequence a tuple or an atom with a payload holds, as [`Value::shared_parts`]
/// gives it: the sequence's [`Id`], and for an atom its name and the [`Id`] of its field names,
/// so a tuple and atoms of other names over one sequence are told apart.
pub type SharedParts<'v> = (Id, Option<(&'v str, Id)>);

impl Value {
    /// The sequence a non-empty tuple or an atom with a payload holds, when another holder shares
    /// it, so that a walk of a value can meet it again on another path; none for any other value
    /// and for a sequence held once, which only its one holder reaches. Two values with the same
    /// answer are one value, so a walk that keeps one result per answer reads each shared part
    /// once and never merges values that are merely equal.
    pub fn shared_parts(&self) -> Option<SharedParts<'_>> {
        match self {
            Value::Tuple(xs) if xs.is_shared() && !xs.is_empty() => Some((xs.id(), None)),
            Value::Atom(a) if a.args.is_shared() && !a.args.is_empty() => {
                Some((a.args.id(), Some((&a.name, a.fields.id()))))
            }
            _ => None,
        }
    }

    /// A string value.
    pub fn str(s: &str) -> Self {
        Value::Str(s.into())
    }

    /// A tuple value.
    pub fn tuple(items: Vec<Value>) -> Self {
        Value::Tuple(items.into())
    }

    /// A keypath value.
    pub fn path(keys: Vec<Value>) -> Self {
        Value::Path(keys.into())
    }

    /// A float value.
    pub fn float(x: f64) -> Self {
        Value::Float(F64::new(x))
    }

    /// A bare atom such as `#empty`, given its name without the `#`.
    pub fn atom(name: &str) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            fields: Fields::default(),
            args: Items::default(),
        })
    }

    /// An atom with a tuple payload, such as `#ioError("disk full")`; a shared name is kept,
    /// not copied.
    pub fn atom_with(name: impl Into<Arc<str>>, args: Vec<Value>) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            fields: Fields::default(),
            args: args.into(),
        })
    }

    /// `#ioError(op:, path:, why:)`: a failed read or write of a port, its operation (`read`
    /// or `write`), its path and the operating system's reason (DESIGN.md sec:ports).
    pub fn io_error(op: &str, path: &str, why: &str) -> Self {
        // The fields in name order, as `atom_named` sorts them.
        Value::Atom(Atom {
            name: "ioError".into(),
            fields: vec![Arc::from("op"), "path".into(), "why".into()].into(),
            args: vec![Value::str(op), Value::str(path), Value::str(why)].into(),
        })
    }

    /// An atom with a struct payload, such as `#err(code: 3)`, its fields in any order;
    /// `None` when a name repeats. A shared name is kept, not copied.
    pub fn atom_named(name: impl Into<Arc<str>>, fields: Vec<(Arc<str>, Value)>) -> Option<Self> {
        let mut fields = fields;
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        if fields.windows(2).any(|w| w[0].0 == w[1].0) {
            return None;
        }
        let (fields, args): (Vec<Arc<str>>, Vec<Value>) = fields.into_iter().unzip();
        Some(Value::Atom(Atom {
            name: name.into(),
            fields: fields.into(),
            args: args.into(),
        }))
    }

    /// The failure several loose atoms make together (DESIGN.md sec:failure): the set of the
    /// distinct ones as `#errs({…})`, an `#errs` among them giving its members, and a single
    /// failure as itself.
    pub fn merge_failures<'a>(atoms: impl IntoIterator<Item = &'a Value>) -> Value {
        // The largest set is extended, not copied, so a chain of n merges costs O(n log n).
        let atoms: Vec<&Value> = atoms.into_iter().collect();
        let base = atoms
            .iter()
            .filter_map(|a| a.errs())
            .max_by_key(|f| f.len());
        let mut set = base.cloned().unwrap_or_default();
        let mut added = Vec::new();
        for a in &atoms {
            match a.errs() {
                Some(m) if base.is_some_and(|b| std::ptr::eq(m, b)) => {}
                Some(m) => added.extend(m.iter().map(|(k, v)| (k.clone(), v.clone()))),
                None => added.push((a.key(), (*a).clone())),
            }
        }
        set.extend(added);
        if set.len() == 1 {
            return set.iter().next().expect("one member").1.clone();
        }
        Value::atom_with("errs", vec![Value::Family(set)])
    }

    /// The set of an `#errs({…})`.
    pub fn errs(&self) -> Option<&Family> {
        match self {
            Value::Atom(a) if &*a.name == "errs" && a.fields.is_empty() => {
                match a.args.as_slice() {
                    [Value::Family(f)] => Some(f),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The integer `n`, as an `Int` when it is in the 64-bit range.
    pub fn int(n: BigInt) -> Self {
        match n.to_i64() {
            Some(n) => Value::Int(n),
            None => Value::Big(Arc::new(Rat::int(n))),
        }
    }

    /// The integer `r`, which must be one, as an `Int` when it is in the 64-bit range.
    pub fn integer(r: Rat) -> Self {
        match r.small_integer() {
            Some(n) => Value::int(n),
            None => Value::Big(Arc::new(r)),
        }
    }

    /// The integer whose digits, in base `radix` (2 to 36), are `text`, after an optional `-` or
    /// `+`; `Ok(None)` when they are not, and [`TooLarge`] when the system refuses the memory for
    /// reading them, asked before anything is built.
    pub fn int_text(text: &str, radix: u32) -> Result<Option<Self>, TooLarge> {
        let (sign, digits) = sign_of(text);
        let int = |n: BigUint| Value::int(BigInt::from_biguint(sign, n));
        if radix == 10 {
            return Ok(read_decimal(digits)?.map(int));
        }
        if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
            return Ok(None);
        }
        // Complexity tradeoff: the memory asked for is twice a byte per digit plus the
        // integer's width, a measured bound, not a proved one, on num-bigint's reading of a
        // text in a base other than 10, which holds the digits as bytes and then packs them
        // into words: the peak heap was 8 bits per digit plus the width (9, 11 and 12 bits per
        // digit in bases 2, 8 and 16) over texts of 2^12 to 2^22 digits, half the ask. A width
        // alone undercounts base 2, whose byte per digit is eight times its width. So a text
        // needing less is refused when the free memory lies between the two, and none aborts.
        // Tested by `a_long_integer_literal_is_refused_when_memory_is_short` (COMPLEXITY.md
        // K30). A complete solution would pack the digits into words with memory reserved once.
        let per_digit = radix.ilog2() + u32::from(!radix.is_power_of_two());
        room((BigUint::from(digits.len()) * (8 + per_digit)) << 1u32)?;
        Ok(BigUint::parse_bytes(digits.as_bytes(), radix).map(int))
    }

    /// The rational `r`.
    pub fn rat(r: Rat) -> Self {
        Value::Rat(Arc::new(r))
    }

    /// The integer inside, of either width.
    pub fn as_integer(&self) -> Option<Cow<'_, Rat>> {
        match self {
            Value::Int(n) => Some(Cow::Owned(Rat::int(BigInt::from(*n)))),
            Value::Big(n) => Some(Cow::Borrowed(n)),
            _ => None,
        }
    }

    /// The value as a key (sec:type_resolution, "Equality and order corner rules"): `-0.0`
    /// becomes `0.0` at any depth, since `0.0 == -0.0` makes the two zeros one key, which then
    /// holds the same bits whichever zero arrived first. NaN is already one value. A value that
    /// is its own key is shared, not copied.
    pub fn key(&self) -> Value {
        match self {
            Value::Tuple(_) | Value::Path(_) | Value::Atom(_) if self.is_key() => self.clone(),
            Value::Tuple(_) | Value::Path(_) | Value::Atom(_) => {
                let mut one = copy(slice::from_ref(self), key_leaf);
                one.pop().expect("a copy of one value holds one value")
            }
            leaf => key_leaf(leaf),
        }
    }

    /// Whether the value is its own key: whether it holds no `-0.0`.
    pub fn is_key(&self) -> bool {
        all_leaves(slice::from_ref(self), |v| match v {
            Value::Float(x) => !(x.get() == 0.0 && x.get().is_sign_negative()),
            _ => true,
        })
    }

    /// The language's order on two values of one kind: structural, except that two floats
    /// compare as IEEE 754 does, so `-0.0` and `0.0` are equal and a NaN is unordered, and
    /// tuples compare component by component in that order. `None` when they are unordered.
    pub fn surface_cmp(&self, other: &Value) -> Option<Ordering> {
        surface_cmp(self, other)
    }

    /// Whether `min(self, other)` (`min` true) or `max(self, other)` is `self`, for two values of
    /// one kind (DESIGN.md sec:reduction, item 5): two tuples are ordered lexicographically, and
    /// the first component in which they differ decides, by `min` or `max` of the two components
    /// there, so that two floats that differ are decided by IEEE 754-2019 `minimum` or
    /// `maximum` (a NaN is taken by both, and `-0.0` is below `0.0`), and two equal values give
    /// `self`. `None` when a pair of components is of two kinds or two tuples differ in length.
    /// The walk reads each distinct pair of shared tuples once, so it costs
    /// O(distinct pairs of components read).
    pub fn selects(&self, other: &Value, min: bool) -> Option<bool> {
        let r = if min { Relation::Min } else { Relation::Max };
        walk(step(self, other, r)).map(|o| match o {
            Ordering::Equal => true,
            Ordering::Less => min,
            Ordering::Greater => !min,
        })
    }

    /// The language's `==` (sec:failure, M0.11): structural, except that two floats compare
    /// as IEEE 754 does, so `NaN != NaN` and `0.0 == -0.0`, at any depth.
    pub fn surface_eq(&self, other: &Value) -> bool {
        surface_eq(self, other)
    }

    /// The order on two values at least one of which holds no parts: the two values' kinds,
    /// or their scalars. Two values of one kind with parts are compared in [`crate::deep`].
    pub(crate) fn scalar_cmp(&self, other: &Value) -> Ordering {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
            (Value::Str(a), Value::Str(b)) => a.cmp(b),
            _ if self.kind() == 2 && other.kind() == 2 => number_cmp(self, other),
            _ => self.kind().cmp(&other.kind()),
        }
    }

    /// The kind of a value, by its rank in the natural order; the numbers are one kind.
    fn kind(&self) -> u8 {
        match self {
            Value::Atom(_) => 0,
            Value::Bool(_) => 1,
            Value::Int(_) | Value::Big(_) | Value::Rat(_) | Value::Float(_) => 2,
            Value::Str(_) => 3,
            Value::Tuple(_) => 4,
            Value::Path(_) => 5,
            Value::Family(_) => 6,
        }
    }

    /// The numeric kind: `int` (either width), `rat` or float; `None` for any other value.
    pub fn number_kind(&self) -> Option<u8> {
        match self {
            Value::Int(_) | Value::Big(_) => Some(0),
            Value::Rat(_) => Some(1),
            Value::Float(_) => Some(2),
            _ => None,
        }
    }

    /// The type of every value of this one's kind, as a program writes it (DESIGN.md L1.40d):
    /// `int` for an integer of either width, `#a` for a bare atom and `#a(..)` for one with a
    /// payload, `(..)` for a tuple or a keypath, `_ ->? _` for a family. A type error names
    /// this, not the value, which may be too large to print; its cost is the atom's name.
    pub fn kind_type(&self) -> String {
        match self {
            Value::Bool(_) => "bool".into(),
            Value::Int(_) | Value::Big(_) => "int".into(),
            Value::Rat(_) => "rat".into(),
            Value::Float(_) => "f64".into(),
            Value::Str(_) => "String".into(),
            Value::Atom(a) if a.args.is_empty() => format!("#{}", a.name),
            Value::Atom(a) => format!("#{}(..)", a.name),
            Value::Tuple(_) | Value::Path(_) => "(..)".into(),
            Value::Family(_) => "_ ->? _".into(),
        }
    }

    /// The number's exact place on the extended line. A wide number is borrowed, not copied:
    /// a copy would be built without asking the system for the memory.
    pub(crate) fn exact(&self) -> Exact<'_> {
        match self {
            Value::Int(n) => Exact::Finite(Cow::Owned(Rat::int(BigInt::from(*n)))),
            Value::Big(n) | Value::Rat(n) => Exact::Finite(Cow::Borrowed(n)),
            Value::Float(x) => Exact::float(x.get()),
            _ => unreachable!("only numbers are placed on the line"),
        }
    }

    /// The integer inside, if this is one.
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// The family inside, if this is one.
    pub fn as_family(&self) -> Option<&Family> {
        match self {
            Value::Family(f) => Some(f),
            _ => None,
        }
    }
}

/// A value `Value::key` keeps: anything but a zero, which is made positive.
fn key_leaf(v: &Value) -> Value {
    match v {
        Value::Float(x) if x.get() == 0.0 => Value::float(0.0),
        v => v.clone(),
    }
}

/// Two numbers by value; equal values by kind, `int` before `rat` before a float, and two
/// floats by their total order, which puts `-0.0` before `0.0` and NaN last.
fn number_cmp(a: &Value, b: &Value) -> Ordering {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::Float(x), Value::Float(y)) => x.cmp(y),
        (Value::Rat(x), Value::Rat(y)) => x.cmp(y),
        (Value::Big(x), Value::Big(y)) => x.cmp(y),
        // A `Big` is never in the 64-bit range.
        (Value::Int(_), Value::Big(y)) => match y.is_negative() {
            true => Ordering::Greater,
            false => Ordering::Less,
        },
        (Value::Big(x), Value::Int(_)) => match x.is_negative() {
            true => Ordering::Less,
            false => Ordering::Greater,
        },
        _ => a
            .exact()
            .cmp(&b.exact())
            .then(a.number_kind().cmp(&b.number_kind())),
    }
}

/// Whether two numbers are the same: of one kind and one value, two floats bitwise. Two exact
/// numbers are compared by their normal forms ([`Rat`]'s `==`), which builds nothing unless a
/// coefficient is divisible by a prime the other keeps as a power.
pub(crate) fn number_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Big(x), Value::Big(y)) | (Value::Rat(x), Value::Rat(y)) => x == y,
        (Value::Float(x), Value::Float(y)) => x.cmp(y) == Ordering::Equal,
        _ => false,
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp(self, other)
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Value {
    /// Equal exactly when [`Ord::cmp`] says so. Two families are compared by their maps,
    /// which differ at once in size and skip the nodes they share, so the test of a lattice
    /// `fix` for its fixpoint does not read the whole iterate each round.
    fn eq(&self, other: &Self) -> bool {
        use Value::*;
        match (self, other) {
            (Family(a), Family(b)) => a == b,
            (Tuple(a), Tuple(b)) | (Path(a), Path(b)) => a == b,
            (Atom(a), Atom(b)) => a == b,
            _ if self.kind() == 2 && other.kind() == 2 => number_eq(self, other),
            _ => self.scalar_cmp(other) == Ordering::Equal,
        }
    }
}

impl Eq for Value {}

impl From<i64> for Value {
    fn from(n: i64) -> Self {
        Value::Int(n)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::str(s)
    }
}

impl From<Family> for Value {
    fn from(f: Family) -> Self {
        Value::Family(f)
    }
}

/// The keys from a family's top level down to one of its leaves.
pub type Keypath = Vec<Value>;

/// The number that names one family, sequence ([`crate::Items`]) or list of field names
/// ([`Fields`]) as it was built, so that provenance can find a family's failures
/// from those of the family it was made from, and a walk can know a shared part met again.
/// Copies share it; a family changed in place takes a new one. Ids are drawn once each and
/// never reused, and a walk only tests them for equality: what it finds does not depend on
/// their values. The empty family, sequence and list have id 0. Other crates draw ids for
/// their own shared nodes from the same source (the premise sets of `zedc::store::cell`).
pub type Id = u64;

/// The ids a thread draws from, a block at a time, so that threads building values do not
/// share one counter.
const BLOCK: Id = 1 << 16;
static BLOCKS: AtomicU64 = AtomicU64::new(1);
thread_local! {
    /// The next id of this thread's block, and the end of the block.
    static NEXT: Cell<(Id, Id)> = const { Cell::new((0, 0)) };
}

/// A new id. Block 0 is never drawn, so nothing built non-empty has id 0.
pub fn fresh_id() -> Id {
    NEXT.with(|next| {
        let (mut id, mut end) = next.get();
        if id == end {
            id = BLOCKS.fetch_add(1, AtomicOrdering::Relaxed) * BLOCK;
            end = id + BLOCK;
        }
        next.set((id + 1, end));
        id
    })
}

/// A finite family. No level of a family is empty except a whole family that has no entries.
/// Its entries sit in a persistent map: a copy of a family costs O(1) whatever its size, and
/// a family one entry larger than another shares all but O(log n) of its nodes with it.
///
/// The second field is the family's [`Id`]: a copy keeps it, and a change takes a new one, so
/// the map is never changed in place except through `Family::extend`. The third is the id of
/// the family this one was made from by adding entries to a copy of its map, 0 for none: the
/// two share all but the nodes the change copied, which provenance reads (`Provenance::origins`).
#[derive(Clone, Default)]
pub struct Family(pub(crate) OrdMap<Value, Value>, Id, Id);

impl Drop for Family {
    fn drop(&mut self) {
        if !self.0.is_empty() {
            free(Part::Map(mem::take(&mut self.0)));
        }
    }
}

impl PartialEq for Family {
    fn eq(&self, other: &Self) -> bool {
        families_eq(self, other)
    }
}

impl Eq for Family {}

impl Ord for Family {
    fn cmp(&self, other: &Self) -> Ordering {
        families_cmp(self, other)
    }
}

impl PartialOrd for Family {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// An entry of a level being built. A leaf may hold a whole family, shared, until a leaf beneath
/// it is added, when its top level is expanded into a level of its own.
enum Slot {
    Leaf(Value),
    /// The index of the level beneath.
    Inner(usize),
}

/// The levels of a family being built, the top one first. A level beneath another is always
/// added after it, so a deep keypath needs no recursion to walk or to finish.
struct Levels(Vec<BTreeMap<Value, Slot>>);

impl Levels {
    /// The level beneath `key` of level `at`, added if there is none, a leaf holding a family
    /// expanded. `None` when a leaf is there.
    fn descend(&mut self, at: usize, key: Value) -> Option<usize> {
        let next = self.0.len();
        let slot = self.0[at].entry(key).or_insert(Slot::Inner(next));
        let level = match &*slot {
            Slot::Inner(i) if *i == next => BTreeMap::new(),
            Slot::Inner(i) => return Some(*i),
            Slot::Leaf(Value::Family(f)) => f
                .iter()
                .map(|(k, v)| (k.clone(), Slot::Leaf(v.clone())))
                .collect(),
            Slot::Leaf(_) => return None,
        };
        *slot = Slot::Inner(next);
        self.0.push(level);
        Some(next)
    }

    /// Puts the nonempty family `sub` at `path` as one shared leaf, and returns true, when no
    /// leaf is at `path` and none above it. Otherwise returns false, having added only levels
    /// that the leaves of `sub` would add.
    fn place(&mut self, path: &[Value], sub: &Family) -> bool {
        let (last, above) = path.split_last().expect("keypaths are nonempty");
        let mut at = 0;
        for key in above {
            match self.descend(at, key.key()) {
                Some(next) => at = next,
                None => return false,
            }
        }
        match self.0[at].entry(last.key()) {
            Entry::Occupied(_) => false,
            Entry::Vacant(slot) => {
                slot.insert(Slot::Leaf(Value::Family(sub.clone())));
                true
            }
        }
    }

    /// Adds `leaf` at `path`, which `path` reports if it collides.
    fn insert(&mut self, path: &[Value], leaf: Value) -> Result<(), KernelError> {
        let collision = || KernelError::Collision {
            keypath: path.to_vec(),
        };
        let (last, above) = path.split_last().expect("keypaths are nonempty");
        let mut at = 0;
        for key in above {
            at = self.descend(at, key.key()).ok_or_else(collision)?;
        }
        match self.0[at].entry(last.key()) {
            Entry::Occupied(_) => Err(collision()),
            Entry::Vacant(slot) => {
                slot.insert(Slot::Leaf(leaf));
                Ok(())
            }
        }
    }

    /// The family, each level built after the levels beneath it.
    fn into_family(self) -> Family {
        let mut built = Vec::new();
        built.resize_with(self.0.len(), Family::new);
        for (i, level) in self.0.into_iter().enumerate().rev() {
            let entries = level.into_iter().map(|(k, slot)| match slot {
                Slot::Leaf(v) => (k, v),
                Slot::Inner(j) => (k, Value::Family(mem::take(&mut built[j]))),
            });
            let family = Family::from_map(entries.collect());
            built[i] = family;
        }
        built.swap_remove(0)
    }
}

impl Family {
    /// The family with no entries.
    pub fn new() -> Self {
        Family::default()
    }

    /// The family of the entries `map`, with an id of its own.
    pub(crate) fn from_map(map: OrdMap<Value, Value>) -> Self {
        Family::made_from(map, 0)
    }

    /// The family of the entries `map`, made by adding entries to a copy of the map of the
    /// family whose id is `from`.
    fn made_from(map: OrdMap<Value, Value>, from: Id) -> Self {
        match map.is_empty() {
            true => Family::default(),
            false => Family(map, fresh_id(), from),
        }
    }

    /// The family's id.
    pub(crate) fn id(&self) -> Id {
        self.1
    }

    /// The id of the family this one was made from, 0 for none.
    pub(crate) fn from(&self) -> Id {
        self.2
    }

    /// A one-level family written out as a literal. A value that is an empty family drops
    /// its key.
    ///
    /// # Panics
    ///
    /// Panics when a key repeats, since a literal with two writers for one keypath is a
    /// mistake in the code that builds it.
    pub fn of<K: Into<Value>, V: Into<Value>>(entries: impl IntoIterator<Item = (K, V)>) -> Self {
        let leaves = entries.into_iter().map(|(k, v)| (vec![k.into()], v.into()));
        Family::from_leaves(leaves).expect("a family literal repeats a key")
    }

    /// A set: each key maps to itself, as a set leaf does, so a membership lookup yields
    /// the element (sec:kernel, `discard`).
    pub fn set<K: Into<Value>>(keys: impl IntoIterator<Item = K>) -> Self {
        Family::from_map(
            keys.into_iter()
                .map(|k| {
                    let k = k.into().key();
                    (k.clone(), k)
                })
                .collect(),
        )
    }

    /// Builds a family from its leaves. A leaf whose value is a family contributes that
    /// family's leaves beneath it, sharing the family when nothing else is written there.
    /// Fails with [`KernelError::Collision`] when two leaves
    /// share a keypath, or one leaf's keypath is a prefix of another's, and with
    /// [`KernelError::EmptyKeypath`] for a leaf with no keys.
    pub fn from_leaves(
        leaves: impl IntoIterator<Item = (Keypath, Value)>,
    ) -> Result<Self, KernelError> {
        let mut levels = Levels(vec![BTreeMap::new()]);
        for (path, value) in leaves {
            let path: Keypath = path;
            if path.is_empty() {
                return Err(KernelError::EmptyKeypath);
            }
            match value {
                Value::Family(sub) if sub.is_empty() || levels.place(&path, &sub) => {}
                Value::Family(sub) => {
                    for (mut sub_path, leaf) in sub.leaves() {
                        let mut whole = path.clone();
                        whole.append(&mut sub_path);
                        levels.insert(&whole, leaf)?;
                    }
                }
                leaf => levels.insert(&path, leaf)?,
            }
        }
        Ok(levels.into_family())
    }

    /// The leaves with their keypaths, in keypath order.
    pub fn leaves(&self) -> Vec<(Keypath, Value)> {
        let mut out = Vec::new();
        let mut prefix = Vec::new();
        let mut level = self.0.iter();
        let mut above = Vec::new();
        loop {
            match level.next() {
                Some((k, Value::Family(sub))) => {
                    prefix.push(k.clone());
                    above.push(mem::replace(&mut level, sub.0.iter()));
                }
                Some((k, leaf)) => {
                    prefix.push(k.clone());
                    out.push((prefix.clone(), leaf.clone()));
                    prefix.pop();
                }
                None => match above.pop() {
                    Some(outer) => {
                        level = outer;
                        prefix.pop();
                    }
                    None => return out,
                },
            }
        }
    }

    /// The value at key `k` of the top level.
    pub fn get(&self, k: &Value) -> Option<&Value> {
        // Copied only when it holds a `-0.0`, which its key does not.
        match k.is_key() {
            true => self.0.get(k),
            false => self.0.get(&k.key()),
        }
    }

    /// The top-level entries, in key order.
    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> {
        self.0.iter()
    }

    /// The top-level keys, in order.
    pub fn keys(&self) -> impl Iterator<Item = &Value> {
        self.0.keys()
    }

    /// The union of two families: the leaves of both, where a keypath both write holds the
    /// same leaf in each. Fails with [`KernelError::Collision`], at the first such keypath in
    /// order, when the leaves differ or one family has a leaf above the other's subtree. It
    /// costs O(m log n) for the smaller size m and the larger n: the larger family's entries
    /// are shared, not copied.
    pub fn union(&self, other: &Family) -> Result<Family, KernelError> {
        union(self, other)
    }

    /// Adds the entries at the top level, sharing all but O(m log n) of the map's nodes with the
    /// family it was cloned from, for m entries.
    pub(crate) fn extend(&mut self, entries: impl IntoIterator<Item = (Value, Value)>) {
        self.0.extend(entries);
        if !self.0.is_empty() {
            self.2 = self.1;
            self.1 = fresh_id();
        }
    }

    /// The changes from `self`'s top level to `other`'s, or `None` once there are `limit` of
    /// them. The walk skips the nodes the two maps share. A value at a key both hold is compared
    /// shallowly: a family inside it that does not share its map with the one it is compared
    /// with differs, unread, so an entry listed as changed may be equal. With `==`, each such
    /// family is read down to its first difference, which on nested families made one from
    /// another is as deep as they are (COMPLEXITY.md K25).
    pub(crate) fn shallow_diff<'a>(
        &'a self,
        other: &'a Family,
        limit: usize,
    ) -> Option<Vec<DiffItem<'a, 'a, Value, Value>>> {
        /// Clears [`SHALLOW`] when the walk ends.
        struct Shallow;
        impl Drop for Shallow {
            fn drop(&mut self) {
                SHALLOW.set(false);
            }
        }
        SHALLOW.set(true);
        let _shallow = Shallow;
        let mut out = Vec::new();
        for d in self.0.diff(&other.0) {
            if out.len() >= limit {
                return None;
            }
            out.push(d);
        }
        Some(out)
    }

    /// The number of top-level entries.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the family has no entries.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// One level of a union in progress: the larger family, the smaller family's entries yet to
/// add, and the entries so far.
struct Merging<'a> {
    big: &'a Family,
    left: Iter<'a, Value, Value, DefaultSharedPtr>,
    small_is_b: bool,
    out: OrdMap<Value, Value>,
}

impl<'a> Merging<'a> {
    fn new(a: &'a Family, b: &'a Family) -> Self {
        let small_is_b = a.len() >= b.len();
        let (big, small) = if small_is_b { (a, b) } else { (b, a) };
        Merging {
            big,
            left: small.0.iter(),
            small_is_b,
            out: big.0.clone(),
        }
    }
}

/// The union of `a` and `b`. A collision is reported as building `a`'s leaves and then `b`'s
/// would report it: at `b`'s leaf, or, where `a` has a leaf above a subtree of `b`, at the
/// subtree's first leaf.
fn union(a: &Family, b: &Family) -> Result<Family, KernelError> {
    let mut prefix = Vec::new();
    let mut level = Merging::new(a, b);
    let mut above = Vec::new();
    loop {
        let Some((k, s)) = level.left.next() else {
            let Some(outer) = above.pop() else {
                return Ok(Family::made_from(level.out, level.big.id()));
            };
            let inner = mem::replace(&mut level, outer);
            let key = prefix
                .pop()
                .expect("each level beneath the top has its key");
            level.out.insert(
                key,
                Value::Family(Family::made_from(inner.out, inner.big.id())),
            );
            continue;
        };
        let big = level.big;
        let Some(g) = big.0.get(k) else {
            level.out.insert(k.clone(), s.clone());
            continue;
        };
        let (x, y) = if level.small_is_b { (g, s) } else { (s, g) };
        prefix.push(k.clone());
        match (x, y) {
            (Value::Family(x), Value::Family(y)) => {
                above.push(mem::replace(&mut level, Merging::new(x, y)));
            }
            (Value::Family(_), _) => return Err(collision(&prefix)),
            (_, Value::Family(y)) => {
                let mut sub = y;
                loop {
                    let (k, v) = sub.0.get_min().expect("no level of a family is empty");
                    prefix.push(k.clone());
                    match v {
                        Value::Family(f) => sub = f,
                        _ => return Err(collision(&prefix)),
                    }
                }
            }
            (x, y) if x == y => {
                prefix.pop();
                level.out.insert(k.clone(), x.clone());
            }
            _ => return Err(collision(&prefix)),
        }
    }
}

fn collision(keypath: &Keypath) -> KernelError {
    KernelError::Collision {
        keypath: keypath.clone(),
    }
}

/// The ids of two shared sequences under comparison ([`Items::id`]).
pub(crate) type Pair = (Id, Id);

/// A part of a value whose owner is being dropped. A family's map is freed whole: the map's own
/// nodes nest only as deep as its height, and the values inside it land here in turn.
#[expect(dead_code, reason = "a part is held only to be dropped")]
pub(crate) enum Part {
    Items(Arc<[Value]>),
    Map(OrdMap<Value, Value>),
}

thread_local! {
    /// The parts of values waiting to be dropped.
    static PARTS: Queue<Part> = const { Queue::new() };
    /// Whether a comparison further up this thread's stack is already reading [`PAIRS`].
    static COMPARING: Cell<bool> = const { Cell::new(false) };
    /// The pairs of families a comparison has yet to read.
    static PAIRS: RefCell<Vec<(Family, Family)>> = const { RefCell::new(Vec::new()) };
    /// How many comparisons are running on this thread, one inside another: `diff` calls `==`
    /// on the entries it finds, which starts a comparison inside the one that called `diff`.
    static SCOPES: Cell<usize> = const { Cell::new(0) };
    /// The pairs of shared sequences and of families that the comparisons running on this
    /// thread have read to their end with no difference, by relation, and the pairs of
    /// families an identity comparison has queued. Emptied when the outermost one ends.
    static READ: RefCell<HashSet<Read, BuildHasherDefault<KeyHasher>>> =
        RefCell::new(HashSet::default());
    /// Whether [`Family::shallow_diff`] is running: two families that do not share their map
    /// are then taken to differ, without reading them.
    static SHALLOW: Cell<bool> = const { Cell::new(false) };
}

/// The pairs a comparison reads are kept while it and every comparison it starts run
/// ([`READ`]). Sequences and families draw their ids from one counter, no id is drawn twice,
/// and a value with an id is never changed, so a pair read once has the same answer wherever
/// the comparison meets it again.
struct Scope;

impl Scope {
    fn enter() -> Scope {
        SCOPES.set(SCOPES.get() + 1);
        Scope
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        let left = SCOPES.get() - 1;
        SCOPES.set(left);
        if left == 0 {
            let read = READ.with_borrow_mut(mem::take);
            drop(read);
        }
    }
}

/// A pair of ids read under a relation. It hashes as three words: the derived hash writes the
/// relation's discriminant a byte at a time.
#[derive(PartialEq, Eq)]
struct Read(Pair, Relation);

impl Hash for Read {
    fn hash<H: Hasher>(&self, h: &mut H) {
        h.write_u64(self.0.0);
        h.write_u64(self.0.1);
        h.write_u64(self.1 as u64);
    }
}

/// Whether a comparison running on this thread has read `pair` under `r` already.
fn was_read(pair: Pair, r: Relation) -> bool {
    READ.with_borrow(|read| read.contains(&Read(pair, r)))
}

/// Records that `pair` was read under `r`; false when it was already.
fn mark_read(pair: Pair, r: Relation) -> bool {
    READ.with_borrow_mut(|read| read.insert(Read(pair, r)))
}

/// Drops `part`. A drop reached from inside this one queues its part and returns, so a chain of
/// parts is freed in a loop, whichever containers lie between them.
pub(crate) fn free(part: Part) {
    deep::free_in(&PARTS, part);
}

/// Which relation a walk over two values computes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Relation {
    /// The total order of [`Ord`].
    Total,
    /// Equality of [`PartialEq`], the ties of the total order. It tests sizes first, and it
    /// reads two families with `diff`, which skips the nodes they share.
    Identity,
    /// The language's `==`: [`Relation::Identity`] with IEEE 754 floats.
    SurfaceEq,
    /// The language's order: IEEE 754 floats, and tuples by component.
    SurfaceOrder,
    /// The order `min` selects the lesser of: [`Relation::Total`], except that of two floats
    /// that differ the one IEEE 754-2019 `minimum` gives is the lesser, so a NaN is below
    /// every other float and `-0.0` below `0.0`.
    Min,
    /// The order `max` selects the greater of: [`Relation::Total`], except that of two floats
    /// that differ the one IEEE 754-2019 `maximum` gives is the greater, so a NaN is above
    /// every other float and `-0.0` below `0.0`.
    Max,
}

/// The two sequences of entries under comparison at one depth.
enum Level<'a> {
    /// The two sequences, and the pair of their ids when either is shared, so a pair
    /// met again through the sharing is not read again.
    Items(
        slice::Iter<'a, Value>,
        slice::Iter<'a, Value>,
        Relation,
        Option<Pair>,
    ),
    /// On the heap: a map iterator is many times the size of a slice iterator, and tuples
    /// are the common level.
    Maps(Box<MapLevel<'a>>),
}

/// The entries of two families under comparison.
struct MapLevel<'a> {
    a: Iter<'a, Value, Value, DefaultSharedPtr>,
    b: Iter<'a, Value, Value, DefaultSharedPtr>,
    /// The values of the entry whose keys were compared last.
    values: Option<(&'a Value, &'a Value)>,
    relation: Relation,
    /// The ids of the two families.
    pair: Pair,
}

/// What one comparison found.
enum Step<'a> {
    /// The two are the same so far.
    Same,
    /// The result of the whole walk: a difference, or `None` for an unordered pair.
    Ends(Option<Ordering>),
    /// The two are the same only if their parts are.
    Enter(Level<'a>),
    /// The level has no entries left on either side.
    Done,
}

fn items<'a>(a: &'a Items, b: &'a Items, r: Relation) -> Step<'a> {
    match r {
        // One shared sequence is bitwise equal to itself; the IEEE 754 relations read it,
        // since a NaN inside is not equal to itself.
        Relation::Identity | Relation::Total | Relation::Min | Relation::Max if a.same(b) => {
            Step::Same
        }
        // `min` and `max` take two tuples of one length only.
        Relation::Identity | Relation::SurfaceEq | Relation::Min | Relation::Max
            if a.len() != b.len() =>
        {
            Step::Ends(None)
        }
        _ => Step::Enter(Level::Items(a.iter(), b.iter(), r, Items::pair(a, b))),
    }
}

fn atoms<'a>(a: &'a Atom, b: &'a Atom, r: Relation) -> Step<'a> {
    match a.name.cmp(&b.name).then_with(|| a.fields.cmp(&b.fields)) {
        Ordering::Equal => items(&a.args, &b.args, r),
        o => Step::Ends(Some(o)),
    }
}

fn maps<'a>(a: &'a Family, b: &'a Family, r: Relation) -> Step<'a> {
    let same = a.0.ptr_eq(&b.0);
    let pair = (a.id(), b.id());
    match r {
        Relation::Identity | Relation::SurfaceEq if a.len() != b.len() => Step::Ends(None),
        Relation::Identity if same => Step::Same,
        Relation::Identity if SHALLOW.get() => Step::Ends(None),
        // The comparison is the same only if every queued pair is, so a pair queued once is
        // not queued again.
        Relation::Identity if !mark_read(pair, r) => Step::Same,
        Relation::Identity => {
            // A family is copied by a reference count, so the queue holds no data.
            PAIRS.with_borrow_mut(|pairs| pairs.push((a.clone(), b.clone())));
            Step::Same
        }
        Relation::Total | Relation::Min | Relation::Max if same => Step::Same,
        _ if was_read(pair, r) => Step::Same,
        _ => Step::Enter(Level::Maps(Box::new(MapLevel {
            a: a.0.iter(),
            b: b.0.iter(),
            values: None,
            relation: r,
            pair,
        }))),
    }
}

/// Compares two values as far as their top level decides.
fn step<'a>(a: &'a Value, b: &'a Value, r: Relation) -> Step<'a> {
    match (a, b, r) {
        (Value::Float(x), Value::Float(y), Relation::SurfaceEq) => match x.get() == y.get() {
            true => Step::Same,
            false => Step::Ends(None),
        },
        (Value::Float(x), Value::Float(y), Relation::SurfaceOrder) => {
            match x.get().partial_cmp(&y.get()) {
                Some(Ordering::Equal) => Step::Same,
                o => Step::Ends(o),
            }
        }
        // `min` and `max` order two values of one kind only, as at the top level.
        (_, _, Relation::Min | Relation::Max)
            if a.number_kind() != b.number_kind()
                || (a.number_kind().is_none() && mem::discriminant(a) != mem::discriminant(b)) =>
        {
            Step::Ends(None)
        }
        (Value::Float(x), Value::Float(y), Relation::Min | Relation::Max) if x == y => Step::Same,
        (Value::Float(x), Value::Float(y), Relation::Min | Relation::Max) => {
            let min = r == Relation::Min;
            // The float `minimum` or `maximum` gives is the lesser under `Min` and the greater
            // under `Max`; two floats that differ bitwise are never both given.
            let first = F64::new(ieee_min_max(min, x.get(), y.get())) == *x;
            Step::Ends(Some(if first == min {
                Ordering::Less
            } else {
                Ordering::Greater
            }))
        }
        // Two numbers are equal by their normal forms, which reads no bounds on their values;
        // only a coefficient divisible by a prime the other keeps as a power is copied, and
        // under a watched run that copy asks for its memory first (`Rat`'s `==`).
        (_, _, Relation::Identity | Relation::SurfaceEq)
            if a.number_kind().is_some() && b.number_kind().is_some() =>
        {
            match number_eq(a, b) {
                true => Step::Same,
                false => Step::Ends(None),
            }
        }
        (Value::Tuple(x), Value::Tuple(y), _) => items(x, y, r),
        // Beneath its tuples the language's order is the total order, read in this walk so
        // that the pairs it reads are kept with the others.
        (_, _, Relation::SurfaceOrder) => step(a, b, Relation::Total),
        (Value::Path(x), Value::Path(y), _) => items(x, y, r),
        (Value::Atom(x), Value::Atom(y), _) => atoms(x, y, r),
        (Value::Family(x), Value::Family(y), _) => maps(x, y, r),
        _ => match a.scalar_cmp(b) {
            Ordering::Equal => Step::Same,
            o => Step::Ends(Some(o)),
        },
    }
}

/// The end of a level at which one side has `a` left and the other `b`.
fn side<'a>(a: bool, b: bool) -> Step<'a> {
    match (a, b) {
        (false, false) => Step::Done,
        (false, true) => Step::Ends(Some(Ordering::Less)),
        (true, _) => Step::Ends(Some(Ordering::Greater)),
    }
}

/// Takes the next entry of `level`.
fn advance<'a>(level: &mut Level<'a>) -> Step<'a> {
    match level {
        Level::Items(a, b, r, _) => match (a.next(), b.next()) {
            (Some(x), Some(y)) => step(x, y, *r),
            (x, y) => side(x.is_some(), y.is_some()),
        },
        Level::Maps(level) => {
            if let Some((v, w)) = level.values.take() {
                return step(v, w, level.relation);
            }
            match (level.a.next(), level.b.next()) {
                (Some((k, v)), Some((l, w))) => {
                    level.values = Some((v, w));
                    // Keys are compared bitwise whichever relation the values are compared by.
                    step(k, l, Relation::Total)
                }
                (x, y) => side(x.is_some(), y.is_some()),
            }
        }
    }
}

/// Runs a walk from its first step to the first difference. `None` is an unordered pair; a walk
/// that ends without one gives `Some(Equal)`. A flat value needs no heap: the stack holds only
/// the levels above the one in hand. Shared tuples make a value a DAG, so a pair of shared
/// sequences or of families read to its end is kept, and met again it is the same without a
/// second reading: the walk is O(distinct pairs), not O(paths). The pairs are kept in [`READ`]
/// until the outermost comparison ends, so the comparisons that `diff` starts share them.
fn walk(first: Step<'_>) -> Option<Ordering> {
    let mut level = match first {
        Step::Same | Step::Done => return Some(Ordering::Equal),
        Step::Ends(o) => return o,
        Step::Enter(level) => level,
    };
    let _scope = Scope::enter();
    if let Level::Items(.., r, Some(pair)) = &level
        && was_read(*pair, *r)
    {
        return Some(Ordering::Equal);
    }
    let mut above = Vec::new();
    loop {
        match advance(&mut level) {
            Step::Same => {}
            Step::Ends(o) => return o,
            Step::Enter(Level::Items(.., r, Some(pair))) if was_read(pair, r) => {}
            Step::Enter(inner) => above.push(mem::replace(&mut level, inner)),
            Step::Done => {
                match &level {
                    Level::Items(.., r, Some(pair)) => _ = mark_read(*pair, *r),
                    Level::Maps(m) => _ = mark_read(m.pair, m.relation),
                    Level::Items(.., None) => {}
                }
                match above.pop() {
                    Some(outer) => level = outer,
                    None => return Some(Ordering::Equal),
                }
            }
        }
    }
}

/// Finishes an identity walk that found `same` so far by reading the queued families. A walk
/// started while the queue is being read leaves its families in the queue: `diff` calls `==`
/// on the entries it finds, inside imbl, where no stack of ours can reach, and this keeps that
/// call from nesting.
fn settle(same: bool) -> bool {
    if COMPARING.get() {
        return same;
    }
    COMPARING.set(true);
    let mut all = same;
    while all && let Some((a, b)) = PAIRS.with_borrow_mut(Vec::pop) {
        all = a.0.diff(&b.0).next().is_none();
    }
    COMPARING.set(false);
    let left = PAIRS.with_borrow_mut(mem::take);
    drop(left);
    all
}

/// Whether two sequences of values are the same.
pub(crate) fn items_eq(a: &Items, b: &Items) -> bool {
    let _scope = Scope::enter();
    settle(walk(items(a, b, Relation::Identity)) == Some(Ordering::Equal))
}

/// Whether two families are the same.
pub(crate) fn families_eq(a: &Family, b: &Family) -> bool {
    let _scope = Scope::enter();
    settle(walk(maps(a, b, Relation::Identity)) == Some(Ordering::Equal))
}

/// The total order on two sequences of values.
pub(crate) fn items_cmp(a: &Items, b: &Items) -> Ordering {
    walk(items(a, b, Relation::Total)).expect("the total order orders every pair")
}

/// The total order on two families.
pub(crate) fn families_cmp(a: &Family, b: &Family) -> Ordering {
    walk(maps(a, b, Relation::Total)).expect("the total order orders every pair")
}

/// The total order on two values.
pub(crate) fn cmp(a: &Value, b: &Value) -> Ordering {
    walk(step(a, b, Relation::Total)).expect("the total order orders every pair")
}

/// The language's `==`.
pub(crate) fn surface_eq(a: &Value, b: &Value) -> bool {
    walk(step(a, b, Relation::SurfaceEq)) == Some(Ordering::Equal)
}

/// The language's order; `None` when the two are unordered.
pub(crate) fn surface_cmp(a: &Value, b: &Value) -> Option<Ordering> {
    walk(step(a, b, Relation::SurfaceOrder))
}

/// What a sequence of copied values is rebuilt into.
enum Shape<'a> {
    Tuple,
    Path,
    Atom(&'a Atom),
}

impl Shape<'_> {
    fn wrap(&self, items: Items) -> Value {
        match self {
            Shape::Tuple => Value::Tuple(items),
            Shape::Path => Value::Path(items),
            Shape::Atom(a) => Value::Atom(Atom {
                name: a.name.clone(),
                fields: a.fields.clone(),
                args: items,
            }),
        }
    }
}

/// A sequence of values being copied.
struct Copying<'a> {
    left: slice::Iter<'a, Value>,
    done: Vec<Value>,
    shape: Shape<'a>,
    /// The id of the sequence copied, when it is shared and so can be met again.
    shared: Option<Id>,
}

impl<'a> Copying<'a> {
    fn new(from: &'a [Value], shape: Shape<'a>, shared: Option<Id>) -> Self {
        Copying {
            left: from.iter(),
            done: Vec::with_capacity(from.len()),
            shape,
            shared,
        }
    }
}

/// Copies `from`, tuples, keypaths and atoms' payloads to any depth, and every other value
/// through `leaf`. A shared sequence is copied once, and its copy is shared in the same places,
/// so the copy of a DAG is a DAG of the same size.
pub(crate) fn copy(from: &[Value], leaf: fn(&Value) -> Value) -> Vec<Value> {
    let mut level = Copying::new(from, Shape::Tuple, None);
    let mut above = Vec::new();
    let mut copied: HashMap<Id, Items> = HashMap::new();
    loop {
        let (xs, shape) = match level.left.next() {
            Some(Value::Tuple(xs)) => (xs, Shape::Tuple),
            Some(Value::Path(xs)) => (xs, Shape::Path),
            Some(Value::Atom(a)) => (&a.args, Shape::Atom(a)),
            Some(v) => {
                level.done.push(leaf(v));
                continue;
            }
            None => match above.pop() {
                Some(outer) => {
                    let inner = mem::replace(&mut level, outer);
                    let items = Items::from(inner.done);
                    if let Some(at) = inner.shared {
                        copied.insert(at, items.clone());
                    }
                    level.done.push(inner.shape.wrap(items));
                    continue;
                }
                None => return level.done,
            },
        };
        let shared = xs.is_shared().then(|| xs.id());
        match shared.and_then(|at| copied.get(&at)) {
            Some(items) => level.done.push(shape.wrap(items.clone())),
            None => above.push(mem::replace(&mut level, Copying::new(xs, shape, shared))),
        }
    }
}

/// Whether `test` holds of every value in `from`, tuples, keypaths and atoms' payloads read to
/// any depth, stopping at the first that fails. A shared sequence is read once.
pub(crate) fn all_leaves(from: &[Value], test: fn(&Value) -> bool) -> bool {
    let mut level = from.iter();
    let mut above = Vec::new();
    let mut read = HashSet::new();
    loop {
        let inner = match level.next() {
            Some(Value::Tuple(xs) | Value::Path(xs)) => xs,
            Some(Value::Atom(a)) => &a.args,
            Some(v) if test(v) => continue,
            Some(_) => return false,
            None => match above.pop() {
                Some(outer) => {
                    level = outer;
                    continue;
                }
                None => return true,
            },
        };
        if inner.is_shared() && !read.insert(inner.id()) {
            continue;
        }
        above.push(mem::replace(&mut level, inner.iter()));
    }
}

/// What is left to write.
enum Task<'a> {
    Text(&'a str),
    Quoted(&'a str),
    Show(&'a Value),
    Debug(&'a Value),
    Family(&'a Family),
    DebugFamily(&'a Family),
}

/// `list` as tasks in reverse, each entry after the first preceded by `sep`, for a stack.
fn push_list<'a>(
    todo: &mut Vec<Task<'a>>,
    list: &'a [Value],
    sep: &'static str,
    task: fn(&'a Value) -> Task<'a>,
) {
    for (i, v) in list.iter().enumerate().rev() {
        todo.push(task(v));
        if i > 0 {
            todo.push(Task::Text(sep));
        }
    }
}

fn show_atom<'a>(a: &'a Atom, todo: &mut Vec<Task<'a>>) {
    if a.args.is_empty() {
        return;
    }
    todo.push(Task::Text(")"));
    for (i, v) in a.args.iter().enumerate().rev() {
        todo.push(Task::Show(v));
        if let Some(k) = a.fields.get(i) {
            todo.extend([Task::Text(": "), Task::Text(k)]);
        }
        if i > 0 {
            todo.push(Task::Text(", "));
        }
    }
    todo.push(Task::Text("("));
}

fn show_family<'a>(fam: &'a Family, todo: &mut Vec<Task<'a>>) {
    // A set, each leaf its own key (`k -> k`), is written by its members.
    let set = !fam.is_empty() && fam.0.iter().all(|(k, v)| k == v);
    todo.push(Task::Text("}"));
    let last = fam.len();
    for (i, (k, v)) in fam.0.iter().rev().enumerate() {
        if !set {
            todo.extend([Task::Show(v), Task::Text(" -> ")]);
        }
        todo.push(Task::Show(k));
        if i + 1 < last {
            todo.push(Task::Text(", "));
        }
    }
    todo.push(Task::Text("{"));
}

/// The form of `{}`: one step of showing `v`.
fn show<'a>(v: &'a Value, f: &mut fmt::Formatter<'_>, todo: &mut Vec<Task<'a>>) -> fmt::Result {
    match v {
        Value::Bool(b) => write!(f, "{b}"),
        Value::Int(n) => write!(f, "{n}"),
        Value::Big(n) => write!(f, "{}", n.numer_text()),
        Value::Rat(r) => write!(f, "{r}"),
        Value::Float(x) => write!(f, "{}", crate::num::show_f64(x.get())),
        Value::Str(s) => write!(f, "{s:?}"),
        Value::Atom(a) => {
            show_atom(a, todo);
            todo.push(Task::Text(&a.name));
            f.write_str("#")
        }
        Value::Tuple(items) => {
            // A one-tuple is `(x,)`, as its type `(T,)` is written: `(x)` is `x` in brackets.
            todo.push(Task::Text(if items.len() == 1 { ",)" } else { ")" }));
            push_list(todo, items, ", ", Task::Show);
            f.write_str("(")
        }
        Value::Path(keys) => {
            todo.push(Task::Text("]"));
            push_list(todo, keys, " -> ", Task::Show);
            f.write_str("[")
        }
        Value::Family(fam) => {
            todo.push(Task::Family(fam));
            Ok(())
        }
    }
}

fn debug_list<'a>(todo: &mut Vec<Task<'a>>, list: &'a [Value], close: &'static str) {
    todo.push(Task::Text(close));
    push_list(todo, list, ", ", Task::Debug);
}

fn debug_family<'a>(fam: &'a Family, todo: &mut Vec<Task<'a>>) {
    todo.push(Task::Text("})"));
    let last = fam.len();
    for (i, (k, v)) in fam.0.iter().rev().enumerate() {
        todo.extend([Task::Debug(v), Task::Text(": "), Task::Debug(k)]);
        if i + 1 < last {
            todo.push(Task::Text(", "));
        }
    }
    todo.push(Task::Text("Family({"));
}

/// The form of `{:?}`, as a derived `Debug` prints it: one step of showing `v`.
fn debug<'a>(v: &'a Value, f: &mut fmt::Formatter<'_>, todo: &mut Vec<Task<'a>>) -> fmt::Result {
    match v {
        Value::Bool(b) => write!(f, "Bool({b:?})"),
        Value::Int(n) => write!(f, "Int({n:?})"),
        Value::Big(n) => write!(f, "Big({n:?})"),
        Value::Rat(r) => write!(f, "Rat({r:?})"),
        Value::Float(x) => write!(f, "Float({x:?})"),
        Value::Str(s) => write!(f, "Str({s:?})"),
        Value::Atom(a) => {
            todo.push(Task::Text(" })"));
            debug_atom(a, todo);
            f.write_str("Atom(")
        }
        Value::Tuple(items) => {
            debug_list(todo, items, "])");
            f.write_str("Tuple([")
        }
        Value::Path(keys) => {
            debug_list(todo, keys, "])");
            f.write_str("Path([")
        }
        Value::Family(fam) => {
            todo.extend([Task::Text(")"), Task::DebugFamily(fam)]);
            f.write_str("Family(")
        }
    }
}

/// An atom's fields as tasks, without the closing `}`, which [`debug`] pushes.
fn debug_atom<'a>(a: &'a Atom, todo: &mut Vec<Task<'a>>) {
    debug_list(todo, &a.args, "]");
    todo.push(Task::Text("], args: ["));
    for (i, name) in a.fields.iter().enumerate().rev() {
        todo.push(Task::Quoted(name));
        if i > 0 {
            todo.push(Task::Text(", "));
        }
    }
    todo.extend([
        Task::Text(", fields: ["),
        Task::Quoted(&a.name),
        Task::Text("Atom { name: "),
    ]);
}

fn run<'a>(mut todo: Vec<Task<'a>>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    while let Some(task) = todo.pop() {
        match task {
            Task::Text(s) => f.write_str(s)?,
            Task::Quoted(s) => write!(f, "{s:?}")?,
            Task::Show(v) => show(v, f, &mut todo)?,
            Task::Debug(v) => debug(v, f, &mut todo)?,
            Task::Family(fam) => show_family(fam, &mut todo),
            Task::DebugFamily(fam) => debug_family(fam, &mut todo),
        }
    }
    Ok(())
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Task::Show(self)], f)
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Task::Debug(self)], f)
    }
}

impl fmt::Display for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Task::Family(self)], f)
    }
}

impl fmt::Debug for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Task::DebugFamily(self)], f)
    }
}

impl fmt::Debug for Items {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("[")?;
        let mut todo = Vec::new();
        debug_list(&mut todo, self, "]");
        run(todo, f)
    }
}

/// Why a kernel evaluation stopped without a value.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum KernelError {
    /// Two entries were written to one keypath, or one entry's keypath is a prefix of
    /// another's: the collision rule (sec:grouping), the premise of T-Reindex.
    Collision {
        /// The keypath written twice.
        keypath: Keypath,
    },
    /// A leaf with no keys, which only a key map that returns an empty keypath can make.
    EmptyKeypath,
    /// A fold met a family with a leaf at another depth than the fold's, so it has no one
    /// level to collapse.
    MixedDepth,
    /// A value had the wrong shape for the construct reading it, which a well-typed term
    /// never does.
    Type(String),
    /// The term named a port the world does not have.
    UnknownPort(String),
    /// A lookup port could not answer a read: the port and why.
    Port(String, String),
    /// The evaluation used up its fuel: a `fix` whose ascent or a `gen` that did not stop
    /// within the step budget (sec:generations, divergence).
    OutOfFuel,
    /// A definedness `fix` stopped with these entries undefined: each reads an entry of the
    /// cycle, which is divergence (T-Fix), never `#notFound`.
    Stalled {
        /// The undefined keys, in order.
        keys: Vec<Value>,
    },
    /// An arithmetic operation had to build or read a number in full, and the system refused the
    /// `bits` bits of memory asked for it (sec:domains says when a number is built). The number
    /// is a value of the language; this evaluator cannot run the program on this machine.
    NumberTooLarge {
        /// The operator: `+`, `-`, `div`, `mod`, `**`, `String` printing a number, or `int` or
        /// `rat` reading one from a string.
        op: &'static str,
        /// The memory asked for, in bits: a measured multiple of the number's size, not the size
        /// itself. The message gives it in bytes.
        bits: num_bigint::BigUint,
    },
    /// `String` of a tuple, keypath, atom or family must write a text of up to `bytes` bytes,
    /// the digits of the numbers inside it counted at their widest, and the system refused the
    /// memory for it, with the widest number's build; `None` for more than `u128::MAX` bytes.
    TextTooLarge {
        /// At most this many bytes: the length of the text.
        bytes: Option<u128>,
    },
    /// Two numbers agree in so many leading bits that ordering them, for `<`, `<=`, `>`,
    /// `>=`, `min` or `max`, needs bounds of them, or the two in full, and the system refused
    /// the `bits` bits of memory asked for them.
    OrderTooLarge {
        /// The operator.
        op: &'static str,
        /// The memory asked for, in bits: a measured multiple of the widest bound's or number's
        /// size, not the size itself. The message gives it in bytes.
        bits: num_bigint::BigUint,
    },
    /// `==` or `!=` of two numbers, one of whose coefficients is divisible by a prime the other
    /// keeps as a power, must copy and divide the coefficients to compare their normal forms,
    /// and the system refused the `bits` bits of memory asked for it.
    EqualityTooLarge {
        /// The operator.
        op: &'static str,
        /// The memory asked for, in bits: a measured multiple of the size of the copy and the
        /// division, not the size itself. The message gives it in bytes.
        bits: num_bigint::BigUint,
    },
    /// Two numbers among a family's keys, or a key looked up and one in the family, agree in
    /// so many leading bits that placing them in key order needs bounds of them, or the two in
    /// full, and the system refused the `bits` bits of memory asked for them.
    KeyOrderTooLarge {
        /// The memory asked for, in bits: a measured multiple of the widest bound's or number's
        /// size, not the size itself. The message gives it in bytes.
        bits: num_bigint::BigUint,
    },
    /// Two numbers in families, compared for equality (two leaves written at one keypath, or a
    /// key and its member when a set is printed), must be put in the same normal form, and the
    /// system refused the `bits` bits of memory asked for it.
    FamilyEqualityTooLarge {
        /// The memory asked for, in bits: a measured multiple of the size of the copy and the
        /// division, not the size itself. The message gives it in bytes.
        bits: num_bigint::BigUint,
    },
    /// A number lies so near a rounding boundary of a float that telling which side it is on
    /// needs bounds of it, or the number in full, and the system refused the `bits` bits of
    /// memory asked for them.
    RoundTooLarge {
        /// The float it is rounded to, as the cast is written: `f64`.
        to: &'static str,
        /// The memory asked for, in bits: a measured multiple of the widest bound's or number's
        /// size, not the size itself. The message gives it in bytes.
        bits: num_bigint::BigUint,
    },
    /// `++` of two strings whose lengths in bytes add up past `usize::MAX`, the most a length
    /// holds: the joined string's length is not representable, whatever memory there is.
    StringTooLong {
        /// The left string's length in bytes.
        left: usize,
        /// The right string's length in bytes.
        right: usize,
    },
    /// `lower`, `upper` or `trim` must write a string of `bytes` bytes, and the system refused
    /// the memory for it and for the value's copy of it.
    StringCopyTooLarge {
        /// The word, as the message writes it.
        op: &'static str,
        /// The length of the string written, in bytes.
        bytes: usize,
    },
    /// An atom's name or field name is a joined string of `bytes` bytes, which an atom holds
    /// as one piece, and the system refused the memory to write it so.
    AtomNameTooLarge {
        /// The name's length in bytes.
        bytes: usize,
    },
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelError::Collision { keypath } => {
                write!(f, "collision: two writers for keypath [")?;
                for (i, k) in keypath.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}")?;
                }
                write!(f, "]")
            }
            KernelError::EmptyKeypath => write!(f, "a key map returned an empty keypath"),
            KernelError::MixedDepth => write!(f, "fold over leaves at another depth than its own"),
            KernelError::Type(msg) => write!(f, "type error: {msg}"),
            KernelError::UnknownPort(name) => write!(f, "unknown port `{name}`"),
            KernelError::Port(name, why) => write!(f, "port `{name}`: {why}"),
            KernelError::OutOfFuel => write!(f, "out of fuel"),
            KernelError::Stalled { keys } => {
                write!(f, "recursion stalled: entries ")?;
                for (i, k) in keys.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}")?;
                }
                write!(f, " depend on each other")
            }
            KernelError::NumberTooLarge { op, bits } => write!(
                f,
                "`{op}` must build a number in full, and the system refused the {} bytes of \
                 memory asked for it; the number is exact and has no size limit, but this \
                 machine cannot hold its digits",
                bytes_of(bits)
            ),
            KernelError::TextTooLarge { bytes } => {
                match bytes {
                    Some(n) => write!(f, "`String` must write a text of up to {n} bytes")?,
                    None => write!(
                        f,
                        "`String` must write a text of more than {} bytes",
                        u128::MAX
                    )?,
                }
                write!(
                    f,
                    ", counting each number inside it at its widest, and the system refused the \
                     memory for it; the value has no size limit, but this machine cannot hold \
                     its text"
                )
            }
            KernelError::OrderTooLarge { op, bits } => write!(
                f,
                "`{op}` must compare two numbers that agree in their leading digits, and the \
                 system refused the {} bytes of memory asked to read enough of their digits; \
                 the numbers are exact and have no size limit, but this machine cannot hold \
                 enough of their digits to order them",
                bytes_of(bits)
            ),
            KernelError::EqualityTooLarge { op, bits } => write!(
                f,
                "`{op}` must compare two numbers in the same normal form, which moves a prime \
                 one keeps as a power out of the other's digits, and the system refused the {} \
                 bytes of memory asked for it; the numbers are exact and have no size limit, \
                 but this machine cannot hold enough of their digits to compare them",
                bytes_of(bits)
            ),
            KernelError::KeyOrderTooLarge { bits } => write!(
                f,
                "two numbers placed in a family's key order agree in their leading digits, and \
                 the system refused the {} bytes of memory asked to read enough of their \
                 digits; the numbers are exact and have no size limit, but this machine cannot \
                 hold enough of their digits to order them",
                bytes_of(bits)
            ),
            KernelError::FamilyEqualityTooLarge { bits } => write!(
                f,
                "two numbers in families, compared to tell whether they are equal, must be put \
                 in the same normal form, which moves a prime one keeps as a power out of the \
                 other's digits, and the system refused the {} bytes of memory asked for it; \
                 the numbers are exact and have no size limit, but this machine cannot hold \
                 enough of their digits to compare them",
                bytes_of(bits)
            ),
            KernelError::RoundTooLarge { to, bits } => write!(
                f,
                "`{to}` must round a number that lies near a rounding boundary, and the system \
                 refused the {} bytes of memory asked to read enough of its digits; the number \
                 is exact and has no size limit, but this machine cannot hold enough of its \
                 digits to round it",
                bytes_of(bits)
            ),
            KernelError::StringTooLong { left, right } => write!(
                f,
                "`++` cannot join a string of {left} bytes to one of {right} bytes: the result \
                 would be {} bytes, more than the {} bytes a string's length can hold; keep \
                 the parts apart, as a list of strings written out one at a time, or join \
                 fewer of them",
                *left as u128 + *right as u128,
                usize::MAX
            ),
            KernelError::StringCopyTooLarge { op, bytes } => write!(
                f,
                "`{op}` must write a string of {bytes} bytes, and the system refused the memory \
                 for it; the string has no size limit, but this machine cannot hold the result"
            ),
            KernelError::AtomNameTooLarge { bytes } => write!(
                f,
                "an atom's name or field name is a joined string of {bytes} bytes, which an \
                 atom holds in one piece, and the system refused the memory to write it so; \
                 the string has no size limit, but this machine cannot hold it as a name"
            ),
        }
    }
}

impl std::error::Error for KernelError {}

impl From<TooLong> for KernelError {
    fn from(TooLong { left, right }: TooLong) -> Self {
        KernelError::StringTooLong { left, right }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_value_is_56_bytes() {
        // Each value of every tuple, list and family costs this much; an id in `Items` with an
        // atom's fields two words wide made it 64 and cost 13 to 27% more peak memory on runs
        // without provenance (COMPLEXITY.md K25). The fields are one word wide, so the atom,
        // the widest kind, holds the id in 48 bytes (ADDR-keys).
        assert_eq!(size_of::<Value>(), 56);
        assert_eq!(size_of::<Atom>(), 48);
        assert_eq!(size_of::<Items>(), 24);
        assert_eq!(size_of::<Fields>(), 8);
    }

    #[test]
    fn signed_zeros_differ_and_nans_are_one_value() {
        assert_ne!(Value::float(0.0), Value::float(-0.0));
        assert!(Value::float(-0.0) < Value::float(0.0));
        let other_nan = f64::from_bits(f64::NAN.to_bits() ^ 1);
        assert!(other_nan.is_nan());
        assert_eq!(Value::float(other_nan), Value::float(f64::NAN));
    }

    #[test]
    fn display_forms() {
        assert_eq!(Value::atom("empty").to_string(), "#empty");
        let io = Value::atom_with("ioError", vec![Value::str("disk full")]);
        assert_eq!(io.to_string(), "#ioError(\"disk full\")");
        let t = Value::tuple(vec![Value::Int(1), Value::Bool(true), Value::float(-0.0)]);
        assert_eq!(t.to_string(), "(1, true, -0.0)");
        let p = Value::path(vec![Value::str("ann"), Value::Int(2)]);
        assert_eq!(p.to_string(), r#"["ann" -> 2]"#);
    }

    #[test]
    fn accessors() {
        assert_eq!(Value::Int(3).as_int(), Some(3));
        assert_eq!(Value::str("x").as_int(), None);
        assert!(Value::Int(3).as_family().is_none());
        assert!(Value::from(Family::default()).as_family().is_some());
        assert_eq!(Value::from(true), Value::Bool(true));
        assert_eq!(F64::new(2.5).get(), 2.5);
        assert_eq!(
            F64::new(1.0).partial_cmp(&F64::new(2.0)),
            Some(Ordering::Less)
        );
    }

    fn kp(keys: &[&str]) -> Keypath {
        keys.iter().map(|k| Value::str(k)).collect()
    }

    #[test]
    fn leaves_round_trip_in_keypath_order() {
        let leaves = vec![
            (kp(&["b", "x"]), Value::Int(2)),
            (kp(&["a"]), Value::Int(1)),
            (kp(&["b", "y"]), Value::Int(3)),
        ];
        let f = Family::from_leaves(leaves).unwrap();
        assert_eq!(f.to_string(), r#"{"a" -> 1, "b" -> {"x" -> 2, "y" -> 3}}"#);
        assert_eq!(
            f.leaves(),
            vec![
                (kp(&["a"]), Value::Int(1)),
                (kp(&["b", "x"]), Value::Int(2)),
                (kp(&["b", "y"]), Value::Int(3))
            ]
        );
    }

    #[test]
    fn two_writers_for_one_keypath_collide() {
        let err = Family::from_leaves(vec![
            (kp(&["a"]), Value::Int(1)),
            (kp(&["a"]), Value::Int(1)),
        ])
        .unwrap_err();
        assert_eq!(
            err,
            KernelError::Collision {
                keypath: kp(&["a"])
            }
        );
    }

    #[test]
    fn a_leaf_above_a_subtree_collides_in_either_order() {
        let leaf_first = Family::from_leaves(vec![
            (kp(&["a"]), Value::Int(1)),
            (kp(&["a", "b"]), Value::Int(2)),
        ]);
        assert_eq!(
            leaf_first.unwrap_err(),
            KernelError::Collision {
                keypath: kp(&["a", "b"])
            }
        );
        let subtree_first = Family::from_leaves(vec![
            (kp(&["a", "b"]), Value::Int(2)),
            (kp(&["a"]), Value::Int(1)),
        ]);
        assert_eq!(
            subtree_first.unwrap_err(),
            KernelError::Collision {
                keypath: kp(&["a"])
            }
        );
    }

    #[test]
    fn an_empty_keypath_is_rejected() {
        assert_eq!(
            Family::from_leaves(vec![(vec![], Value::Int(1))]).unwrap_err(),
            KernelError::EmptyKeypath
        );
    }

    #[test]
    fn an_empty_inner_level_drops_its_key() {
        let f = Family::of([("a", Value::Int(1)), ("b", Value::Family(Family::new()))]);
        assert_eq!(f.to_string(), r#"{"a" -> 1}"#);
        assert_eq!(f.len(), 1);
        assert!(!f.is_empty());
        assert!(Family::new().is_empty());
    }

    #[test]
    fn a_set_maps_each_key_to_itself() {
        let s = Family::set([3, 1]);
        assert_eq!(s.to_string(), "{1, 3}", "a set is written by its members");
        assert_eq!(s.get(&Value::Int(3)), Some(&Value::Int(3)));
        assert_eq!(
            s.keys().cloned().collect::<Vec<_>>(),
            vec![Value::Int(1), Value::Int(3)]
        );
        assert_eq!(s.iter().count(), 2);
    }

    #[test]
    #[should_panic(expected = "repeats a key")]
    fn a_literal_with_a_repeated_key_panics() {
        Family::of([("a", 1), ("a", 2)]);
    }

    #[test]
    fn the_two_zeros_are_one_key() {
        let neg = || Value::float(-0.0);
        let f = Family::from_leaves([(vec![neg()], Value::Int(1))]).unwrap();
        assert_eq!(f.to_string(), "{0.0 -> 1}", "the key holds 0.0's bits");
        assert_eq!(f.get(&Value::float(0.0)), Some(&Value::Int(1)));
        assert_eq!(f.get(&neg()), Some(&Value::Int(1)));
        let both = [
            (vec![neg()], Value::Int(1)),
            (vec![Value::float(0.0)], Value::Int(2)),
        ];
        assert!(matches!(
            Family::from_leaves(both),
            Err(KernelError::Collision { .. })
        ));
        // At any depth: inside a tuple key, and at an inner level.
        let t = |z| Value::tuple(vec![Value::str("x"), Value::float(z)]);
        let g = Family::from_leaves([(vec![t(-0.0), neg()], Value::Int(3))]).unwrap();
        assert_eq!(g.to_string(), "{(\"x\", 0.0) -> {0.0 -> 3}}");
        assert_eq!(Family::set([neg(), Value::float(0.0)]).len(), 1);
    }

    #[test]
    fn a_join_past_the_largest_length_is_reported_with_both_lengths() {
        let half = 1usize << 63;
        let e = KernelError::from(TooLong {
            left: half,
            right: half,
        });
        assert_eq!(
            e.to_string(),
            "`++` cannot join a string of 9223372036854775808 bytes to one of \
             9223372036854775808 bytes: the result would be 18446744073709551616 bytes, more \
             than the 18446744073709551615 bytes a string's length can hold; keep the parts \
             apart, as a list of strings written out one at a time, or join fewer of them"
        );
    }

    #[test]
    fn messages() {
        let c = KernelError::Collision {
            keypath: vec![Value::str("ann"), Value::Int(2)],
        };
        assert_eq!(
            c.to_string(),
            r#"collision: two writers for keypath ["ann", 2]"#
        );
        assert_eq!(
            KernelError::EmptyKeypath.to_string(),
            "a key map returned an empty keypath"
        );
        assert_eq!(
            KernelError::MixedDepth.to_string(),
            "fold over leaves at another depth than its own"
        );
        assert_eq!(KernelError::Type("x".into()).to_string(), "type error: x");
        assert_eq!(
            KernelError::UnknownPort("p".into()).to_string(),
            "unknown port `p`"
        );
        assert_eq!(KernelError::OutOfFuel.to_string(), "out of fuel");
        let s = KernelError::Stalled {
            keys: vec![Value::Int(1), Value::Int(2)],
        };
        assert_eq!(
            s.to_string(),
            "recursion stalled: entries 1, 2 depend on each other"
        );
    }
}
