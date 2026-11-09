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
//! has exactly one writer, and an outer key over an empty level is a keypath that ends early,
//! so it is kept (sec:kernel, reference semantics (d)).
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

/// A finite family. A level may be empty: in `{"a" -> {}}` the key `"a"` is a keypath that ends
/// early, with an empty level beneath it, and the family differs from `{}` (DESIGN.md sec:kernel,
/// reference semantics (d)). Its entries sit in a persistent map: a copy of a family costs O(1) whatever its size, and
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

    /// Adds `leaf` at `path`, which `path` reports if it collides. A leaf that is the empty
    /// family is an empty level beneath `path`, which writes no leaf: it collides only with a
    /// leaf at `path`, and merges with any other level there, empty or not.
    fn insert(&mut self, path: &[Value], leaf: Value) -> Result<(), KernelError> {
        let collision = || KernelError::Collision {
            keypath: path.to_vec(),
        };
        let (last, above) = path.split_last().expect("keypaths are nonempty");
        let mut at = 0;
        for key in above {
            at = self.descend(at, key.key()).ok_or_else(collision)?;
        }
        let empty = matches!(&leaf, Value::Family(f) if Family::is_empty(f));
        match self.0[at].entry(last.key()) {
            Entry::Occupied(slot) => match slot.get() {
                Slot::Inner(_) | Slot::Leaf(Value::Family(_)) if empty => Ok(()),
                _ => Err(collision()),
            },
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

    /// A one-level family written out as a literal. A value that is an empty family keeps its
    /// key, with an empty level beneath.
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
    /// family's leaves beneath it, sharing the family when nothing else is written there; a leaf
    /// whose value is the empty family is an empty level beneath its keypath, which merges with
    /// any other level there. Fails with [`KernelError::Collision`] when two leaves
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
                Value::Family(sub) if sub.is_empty() => levels.insert(&path, Value::Family(sub))?,
                Value::Family(sub) if levels.place(&path, &sub) => {}
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

    /// The leaves with their keypaths, in keypath order. A keypath that ends early, above an
    /// empty level, is a leaf whose value is the empty family, so that `from_leaves` of the
    /// leaves is the family again.
    pub fn leaves(&self) -> Vec<(Keypath, Value)> {
        let mut out = Vec::new();
        let mut prefix = Vec::new();
        let mut level = self.0.iter();
        let mut above = Vec::new();
        loop {
            match level.next() {
                Some((k, Value::Family(sub))) if !sub.is_empty() => {
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
    /// family it was cloned from, for m entries. A key already held keeps its value
    /// (`merge_failures` adds a member twice): a family made from another holds each of its
    /// entries, which `provenance::Holds` reads it by.
    pub(crate) fn extend(&mut self, entries: impl IntoIterator<Item = (Value, Value)>) {
        for (k, v) in entries {
            debug_assert!(
                self.0.get(&k).is_none_or(|old| *old == v),
                "an entry of the family is replaced by another value"
            );
            self.0.insert(k, v);
        }
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
    pub(crate) fn shallow_diff<'a, 'b>(
        &'a self,
        other: &'b Family,
        limit: usize,
    ) -> Option<Vec<DiffItem<'a, 'b, Value, Value>>> {
        /// Clears `shallow` ([`Comparisons`]) when the walk ends.
        struct Shallow;
        impl Drop for Shallow {
            fn drop(&mut self) {
                COMPARISONS.with(|c| c.shallow.set(false));
            }
        }
        COMPARISONS.with(|c| c.shallow.set(true));
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
                    // A leaf of `x` above an empty level of `y` collides at the leaf's keypath.
                    let Some((k, v)) = sub.0.get_min() else {
                        return Err(collision(&prefix));
                    };
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
    /// The state of the comparisons running on this thread.
    static COMPARISONS: Comparisons = const {
        Comparisons {
            comparing: Cell::new(false),
            pairs: RefCell::new(Vec::new()),
            scopes: Cell::new(0),
            read: RefCell::new(
                [const { ReadSet::new() }; RELATIONS],
            ),
            shallow: Cell::new(false),
        }
    };
}

/// The state of the comparisons running on one thread, in one thread local: the kernel is a
/// shared library in the test build, where each access to a thread local is a call, and a
/// comparison reads it once and passes it down. Two families compared by `==` inside `diff`
/// took 6 accesses each when every field was a thread local of its own (K73).
struct Comparisons {
    /// Whether a comparison further up this thread's stack is already reading `pairs`.
    comparing: Cell<bool>,
    /// The pairs of families a comparison has yet to read.
    pairs: RefCell<Vec<(Family, Family)>>,
    /// How many comparisons are running on this thread, one inside another: `diff` calls `==`
    /// on the entries it finds, which starts a comparison inside the one that called `diff`.
    scopes: Cell<usize>,
    /// By relation, the pairs of shared sequences and of families that the comparisons running
    /// on this thread have read to their end with no difference, the pairs the walk in hand has
    /// entered and not yet left, and under identity the pairs of families queued. Emptied when
    /// the outermost comparison ends.
    read: RefCell<[ReadSet; RELATIONS]>,
    /// Whether [`Family::shallow_diff`] is running: two families that do not share their map
    /// are then taken to differ, without reading them.
    shallow: Cell<bool>,
}

impl Comparisons {
    /// Records that a walk enters `pair` under `r`; false when a comparison running on this
    /// thread has entered it already. One lookup per pair: a pair is kept from the moment it is
    /// entered, and [`Comparisons::leave`] takes it out again when the walk ends at a difference
    /// first.
    fn enter(&self, pair: Pair, r: Relation) -> bool {
        self.read.borrow_mut()[r as usize].insert(pair)
    }

    /// Takes `pair` out of the pairs read under `r`: the walk ended before reading it to its end.
    fn leave(&self, pair: Pair, r: Relation) {
        self.read.borrow_mut()[r as usize].remove(pair);
    }
}

/// The number of relations, one set of pairs each in `read` ([`Comparisons`]):
/// [`Relation::Max`] is the last.
const RELATIONS: usize = Relation::Max as usize + 1;

/// The pairs of ids read under one relation: a set in one array of slots, found by linear
/// probing from the slot the pair's hash gives, the empty slot being `(0, 0)`. The slots are a
/// power of two in number and at most half full, so a lookup reads two slots on average. It
/// takes fewer instructions per pair than `HashSet` with the same hash, which also keeps a
/// byte of tags per slot and reads it first (K73).
struct ReadSet {
    slots: Vec<Pair>,
    len: usize,
}

/// The empty slot of a [`ReadSet`]. No pair kept is `(0, 0)`: id 0 is the empty sequence's and
/// the empty family's, and two empty values are read in O(1), so they are not kept.
const EMPTY: Pair = (0, 0);

impl ReadSet {
    const fn new() -> Self {
        ReadSet {
            slots: Vec::new(),
            len: 0,
        }
    }

    /// The slot a search for `pair` starts at: each id folded in by one 64 by 64 to 128 bit
    /// multiply, whose two halves are added by exclusive or. Ids come from one counter in the
    /// runtime, not from input. SipHash took 60 to 80% more instructions per pair of families
    /// than splitmix64's finalizer on each id, and that finalizer 45 more per pair than this.
    #[inline(always)]
    fn home(&self, (a, b): Pair) -> usize {
        let fold = |x: u64| {
            let m = u128::from(x) * 0x9e37_79b9_7f4a_7c15_u128;
            (m as u64) ^ ((m >> 64) as u64)
        };
        (fold(fold(a) ^ b) as usize) & (self.slots.len() - 1)
    }

    /// Adds `pair`; false when it is there already.
    #[inline]
    fn insert(&mut self, pair: Pair) -> bool {
        if pair == EMPTY {
            return true;
        }
        if 2 * (self.len + 1) > self.slots.len() {
            self.grow();
        }
        let mask = self.slots.len() - 1;
        let mut i = self.home(pair);
        loop {
            let slot = self.slots[i];
            if slot == pair {
                return false;
            }
            if slot == EMPTY {
                self.slots[i] = pair;
                self.len += 1;
                return true;
            }
            i = (i + 1) & mask;
        }
    }

    /// Takes `pair` out, if it is there. The pairs after it in its run that could sit in its
    /// slot move back, so every pair stays reachable from its home slot with no empty slot
    /// between (deletion by backward shift).
    fn remove(&mut self, pair: Pair) {
        if pair == EMPTY || self.len == 0 {
            return;
        }
        let mask = self.slots.len() - 1;
        let mut i = self.home(pair);
        loop {
            let slot = self.slots[i];
            if slot == EMPTY {
                return;
            }
            if slot == pair {
                break;
            }
            i = (i + 1) & mask;
        }
        let mut j = i;
        loop {
            j = (j + 1) & mask;
            let slot = self.slots[j];
            if slot == EMPTY {
                break;
            }
            // The pair at `j` may move to the hole at `i` unless its home lies cyclically
            // after `i`, up to `j`.
            let home = self.home(slot);
            if (j.wrapping_sub(home) & mask) >= (j.wrapping_sub(i) & mask) {
                self.slots[i] = slot;
                i = j;
            }
        }
        self.slots[i] = EMPTY;
        self.len -= 1;
    }

    /// Doubles the slots, 16 at the least, and puts each pair back.
    #[cold]
    fn grow(&mut self) {
        let size = (2 * self.slots.len()).max(16);
        let old = mem::replace(&mut self.slots, vec![EMPTY; size]);
        let mask = self.slots.len() - 1;
        for pair in old.into_iter().filter(|&p| p != EMPTY) {
            let mut i = self.home(pair);
            while self.slots[i] != EMPTY {
                i = (i + 1) & mask;
            }
            self.slots[i] = pair;
        }
    }

    /// The number of slots.
    #[cfg(test)]
    fn capacity(&self) -> usize {
        self.slots.len()
    }

    /// Takes every pair out. Complexity tradeoff: the slots are kept for the next comparison,
    /// which then does not grow them again (13 to 16 million instructions of 630 on 200 000
    /// pairs, K73); emptying takes time in proportion to the slots, so slots more than 8 times
    /// the pairs they held are freed instead. Either way the cost is at most a constant times
    /// the pairs this comparison added, and a thread keeps at most 8 times as many slots as
    /// the last comparison's pairs.
    fn clear(&mut self) {
        if self.len * 8 < self.slots.len() {
            self.slots = Vec::new();
        } else {
            self.slots.fill(EMPTY);
        }
        self.len = 0;
    }
}

/// The pairs a comparison reads are kept while it and every comparison it starts run
/// (`read` in [`Comparisons`]). Sequences and families draw their ids from one counter, no id
/// is drawn twice, and a value with an id is never changed, so a pair read once has the same
/// answer wherever the comparison meets it again.
///
/// Every pair of families a walk enters is kept, however the two are held. Keeping only the
/// pairs that can be met again would need to know which families are held in more than one
/// place, and nothing shows it: imbl counts the holders of a map's root and of each of its
/// nodes but gives neither count; a copy of a family is one more holder of the root; and a
/// family made by adding entries to a copy of another's map shares every node the addition did
/// not copy, with the values in them. So a family held in one entry of one map is still met
/// once per family that shares that map's node, and a pair met n times and read each time
/// costs n times its size (`comparing_families_made_from_one_family_scales`). A sequence is
/// different: it is one `Arc` with no inner nodes, so one held once is kept by no pair.
struct Scope<'c>(&'c Comparisons);

impl<'c> Scope<'c> {
    fn enter(c: &'c Comparisons) -> Self {
        c.scopes.set(c.scopes.get() + 1);
        Scope(c)
    }
}

impl Drop for Scope<'_> {
    fn drop(&mut self) {
        let left = self.0.scopes.get() - 1;
        self.0.scopes.set(left);
        if left == 0 {
            for set in self.0.read.borrow_mut().iter_mut() {
                set.clear();
            }
        }
    }
}

/// Drops `part`. A drop reached from inside this one queues its part and returns, so a chain of
/// parts is freed in a loop, whichever containers lie between them.
pub(crate) fn free(part: Part) {
    deep::free_in(&PARTS, part);
}

/// Which relation a walk over two values computes.
#[derive(Clone, Copy, PartialEq, Eq)]
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
    /// The entries of two families: the last of the walk's map levels. A map iterator is many
    /// times the size of a slice iterator, and tuples are the common level, so the map levels
    /// are kept apart, on a stack of their own that one walk allocates once.
    Maps,
}

/// A level a walk is to enter.
enum Enter<'a> {
    /// The two sequences, and the pair of their ids when either is shared.
    Items(
        slice::Iter<'a, Value>,
        slice::Iter<'a, Value>,
        Relation,
        Option<Pair>,
    ),
    /// The two families.
    Maps(&'a Family, &'a Family, Relation),
}

/// The level `enter` opens, its map's entries pushed on `maps`, and its pair kept in `read`
/// ([`Comparisons`]) from now on. `Ok(None)` when there is nothing to read here: a comparison
/// running on this thread has entered that pair already, or under identity the two families
/// are queued, to be read with `diff` ([`settle`]). `Err` ends the walk with its result. A pair
/// met again is found before its map iterators are made.
fn open<'a>(
    c: &Comparisons,
    enter: Enter<'a>,
    maps: &mut Vec<MapLevel<'a>>,
) -> Result<Option<Level<'a>>, Option<Ordering>> {
    match enter {
        Enter::Items(a, b, r, pair) => Ok(pair
            .is_none_or(|pair| c.enter(pair, r))
            .then_some(Level::Items(a, b, r, pair))),
        Enter::Maps(_, _, Relation::Identity) if c.shallow.get() => Err(None),
        Enter::Maps(a, b, relation) => {
            let pair = (a.id(), b.id());
            // The comparison is the same only if every queued pair is, so a pair queued once
            // is not queued again.
            if !c.enter(pair, relation) {
                return Ok(None);
            }
            if relation == Relation::Identity {
                // A family is copied by a reference count, so the queue holds no data.
                c.pairs.borrow_mut().push((a.clone(), b.clone()));
                return Ok(None);
            }
            maps.push(MapLevel {
                a: a.0.iter(),
                b: b.0.iter(),
                values: None,
                relation,
                pair,
            });
            Ok(Some(Level::Maps))
        }
    }
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
    Enter(Enter<'a>),
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
        _ => Step::Enter(Enter::Items(a.iter(), b.iter(), r, Items::pair(a, b))),
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
    match r {
        Relation::Identity | Relation::SurfaceEq if a.len() != b.len() => Step::Ends(None),
        Relation::Identity | Relation::Total | Relation::Min | Relation::Max if same => Step::Same,
        _ => Step::Enter(Enter::Maps(a, b, r)),
    }
}

/// Compares two values as far as their top level decides. The relations other than identity,
/// the total order and the language's `==` branch off first, so that those three, the common
/// ones, take the arms they took before `min` and `max` were added, and no arm calls `step`
/// again: a recursive `step` is not inlined into the walk (K73).
#[inline(always)]
fn step<'a>(a: &'a Value, b: &'a Value, r: Relation) -> Step<'a> {
    match r {
        Relation::SurfaceOrder => surface_order_step(a, b),
        Relation::Min | Relation::Max => min_max_step(a, b, r),
        _ => plain_step(a, b, r),
    }
}

/// [`step`] under [`Relation::SurfaceOrder`]: floats by IEEE 754 and tuples by component; beneath
/// its tuples the language's order is the total order, read in this walk so that the pairs it
/// reads are kept with the others.
fn surface_order_step<'a>(a: &'a Value, b: &'a Value) -> Step<'a> {
    match (a, b) {
        (Value::Float(x), Value::Float(y)) => match x.get().partial_cmp(&y.get()) {
            Some(Ordering::Equal) => Step::Same,
            o => Step::Ends(o),
        },
        (Value::Tuple(x), Value::Tuple(y)) => items(x, y, Relation::SurfaceOrder),
        _ => plain_step(a, b, Relation::Total),
    }
}

/// [`step`] under [`Relation::Min`] or [`Relation::Max`], which order two values of one kind
/// only, as at the top level, and two floats that differ by IEEE 754-2019 `minimum` or `maximum`.
#[cold]
#[inline(never)]
fn min_max_step<'a>(a: &'a Value, b: &'a Value, r: Relation) -> Step<'a> {
    if a.number_kind() != b.number_kind()
        || (a.number_kind().is_none() && mem::discriminant(a) != mem::discriminant(b))
    {
        return Step::Ends(None);
    }
    match (a, b) {
        (Value::Float(x), Value::Float(y)) if x == y => Step::Same,
        (Value::Float(x), Value::Float(y)) => {
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
        _ => plain_step(a, b, r),
    }
}

/// [`step`] under identity, the total order and the language's `==`, and beneath the checks of
/// the other relations.
#[inline(always)]
fn plain_step<'a>(a: &'a Value, b: &'a Value, r: Relation) -> Step<'a> {
    match (a, b, r) {
        (Value::Float(x), Value::Float(y), Relation::SurfaceEq) => match x.get() == y.get() {
            true => Step::Same,
            false => Step::Ends(None),
        },
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
        (Value::Tuple(x), Value::Tuple(y), _) | (Value::Path(x), Value::Path(y), _) => {
            items(x, y, r)
        }
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

/// Takes the next entry of `level`, whose map entries, if any, are the last of `maps`.
fn advance<'a>(level: &mut Level<'a>, maps: &mut [MapLevel<'a>]) -> Step<'a> {
    match level {
        Level::Items(a, b, r, _) => match (a.next(), b.next()) {
            (Some(x), Some(y)) => step(x, y, *r),
            (x, y) => side(x.is_some(), y.is_some()),
        },
        Level::Maps => {
            let level = maps
                .last_mut()
                .expect("a map level has its entries on the stack");
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
/// sequences or of families is kept when the walk enters it, and met again it is the same
/// without a second reading: the walk is O(distinct pairs), not O(paths). The pairs are kept in
/// `read` ([`Comparisons`]) until the outermost comparison ends, so the comparisons that `diff` starts share
/// them. A pair met again while it is being read would be a cycle, which no value has; a walk
/// that ends at a difference inside another comparison takes out the pairs it has not read to
/// their end, so that the comparison around it finds only pairs read with no difference.
fn walk(first: Step<'_>) -> Option<Ordering> {
    match first {
        Step::Same | Step::Done => Some(Ordering::Equal),
        Step::Ends(o) => o,
        Step::Enter(first) => COMPARISONS.with(|c| walk_in(c, first)),
    }
}

/// [`walk`] with this thread's [`Comparisons`] in hand.
fn walk_with(c: &Comparisons, first: Step<'_>) -> Option<Ordering> {
    match first {
        Step::Same | Step::Done => Some(Ordering::Equal),
        Step::Ends(o) => o,
        Step::Enter(first) => walk_in(c, first),
    }
}

/// [`walk`] from the first level it enters.
fn walk_in(c: &Comparisons, first: Enter<'_>) -> Option<Ordering> {
    let _scope = Scope::enter(c);
    let mut maps = Vec::new();
    let mut level = match open(c, first, &mut maps) {
        Ok(Some(level)) => level,
        Ok(None) => return Some(Ordering::Equal),
        Err(o) => return o,
    };
    let mut above = Vec::new();
    loop {
        let o = match advance(&mut level, &mut maps) {
            Step::Same => continue,
            Step::Ends(o) => o,
            Step::Enter(Enter::Items(a, b, r, pair)) => {
                if pair.is_none_or(|pair| c.enter(pair, r)) {
                    above.push(mem::replace(&mut level, Level::Items(a, b, r, pair)));
                }
                continue;
            }
            Step::Enter(inner) => match open(c, inner, &mut maps) {
                Ok(Some(inner)) => {
                    above.push(mem::replace(&mut level, inner));
                    continue;
                }
                Ok(None) => continue,
                Err(o) => o,
            },
            Step::Done => {
                if let Level::Maps = level {
                    maps.pop();
                }
                match above.pop() {
                    Some(outer) => level = outer,
                    None => return Some(Ordering::Equal),
                }
                continue;
            }
        };
        // The walk ends at a difference. The outermost comparison empties the set as it ends.
        if c.scopes.get() > 1 {
            for l in above.iter().chain([&level]) {
                if let Level::Items(.., r, Some(pair)) = l {
                    c.leave(*pair, *r);
                }
            }
            for m in &maps {
                c.leave(m.pair, m.relation);
            }
        }
        return o;
    }
}

/// Finishes an identity walk that found `same` so far by reading the queued families. A walk
/// started while the queue is being read leaves its families in the queue: `diff` calls `==`
/// on the entries it finds, inside imbl, where no stack of ours can reach, and this keeps that
/// call from nesting.
fn settle(c: &Comparisons, same: bool) -> bool {
    if c.comparing.get() {
        return same;
    }
    c.comparing.set(true);
    let mut all = same;
    let pop = || c.pairs.borrow_mut().pop();
    while all && let Some((a, b)) = pop() {
        all = a.0.diff(&b.0).next().is_none();
    }
    c.comparing.set(false);
    let left = mem::take(&mut *c.pairs.borrow_mut());
    drop(left);
    all
}

/// Whether two sequences of values are the same.
pub(crate) fn items_eq(a: &Items, b: &Items) -> bool {
    // One shared sequence, or two empty ones: equal without a walk. The entries `diff` compares
    // inside two families made one from the other are mostly such copies.
    if a.same(b) {
        return true;
    }
    COMPARISONS.with(|c| {
        let _scope = Scope::enter(c);
        settle(
            c,
            walk_with(c, items(a, b, Relation::Identity)) == Some(Ordering::Equal),
        )
    })
}

/// Whether two families are the same.
pub(crate) fn families_eq(a: &Family, b: &Family) -> bool {
    // One shared map: equal without a walk, as for sequences in `items_eq`.
    if a.0.ptr_eq(&b.0) {
        return true;
    }
    COMPARISONS.with(|c| {
        // Within `Family::shallow_diff`, two maps not shared differ unread (`open`).
        if c.shallow.get() {
            return false;
        }
        let _scope = Scope::enter(c);
        settle(
            c,
            walk_with(c, maps(a, b, Relation::Identity)) == Some(Ordering::Equal),
        )
    })
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
/// any depth, an atom tested before its payload, stopping at the first that fails. A shared
/// sequence is read once.
pub(crate) fn all_leaves(from: &[Value], test: fn(&Value) -> bool) -> bool {
    let mut level = from.iter();
    let mut above = Vec::new();
    let mut read = HashSet::new();
    loop {
        let inner = match level.next() {
            Some(Value::Tuple(xs) | Value::Path(xs)) => xs,
            Some(v @ Value::Atom(a)) if test(v) => &a.args,
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
        /// The operator: `+`, `-`, `div`, `mod`, `^`, `String` printing a number, or `int` or
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

/// Where a bug in zedc is reported: a message for a broken invariant names it
/// (DESIGN.md sec:diagnostics).
pub const REPORT_TO: &str = "https://github.com/zedlanguage/zed/issues";

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelError::Collision { keypath } => {
                write!(f, "two entries were written at the same key path, [")?;
                for (i, k) in keypath.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}")?;
                }
                write!(
                    f,
                    "], of one family (or one entry's key path begins another's), and a family \
                     holds one value at each key path; the program does not say which of the \
                     two to keep or how to combine them. To repair it, make the keys distinct, \
                     or combine the values that share a key with a reduction such as `sum`"
                )
            }
            KernelError::EmptyKeypath => write!(
                f,
                "a key function gave the empty key path `[]` for an entry, and every entry of \
                 a family needs at least one key. To repair it, make the key function give at \
                 least one key for every value"
            ),
            KernelError::MixedDepth => write!(
                f,
                "a reduction collapses one level of a family's keys, and this family holds \
                 values at more than one depth of keys, so it has no one level to collapse. \
                 To repair it, give every entry of the family the same number of keys"
            ),
            KernelError::Type(msg) => write!(
                f,
                "the run stopped because of a bug in zedc itself, not in your program: a \
                 program the checker accepts never gives an operation a value it cannot take, \
                 and here the evaluator met this: {msg}. Please report it at {REPORT_TO}, with \
                 the command line you ran and the files it read, so that it can be repeated"
            ),
            KernelError::UnknownPort(name) => write!(
                f,
                "the program uses the port `{name}`, and the run was given no port of that \
                 name. To repair it, declare `{name}` as a port of `main`, or remove the use"
            ),
            KernelError::Port(name, why) => {
                write!(f, "the port `{name}` could not answer a read: {why}")
            }
            KernelError::OutOfFuel => write!(
                f,
                "the evaluation stopped after the number of steps it was allowed: a recursion \
                 or a `gen` loop did not finish within them, so it may never finish. To repair \
                 it, make each step of the recursion or loop come closer to its end"
            ),
            KernelError::Stalled { keys } => {
                write!(
                    f,
                    "the recursive definition could not finish: the entries at keys "
                )?;
                for (i, k) in keys.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}")?;
                }
                write!(
                    f,
                    " each wait for another of them, so none of them ever gets a value. To \
                     repair it, give at least one of them a value that does not read the others"
                )
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
    fn an_empty_inner_level_keeps_its_key() {
        let empty = || Value::Family(Family::new());
        let f = Family::of([("a", Value::Int(1)), ("b", empty())]);
        assert_eq!(f.to_string(), r#"{"a" -> 1, "b" -> {}}"#);
        assert_eq!(f.len(), 2);
        assert!(Family::new().is_empty());
        let only = Family::of([("b", empty())]);
        assert!(!only.is_empty());
        assert_ne!(only, Family::new());
        // The short keypath is a leaf holding the empty family, so the leaves rebuild the family.
        assert_eq!(
            f.leaves(),
            vec![(kp(&["a"]), Value::Int(1)), (kp(&["b"]), empty())]
        );
        assert_eq!(Family::from_leaves(f.leaves()).unwrap(), f);
        // Deeper: `{"x" -> {"y" -> {}}}` is one keypath of length 2 above an empty level.
        let deep = Family::from_leaves(vec![(kp(&["x", "y"]), empty())]).unwrap();
        assert_eq!(deep.to_string(), r#"{"x" -> {"y" -> {}}}"#);
        assert_eq!(deep.leaves(), vec![(kp(&["x", "y"]), empty())]);
    }

    #[test]
    fn an_empty_level_merges_with_levels_and_collides_with_a_leaf() {
        let empty = || Value::Family(Family::new());
        // An empty level writes no leaf: leaves beneath its key fill it, in either order, and a
        // second empty level at the same keypath adds nothing.
        for leaves in [
            vec![(kp(&["a"]), empty()), (kp(&["a", "b"]), Value::Int(1))],
            vec![(kp(&["a", "b"]), Value::Int(1)), (kp(&["a"]), empty())],
            vec![
                (kp(&["a"]), empty()),
                (kp(&["a"]), empty()),
                (kp(&["a", "b"]), Value::Int(1)),
            ],
        ] {
            let f = Family::from_leaves(leaves).unwrap();
            assert_eq!(f.to_string(), r#"{"a" -> {"b" -> 1}}"#);
        }
        let twice = Family::from_leaves(vec![(kp(&["a"]), empty()), (kp(&["a"]), empty())]);
        assert_eq!(twice.unwrap().to_string(), r#"{"a" -> {}}"#);
        // A leaf where the empty level is, in either order, is two writers for one keypath.
        for (leaves, at) in [
            (
                vec![(kp(&["a"]), empty()), (kp(&["a"]), Value::Int(1))],
                kp(&["a"]),
            ),
            (
                vec![(kp(&["a"]), Value::Int(1)), (kp(&["a"]), empty())],
                kp(&["a"]),
            ),
            (
                vec![(kp(&["a"]), Value::Int(1)), (kp(&["a", "b"]), empty())],
                kp(&["a", "b"]),
            ),
        ] {
            assert_eq!(
                Family::from_leaves(leaves).unwrap_err(),
                KernelError::Collision { keypath: at }
            );
        }
        // Union: an empty level and a level merge; an empty level and a leaf collide.
        let a = Family::of([("a", empty())]);
        let b = Family::from_leaves(vec![(kp(&["a", "b"]), Value::Int(1))]).unwrap();
        assert_eq!(a.union(&b).unwrap(), b);
        assert_eq!(b.union(&a).unwrap(), b);
        assert_eq!(a.union(&a).unwrap(), a);
        let leaf = Family::of([("a", 1i64)]);
        for (x, y) in [(&a, &leaf), (&leaf, &a)] {
            assert_eq!(
                x.union(y).unwrap_err(),
                KernelError::Collision {
                    keypath: kp(&["a"])
                }
            );
        }
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
            r#"two entries were written at the same key path, ["ann", 2], of one family (or one entry's key path begins another's), and a family holds one value at each key path; the program does not say which of the two to keep or how to combine them. To repair it, make the keys distinct, or combine the values that share a key with a reduction such as `sum`"#
        );
        assert_eq!(
            KernelError::EmptyKeypath.to_string(),
            "a key function gave the empty key path `[]` for an entry, and every entry of a \
             family needs at least one key. To repair it, make the key function give at least \
             one key for every value"
        );
        assert_eq!(
            KernelError::MixedDepth.to_string(),
            "a reduction collapses one level of a family's keys, and this family holds values \
             at more than one depth of keys, so it has no one level to collapse. To repair it, \
             give every entry of the family the same number of keys"
        );
        assert_eq!(
            KernelError::Type("`+` applied to `int`, `bool`".into()).to_string(),
            "the run stopped because of a bug in zedc itself, not in your program: a program \
             the checker accepts never gives an operation a value it cannot take, and here the \
             evaluator met this: `+` applied to `int`, `bool`. Please report it at \
             https://github.com/zedlanguage/zed/issues, with the command line you ran and the \
             files it read, so that it can be repeated"
        );
        assert_eq!(
            KernelError::UnknownPort("p".into()).to_string(),
            "the program uses the port `p`, and the run was given no port of that name. To \
             repair it, declare `p` as a port of `main`, or remove the use"
        );
        assert_eq!(
            KernelError::OutOfFuel.to_string(),
            "the evaluation stopped after the number of steps it was allowed: a recursion or a \
             `gen` loop did not finish within them, so it may never finish. To repair it, make \
             each step of the recursion or loop come closer to its end"
        );
        let s = KernelError::Stalled {
            keys: vec![Value::Int(1), Value::Int(2)],
        };
        assert_eq!(
            s.to_string(),
            "the recursive definition could not finish: the entries at keys 1, 2 each wait for \
             another of them, so none of them ever gets a value. To repair it, give at least \
             one of them a value that does not read the others"
        );
    }

    #[test]
    fn a_table_of_pairs_is_kept_only_for_a_comparison_of_like_size() {
        // A comparison empties the table of pairs it filled and keeps it for the next, which
        // then does not grow it again. Emptying takes time in proportion to the table, so a
        // comparison that adds far fewer pairs frees it: small comparisons after a large one do
        // not each empty the large table.
        let small = |k: i64| Value::Family(Family::of([("x", Value::Int(k))]));
        let large = || Value::Family(Family::of((0..1000).map(|k| (k, small(k)))));
        let capacity =
            || COMPARISONS.with(|c| c.read.borrow()[Relation::Identity as usize].capacity());
        assert!(large() == large());
        let kept = capacity();
        assert!(kept > 1000);
        assert!(large() == large());
        assert_eq!(capacity(), kept);
        assert!(small(1) == small(1));
        assert_eq!(capacity(), 0);
    }

    /// The pairs `(k, k + 2^40)` for `k` from 1, as one comparison of two values built apart
    /// enters them: ids drawn in order from one counter on each side.
    fn drawn_pairs(n: usize) -> Vec<Pair> {
        (1..=n as u64).map(|k| (k, k + (1 << 40))).collect()
    }

    #[test]
    fn the_table_of_pairs_holds_what_a_set_holds() {
        // Pairs from a few ids, so runs of occupied slots form, meet and wrap past the last
        // slot; each insert, removal and lookup is checked against `HashSet`. A removal moves
        // later pairs of its run back, and a pair must stay findable from its home slot.
        let mut table = ReadSet::new();
        let mut set = HashSet::new();
        let mut x: u64 = 0x2545_f491_4f6c_dd1d;
        for _ in 0..200_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let pair = (x % 23, (x >> 8) % 19);
            if pair == EMPTY {
                // Two empty values are read at once and never kept.
                assert!(table.insert(pair));
                assert!(table.insert(pair));
                table.remove(pair);
                continue;
            }
            match x >> 60 {
                0..=8 => assert_eq!(table.insert(pair), set.insert(pair), "insert {pair:?}"),
                9..=14 => {
                    table.remove(pair);
                    set.remove(&pair);
                }
                _ => {
                    table.clear();
                    set.clear();
                }
            }
            assert_eq!(table.len, set.len());
        }
        for a in 0..23 {
            for b in 0..19 {
                let pair = (a, b);
                if pair != EMPTY {
                    // Inserting a pair present gives false and changes nothing.
                    let present = set.contains(&pair);
                    assert_eq!(!table.insert(pair), present, "{pair:?}");
                    if !present {
                        table.remove(pair);
                    }
                }
            }
        }
        assert_eq!(table.len, set.len());
    }

    #[test]
    fn a_pair_taken_out_leaves_the_pairs_after_it_findable() {
        // Every pair of a large table taken out in the order it went in, each removal moving
        // pairs back: afterward none is found and every slot is empty.
        let pairs = drawn_pairs(5_000);
        let mut table = ReadSet::new();
        for &p in &pairs {
            assert!(table.insert(p));
        }
        for (i, &p) in pairs.iter().enumerate() {
            table.remove(p);
            assert_eq!(table.len, pairs.len() - i - 1);
            if i % 997 == 0 {
                assert!(pairs[i + 1..].iter().all(|&q| !table.insert(q)));
            }
        }
        assert!(table.slots.iter().all(|&s| s == EMPTY));
    }

    #[test]
    fn the_table_of_pairs_scales() {
        // n pairs entered, every other one taken out again, as a walk that ends at a difference
        // inside another comparison does, and all n met again. Each step is O(1) on average:
        // the slots are at most half full and the hash spreads ids drawn in order.
        let inputs: HashMap<usize, Vec<Pair>> = [20_000, 160_000]
            .into_iter()
            .map(|n| (n, drawn_pairs(n)))
            .collect();
        crate::scaling::check_order(
            "the table of pairs: n entered, n/2 taken out, n met again",
            20_000,
            1,
            |n| {
                let pairs = &inputs[&n];
                let mut table = ReadSet::new();
                for &p in pairs {
                    assert!(table.insert(p));
                }
                for &p in pairs.iter().step_by(2) {
                    table.remove(p);
                }
                let again = pairs.iter().filter(|&&p| table.insert(p)).count();
                assert_eq!(again, n.div_ceil(2));
                table.clear();
            },
        );
    }
}
