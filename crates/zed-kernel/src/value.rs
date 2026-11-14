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
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::Deref;
use std::slice;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::{Arc, LazyLock};

use crate::btree::{self, Hole};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive};

use crate::deep::{self, Queue};
use crate::digest::Digest;
use crate::num::{
    Exact, FloatFormat, LiteralRounding, Rat, TooLarge, bytes_text, literal_f32, literal_f64,
    memory_clause, read_decimal, room, sign_of,
};
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

/// A 32-bit float, compared as [`F64`] is: bitwise after NaN canonicalization.
#[derive(Clone, Copy)]
pub struct F32(f32);

impl F32 {
    /// Wraps `x`, replacing any NaN by the canonical NaN.
    pub fn new(x: f32) -> Self {
        if x.is_nan() { F32(f32::NAN) } else { F32(x) }
    }

    /// The wrapped float.
    pub fn get(self) -> f32 {
        self.0
    }
}

impl PartialEq for F32 {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for F32 {}

impl Ord for F32 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl PartialOrd for F32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for F32 {
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
    /// The payload: none for a bare atom such as `#e`, and the values otherwise, one per
    /// field of a struct payload. `#e()` has an empty payload and is a value apart from `#e`
    /// (sec:lexical: `#a` and `#a()` are different types). `None` sits in a niche of
    /// [`Items`], so a bare atom is no larger than before and allocates nothing.
    pub payload: Option<Items>,
}

/// The values of a bare atom's absent payload, for walks that read every atom's values alike.
static NO_ARGS: LazyLock<Items> = LazyLock::new(Items::default);

impl Atom {
    /// The payload's values; empty for a bare atom and for `#e()`.
    pub fn args(&self) -> &Items {
        self.payload.as_ref().unwrap_or(&NO_ARGS)
    }

    /// Whether the atom has no payload, as `#e` has none and `#e()` has an empty one.
    pub fn is_bare(&self) -> bool {
        self.payload.is_none()
    }
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
    /// An `f64`, compared bitwise.
    Float(F64),
    /// An `f32`, compared bitwise.
    Float32(F32),
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
            Value::Atom(a) if a.args().is_shared() && !a.args().is_empty() => {
                Some((a.args().id(), Some((&a.name, a.fields.id()))))
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

    /// An `f32` value.
    pub fn float32(x: f32) -> Self {
        Value::Float32(F32::new(x))
    }

    /// The float literal `text` as a value of the format `suffix` names, `f32` or `f64`, or of
    /// `f64` with no suffix: the format a decimal no use fixes takes (DESIGN.md L1.26a).
    pub fn literal_float(text: &str, suffix: Option<FloatFormat>) -> Result<Self, LiteralRounding> {
        match suffix {
            Some(FloatFormat::F32) => literal_f32(text).map(Value::float32),
            _ => literal_f64(text).map(Value::float),
        }
    }

    /// A bare atom such as `#empty`, given its name without the `#`.
    pub fn atom(name: &str) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            fields: Fields::default(),
            payload: None,
        })
    }

    /// An atom with a tuple payload, such as `#ioError("disk full")`; a shared name is kept,
    /// not copied.
    pub fn atom_with(name: impl Into<Arc<str>>, args: Vec<Value>) -> Self {
        Value::Atom(Atom {
            name: name.into(),
            fields: Fields::default(),
            payload: Some(args.into()),
        })
    }

    /// `#ioError(op:, path:, why:)`: a failed read or write of a port, its operation (`read`
    /// or `write`), its path and the operating system's reason (DESIGN.md sec:ports).
    pub fn io_error(op: &str, path: &str, why: &str) -> Self {
        // The fields in name order, as `atom_named` sorts them.
        Value::Atom(Atom {
            name: "ioError".into(),
            fields: vec![Arc::from("op"), "path".into(), "why".into()].into(),
            payload: Some(vec![Value::str(op), Value::str(path), Value::str(why)].into()),
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
            payload: Some(args.into()),
        }))
    }

    /// The failure several loose atoms make together (DESIGN.md sec:failure): the set of the
    /// distinct ones as `#errs({…})`, an `#errs` among them giving its members, and a single
    /// failure as itself.
    pub fn merge_failures<'a>(atoms: impl IntoIterator<Item = &'a Value>) -> Value {
        // Complexity tradeoff (COMPLEXITY.md K18): the naive merge copies every member of each
        // `#errs` set into a new set, O(n) per merge and O(n²) for a chain of `n` failing
        // operands. Used: the largest set is shared (a copy of its persistent map) and extended by the others' members,
        // O(m log n) for the `m` members added, so the chain costs O(n log n). Tradeoff: the
        // smaller sets are still copied in; merging many sets of equal size costs their sum.
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
                match a.args().as_slice() {
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
        let len = BigUint::from(digits.len());
        room(&len * per_digit, (len * (8 + per_digit)) << 1u32)?;
        Ok(BigUint::parse_bytes(digits.as_bytes(), radix).map(int))
    }

    /// The integer of a literal type's product of powers (`LitType` in DESIGN.md sec:grammar):
    /// `prod b^k` over `factors`, integers of no sign, negated when `negative`, so `3^200000` and
    /// `5*3^200000`. A base within 64 bits is factored and its power kept as exponents
    /// ([`Rat::pow`]), so the cost is the text's, never the digits'; [`TooLarge`] when a wider
    /// base's power is built and the system refuses the memory.
    pub fn power_product(negative: bool, factors: &[(Value, Value)]) -> Result<Self, TooLarge> {
        let int = |v: &Value| {
            (v.as_integer()
                .expect("a factor of a power product is an integer"))
            .into_owned()
        };
        let mut out = Rat::int(BigInt::one());
        for (b, k) in factors {
            let (b, k) = (int(b), int(k).to_integer()?);
            let k = k.magnitude();
            out = out.mul(&match k.is_one() {
                true => b,
                false => b.pow(k)?,
            })?;
        }
        Ok(Value::integer(match negative {
            true => out.neg(),
            false => out,
        }))
    }

    /// [`Value::power_product`] of the text of one, as the kernel prints it with no spaces,
    /// `-5*3^200000`: decimal digits, each factor with an optional `^` and exponent. `Ok(None)`
    /// when the text is not one.
    pub fn power_text(text: &str) -> Result<Option<Self>, TooLarge> {
        let (negative, body) = match text.strip_prefix('-') {
            Some(b) => (true, b),
            None => (false, text),
        };
        let mut factors = Vec::new();
        for f in body.split('*') {
            let (b, k) = f.split_once('^').unwrap_or((f, "1"));
            match (read_decimal(b)?, read_decimal(k)?) {
                (Some(b), Some(k)) => {
                    let int = |n: BigUint| Value::integer(Rat::int(BigInt::from(n)));
                    factors.push((int(b), int(k)))
                }
                _ => return Ok(None),
            }
        }
        Value::power_product(negative, &factors).map(Some)
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
            Value::Float32(x) => !(x.get() == 0.0 && x.get().is_sign_negative()),
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
    // Complexity tradeoff: naive version, both tuples read as trees to the first difference,
    // O(paths), which is `2^d` for `t(k + 1) = (t(k), t(k))` nested `d` deep. Used: the walk
    // of `items_eq` with its pair table keyed by the parts' ids (see the tradeoff there, K15,
    // K21, K40), O(distinct pairs of components read), stopping at the first pair that
    // differs. Tradeoffs: the pair table's memory, as there. Tests
    // `l01_18_scalar_interpreter::tuple_min_max::min_of_two_tuples_nested_n_deep_through_shared_parts_scales`
    // (depth 1,000 and 8,000). COMPLEXITY.md row K75.
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
            Value::Int(_) | Value::Big(_) | Value::Rat(_) | Value::Float(_) | Value::Float32(_) => {
                2
            }
            Value::Str(_) => 3,
            Value::Tuple(_) => 4,
            Value::Path(_) => 5,
            Value::Family(_) => 6,
        }
    }

    /// The numeric kind: `int` (either width), `rat`, `f32` or `f64`, in the order of equal
    /// values (DESIGN.md L1.17); `None` for any other value.
    pub fn number_kind(&self) -> Option<u8> {
        match self {
            Value::Int(_) | Value::Big(_) => Some(0),
            Value::Rat(_) => Some(1),
            Value::Float32(_) => Some(2),
            Value::Float(_) => Some(3),
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
            Value::Float32(_) => "f32".into(),
            Value::Str(_) => "String".into(),
            Value::Atom(a) if a.is_bare() => format!("#{}", a.name),
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
            // Every `f32` is an `f64`, exactly.
            Value::Float32(x) => Exact::float(f64::from(x.get())),
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
        Value::Float32(x) if x.get() == 0.0 => Value::float32(0.0),
        v => v.clone(),
    }
}

/// Two numbers by value; equal values by kind, `int`, `rat`, `f32`, `f64`, and two
/// floats by their total order, which puts `-0.0` before `0.0` and NaN last.
pub(crate) fn number_cmp(a: &Value, b: &Value) -> Ordering {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::Float(x), Value::Float(y)) => x.cmp(y),
        (Value::Float32(x), Value::Float32(y)) => x.cmp(y),
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
        (Value::Float32(x), Value::Float32(y)) => x == y,
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

/// Hashes the value's digest (`digest`): two values equal under `==` hash alike, so a value
/// can key a hash map. For a boolean, number or string, `==` is `Value::scalar_cmp` giving
/// `Equal`. Unlike the order, the hash of a value of many parts costs its size.
impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(digest(self));
    }
}

/// `a` and `b` combined by [`Digest`]'s step.
fn mix(a: u64, b: u64) -> u64 {
    crate::digest::step(a, b)
}

/// The digest of a value that holds no sequence: a boolean, number, string or family. Two such
/// values equal under `==` are of one variant (an `int` of 64 bits never equals a wide one) and
/// equal there: booleans and integers by value, a rational by its residues, the same whatever primes
/// it keeps as powers ([`Rat::residues`]), a float by its bits, a string by its text however joined,
/// and a family by its number of entries, which equal families share.
fn leaf_digest(v: &Value) -> u64 {
    let mut h = Digest::default();
    match v {
        Value::Bool(b) => h.write_u64(u64::from(*b)),
        Value::Int(n) => (1, n).hash(&mut h),
        Value::Big(r) => (2, r.residues()).hash(&mut h),
        Value::Rat(r) => (3, r.residues()).hash(&mut h),
        Value::Float(x) => (4, x.get().to_bits()).hash(&mut h),
        Value::Float32(x) => (10, x.get().to_bits()).hash(&mut h),
        Value::Str(s) => (5, s).hash(&mut h),
        Value::Family(f) => (6, f.len()).hash(&mut h),
        Value::Atom(_) | Value::Tuple(_) | Value::Path(_) => {
            unreachable!("a value with a sequence")
        }
    }
    h.finish()
}

/// The digest of all but the sequence of a tuple, keypath or atom, and the sequence; none for
/// any other value. An atom's is its name and field names, and for `#e()` a mark that tells it from
/// the bare `#e`; the digest of every other atom is as it was before `#e()` was a value.
fn with_sequence(v: &Value) -> Option<(u64, &Items)> {
    let mut h = Digest::default();
    let items = match v {
        Value::Tuple(xs) => {
            h.write_u64(7);
            xs
        }
        Value::Path(xs) => {
            h.write_u64(8);
            xs
        }
        Value::Atom(a) => {
            (9, &a.name, &*a.fields).hash(&mut h);
            if !a.is_bare() && a.args().is_empty() {
                h.write_u64(1);
            }
            a.args()
        }
        _ => return None,
    };
    Some((h.finish(), items))
}

/// The digest of `v`, the same for values equal under `==` (each sequence is equal component by
/// component, see `deep`), and the same on every run. A sequence held by more than one holder,
/// which a walk can meet again, is read once and its digest kept by its [`Id`], so a value of
/// shared parts costs its distinct parts, as comparing it does; the walk keeps its own stack.
fn digest(v: &Value) -> u64 {
    /// A sequence being read: the digest of its holder's other parts, of its components so far,
    /// the components left, and its id when it is shared.
    struct Frame<'v> {
        head: u64,
        acc: u64,
        rest: slice::Iter<'v, Value>,
        id: Option<Id>,
    }
    fn shared(xs: &Items) -> Option<Id> {
        (xs.is_shared() && !xs.is_empty()).then(|| xs.id())
    }
    fn open(head: u64, xs: &Items) -> Frame<'_> {
        Frame {
            head,
            acc: mix(10, xs.len() as u64),
            rest: xs.iter(),
            id: shared(xs),
        }
    }
    let Some((head, xs)) = with_sequence(v) else {
        return leaf_digest(v);
    };
    if xs.is_empty() {
        return mix(head, mix(10, 0));
    }
    let mut seen: HashMap<Id, u64> = HashMap::new();
    let mut stack = vec![open(head, xs)];
    while let Some(top) = stack.last_mut() {
        if let Some(x) = top.rest.next() {
            match with_sequence(x) {
                None => top.acc = mix(top.acc, leaf_digest(x)),
                Some((head, xs)) => match shared(xs).and_then(|id| seen.get(&id)) {
                    Some(&acc) => top.acc = mix(top.acc, mix(head, acc)),
                    None => stack.push(open(head, xs)),
                },
            }
            continue;
        }
        let done = stack.pop().expect("the frame just read");
        if let Some(id) = done.id {
            seen.insert(id, done.acc);
        }
        let d = mix(done.head, done.acc);
        match stack.last_mut() {
            Some(up) => up.acc = mix(up.acc, d),
            None => return d,
        }
    }
    unreachable!("the walk returns when it closes the outermost sequence")
}

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
    crate::local::with(&NEXT, |next| {
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
pub struct Family(pub(crate) btree::Map<Value, Value>, Id, Id);

impl Hole for Value {
    /// `false`, which holds nothing on the heap.
    fn hole() -> Self {
        Value::Bool(false)
    }
}

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
    pub(crate) fn from_map(map: btree::Map<Value, Value>) -> Self {
        Family::made_from(map, 0)
    }

    /// The family of the entries `map`, made by adding entries to a copy of the map of the
    /// family whose id is `from`.
    fn made_from(map: btree::Map<Value, Value>, from: Id) -> Self {
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
    // Complexity tradeoff (COMPLEXITY.md K7, K10): the naive version writes every leaf of a
    // family given as a leaf one by one, O(L·d) for `L` leaves `d` deep, and O(L·d²) through a
    // `discard` that rebuilds each level. Used: such a family is kept whole (`Levels::place`)
    // when nothing else is at or above its keypath, O(log n) to place it, so each level costs
    // its own entries. Tradeoff: where something else is written beneath that keypath the
    // family's leaves are still written one by one, as before.
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
    ) -> Option<Vec<btree::DiffItem<'a, 'b, Value, Value>>> {
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
    left: btree::Iter<'a, Value, Value>,
    small_is_b: bool,
    out: btree::Map<Value, Value>,
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
// Complexity tradeoff (COMPLEXITY.md K7): the naive union rebuilds the family from the
// leaves of both, O(n + m) per union and O(n²) over a loop that adds one entry per step. Used: a
// persistent ordered map; the smaller family's entries are inserted into a shared copy of the
// larger's, recursing only where both hold a family under one key, O(m log n) for the smaller
// size `m`. Tradeoffs: the B-tree's nodes (`btree`) cost a constant factor in time over a flat
// vector, each reallocated at its exact length at an insertion into it; a collision is reported where building `a`'s leaves then `b`'s would report it, so the
// walk keeps the keypath prefix, O(depth) memory.
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
    Map(btree::Map<Value, Value>),
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
    /// the last comparison's pairs, or the 16 slots of the smallest table.
    // Complexity tradeoff (KERNEL-near-limit-benches): the 16 slots of the smallest table were
    // freed too, since one pair is fewer than an eighth of them, so a comparison that kept one
    // pair allocated, zeroed and freed a table: a lookup of a shared tuple key in an ordered
    // map paid it at each of its `O(log n)` comparisons, 2.5 of the 6.0 billion instructions
    // of a definedness fix over 32,000 such keys. Used: the smallest table is kept, and a set
    // that holds no pair is left as it is. Cost: 256 bytes a thread for each relation used.
    fn clear(&mut self) {
        if self.len == 0 {
            return;
        }
        if self.len * 8 < self.slots.len() && self.slots.len() > 16 {
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
/// place, and the counts kept do not show it: the `Arc` of each node of a map (`btree`) counts
/// the holders of that node, not of the families in it; a copy of a family is one more holder of the root; and a
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
                pairs: a.0.zip(&b.0),
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
    /// The entries of the two maps side by side.
    pairs: btree::Zip<'a, Value, Value>,
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
        Ordering::Equal => match (&a.payload, &b.payload) {
            (Some(xs), Some(ys)) => items(xs, ys, r),
            (None, None) => Step::Same,
            // A bare atom orders before the same atom with a payload, as a name orders.
            (x, y) => Step::Ends(Some(x.is_some().cmp(&y.is_some()))),
        },
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
        (Value::Float32(x), Value::Float32(y)) => match x.get().partial_cmp(&y.get()) {
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
        (Value::Float32(x), Value::Float32(y)) if x == y => Step::Same,
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
        (Value::Float32(x), Value::Float32(y)) => {
            let min = r == Relation::Min;
            // The one taken is `x` or `y` widened, so narrowing it back is exact.
            let (wx, wy) = (f64::from(x.get()), f64::from(y.get()));
            let first = F32::new(ieee_min_max(min, wx, wy) as f32) == *x;
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
        (Value::Float32(x), Value::Float32(y), Relation::SurfaceEq) => match x.get() == y.get() {
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
            // A subtree both maps hold at the same place is equal to itself under every relation
            // but the IEEE 754 ones, under which a NaN inside is not, so those read it.
            let skip = !matches!(level.relation, Relation::SurfaceEq | Relation::SurfaceOrder);
            match level.pairs.next(skip) {
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
    // The two sequences an outermost comparison starts with are not kept: meeting them again
    // inside them would be a cycle, which no value has, so a comparison of two flat tuples,
    // such as a key read in an ordered map, keeps no pair and does not touch the table.
    let first = match first {
        Enter::Items(a, b, r, Some(_)) if c.scopes.get() == 1 => Enter::Items(a, b, r, None),
        first => first,
    };
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
/// on the entries it finds, inside `btree::Diff`, where no stack of ours can reach, and this keeps that
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

// Complexity tradeoff (COMPLEXITY.md K15, K21, K40, K73): the naive equality reads both values as
// trees in full, O(tree size), which is `2^d` for `d` levels that share one part and `O(n)` per
// round for the fixpoint test of a lattice `fix` whose iterate changes one key (O(R·n) over `R`
// rounds); one part held in n places of two values is read n times under the surface
// relations, O(n²) (K73). The same table serves `==`, `cmp`, `surface_eq` and `surface_cmp`,
// one set per relation, kept until the outermost comparison ends (`Scope`). Used: a shared
// sequence or map is equal to itself at once; each pair of shared parts is read once per
// comparison, kept in `Comparisons` by the parts' ids, never their addresses;
// two families under identity are read by `btree::Map::diff`, and the other relations but the
// IEEE 754 ones by `btree::Zip`, both of which pass over the subtrees the two share. Cost
// O(distinct pairs of parts read), and for a lattice iterate the nodes the round changed.
// Tradeoffs: the pair table's memory, kept between comparisons up to 8 times the last one's
// pairs (`clear`); one hash insert per pair entered, 18 to 24% more instructions on families
// with no sharing (K73); every pair of families entered is kept, since which are held twice is not
// known; the IEEE 754 relations still read a shared sequence, since a NaN is not equal to
// itself.
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
                payload: a.payload.as_ref().map(|_| items),
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
// Complexity tradeoff (COMPLEXITY.md K21, K22, K40): the naive copy and the naive test of
// `all_leaves` recurse on the thread's stack and read the value as a tree, O(depth) native stack
// and O(tree size), `2^d` for `d` levels that share one sequence. Used: a loop with a stack on
// the heap and a map, or a set, keyed by the shared sequence's id (drawn by `fresh_id`, never
// its address), so each shared sequence is read once: O(distinct sequences) time, O(depth)
// heap. Tradeoff: the map or set costs memory in the shared sequences met, and only sequences
// held in more than one place (`is_shared`) are entered in it.
pub(crate) fn copy(from: &[Value], leaf: fn(&Value) -> Value) -> Vec<Value> {
    let mut level = Copying::new(from, Shape::Tuple, None);
    let mut above = Vec::new();
    let mut copied: HashMap<Id, Items> = HashMap::new();
    loop {
        let (xs, shape) = match level.left.next() {
            Some(Value::Tuple(xs)) => (xs, Shape::Tuple),
            Some(Value::Path(xs)) => (xs, Shape::Path),
            Some(Value::Atom(a)) => (a.args(), Shape::Atom(a)),
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
            Some(v @ Value::Atom(a)) if test(v) => a.args(),
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
    let Some(args) = &a.payload else {
        return;
    };
    todo.push(Task::Text(")"));
    for (i, v) in args.iter().enumerate().rev() {
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
        Value::Big(n) => write!(f, "{}", n.integer_digits()),
        Value::Rat(r) => write!(f, "{r}"),
        Value::Float(x) => write!(f, "{}", crate::num::show_f64(x.get())),
        // With its suffix, as a `rat` is written with its `r`: `0.5f32` and the `f64` `0.5` are
        // two values, and a type or a ZIR text that holds both tells them apart.
        Value::Float32(x) => write!(f, "{}f32", crate::num::show_f32(x.get())),
        Value::Str(s) => write!(f, "{}", s.literal()),
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
        Value::Float32(x) => write!(f, "Float32({x:?})"),
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
    match &a.payload {
        Some(args) => {
            debug_list(todo, args, "])");
            todo.push(Task::Text("], payload: Some(["));
        }
        None => todo.push(Task::Text("], payload: None")),
    }
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
    /// An arithmetic operation had to build or read a number in full, and the system did not
    /// give the memory for it (sec:domains says when a number is built). The number is a value
    /// of the language; this evaluator cannot run the program on this machine.
    NumberTooLarge {
        /// The operator: `+`, `-`, `div`, `mod`, `^`, `String` printing a number, or `int` or
        /// `rat` reading one from a string.
        op: &'static str,
        /// The size of the number and the memory asked for it.
        need: TooLarge,
    },
    /// `String` of a tuple, keypath, atom or family must write a text of up to `bytes` bytes,
    /// the digits of the numbers inside it counted at their widest, and the system did not give
    /// the memory for it, with the widest number's build; `None` for more than `u128::MAX` bytes.
    TextTooLarge {
        /// At most this many bytes: the length of the text.
        bytes: Option<u128>,
    },
    /// Two numbers agree in so many leading bits that ordering them, for `<`, `<=`, `>`,
    /// `>=`, `min` or `max`, needs bounds of them, or the two in full, and the system did not
    /// give the memory for them.
    OrderTooLarge {
        /// The operator.
        op: &'static str,
        /// The bits read of the two and the memory asked for them.
        need: TooLarge,
    },
    /// `==` or `!=` of two numbers, one of whose coefficients is divisible by a prime the other
    /// keeps as a power, must copy and divide the coefficients to compare their normal forms,
    /// and the system did not give the memory for it.
    EqualityTooLarge {
        /// The operator.
        op: &'static str,
        /// The size of the numbers built and the memory asked for them.
        need: TooLarge,
    },
    /// Two numbers among a family's keys, or a key looked up and one in the family, agree in
    /// so many leading bits that placing them in key order needs bounds of them, or the two in
    /// full, and the system did not give the memory for them.
    KeyOrderTooLarge {
        /// The bits read of the two and the memory asked for them.
        need: TooLarge,
    },
    /// Two numbers in families, compared for equality (two leaves written at one keypath, or a
    /// key and its member when a set is printed), must be put in the same normal form, and the
    /// system did not give the memory for it.
    FamilyEqualityTooLarge {
        /// The size of the numbers built and the memory asked for them.
        need: TooLarge,
    },
    /// A number lies so near a rounding boundary of a float that telling which side it is on
    /// needs bounds of it, or the number in full, and the system did not give the memory for
    /// them.
    RoundTooLarge {
        /// The float it is rounded to, as the cast is written: `f64`.
        to: &'static str,
        /// The bits read of the number and the memory asked for them.
        need: TooLarge,
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

/// The first words of a message for a number too large for this machine's memory.
const NUMBER_TOO_LARGE: &str = "Number too large for memory";
/// The first words of a message for a text too large for this machine's memory.
const TEXT_TOO_LARGE: &str = "Text too large for memory";
/// The first words of a message for two numbers too close to order in memory.
const ORDER_TOO_LARGE: &str = "Numbers too close to order in memory";
/// The first words of a message for two numbers too large to compare in memory.
const EQUALITY_TOO_LARGE: &str = "Numbers too large to compare in memory";
/// The first words of a message for a number too close to a float's rounding boundary.
const ROUND_TOO_LARGE: &str = "Number too close to a rounding boundary for memory";
/// The first words of a message for a string too large for this machine's memory.
const STRING_TOO_LARGE: &str = "String too large for memory";
/// The first words of a message for a join longer than a string can be.
const STRING_TOO_LONG: &str = "String too long";

/// `why`, a [`KernelError`]'s text, with the operator it names replaced by the expression as
/// the program writes it, `written`, the source of the site the run stopped at: "`^` needs a
/// number of …" becomes "`b ^ (2^64)` needs a number of …". The text is left as it is when it
/// is not one of the errors that name an operator, or when `written` does not contain the
/// operator (the site is another expression). A line break in `written`, with the spaces
/// around it, is written as one space, so the headline stays on one line.
///
/// Tradeoff: an error reaches the place where its site is known as text (both engines carry
/// it as a `String`), so the expression is put in by recognizing the headline's first words
/// here, next to the [`fmt::Display`] that writes them, rather than by carrying the error
/// value to that place, which would change the error type of both engines' runs. Cost: one
/// pass over `why` and `written`, O(their length).
pub fn name_expression(why: String, written: &str) -> String {
    let titles = [
        NUMBER_TOO_LARGE,
        TEXT_TOO_LARGE,
        ORDER_TOO_LARGE,
        EQUALITY_TOO_LARGE,
        ROUND_TOO_LARGE,
        STRING_TOO_LARGE,
        STRING_TOO_LONG,
    ];
    let Some(rest) = titles.iter().find_map(|t| why.strip_prefix(t)) else {
        return why;
    };
    let Some(op) = rest
        .strip_prefix(": `")
        .and_then(|r| r.split_once('`'))
        .map(|(op, _)| op)
    else {
        return why;
    };
    if !written.contains(op) || written.trim() == op {
        return why;
    }
    let at = why.len() - rest.len() + 3;
    let mut out = String::with_capacity(why.len() + written.len());
    out.push_str(&why[..at]);
    let mut parts = written.trim().split('\n');
    out.push_str(parts.next().unwrap_or_default().trim_end());
    for line in parts {
        out.push(' ');
        out.push_str(line.trim());
    }
    out.push_str(&why[at + op.len()..]);
    out
}

/// The first words of a message for an allocation refused under the memory limit of `main`
/// (DESIGN.md sec:diagnostics, row "Limit of `main` passed in a run").
pub const MEMORY_LIMIT_PASSED: &str = "Memory limit of `main` passed";

/// The first words of each message for memory the system refused a run: a fault of the
/// machine, not an error of the program (DESIGN.md sec:checking_in_zed). A join longer than a
/// string can be, [`STRING_TOO_LONG`], is not one: no machine holds it.
const MEMORY_TITLES: [&str; 8] = [
    NUMBER_TOO_LARGE,
    TEXT_TOO_LARGE,
    ORDER_TOO_LARGE,
    EQUALITY_TOO_LARGE,
    ROUND_TOO_LARGE,
    STRING_TOO_LARGE,
    "Keys too close to order in memory",
    "Atom name too large for memory",
];

/// `why`, a run's error, with the first words of a refusal of memory replaced by
/// [`MEMORY_LIMIT_PASSED`] when a memory limit of `main` is in force
/// ([`crate::limits::memory`]): the limit, not the machine, is what the run passed, and the
/// rest of the message already says so ([`crate::num::memory_clause`]). Any other `why` is
/// left as it is. Tradeoff as for [`name_expression`]: the error reaches here as text, so it
/// is recognized by its first words. O(length of `why`).
pub fn under_memory_limit(why: String) -> String {
    if crate::limits::memory().is_none() {
        return why;
    }
    match MEMORY_TITLES.iter().find(|t| why.starts_with(*t)) {
        Some(t) => format!("{MEMORY_LIMIT_PASSED}{}", &why[t.len()..]),
        None => why,
    }
}

/// Whether `why`, a run's error, placed or not, is a fault of the run that ends it with exit
/// status 3 (DESIGN.md sec:ports): a refusal of memory, under the memory limit of `main` or
/// not. Its first line starts with the headline's first words, or holds them after the
/// `file:line:col: ` of a placed error. O(length of the first line).
pub fn is_fault(why: &str) -> bool {
    let first = why.lines().next().unwrap_or_default();
    std::iter::once(MEMORY_LIMIT_PASSED)
        .chain(MEMORY_TITLES)
        .any(|t| first.starts_with(t) || first.contains(&format!(": {t}: ")))
}

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
            KernelError::NumberTooLarge { op: "String", need } => {
                write!(
                    f,
                    "{}: `String` would write {}",
                    TEXT_TOO_LARGE,
                    need.text()
                )
            }
            KernelError::NumberTooLarge { op, need } => {
                write!(f, "{}: `{op}` needs {}", NUMBER_TOO_LARGE, need.number())
            }
            KernelError::TextTooLarge { bytes } => match bytes {
                Some(n) => write!(
                    f,
                    "{}: `String` would write up to {} of text{}",
                    TEXT_TOO_LARGE,
                    bytes_text(&BigUint::from(*n)),
                    memory_clause(&BigUint::from(*n), &BigUint::from(*n))
                ),
                None => write!(
                    f,
                    "{}: `String` would write more than {} of text{}",
                    TEXT_TOO_LARGE,
                    bytes_text(&BigUint::from(u128::MAX)),
                    memory_clause(&BigUint::from(u128::MAX), &BigUint::from(u128::MAX))
                ),
            },
            KernelError::OrderTooLarge { op, need } => write!(
                f,
                "{}: `{op}` compares two numbers so close that ordering them needs {}",
                ORDER_TOO_LARGE,
                need.amount(" of them")
            ),
            KernelError::EqualityTooLarge { op, need } => write!(
                f,
                "{}: `{op}` must write two numbers in one form to compare them, which needs {}",
                EQUALITY_TOO_LARGE,
                need.amount(" of them")
            ),
            KernelError::KeyOrderTooLarge { need } => write!(
                f,
                "Keys too close to order in memory: two numbers placed in a family's key order \
                 are so close that ordering them needs {}",
                need.amount(" of them")
            ),
            KernelError::FamilyEqualityTooLarge { need } => write!(
                f,
                "{}: two numbers in families must be written in one form to tell whether they \
                 are equal, which needs {}",
                EQUALITY_TOO_LARGE,
                need.amount(" of them")
            ),
            KernelError::RoundTooLarge { to, need } => write!(
                f,
                "{}: `{to}` must round a number so close to a rounding boundary that it needs {}",
                ROUND_TOO_LARGE,
                need.amount(" of it")
            ),
            // The largest length is written as a power of 2, not in binary units, where it and
            // one byte more both read `16 EiB`.
            KernelError::StringTooLong { left, right } => write!(
                f,
                "{}: `++` would join strings of {} and {}, {} in all; a string holds at most \
                 2^{} - 1 bytes. Keep the parts apart, as a list of strings written out one at a \
                 time, or join fewer of them",
                STRING_TOO_LONG,
                bytes_text(&BigUint::from(*left)),
                bytes_text(&BigUint::from(*right)),
                bytes_text(&(BigUint::from(*left) + *right)),
                usize::BITS
            ),
            KernelError::StringCopyTooLarge { op, bytes } => write!(
                f,
                "{}: `{op}` would write a string of {}{}",
                STRING_TOO_LARGE,
                bytes_text(&BigUint::from(*bytes)),
                memory_clause(&BigUint::from(*bytes), &BigUint::from(*bytes))
            ),
            KernelError::AtomNameTooLarge { bytes } => write!(
                f,
                "Atom name too large for memory: an atom's name or field name is a joined \
                 string of {}, which an atom holds in one piece{}",
                bytes_text(&BigUint::from(*bytes)),
                memory_clause(&BigUint::from(*bytes), &BigUint::from(*bytes))
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
mod bench;

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

    /// `#e()` is a value apart from `#e` (sec:lexical): unequal, ordered after it and before
    /// `#e(1)`, digested apart, printed with its parentheses, and with no allocation for either.
    #[test]
    fn an_atom_with_an_empty_payload_is_its_own_value() {
        let bare = Value::atom("e");
        let empty = Value::atom_with("e", vec![]);
        let one = Value::atom_with("e", vec![Value::Int(1)]);
        assert_ne!(bare, empty);
        assert!(bare < empty && empty < one);
        assert_ne!(digest(&bare), digest(&empty));
        assert_eq!(empty, Value::atom_named("e", vec![]).expect("no fields"));
        assert_eq!(
            (bare.to_string(), empty.to_string()),
            ("#e".into(), "#e()".into())
        );
        assert_eq!(
            (bare.kind_type(), empty.kind_type()),
            ("#e".into(), "#e(..)".into())
        );
        let debug = |v: &Value| format!("{v:?}");
        assert_eq!(
            debug(&empty),
            "Atom(Atom { name: \"e\", fields: [], payload: Some([]) })"
        );
        assert_eq!(
            debug(&bare),
            "Atom(Atom { name: \"e\", fields: [], payload: None })"
        );
        let (Value::Atom(b), Value::Atom(e)) = (&bare, &empty) else {
            unreachable!("two atoms")
        };
        assert!(b.is_bare() && !e.is_bare());
        assert!(b.args().is_empty() && e.args().is_empty());
        assert!(empty.shared_parts().is_none());
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
            "String too long: `++` would join strings of 8.0 EiB and 8.0 EiB, 16 EiB in all; a \
             string holds at most 2^64 - 1 bytes. Keep the parts apart, as a list of strings \
             written out one at a time, or join fewer of them"
        );
    }

    /// The operator a refusal names is replaced by the expression the program writes, its
    /// lines joined by one space; any other message, or a site that does not contain the
    /// operator or is only the operator, leaves the text as it is.
    #[test]
    fn a_refusal_names_the_expression_as_written() {
        let why = |op: &'static str| {
            KernelError::NumberTooLarge {
                op,
                need: TooLarge {
                    size: BigUint::from(8u32),
                    ask: BigUint::from(8u32),
                },
            }
            .to_string()
        };
        let caret = why("^");
        let named = name_expression(caret.clone(), "b ^ (2^64)");
        assert_eq!(named, caret.replacen("`^`", "`b ^ (2^64)`", 1));
        assert!(named.starts_with("Number too large for memory: `b ^ (2^64)` needs a number of"));
        // A site written over three lines is shown on one.
        assert_eq!(
            name_expression(caret.clone(), "  b\n      ^\n  (2^64)  "),
            caret.replacen("`^`", "`b ^ (2^64)`", 1)
        );
        // The site is another expression, or the operator alone: nothing is put in.
        assert_eq!(name_expression(caret.clone(), "f(x)"), caret);
        assert_eq!(name_expression(caret.clone(), " ^ "), caret);
        assert_eq!(name_expression(caret.clone(), ""), caret);
        // A message that names no operator is left as it is.
        let other = KernelError::EmptyKeypath.to_string();
        assert_eq!(name_expression(other.clone(), "a ^ b"), other);
        // `String` of a value is named as the call is written.
        assert!(
            name_expression(why("String"), "String(2^2^100)")
                .starts_with("Text too large for memory: `String(2^2^100)` would write about ")
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
        // The smallest table is kept, so a run of comparisons of one pair each allocates it
        // once, not once per comparison.
        assert!(small(2) == small(2));
        assert_eq!(capacity(), 16);
        let slots =
            || COMPARISONS.with(|c| c.read.borrow()[Relation::Identity as usize].slots.as_ptr());
        let first = slots();
        assert!(small(3) == small(3));
        assert_eq!((capacity(), slots()), (16, first));
    }

    /// The pairs `(k, k + 2^40)` for `k` from 1, as one comparison of two values built apart
    /// enters them: ids drawn in order from one counter on each side.
    pub(super) fn drawn_pairs(n: usize) -> Vec<Pair> {
        (1..=n as u64).map(|k| (k, k + (1 << 40))).collect()
    }

    /// A tuple of `n` levels in which each level holds the one below twice: 2^n paths and
    /// `n` distinct sequences.
    pub(super) fn shared(n: usize) -> Value {
        (0..n).fold(Value::Int(0), |v, _| Value::tuple(vec![v.clone(), v]))
    }

    #[test]
    fn the_table_of_pairs_holds_what_a_set_holds() {
        // Pairs from a few ids, so runs of occupied slots form, meet and wrap past the last
        // slot; each insert, removal and lookup is checked against `HashSet`. A removal moves
        // later pairs of its run back, and a pair must stay findable from its home slot.
        let mut table = ReadSet::new();
        let mut set = HashSet::new();
        let mut x: u64 = crate::seed::seed("the_table_of_pairs_holds_what_a_set_holds") | 1;
        for _ in 0..20_000 {
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
    fn the_pairs_of_one_comparison_are_entered_taken_out_and_met_again() {
        // The input of the benchmark `the_table_of_pairs_scales` in `bench.rs` at small sizes:
        // n pairs entered, every other one taken out, all n met again, and the table cleared.
        let mut table = ReadSet::new();
        for n in [1, 2, 3, 4, 100, 5_000] {
            let pairs = drawn_pairs(n);
            for &p in &pairs {
                assert!(table.insert(p), "{n}");
            }
            assert_eq!(table.len, n);
            for &p in pairs.iter().step_by(2) {
                table.remove(p);
            }
            assert_eq!(table.len, n / 2);
            let again = pairs.iter().filter(|&&p| table.insert(p)).count();
            assert_eq!(again, n.div_ceil(2), "{n}");
            assert_eq!(table.len, n);
            table.clear();
            assert_eq!(table.len, 0);
            assert!(pairs.iter().all(|&p| table.insert(p)), "{n}: cleared");
            table.clear();
        }
    }

    /// splitmix64 from `seed`.
    struct Draw(u64);

    impl Draw {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn std_hash(keys: &std::hash::RandomState, v: &Value) -> u64 {
        use std::hash::BuildHasher;
        keys.hash_one(v)
    }

    /// A value from a small domain, so that two drawn values are often equal, and the same value
    /// in another form: a `rat` with its powers of 2 and 5 kept or built, a wide integer read
    /// from a decimal exponent or from its digits, a string joined from two parts, a sequence
    /// shared or fresh, a struct payload with fields of another id, and NaN by other bits.
    fn drawn(d: &mut Draw, depth: u32) -> (Value, Value) {
        let pick = d.below(if depth == 0 { 7 } else { 10 });
        match pick {
            0 => {
                let b = d.below(2) == 1;
                (Value::Bool(b), Value::Bool(b))
            }
            1 => {
                let n = d.below(5) as i64 - 2;
                (Value::Int(n), Value::Int(n))
            }
            2 => {
                // m * 10^k / den, written with an exponent and built in full.
                let (m, k, den) = (d.below(7) as i64 - 3, d.below(3), 1 + d.below(3) as i64);
                let full = Rat::new(BigInt::from(m * 10_i64.pow(k as u32)), BigInt::from(den))
                    .expect("a denominator above 0");
                let kept = Rat::decimal(&format!("{m}e{k}"))
                    .expect("memory")
                    .expect("a decimal")
                    .div(&Rat::int(BigInt::from(den)))
                    .expect("memory")
                    .expect("a denominator above 0");
                let (a, b) = (Value::rat(full), Value::rat(kept));
                if d.below(2) == 0 { (a, b) } else { (b, a) }
            }
            3 => {
                // 10^(19 + k), beyond 64 bits, from its digits and from an exponent.
                let k = d.below(2) as usize;
                let digits = format!("1{}", "0".repeat(19 + k));
                let a = Value::int_text(&digits, 10)
                    .expect("memory")
                    .expect("digits");
                let r = Rat::decimal(&format!("1e{}", 19 + k))
                    .expect("memory")
                    .expect("a decimal");
                let b = Value::integer(r);
                assert!(matches!((&a, &b), (Value::Big(_), Value::Big(_))));
                (a, b)
            }
            4 => {
                let bits = [0.0, -0.0, 1.5, f64::NAN, f64::INFINITY];
                let x = bits[d.below(5) as usize];
                let y = if x.is_nan() {
                    f64::from_bits(x.to_bits() ^ 1)
                } else {
                    x
                };
                (Value::float(x), Value::float(y))
            }
            5 => {
                let words = ["", "ab", "abc", "a"];
                let (s, t) = (words[d.below(4) as usize], words[d.below(4) as usize]);
                let whole = Value::str(&format!("{s}{t}"));
                let joined = Text::join(&Text::from(s), &Text::from(t)).expect("short");
                (whole, Value::Str(joined))
            }
            6 => {
                // Long enough that a text spans several of the blocks its hash reads.
                let n = 60 + d.below(10) as usize;
                let cut = d.below(n as u64) as usize;
                let s = "x".repeat(n);
                let joined =
                    Text::join(&Text::from(&s[..cut]), &Text::from(&s[cut..])).expect("short");
                (Value::str(&s), Value::Str(joined))
            }
            7 | 8 => {
                let len = d.below(3) as usize;
                let (xs, ys): (Vec<Value>, Vec<Value>) =
                    (0..len).map(|_| drawn(d, depth - 1)).unzip();
                let (a, b) = if pick == 7 {
                    (Value::tuple(xs), Value::tuple(ys))
                } else {
                    (Value::path(xs), Value::path(ys))
                };
                // A shared copy has the same id; a fresh one another.
                if d.below(2) == 0 {
                    (a.clone(), a)
                } else {
                    (a, b)
                }
            }
            _ => {
                let name = ["e", "f"][d.below(2) as usize];
                let len = d.below(3) as usize;
                let (xs, ys): (Vec<Value>, Vec<Value>) =
                    (0..len).map(|_| drawn(d, depth - 1)).unzip();
                if d.below(2) == 0 {
                    (Value::atom_with(name, xs), Value::atom_with(name, ys))
                } else {
                    let named = |vs: Vec<Value>| {
                        let fields = vs
                            .into_iter()
                            .enumerate()
                            .map(|(i, v)| (Arc::from(["p", "q", "r"][i]), v));
                        Value::atom_named(name, fields.rev().collect()).expect("distinct names")
                    };
                    (named(xs), named(ys))
                }
            }
        }
    }

    /// Equal values hash alike, under `Hash` with the standard hasher's random keys and under
    /// the digest: each drawn value against its other form, and against the value drawn before
    /// it, which is often equal in this small domain. 20,000 cases; the counts show that both
    /// kinds of pair were met, and that unequal values do not all share a hash.
    #[test]
    fn equal_values_hash_alike() {
        let mut d = Draw(crate::seed::seed("equal_values_hash_alike"));
        let (mut same, mut by_chance, mut apart, mut collided) = (0, 0, 0, 0);
        let mut forms_differ = 0;
        let mut last: std::collections::VecDeque<Value> = Default::default();
        let keys = std::hash::RandomState::new();
        for _ in 0..20_000 {
            let (a, b) = drawn(&mut d, 3);
            assert_eq!(a, b, "two forms of one value");
            assert_eq!(digest(&a), digest(&b), "{a} in two forms");
            assert_eq!(std_hash(&keys, &a), std_hash(&keys, &b), "{a} in two forms");
            same += 1;
            if let (Value::Rat(x), Value::Rat(y)) = (&a, &b) {
                forms_differ += usize::from(x.integer_factors().1 != y.integer_factors().1);
            }
            for c in &last {
                if *c == a {
                    assert_eq!(digest(&a), digest(c), "{a} drawn twice");
                    by_chance += 1;
                } else {
                    apart += 1;
                    collided += usize::from(digest(&a) == digest(c));
                }
            }
            if last.len() == 8 {
                last.pop_front();
            }
            last.push_back(a);
        }
        assert_eq!(same, 20_000);
        eprintln!(
            "{forms_differ} rats in two forms, {by_chance} equal and {apart} unequal pairs, {collided} collided"
        );
        assert!(forms_differ > 100, "{forms_differ} rats in two forms");
        assert!(by_chance > 1000, "{by_chance} equal pairs drawn");
        assert!(apart > 1000 && collided == 0, "{collided} of {apart}");
    }

    /// A tuple of `n` levels in which each level holds the one below twice: 2^n paths, n
    /// distinct sequences. Its digest reads each shared sequence once: at 64 levels, 2^64
    /// paths, it finishes at once, and at 12 levels, where reading every path is cheap, it
    /// equals the digest of the same value built fresh with nothing shared. That the walk keeps
    /// its own stack, so 200,000 levels finish, is `bench::a_value_200000_levels_deep_is_digested`.
    #[test]
    fn a_deep_shared_value_is_digested_once_per_sequence() {
        fn fresh(n: usize) -> Value {
            match n {
                0 => Value::Int(0),
                _ => Value::tuple(vec![fresh(n - 1), fresh(n - 1)]),
            }
        }
        assert_eq!(digest(&shared(12)), digest(&fresh(12)));
        assert_ne!(digest(&shared(64)), digest(&shared(63)));
    }

    /// `Rat::integer_text` of a power and of a product with one, and the value read back from
    /// the text by `Value::power_text` or `Value::int_text`. The test is here and not in `num`,
    /// since it reads through `Value`, which `num` does not import.
    #[test]
    fn an_integer_prints_its_shorter_text_and_reads_back() {
        let power = |b: u64, k: u64| Rat::int(BigInt::from(b)).pow(&BigUint::from(k)).unwrap();
        let neg = |r: Rat| r.neg();
        let times = |c: i64, r: Rat| Rat::int(BigInt::from(c)).mul(&r).unwrap();
        for (value, text) in [
            (power(2, 3), "8"),
            (power(2, 10), "1024"),
            (power(10, 5), "10^5"),
            (power(10, 3), "1000"),
            // 2^64 has 20 digits, its power 4 characters.
            (power(2, 64), "2^64"),
            (power(3, 200000), "3^200000"),
            (power(9, 100000), "3^200000"),
            (neg(power(3, 200000)), "-3^200000"),
            (times(5, power(3, 200000)), "5*3^200000"),
            (times(-5, power(3, 200000)), "-5*3^200000"),
            (power(5, 1).mul(&power(3, 200000)).unwrap(), "5*3^200000"),
            (
                power(7, 1)
                    .mul(&power(11, 1))
                    .unwrap()
                    .mul(&power(2, 64))
                    .unwrap(),
                "77*2^64",
            ),
            (power(12, 100000), "12^100000"),
            (power(6, 100), "6^100"),
            (power(2, 200).mul(&power(3, 100)).unwrap(), "12^100"),
            (power(2, 300).mul(&power(3, 100)).unwrap(), "24^100"),
            (power(2, 300).mul(&power(3, 7)).unwrap(), "2^300*3^7"),
            (
                power(2, 300)
                    .mul(&power(5, 300))
                    .unwrap()
                    .mul(&power(3, 7))
                    .unwrap(),
                "10^300*3^7",
            ),
        ] {
            assert_eq!(value.integer_text(), text, "{text}");
            let back = Value::power_text(text).unwrap();
            let back = back.or_else(|| Value::int_text(text, 10).unwrap());
            assert_eq!(*back.unwrap().as_integer().unwrap(), value, "{text}");
        }
        // Equal values print alike, however they were made.
        assert_eq!(power(9, 100000), power(3, 200000));
        assert_ne!(
            power(3, 200000),
            power(3, 200000).add(&Rat::int(BigInt::one())).unwrap()
        );
    }
}
