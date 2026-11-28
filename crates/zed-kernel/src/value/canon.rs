//! Canonical forms of values, by which two values are equal exactly when they are equal as
//! values, compared without reading a string's bytes or a shared tuple twice: each string is
//! named by its bytes ([`crate::text::names::Names`]) and each tuple or keypath by its kind and
//! the forms of its parts. zedc-stage keys its calls, its tables and the values a Trick reads by
//! them (items STAGE-joined-eq-build, STAGE-byte-keys), and the world keys the answers of a
//! lookup port by them ([`crate::eval::World::reads`], item WORLD-reads-canon-keys).

use std::collections::{BTreeMap, HashMap};

use crate::text;
use crate::value::Value;

/// A value's canonical form, given by one [`Namer`]: two values named by one namer have equal
/// forms exactly when they are equal values. The order is that of the names, which the namer
/// gives in the order it met them, not that of the values.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Canon {
    /// A number, boolean, atom or family, compared as a value.
    Other(Value),
    /// A string, by its name.
    Str(text::names::Name),
    /// A tuple or keypath, by its number in `Namer::seqs`.
    Seq(u64),
}

/// The names of the strings and the numbers of the tuples and keypaths of the values one map
/// keys.
#[derive(Debug, Default)]
pub struct Namer {
    text: text::names::Names,
    /// The number of each tuple (`false`) or keypath (`true`), by the forms of its parts.
    seqs: BTreeMap<(bool, Vec<Canon>), u64>,
    /// The number of each shared tuple met, by its id ([`Value::shared_parts`]). A sequence is
    /// never changed in place and its id is never drawn again, so an id names one sequence.
    seen: HashMap<u64, u64>,
}

impl Namer {
    /// An empty namer.
    pub fn new() -> Self {
        Self::default()
    }

    /// The canonical form of `v`, read on the heap, so a tuple of any depth is read, and each
    /// shared tuple once.
    pub fn canon(&mut self, v: &Value) -> Canon {
        // The tuples and keypaths being read: each, its parts not yet read, and the forms of
        // those read.
        // Neither the `unreachable!` nor the `expect` below can fire: `known` gives `None`
        // only for a tuple or a keypath (its other arms give `Some`), and `next` is `None`
        // only when it was read by `rest.next()` from the iterator of `open`'s top entry,
        // which is still on `open` then (it starts as `Some(v)`, and after a form is made
        // the loop returns when `open` is empty, before `next` is read again).
        let mut open: Vec<(&Value, std::slice::Iter<'_, Value>, Vec<Canon>)> = Vec::new();
        let mut next = Some(v);
        loop {
            let c = match next {
                Some(v) => match self.known(v) {
                    Some(c) => c,
                    None => {
                        let (Value::Tuple(items) | Value::Path(items)) = v else {
                            unreachable!("only a sequence is not known at once")
                        };
                        let mut rest = items.as_slice().iter();
                        next = rest.next();
                        open.push((v, rest, Vec::with_capacity(items.len())));
                        continue;
                    }
                },
                None => {
                    let (v, _, parts) = open.pop().expect("a sequence being read");
                    let fresh = self.seqs.len() as u64;
                    let n = *self
                        .seqs
                        .entry((matches!(v, Value::Path(_)), parts))
                        .or_insert(fresh);
                    if let Some((id, _)) = v.shared_parts() {
                        self.seen.insert(id, n);
                    }
                    Canon::Seq(n)
                }
            };
            let Some((_, rest, parts)) = open.last_mut() else {
                return c;
            };
            parts.push(c);
            next = rest.next();
        }
    }

    /// The form of `v` when it is known without reading parts: none for a tuple or keypath
    /// not met before.
    fn known(&mut self, v: &Value) -> Option<Canon> {
        Some(match v {
            Value::Str(s) => Canon::Str(self.text.name(s)),
            Value::Tuple(_) | Value::Path(_) => {
                let (id, _) = v.shared_parts()?;
                Canon::Seq(*self.seen.get(&id)?)
            }
            Value::Bool(_)
            | Value::Int(_)
            | Value::Big(_)
            | Value::Rat(_)
            | Value::Float(_)
            | Value::Float32(_)
            | Value::Atom(_)
            | Value::Family(_) => Canon::Other(v.clone()),
        })
    }
}
