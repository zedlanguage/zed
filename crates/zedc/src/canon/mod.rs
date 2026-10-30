//! The canonicalizer (DESIGN.md sec:ir, "Identity"; written by step M0.7): a small, oriented,
//! terminating rewrite system whose normal form is what a content address is taken over.
//!
//! A definition is canonicalized by four rules, applied in this order of priority until none
//! applies:
//!
//! 1. **binders**: the first local binder in preorder that carries its written name is renamed
//!    to its de Bruijn level, and its written name becomes a hint facet;
//! 2. **hints**: a hint facet is dropped, since no value may depend on one;
//! 3. **facets**: two adjacent facets out of order are swapped, and of two adjacent equal
//!    facets one is dropped, so the facets end sorted and without repeats;
//! 4. **domain**: the integer facts are replaced by their normal form ([`Domain::normal`]).
//!
//! Each rule has a rank, a natural number that the rule strictly decreases and that no rule
//! later in the list increases: binders, the binders still written; hints, the hint facets;
//! facets, the inversions in the facet list plus its length; domain, 1 while the integer
//! facts are not normal. The tuple of ranks therefore decreases lexicographically at every
//! step, which proves termination. The rules touch disjoint parts of a definition, apart from
//! the binder rule adding hint facets, which only the rules after it remove.
//!
//! The address is the BLAKE3-256 hash of [`VERSION`] and the normal form's serialization.
//! Any change to a rule or to the serialization increments [`VERSION`], so every address
//! changes with it and no address is shared across rule sets.
//!
//! A unit, the prelude's units included, is addressed by its exported declarations
//! ([`unit_address`], step M0.11). It has no version number of its own: a changed unit has a new
//! address, and the address is what an import's pin names (step L2.8).

pub mod binders;
pub mod domain;
mod serial;

use std::sync::Arc;

use zed_kernel::term::Term;
use zed_kernel::value::Value;

use crate::address::ContentAddress;
pub use domain::Domain;

/// The version of the rule set and the serialization, hashed into every address.
pub const VERSION: u32 = 2;

/// A facet of a definition: a named fact about it, such as its units or a proved property.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Facet {
    /// Whether the facet is a hint, which diagnostics and printing read and no value may
    /// depend on, such as a binder's written name.
    pub hint: bool,
    /// The facet's kind, such as `units`.
    pub kind: Arc<str>,
    /// The facet's value.
    pub value: Value,
}

/// A definition as the canonicalizer sees it.
#[derive(Clone, Debug, PartialEq)]
pub struct Def {
    /// The declaration's own name, which is part of its interface and so of its value.
    pub name: Arc<str>,
    /// The integer facts of its result, when it has any.
    pub domain: Option<Domain>,
    /// Its other facets.
    pub facets: Vec<Facet>,
    /// Its body.
    pub body: Term,
}

/// A rewrite rule of the canonicalizer.
pub struct Rule {
    /// The rule's name.
    pub name: &'static str,
    /// Applies the rule once, returning whether it applied.
    pub apply: fn(&mut Def) -> bool,
    /// The rule's rank, which `apply` strictly decreases.
    pub rank: fn(&Def) -> u64,
}

/// The rules, in priority order.
pub const RULES: [Rule; 4] = [
    Rule {
        name: "binders",
        apply: |d| match binders::step(&d.body) {
            Some((body, index, written)) => {
                d.body = body;
                d.facets.push(Facet {
                    hint: true,
                    kind: "binder".into(),
                    value: Value::Tuple(vec![Value::Int(index as i64), Value::Str(written.into())]),
                });
                true
            }
            None => false,
        },
        rank: |d| binders::written(&d.body),
    },
    Rule {
        name: "hints",
        apply: |d| match d.facets.iter().position(|f| f.hint) {
            Some(i) => {
                d.facets.remove(i);
                true
            }
            None => false,
        },
        rank: |d| d.facets.iter().filter(|f| f.hint).count() as u64,
    },
    Rule {
        name: "facets",
        apply: |d| match d.facets.windows(2).position(|w| w[0] >= w[1]) {
            Some(i) if d.facets[i] == d.facets[i + 1] => {
                d.facets.remove(i);
                true
            }
            Some(i) => {
                d.facets.swap(i, i + 1);
                true
            }
            None => false,
        },
        rank: |d| (inversions(&mut d.facets.clone()) + d.facets.len()) as u64,
    },
    Rule {
        name: "domain",
        apply: |d| match &d.domain {
            Some(dom) if dom.rank() > 0 => {
                d.domain = Some(dom.normal());
                true
            }
            _ => false,
        },
        rank: |d| d.domain.as_ref().map_or(0, Domain::rank),
    },
];

/// The pairs of `f` out of order, counted while merge-sorting it: `O(F log F)`.
fn inversions(f: &mut [Facet]) -> usize {
    if f.len() < 2 {
        return 0;
    }
    let mid = f.len() / 2;
    let mut n = inversions(&mut f[..mid]) + inversions(&mut f[mid..]);
    let (mut merged, mut i, mut j) = (Vec::with_capacity(f.len()), 0, mid);
    while i < mid && j < f.len() {
        if f[j] < f[i] {
            // `f[j]` comes before each of the left half's remaining facets.
            n += mid - i;
            merged.push(f[j].clone());
            j += 1;
        } else {
            merged.push(f[i].clone());
            i += 1;
        }
    }
    merged.extend_from_slice(&f[i..mid]);
    merged.extend_from_slice(&f[j..]);
    f.clone_from_slice(&merged);
    n
}

/// The ranks of every rule on `d`, in rule order: the measure that decreases
/// lexicographically at every step.
pub fn ranks(d: &Def) -> [u64; 4] {
    RULES.map(|r| (r.rank)(d))
}

/// The normal form of `d`: the rules applied, the first that applies each time, until none
/// does.
pub fn canonicalize(d: &Def) -> Def {
    // The rules' normal form, reached directly: every binder renamed, the hints the renaming
    // adds and the written ones dropped, the facets sorted without repeats, the domain normal.
    let mut facets: Vec<Facet> = d.facets.iter().filter(|f| !f.hint).cloned().collect();
    facets.sort();
    facets.dedup();
    Def {
        name: d.name.clone(),
        domain: d.domain.as_ref().map(Domain::normal),
        facets,
        body: binders::canonical(&d.body),
    }
}

/// The content address of `d`. A free variable that `refs` resolves names another
/// definition and is hashed as that definition's address, so a dependency's change changes
/// its dependents' addresses; any other free variable, such as a built-in, is hashed by name.
pub fn address(d: &Def, refs: &dyn Fn(&str) -> Option<ContentAddress>) -> ContentAddress {
    address_at(VERSION, d, refs)
}

/// The content address of `d` under rule-set version `version`.
pub fn address_at(
    version: u32,
    d: &Def,
    refs: &dyn Fn(&str) -> Option<ContentAddress>,
) -> ContentAddress {
    let mut h = blake3::Hasher::new();
    h.update(b"zed-canon\0");
    h.update(&version.to_le_bytes());
    h.update(&serialize(&canonicalize(d), refs));
    ContentAddress(*h.finalize().as_bytes())
}

/// The serialization of a definition already in normal form: a self-delimiting byte string,
/// so two normal forms with equal serializations are equal.
pub fn serialize(d: &Def, refs: &dyn Fn(&str) -> Option<ContentAddress>) -> Vec<u8> {
    serial::def(d, refs)
}

/// The content address of a unit (step M0.11): the BLAKE3-256 hash of `zed-unit\0`,
/// [`VERSION`], and the unit's exported declarations sorted by name and then by address (the
/// arrows of an overloaded name), each written as its name and its address. The unit's path and
/// its local declarations are not hashed: a local declaration reaches the address through the
/// address of every export that uses it, and one that no export uses cannot change a value an
/// importer sees.
pub fn unit_address(exports: &[(&str, ContentAddress)]) -> ContentAddress {
    let mut exports = exports.to_vec();
    exports.sort();
    let mut h = blake3::Hasher::new();
    h.update(b"zed-unit\0");
    h.update(&VERSION.to_le_bytes());
    h.update(&(exports.len() as u64).to_le_bytes());
    for (name, address) in exports {
        h.update(&(name.len() as u64).to_le_bytes());
        h.update(name.as_bytes());
        h.update(&address.0);
    }
    ContentAddress(*h.finalize().as_bytes())
}
