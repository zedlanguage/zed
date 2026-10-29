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

pub mod binders;
pub mod domain;
mod serial;

use std::sync::Arc;

use zed_kernel::term::Term;
use zed_kernel::value::Value;

use crate::address::ContentAddress;
pub use domain::Domain;

/// The version of the rule set and the serialization, hashed into every address.
pub const VERSION: u32 = 1;

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
                    value: Value::Tuple(vec![Value::Int(index as i64), Value::Str(written)]),
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
        rank: |d| {
            let f = &d.facets;
            let inversions = (0..f.len())
                .flat_map(|i| (i + 1..f.len()).map(move |j| (i, j)))
                .filter(|&(i, j)| f[i] > f[j])
                .count();
            (inversions + f.len()) as u64
        },
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

/// The ranks of every rule on `d`, in rule order: the measure that decreases
/// lexicographically at every step.
pub fn ranks(d: &Def) -> [u64; 4] {
    RULES.map(|r| (r.rank)(d))
}

/// The normal form of `d`: the rules applied, the first that applies each time, until none
/// does.
pub fn canonicalize(d: &Def) -> Def {
    let mut d = d.clone();
    while RULES.iter().any(|r| (r.apply)(&mut d)) {}
    d
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
