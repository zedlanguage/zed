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
mod def;
pub mod domain;

mod serial;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::num::TooLarge;
use zed_kernel::term::Term;
use zed_kernel::value::Value;

pub use def::{Def, Facet};
pub use domain::Domain;
use zedc_base::address::ContentAddress;

/// The version of the rule set and the serialization, hashed into every address. Version 3
/// writes a primitive by its fixed number ([`zed_kernel::Prim::code`]), not its Rust name;
/// version 4 writes an exact number past `i64` by its limbs, not its decimal digits; version 5
/// writes an interval end or a class past `i64` by its sign and limbs too; version 6 writes a
/// number kept with prime powers by the form it is kept in, with no digits built (item
/// ENGINE-one); version 7 renames a ZIR pattern binder spelled as a level other than its own
/// position's, such as `$$5` first in `($$5, y)`, where version 6 kept it (commit 0a516f19c,
/// FAIL-zir-canon-misplaced-level-binder, which left the number at 6; raised by
/// FAIL-zir-canon-version-not-bumped); version 8 does the same for a kernel binder spelled as a
/// level other than its own, such as `\05` in `\05. \05`, which version 7 kept, and renames a
/// step's scope without capture (FAIL-kernel-canon-misplaced-level); version 9 writes a string
/// value in the ZIR binary form as the nodes of its text's tree, each once in the graph, not
/// its bytes (BUILD-doubling-60s); version 10 addresses an exported definition by its own
/// address and the names of the parameters a call may write ([`export_address`],
/// ADDR-param-names), with every normal form as version 9 left it; version 11 writes a string
/// value in a definition's serialization as the rules of its text's canonical parse, each once
/// in the definition, not its bytes (CANON-term-string-nodes); version 12 adds to an export's
/// address the names a call may write inside its type, as those of a function it returns or of
/// a parameter's function type (ADDR-nested-param-names), with every normal form as version 11
/// left it; version 13 labels each rule of a string's canonical parse whose code fits in 125
/// bits by that code, not by its hash (`Names::canonical`, PERF-canon-flat-strings), which
/// changes the parse, and so the rules written, of a string of more than a few bytes. The test
/// `l01_32_canonical_zir::version_pins` records the normal forms of a fixed set of graphs and
/// definitions under each version, and fails when they change and this number does not.
pub const VERSION: u32 = 13;

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
                    value: Value::tuple(vec![Value::Int(index as i64), Value::Str(written.into())]),
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
// Complexity tradeoff (COMPLEXITY.md F5): comparing every pair counts the inversions in
// O(F²); counting them while merge-sorting costs O(F log F), with a buffer of F facets per
// merge and the slice left sorted (callers pass a copy).
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
    // Complexity tradeoff (COMPLEXITY.md F5): the naive form applies the rules one step at a
    // time, renaming one binder and walking the whole term per step, O(B · t · d), and
    // bubble-sorting the facets by the swap rule, O(F³) with the rank recomputed per step.
    // Here the binders are renamed in one walk, O(t log t), and the facets filtered, sorted
    // and deduplicated once, O(F log F) (`sorted_facets`). The rules stay as the definition;
    // the test `alpha::the_normal_form_is_the_rules_applied_one_step_at_a_time` checks that
    // both agree.
    Def {
        name: d.name.clone(),
        domain: d.domain.as_ref().map(Domain::normal),
        facets: sorted_facets(&d.facets),
        body: binders::canonical(&d.body),
    }
}

/// The facets of `facets` that are not hints, in [`Facet`]'s order and without repeats: the
/// normal form of the hint and facet rules. `O(F log F)` for `F` facets.
// Complexity tradeoff (COMPLEXITY.md F5, FAIL-ratio-facet-sort): sorting the facets themselves
// compares each pair by its hint, its kind's text (a string comparison through `memcmp`) and its
// value, and moves whole facets; at 250 and 2000 facets the comparisons were half the
// instructions, and the work grew 9.54 times at 8 times the facets. Used: each distinct kind is
// ranked once (one hash lookup per facet, then the K distinct kinds sorted, O(K log K)), and the
// sort orders (rank, facet) pairs by the rank, an integer, then the value; only the facets kept
// are cloned. The order is the same: the hints are gone, so every pair has the same hint, and
// the ranks are in the kinds' text order. The sort is stable and the repeats dropped after it are
// the later ones, as before, so of two equal facets the first written is kept. Cost: a hash map
// of the K kinds and a vector of F pairs.
fn sorted_facets(facets: &[Facet]) -> Vec<Facet> {
    let kept = || facets.iter().filter(|f| !f.hint);
    // Each facet's kind as the index of the kind's first appearance, then each index mapped to
    // the kind's rank in text order.
    let mut first: HashMap<&str, u32> = HashMap::new();
    let ids: Vec<u32> = kept()
        .map(|f| {
            let next = first.len() as u32;
            *first.entry(&f.kind).or_insert(next)
        })
        .collect();
    let mut kinds: Vec<(&str, u32)> = first.into_iter().collect();
    kinds.sort_unstable();
    let mut rank = vec![0; kinds.len()];
    for (r, (_, id)) in kinds.into_iter().enumerate() {
        rank[id as usize] = r as u32;
    }
    let mut keyed: Vec<(u32, &Facet)> = ids
        .into_iter()
        .map(|id| rank[id as usize])
        .zip(kept())
        .collect();
    keyed.sort_by(|(r, f), (s, g)| r.cmp(s).then_with(|| f.value.cmp(&g.value)));
    // A repeat is a facet whose rank and value compare Equal under the order of the sort, so
    // the dedup uses that order and not `Value`'s `==` (PROOF-sweep, P246: the claim that the
    // two agree was not proved here). Proof that this drops every repeat: the sort orders by
    // the pair (rank, `Value::cmp`), a total order since each part is one (`Ord`, which every
    // sort and `BTreeMap` of values rests on), and in a sequence sorted by a total order the
    // elements Equal to one another are neighbors; `dedup_by` keeps the first of each run.
    keyed.dedup_by(|(r, f), (s, g)| r == s && f.value.cmp(&g.value) == Ordering::Equal);
    keyed.into_iter().map(|(_, f)| f.clone()).collect()
}

/// The content address of `d`. A free variable that `refs` resolves names another
/// definition and is hashed as that definition's address, so a dependency's change changes
/// its dependents' addresses; any other free variable, such as a built-in, is hashed by name.
/// [`TooLarge`] when the system refuses the memory to write one of its exact numbers.
pub fn address(
    d: &Def,
    refs: &dyn Fn(&str) -> Option<ContentAddress>,
) -> Result<ContentAddress, TooLarge> {
    address_at(VERSION, d, refs)
}

/// The content address of `d` under rule-set version `version`.
pub fn address_at(
    version: u32,
    d: &Def,
    refs: &dyn Fn(&str) -> Option<ContentAddress>,
) -> Result<ContentAddress, TooLarge> {
    hashed(version, &canonicalize(d), refs)
}

/// The address under rule-set version `version` of `normal`, a definition in normal form.
fn hashed(
    version: u32,
    normal: &Def,
    refs: &dyn Fn(&str) -> Option<ContentAddress>,
) -> Result<ContentAddress, TooLarge> {
    let mut h = blake3::Hasher::new();
    h.update(b"zed-canon\0");
    h.update(&version.to_le_bytes());
    h.update(&serialize(normal, refs)?);
    Ok(ContentAddress::hashed(&h))
}

/// The content address of the definition `name` whose body is `body`, with no domain and no
/// facets: [`address`] of that definition, read from `body` in place, so that a definition an
/// elaboration holds is addressed without first being copied into a [`Def`] (a unit's exports,
/// step L2.8). O(t log t) for a body of size t, the canonicalizer's cost.
pub fn address_of_body(
    name: &str,
    body: &Term,
    refs: &dyn Fn(&str) -> Option<ContentAddress>,
) -> Result<ContentAddress, TooLarge> {
    let normal = Def {
        name: name.into(),
        domain: None,
        facets: Vec::new(),
        body: binders::canonical(body),
    };
    hashed(VERSION, &normal, refs)
}

/// The serialization of a definition already in normal form: a self-delimiting byte string,
/// so two normal forms with equal serializations are equal. [`TooLarge`] when the system
/// refuses the memory to write one of its exact numbers.
pub fn serialize(
    d: &Def,
    refs: &dyn Fn(&str) -> Option<ContentAddress>,
) -> Result<Vec<u8>, TooLarge> {
    serial::def(d, refs)
}

/// The content address of an exported definition whose own address ([`address_of_body`]) is
/// `body` and whose parameters a call may pass as `name:` are `params`, each by its index and
/// name in index order (DESIGN.md sec:units, "Imports pin hashes"): the BLAKE3-256 hash of
/// `zed-export\0`, [`VERSION`], `body`, and the count of `params` and each one's index and
/// name. The canonicalizer renames every binder of the body, parameters included, so the
/// body's address keeps no parameter's name; a call in another unit may write one, so the
/// export's address does. The names are hashed here rather than as facets of the body's
/// normal form so that a definition of the same unit that uses this one is addressed with the
/// body's address (`pin::address`): its call has each argument already in its place, and its
/// value does not change when a name does. Then `inside`, when the checker gives the definition
/// a type: a 1 and the digest of the names a call may write inside that type
/// (`zedc_types::ty::NameDigests`), as the parameter names of a function the definition returns
/// or of a parameter's function type, which an importer writes in `p(k: 1.0)(z: 2.0)` or must
/// match to pass `apply(f: h)` (ADDR-nested-param-names); else a 0. O(p) for p parameters and
/// the bytes of their names.
pub fn export_address(
    body: ContentAddress,
    params: &[(u32, Arc<str>)],
    inside: Option<&[u8; 32]>,
) -> ContentAddress {
    let mut h = blake3::Hasher::new();
    h.update(b"zed-export\0");
    h.update(&VERSION.to_le_bytes());
    h.update(&body.0);
    h.update(&(params.len() as u64).to_le_bytes());
    for (index, name) in params {
        h.update(&index.to_le_bytes());
        h.update(&(name.len() as u64).to_le_bytes());
        h.update(name.as_bytes());
    }
    match inside {
        Some(digest) => h.update(&[1]).update(digest),
        None => h.update(&[0]),
    };
    ContentAddress::hashed(&h)
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
    ContentAddress::hashed(&h)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use zed_kernel::term::build::{lam, lit, var};

    use super::*;

    #[test]
    fn a_body_is_addressed_as_its_definition_is() {
        let body = lam(&["x"], var("x"));
        let def = Def {
            name: "id".into(),
            domain: None,
            facets: Vec::new(),
            body: body.clone(),
        };
        let refs = |_: &str| None;
        assert_eq!(address_of_body("id", &body, &refs), address(&def, &refs));
        // A name an earlier definition binds is hashed as its address.
        let uses = lam(&["y"], var("rate"));
        let known = |x: &str| (x == "rate").then(|| address(&def, &refs).unwrap());
        let other = |x: &str| (x == "rate").then(|| address_of_body("r", &lit(1), &refs).unwrap());
        assert_ne!(
            address_of_body("tax", &uses, &known),
            address_of_body("tax", &uses, &other)
        );
    }

    /// The keyed form drops the numbers elaboration gives binders, keeps their written names
    /// and which binder each variable means, and renames the free names it is given
    /// (FAIL-queries-reorder).
    #[test]
    fn the_keyed_form_drops_binder_numbers_and_keeps_written_names() {
        use zed_kernel::term::build::let_;
        let none = |_: &str| None;
        let keyed = |t: &Term| binders::keyed(t, &none);
        // The same parameter numbered by its place in two units.
        assert_eq!(
            keyed(&lam(&["n@1"], var("n@1"))),
            keyed(&lam(&["n@7"], var("n@7")))
        );
        // A temporary numbered two ways.
        assert_eq!(
            keyed(&let_("$3", lit(1), var("$3"))),
            keyed(&let_("$12", lit(1), var("$12")))
        );
        // Another written name is another key.
        assert_ne!(
            keyed(&lam(&["n@1"], var("n@1"))),
            keyed(&lam(&["m@1"], var("m@1")))
        );
        // Two binders written `n`: which one the variable means stays apart.
        let outer = lam(&["n@1"], lam(&["n@2"], var("n@1")));
        let inner = lam(&["n@1"], lam(&["n@2"], var("n@2")));
        assert_ne!(keyed(&outer), keyed(&inner));
        assert_eq!(
            keyed(&outer),
            keyed(&lam(&["n@5"], lam(&["n@3"], var("n@5"))))
        );
        // A free name is renamed as `free` says, and kept where it says nothing.
        let free = |x: &str| (x == "f@2").then(|| Arc::<str>::from("@f"));
        assert_eq!(
            binders::keyed(&app_of("f@2", "max"), &free),
            binders::keyed(&app_of("f@9", "max"), &|x: &str| {
                (x == "f@9").then(|| Arc::<str>::from("@f"))
            })
        );
        assert_ne!(
            binders::keyed(&app_of("f@2", "max"), &free),
            binders::keyed(&app_of("f@2", "min"), &free)
        );
        // The canonical form names a binder by its level alone.
        assert_eq!(
            binders::canonical(&lam(&["n@1"], var("n@1"))),
            lam(&["\u{0}0"], var("\u{0}0"))
        );
    }

    /// `f(g)` with both names free.
    fn app_of(f: &str, g: &str) -> Term {
        zed_kernel::term::build::app(var(f), vec![var(g)])
    }
}
