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
//! The address is the BLAKE3-256 hash of `zed-canon\0` and the normal form's serialization.
//! No version number is hashed: until Zed 1.0 a change to a rule or to the serialization
//! changes the addresses it changes, and the tests that pin addresses are pinned again (author
//! order, 2026-11-20: "just keep building and fixing, you don't need to rubber stamp anything
//! as a specific ABI version").
//!
//! A unit, the prelude's units included, is addressed by its exported declarations
//! ([`unit_address`], step M0.11). It has no version number of its own: a changed unit has a new
//! address, and the address is what an import's pin names (step L2.8).

pub mod binders;
mod def;
pub mod domain;

mod serial;
use std::cmp::Ordering;
use std::sync::Arc;

use zed_collections::index::to_u32;
use zed_collections::intern::Interner;
use zed_kernel::num::TooLarge;
use zed_kernel::term::Term;
use zed_kernel::value::Value;

pub use def::{Def, Facet};
pub use domain::Domain;
use zedc_base::address::ContentAddress;

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
    //
    // Proof that the one-walk form is the rules' normal form, whatever order they apply in
    // (DOC-proofs-in-comments-audit-rest). The rules end (the ranks above fall
    // lexicographically at every step), and each touches its own parts only: `binders` the
    // body, adding one hint facet; `hints` and `facets` the facets; `domain` the domain. So
    // each part's final value is fixed by its initial value, and it is enough to show each.
    // 1. Domain. The rule replaces it by `normal()` once; `Domain::normal` is idempotent (its
    //    proof), so the rank is then 0 and the final domain is `normal()` of the first.
    // 2. Facets. `hints` removes a hint, `facets` swaps two neighbors or drops one of two
    //    equal neighbors, and `binders` adds only hints, so the set of the non-hint facets
    //    never changes. At the end no hint is left (the hints rank is 0) and no neighbors
    //    have `w[0] >= w[1]`, so the facets are strictly increasing in `Facet`'s order: the
    //    one strictly increasing list of that set, which `sorted_facets` builds (its comment
    //    proves its order is `Facet`'s on non-hint facets and that it drops exactly repeats).
    // 3. Body. Let the nameless form of a term be the term with each variable replaced by
    //    the level of the binder it means, or its own name when free. (a) `binders::canonical`
    //    names each binder at level `l` `\0l` (`Levels::new_name` in `Mode::Canonical`) and
    //    each variable the new name of its binder, and it refuses a free name spelled as a
    //    level (`refuse_free_level`); only one binder at level `l` encloses any point, so
    //    each variable still means its binder, and the nameless form is kept. (b) A step of
    //    the rule keeps the nameless form and adds no free name (the module comment of
    //    `binders`: the renamed binder at level `l` takes `\0l`; a binder inside its scope
    //    has a higher level, so one spelled `\0l` is given its own level, and a written name
    //    is never a level name, so nothing inside captures `\0l`), and the rank falls; at
    //    rank 0 every binder is spelled as its level. (c) A term in which every binder is
    //    spelled as its level and no free name is a level name is fixed by its nameless form:
    //    a binder at level `l` and each variable meaning it read `\0l`, and a free variable
    //    its own name. By (a) and (b) both forms meet (c) with one nameless form, so they are
    //    equal. The rules' form on a term with a free level name is not compared: the walk
    //    refuses that term, and `canonicalize` gives no address for it.
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
    let mut first: Interner<&str> = Interner::default();
    let ids: Vec<usize> = kept().map(|f| first.intern(&f.kind)).collect();
    let mut kinds: Vec<(&str, usize)> = first.values().iter().copied().zip(0..).collect();
    kinds.sort_unstable();
    let mut rank = vec![0; kinds.len()];
    for (r, (_, id)) in kinds.into_iter().enumerate() {
        rank[id] = to_u32(r, "facet kinds");
    }
    let mut keyed: Vec<(u32, &Facet)> = ids.into_iter().map(|id| rank[id]).zip(kept()).collect();
    keyed.sort_by(|(r, f), (s, g)| r.cmp(s).then_with(|| f.value.cmp(&g.value)));
    // A repeat is a facet whose rank and value compare Equal under the order of the sort, so
    // the dedup uses that order. Proof that this drops every repeat: the sort orders by the
    // pair (rank, `Value::cmp`), a total order since each part is one, and in a sequence
    // sorted by a total order the elements Equal to one another are neighbors; `dedup_by`
    // keeps the first of each run. Proof that it drops nothing else: `Value::cmp` gives Equal
    // exactly when `==` says the values are the same (zed-kernel's `impl PartialEq for Value`
    // says so; the test `value_cmp_is_a_total_order_that_agrees_with_equality` checks it,
    // with totality, on every pair and triple of values of every kind, with two broken orders
    // as negative controls; PROOF-value-cmp-total). Cost, not soundness: a number kept with
    // prime powers is written in its kept form (sec:kernel, tags 13 and 14), so of two Equal
    // facet values, `2^64` kept as a power and `2^64` in digits, the one kept is the one
    // written first and the address depends on which; two equal definitions can then have two
    // addresses (a share missed), never two different ones one address. A form of each value
    // alone would have to factor the digits or write out the powers, neither bounded.
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
    hashed(&canonicalize(d), refs)
}

/// The address of `normal`, a definition in normal form: the BLAKE3-256 hash of `zed-canon\0`
/// and its serialization.
fn hashed(
    normal: &Def,
    refs: &dyn Fn(&str) -> Option<ContentAddress>,
) -> Result<ContentAddress, TooLarge> {
    let mut h = blake3::Hasher::new();
    h.update(b"zed-canon\0");
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
    hashed(&normal, refs)
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
/// `zed-export\0`, `body`, and the count of `params` and each one's index and
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
/// and the unit's exported declarations sorted by name and then by address (the
/// arrows of an overloaded name), each written as its name and its address. The unit's path and
/// its local declarations are not hashed: a local declaration reaches the address through the
/// address of every export that uses it, and one that no export uses cannot change a value an
/// importer sees.
pub fn unit_address(exports: &[(&str, ContentAddress)]) -> ContentAddress {
    let mut exports = exports.to_vec();
    exports.sort();
    let mut h = blake3::Hasher::new();
    h.update(b"zed-unit\0");
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

    /// Values of every kind, with the pairs an order could confuse: `0.0` and `-0.0`, a NaN,
    /// one number in several kinds (`2`, `2/1`, `2.0`), an integer just outside 64 bits and
    /// `2^64` kept as a power, a string written whole and joined from two blocks, a bare atom
    /// and the same atom with an empty payload, a tuple shared and the same tuple built again,
    /// and a set kept as a range and the same set written out.
    fn sample_values() -> Vec<Value> {
        use zed_kernel::{Family, Rat, Text};
        let big = |t: &str| Value::int_text(t, 10).unwrap().unwrap();
        let rat = |n: i64, d: i64| Value::rat(Rat::new(n.into(), d.into()).unwrap());
        let shared = Value::tuple(vec![Value::Int(1), Value::str("a")]);
        let mut values = vec![
            Value::Bool(false),
            Value::Bool(true),
            Value::Int(0),
            Value::Int(1),
            Value::Int(-1),
            Value::Int(2),
            Value::Int(i64::MAX),
            Value::Int(i64::MIN),
            big("9223372036854775808"),
            big("-9223372036854775809"),
            big("18446744073709551616"),
            Value::power_text("2^64").unwrap().unwrap(),
            rat(1, 2),
            rat(-1, 2),
            rat(1, 3),
            rat(2, 1),
            rat(0, 1),
            Value::float(0.0),
            Value::float(-0.0),
            Value::float(0.5),
            Value::float(1.0),
            Value::float(2.0),
            Value::float(f64::NAN),
            Value::float(f64::INFINITY),
            Value::float(f64::NEG_INFINITY),
            Value::float32(0.0),
            Value::float32(-0.0),
            Value::float32(1.0),
            Value::float32(f32::NAN),
            Value::str(""),
            Value::str("a"),
            Value::str("ab"),
            Value::str("b"),
            Value::Str(Text::join(&"a".into(), &"b".into()).unwrap()),
            Value::atom("a"),
            Value::atom("b"),
            Value::atom_with("a", vec![]),
            Value::atom_with("a", vec![Value::Int(1)]),
            Value::atom_with("a", vec![Value::float(1.0)]),
            Value::atom_named("a", vec![("x".into(), Value::Int(1))]).unwrap(),
            Value::atom_named("a", vec![("y".into(), Value::Int(1))]).unwrap(),
            Value::tuple(vec![]),
            Value::tuple(vec![Value::Int(1)]),
            Value::tuple(vec![Value::float(1.0)]),
            Value::tuple(vec![Value::Int(1), Value::str("a")]),
            shared.clone(),
            Value::tuple(vec![shared.clone(), Value::float(-0.0)]),
            Value::tuple(vec![shared, Value::float(0.0)]),
            Value::path(vec![]),
            Value::path(vec![Value::Int(1)]),
            Value::from(Family::new()),
            Value::from(Family::of([(1, "a")])),
            Value::from(Family::of([(1, "b")])),
            Value::from(Family::of([(Value::float(1.0), "a")])),
            Value::from(Family::set([1, 2])),
            Value::from(Family::range(1, 2)),
            Value::from(Family::set([Value::float(0.0)])),
            Value::from(Family::set([Value::float(-0.0)])),
        ];
        // Each value again inside a tuple, so the walk over parts is tested on every pair.
        let wrapped: Vec<Value> = values
            .iter()
            .map(|v| Value::tuple(vec![v.clone()]))
            .collect();
        values.extend(wrapped);
        values
    }

    type Cmp<'a> = &'a dyn Fn(&Value, &Value) -> Ordering;

    /// The first way in which `cmp` is not a total order on `values` that agrees with `eq`:
    /// two values ordered the same way both ways round (so also a value not Equal to itself),
    /// `cmp` saying Equal where `eq` says unequal or the other way round, or three values out
    /// of order (`a <= b <= c` with not `a <= c`, or with `a == c` where one step is strict).
    /// `None` when there is none. O(n^3) comparisons for n values.
    fn order_fault(
        values: &[Value],
        cmp: Cmp,
        eq: &dyn Fn(&Value, &Value) -> bool,
    ) -> Option<String> {
        for a in values {
            for b in values {
                let ab = cmp(a, b);
                if ab != cmp(b, a).reverse() {
                    return Some(format!("not antisymmetric on {a:?} and {b:?}"));
                }
                if (ab == Ordering::Equal) != eq(a, b) {
                    return Some(format!(
                        "cmp gives {ab:?} but == gives {} on {a:?} and {b:?}",
                        eq(a, b)
                    ));
                }
                for c in values {
                    let bc = cmp(b, c);
                    if ab == Ordering::Greater || bc == Ordering::Greater {
                        continue;
                    }
                    let want = match (ab, bc) {
                        (Ordering::Equal, Ordering::Equal) => Ordering::Equal,
                        _ => Ordering::Less,
                    };
                    if cmp(a, c) != want {
                        return Some(format!("not transitive on {a:?}, {b:?} and {c:?}"));
                    }
                }
            }
        }
        None
    }

    /// PROOF-value-cmp-total: `sorted_facets` drops a facet as a repeat when its value compares
    /// Equal under `Value::cmp` to the one before, which is sound only when `Value::cmp` is a
    /// total order and Equal exactly when `==` says the values are the same. This tests both on
    /// every pair and triple of [`sample_values`], and that values Equal under the order give
    /// one address, so the facet the dedup keeps does not change the address. Negative
    /// controls: an order that makes numbers of different kinds with one value Equal (`1` and
    /// `1.0`), and one that makes `-0.0` and `0.0` Equal, are each caught.
    #[test]
    fn value_cmp_is_a_total_order_that_agrees_with_equality() {
        let values = sample_values();
        let eq = |a: &Value, b: &Value| a == b;
        assert_eq!(order_fault(&values, &|a, b| a.cmp(b), &eq), None);

        let refs = |_: &str| None;
        let address_with = |v: &Value| {
            let facet = Facet {
                hint: false,
                kind: "k".into(),
                value: v.clone(),
            };
            let def = Def {
                name: "d".into(),
                domain: None,
                facets: vec![facet],
                body: lit(0),
            };
            address(&def, &refs).unwrap()
        };
        // A number kept with prime powers is written in the form it is kept in (DESIGN.md
        // sec:kernel, tags 13 and 14), so `2^64` kept as a power and `2^64` in digits are one
        // value with two addresses: a share missed, never two values given one address.
        fn kept(v: &Value) -> bool {
            match v {
                Value::Big(r) | Value::Rat(r) => !r.kept().2.is_empty(),
                Value::Tuple(xs) => xs.as_slice().iter().any(kept),
                _ => false,
            }
        }
        for a in &values {
            for b in &values {
                if a.cmp(b) == Ordering::Equal {
                    match kept(a) == kept(b) {
                        true => assert_eq!(address_with(a), address_with(b), "{a:?} and {b:?}"),
                        false => assert_ne!(address_with(a), address_with(b), "{a:?} and {b:?}"),
                    }
                }
            }
        }

        let kindless = |a: &Value, b: &Value| match (a.number_kind(), b.number_kind()) {
            (Some(_), Some(_)) if a.surface_cmp(b) == Some(Ordering::Equal) => Ordering::Equal,
            _ => a.cmp(b),
        };
        assert!(order_fault(&values, &kindless, &eq).is_some());
        let signless = |a: &Value, b: &Value| match (a, b) {
            (Value::Float(x), Value::Float(y)) if x.get() == 0.0 && y.get() == 0.0 => {
                Ordering::Equal
            }
            _ => a.cmp(b),
        };
        assert!(order_fault(&values, &signless, &eq).is_some());
    }
}
