//! The compiler as queries (step L1.30): each stage is a query whose result is memoized under
//! a key made of everything it reads, so asking again after an edit recomputes only the
//! queries whose inputs changed.
//!
//! Three queries exist at L1. Step L2.3 adds two over a package's units (`crate::unit`): a unit's
//! statements and imports, keyed by its text, and its resolution, keyed by its text and the
//! exports of the units it imports, which hold no text position, so an edit inside a unit that
//! keeps its names resolves none of its importers again; each unit a resolution reads is in its
//! key as its path, a tag byte (resolved import, failed import, or prelude) and then the number
//! of its exports or why the import failed. The front end (lexing through elaboration) is keyed by the
//! unit's text and the build it is compiled for (step L2.8d), since every structure before
//! the kernel terms carries byte spans and so
//! changes with any edit. Step L2.8 adds a unit's content address, keyed by its text as the front
//! end is and computed from the front end's result, so a build that checks or writes the pins of
//! many importers of one unit addresses it once. A row of a function's `test` table is keyed by its check and the
//! definitions the check reaches, and a row of `main`'s table by its key, its value, the
//! ports, and the definitions `main` and those terms reach: kernel terms carry no spans, so
//! an edit that leaves those definitions alone (a comment, another function, another row)
//! reuses the row's result. This cutoff is the point of the structure.
//!
//! The keys are syntactic, as step L1.30 allows: a key holds the terms' printed form, so two
//! spellings of one value are two keys, which costs a recomputation and never a wrong answer.
//! Canonical (alpha-invariant) keys are the canonicalizer's addresses, which the queries take
//! over when they move onto the engine (step L7.13). A key is the bytes `zed-query\0`, the
//! query's name, and its parts, each written as its length in bytes and then its bytes, so no
//! two different part lists share a key. A key is its inputs, not a hash of them: a hash
//! never decides equality (DESIGN.md sec:theories, the trusted base; step L1.37a), and the
//! map's hash of a key is confirmed by comparing the keys' bytes. A definition in a row's key
//! is the number the [`Db`] gave its text when it first met it, so a key costs one number per
//! definition, as a digest did, and two definitions share a number only when their texts are
//! equal.
//!
//! Where DESIGN.md does not say: results are kept for the life of the [`Db`] and never
//! evicted, which a long-lived process (the language server, step L25.1) must bound; the
//! interpreter and the prelude are fixed for one build of the compiler, so they are not in
//! a key.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use zed_kernel::Term;

use crate::ast::Error;
use crate::build::Build;
use crate::elab::Cones;
use crate::front::{self, Front, Parsed};
use crate::pin::{self, Address};
use crate::resolve::{Exports, Resolved};

/// A query's key: its inputs, encoded.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Key(pub Box<[u8]>);

/// The key of query `name` over `parts`.
pub fn key(name: &str, parts: &[&[u8]]) -> Key {
    let tag = b"zed-query\0";
    let len = tag.len() + 8 + name.len() + parts.iter().map(|p| 8 + p.len()).sum::<usize>();
    let mut out = Vec::with_capacity(len);
    out.extend_from_slice(tag);
    out.extend_from_slice(&(name.len() as u64).to_le_bytes());
    out.extend_from_slice(name.as_bytes());
    for p in parts {
        out.extend_from_slice(&(p.len() as u64).to_le_bytes());
        out.extend_from_slice(p);
    }
    Key(out.into_boxed_slice())
}

/// The front end's result for the unit `text` built for `build`, kept in `front` under its key
/// and counted in `computed` when computed.
fn front_at(
    front: &mut HashMap<Key, Arc<Front>>,
    computed: &mut HashMap<Query, usize>,
    text: &str,
    build: &Build,
) -> Arc<Front> {
    let k = key("front", &[text.as_bytes(), &build.bytes()]);
    if let Some(f) = front.get(&k) {
        return f.clone();
    }
    *computed.entry(Query::Front).or_default() += 1;
    let f = Arc::new(front::compile(text, build));
    front.insert(k, f.clone());
    f
}

/// The queries.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Query {
    /// Lexing through elaboration, keyed by the text and the build.
    Front,
    /// A row of a function's table.
    Row,
    /// A row of `main`'s table: one wave.
    Wave,
    /// A unit's statements and imports (step L2.3), keyed by its text.
    Parse,
    /// A unit's resolution (step L2.3), keyed by its text and the exports of the units it
    /// imports and of the prelude unit it sees.
    Resolve,
    /// A unit's content address (step L2.8), keyed by its text, of which its exports and their
    /// values are functions, and the build it is compiled for.
    Address,
    /// The errors of a unit that compiles alone, checked in a package build (step L1.29d),
    /// keyed by its text and the build.
    Check,
}

/// The memoized results, and how many times each query was computed rather than reused.
pub struct Db {
    front: HashMap<Key, Arc<Front>>,
    /// The results of each table query, by key.
    rows: HashMap<Query, HashMap<Key, Result<(), String>>>,
    parsed: HashMap<Key, Arc<Parsed>>,
    resolved: HashMap<Key, Arc<Resolved>>,
    addresses: HashMap<Key, Arc<Address>>,
    checks: HashMap<Key, Arc<Vec<Error>>>,
    computed: HashMap<Query, usize>,
    /// The number given to each definition's text, for a row's key.
    texts: HashMap<Box<str>, u64>,
    /// The number given to each unit's exports ([`Exports::bytes`]), for its importers' keys.
    exports: HashMap<Box<[u8]>, u64>,
    /// The build every unit is compiled for ([`Db::front`]).
    build: Build,
    /// This database's own number, so that the numbers a [`Cones`] keeps are read only with
    /// the database that gave them.
    stamp: u64,
}

/// The number of the next [`Db`] made.
static STAMPS: AtomicU64 = AtomicU64::new(0);

impl Default for Db {
    fn default() -> Self {
        Db {
            front: HashMap::new(),
            rows: HashMap::new(),
            parsed: HashMap::new(),
            resolved: HashMap::new(),
            addresses: HashMap::new(),
            checks: HashMap::new(),
            computed: HashMap::new(),
            texts: HashMap::new(),
            exports: HashMap::new(),
            build: Build::default(),
            stamp: STAMPS.fetch_add(1, Ordering::Relaxed),
        }
    }
}

/// A copy has a number of its own: the two give later texts different numbers.
impl Clone for Db {
    fn clone(&self) -> Self {
        Db {
            front: self.front.clone(),
            rows: self.rows.clone(),
            parsed: self.parsed.clone(),
            resolved: self.resolved.clone(),
            addresses: self.addresses.clone(),
            checks: self.checks.clone(),
            computed: self.computed.clone(),
            texts: self.texts.clone(),
            exports: self.exports.clone(),
            build: self.build.clone(),
            stamp: STAMPS.fetch_add(1, Ordering::Relaxed),
        }
    }
}

impl Db {
    /// An empty database.
    pub fn new() -> Self {
        Self::default()
    }

    /// An empty database whose units are compiled for `build` (step L2.8d).
    pub fn for_build(build: Build) -> Self {
        Db {
            build,
            ..Self::default()
        }
    }

    /// Compiles the units asked for from now on for `build`. What was kept for another build
    /// stays kept, under that build's keys.
    pub fn set_build(&mut self, build: &Build) {
        if self.build != *build {
            self.build = build.clone();
        }
    }

    /// The build every unit is compiled for.
    pub fn build(&self) -> &Build {
        &self.build
    }

    /// The front end's result for the unit `text`, built for this database's build.
    pub fn front(&mut self, text: &str) -> Arc<Front> {
        front_at(&mut self.front, &mut self.computed, text, &self.build)
    }

    /// The errors the unit `text`, which compiles alone, is rejected with, built for this
    /// database's build, before they are placed ([`front::rejection`]): empty when it compiles.
    pub fn check(&mut self, text: &str) -> Arc<Vec<Error>> {
        let k = key("check", &[text.as_bytes(), &self.build.bytes()]);
        if let Some(c) = self.checks.get(&k) {
            return c.clone();
        }
        *self.computed.entry(Query::Check).or_default() += 1;
        let c = Arc::new(front::rejection(text, &self.build));
        self.checks.insert(k, c.clone());
        c
    }

    /// The statements and imports of the unit `text`.
    pub fn parse(&mut self, text: &str) -> Arc<Parsed> {
        let k = key("parse", &[text.as_bytes()]);
        if let Some(p) = self.parsed.get(&k) {
            return p.clone();
        }
        *self.computed.entry(Query::Parse).or_default() += 1;
        let p = Arc::new(front::parse_unit(text));
        self.parsed.insert(k, p.clone());
        p
    }

    /// The resolution kept under `k`, a key of [`Query::Resolve`], computing it with `compute`
    /// when none is kept.
    pub fn resolve(&mut self, k: Key, compute: impl FnOnce() -> Resolved) -> Arc<Resolved> {
        if let Some(r) = self.resolved.get(&k) {
            return r.clone();
        }
        *self.computed.entry(Query::Resolve).or_default() += 1;
        let r = Arc::new(compute());
        self.resolved.insert(k, r.clone());
        r
    }

    /// The content address of the unit `text` (step L2.8), whose top level defines `exports`:
    /// `None` when the unit does not compile alone. Keyed by the text and the build it is
    /// compiled for, since `exports` is a function of the text. The unit is compiled for this
    /// database's build with every option off ([`Build::pinned`]), so the options a build
    /// turns on leave its pins as they are.
    pub fn address(&mut self, text: &str, exports: &Exports) -> Arc<Address> {
        let pinned = self.build.pinned();
        let k = key("address", &[text.as_bytes(), &pinned.bytes()]);
        if let Some(a) = self.addresses.get(&k) {
            return a.clone();
        }
        let front = front_at(&mut self.front, &mut self.computed, text, &pinned);
        *self.computed.entry(Query::Address).or_default() += 1;
        let a = Arc::new(match &*front {
            Ok((_, unit, _)) => Some(pin::address(unit, exports)),
            Err(_) => None,
        });
        self.addresses.insert(k, a.clone());
        a
    }

    /// The result of the table row `q` under `k`, computing it with `check` when no result
    /// is kept.
    pub fn row(
        &mut self,
        q: Query,
        k: Key,
        check: impl FnOnce() -> Result<(), String>,
    ) -> Result<(), String> {
        let rows = self.rows.entry(q).or_default();
        if let Some(r) = rows.get(&k) {
            return r.clone();
        }
        *self.computed.entry(q).or_default() += 1;
        let r = check();
        rows.insert(k, r.clone());
        r
    }

    /// The number of the exports `e`, given when this database first meets them: two exports
    /// share a number only when they are equal.
    pub fn exports_number(&mut self, e: &Exports) -> u64 {
        let n = self.exports.len() as u64;
        *self.exports.entry(e.bytes().into()).or_insert(n)
    }

    /// How many times query `q` has been computed.
    pub fn computed(&self, q: Query) -> usize {
        self.computed.get(&q).copied().unwrap_or(0)
    }

    /// The numbers of the definitions of the unit of `cones` that `roots` reach, in the
    /// unit's order, followed by the roots' syntactic bytes: what a term evaluated under the
    /// unit can read. A definition's number is that of its text, given once per unit, so the
    /// key of a row costs the size of its roots and the number of definitions they reach.
    pub fn cone(&mut self, cones: &Cones<'_>, roots: &[&Term]) -> Vec<u8> {
        let mut out = Vec::new();
        let mut put = |s: &[u8]| {
            out.extend_from_slice(&(s.len() as u64).to_le_bytes());
            out.extend_from_slice(s);
        };
        let texts = &mut self.texts;
        for i in cones.reach(roots) {
            let id = cones.number(i, self.stamp, |text| {
                if let Some(&n) = texts.get(text) {
                    return n;
                }
                let n = texts.len() as u64;
                texts.insert(text.into(), n);
                n
            });
            put(&id.to_le_bytes());
        }
        for t in roots {
            put(format!("{t:?}").as_bytes());
        }
        out
    }
}
