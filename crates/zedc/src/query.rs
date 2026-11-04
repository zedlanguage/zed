//! The compiler as queries (step L1.30): each stage is a query whose result is memoized under
//! a key made of everything it reads, so asking again after an edit recomputes only the
//! queries whose inputs changed.
//!
//! Three queries exist at L1. Step L2.3 adds two over a package's units (`crate::unit`): a unit's
//! statements and imports, keyed by its text, and its resolution, keyed by its text and the
//! exports of the units it imports, which hold no text position, so an edit inside a unit that
//! keeps its names resolves none of its importers again. The front end (lexing through elaboration) is keyed by the
//! unit's text, since every structure before the kernel terms carries byte spans and so
//! changes with any edit. A row of a function's `test` table is keyed by its check and the
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

use crate::ast::{self, Stmt};
use crate::elab::{Cones, Unit};
use crate::lex::Span;
use crate::resolve::{Exports, Resolved};
use crate::run::{self, Diagnostic};
use crate::unit;

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

/// The queries.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Query {
    /// Lexing through elaboration, keyed by the text.
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
}

/// The front end's result: the statements, elaboration and placed warnings, or the first
/// rejecting phase's diagnostics.
pub type Front = Result<(Vec<Stmt>, Unit, Vec<Diagnostic>), Vec<Diagnostic>>;

/// A unit's statements and its imports, each with the unit it names, in text order; or the
/// errors of the first phase that rejects it.
pub type Parsed = Result<(Vec<Stmt>, Vec<(Arc<str>, Span)>), Vec<ast::Error>>;

/// The memoized results, and how many times each query was computed rather than reused.
pub struct Db {
    front: HashMap<Key, Arc<Front>>,
    /// The results of each table query, by key.
    rows: HashMap<Query, HashMap<Key, Result<(), String>>>,
    parsed: HashMap<Key, Arc<Parsed>>,
    resolved: HashMap<Key, Arc<Resolved>>,
    computed: HashMap<Query, usize>,
    /// The number given to each definition's text, for a row's key.
    texts: HashMap<Box<str>, u64>,
    /// The number given to each unit's exports ([`Exports::bytes`]), for its importers' keys.
    exports: HashMap<Box<[u8]>, u64>,
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
            computed: HashMap::new(),
            texts: HashMap::new(),
            exports: HashMap::new(),
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
            computed: self.computed.clone(),
            texts: self.texts.clone(),
            exports: self.exports.clone(),
            stamp: STAMPS.fetch_add(1, Ordering::Relaxed),
        }
    }
}

impl Db {
    /// An empty database.
    pub fn new() -> Self {
        Self::default()
    }

    /// The front end's result for the unit `text`.
    pub fn front(&mut self, text: &str) -> Arc<Front> {
        let k = key("front", &[text.as_bytes()]);
        if let Some(f) = self.front.get(&k) {
            return f.clone();
        }
        *self.computed.entry(Query::Front).or_default() += 1;
        let f = Arc::new(run::compile(text));
        self.front.insert(k, f.clone());
        f
    }

    /// The statements and imports of the unit `text`.
    pub fn parse(&mut self, text: &str) -> Arc<Parsed> {
        let k = key("parse", &[text.as_bytes()]);
        if let Some(p) = self.parsed.get(&k) {
            return p.clone();
        }
        *self.computed.entry(Query::Parse).or_default() += 1;
        let p = Arc::new(unit::parse_unit(text));
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
