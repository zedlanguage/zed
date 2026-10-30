//! The compiler as queries (step L1.30): each stage is a query whose result is memoized under
//! a content hash of everything it reads, so asking again after an edit recomputes only the
//! queries whose inputs changed.
//!
//! Three queries exist at L1. The front end (lexing through elaboration) is keyed by the
//! unit's text, since every structure before the kernel terms carries byte spans and so
//! changes with any edit. A row of a function's `test` table is keyed by its check and the
//! definitions the check reaches, and a row of `main`'s table by its key, its value, the
//! ports, and the definitions `main` and those terms reach: kernel terms carry no spans, so
//! an edit that leaves those definitions alone (a comment, another function, another row)
//! reuses the row's result. This cutoff is the point of the structure.
//!
//! The hashes are syntactic, as step L1.30 allows: a key hashes the terms' printed form, so
//! two spellings of one value are two keys, which costs a recomputation and never a wrong
//! answer. Canonical (alpha-invariant) keys are the canonicalizer's addresses, which the
//! queries take over when they move onto the engine (step L7.13). A key is the BLAKE3-256
//! hash of `zed-query\0`, the query's name, and its parts, each written as its length in
//! bytes and then its bytes, so no two different part lists share a key.
//!
//! Where DESIGN.md does not say: results are kept for the life of the [`Db`] and never
//! evicted, which a long-lived process (the language server, step L25.1) must bound; the
//! interpreter and the prelude are fixed for one build of the compiler, so they are not hashed.

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::Term;

use crate::ast::Stmt;
use crate::elab::{Cones, Unit};
use crate::run::{self, Diagnostic};

/// A query's key: a content hash of its inputs.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Key(pub [u8; 32]);

/// The key of query `name` over `parts`.
pub fn key(name: &str, parts: &[&[u8]]) -> Key {
    let mut h = blake3::Hasher::new();
    h.update(b"zed-query\0");
    h.update(&(name.len() as u64).to_le_bytes());
    h.update(name.as_bytes());
    for p in parts {
        h.update(&(p.len() as u64).to_le_bytes());
        h.update(p);
    }
    Key(*h.finalize().as_bytes())
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
}

/// The front end's result: the statements and elaboration, or the first rejecting phase's
/// diagnostics.
pub type Front = Result<(Vec<Stmt>, Unit), Vec<Diagnostic>>;

/// The memoized results, and how many times each query was computed rather than reused.
#[derive(Clone, Default)]
pub struct Db {
    front: HashMap<Key, Arc<Front>>,
    rows: HashMap<(Query, Key), Result<(), String>>,
    computed: HashMap<Query, usize>,
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

    /// The result of the table row `q` under `k`, computing it with `check` when no result
    /// is kept.
    pub fn row(
        &mut self,
        q: Query,
        k: Key,
        check: impl FnOnce() -> Result<(), String>,
    ) -> Result<(), String> {
        if let Some(r) = self.rows.get(&(q, k)) {
            return r.clone();
        }
        *self.computed.entry(q).or_default() += 1;
        let r = check();
        self.rows.insert((q, k), r.clone());
        r
    }

    /// How many times query `q` has been computed.
    pub fn computed(&self, q: Query) -> usize {
        self.computed.get(&q).copied().unwrap_or(0)
    }
}

/// The syntactic bytes of the definitions of the unit of `cones` that `roots` reach, in the unit's order,
/// followed by the roots: what a term evaluated under the unit can read.
pub fn cone(cones: &Cones<'_>, roots: &[&Term]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut put = |s: String| {
        out.extend_from_slice(&(s.len() as u64).to_le_bytes());
        out.extend_from_slice(s.as_bytes());
    };
    for d in cones.defs(roots) {
        put(format!("{}={:?}", d.kernel, d.term));
    }
    for t in roots {
        put(format!("{t:?}"));
    }
    out
}
