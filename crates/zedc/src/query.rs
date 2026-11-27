//! The compiler as queries (step L1.30): each stage is a query whose result is memoized under
//! a key made of everything it reads, so asking again after an edit recomputes only the
//! queries whose inputs changed.
//!
//! Three queries exist at L1. Step L2.3 adds two over a package's units (`crate::unit`): a unit's
//! statements and imports, keyed by its text, and its resolution, keyed by its text and the
//! exports of the units it imports, which hold no text position, so an edit inside a unit that
//! keeps its names resolves none of its importers again; each unit a resolution reads is in its
//! key as its path, a tag byte (resolved import, failed import, or prelude) and then the number
//! of its exports or why the import failed. The front end (lexing through elaboration) is keyed by
//! the unit's text and the build it is compiled for (step L2.8d), since every structure before
//! the kernel terms carries byte spans and so
//! changes with any edit. Step L2.8 adds a unit's content address, keyed by its text as the front
//! end is and computed from the front end's result, so a build that checks or writes the pins of
//! many importers of one unit addresses it once. A row of a function's `test` table is keyed by its
//! check and the definitions the check reaches, and a row of `main`'s table by its key, its value,
//! the ports, and the definitions `main` and those terms reach: kernel terms carry no spans, so
//! an edit that leaves those definitions alone (a comment, another function, another row)
//! reuses the row's result. This cutoff is the point of the structure.
//!
//! The keys are syntactic, as step L1.30 allows: a key holds the terms' printed form, with
//! binders named by level and written name and definitions by written name (`Db::cone`), so
//! moving a definition changes no key (FAIL-queries-reorder) while two
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
//! Each query records what it read when it is computed (step L1.30a; DESIGN.md sec:incremental,
//! "The compiler's own stages are derived the same way", item 3): a row, each definition its
//! cone reaches ([`Read::Definition`], by its number and written name); a unit's resolution, the
//! resolution of each unit it imports and of the prelude unit it sees; a unit's address, the
//! front end it reads ([`Read::Query`]). The front end, a unit's parse and its check read their
//! text and the build alone, which are their keys, so they record nothing. The database keeps
//! the reverse map from each read to the queries that read it ([`Db::readers`]). No result
//! depends on the records; step L7.13 propagates a change along the reverse map. A query
//! answered from what is kept records nothing again, so an edit that recomputes no query (a
//! comment) changes no record.
//!
//! Where DESIGN.md does not say: results are kept for the life of the [`Db`] and never
//! evicted, which a long-lived process (the language server, step L25.1) must bound; the
//! interpreter and the prelude are fixed for one build of the compiler, so they are not in
//! a key.

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::Term;

use crate::ast::Error;
use crate::build::Build;
use crate::canon::binders::keyed;
use crate::elab::Cones;
use crate::front::{self, Front, Parsed};
use crate::pin::{self, Address};
use crate::resolve::{Exports, Resolved};

/// A query's key: its inputs, encoded.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Key(pub Box<[u8]>);

/// What a query read (step L1.30a).
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Read {
    /// A definition of the unit: the number the database gave its text ([`Db::cone`]), which a
    /// row's key holds, and its written name.
    Definition(u64, Arc<str>),
    /// The result of another query, by its key.
    Query(Query, Key),
}

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
    let k = front_key(text, build);
    if let Some(f) = front.get(&k) {
        return f.clone();
    }
    *computed.entry(Query::Front).or_default() += 1;
    let f = Arc::new(front::compile(text, build));
    front.insert(k, f.clone());
    f
}

/// The key of the front end's result for the unit `text` built for `build`.
fn front_key(text: &str, build: &Build) -> Key {
    key("front", &[text.as_bytes(), &build.bytes()])
}

/// The queries.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
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
    /// What each query computed read, in the order computed: its query, its key and its reads
    /// (step L1.30a). A query that read nothing has no record.
    records: Vec<(Query, Key, Box<[Read]>)>,
    /// The position in `records` of each recorded query, by query and key.
    recorded: HashMap<Query, HashMap<Key, usize>>,
    /// The reverse map: the positions in `records` of the queries that read each read.
    readers: HashMap<Read, Vec<usize>>,
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
static STAMPS: zed_graph::IdSource = zed_graph::IdSource::starting_at(0);

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
            records: Vec::new(),
            recorded: HashMap::new(),
            readers: HashMap::new(),
            texts: HashMap::new(),
            exports: HashMap::new(),
            build: Build::default(),
            stamp: STAMPS.next(),
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
            records: self.records.clone(),
            recorded: self.recorded.clone(),
            readers: self.readers.clone(),
            texts: self.texts.clone(),
            exports: self.exports.clone(),
            build: self.build.clone(),
            stamp: STAMPS.next(),
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
    /// database's build, before they are placed (`front::rejection`): empty when it compiles.
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
    /// when none is kept, which then records `reads`: the resolutions it reads.
    pub fn resolve(
        &mut self,
        k: Key,
        reads: Vec<Read>,
        compute: impl FnOnce() -> Resolved,
    ) -> Arc<Resolved> {
        if let Some(r) = self.resolved.get(&k) {
            return r.clone();
        }
        *self.computed.entry(Query::Resolve).or_default() += 1;
        let r = Arc::new(compute());
        self.record(Query::Resolve, &k, reads);
        self.resolved.insert(k, r.clone());
        r
    }

    /// The content address of the unit `text` (step L2.8), whose top level defines `exports`:
    /// `None` when the unit does not compile alone. Keyed by the text and the build it is
    /// compiled for, since `exports` is a function of the text. The unit is compiled for this
    /// database's build with every option off ([`Build::pinned`]), so the options a build
    /// turns on leave its pins as they are. `front_at` elaborates and evaluates nothing, so
    /// every string the unit's terms hold is a literal of `text`, a name or a target name, and
    /// [`crate::pin::address`] writes each as its bytes (author answer A106, 2026-11-20): the
    /// cost is O(t log t + B) for terms of size t whose literals hold B bytes at all their
    /// nodes (row PROOF-address-reads-literals-only, proof in
    /// crates/zedc-zir/src/canon/serial.rs).
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
        let read = Read::Query(Query::Front, front_key(text, &pinned));
        self.record(Query::Address, &k, vec![read]);
        self.addresses.insert(k, a.clone());
        a
    }

    /// The result of the table row `q` under `k`, computing it with `check` when no result
    /// is kept, which then records `reads`: the definitions the row reaches ([`Db::cone`]).
    pub fn row(
        &mut self,
        q: Query,
        k: Key,
        reads: Vec<Read>,
        check: impl FnOnce() -> Result<(), String>,
    ) -> Result<(), String> {
        let rows = self.rows.entry(q).or_default();
        if let Some(r) = rows.get(&k) {
            return r.clone();
        }
        *self.computed.entry(q).or_default() += 1;
        let r = check();
        rows.insert(k.clone(), r.clone());
        self.record(q, &k, reads);
        r
    }

    /// Records that the query `q` computed under `k` read `reads`, and enters it in the reverse
    /// map under each: nothing when it read nothing. Each query is computed once under a key,
    /// so it is recorded once.
    // Complexity tradeoff: a reader in the reverse map is the position of its record, not its
    // key, which for a row holds a number per definition it reaches: entering the key under
    // each of a row's r reads would copy O(r) bytes r times, O(r²), where a position costs
    // O(1). The record costs O(r) entries, one hash of each read (a definition's name, or a
    // key of the query read, whose bytes the caller built already), and the key twice, in the
    // record and in `recorded`.
    fn record(&mut self, q: Query, k: &Key, reads: Vec<Read>) {
        if reads.is_empty() {
            return;
        }
        let at = self.records.len();
        for r in &reads {
            self.readers.entry(r.clone()).or_default().push(at);
        }
        self.recorded.entry(q).or_default().insert(k.clone(), at);
        self.records.push((q, k.clone(), reads.into_boxed_slice()));
    }

    /// Every record: each query computed that read something, its key and what it read, in
    /// the order computed.
    pub fn records(&self) -> impl Iterator<Item = (Query, &Key, &[Read])> {
        (self.records.iter()).map(|(q, k, reads)| (*q, k, &**reads))
    }

    /// What the query `q` read when computed under `k`; `None` when it read nothing or was not
    /// computed.
    pub fn reads(&self, q: Query, k: &Key) -> Option<&[Read]> {
        let at = *self.recorded.get(&q)?.get(k)?;
        Some(&self.records[at].2)
    }

    /// The queries that read `r`, each by its query and key, in the order computed.
    pub fn readers(&self, r: &Read) -> impl Iterator<Item = (Query, &Key)> {
        (self.readers.get(r).into_iter().flatten())
            .map(|&at| (self.records[at].0, &self.records[at].1))
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

    /// The numbers of the definitions of the unit of `cones` that `roots` reach, in increasing
    /// order, followed by the roots' syntactic bytes: what a term evaluated under the unit can
    /// read. A definition's number is that of its text, given once per unit, so the key of a
    /// row costs the size of its roots and the number of definitions they reach.
    ///
    /// Nothing in the key depends on where a definition or a case stands in the unit
    /// (FAIL-queries-reorder): each term is printed in [`keyed`] form, its binders by level
    /// and written name rather than by the unit-wide numbers elaboration gives them, and each
    /// definition it names by [`Cones::key_name`]; and the numbers are sorted, not in the
    /// unit's order. A definition's text holds the names of those it reads, so the set of
    /// texts gives the definitions and how they read each other whatever their order, and
    /// closing a term over them in any order each after those it uses gives one value.
    // Complexity tradeoff: printing each term with `Debug` as elaboration names it costs O(t)
    // for a term of size t, but its names count binders over the whole unit, so moving a
    // definition recomputed every row after it. The keyed form costs O(t log t), the
    // canonicalizer's walk (`canon::binders`), once per definition, whose number is kept, and
    // once per root of each row; sorting the numbers costs O(d log d) for d definitions
    // reached, which `Cones::reach` already pays to collect them in a `BTreeSet`.
    ///
    /// With the bytes, the reads a row keyed by them records ([`Db::row`]): each definition
    /// reached, by its number and written name, in the unit's order.
    pub fn cone(&mut self, cones: &Cones<'_>, roots: &[&Term]) -> (Vec<u8>, Vec<Read>) {
        let mut out = Vec::new();
        let mut put = |s: &[u8]| {
            out.extend_from_slice(&(s.len() as u64).to_le_bytes());
            out.extend_from_slice(s);
        };
        let free = |x: &str| cones.key_name(x);
        let texts = &mut self.texts;
        let mut ids = Vec::new();
        let mut reads = Vec::new();
        for i in cones.reach(roots) {
            let n = cones.number(i, self.stamp, |d| {
                let name = cones
                    .key_name(&d.kernel)
                    .unwrap_or_else(|| d.kernel.clone());
                let text = format!("{name}={:?}", keyed(&d.term, &free));
                let n = texts.len() as u64;
                *texts.entry(text.into()).or_insert(n)
            });
            ids.push(n);
            reads.push(Read::Definition(n, cones.def(i).name.as_str().into()));
        }
        ids.sort_unstable();
        for id in ids {
            put(&id.to_le_bytes());
        }
        for t in roots {
            put(format!("{:?}", keyed(t, &free)).as_bytes());
        }
        (out, reads)
    }
}
