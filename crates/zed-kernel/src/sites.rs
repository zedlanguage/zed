//! Source sites of terms (plan row RT-sites): a table from a term node to the span of the
//! program's source it was elaborated from, kept beside the terms, so that a term, its printed
//! form and its identity are what they were without it.
//!
//! A node is named by the address one past the end of the buffer of its own parts: the
//! arguments of a call or a primitive, the arms of a `match`. The buffer is on the heap, so
//! the name stays the same when the node is moved, and two nodes alive at once never share
//! it. A node with no parts of its own has no name and no site; an error at one is placed by
//! the nearest node around it that has one. The address is used only as a name, to look a
//! node up while it is alive, never for order or in a memo (author decision node-ids).
//!
//! While the front end and staging build the program they record sites
//! ([`Recorder::start`]): elaboration marks the nodes it built for each expression
//! ([`mark`]), a copy of a node takes the node's site ([`inherit`]), and a node that is dropped
//! loses its site (`Drop for Term`), so that a buffer freed and used again for another node does
//! not pass the site on. At the end the sites of the nodes the program holds are kept
//! ([`Recorder::freeze`]); the rest of the run reads them and records nothing.
//!
//! Method: a table beside the code, keyed by a position in it, as DWARF's line number program
//! maps machine addresses to source lines (DWARF Debugging Information Format Committee,
//! *DWARF Debugging Information Format, Version 5*, 2017, section 6.2). The plan row names a
//! table built at lowering; lowering reads terms, which hold no spans, so the spans are taken
//! here, where elaboration still has them, and lowering turns this table into one by graph
//! node (`lower_sited` in `zedc_zir::zir::lower`).
//
// Complexity tradeoff: while recording, each node built, copied or dropped costs one hash
// table operation, O(1) expected, and the table holds a word and a span for each node alive,
// where a span stored in each `Term` would cost nothing to look up but would change the term's
// layout, its printed form and its identity. Freezing walks the program once, O(n) for n
// nodes. Off, as in every run after the program is built, each drop and copy reads one
// thread-local flag. Measured: loading a program of n joins with sites, n = 200 and 1600,
// takes 7.9 times the instructions and 7.9 times the bytes
// (`l01_36a_executables::sites::loading_with_sites_scales`, 2026-11-13).

use std::collections::{HashMap, HashSet};

use crate::site_table;
pub use crate::site_table::Span;
use crate::term::{Shared, Term};

/// The name of `t` while it is alive: the address one past the end of its own parts, or
/// `None` when it has none. O(1).
pub fn key(t: &Term) -> Option<usize> {
    t.site_key()
}

/// The address one past the last element of `xs`.
pub fn end<T>(xs: &[T]) -> usize {
    crate::term::parts_end(xs)
}

/// The sites of the nodes of a program, frozen: read while it runs, never changed.
#[derive(Default, Debug)]
pub struct Sites {
    at: HashMap<usize, Span>,
}

impl Sites {
    /// The site of the node named `key`, if it has one. O(1).
    pub fn at(&self, key: usize) -> Option<Span> {
        self.at.get(&key).copied()
    }

    /// The site of `t`, if it has one. O(1).
    pub fn of(&self, t: &Term) -> Option<Span> {
        key(t).and_then(|k| self.at(k))
    }

    /// How many nodes have a site.
    pub fn len(&self) -> usize {
        self.at.len()
    }

    /// Whether no node has a site.
    pub fn is_empty(&self) -> bool {
        self.at.is_empty()
    }
}

/// Records sites on this thread until it is frozen or dropped.
pub struct Recorder {
    /// The table and the flag of a recording this one interrupted, put back at the end.
    outer: Option<(HashMap<usize, Span>, bool)>,
}

impl Recorder {
    /// Starts recording on this thread, with the sites of `seed`, which must name only nodes
    /// still alive. A recording already running is put aside until this one ends.
    pub fn start(seed: &Sites) -> Recorder {
        Recorder {
            outer: Some(site_table::swap(seed.at.clone(), true)),
        }
    }

    /// Ends the recording and keeps the sites of the nodes `roots` hold, each shared part
    /// visited once: O(n) for the n nodes the roots reach. The nodes recorded that the roots
    /// do not reach are dropped from the table, since nothing keeps them alive.
    pub fn freeze<'a>(mut self, roots: impl IntoIterator<Item = &'a Term>) -> Sites {
        let table = self.end();
        let mut at = HashMap::new();
        let mut seen = HashSet::new();
        let mut todo: Vec<&Term> = roots.into_iter().collect();
        while let Some(t) = todo.pop() {
            if let Some(k) = key(t)
                && let Some(&s) = table.get(&k)
            {
                at.insert(k, s);
            }
            parts(t, &mut seen, &mut todo);
        }
        Sites { at }
    }

    /// Ends the recording: puts back the one it interrupted, and gives this one's table.
    fn end(&mut self) -> HashMap<usize, Span> {
        match self.outer.take() {
            Some((table, on)) => site_table::swap(table, on).0,
            None => HashMap::new(),
        }
    }
}

impl Drop for Recorder {
    fn drop(&mut self) {
        self.end();
    }
}

/// Pushes the parts of `t` onto `todo`: each inline part, and each shared part not in `seen`.
fn parts<'a>(t: &'a Term, seen: &mut HashSet<u64>, todo: &mut Vec<&'a Term>) {
    let mut shared = |s: &'a Shared, todo: &mut Vec<&'a Term>| {
        if seen.insert(s.id()) {
            todo.push(s);
        }
    };
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => {}
        Term::Lam(_, b) | Term::Push(_, b) => shared(b, todo),
        Term::App(f, args) => {
            shared(f, todo);
            todo.extend(args);
        }
        Term::Prim(_, args) => todo.extend(args),
        Term::Match(e, arms) => {
            shared(e, todo);
            todo.extend(arms.iter().map(|(_, b)| b));
        }
        Term::Let(_, a, b) | Term::Discard { family: a, sel: b } => {
            shared(a, todo);
            shared(b, todo);
        }
        Term::Fam { domain, body, .. } => {
            shared(domain, todo);
            shared(body, todo);
        }
        Term::If(a, b, c)
        | Term::Reindex {
            family: a,
            kf: b,
            vf: c,
            ..
        }
        | Term::Gen {
            init: a,
            step: b,
            guard: c,
            ..
        } => {
            shared(a, todo);
            shared(b, todo);
            shared(c, todo);
        }
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => {
            shared(family, todo);
            shared(op, todo);
            if let Some(i) = identity {
                shared(i, todo);
            }
        }
        Term::Fix {
            init, step, kind, ..
        } => {
            shared(init, todo);
            shared(step, todo);
            if let crate::term::FixKind::Lattice { join } = kind {
                shared(join, todo);
            }
        }
    }
}

/// Whether this thread records sites. O(1).
pub fn recording() -> bool {
    site_table::recording()
}

/// Gives `span` to each node of `t` that has no site yet, stopping at the nodes that have one;
/// a shared part is entered once over all calls that pass the same `seen`. Elaboration calls
/// it when an expression is done, inner expressions first, so each node takes the span of the
/// innermost expression that built it. Each node is given a site once and passed by later
/// calls only at the edge of the marked part, so the calls cost O(n) in all for n nodes, and
/// O(1) more each. Does nothing when this thread is not recording.
pub fn mark(t: &Term, span: Span, seen: &mut HashSet<u64>) {
    if !recording() {
        return;
    }
    site_table::with(|table| {
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            if let Some(k) = key(t) {
                if table.contains_key(&k) {
                    continue;
                }
                table.insert(k, span);
            }
            parts(t, seen, &mut todo);
        }
    });
}

/// Gives `to` the site of `from` when `to` has none: a node staging built in place of
/// `from`, or a copy of it. O(1).
pub fn inherit(from: &Term, to: &Term) {
    if !recording() {
        return;
    }
    if let (Some(f), Some(t)) = (key(from), key(to)) {
        site_table::copy(f, t);
    }
}
