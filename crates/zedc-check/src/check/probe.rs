//! Counters for row FAIL-map-chain-step0: on the eager path of `Ck`, which calls design D
//! of row FAIL-map-chain-needs-quadratic ("defer and force") would admit, and, at each later
//! read or write of a class, whether the item D keeps at such a call (a "forward") would
//! have to be written out ("forced") there. D itself is not built; the eager path runs as it
//! does without the counters, and the counters only watch it. Findings:
//! /home/luke/Work/wt/cd-xr/FAIL-map-chain-needs-quadratic/STEP0.md.
//!
//! On only under `cfg(test)` or the feature `forward-probe`; otherwise `Classes` is the
//! plain `Vec` it stands for and every hook is compiled out, so a release build is the same
//! code as before. This file holds the store of the counters, which names no item of the
//! checker (so the checker's module can name `Classes` and call `Classes::event` with no
//! import cycle); the hooks `walk.rs` calls are in `probe/hooks.rs`, and the tests, which
//! call the checker, in `probe/tests.rs`.
//!
//! What is counted:
//! - At each call `apply_one` checks the needs of (a callee with needs), the first of D's
//!   admission rules F1 and F2 that the call fails, or `admit`.
//! - For each admitted call, a forward: the classes the eager check of its needs made
//!   (its internal classes, a range of ids), the roots of its arguments' classes and the
//!   classes of its result (its watched roots), the keys each need it recorded had on each
//!   root, and the number of needs it recorded.
//! - Each later index of `classes` at an id the forward watches: the source line of the
//!   index, once per forward and line, in order of first touch (`R` for a watched root the
//!   forward recorded needs on, `W` for another watched root, `I` for an internal class);
//!   and named events: `touch-trying` (`touch` under a trial), `lower-walk` (`lower` passes
//!   its skip test and reads `uses`), and at `need` on a watched root, `need-collide` (the
//!   key is one the forward recorded on that root, so eager finds it in `known` and D would
//!   not), else `need-noclass` (the key's kind names no class), `need-inside` (it names
//!   only classes the forward watches or made) or `need-outside` (it names another class,
//!   the case of D's Lemma D).
//! - At `generalize` of the forward's level: `kept` if every class of the forward is still
//!   at that level (D keeps it as one item of the signature), else `escaped` (D forces it).
//! - While the needs of an admitted call are checked: each scalar field (every field but
//!   `uses`, `known`, `orders`, `order_of` and `data`) of an older class that the check
//!   changed, and the pushes to `same_use` and `errors` it made. D's claim is that there are
//!   none.
//!
//! Each `Ck` writes one report when it is dropped: to the thread's last report, which
//! `last_report` gives, and, when the variable `ZED_FORWARD_PROBE` names a file, appended
//! to that file, each line headed by the thread's name.

#[cfg(not(any(test, feature = "forward-probe")))]
pub(super) type Classes<C> = Vec<C>;

#[cfg(any(test, feature = "forward-probe"))]
pub(super) use on::Classes;
#[cfg(any(test, feature = "forward-probe"))]
pub use on::last_report;

#[cfg(any(test, feature = "forward-probe"))]
mod hooks;
#[cfg(test)]
mod tests;

#[cfg(any(test, feature = "forward-probe"))]
mod on {
    use std::cell::RefCell;
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
    use std::io::Write;
    use std::ops::{Index, IndexMut};
    use std::panic::Location;

    thread_local! {
        static LAST: RefCell<String> = const { RefCell::new(String::new()) };
    }

    /// The report of the last `Ck` dropped on this thread.
    pub fn last_report() -> String {
        LAST.with(|l| l.borrow().clone())
    }

    /// What the store reads of a class: its parent, and the fields D says a forward never
    /// writes on a class that existed at the call, each shown as text.
    pub(in crate::check) trait Watched {
        fn parent(&self) -> usize;
        fn scalars(&self) -> Vec<(&'static str, String)>;
    }

    /// The classes, with the counters beside them.
    pub(in crate::check) struct Classes<C> {
        pub(in crate::check::probe) v: Vec<C>,
        pub(in crate::check::probe) probe: RefCell<Probe>,
    }

    impl<C> Default for Classes<C> {
        fn default() -> Self {
            Classes {
                v: Vec::new(),
                probe: RefCell::default(),
            }
        }
    }

    impl<C> Classes<C> {
        /// A named event at class `k`, for each open forward that watches it.
        pub fn event(&mut self, k: usize, what: &'static str) {
            self.probe.get_mut().event(k, what);
        }
    }

    impl<C: Watched> Classes<C> {
        pub fn len(&self) -> usize {
            self.v.len()
        }

        pub fn push(&mut self, c: C) {
            self.v.push(c);
        }

        /// The root of `k` by the parents, without counting the reads.
        pub(in crate::check::probe) fn raw_find(&self, mut k: usize) -> usize {
            while self.v[k].parent() != k {
                k = self.v[k].parent();
            }
            k
        }
    }

    impl<C: Watched> Index<usize> for Classes<C> {
        type Output = C;
        #[track_caller]
        fn index(&self, k: usize) -> &C {
            self.probe.borrow_mut().hit(k, Location::caller());
            &self.v[k]
        }
    }

    impl<C: Watched> IndexMut<usize> for Classes<C> {
        #[track_caller]
        fn index_mut(&mut self, k: usize) -> &mut C {
            let p = self.probe.get_mut();
            p.hit(k, Location::caller());
            if p.recording > 0 && k < p.rec_lo && !p.snaps.contains_key(&k) {
                p.snaps.insert(k, self.v[k].scalars());
            }
            &mut self.v[k]
        }
    }

    impl<C> Drop for Classes<C> {
        fn drop(&mut self) {
            let text = self.probe.get_mut().report();
            if let Ok(path) = std::env::var("ZED_FORWARD_PROBE") {
                let who = std::thread::current().name().unwrap_or("-").to_string();
                let mut out = String::new();
                for line in text.lines() {
                    out.push_str(&format!("{who}\t{line}\n"));
                }
                // One write per report, in append mode, so reports of threads that end at
                // once do not interleave within a line.
                if let Ok(mut f) = std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(path)
                {
                    let _ = f.write_all(out.as_bytes());
                }
            }
            LAST.with(|l| *l.borrow_mut() = text);
        }
    }

    /// Where a forward was touched: `W` a watched root, `I` an internal class, `E` a named
    /// event; the file and line of the index, or the event's name and 0.
    pub(in crate::check::probe) type Site = (char, &'static str, u32);

    /// What D would keep at one admitted call.
    pub(in crate::check::probe) struct Fwd {
        /// The call.
        pub call: String,
        /// The level of the call.
        pub level: usize,
        /// The needs the eager check recorded.
        pub size: usize,
        /// The ids of the classes the eager check made, `lo..hi`.
        pub lo: usize,
        pub hi: usize,
        /// The keys of the needs it recorded, by the root they were recorded on.
        pub keys: HashMap<usize, HashSet<u64>>,
        /// Its watched roots: the arguments' roots and the result's classes.
        pub watched: BTreeSet<usize>,
        /// The sites that touched it, in order of first touch.
        pub sites: Vec<Site>,
        pub seen: HashSet<Site>,
        /// `kept` or `escaped` once its level ended.
        pub end: Option<&'static str>,
    }

    #[derive(Default)]
    pub(in crate::check::probe) struct Probe {
        /// How many admitted calls' needs are being checked, one inside another; only the
        /// outermost makes a forward, and nothing is counted while it runs.
        pub recording: usize,
        /// The first class id the outermost of them made.
        pub rec_lo: usize,
        /// The scalar fields of each older class it wrote, as they were before.
        pub snaps: HashMap<usize, Vec<(&'static str, String)>>,
        /// The keys of the needs it recorded, with the root.
        pub keys: Vec<(usize, u64)>,
        pub fwds: Vec<Fwd>,
        /// The forwards each class id is internal to, and each watched root is watched by.
        pub internal: HashMap<usize, Vec<usize>>,
        pub roots: HashMap<usize, Vec<usize>>,
        /// Calls with needs, by the first admission rule they fail, or `admit`.
        pub admit: BTreeMap<String, u64>,
        /// Scalar fields of older classes the checks of admitted calls changed, by field.
        pub scalar: BTreeMap<&'static str, u64>,
        /// Pushes to `same_use` and `errors` those checks made.
        pub same_use: u64,
        pub errors: u64,
    }

    impl Probe {
        fn watchers(&self, k: usize) -> Vec<(char, usize)> {
            let mut out = Vec::new();
            if let Some(fs) = self.internal.get(&k) {
                out.extend(fs.iter().map(|&f| ('I', f)));
            }
            if let Some(fs) = self.roots.get(&k) {
                out.extend(fs.iter().map(|&f| ('W', f)));
            }
            out.retain(|&(_, f)| self.fwds[f].end.is_none());
            out
        }

        pub fn add(&mut self, f: usize, site: Site) {
            let fwd = &mut self.fwds[f];
            if fwd.seen.insert(site) {
                fwd.sites.push(site);
            }
        }

        fn hit(&mut self, k: usize, at: &'static Location<'static>) {
            if self.recording > 0 || self.fwds.is_empty() {
                return;
            }
            let file = at.file().rsplit('/').next().unwrap_or(at.file());
            for (tag, f) in self.watchers(k) {
                // `R`: a watched root the forward recorded needs on, whose `uses` and `known`
                // D leaves short until the force; `W`: one it recorded none on.
                let tag = match tag == 'W' && self.fwds[f].keys.contains_key(&k) {
                    true => 'R',
                    false => tag,
                };
                self.add(f, (tag, file, at.line()));
            }
        }

        pub fn event(&mut self, k: usize, what: &'static str) {
            if self.recording > 0 {
                return;
            }
            for (_, f) in self.watchers(k) {
                self.add(f, ('E', what, 0));
            }
        }

        fn report(&mut self) -> String {
            let mut s = String::new();
            let admit: Vec<String> = (self.admit.iter())
                .map(|(k, n)| format!("{k}={n}"))
                .collect();
            s.push_str(&format!("A {}\n", admit.join(" ")));
            let scalar: Vec<String> = (self.scalar.iter())
                .map(|(k, n)| format!("{k}={n}"))
                .collect();
            s.push_str(&format!(
                "S scalar[{}] same_use={} errors={}\n",
                scalar.join(" "),
                self.same_use,
                self.errors
            ));
            for f in &self.fwds {
                let sites: Vec<String> = (f.sites.iter())
                    .map(|(t, file, line)| match t {
                        'E' => format!("E:{file}"),
                        _ => format!("{t}:{file}:{line}"),
                    })
                    .collect();
                s.push_str(&format!(
                    "F call={} level={} size={} internal={} end={} sites={}\n",
                    f.call,
                    f.level,
                    f.size,
                    f.hi - f.lo,
                    f.end.unwrap_or("open"),
                    sites.join(";")
                ));
            }
            s
        }
    }
}
