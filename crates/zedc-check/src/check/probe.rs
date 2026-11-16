//! Counters for row FAIL-map-chain-step0: on the eager path of `Ck`, which calls design D
//! of row FAIL-map-chain-needs-quadratic ("defer and force") would admit, and, at each later
//! read or write of a class, whether the item D keeps at such a call (a "forward") would
//! have to be written out ("forced") there. D itself is not built; the eager path runs as it
//! does without the counters, and the counters only watch it.
//!
//! On only under `cfg(test)` or the feature `forward-probe`; otherwise `Classes` is the
//! plain `Vec<Class>` it stands for and every hook below is compiled out, so a release build
//! is the same code as before.
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
pub(super) type Classes = Vec<super::Class>;

#[cfg(any(test, feature = "forward-probe"))]
pub(super) use on::Classes;
#[cfg(any(test, feature = "forward-probe"))]
pub use on::last_report;

#[cfg(any(test, feature = "forward-probe"))]
mod on {
    use std::cell::RefCell;
    use std::collections::hash_map::DefaultHasher;
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
    use std::hash::{Hash, Hasher};
    use std::io::Write;
    use std::ops::{Index, IndexMut};
    use std::panic::Location;

    use zedc_syntax::lex::Span;
    use zedc_types::ty::{Need, NeedKind, Sig, Ty, Vars, class_id};

    use super::super::{Arg, Ck, Class};

    thread_local! {
        static LAST: RefCell<String> = const { RefCell::new(String::new()) };
    }

    /// The report of the last `Ck` dropped on this thread.
    pub fn last_report() -> String {
        LAST.with(|l| l.borrow().clone())
    }

    /// The classes, with the counters beside them.
    #[derive(Default)]
    pub(in crate::check) struct Classes {
        v: Vec<Class>,
        probe: RefCell<Probe>,
    }

    impl Classes {
        pub fn len(&self) -> usize {
            self.v.len()
        }

        pub fn push(&mut self, c: Class) {
            self.v.push(c);
        }

        /// The root of `k` by the parents, without counting the reads.
        fn raw_find(&self, mut k: usize) -> usize {
            while self.v[k].parent != k {
                k = self.v[k].parent;
            }
            k
        }
    }

    impl Index<usize> for Classes {
        type Output = Class;
        #[track_caller]
        fn index(&self, k: usize) -> &Class {
            self.probe.borrow_mut().hit(k, Location::caller());
            &self.v[k]
        }
    }

    impl IndexMut<usize> for Classes {
        #[track_caller]
        fn index_mut(&mut self, k: usize) -> &mut Class {
            let p = self.probe.get_mut();
            p.hit(k, Location::caller());
            if p.recording > 0 && k < p.rec_lo && !p.snaps.contains_key(&k) {
                p.snaps.insert(k, scalars(&self.v[k]));
            }
            &mut self.v[k]
        }
    }

    impl Drop for Classes {
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
    type Site = (char, &'static str, u32);

    /// What D would keep at one admitted call.
    struct Fwd {
        /// The call.
        call: String,
        /// The level of the call.
        level: usize,
        /// The needs the eager check recorded.
        size: usize,
        /// The ids of the classes the eager check made, `lo..hi`.
        lo: usize,
        hi: usize,
        /// The keys of the needs it recorded, by the root they were recorded on.
        keys: HashMap<usize, HashSet<u64>>,
        /// Its watched roots: the arguments' roots and the result's classes.
        watched: BTreeSet<usize>,
        /// The sites that touched it, in order of first touch.
        sites: Vec<Site>,
        seen: HashSet<Site>,
        /// `kept` or `escaped` once its level ended.
        end: Option<&'static str>,
    }

    /// An admitted call whose needs are being checked.
    pub(in crate::check) struct Rec {
        call: String,
        lo: usize,
        seq: usize,
        same_use: usize,
        errors: usize,
    }

    #[derive(Default)]
    struct Probe {
        /// How many admitted calls' needs are being checked, one inside another; only the
        /// outermost makes a forward, and nothing is counted while it runs.
        recording: usize,
        /// The first class id the outermost of them made.
        rec_lo: usize,
        /// The scalar fields of each older class it wrote, as they were before.
        snaps: HashMap<usize, Vec<(&'static str, String)>>,
        /// The keys of the needs it recorded, with the root.
        keys: Vec<(usize, u64)>,
        fwds: Vec<Fwd>,
        /// The forwards each class id is internal to, and each watched root is watched by.
        internal: HashMap<usize, Vec<usize>>,
        roots: HashMap<usize, Vec<usize>>,
        /// Calls with needs, by the first admission rule they fail, or `admit`.
        admit: BTreeMap<String, u64>,
        /// Scalar fields of older classes the checks of admitted calls changed, by field.
        scalar: BTreeMap<&'static str, u64>,
        /// Pushes to `same_use` and `errors` those checks made.
        same_use: u64,
        errors: u64,
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

        fn add(&mut self, f: usize, site: Site) {
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

        fn event(&mut self, k: usize, what: &'static str) {
            if self.recording > 0 {
                return;
            }
            for (_, f) in self.watchers(k) {
                self.add(f, ('E', what, 0));
            }
        }

        fn report(&mut self) -> String {
            let mut s = String::new();
            let admit: Vec<String> = (self.admit.iter()).map(|(k, n)| format!("{k}={n}")).collect();
            s.push_str(&format!("A {}\n", admit.join(" ")));
            let scalar: Vec<String> =
                (self.scalar.iter()).map(|(k, n)| format!("{k}={n}")).collect();
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

    /// The fields D says a forward never writes on a class that existed at the call, each
    /// shown as text. A field whose type has no `Debug` is shown by its length.
    fn scalars(c: &Class) -> Vec<(&'static str, String)> {
        vec![
            ("parent", c.parent.to_string()),
            ("rank", c.rank.to_string()),
            ("mask", c.mask.to_string()),
            ("level", c.level.to_string()),
            ("lits", c.lits.len().to_string()),
            ("reasons", c.reasons.len().to_string()),
            ("resolved", format!("{:?}", c.resolved)),
            ("name", format!("{:?}", c.name)),
            ("flowed", c.flowed.len().to_string()),
            ("size", c.size.to_string()),
            ("proof", format!("{:?}", c.proof.as_ref().map(|p| p.0))),
            ("binder", format!("{:?}", c.binder)),
            ("generic", c.generic.to_string()),
            ("asked", c.asked.to_string()),
            ("floats", c.floats.to_string()),
            ("rat", c.rat.to_string()),
            ("given", c.given.to_string()),
            ("narrowed_to", format!("{:?}", c.narrowed_to)),
            ("narrows", c.narrows.to_string()),
            ("decimal", c.decimal.to_string()),
        ]
    }

    fn key_hash(key: &(NeedKind, bool)) -> u64 {
        let mut h = DefaultHasher::new();
        key.hash(&mut h);
        h.finish()
    }

    /// The name of a need kind, for the count of calls F1 refuses by kind.
    fn kind_name(k: &NeedKind) -> &'static str {
        match k {
            NeedKind::Component { .. } => "Component",
            NeedKind::Index(_) => "Index",
            NeedKind::Destructure { .. } => "Destructure",
            NeedKind::Call { .. } => "Call",
            NeedKind::Data(..) => "Data",
            NeedKind::Into { .. } => "Into",
            NeedKind::Payload { .. } => "Payload",
            NeedKind::Narrow(_) => "Narrow",
            NeedKind::Order { .. } => "Order",
            NeedKind::NoInt(_) => "NoInt",
            NeedKind::Power(_) => "Power",
            NeedKind::InDomain { .. } => "InDomain",
            NeedKind::Sum => "Sum",
            NeedKind::Entries => "Entries",
            NeedKind::SumMethod { .. } => "SumMethod",
            NeedKind::Map { .. } => "Map",
            NeedKind::Group { .. } => "Group",
            NeedKind::Remap { .. } => "Remap",
            NeedKind::Reduce(..) => "Reduce",
            NeedKind::Fold { .. } => "Fold",
        }
    }

    impl<'t, 'a> Ck<'t, 'a> {
        fn probe_count(&self, why: &str) {
            *self.classes.probe.borrow_mut().admit.entry(why.into()).or_default() += 1;
        }

        /// Before `apply_one` checks the needs of `sig` at a call on `args`: counts the first
        /// rule of D the call fails, and for an admitted call starts recording what the check
        /// writes. `partial` is whether the call leaves parameters out.
        // Complexity tradeoff: O(size of the needs + arguments) per call, a second walk of the
        // needs beside the one `replay` makes; on only in tests and under the feature.
        pub(in crate::check) fn probe_admit(
            &mut self,
            sig: &Sig,
            args: &[Option<Arg<'a>>],
            partial: bool,
            call: Span,
        ) -> Option<Rec> {
            if sig.needs.is_empty() {
                return None;
            }
            if self.classes.probe.borrow().recording > 0 {
                self.probe_count("nested-in-admitted");
                return None;
            }
            let why: Option<String> = 'why: {
                if !sig.bounds.is_empty() {
                    break 'why Some("F1-bounds".into());
                }
                for n in &sig.needs {
                    if !matches!(
                        n.kind,
                        NeedKind::Entries | NeedKind::Call { .. } | NeedKind::Map { .. }
                    ) {
                        break 'why Some(format!("F1-kind-{}", kind_name(&n.kind)));
                    }
                }
                let mut vars = Vars::default();
                sig.needs.iter().for_each(|n| n.vars_in(&mut vars));
                if vars.order.iter().any(|v| self.is_class(v)) {
                    break 'why Some("F1-free-class".into());
                }
                if self.trying {
                    break 'why Some("F2-trying".into());
                }
                if partial || !self.leaving.is_empty() {
                    break 'why Some("F2-partial".into());
                }
                if !self.refused.is_empty() {
                    break 'why Some("F2-refused".into());
                }
                for a in args {
                    let Some(a) = a else {
                        break 'why Some("F2-arg-missing".into());
                    };
                    let pieces = a.ty.pieces();
                    let one = match &pieces[..] {
                        [p] if a.lit.is_none() && a.branches.is_none() => self.class_of(p),
                        _ => None,
                    };
                    let Some(r) = one else {
                        break 'why Some("F2-arg-not-class".into());
                    };
                    let c = &self.classes[r];
                    if !c.flowed.is_empty() || c.data {
                        break 'why Some("F2-root-flowed-or-data".into());
                    }
                    if c.level > self.level {
                        break 'why Some("F2-root-deeper".into());
                    }
                }
                None
            };
            if let Some(why) = why {
                self.probe_count(&why);
                return None;
            }
            self.probe_count("admit");
            let lo = self.classes.len();
            let p = self.classes.probe.get_mut();
            p.recording += 1;
            p.rec_lo = lo;
            p.snaps.clear();
            p.keys.clear();
            Some(Rec {
                call: format!("{}..{}", call.start, call.end),
                lo,
                seq: self.needs,
                same_use: self.same_use.len(),
                errors: self.errors.len(),
            })
        }

        /// After the needs of the admitted call `rec` were checked: compares the older classes
        /// it wrote with their snapshots, and makes its forward. `result` is the call's result
        /// type, with the check's bindings put in.
        pub(in crate::check) fn probe_recorded(&mut self, rec: Rec, args: &[Option<Arg<'a>>], result: &Ty) {
            let hi = self.classes.len();
            let mut watched = BTreeSet::new();
            for a in args.iter().flatten() {
                for v in a.ty.var_facts().classes {
                    if let Some(k) = class_id(&v).filter(|&k| k < hi) {
                        watched.insert(self.classes.raw_find(k));
                    }
                }
            }
            let mut exit = BTreeSet::new();
            for v in result.var_facts().classes {
                if let Some(k) = class_id(&v).filter(|&k| k < hi) {
                    let r = self.classes.raw_find(k);
                    watched.insert(r);
                    exit.insert(k);
                    exit.insert(r);
                }
            }
            let snaps = std::mem::take(&mut self.classes.probe.get_mut().snaps);
            let mut changed: Vec<&'static str> = Vec::new();
            for (k, before) in &snaps {
                let now = scalars(&self.classes.v[*k]);
                for ((name, b), (_, n)) in before.iter().zip(&now) {
                    if b != n {
                        changed.push(name);
                    }
                }
            }
            let (same_use, errors) = (
                self.same_use.len() - rec.same_use,
                self.errors.len() - rec.errors,
            );
            let size = self.needs - rec.seq;
            let level = self.level;
            let p = self.classes.probe.get_mut();
            p.recording -= 1;
            for name in changed {
                *p.scalar.entry(name).or_default() += 1;
            }
            p.same_use += same_use as u64;
            p.errors += errors as u64;
            let f = p.fwds.len();
            let mut keys: HashMap<usize, HashSet<u64>> = HashMap::new();
            for (r, h) in std::mem::take(&mut p.keys) {
                keys.entry(r).or_default().insert(h);
            }
            for k in rec.lo..hi {
                if !exit.contains(&k) {
                    p.internal.entry(k).or_default().push(f);
                }
            }
            for &r in &watched {
                p.roots.entry(r).or_default().push(f);
            }
            p.fwds.push(Fwd {
                call: rec.call,
                level,
                size,
                lo: rec.lo,
                hi,
                keys,
                watched,
                sites: Vec::new(),
                seen: HashSet::new(),
                end: None,
            });
        }

        /// At `need` on root `r` with `key`: while an admitted call's needs are checked, notes
        /// the key; else names the event for each forward that watches `r`.
        pub(in crate::check) fn probe_need(&mut self, r: usize, key: &(NeedKind, bool), span: Span) {
            let h = key_hash(key);
            // A key the root holds already gives the old result; only a new one is recorded.
            // `need` records every key it does not find, so this is the key of a record the
            // forward makes (or, for an `Order` key, joins; F1 admits no `Order` need).
            let fresh = !self.classes.v[r].known.contains_key(key);
            let p = self.classes.probe.get_mut();
            if p.recording > 0 {
                if fresh {
                    p.keys.push((r, h));
                }
                return;
            }
            let fs: Vec<usize> = (p.roots.get(&r).into_iter().flatten())
                .copied()
                .filter(|&f| p.fwds[f].end.is_none())
                .collect();
            if fs.is_empty() {
                return;
            }
            let need = Need {
                on: Ty::var(format!("${r}").into()),
                kind: key.0.clone(),
                result: None,
                span,
            };
            let mut vars = Vars::default();
            need.vars_in(&mut vars);
            let named: Vec<usize> = (vars.order.iter())
                .filter_map(|v| class_id(v))
                .filter(|&k| k < self.classes.v.len())
                .map(|k| self.classes.raw_find(k))
                .filter(|&k| k != r)
                .collect();
            let p = self.classes.probe.get_mut();
            for f in fs {
                let fwd = &p.fwds[f];
                // Lemma D of the design: a key that names a class outside the forward's watched
                // roots and internal range cannot equal a key it deferred, so D does not force
                // (`need-outside`); a key that names no class (`need-noclass`) or only such
                // classes (`need-inside`) D forces. `need-collide` is the exact case: the key
                // equals one the forward recorded on this root, so eager finds it in `known`.
                let ours = |k: &usize| fwd.watched.contains(k) || (fwd.lo..fwd.hi).contains(k);
                let what = if fwd.keys.get(&r).is_some_and(|ks| ks.contains(&h)) {
                    "need-collide"
                } else if named.is_empty() {
                    "need-noclass"
                } else if named.iter().all(ours) {
                    "need-inside"
                } else {
                    "need-outside"
                };
                p.add(f, ('E', what, 0));
            }
        }

        /// A named event at class `k`.
        pub(in crate::check) fn probe_event(&mut self, k: usize, what: &'static str) {
            self.classes.probe.get_mut().event(k, what);
        }

        /// At `generalize` of `level`: each open forward of the level is kept if every class
        /// it made or watches is still of that level, else escaped.
        pub(in crate::check) fn probe_generalize(&mut self, level: usize) {
            let fwds = &self.classes.probe.get_mut().fwds;
            let open: Vec<usize> = (0..fwds.len())
                .filter(|&f| fwds[f].end.is_none() && fwds[f].level == level)
                .collect();
            for f in open {
                let (lo, hi, watched) = {
                    let fwd = &self.classes.probe.get_mut().fwds[f];
                    (fwd.lo, fwd.hi, fwd.watched.clone())
                };
                let stays = (lo..hi).chain(watched).all(|k| {
                    let r = self.classes.raw_find(k);
                    self.classes.v[r].level == level
                });
                self.classes.probe.get_mut().fwds[f].end =
                    Some(if stays { "kept" } else { "escaped" });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::last_report;

    /// The probe's report for the unit `text`, checked alone.
    fn report(text: &str) -> String {
        let tokens = zedc_syntax::lex::lex(text).expect("the unit lexes");
        let (tree, errors) = zedc_syntax::parse::parse_unit(text, &tokens, zedc_syntax::parse::TOP);
        assert!(errors.is_empty(), "the unit parses");
        let unit = zedc_syntax::ast::unit(text, &tokens, &tree).expect("the unit builds");
        let res = zedc_resolve::resolve::resolve(&unit).expect("the unit resolves");
        let info = super::super::walk::check(&unit, &res);
        assert!(info.errors.is_empty(), "the unit checks");
        last_report()
    }

    fn forwards(r: &str) -> Vec<&str> {
        r.lines().filter(|l| l.starts_with("F ")).collect()
    }

    /// `h1` calls `h0`, whose one need is a call of its parameter `f`: the call is admitted
    /// (its arguments are `h1`'s own parameters), its needs record one need, nothing reads
    /// the record before `h1` ends, and `h1`'s end keeps it. The call of `h1` at the top
    /// passes a lambda and a literal, no classes, and is not admitted.
    #[test]
    fn a_call_of_a_generic_function_on_parameters_is_admitted_and_kept() {
        let r = report(
            "h0(positional f, positional x) = f(x);\n\
             h1(positional f, positional x) = h0(f, x);\n\
             a = h1(y -> y + 1, 1);\n",
        );
        assert!(r.starts_with("A F2-arg-not-class=1 admit=1\n"), "{r}");
        assert!(r.contains("\nS scalar[] same_use=0 errors=0\n"), "{r}");
        let fs = forwards(&r);
        assert_eq!(fs.len(), 1, "{r}");
        assert!(fs[0].contains(" level=1 size=1 internal=1 end=kept "), "{r}");
        assert!(!fs[0].contains("E:need"), "{r}");
    }

    /// A second call of `f` on `x` after the call of `h0` is a need equal to the one the
    /// forward recorded on `f`'s class: eager finds it in `known`, so D must force there.
    #[test]
    fn a_need_equal_to_a_deferred_one_collides() {
        let r = report(
            "h0(positional f, positional x) = f(x);\n\
             h1(positional f, positional x) = (h0(f, x), f(x));\n\
             a = h1(y -> y + 1, 1);\n",
        );
        let fs = forwards(&r);
        assert_eq!(fs.len(), 1, "{r}");
        assert!(fs[0].contains("E:need-collide"), "{r}");
    }

    /// Negative control: no function calls a generic function on classes, so no call is
    /// admitted and no forward is made.
    #[test]
    fn no_generic_call_on_classes_makes_no_forward() {
        let r = report(
            "h0(positional f, positional x) = f(x);\n\
             a = h0(y -> y + 1, 1);\n",
        );
        assert!(r.starts_with("A F2-arg-not-class=1\n"), "{r}");
        assert!(forwards(&r).is_empty(), "{r}");
    }
}
