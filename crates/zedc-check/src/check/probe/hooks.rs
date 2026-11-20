//! The hooks of the counters of `probe.rs` that `Ck` calls on its eager path, and their tests.

use std::collections::{BTreeSet, HashMap, HashSet};

use zedc_syntax::lex::Span;
use zedc_types::ty::{Need, NeedKind, Sig, Ty, Vars, class_id};

use super::super::{Arg, Ck, Class};
use super::on::{Fwd, Watched};

impl Watched for Class {
    fn parent(&self) -> usize {
        self.parent
    }

    /// A field whose type has no `Debug` is shown by its length.
    fn scalars(&self) -> Vec<(&'static str, String)> {
        let c = self;
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
}

/// An admitted call whose needs are being checked.
pub(in crate::check) struct Rec {
    call: String,
    lo: usize,
    seq: usize,
    same_use: usize,
    errors: usize,
}

fn key_hash(key: &(NeedKind, bool)) -> u64 {
    zed_kernel::digest::fixed_hash(key)
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
        NeedKind::Level { .. } => "Level",
        NeedKind::Strings { .. } => "Strings",
        NeedKind::Concat { .. } => "Concat",
        NeedKind::Zip { .. } => "Zip",
        NeedKind::Fwd(_) => "Fwd",
    }
}

impl<'t, 'a> Ck<'t, 'a> {
    fn probe_count(&self, why: &str) {
        *self
            .classes
            .probe
            .borrow_mut()
            .admit
            .entry(why.into())
            .or_default() += 1;
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
    pub(in crate::check) fn probe_recorded(
        &mut self,
        rec: Rec,
        args: &[Option<Arg<'a>>],
        result: &Ty,
    ) {
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
            let now = self.classes.v[*k].scalars();
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
            alike: std::sync::Arc::from([]),
            via: zedc_types::ty::CallPath::default(),
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
            self.classes.probe.get_mut().fwds[f].end = Some(if stays { "kept" } else { "escaped" });
        }
    }
}
