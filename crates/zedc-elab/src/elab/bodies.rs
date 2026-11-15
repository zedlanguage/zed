//! The bodies made for the calls of a generic function whose calls decide the identities of
//! its folds, and the refusal of every fold no body could take (REDUCE-generic-identity;
//! [`instances`](super::instances) explains the whole). Run once the unit's statements are
//! elaborated.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::mem;
use std::sync::Arc;

use zed_kernel::Shared;
use zedc_base::rejection::not_yet;
use zedc_stage::defs::{Def, Test};
use zedc_stage::stage::free;
use zedc_syntax::ast::{Error, Note, StmtKind};
use zedc_syntax::lex::Span;

use super::state::Elab;

/// The refusal of the fold at `site`, whose words the checker wrote (`Info::split_folds`).
fn refusal(site: Span, what: &str) -> Error {
    Error {
        menu: String::new(),
        row: None,
        span: site,
        message: not_yet(what),
        notes: vec![Note {
            span: site,
            text: "repair: write the function once for each of these types".to_string(),
        }],
    }
}

impl<'a> Elab<'a> {
    /// Makes each body [`Self::fref`] queued for a top-level function, and the bodies their
    /// calls queue in turn.
    pub(super) fn make_instances(&mut self) {
        while let Some((id, kernel, env)) = self.inst.queue.pop() {
            let s = self.inst.fns[&id];
            let StmtKind::Function(f) = &s.kind else {
                unreachable!("`fns` holds function declarations")
            };
            let (term, sites) = self.instance_body(id, s, env);
            self.inst.attribute([&kernel], sites);
            if let Some(term) = term {
                let first_order = self.info.tops.get(&f.name).is_some_and(|t| t.first_order());
                self.inst.bodies.push((
                    id,
                    Def {
                        name: kernel.to_string(),
                        kernel,
                        term: Shared::new(term),
                        first_order,
                    },
                ));
            }
        }
    }

    /// The refusals of the folds no body could take: each fold of a call the checker decided
    /// that no call's elaboration took ([`Self::fkernel`]), the folds `export` left undecided
    /// in the unit's export, which the unit always runs, and each fold left undecided in a
    /// definition the unit reaches, from every definition other than the written bodies of
    /// functions whose calls decide folds and the bodies made for them, and from every test
    /// row. A written body no call reaches is not run, so its folds need no identity.
    // Complexity tradeoff: one search of the definitions the unit reaches, each met once (a
    // visited set), O(t log t) for terms of size t in all with `stage::free`; it runs only when
    // a fold was left undecided. The naive form, a search from each root, costs O(roots × t).
    pub(super) fn check_instances(&mut self, defs: &[Def], tests: &[Test], export: Vec<Span>) {
        let info = self.info;
        let mut sites: BTreeSet<Span> = export.into_iter().collect();
        for (&call, folds) in &info.fold_calls {
            for &(s, _) in folds {
                if !self.inst.consumed.contains(&(call, s)) {
                    sites.insert(s);
                }
            }
        }
        if !self.inst.undecided_defs.is_empty() {
            let at: HashMap<&str, usize> = (defs.iter().enumerate())
                .map(|(i, d)| (&*d.kernel, i))
                .collect();
            let made: HashSet<&str> = self.inst.made.values().map(|k| &**k).collect();
            let written: HashSet<&str> = (info.split_needs.keys())
                .filter(|id| self.inst.fns.contains_key(id))
                .map(|&id| &*self.names[id])
                .collect();
            let mut seen = vec![false; defs.len()];
            let mut todo: Vec<usize> = Vec::new();
            for (i, d) in defs.iter().enumerate() {
                if !made.contains(&*d.kernel) && !written.contains(&*d.kernel) {
                    seen[i] = true;
                    todo.push(i);
                }
            }
            let mut reach = |names: BTreeSet<Arc<str>>, todo: &mut Vec<usize>| {
                for x in names {
                    if let Some(&i) = at.get(&*x)
                        && !mem::replace(&mut seen[i], true)
                    {
                        todo.push(i);
                    }
                }
            };
            for t in tests {
                reach(free(&t.check), &mut todo);
            }
            while let Some(i) = todo.pop() {
                if let Some(s) = self.inst.undecided_defs.get(&defs[i].kernel) {
                    sites.extend(s);
                }
                reach(free(&defs[i].term), &mut todo);
            }
        }
        for site in sites {
            let what = &info.split_folds[&site];
            self.errors.push(refusal(site, what));
        }
    }
}
