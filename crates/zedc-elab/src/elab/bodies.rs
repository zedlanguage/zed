//! The bodies made for the calls of a generic function whose calls decide the identities of
//! its folds, and the refusal of every fold no body could take (REDUCE-generic-identity;
//! [`instances`](super::instances) explains the whole). Run once the unit's statements are
//! elaborated.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::mem;
use std::sync::Arc;

use zed_kernel::{Shared, Term};
use zedc_base::rejection::not_yet;
use zedc_stage::defs::{Def, Test};
use zedc_stage::stage::free;
use zedc_syntax::ast::{Error, Note, StmtKind};
use zedc_syntax::lex::Span;

use super::state::Elab;

/// `t`, a default's term at a call ([`Elab::defaults`]), with each name of `map` renamed: a
/// literal, a marked literal, a parameter's name, or a call of the default's own definition on
/// parameters' names, the shapes `Frame::FnDefault` makes.
fn renamed(t: &Term, map: &HashMap<Arc<str>, Arc<str>>) -> Term {
    let name = |x: &Arc<str>| map.get(x).unwrap_or(x).clone();
    match t {
        Term::Var(x) => Term::Var(name(x)),
        Term::App(f, args) => Term::App(
            f.clone(),
            (args.iter())
                .map(|a| match a {
                    Term::Var(x) => Term::Var(name(x)),
                    a => a.clone(),
                })
                .collect(),
        ),
        t => t.clone(),
    }
}

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

impl Elab<'_> {
    /// Makes each body [`Self::fref`] queued, and the bodies their calls queue in turn.
    /// Each binder of the function's statement other than the function's own is given a fresh
    /// kernel name while its body is elaborated, as kernel names are unique in the unit (stage
    /// `mix` and a default's `let` rely on it), then given back.
    // Complexity tradeoff: each body costs one elaboration of the function, O(s) for a
    // function of size s, and one search of the binders by start, O(log b); the bodies are
    // as many as the distinct lists of identities the calls decide, at most the calls. The
    // naive form, one copy of the elaborated body with its names renamed by a walk of the
    // term, would cost the same O(s) but must know every form of the kernel that binds a name.
    pub(super) fn make_instances(&mut self) {
        while let Some((id, kernel, env)) = self.inst.queue.pop() {
            let s = self.inst.fns[&id];
            let StmtKind::Function(f) = &s.kind else {
                unreachable!("`fns` holds function declarations")
            };
            if self.inst.by_start.is_empty() {
                let mut by_start: Vec<_> = (self.t.res.binders.iter().enumerate())
                    .map(|(i, b)| (b.span.start, b.span.end, i))
                    .collect();
                by_start.sort_unstable();
                self.inst.by_start = by_start;
            }
            let lo = (self.inst.by_start).partition_point(|&(start, ..)| start < s.span.start);
            let mut map: HashMap<Arc<str>, Arc<str>> = HashMap::new();
            let mut given_back = Vec::new();
            for k in lo..self.inst.by_start.len() {
                let (start, end, b) = self.inst.by_start[k];
                if start >= s.span.end {
                    break;
                }
                if end > s.span.end || b == id {
                    continue;
                }
                let fresh: Arc<str> =
                    format!("{}@{}", self.t.res.binders[b].name, self.inst.next).into();
                self.inst.next += 1;
                let old = mem::replace(&mut self.names[b], fresh.clone());
                map.insert(old.clone(), fresh);
                given_back.push((b, old));
            }
            let defaults: Vec<(usize, Term)> = (0..f.params.len())
                .filter_map(|j| Some((j, self.defaults.get(&(id, j))?.clone())))
                .collect();
            for (j, t) in &defaults {
                self.defaults.insert((id, *j), renamed(t, &map));
            }
            let reads = mem::take(&mut self.reads);
            // The body's identities came from its call, which took them ([`Self::fkernel`]):
            // no built-in call around the body provides them.
            let outer = mem::replace(&mut self.inst.env, env);
            let providers = mem::take(&mut self.inst.provider);
            let opaque = mem::replace(&mut self.inst.opaque, 0);
            let mark = self.inst.undecided.len();
            let body = self.body_term(f);
            let params: Vec<Arc<str>> = (f.params.iter())
                .map(|p| self.names[self.id(p.span, &p.name)].clone())
                .collect();
            let sites = self.inst.undecided.split_off(mark);
            self.inst.attribute([&kernel], sites);
            self.inst.env = outer;
            self.inst.provider = providers;
            self.inst.opaque = opaque;
            self.reads = reads;
            for (j, t) in defaults {
                self.defaults.insert((id, j), t);
            }
            for (b, old) in given_back {
                self.names[b] = old;
            }
            if let Some(body) = body {
                let first_order = self.info.tops.get(&f.name).is_some_and(|t| t.first_order());
                self.inst.bodies.push((
                    id,
                    Def {
                        name: kernel.to_string(),
                        kernel,
                        term: Shared::new(Term::Lam(params, Shared::new(body))),
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
