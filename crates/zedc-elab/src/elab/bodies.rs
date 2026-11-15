//! The bodies made for the calls of a generic function whose calls decide the identities of
//! its folds, and the refusal of every fold no body could take (REDUCE-generic-identity;
//! [`instances`](super::instances) explains the whole). Run once the unit's statements are
//! elaborated.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::mem;
use std::sync::Arc;

use zed_kernel::Shared;
use zedc_base::rejection::not_yet;
use zedc_stage::defs::{Def, Test};
use zedc_stage::stage::free;
use zedc_syntax::ast::{Error, Note, StmtKind};
use zedc_syntax::lex::Span;

use super::instances::Dropped;
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

    /// The refusal of each function declared in a block whose written body was dropped
    /// ([`Self::place_locals`]) while a kept definition or test row names it, which would
    /// leave the name unbound when the program runs (PROOF-block-body-kept-when-named).
    /// `place_locals` keeps every written body that `Instancing::written_named` saw named, so
    /// this refuses only a reference that bypassed it. A name free in a kept term is such a
    /// reference: kernel names are unique in the unit, each binder's from `Elab::new` (the
    /// bare name or `name@k`, which no identifier spells) and each fresh one `name@N` with
    /// `N` above every `k` (`Instancing::next`), and `stage::free` leaves out every name bound
    /// inside the term, so a dropped binding's name is free in a kept term exactly where that
    /// term names it.
    // Complexity tradeoff: one `stage::free` per definition and test row, O(t log t) for terms
    // of size t in all, and none when no body was dropped. The naive form, a search of every
    // term for each dropped name, costs O(dropped × t).
    pub(super) fn check_dropped(&mut self, defs: &[Def], tests: &[Test]) {
        if self.inst.dropped.is_empty() {
            return;
        }
        let terms = (defs.iter().map(|d| &*d.term)).chain(tests.iter().map(|t| &t.check));
        let mut named: BTreeMap<Span, &Dropped<'a>> = BTreeMap::new();
        for t in terms {
            for x in free(t) {
                if let Some(d) = self.inst.dropped.get(&x) {
                    named.insert(d.stmt.span, d);
                }
            }
        }
        let mut errors: Vec<Error> = named.into_values().map(|d| self.dropped_named(d)).collect();
        self.errors.append(&mut errors);
    }

    /// The refusal of the block's function `d` named where no call gives its folds one type.
    fn dropped_named(&self, d: &Dropped<'a>) -> Error {
        let StmtKind::Function(f) = &d.stmt.kind else {
            unreachable!("a block's dropped body is a function's")
        };
        let h = &f.name;
        let args: Vec<String> = (f.params.iter())
            .filter(|p| p.positional || p.default.is_none())
            .map(|p| match p.positional {
                true => p.name.clone(),
                false => format!("{0}: {0}", p.name),
            })
            .collect();
        let call = format!("{h}({})", args.join(", "));
        let mut notes: Vec<Note> = (d.sites.iter())
            .map(|&s| Note {
                span: s,
                text: format!("`{h}` runs this fold: {}", self.info.split_folds[&s]),
            })
            .collect();
        notes.push(Note {
            span: d.stmt.span,
            text: format!(
                "repair: call `{h}` where it is used, as `{call}`, or write `{h}` once for each \
                 of these types"
            ),
        });
        Error {
            menu: String::new(),
            row: None,
            span: d.stmt.span,
            message: not_yet(&format!(
                "`{h}` used as a value while its calls run a fold at more than one type,"
            )),
            notes,
        }
    }
}

#[cfg(test)]
mod tests {
    use zedc_syntax::ast::unit;
    use zedc_syntax::lex::lex_fence;
    use zedc_syntax::parse::{TOP, parse};

    use super::super::instances::MISS_WRITTEN_NAMED;

    /// `top`, a fold by `max` whose identity its calls decide; `mi["a"]` an empty `int` level and
    /// `m["a"]` an empty `f64` level.
    const AT: &str = "top(positional xs) = xs >< max;\n\
        m = { \"a\" -> [1.0] }.map(r -> r.where(v -> v > 3.0));\n\
        mi = { \"a\" -> [1] }.map(r -> r.where(v -> v > 3));\n";

    /// The errors of elaborating `body` after [`AT`], with [`MISS_WRITTEN_NAMED`] set to `miss`,
    /// each as its message followed by its notes' texts.
    fn errors(body: &str, miss: bool) -> Vec<String> {
        let text = format!("{AT}{body}");
        let tokens = lex_fence(&text).unwrap();
        let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
        let stmts = unit(&text, &tokens, &tree).unwrap();
        let res = zedc_resolve::resolve::resolve(&stmts).unwrap();
        MISS_WRITTEN_NAMED.set(miss);
        let out = crate::elab::elaborate_text(&stmts, &res, Some(&text), None);
        MISS_WRITTEN_NAMED.set(false);
        let es = out.err().unwrap_or_default();
        (es.iter())
            .map(|e| {
                let notes: Vec<&str> = e.notes.iter().map(|n| &*n.text).collect();
                format!("{} | {}", e.message, notes.join(" | "))
            })
            .collect()
    }

    /// The words the checker gives the fold of `top` run at `int` and at `f64`.
    const FOLD: &str = "a fold `><` that the calls of one function run on entries of type `int` \
                        and `f64`, where an empty level folds to `#empty` at `int` and `-inf` at \
                        `f64`";

    #[test]
    fn a_kept_term_that_names_a_dropped_written_body_is_refused() {
        // `p = h` names `h`'s written body, whose fold no call decides, so it is kept and its
        // fold refused. Were that reference missed, the body would be dropped while `p` names
        // it, and `check_dropped` refuses the program, naming `h`, rather than leave `p`
        // unbound.
        let body = "a = { h(positional q) = top(q); p = h; (h(mi[\"a\"]), p(m[\"a\"])) };\n";
        let seen = errors(body, false);
        assert_eq!(seen.len(), 1, "{seen:?}");
        assert!(seen[0].starts_with(FOLD), "{seen:?}");
        // The call `p(m["a"])`, which no body took, is refused at the fold as before.
        let dropped = |missed: &[String]| -> String {
            let named: Vec<&String> = (missed.iter())
                .filter(|e| e.starts_with("`h` used as a value"))
                .collect();
            assert_eq!(named.len(), 1, "{missed:?}");
            named[0].clone()
        };
        let e = dropped(&errors(body, true));
        assert!(
            e.starts_with(
                "`h` used as a value while its calls run a fold at more than one type, is part \
                 of the Zed language"
            ),
            "{e}"
        );
        assert!(e.contains(&format!("`h` runs this fold: {FOLD}")), "{e}");
        assert!(
            e.contains("repair: call `h` where it is used, as `h(q)`, or write `h` once"),
            "{e}"
        );
        // The repair's call passes each parameter with no default, a named one by name.
        let body = "a = { h(positional q, by: int, d = 0) = (top(q), by, d); p = h; \
                    (h(mi[\"a\"], by: 1), p(m[\"a\"], by: 2)) };\n";
        let e = dropped(&errors(body, true));
        assert!(e.contains("as `h(q, by: by)`"), "{e}");
    }

    #[test]
    fn a_dropped_written_body_no_term_names_is_not_refused() {
        // `h` called by name at each type: each call runs a body made at its identity, the
        // written body is dropped, and nothing names it, with the reference search on or off.
        let body = "a = { h(positional q) = top(q); (h(mi[\"a\"]), h(m[\"a\"])) };\n";
        assert_eq!(errors(body, false), Vec::<String>::new());
        assert_eq!(errors(body, true), Vec::<String>::new());
    }
}
