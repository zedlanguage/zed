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
use zedc_syntax::ast::{Error, ExprKind, Note, StmtKind, Target};
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
        // Why a function a call returns, run later at another identity, is refused here (row
        // REDUCE-identity-escaping-values: `p = h3(x -> top(x), m["a"]); p[1](mi["a"])` with
        // `h3(f, y) = (f(y), f)`). The checker accepts it: the check of the fold under `h3`'s
        // call finds `f64`, the one under `p[1](…)` finds `int`, one carrier at each call. A
        // call whose result may hold the function passed to it is in `Info::escaping_calls`,
        // and `enter_expr` puts none of its identities in force, so no body takes its entry
        // and the fold is refused below. It cannot be compiled with the closures the kernel
        // has: `p[1]` is the one closure the call ran, both runs apply it to an empty level,
        // and an empty family holds no carrier (`zed_kernel::value::Family` is its entries
        // and two ids), so both runs compute the one identity term on equal inputs, while
        // the language gives `-inf` at `f64` and `#empty` at `int`. Compiling it needs the
        // identity chosen at each application, a closure holding one body per list of
        // identities or the identity passed as an argument, which changes the value form of
        // the kernel, ZIR and the native back end (row REDUCE-identity-closure-bodies).
        // `escaping_calls` takes each call whose result's type reaches a function with needs
        // through tuples, payloads, families and returned functions, or holds a part that
        // does not say what it holds (`_`, a type variable, `(..)`), and each call that leaves
        // parameters open (`Ty::may_hold_needs` in zedc-types, which names the one
        // unproved gap: an atom whose payload is not listed). Taking too many calls only
        // refuses more: a call taken here gives no body.
        // Tests: tests/steps/l08_02_remaps/empty.rs
        // `a_function_a_call_returns_and_runs_at_another_carrier_is_not_compiled_yet` (h3 and
        // the forms that hold the function deeper, refused) and
        // `a_call_whose_result_holds_the_function_at_any_depth_is_one_it_may_run_after` (each
        // such call recorded). They check chosen shapes; the gap `Ty::may_hold_needs` names is
        // not checked by them.
        // Cost: one lookup per entry of each decided call, O(e) for e entries, as before.
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
        let (h, params) = match &d.stmt.kind {
            StmtKind::Function(f) => (&f.name, &f.params),
            StmtKind::Bind { targets, value } => match (&targets[..], &value.kind) {
                ([Target::Name(h, _)], ExprKind::Lambda { params, .. }) => (h, params),
                _ => unreachable!("a block's dropped binding binds a lambda to a name"),
            },
            _ => unreachable!("a block's dropped body is a function's or a lambda's"),
        };
        let args: Vec<String> = (params.iter())
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
