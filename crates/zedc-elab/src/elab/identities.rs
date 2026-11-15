//! The fold identities in force while a body is elaborated, and the kernel name of each call
//! of a function whose calls decide the identities of its folds (REDUCE-generic-identity;
//! [`instances`](super::instances) explains the whole). The walk over expressions
//! ([`walk`](super::walk)) calls these at each expression, fold and call.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::mem;
use std::sync::Arc;

use zed_kernel::{Shared, Term, Value};
use zedc_syntax::ast::{Expr, ExprKind};
use zedc_syntax::lex::Span;

use super::instances::Env;
use super::state::Elab;

/// What [`Elab::enter_expr`] changed, for [`Elab::leave_expr`] to put back.
pub(super) enum Saved {
    /// The entries a built-in call put in `env`: each fold with its earlier entry and
    /// provider, or none.
    Pushed(Vec<(Span, Option<Option<Value>>, Option<Span>)>),
    /// The identities and providers in force around a body that takes none from there.
    Cleared(Env, HashMap<Span, Span>),
}

/// The built-in methods that apply a lambda passed to them only while the call runs (DESIGN.md
/// sec:tour_collections, sec:grouping, sec:reduction): a check of such a lambda's folds is a
/// check of the call's needs, made at the call's frame. The lambda itself is not kept in the
/// result; what its body builds that outlives the call, as `r -> (y -> top(y))` builds
/// `y -> top(y)`, is a lambda or a function of its own, whose body takes no identity from here
/// (`clear_env`).
pub(super) const IN_PLACE: [&str; 8] = [
    "map", "where", "foldl", "foldr", "flatMap", "group", "rekey", "reduce",
];

impl<'a> Elab<'a> {
    /// The identity of the fold at `site`: the one the checker found, or for a fold whose
    /// calls decide it ([`zedc_check::check::Info::split_folds`]) the one of the body being
    /// made; none where that folds an empty level to `#empty`. A fold no call decided here is
    /// recorded ([`Instancing::undecided`](super::instances::Instancing::undecided)) and
    /// elaborated with none, for a body no call reaches, or for [`Self::check_instances`] to
    /// refuse.
    pub(super) fn fold_identity(&mut self, site: Span) -> Option<Value> {
        if !self.info.split_folds.contains_key(&site) {
            return self.info.reduce.get(&site).cloned();
        }
        self.env_identity(site).flatten()
    }

    /// The identity `env` holds for the fold at `site`, taking the entry of the built-in call
    /// that put it there; none recorded as undecided.
    fn env_identity(&mut self, site: Span) -> Option<Option<Value>> {
        let Some(v) = self.inst.env.get(&site) else {
            self.inst.undecided.push(site);
            return None;
        };
        if let Some(&call) = self.inst.provider.get(&site) {
            self.inst.consumed.insert((call, site));
        }
        Some(v.clone())
    }

    /// Enters the expression `e` where folds the checker decided at calls exist
    /// ([`zedc_check::check::Info::split_folds`]). Returns what it changed, for
    /// [`Self::leave_expr`].
    ///
    /// A call of a built-in of [`IN_PLACE`] puts the identities the checker decided at it
    /// ([`zedc_check::check::Info::fold_calls`]) in `env` for the code within it, as the
    /// lambda of `m.map(r -> top(r))` is checked at the call of `map`; its lambdas take them.
    /// Any other lambda's body, and the written body of any function declared in a block,
    /// takes none and lets no built-in put any: the checker checks it where it is called, as
    /// `f(m["a"])` for `f = x -> top(x)`, which is not where it is written. A fold met there
    /// with no call of its function deciding it is refused when the unit reaches it; a block's
    /// function takes bodies made at its calls' identities instead ([`Self::fkernel`]).
    ///
    /// Why a fold's read inside a built-in's lambda takes the identity its check found: the
    /// read's need is met at its own call (whose entry [`Self::fkernel`] takes before `env`),
    /// or passes to the lambda's signature and from there is met at the built-in's call or
    /// passes on outward, through built-in calls only, since every other body cuts `env`
    /// off, to the body being elaborated, whose entries came from its own call. Each of
    /// those calls that met a need on the fold put its one result in `env` around the read,
    /// and a call whose result differs from the entry in force is refused, not put there
    /// (the fold is recorded as undecided), so every entry in force around the read is the one
    /// result, the meeting call's among them.
    // Complexity tradeoff: one hash lookup per expression, and per built-in call O(k) to put
    // and later restore the k identities the checker decided at it, so O(e + Σk) for a body
    // of e expressions; a lambda's body takes the maps out and puts them back whole, O(1).
    // The naive form, a scope chain searched outward at each fold, costs O(depth) per fold.
    pub(super) fn enter_expr(&mut self, e: &Expr) -> Option<Saved> {
        match &e.kind {
            ExprKind::Lambda { .. } if self.inst.in_place.remove(&e.span) => None,
            ExprKind::Lambda { .. } => Some(self.clear_env()),
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } if matches!(&callee.kind, ExprKind::Member { name, .. } if IN_PLACE.contains(&&**name)) =>
            {
                let args = positional.iter().chain(named.iter().map(|(_, a)| a));
                for a in args {
                    if matches!(a.kind, ExprKind::Lambda { .. }) {
                        self.inst.in_place.insert(a.span);
                    }
                }
                if self.inst.opaque > 0 {
                    return None;
                }
                let given = self.info.fold_calls.get(&e.span)?;
                let mut saved = Vec::with_capacity(given.len());
                for (s, v) in given {
                    // A different identity in force is refused where the body is reached:
                    // the fold is undecided here. It is recorded in each body, since the
                    // written body of a function, in which nothing is in force, may have
                    // consumed the call's entry already.
                    if self.inst.env.get(s).is_some_and(|old| old != v) {
                        self.inst.undecided.push(*s);
                        continue;
                    }
                    let old = self.inst.env.insert(*s, v.clone());
                    let from = self.inst.provider.insert(*s, e.span);
                    saved.push((*s, old, from));
                }
                Some(Saved::Pushed(saved))
            }
            _ => None,
        }
    }

    /// Empties `env` for a body that takes no identity from around it.
    pub(super) fn clear_env(&mut self) -> Saved {
        self.inst.opaque += 1;
        Saved::Cleared(
            mem::take(&mut self.inst.env),
            mem::take(&mut self.inst.provider),
        )
    }

    /// Puts back what [`Self::enter_expr`] or [`Self::clear_env`] changed.
    pub(super) fn leave_expr(&mut self, saved: Saved) {
        match saved {
            Saved::Pushed(entries) => {
                for (s, old, from) in entries {
                    match old {
                        Some(v) => self.inst.env.insert(s, v),
                        None => self.inst.env.remove(&s),
                    };
                    match from {
                        Some(c) => self.inst.provider.insert(s, c),
                        None => self.inst.provider.remove(&s),
                    };
                }
            }
            Saved::Cleared(env, provider) => {
                self.inst.opaque -= 1;
                self.inst.env = env;
                self.inst.provider = provider;
            }
        }
    }

    /// The term of the declared function `id` called at `at`: its own kernel name, or for a
    /// function whose calls decide folds ([`zedc_check::check::Info::split_needs`]), declared
    /// at the top level or in a block being elaborated, the body made at the identities the
    /// call decides, each the checker's for this call or else the one the body being made
    /// holds. A call where any is decided by neither takes the written body and records the
    /// folds as undecided; for a block's function it records that the written body is named
    /// ([`Instancing::written_named`](super::instances::Instancing::written_named)).
    // Complexity tradeoff: the identities of a call's folds are found by binary search in the
    // checker's sorted list, O(k log k) for a callee of k decided folds, against O(k²) for a
    // search of the list for each fold. A body is made once for each distinct list of
    // identities, found in a hash map, O(k) to hash the list.
    pub(super) fn fref(&mut self, id: usize, at: Span) -> Shared {
        Shared::new(Term::Var(self.fkernel(id, at)))
    }

    /// The kernel name [`Self::fref`] calls.
    pub(super) fn fkernel(&mut self, id: usize, at: Span) -> Arc<str> {
        let info = self.info;
        let Some(sites) = info.split_needs.get(&id) else {
            return self.names[id].clone();
        };
        let local = self.inst.local_at.get(&id).copied();
        if local.is_none() && !self.inst.fns.contains_key(&id) {
            return self.names[id].clone();
        }
        let given = info.fold_calls.get(&at).map_or(&[][..], Vec::as_slice);
        let mut key = Vec::with_capacity(sites.len());
        let mut open = false;
        for s in sites {
            match given.binary_search_by_key(s, |(x, _)| *x) {
                Ok(i) => {
                    self.inst.consumed.insert((at, *s));
                    key.push(given[i].1.clone());
                }
                Err(_) => match self.env_identity(*s) {
                    Some(v) => key.push(v),
                    None => open = true,
                },
            }
        }
        if open {
            self.inst.written_named(id);
            return self.names[id].clone();
        }
        let env: Env = sites.iter().copied().zip(key.iter().cloned()).collect();
        if let Some(i) = local {
            let name = &self.t.res.binders[id].name;
            let l = &mut self.inst.locals[i];
            return match l.made.entry(key) {
                Entry::Occupied(e) => e.get().clone(),
                Entry::Vacant(e) => {
                    let kernel: Arc<str> = format!("{name}@{}", self.inst.next).into();
                    self.inst.next += 1;
                    e.insert(kernel.clone());
                    if l.queue.is_empty() {
                        self.inst.pending.push(i);
                    }
                    l.queue.push((kernel.clone(), env));
                    kernel
                }
            };
        }
        match self.inst.made.entry((id, key)) {
            Entry::Occupied(e) => e.get().clone(),
            Entry::Vacant(e) => {
                let name = &self.t.res.binders[id].name;
                let kernel: Arc<str> = format!("{name}@{}", self.inst.next).into();
                self.inst.next += 1;
                e.insert(kernel.clone());
                self.inst.queue.push((id, kernel.clone(), env));
                kernel
            }
        }
    }
}
