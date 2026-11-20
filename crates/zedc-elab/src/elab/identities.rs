//! The fold identities in force while a body is elaborated, and the kernel name of each call
//! of a function whose calls decide the identities of its folds (REDUCE-generic-identity;
//! [`instances`](super::instances) explains the whole). The walk over expressions
//! ([`walk`](super::walk)) calls these at each expression, fold and call.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::mem;
use std::sync::Arc;

use zed_kernel::{Shared, Term, Value};
use zedc_resolve::resolve::Ref;
use zedc_syntax::ast::{Expr, ExprKind};
use zedc_syntax::lex::Span;

use super::instances::{Env, InForce};
use super::state::Elab;

/// What [`Elab::enter_expr`] changed, for [`Elab::leave_expr`] to put back.
pub(super) enum Saved {
    /// The call that put its identities in `pushed`, one entry on top of each of its folds'.
    Pushed(Span),
    /// The identities in force around a body that takes none from there: the body's own and
    /// those its calls put in force.
    Cleared(Env, Pushed),
}

/// The identities calls put in force, by fold
/// ([`Instancing::pushed`](super::instances::Instancing::pushed)).
pub(super) type Pushed = HashMap<Span, InForce>;

/// The one identity of `xs`, if there is one and they all agree.
fn agree<'v>(mut xs: impl Iterator<Item = &'v Option<Value>>) -> Option<Option<Value>> {
    let v = xs.next()?;
    xs.all(|x| x == v).then(|| v.clone())
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
        self.env_identity(site, site).flatten()
    }

    /// The identity in force for the fold at `site` at its use `read` (the fold itself, or a
    /// call of a function that runs it): that of each call around the use that checked the
    /// fold through it ([`zedc_check::check::Info::fold_reads`]), when they agree; else the
    /// one of the body being made. The calls whose entry it takes are recorded as taken. None
    /// is recorded as undecided.
    ///
    /// Why the first is the identity the use runs at: a call records the uses its check of
    /// the fold passed through, so a use under several calls that decide the fold, as `top(q)`
    /// under the `.map` at `int` and the one at `f64` in
    /// `mi.map(q -> m.map(r -> (top(r), top(q))))`, takes the identity of the call that
    /// checked it, the outer one. A use no call around it checked has its need met at the
    /// call of the body being made, whose identities that body holds (the second). A use
    /// under calls none of which checked it, and outside any body made at identities, is left
    /// undecided rather than given the identity of the calls around it: no check found it at
    /// theirs, so `check_instances` refuses the program instead of running a guess.
    // Complexity tradeoff: O(c) expected for the c calls holding the use that checked it,
    // each one hash lookup among those in force ([`InForce`]), and each call in force taken
    // once over all its uses. The naive form, a search of the d calls in force deciding the
    // fold for those that checked the use, costs O(d) per use, O(d²) over a nest of d `.map`
    // calls; keeping only the innermost entry costs O(1) but cannot tell which call checked
    // the use, so a read under two calls was refused.
    fn env_identity(&mut self, site: Span, read: Span) -> Option<Option<Value>> {
        let checked: Vec<&Option<Value>> = match self.inst.pushed.get(&site) {
            Some(around) => (self
                .inst
                .checked_by
                .get(&(site, read))
                .into_iter()
                .flatten())
            .filter_map(|c| around.get(c))
            .collect(),
            None => Vec::new(),
        };
        let v = match checked.is_empty() {
            false => agree(checked.into_iter()),
            true => self.inst.env.get(&site).cloned(),
        };
        let Some(v) = v else {
            self.inst.undecided.push(site);
            return None;
        };
        // The calls around that decided the same identity are taken with it.
        if let Some(around) = self.inst.pushed.get_mut(&site) {
            for c in around.take(&v) {
                self.inst.consumed.insert((c, site));
            }
        }
        Some(v)
    }

    /// The function `e` names, if it is a name of one that takes a body for each list of
    /// identities its calls decide, directly or through names bound to it: a top-level
    /// function or one declared in a block whose calls decide folds, or a lambda bound to a
    /// name in a block whose written body left folds undecided
    /// ([`Local`](super::instances::Local)).
    pub(super) fn instanced(&self, e: &Expr) -> Option<usize> {
        let (ExprKind::Name(_), Some(Ref::Bound(ids))) = (&e.kind, self.t.res.uses.get(&e.span))
        else {
            return None;
        };
        if ids.len() != 1 {
            return None;
        }
        let id = self.target(ids[0]);
        let split = self.info.split_needs.contains_key(&id);
        match self.inst.local_at.get(&id) {
            Some(&i) => (split || self.inst.locals[i].key.is_some()).then_some(id),
            None => (split && self.inst.fns.contains_key(&id)).then_some(id),
        }
    }

    /// Enters the expression `e` where folds the checker decided at calls exist
    /// ([`zedc_check::check::Info::split_folds`]). Returns what it changed, for
    /// [`Self::leave_expr`].
    ///
    /// A call that decides folds ([`zedc_check::check::Info::fold_calls`]) puts its
    /// identities in force (`pushed`) for the code within it, as the lambda of
    /// `m.map(r -> top(r))` is checked at the call of `map`; the lambdas passed to it take
    /// them. A built-in of [`IN_PLACE`] runs its lambdas only while it runs; any other call
    /// does so unless its result holds a function with needs or leaves parameters open
    /// (`Info::escaping_calls`), and then puts nothing in force. A name of a function that
    /// takes a body per list of identities passed to such a call stands for the body made at
    /// the call's identities ([`Self::value_kernel`]), as `top` in `ap(top, m["a"])`.
    /// Any other lambda's body, and the written body of any function declared in a block,
    /// takes none and lets no call put any: the checker checks it where it is called, as
    /// `f(m["a"])` for `f = x -> top(x)`, which is not where it is written. A fold met there
    /// with no call of its function deciding it is refused when the unit reaches it; a block's
    /// function, and a lambda bound to a name in a block, takes bodies made at its calls'
    /// identities instead ([`Self::fkernel`]).
    ///
    /// Why a fold's use inside a lambda passed to such a call takes the identity its check
    /// found: the use's need is met at its own call (whose entry [`Self::fkernel`] takes
    /// before any in force), or passes to the lambda's signature and from there is met at the
    /// call the lambda is passed to, which records the use ([`Self::env_identity`] takes that
    /// call's entry), or passes on outward, through such calls only, since every other body
    /// cuts `pushed` off, to the body being made, whose identities came from its own call.
    /// A call whose entry no use took is refused ([`Self::check_instances`]).
    // Complexity tradeoff: one hash lookup per expression, and per call that decides folds
    // O(k) to push and later pop the k identities the checker decided at it, so O(e + Σk) for
    // a body of e expressions; a lambda's body takes the maps out and puts them back whole,
    // O(1). The naive form, a scope chain searched outward at each fold, costs O(depth) per
    // fold.
    pub(super) fn enter_expr(&mut self, e: &Expr) -> Option<Saved> {
        let ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } = &e.kind
        else {
            return match &e.kind {
                ExprKind::Lambda { .. } if self.inst.in_place.remove(&e.span) => None,
                ExprKind::Lambda { .. } => Some(self.clear_env()),
                _ => None,
            };
        };
        let args = || positional.iter().chain(named.iter().map(|(_, a)| a));
        let built_in =
            matches!(&callee.kind, ExprKind::Member { name, .. } if IN_PLACE.contains(&&**name));
        if built_in {
            for a in args() {
                if matches!(a.kind, ExprKind::Lambda { .. }) {
                    self.inst.in_place.insert(a.span);
                }
            }
        }
        if self.inst.opaque > 0 {
            return None;
        }
        let info = self.info;
        let given = info.fold_calls.get(&e.span)?;
        // A function passed to a call that decides its folds runs within the call, at the
        // types the call fixes, unless the call's result holds it or leaves parameters open
        // (`Info::escaping_calls`): then it may run later at other identities, as `p[1]` of
        // `p = h3(x -> top(x), m["a"])` for `h3(f, y) = (f(y), f)` runs at `int`.
        if !info.escaping_calls.contains(&e.span) {
            for a in args() {
                match &a.kind {
                    ExprKind::Lambda { .. } => {
                        self.inst.in_place.insert(a.span);
                    }
                    ExprKind::Name(_) if self.instanced(a).is_some() => {
                        self.inst.value_at.insert(a.span, e.span);
                    }
                    _ => {}
                }
            }
        } else if !built_in {
            return None;
        }
        for (s, v) in given {
            (self.inst.pushed.entry(*s).or_default()).enter(e.span, v.clone());
        }
        Some(Saved::Pushed(e.span))
    }

    /// Empties `env` and `pushed` for a body that takes no identity from around it.
    pub(super) fn clear_env(&mut self) -> Saved {
        self.inst.opaque += 1;
        Saved::Cleared(
            mem::take(&mut self.inst.env),
            mem::take(&mut self.inst.pushed),
        )
    }

    /// Puts back what [`Self::enter_expr`] or [`Self::clear_env`] changed.
    pub(super) fn leave_expr(&mut self, saved: Saved) {
        match saved {
            Saved::Pushed(call) => {
                for (s, _) in &self.info.fold_calls[&call] {
                    let Entry::Occupied(mut e) = self.inst.pushed.entry(*s) else {
                        unreachable!("a call's entries stay in force until it is left")
                    };
                    if e.get_mut().leave(call) {
                        e.remove();
                    }
                }
            }
            Saved::Cleared(env, pushed) => {
                self.inst.opaque -= 1;
                self.inst.env = env;
                self.inst.pushed = pushed;
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
        self.kernel_at(id, at, true)
    }

    /// The kernel name of the function `id` passed as a value to the call `at`, which decides
    /// its folds ([`Instancing::value_at`](super::instances::Instancing::value_at)): the body
    /// made at the call's identities, or the written body where the call does not decide them
    /// all. The identities of the body being made are not taken, since a value may outlive
    /// it: in `g(ys) = (top(ys), top)` the `top` that `g(mi["a"])` returns is called at any
    /// type.
    pub(super) fn value_kernel(&mut self, id: usize, at: Span) -> Arc<str> {
        self.kernel_at(id, at, false)
    }

    /// The kernel name of the function `id` at the call `at`: [`Self::fkernel`], with the
    /// identities the call does not decide taken from those in force when `from_env`.
    fn kernel_at(&mut self, id: usize, at: Span, from_env: bool) -> Arc<str> {
        let info = self.info;
        let local = self.inst.local_at.get(&id).copied();
        let own;
        let sites: &[Span] = match local.and_then(|i| self.inst.locals[i].key.clone()) {
            Some(key) => {
                own = key;
                &own
            }
            None => match info.split_needs.get(&id) {
                Some(sites) if local.is_some() || self.inst.fns.contains_key(&id) => sites,
                _ => {
                    self.inst.written_named(id);
                    return self.names[id].clone();
                }
            },
        };
        let given = info.fold_calls.get(&at).map_or(&[][..], Vec::as_slice);
        let mut key = Vec::with_capacity(sites.len());
        let mut open = false;
        for s in sites {
            match zed_collections::sorted::sorted_get(given, s) {
                Some(k) => {
                    self.inst.consumed.insert((at, *s));
                    key.push(k.clone());
                }
                None if !from_env => open = true,
                None => match self.env_identity(*s, at) {
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
