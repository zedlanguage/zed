//! Round 10 fixed-D admission, compact export, M62 bulk naming, M63 pending slots, and M56(c)
//! hooks on `Ck`. Submodule of `walk.rs` that imports only `super::super::*` (`check/mod.rs` and
//! `probe`), so there is no import cycle (`tests/steps/s_01f_import_graph`).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use zedc_syntax::lex::Span;
use zedc_types::ty::{
    Arrow, Binds, CallPath, EVERY, FwdFinishNaming, FwdVarStep, MapWord, NameRun, Names, Need,
    NeedKind, OTHER, Sig, SkipIndex, Ty, VarFacts, Vars, class_id, current_held_var_snapshot,
    fresh_name, fresh_variable_span_stats_indexed, r10_hash,
};

use super::super::probe::{
    CalleeSummary, ExposedTemplate, ForwardStatus, OpenForward, PendingLevel, StoreMode,
};
use super::super::{Arg, Ck, only_fn, site_free};

fn push_var_step(steps: &mut Vec<FwdVarStep>, step: FwdVarStep) {
    match (steps.last_mut(), step) {
        (Some(FwdVarStep::InternalRun(prev)), FwdVarStep::InternalRun(add)) => {
            *prev += add;
        }
        (_, FwdVarStep::InternalRun(0)) => {}
        (_, s) => steps.push(s),
    }
}

fn need_deep_vars(n: &Need, out: &mut Vars) {
    n.vars_in(out);
    for t in n.tys() {
        for v in t.var_facts().classes {
            Ty::var(v).vars_in(out);
        }
    }
}

/// `#27`: `map`'s operand `f` must be a variable or a function taking 1 argument (so `map_end`
/// makes no arity or non-function error on replay).
fn check_map_fn_27(f: &Ty) -> bool {
    if f.as_var().is_some() {
        return true;
    }
    let Some(fsig) = only_fn(f) else {
        return false;
    };
    let has = fsig.params.len();
    let req = fsig.params.iter().filter(|p| p.default.is_none()).count();
    has >= 1 && req <= 1
}

/// Small union-find over variable names for `CalleeSummary::var_ties` (`unfixed_args`).
#[derive(Default)]
struct TieUf {
    ids: HashMap<Arc<str>, usize>,
    names: Vec<Arc<str>>,
    parent: Vec<usize>,
}

impl TieUf {
    fn id(&mut self, v: &Arc<str>) -> usize {
        if let Some(&i) = self.ids.get(v) {
            return i;
        }
        let i = self.names.len();
        self.ids.insert(v.clone(), i);
        self.names.push(v.clone());
        self.parent.push(i);
        i
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            let p = self.parent[x];
            self.parent[x] = self.parent[p];
            x = self.parent[x];
        }
        x
    }

    fn union_group<'a>(&mut self, mut it: impl Iterator<Item = &'a Arc<str>>) {
        let Some(first) = it.next() else {
            return;
        };
        let a = self.id(first);
        for v in it {
            let b = self.id(v);
            let (ra, rb) = (self.find(a), self.find(b));
            if ra != rb {
                self.parent[rb] = ra;
            }
        }
    }

    fn project(&mut self, visible: &HashSet<Arc<str>>) -> Vec<Vec<Arc<str>>> {
        let mut groups: BTreeMap<usize, Vec<Arc<str>>> = BTreeMap::new();
        for i in 0..self.names.len() {
            let name = self.names[i].clone();
            if visible.contains(&name) {
                let r = self.find(i);
                groups.entry(r).or_default().push(name);
            }
        }
        groups.into_values().filter(|g| g.len() >= 2).collect()
    }
}

impl<'t, 'a> Ck<'t, 'a> {
    pub(in crate::check) fn r10_open_level(&mut self, level: usize) {
        if self.r10.cfg.enabled {
            self.r10.ensure_level(level);
        }
    }

    pub(in crate::check) fn r10_peek_pending(&self, level: usize) -> Option<Vec<usize>> {
        if !self.r10.cfg.enabled {
            return None;
        }
        Some(
            self.r10
                .pending_levels
                .get(level)
                .map(PendingLevel::flatten)
                .unwrap_or_default(),
        )
    }

    pub(in crate::check) fn r10_take_pending(&mut self, level: usize) -> Option<Vec<usize>> {
        if !self.r10.cfg.enabled {
            return None;
        }
        self.r10.ensure_level(level);
        let _ = std::mem::take(&mut self.pending[level]);
        Some(self.r10.pending_levels[level].flatten())
    }

    pub(in crate::check) fn r10_push_outer_pending(&mut self, at: usize, k: usize) {
        if self.r10.cfg.enabled {
            self.r10.ensure_level(at);
            self.r10.pending_levels[at].push_class_o1(k);
        }
    }

    /// Builds or retrieves an `O(1)`-composable `CalleeSummary` for `sig` without decoding any
    /// `NeedKind::Fwd` item (`O(|sig.needs|)` = `O(1)` per link on both chains).
    pub(in crate::check) fn r10_get_or_build_summary(&mut self, sig: &Sig) -> Arc<CalleeSummary> {
        let key = (sig as *const Sig as usize, sig.digest());
        if let Some(found) = self.r10.sig_summaries.get(&key) {
            return found.clone();
        }

        let mut intrinsic_fails: BTreeSet<&'static str> = BTreeSet::new();
        let mut arrow_param_vars = Vars::default();
        let mut arrow_all_vars = Vars::default();
        for a in &sig.arrows {
            for p in &a.params {
                p.vars_in(&mut arrow_param_vars);
                p.vars_in(&mut arrow_all_vars);
            }
            a.result.vars_in(&mut arrow_all_vars);
        }
        let param_var_set: HashSet<Arc<str>> = arrow_param_vars.order.iter().cloned().collect();
        let arrow_var_set: HashSet<Arc<str>> = arrow_all_vars.order.iter().cloned().collect();

        let mut total_needs = 0usize;
        let mut total_results = 0usize;
        let mut result_ranges: Vec<(usize, usize)> = Vec::new();
        let mut explicit_results: Vec<Arc<str>> = Vec::new();
        let mut seen_res_vars: HashSet<Arc<str>> = HashSet::new();
        let mut ok_5 = true;
        let mut ok_26 = true;

        let mut all_mentioned_vars = Vars::default();
        let mut on_mentioned_vars = Vars::default();
        let mut held_free = 0usize;
        let mut held_names: BTreeSet<Arc<str>> = BTreeSet::new();
        let mut held_outer: BTreeSet<Arc<str>> = BTreeSet::new();
        let mut held_foreign_fn = false;
        let mut held_classes: BTreeSet<Arc<str>> = BTreeSet::new();
        let mut tie_uf = TieUf::default();

        let mut child_summaries: Vec<Option<Arc<CalleeSummary>>> =
            Vec::with_capacity(sig.needs.len());
        for n in &sig.needs {
            if let NeedKind::Fwd(fwd) = &n.kind {
                child_summaries.push(Some(self.r10_get_or_build_summary(&fwd.callee)));
            } else {
                child_summaries.push(None);
            }
        }

        for (idx, n) in sig.needs.iter().enumerate() {
            match &n.kind {
                NeedKind::Fwd(fwd) => {
                    let cs = child_summaries[idx].as_ref().expect("child summary");
                    for &cf in &cs.intrinsic_fails {
                        intrinsic_fails.insert(cf);
                    }
                    // If `instantiated` replaced a `sigma` slot with a non-variable type,
                    // refuse admission so `replay` decodes with exact substitution (`M66`).
                    if fwd.sigma.iter().any(|(_, t)| t.as_var().is_none()) {
                        intrinsic_fails.insert("#6");
                    }
                    total_needs += fwd.need_count;
                    total_results += fwd.need_count;
                    if let Some(lo) = fwd.base_class {
                        result_ranges.push((lo, lo + fwd.need_count));
                        for (_, ety) in &fwd.exits {
                            if let Some(ev) = ety.as_var() {
                                if !sig.own.contains(ev)
                                    || param_var_set.contains(ev)
                                    || !seen_res_vars.insert(ev.clone())
                                {
                                    ok_5 = false;
                                }
                            } else {
                                ok_5 = false;
                            }
                        }
                    } else {
                        ok_26 = false;
                        if let Some(exp) = &fwd.explicit_result_vars {
                            explicit_results.extend(exp.iter().cloned());
                        }
                    }
                    for (_, t) in &fwd.sigma {
                        t.vars_in(&mut all_mentioned_vars);
                    }
                    for (_, t) in &fwd.exits {
                        t.vars_in(&mut all_mentioned_vars);
                    }
                    for t in &fwd.on_vars {
                        t.vars_in(&mut on_mentioned_vars);
                    }
                    for grp in &fwd.var_ties {
                        let mut gv = Vars::default();
                        for t in grp {
                            t.vars_in(&mut gv);
                        }
                        tie_uf.union_group(gv.order.iter());
                    }
                    held_free = held_free.max(fwd.held_free);
                    held_names.extend(fwd.held_names.iter().cloned());
                    held_outer.extend(fwd.held_outer.iter().cloned());
                    held_foreign_fn |= fwd.held_foreign_fn;
                    held_classes.extend(fwd.held_classes.iter().cloned());
                }
                _ => {
                    let kind_ok = matches!(
                        &n.kind,
                        NeedKind::Entries
                            | NeedKind::Call { curry: false, .. }
                            | NeedKind::Map {
                                word: MapWord::Map,
                                ..
                            }
                    );
                    if !kind_ok {
                        intrinsic_fails.insert("#3");
                    }
                    if n.on.as_var().is_none() {
                        intrinsic_fails.insert("#22");
                    }
                    // A function held in a need's types (`f(y -> (m, y))`) may own classes and
                    // hold the callee's parameters, which `finish` would leave unnamed in a
                    // kept forward (landing review of LAND-map-chain-neon, Neon B3); refuse.
                    if !matches!(n.kind, NeedKind::Map { .. })
                        && n.tys()
                            .any(|t| !t.fns.is_empty() || t.held_function().is_some())
                    {
                        intrinsic_fails.insert("#4");
                    }
                    if let NeedKind::Map { f, .. } = &n.kind
                        && !check_map_fn_27(f)
                    {
                        intrinsic_fails.insert("#27");
                    }
                    n.on.vars_in(&mut on_mentioned_vars);
                    need_deep_vars(n, &mut all_mentioned_vars);
                    let mut nv_tie = Vars::default();
                    n.vars_in(&mut nv_tie);
                    tie_uf.union_group(nv_tie.order.iter());
                    held_foreign_fn |= !zedc_types::ty::tys_hold_only_own_fns(n.tys());
                    for t in n.tys() {
                        let vf = t.var_facts();
                        // A function held in the need's types that binds variables of its own
                        // (`m.map(id)` with `id(x) = x`; `m.map(top)` or a lambda
                        // `xs -> xs >< max`, whose types hold `max`'s or `(+)`'s variables) is
                        // named by E with the caller's variables around it, which a kept
                        // forward does not carry, so D and E gave different digests (landing
                        // round 3, Gemini L3-G1); refuse, under its own label so a test can
                        // drop it as a negative control (`drop_conds`). The test is
                        // `VarFacts::binds`, which each signature of the nest sets when it
                        // binds a variable and ORs up from the functions it holds. Comparing
                        // the sizes of `names` and `outer`, as round 4 did, misses a pair
                        // holding `A -> A` with `A` its own and `A -> A` with `A` free, whose
                        // sets are both `{A}` (landing round 4, Codex L4.Codex-own-facts).
                        // Complexity tradeoff: the naive test walks `names` against `outer`,
                        // O(v log v) for v variables held, and has the same flaw; used: one
                        // kept bit, O(1).
                        if vf.binds {
                            intrinsic_fails.insert("#4-own-vars");
                        }
                        held_free = held_free.max(vf.free);
                        for nm in vf.names {
                            held_names.insert(nm);
                        }
                        for ov in vf.outer {
                            if !sig.own.contains(&ov) {
                                held_outer.insert(ov);
                            }
                        }
                        for cv in vf.classes {
                            if !sig.own.contains(&cv) && self.is_class(&cv) {
                                held_classes.insert(cv);
                            }
                        }
                    }
                    total_needs += 1;
                    match n.result.as_ref().and_then(Ty::as_var) {
                        Some(rv)
                            if sig.own.contains(rv)
                                && !param_var_set.contains(rv)
                                && seen_res_vars.insert(rv.clone()) =>
                        {
                            total_results += 1;
                            explicit_results.push(rv.clone());
                            if let Some(rk) = class_id(rv) {
                                result_ranges.push((rk, rk + 1));
                            } else {
                                ok_26 = false;
                            }
                        }
                        _ => {
                            ok_5 = false;
                            ok_26 = false;
                        }
                    }
                }
            }
        }

        if !ok_5 {
            intrinsic_fails.insert("#5");
        }
        let consecutive = ok_26
            && !result_ranges.is_empty()
            && result_ranges.windows(2).all(|w| w[0].1 == w[1].0);
        if !consecutive {
            intrinsic_fails.insert("#26");
        }
        let first_result_id = consecutive.then(|| result_ranges[0].0);

        if all_mentioned_vars
            .order
            .iter()
            .any(|v| !sig.own.contains(v) && self.is_class(v))
            || !held_classes.is_empty()
        {
            intrinsic_fails.insert("#4");
        }

        let is_own_result_var = |v: &Arc<str>| -> bool {
            if seen_res_vars.contains(v) {
                return true;
            }
            if let Some(k0) = first_result_id
                && let Some(k) = class_id(v)
            {
                return k >= k0 && k < k0 + total_results;
            }
            false
        };
        let whole_param_set: HashSet<&Arc<str>> = sig
            .arrows
            .iter()
            .flat_map(|a| a.params.iter())
            .filter_map(Ty::as_var)
            .collect();
        if all_mentioned_vars.order.iter().any(|v| {
            (sig.own.contains(v) || self.is_class(v))
                && !whole_param_set.contains(v)
                && !is_own_result_var(v)
        }) {
            intrinsic_fails.insert("#6");
        }

        // Compute `exit_offsets` (`0..total_results` appearing in `sig.arrows`).
        let mut exit_offsets = Vec::new();
        let mut exit_id_set = HashSet::new();
        let mut exit_var_set: HashSet<Arc<str>> = HashSet::new();
        if let Some(k0) = first_result_id {
            for v in &arrow_var_set {
                if let Some(k) = class_id(v)
                    && k >= k0
                    && k < k0 + total_results
                {
                    exit_offsets.push(k - k0);
                    exit_id_set.insert(k);
                    exit_var_set.insert(v.clone());
                }
            }
            exit_offsets.sort_unstable();
            exit_offsets.dedup();
        } else {
            for (j, rv) in explicit_results.iter().enumerate() {
                if arrow_var_set.contains(rv) {
                    exit_offsets.push(j);
                    exit_var_set.insert(rv.clone());
                }
            }
        }

        let is_internal_var = |v: &Arc<str>| -> bool {
            if let Some(k0) = first_result_id
                && let Some(k) = class_id(v)
                && k >= k0
                && k < k0 + total_results
            {
                return !exit_id_set.contains(&k);
            }
            !arrow_var_set.contains(v) && seen_res_vars.contains(v)
        };

        // Compose `exposed_needs`, `#7'` check, and compressed `var_steps` in `O(|sig.needs|)` = `O(1)`.
        let mut exposed_needs = Vec::new();
        // A key holding a `NeedKind`. Clippy flags its `OnceLock`s; these are its only interior-mutable
        // parts: a `Via`'s chain hash, which its `Hash` and `Eq` never read (they read `at`, `text`
        // and `next`), and the set-once caches of the signatures and types it holds, whose `Hash` and
        // `Eq` read their fixed fields and a digest filled once from those. Nothing behind a shared
        // `Arc` is changed in place, so no key's hash or equality can change while it is held.
        #[allow(clippy::mutable_key_type)]
        let mut seen_7p_keys = HashSet::new();
        let mut var_steps = Vec::new();
        let mut seen_step_vars: HashSet<Arc<str>> = HashSet::new();

        for (idx, n) in sig.needs.iter().enumerate() {
            match &n.kind {
                NeedKind::Fwd(fwd) => {
                    let cs = child_summaries[idx].as_ref().expect("child summary");
                    let mut child_subst: Binds = fwd
                        .sigma
                        .iter()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .collect();
                    if let Some(ck0) = cs.first_result_id {
                        for &(off, ref ety) in &fwd.exits {
                            child_subst.insert(format!("${}", ck0 + off).into(), ety.clone());
                        }
                    }
                    for tpl in &cs.exposed_needs {
                        let on_ty = child_subst
                            .get(&tpl.on_var)
                            .cloned()
                            .unwrap_or_else(|| Ty::var(tpl.on_var.clone()));
                        let Some(on_v) = on_ty.as_var() else {
                            continue;
                        };
                        let mapped_need = Need {
                            on: on_ty.clone(),
                            kind: tpl.kind.clone(),
                            result: None,
                            span: n.span,
                            alike: Arc::from([]),
                            via: CallPath::default(),
                        }
                        .replace(&child_subst);
                        let mut mapped_kind = mapped_need.kind;
                        if let NeedKind::Map { lambda, .. } = &mut mapped_kind {
                            *lambda = false;
                        }
                        if !seen_7p_keys.insert((
                            mapped_need.on.clone(),
                            mapped_kind.clone(),
                            tpl.gives,
                        )) {
                            intrinsic_fails.insert("#7'");
                        }
                        let tmp = Need {
                            on: mapped_need.on,
                            kind: mapped_kind.clone(),
                            result: None,
                            span: n.span,
                            alike: Arc::from([]),
                            via: CallPath::default(),
                        };
                        let mut mv = Vars::default();
                        need_deep_vars(&tmp, &mut mv);
                        if mv.order.iter().all(|v| !is_internal_var(v)) {
                            exposed_needs.push(ExposedTemplate {
                                on_var: on_v.clone(),
                                kind: mapped_kind,
                                gives: tpl.gives,
                            });
                        }
                    }
                    for st in &cs.var_steps {
                        match st {
                            FwdVarStep::InternalRun(cnt) => {
                                push_var_step(&mut var_steps, FwdVarStep::InternalRun(*cnt));
                            }
                            FwdVarStep::ClassVar(cv) => {
                                if let Some(mapped_ty) = child_subst.get(cv)
                                    && let Some(mv) = mapped_ty.as_var()
                                {
                                    if !sig.own.contains(mv) && !is_own_result_var(mv) {
                                        continue;
                                    }
                                    if !seen_step_vars.insert(mv.clone()) {
                                        continue;
                                    }
                                    if is_internal_var(mv) {
                                        push_var_step(&mut var_steps, FwdVarStep::InternalRun(1));
                                    } else {
                                        push_var_step(
                                            &mut var_steps,
                                            FwdVarStep::ClassVar(mv.clone()),
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {
                    // The key is the need as a replay records it, `Map.lambda` cleared, as for
                    // a child's templates above: two maps that differ only in that bit replay
                    // to one key, so they must fail `#7'` here (landing review B3).
                    let mut sf = site_free(&n.kind).into_owned();
                    if let NeedKind::Map { lambda, .. } = &mut sf {
                        *lambda = false;
                    }
                    let gives = n.result.is_some();
                    if !seen_7p_keys.insert((n.on.clone(), sf.clone(), gives)) {
                        intrinsic_fails.insert("#7'");
                    }
                    if let Some(on_v) = n.on.as_var() {
                        let exp_kind = sf;
                        let tmp = Need {
                            on: n.on.clone(),
                            kind: exp_kind.clone(),
                            result: None,
                            span: n.span,
                            alike: Arc::from([]),
                            via: CallPath::default(),
                        };
                        let mut mv = Vars::default();
                        need_deep_vars(&tmp, &mut mv);
                        if mv.order.iter().all(|v| !is_internal_var(v)) {
                            exposed_needs.push(ExposedTemplate {
                                on_var: on_v.clone(),
                                kind: exp_kind,
                                gives,
                            });
                        }
                    }
                    let mut nv = Vars::default();
                    need_deep_vars(n, &mut nv);
                    for v in nv.order {
                        if (!sig.own.contains(&v) && !is_own_result_var(&v))
                            || !seen_step_vars.insert(v.clone())
                        {
                            continue;
                        }
                        if is_internal_var(&v) {
                            push_var_step(&mut var_steps, FwdVarStep::InternalRun(1));
                        } else {
                            push_var_step(&mut var_steps, FwdVarStep::ClassVar(v));
                        }
                    }
                }
            }
        }

        let used_param_vars: Vec<Arc<str>> = arrow_param_vars
            .order
            .iter()
            .filter(|v| all_mentioned_vars.contains(v))
            .cloned()
            .collect();
        let on_param_vars: Vec<Arc<str>> = arrow_param_vars
            .order
            .iter()
            .filter(|v| on_mentioned_vars.contains(v))
            .cloned()
            .collect();
        let mut on_exit_offsets = Vec::new();
        if let Some(k0) = first_result_id {
            for &off in &exit_offsets {
                let ev: Arc<str> = format!("${}", k0 + off).into();
                if on_mentioned_vars.contains(&ev) {
                    on_exit_offsets.push(off);
                }
            }
        } else {
            for &off in &exit_offsets {
                if let Some(ev) = explicit_results.get(off)
                    && on_mentioned_vars.contains(ev)
                {
                    on_exit_offsets.push(off);
                }
            }
        }

        let mut visible_vars: HashSet<Arc<str>> = used_param_vars.iter().cloned().collect();
        visible_vars.extend(exit_var_set);
        let var_ties = tie_uf.project(&visible_vars);

        let summary = Arc::new(CalleeSummary {
            used_param_vars,
            on_param_vars,
            on_exit_offsets,
            var_ties,
            first_result_id,
            explicit_result_vars: (!consecutive).then_some(explicit_results),
            total_needs,
            total_results,
            exit_offsets,
            held_free,
            held_names,
            held_outer,
            held_foreign_fn,
            held_classes,
            intrinsic_fails,
            exposed_needs,
            var_steps,
        });
        self.r10.sig_summaries.insert(key, summary.clone());
        summary
    }

    /// Evaluates `A'` (`#1..#24`, `#26`, `#27`, `#7'`; `#25` dropped since `#24-lists + #17` imply it).
    fn r10_eval_a_prime(
        &self,
        sig: &Sig,
        summary: &CalleeSummary,
        args: &[Option<Arg<'a>>],
        partial: bool,
        defer: &BTreeSet<Arc<str>>,
    ) -> Vec<String> {
        let mut fails: BTreeSet<String> = BTreeSet::new();
        if sig.needs.is_empty() {
            fails.insert("#1".into());
            return fails.into_iter().collect();
        }
        if !sig.bounds.is_empty() {
            fails.insert("#2".into());
        }
        if self.level == 0 {
            fails.insert("#8".into());
        }
        if self.replaying > 0 || !self.open.is_empty() {
            fails.insert("#9".into());
        }
        if self.trying {
            fails.insert("#10".into());
        }
        if partial || !self.leaving.is_empty() {
            fails.insert("#11".into());
        }
        if !defer.is_empty() {
            fails.insert("#12".into());
        }
        if !self.refused.is_empty() {
            fails.insert("#13".into());
        }
        if sig.arrows.len() != 1 || sig.arrows.iter().any(|a| a.partial) {
            fails.insert("#21a".into());
        }
        if sig.data || sig.word.is_some() || sig.hull.is_some() || sig.keys.is_some() {
            fails.insert("#21b".into());
        }
        if !sig.held.is_empty() {
            fails.insert("#21c".into());
        }
        let mut ok_21d = true;
        for a in &sig.arrows {
            let mut seen = HashSet::new();
            if a.params.iter().any(|p| {
                !p.as_var()
                    .is_some_and(|v| sig.own.contains(v) && seen.insert(v.clone()))
            }) {
                ok_21d = false;
            }
        }
        if !ok_21d {
            fails.insert("#21d".into());
        }

        let mut roots = HashSet::new();
        let mut ok_14 = true;
        let mut ok_20 = true;
        for a in args {
            let Some(a) = a else {
                ok_14 = false;
                fails.insert("#14".into());
                continue;
            };
            let pieces = a.ty.pieces();
            let one = match &pieces[..] {
                [p] if a.lit.is_none() && a.branches.is_none() => self.class_of(p),
                _ => None,
            };
            let Some(k) = one else {
                ok_14 = false;
                fails.insert("#14".into());
                continue;
            };
            let r = self.find(k);
            let c = &self.classes[r];
            if !c.flowed.is_empty() || c.data {
                fails.insert("#15".into());
            }
            if c.level != self.level {
                fails.insert("#16".into());
            }
            if c.resolved.is_some() || c.generic {
                fails.insert("#17".into());
            }
            if c.mask & OTHER == 0 {
                fails.insert("#18".into());
            }
            // Exact `#19`: refuse if `c.known` is non-empty OR any open forward has >= 1 deferred need on `r`.
            // O(1) by the count `deferred_open`; scanning `r`'s watchers was O(w) per call, O(w^2)
            // for w calls on one operand.
            let has_deferred_known = self.r10.deferred_open.get(&r).is_some_and(|&n| n > 0);
            if !c.known.is_empty() || has_deferred_known {
                fails.insert("#19".into());
            }
            if !roots.insert(r) {
                ok_20 = false;
                fails.insert("#20".into());
            }
            if c.mask != EVERY {
                fails.insert("#23".into());
            }
            if !c.lits.is_empty() || !c.reasons.is_empty() || !c.ops.is_empty() {
                fails.insert("#24-lists".into());
            }
            if !c.orders.is_empty() || c.order_of.is_some() {
                fails.insert("#24-orders".into());
            }
            if !c.narrowed_to.is_empty() || c.narrows {
                fails.insert("#24-narrowing".into());
            }
            if c.asked || c.floats || c.rat || c.refused || c.unoffered != 0 {
                fails.insert("#24-flags".into());
            }
        }

        for &f in &summary.intrinsic_fails {
            fails.insert(f.into());
        }

        if (!ok_21d || !ok_20 || !ok_14)
            && !fails.contains("#7'")
            && let Some(a0) = sig.arrows.first()
        {
            let mut subst = Binds::new();
            for (p, a) in a0.params.iter().zip(args) {
                if let (Some(v), Some(a)) = (p.as_var(), a) {
                    let mapped = subst
                        .remove(v)
                        .map_or_else(|| a.ty.clone(), |old| old.union(&a.ty));
                    subst.insert(v.clone(), mapped);
                }
            }
            // A key holding a `NeedKind`. Clippy flags its `OnceLock`s; these are its only interior-mutable
            // parts: a `Via`'s chain hash, which its `Hash` and `Eq` never read (they read `at`, `text`
            // and `next`), and the set-once caches of the signatures and types it holds, whose `Hash` and
            // `Eq` read their fixed fields and a digest filled once from those. Nothing behind a shared
            // `Arc` is changed in place, so no key's hash or equality can change while it is held.
            #[allow(clippy::mutable_key_type)]
            let mut seen_keys = HashSet::new();
            for tpl in &summary.exposed_needs {
                let on_ty = subst
                    .get(&tpl.on_var)
                    .cloned()
                    .unwrap_or_else(|| Ty::var(tpl.on_var.clone()));
                let dummy = Need {
                    on: on_ty,
                    kind: tpl.kind.clone(),
                    result: None,
                    span: Span { start: 0, end: 0 },
                    alike: Arc::from([]),
                    via: CallPath::default(),
                }
                .replace(&subst);
                if !seen_keys.insert((dummy.on, dummy.kind, tpl.gives)) {
                    fails.insert("#7'".into());
                    break;
                }
            }
        }

        let drop_conds = &self.r10.cfg.drop_conds;
        fails
            .into_iter()
            .filter(|f| !drop_conds.contains(f))
            .collect()
    }

    /// Attempts to admit the call at `apply_one` in `O(1)` time (`M62`, `M63`, `M66`).
    #[allow(clippy::too_many_arguments)]
    pub(in crate::check) fn r10_try_admit(
        &mut self,
        what: &str,
        sig: &Sig,
        arrow: &Arrow,
        args: &[Option<Arg<'a>>],
        partial: bool,
        binds: &mut Binds,
        defer: &BTreeSet<Arc<str>>,
        span: Span,
    ) -> Option<Vec<Need>> {
        if !self.r10.cfg.enabled || sig.needs.is_empty() {
            return None;
        }

        let summary = self.r10_get_or_build_summary(sig);
        let fails = self.r10_eval_a_prime(sig, &summary, args, partial, defer);
        if !fails.is_empty() {
            for f in &fails {
                *self.r10.stats.refused.entry(f.clone()).or_default() += 1;
            }
            return None;
        }

        let level = self.level;
        // M2 / Codex R4: zero-extend `self.gens` if needed (as `bound` would during replay).
        if self.gens.len() <= level {
            self.gens.resize(level + 1, 0);
        }

        let store_mode = self.r10.cfg.store_mode;
        let total_results = summary.total_results;

        // 1. Reserve `total_results` class IDs in `O(1)` and materialize ONLY `exit(F)` (`M62`).
        let lo = match store_mode {
            StoreMode::SparseM62 => self.classes.reserve_ids_o1(total_results),
            StoreMode::BrokenNoCounterAdvance => self.classes.len(),
        };
        let hi = lo + total_results;

        let mut exit_ids = Vec::with_capacity(summary.exit_offsets.len());
        for &off in &summary.exit_offsets {
            let eid = match store_mode {
                StoreMode::BrokenNoCounterAdvance => {
                    self.r10.ensure_level(level);
                    self.r10.pending_levels[level].reserving = true;
                    let id = self.classes.len();
                    self.classes.push(Self::make_fresh_class(id, level, true));
                    self.r10.pending_levels[level].reserving = false;
                    id
                }
                StoreMode::SparseM62 => {
                    let id = lo + off;
                    self.classes
                        .materialize_at(id, Self::make_fresh_class(id, level, true));
                    id
                }
            };
            exit_ids.push(eid);
        }

        // 2. Bind exit result variables in `binds` (`O(|exit(F)|)` = `O(1)`).
        if let Some(k0) = summary.first_result_id {
            for (idx, &off) in summary.exit_offsets.iter().enumerate() {
                let v: Arc<str> = format!("${}", k0 + off).into();
                let eid = match store_mode {
                    StoreMode::BrokenNoCounterAdvance => exit_ids[idx],
                    StoreMode::SparseM62 => lo + off,
                };
                binds.insert(v, Ty::var(format!("${eid}").into()));
            }
        } else if let Some(exp_vars) = &summary.explicit_result_vars {
            for (idx, &off) in summary.exit_offsets.iter().enumerate() {
                let eid = exit_ids[idx];
                binds.insert(exp_vars[off].clone(), Ty::var(format!("${eid}").into()));
            }
        }

        // 3. Advance `self.needs` by `total_needs` in `O(1)`.
        let seq_lo = self.needs + 1;
        self.needs += summary.total_needs;

        // 4. Build `param_map`, `watched_roots`, and `has_any_need_on` (`#19`).
        let used_set: HashSet<&Arc<str>> = summary.used_param_vars.iter().collect();
        let on_param_set: HashSet<&Arc<str>> = summary.on_param_vars.iter().collect();
        let mut param_map: Vec<(Arc<str>, Ty)> = Vec::with_capacity(summary.used_param_vars.len());
        let mut watched_roots: BTreeSet<usize> = BTreeSet::new();
        let mut has_any_need_on: HashSet<usize> = HashSet::new();
        let mut seen_pvars = HashSet::new();
        for (p, a) in arrow.params.iter().zip(args) {
            if let Some(pv) = p.as_var()
                && seen_pvars.insert(pv.clone())
            {
                let bound_ty = binds.get(pv).cloned().unwrap_or_else(|| {
                    a.as_ref()
                        .map(|arg| arg.ty.clone())
                        .unwrap_or_else(Ty::empty)
                });
                for piece in bound_ty.pieces() {
                    if let Some(k) = self.class_of(&piece) {
                        let r = self.find(k);
                        watched_roots.insert(r);
                        if on_param_set.contains(pv) {
                            has_any_need_on.insert(r);
                        }
                    }
                }
                if used_set.contains(pv) {
                    let root_ty = match bound_ty.pieces().as_slice() {
                        [piece] => match self.class_of(piece) {
                            Some(k) => Ty::var(format!("${}", self.find(k)).into()),
                            None => bound_ty,
                        },
                        _ => bound_ty,
                    };
                    param_map.push((pv.clone(), root_ty));
                }
            }
        }
        for a in args.iter().flatten() {
            for piece in a.ty.pieces() {
                if let Some(k) = self.class_of(&piece) {
                    watched_roots.insert(self.find(k));
                }
            }
        }
        for (&off, &eid) in summary.exit_offsets.iter().zip(&exit_ids) {
            watched_roots.insert(eid);
            if summary.on_exit_offsets.contains(&off) {
                has_any_need_on.insert(eid);
            }
        }

        // 5. Instantiate `O(1)` `exposed_keys` for `f1` need-hit detection.
        let mut exposed_subst = Binds::new();
        for (pv, rty) in &param_map {
            exposed_subst.insert(pv.clone(), rty.clone());
        }
        if let Some(k0) = summary.first_result_id {
            for (idx, &off) in summary.exit_offsets.iter().enumerate() {
                exposed_subst.insert(
                    format!("${}", k0 + off).into(),
                    Ty::var(format!("${}", exit_ids[idx]).into()),
                );
            }
        }
        let mut exposed_keys: HashMap<usize, Vec<(NeedKind, bool)>> = HashMap::new();
        for tpl in &summary.exposed_needs {
            let on_ty = exposed_subst
                .get(&tpl.on_var)
                .cloned()
                .unwrap_or_else(|| Ty::var(tpl.on_var.clone()));
            if let Some(on_v) = on_ty.as_var()
                && let Some(k) = class_id(on_v)
                && self.classes.is_materialized(k)
            {
                let r = self.find(k);
                let dummy = Need {
                    on: on_ty,
                    kind: tpl.kind.clone(),
                    result: None,
                    span,
                    alike: Arc::from([]),
                    via: CallPath::default(),
                }
                .replace(&exposed_subst);
                exposed_keys
                    .entry(r)
                    .or_default()
                    .push((dummy.kind, tpl.gives));
            }
        }

        // 6. Reserve `M63` `PendingSlot` at `level` in `O(1)`.
        self.r10.ensure_level(level);
        let pending_slot = self.r10.pending_levels[level].reserve_slot_o1(exit_ids.clone());
        self.r10.stats.pending_slot_reserves += 1;
        self.r10.stats.admitted += 1;

        let fwd_id = self.r10.forwards.len();
        for &r in &watched_roots {
            self.r10.root_watchers.entry(r).or_default().push(fwd_id);
            *self.r10.open_watchers.entry(r).or_default() += 1;
        }
        for &r in &has_any_need_on {
            *self.r10.deferred_open.entry(r).or_default() += 1;
        }
        for (&r, ks) in &exposed_keys {
            for k in ks {
                self.r10
                    .key_watchers
                    .entry((r, k.clone()))
                    .or_default()
                    .push(fwd_id);
            }
        }
        self.r10.open_by_level[level].push(fwd_id);
        self.r10.forwards.push(OpenForward {
            level,
            what_note: format!("{what} needs this of its argument here").into(),
            callee_sig: Arc::new(sig.clone()),
            summary,
            param_map,
            lo,
            hi,
            exit_ids,
            seq_lo,
            call_span: span,
            pending_slot,
            watched_roots,
            has_any_need_on,
            exposed_keys,
            status: ForwardStatus::Open,
        });

        Some(Vec::new())
    }

    /// Checks `f2` (`Order` need) and `f1` (exact exposed-key collision) in `Ck::need`.
    pub(in crate::check) fn r10_on_need(&mut self, r: usize, key: &(NeedKind, bool)) {
        if !self.r10.cfg.enabled {
            return;
        }
        assert!(
            !self.r10.forcing,
            "M56(c): Ck::need must never be entered while forcing"
        );
        // Naive: clone `r`'s watcher list and compare `key` with every open watcher's exposed keys,
        // O(w) per need and O(w^2) for w forwards on one operand. Here: the open count answers
        // "none" in O(1), and `key_watchers` gives the forwards exposing exactly `key` on `r`.
        // Each entry it returns is dropped here (the open ones are forced, the rest are closed
        // already), so every entry is visited once: O(1) amortized per need.
        if self.r10.open_watchers.get(&r).is_none_or(|&n| n == 0) {
            return;
        }
        if matches!(key.0, NeedKind::Order { .. }) {
            self.r10_force_root(r, "f2");
            return;
        }
        if self.r10.barrier_skipped("f1") {
            return;
        }
        let Some(fids) = self.r10.key_watchers.remove(&(r, key.clone())) else {
            return;
        };
        self.r10.stats.f1_key_checks += fids.len();
        let mut hit_fids: Vec<usize> = fids
            .into_iter()
            .filter(|&fid| self.r10.forwards[fid].status == ForwardStatus::Open)
            .collect();
        if !hit_fids.is_empty() {
            self.r10.forcing = true;
            hit_fids.sort_unstable();
            hit_fids.dedup();
            for fid in hit_fids {
                self.r10_force_forward(fid, "f1");
            }
            self.r10.forcing = false;
        }
    }

    /// Pre-`resolve` `f8` negative-control hook (`M28` / `M56(c)`).
    pub(in crate::check) fn r10_f8_before_resolve_if_configured(&mut self, level: usize) {
        if !self.r10.cfg.enabled || !self.r10.cfg.f8_before_resolve {
            return;
        }
        self.r10.ensure_level(level);
        let open_fids: Vec<usize> = self.r10.open_by_level[level]
            .iter()
            .copied()
            .filter(|&fid| self.r10.forwards[fid].status == ForwardStatus::Open)
            .collect();
        for fid in open_fids {
            let escaped = self.r10.forwards[fid].watched_roots.iter().any(|&w| {
                let r = self.find(w);
                let c = &self.classes[r];
                c.level != level
                    || c.resolved
                        .as_ref()
                        .is_some_and(|t| t != &Ty::var(format!("${r}").into()))
            });
            if escaped {
                self.r10_force_forward(fid, "f8-early");
            }
        }
    }

    /// Post-`resolve`, pre-`now` `f8` check and forward detachment in `generalize`.
    pub(in crate::check) fn r10_after_resolve_and_detach(
        &mut self,
        level: usize,
        own: &mut Vec<usize>,
        done: &mut Vec<usize>,
    ) -> Vec<usize> {
        if !self.r10.cfg.enabled {
            return Vec::new();
        }
        self.r10.ensure_level(level);
        let open_fids: Vec<usize> = self.r10.open_by_level[level]
            .iter()
            .copied()
            .filter(|&fid| self.r10.forwards[fid].status == ForwardStatus::Open)
            .collect();

        let mut any_forced = false;
        if self.r10.cfg.decode_in_generalize {
            for &fid in &open_fids {
                self.r10_force_forward(fid, "neg-decode-generalize");
                any_forced = true;
            }
        } else if !self.r10.cfg.f8_before_resolve && !self.r10.barrier_skipped("f8") {
            for &fid in &open_fids {
                let must_force = self.r10.forwards[fid].watched_roots.iter().any(|&w| {
                    let r = self.find(w);
                    let c = &self.classes[r];
                    c.level != level
                        || match &c.resolved {
                            Some(t) => t != &Ty::var(format!("${r}").into()),
                            None => true,
                        }
                });
                if must_force {
                    self.r10_force_forward(fid, "f8");
                    any_forced = true;
                }
            }
        }

        if any_forced {
            let full_order = self.r10.pending_levels[level].flatten();
            let mut new_own = Vec::with_capacity(full_order.len());
            let mut new_done = Vec::with_capacity(full_order.len());
            let mut seen_own = HashSet::new();
            for k in full_order {
                let r = self.find(k);
                let at = self.classes[r].level;
                if at < level && self.classes[r].resolved.is_none() {
                    continue;
                }
                if self.classes[r].resolved.is_none() {
                    self.resolve(r);
                }
                if at == level && seen_own.insert(r) {
                    new_own.push(r);
                }
                new_done.push(k);
            }
            *own = new_own;
            *done = new_done;
        }

        let mut kept_fids = Vec::new();
        for fid in open_fids {
            if self.r10.forwards[fid].status == ForwardStatus::Open {
                self.r10.forwards[fid].status = ForwardStatus::KeptInSig;
                let (lo, hi) = (self.r10.forwards[fid].lo, self.r10.forwards[fid].hi);
                if lo < hi {
                    self.r10.closed_internal_ranges.insert(lo, hi);
                }
                self.r10.stats.kept_at_generalize += 1;
                // Was: `retain` on each watched root's list, O(w) per kept forward.
                self.r10.close_counts(fid);
                kept_fids.push(fid);
            }
        }
        self.r10.pending_levels[level] = PendingLevel::default();
        self.r10.open_by_level[level].clear();
        kept_fids
    }

    /// Merges direct needs with `NeedKind::Fwd` items in exact sequence order before `share_alike` (`M66`).
    pub(in crate::check) fn r10_merge_direct_and_kept_needs(
        &mut self,
        kept_fids: &[usize],
        direct_sorted: Vec<(usize, Need)>,
    ) -> Vec<Need> {
        if kept_fids.is_empty() {
            self.r10.stats.generalize_needs_walked += direct_sorted.len();
            return direct_sorted.into_iter().map(|(_, n)| n).collect();
        }
        let mut all_seq: Vec<(usize, Need)> =
            Vec::with_capacity(direct_sorted.len() + kept_fids.len());
        all_seq.extend(direct_sorted);
        for &fid in kept_fids {
            let f = &self.r10.forwards[fid];
            let fwd_need = self.build_fwd_need_from_open(f);
            all_seq.push((
                f.seq_lo,
                Need {
                    on: Ty::empty(),
                    kind: NeedKind::Fwd(Arc::new(fwd_need)),
                    result: None,
                    span: f.call_span,
                    alike: Arc::from([]),
                    via: CallPath::default(),
                },
            ));
        }
        all_seq.sort_by_key(|(seq, _)| *seq);
        self.r10.stats.generalize_needs_walked += all_seq.len();
        all_seq.into_iter().map(|(_, n)| n).collect()
    }

    /// Barrier `N4`: if `share_alike` merged any variable held by a kept `NeedKind::Fwd`, expand
    /// that forward so `sig.replace(&deep)` rewrites it identically to `E`.
    pub(in crate::check) fn r10_n4_expand_if_merged(
        &mut self,
        shared: Vec<Need>,
        merged: &Binds,
        level: usize,
        own: &mut Vec<usize>,
        done: &mut Vec<usize>,
    ) -> Vec<Need> {
        if merged.is_empty() || self.r10.barrier_skipped("N4") {
            return shared;
        }
        let any_hit = shared.iter().any(|n| match &n.kind {
            NeedKind::Fwd(fwd) => fwd
                .sigma
                .iter()
                .map(|(_, t)| t)
                .chain(fwd.exits.iter().map(|(_, t)| t))
                .any(|t| t.vars.iter().any(|v| merged.contains_key(v))),
            _ => false,
        });
        if !any_hit {
            return shared;
        }
        self.r10_expand_kept_fwds(shared, level, own, done)
    }

    /// Expands every kept forward in `needs` into its needs, making and resolving its
    /// internal classes at `level` and listing them in `own` and `done`.
    pub(in crate::check) fn r10_expand_kept_fwds(
        &mut self,
        shared: Vec<Need>,
        level: usize,
        own: &mut Vec<usize>,
        done: &mut Vec<usize>,
    ) -> Vec<Need> {
        let clear_lambda = !self.r10.cfg.keep_map_lambda_on_decode;
        let mut expanded = Vec::new();
        for n in shared {
            match &n.kind {
                NeedKind::Fwd(fwd) => {
                    self.r10.stats.n4_merged_expansions += 1;
                    // The decoded needs name the forward's internal classes `$k`. A kept
                    // forward never made them, so make and resolve them here as `generalize`
                    // does its own; otherwise they reach the signature unnamed (Neon B2).
                    if let Some(lo) = fwd.base_class {
                        for id in lo..lo + fwd.need_count {
                            if !self.classes.is_materialized(id) {
                                self.classes
                                    .materialize_at(id, Self::make_fresh_class(id, level, true));
                                self.resolve(id);
                                own.push(id);
                                done.push(id);
                            }
                        }
                    }
                    expanded.extend(fwd.decode_uncounted(n.span, clear_lambda));
                }
                _ => expanded.push(n),
            }
        }
        expanded
    }

    /// Makes, resolves and names the internal classes of `sig`'s compact forwards that are not
    /// made yet, for a partial application of `sig` that leaves their needs to the function it
    /// gives (landing round 4, Gemini F-R4-1). The decoded needs name those results `$k`, so
    /// they become the given function's own variables. The flat form made each one when the
    /// callee was checked, resolved it, and named it at the callee's `generalize`; a kept
    /// forward made none and keeps those names in its runs (`gen_naming`), so finishing would
    /// leave each `$k` unnamed in the finished caller. Each class takes the name its run gives
    /// it, as in the flat form. A forward named at `finish` already decodes to names, not
    /// classes, and needs none.
    // Complexity tradeoff: O(need_count) per forward, as the decode `replay` already made for
    // this call. The naive alternative, decoding every kept forward when its function is
    // generalized, costs that much at every link of a chain; this costs it only at a partial
    // application, which is never a link of a chain.
    pub(in crate::check) fn r10_make_left_internal_classes(&mut self, sig: &Sig) {
        for n in &sig.needs {
            let NeedKind::Fwd(fwd) = &n.kind else {
                continue;
            };
            let (Some(lo), None) = (fwd.base_class, &fwd.finish_naming) else {
                continue;
            };
            let exits: HashSet<usize> = fwd.exits.iter().map(|(o, _)| *o).collect();
            let runs = fwd.gen_naming.iter().flat_map(|g| g.runs.iter());
            let mut names = runs.flat_map(|r| r.names::<Arc<str>>());
            for j in (0..fwd.need_count).filter(|j| !exits.contains(j)) {
                let name = names.next();
                let id = lo + j;
                if self.classes.is_materialized(id) {
                    continue;
                }
                let class = Self::make_fresh_class(id, self.level, true);
                self.classes.materialize_at(id, class);
                self.resolve(id);
                self.classes[id].name = name;
            }
        }
    }

    /// M56(c) counter: checks whether `deep` or `outside` binds any variable of any kept `FwdNeed`.
    pub(in crate::check) fn r10_check_m56c_deep_outside(
        &mut self,
        sig: &Sig,
        deep: &Binds,
        outside: &Binds,
    ) {
        for n in &sig.needs {
            if let NeedKind::Fwd(_) = &n.kind {
                self.r10.stats.m56c_kept_blocks += 1;
                let mut vs = Vars::default();
                n.vars_in(&mut vs);
                for v in &vs.order {
                    self.r10.stats.m56c_kept_vars += 1;
                    if deep.contains_key(v) || outside.contains_key(v) {
                        self.r10.stats.m56c_bound_vars += 1;
                    }
                }
            }
        }
    }

    /// Names `sig`'s materialized `mine` variables in `O(1)` per compact link (`M62`), advancing
    /// `n_idx` across unmaterialized `I(F)` runs in one step via `fresh_variable_span_stats_indexed` and
    /// pre-computing each `FwdNeed`'s `M65` `digest_summary`.
    pub(in crate::check) fn r10_name_compact_sig_in_generalize(
        &mut self,
        sig: &mut Sig,
        own: &[usize],
        outside: &Binds,
    ) {
        let facts = VarFacts::of(sig);
        let mine: HashSet<Arc<str>> = own
            .iter()
            .map(|r| Arc::from(format!("${r}")))
            .filter(|v| facts.classes.contains(v) && !outside.contains_key(v))
            .collect();
        // The skip set, indexed once for every run of the signature (`SkipIndex`, whose
        // comment gives the tradeoff): O(s log s) here, O(log s) per run below.
        let held_now = current_held_var_snapshot();
        let skip_arc = Arc::new(SkipIndex::new(
            facts.names.iter().map(|s| s.as_ref()),
            &held_now,
        ));

        let mut n_idx = facts.free;
        let mut mine_seen = BTreeSet::new();
        let mut seen_vars: HashSet<Arc<str>> = HashSet::new();
        let broken_linear_names = self.r10.cfg.broken_linear_names;

        let mut name_var = |ck: &mut Self,
                            bounds: &mut BTreeMap<Arc<str>, u8>,
                            v: &Arc<str>,
                            n_ref: &mut usize| {
            if !mine.contains(v) || !seen_vars.insert(v.clone()) {
                return;
            }
            let r = class_id(v).expect("a class variable");
            let name = fresh_name(Names::Variables, n_ref, |nm| facts.names.contains(nm));
            ck.r10.stats.names_drawn += 1;
            if ck.classes[r].mask != EVERY {
                bounds.insert(v.clone(), ck.classes[r].mask);
            }
            ck.classes[r].name = Some(name);
            mine_seen.insert(v.clone());
        };

        // 1. Walk `sig.arrows` first (`Sig::first_seen` order).
        let mut arrow_vars = Vars::default();
        let mut arrow_param_vars: HashSet<Arc<str>> = HashSet::new();
        for a in &sig.arrows {
            for p in &a.params {
                p.vars_in(&mut arrow_vars);
                if let Some(pv) = p.as_var() {
                    arrow_param_vars.insert(pv.clone());
                }
            }
            a.result.vars_in(&mut arrow_vars);
        }
        for v in &arrow_vars.order {
            name_var(self, &mut sig.bounds, v, &mut n_idx);
        }

        // 2. Walk `sig.needs` in order, stepping `InternalRun(cnt)` in ONE step (`M62`)!
        for nd in &mut sig.needs {
            match &mut nd.kind {
                NeedKind::Fwd(fwd_arc) => {
                    let steps = fwd_arc.var_steps.clone();
                    let mut runs = Vec::new();
                    for st in steps {
                        match st {
                            FwdVarStep::ClassVar(v) => {
                                name_var(self, &mut sig.bounds, &v, &mut n_idx);
                            }
                            FwdVarStep::InternalRun(cnt) => {
                                if cnt > 0 {
                                    runs.push(NameRun {
                                        start_n: n_idx,
                                        count: cnt,
                                        skip: skip_arc.clone(),
                                        held: held_now.clone(),
                                    });
                                    if broken_linear_names {
                                        // M62 negative control: quadratic one-by-one draw (Codex R9).
                                        for _ in 0..cnt {
                                            let _: Arc<str> =
                                                fresh_name(Names::Variables, &mut n_idx, |nm| {
                                                    facts.names.contains(nm)
                                                });
                                            self.r10.stats.names_drawn += 1;
                                        }
                                    } else {
                                        // M62 fix: ONE bulk step handling n < 4 + ProgramNames + skip!
                                        let stats = fresh_variable_span_stats_indexed(
                                            n_idx, cnt, &skip_arc, &held_now,
                                        );
                                        n_idx = stats.end_n;
                                    }
                                }
                            }
                        }
                    }
                    let inner = Arc::make_mut(fwd_arc);
                    inner.gen_naming = Some(FwdFinishNaming { runs });
                }
                _ => {
                    let mut nv = Vars::default();
                    nd.vars_in(&mut nv);
                    for v in &nv.order {
                        name_var(self, &mut sig.bounds, v, &mut n_idx);
                    }
                }
            }
        }

        for &r in own {
            if self.classes[r].name.is_none()
                && let Some(t) = &self.classes[r].resolved
                && t.vars.iter().any(|v| class_id(v).is_some())
            {
                self.classes[r].resolved = Some(Ty::dynamic());
            }
        }

        sig.own = mine_seen;
        sig.named = n_idx;
        sig.facts = Default::default();
        sig.note_held();

        // 3. Pre-compute `digest_summary` at `R_BASE` on each `NeedKind::Fwd` in `O(#sigma)` = `O(1)`.
        let mut mat_result_ranks: HashMap<Arc<str>, usize> = HashMap::new();
        let mut cur_rank = 0usize;
        for nd in &sig.needs {
            match &nd.kind {
                NeedKind::Fwd(fwd) => {
                    for &(off, ref ety) in &fwd.exits {
                        if let Some(v) = ety.as_var()
                            && sig.own.contains(v)
                            && !arrow_param_vars.contains(v)
                        {
                            mat_result_ranks.entry(v.clone()).or_insert(cur_rank + off);
                        }
                    }
                    cur_rank += fwd.need_count;
                }
                _ => {
                    if let Some(v) = nd.result.as_ref().and_then(Ty::as_var)
                        && sig.own.contains(v)
                        && !arrow_param_vars.contains(v)
                    {
                        mat_result_ranks.entry(v.clone()).or_insert(cur_rank);
                    }
                    cur_rank += 1;
                }
            }
        }

        let mut build_rank = 0usize;
        for nd in &mut sig.needs {
            if let NeedKind::Fwd(fwd_arc) = &mut nd.kind {
                let inner = Arc::make_mut(fwd_arc);
                r10_hash::set_fwd_digest_summary(inner, nd.span, build_rank, &mat_result_ranks);
                build_rank += inner.need_count;
            } else {
                build_rank += 1;
            }
        }
    }
}
