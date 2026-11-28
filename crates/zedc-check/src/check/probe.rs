//! The sparse class store, M63 pending slots, and the state of the forward needs of design D
//! (`R10State`, `R10Config`, `R10Stats`, `CalleeSummary`, `OpenForward`).
//!
//! Kept as a leaf module (names no item of `check/mod.rs` or `check/walk.rs`) so `zedc-check`
//! has no import cycle (`tests/steps/s_01f_import_graph`).

#![allow(missing_docs)]

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use zedc_syntax::lex::Span;
use zedc_types::ty::{FwdVarStep, NeedKind, Sig, Ty};

pub(super) use store::Classes;

// ===========================================================================
// Round 10 Fixed-D Configuration, Statistics, Pending Slots & Forward State
// ===========================================================================

/// Sparse class store mode (`M62`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreMode {
    /// Reserve logical IDs in O(1), materialize only `exit(F)` at admission.
    SparseM62,
    /// Negative control: do not advance logical ID counter at admission.
    BrokenNoCounterAdvance,
}

/// Pending-level mode (`M63`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PendingMode {
    /// Exact O(1) slot reservation, O(L) fill at force (preserves E's pending order).
    SlotsM63,
    /// Negative control: append forced IDs to end of `pending[level]` (disproved by M63).
    BrokenAppendAtForce,
}

/// Configuration for fixed-D and its negative controls.
#[derive(Clone, Debug)]
pub struct R10Config {
    pub store_mode: StoreMode,
    pub pending_mode: PendingMode,
    /// M66 control: force all kept forwards inside `generalize` (quadratic decode).
    pub decode_in_generalize: bool,
    /// M66 control: do not clear `Map.lambda` when decoding a `FwdNeed` (reproduces R9 lambda bug).
    pub keep_map_lambda_on_decode: bool,
    /// M31 control: disable the shared `split_sites` memo in `finish` (quadratic split walk).
    pub no_split_memo: bool,
    /// M31 control: skip walking `NeedKind::Fwd` callees in `finish` `split_needs`.
    pub skip_compact_split_needs: bool,
    /// M62 control: draw hidden names one by one (`0..count`) instead of O(1) bulk jump.
    pub broken_linear_names: bool,
    /// M8 control: skip writing deferred `call_written` entries on force.
    pub skip_call_written_on_force: bool,
    /// M28 / M56(c) control: run `f8` before `resolve`.
    pub f8_before_resolve: bool,
    /// M56(c) control: simulate stuck `forcing` skipping the second forward on a `merge`.
    pub force_skip_second_on_merge: bool,
    /// Barrier skip control (`"f1"`..`"f8"`, `"N4"`, and `"B4"`, the expansion at `generalize` of
    /// the kept forwards of a signature that holds a class of a function around it).
    pub skip_barrier: Option<&'static str>,
    /// Admission conditions dropped for negative controls (`"#7'"`, `"#14"`, `"#19"`, `"#27"`,
    /// etc.).
    pub drop_conds: HashSet<String>,
    /// FAIL-map-chain-own-vars-carry control: `finish` leaves out the held names of compact
    /// forwards (`VarFacts::fwd_names`) and the finishing of the functions that hold such a
    /// forward, as D did before that row while `#4-own-vars` refused every function that binds
    /// variables of its own.
    pub skip_held_names: bool,
    /// HELDNAME-closed-in-callee control: a callee finishes only the held functions that bind
    /// all their variables, as before that row, so a forward holding one that reads classes of
    /// its callee keeps them written `$k` and its callers decode it (`unnamed`); the reference
    /// the default check is compared with.
    pub finish_only_closed_held: bool,
    /// HELDNAME-defer-unmentioned-admit control: `#12` refuses every call with a variable left
    /// to the function's own calls (`defer` not empty), as before that row, not only one whose
    /// needs mention such a variable; the reference the default check is compared with.
    pub refuse_any_defer: bool,
    /// FAIL-map-chain-held-name-renamed-apart-quadratic reference (plan section 8, D5): a
    /// signature whose held name is named apart decodes its forwards and names the flat form
    /// (`r10_flat_held`), as the checker did before that row's part A. Until part A is written
    /// this is the only route, so the switch changes nothing yet; part A's naming in the eager
    /// order must read it and keep this route under it, and the red tests that compare with it
    /// assert that the default route decodes nothing.
    pub flat_on_apart: bool,
    /// The mutant of that plan's T3 (Claude's `FORCE_HELD_LAST`, XR-renamed-apart-plan r1): a
    /// signature that takes the flat form for a held name named apart and nothing else keeps
    /// each key's name from the first pass, held names last. It must make the T3 programs A, B,
    /// D, F, G, H and J differ from the reference on `Sig::digest`, and change nothing in C, E,
    /// I and K.
    pub force_held_last: bool,
}

impl Default for R10Config {
    fn default() -> Self {
        R10Config {
            store_mode: StoreMode::SparseM62,
            pending_mode: PendingMode::SlotsM63,
            decode_in_generalize: false,
            keep_map_lambda_on_decode: false,
            no_split_memo: false,
            skip_compact_split_needs: false,
            broken_linear_names: false,
            skip_call_written_on_force: false,
            f8_before_resolve: false,
            force_skip_second_on_merge: false,
            skip_barrier: None,
            drop_conds: HashSet::new(),
            skip_held_names: false,
            finish_only_closed_held: false,
            refuse_any_defer: false,
            flat_on_apart: false,
            force_held_last: false,
        }
    }
}

/// Operation counts recorded during one `Ck` run (`M62`, `M31`, `M66`, `M56(c)`).
#[derive(Clone, Debug, Default)]
pub struct R10Stats {
    pub admitted: usize,
    pub forced: usize,
    pub kept_at_generalize: usize,
    pub refused: BTreeMap<String, usize>,
    pub force_reasons: BTreeMap<String, usize>,
    pub f1_key_checks: usize,
    pub pending_slot_reserves: usize,
    pub pending_slot_fills: usize,
    pub n4_merged_expansions: usize,
    /// Physical `Class` structs allocated in `Classes`.
    pub alloc_classes: usize,
    /// Logical class ID watermark (`classes.len()`).
    pub logical_classes: usize,
    /// Items iterated in `generalize`'s `done` loop.
    pub generalize_done_items: usize,
    /// Needs walked in `generalize` (before `share_alike`).
    pub generalize_needs_walked: usize,
    /// Needs passed into `share_alike`.
    pub share_alike_needs_walked: usize,
    /// Signatures visited by `finish`'s `split_needs` walk.
    pub finish_sigs_walked: usize,
    /// Needs walked by `finish`'s `split_needs` walk.
    pub finish_needs_walked: usize,
    /// Individual `fresh_name` calls made in `generalize` (constant per link with O(1) bulk jump!).
    pub names_drawn: usize,
    /// Records (`uses` + `known` + `orders`) written by `need` or `force`.
    pub records_written: usize,
    /// `call_written` entries pushed.
    pub call_written_entries: usize,
    /// M56(c) census: kept `FwdNeed` blocks checked at `generalize`.
    pub m56c_kept_blocks: usize,
    /// M56(c) census: variables held by kept `FwdNeed` blocks.
    pub m56c_kept_vars: usize,
    /// M56(c) census: kept `FwdNeed` variables bound by `deep` or `outside` (must be 0!).
    pub m56c_bound_vars: usize,
}

// The configuration switches are for tests only (landing review B1): a production build has no
// way to pick a negative control. E, the eager checker D was compared with, is gone (author,
// QUESTIONS A170: removed once PROOF-map-chain-d-skip-and-admit proved D gives no wrong answer);
// the r10 tests check D against E's output, recorded as expected output (`r10_tests/expected.out`).
#[cfg(test)]
thread_local! {
    static NEXT_CONFIG: RefCell<Option<R10Config>> = const { RefCell::new(None) };
    static PERSISTENT_CONFIG: RefCell<Option<R10Config>> = const { RefCell::new(None) };
}

thread_local! {
    static LAST_STATS: RefCell<R10Stats> = RefCell::new(R10Stats::default());
}

#[cfg(test)]
pub fn set_next_config(cfg: R10Config) {
    NEXT_CONFIG.with(|c| *c.borrow_mut() = Some(cfg));
}

/// The configuration a test set for the next check, or for every check on this thread.
#[cfg(test)]
fn set_config() -> Option<R10Config> {
    NEXT_CONFIG
        .with(|c| c.borrow_mut().take())
        .or_else(|| PERSISTENT_CONFIG.with(|c| c.borrow().clone()))
}

/// None: a production build takes no configuration from code.
#[cfg(not(test))]
fn set_config() -> Option<R10Config> {
    None
}

#[cfg(test)]
pub fn set_persistent_config(cfg: Option<R10Config>) {
    PERSISTENT_CONFIG.with(|c| *c.borrow_mut() = cfg);
}

pub fn last_r10_stats() -> R10Stats {
    LAST_STATS.with(|s| s.borrow().clone())
}

pub(in crate::check) fn save_r10_stats(stats: &R10Stats) {
    LAST_STATS.with(|s| *s.borrow_mut() = stats.clone());
}

/// One entry in a level's `M63` pending list.
#[derive(Clone, Copy, Debug)]
pub enum PendingItem {
    Class(usize),
    Slot(usize),
}

/// Reserved slot for an admitted forward's class IDs (`M63`).
#[derive(Clone, Debug)]
pub enum PendingSlot {
    Unforced { exits: Vec<usize> },
    Forced(Vec<usize>),
}

/// Per-level pending list supporting O(1) slot reservation and O(L) exact in-place fill (`M63`).
#[derive(Clone, Debug, Default)]
pub struct PendingLevel {
    pub items: Vec<PendingItem>,
    pub slots: Vec<PendingSlot>,
    pub reserving: bool,
}

impl PendingLevel {
    pub fn push_class_o1(&mut self, id: usize) {
        if !self.reserving {
            self.items.push(PendingItem::Class(id));
        }
    }

    pub fn reserve_slot_o1(&mut self, exits: Vec<usize>) -> usize {
        let slot_id = self.slots.len();
        self.slots.push(PendingSlot::Unforced { exits });
        self.items.push(PendingItem::Slot(slot_id));
        slot_id
    }

    pub fn fill_slot_ol(&mut self, slot_id: usize, all_ids: Vec<usize>, mode: PendingMode) {
        match mode {
            PendingMode::SlotsM63 => {
                self.slots[slot_id] = PendingSlot::Forced(all_ids);
            }
            PendingMode::BrokenAppendAtForce => {
                let prev_exits = match &self.slots[slot_id] {
                    PendingSlot::Unforced { exits } => exits.clone(),
                    PendingSlot::Forced(v) => v.clone(),
                };
                for id in all_ids {
                    if !prev_exits.contains(&id) {
                        self.items.push(PendingItem::Class(id));
                    }
                }
            }
        }
    }

    pub fn flatten(&self) -> Vec<usize> {
        let mut out = Vec::new();
        for item in &self.items {
            match *item {
                PendingItem::Class(id) => out.push(id),
                PendingItem::Slot(slot_id) => match &self.slots[slot_id] {
                    PendingSlot::Unforced { exits } => out.extend(exits.iter().copied()),
                    PendingSlot::Forced(ids) => out.extend(ids.iter().copied()),
                },
            }
        }
        out
    }
}

/// Template for an exposed `f1` need-hit key on a callee parameter or exit variable.
#[derive(Clone, Debug)]
pub struct ExposedTemplate {
    pub on_var: Arc<str>,
    pub kind: NeedKind,
    pub gives: bool,
}

/// O(1)-composable admission summary cached per callee `Sig`.
#[derive(Clone, Debug)]
pub struct CalleeSummary {
    /// Arrow parameter variables of `sig` mentioned in `sig.needs`.
    pub used_param_vars: Vec<Arc<str>>,
    /// Arrow parameter variables of `sig` appearing as `.on` of at least one leaf need.
    pub on_param_vars: Vec<Arc<str>>,
    /// Exit offsets `0..total_results` appearing as `.on` of at least one leaf need (exact `#19`).
    pub on_exit_offsets: Vec<usize>,
    /// Connected groups of visible (`used_param_vars` + exit vars) variables tied by needs
    /// (`unfixed_args`).
    pub var_ties: Vec<Vec<Arc<str>>>,
    /// First result class ID `k0` when results are consecutive `[k0 .. k0 + total_results)`.
    pub first_result_id: Option<usize>,
    /// Explicit result variables when `#26` is dropped in a negative control.
    pub explicit_result_vars: Option<Vec<Arc<str>>>,
    pub total_needs: usize,
    pub total_results: usize,
    /// Offsets `0..total_results` that appear in `sig.arrows`.
    pub exit_offsets: Vec<usize>,
    pub held_free: usize,
    pub held_names: BTreeSet<Arc<str>>,
    pub held_outer: BTreeSet<Arc<str>>,
    /// Whether a function held in the needs, outside functions, holds a variable not its own
    /// (E: [`Sig::holds_only_own_variables`] false on it); see `FwdNeed::held_foreign_fn` in
    /// zedc-types.
    /// Test: r10_tests.rs `r10_function_held_in_a_forward_block_counts_for_own_variables`.
    pub held_foreign_fn: bool,
    /// Whether a function held in the needs, outside functions, is not closed within the
    /// callee (`Sig::closed_within(&callee.own)` false; `tys_hold_only_fns_closed_within`);
    /// see `FwdNeed::held_open_fn` in zedc-types.
    /// Test: r10_tests.rs
    /// `r10_chain_of_maps_by_a_function_returning_a_lambda_decodes_no_link`.
    pub held_open_fn: bool,
    pub held_classes: BTreeSet<Arc<str>>,
    /// Every variable the needs mention, at any depth, as their decode may write it apart from
    /// an internal result of `[first_result_id, first_result_id + total_results)`: the
    /// variables of the leaf needs (functions held in them entered), of each forward's `sigma`,
    /// `exits` and `on_vars`, the held names, and the explicit result variables. `#12` admits
    /// a call whose `defer` meets none of them nor an internal result (the lemma there).
    pub mentioned: HashSet<Arc<str>>,
    pub intrinsic_fails: BTreeSet<&'static str>,
    pub exposed_needs: Vec<ExposedTemplate>,
    pub var_steps: Vec<FwdVarStep>,
}

/// Lifecycle state of an admitted forward.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForwardStatus {
    Open,
    Forced,
    KeptInSig,
}

/// An admitted forward held in `Ck::r10`.
#[derive(Clone, Debug)]
pub struct OpenForward {
    pub level: usize,
    pub what_note: Arc<str>,
    pub callee_sig: Arc<Sig>,
    pub summary: Arc<CalleeSummary>,
    pub param_map: Vec<(Arc<str>, Ty)>,
    pub lo: usize,
    pub hi: usize,
    pub exit_ids: Vec<usize>,
    pub seq_lo: usize,
    pub call_span: Span,
    pub pending_slot: usize,
    pub watched_roots: BTreeSet<usize>,
    /// Exact set of watched roots on which this forward has >= 1 deferred need (exact `#19`).
    pub has_any_need_on: HashSet<usize>,
    pub exposed_keys: HashMap<usize, Vec<(NeedKind, bool)>>,
    pub status: ForwardStatus,
}

impl OpenForward {
    pub fn is_consecutive(&self) -> bool {
        self.summary.first_result_id.is_some() && self.hi == self.lo + self.summary.total_results
    }
}

/// Per-`Ck` state for fixed-D.
pub struct R10State {
    pub cfg: R10Config,
    pub stats: R10Stats,
    pub pending_levels: Vec<PendingLevel>,
    pub open_by_level: Vec<Vec<usize>>,
    /// Keyed by `(sig as *const Sig as usize, sig.digest())` to prevent freed-address aliasing.
    pub sig_summaries: HashMap<(usize, u64), Arc<CalleeSummary>>,
    pub forwards: Vec<OpenForward>,
    /// Forwards admitted watching each root, in admission order. A forward that is forced or kept
    /// stays listed until `Ck::r10_force_root` next empties the root's list, and readers skip
    /// it by its status. Removing it at once (`retain`) cost O(w) per closed forward, O(w^2) for w
    /// forwards on one root; left in place, each entry is dropped once, O(1) amortized.
    pub root_watchers: HashMap<usize, Vec<usize>>,
    /// Number of open forwards watching each root. `r10_on_need` returns at once on zero.
    pub open_watchers: HashMap<usize, usize>,
    /// Number of open forwards with a deferred need on each root (`#19`). Scanning the root's
    /// watchers for one cost O(w) per admission, O(w^2) for w calls on one operand.
    pub deferred_open: HashMap<usize, usize>,
    /// Open forwards by root and exposed key (`f1`). Scanning every watcher's keys cost O(w) per
    /// need; a lookup costs O(1) plus the forwards it hits, which are then forced.
    pub key_watchers: HashMap<(usize, (NeedKind, bool)), Vec<usize>>,
    /// Class ranges `lo..hi` of kept forwards, by `lo`. They are disjoint, which the lookup
    /// in `Ck::r10_is_closed_internal` (`range(..=k).next_back()`, one range) needs: a range
    /// nested in another would hide it and give a wrong `false`. Proof: each `lo` is taken by
    /// `reserve_ids_o1(total_results)` (`lo = logical_len; logical_len += count`) in
    /// walk/r10_forward.rs, and `hi = lo + total_results`, so `lo..hi` is exactly the block
    /// reserved. (The negative control `StoreMode::BrokenNoCounterAdvance`, r10_tests.rs,
    /// reserves nothing and may overlap; no check runs in that mode.) `logical_len` never
    /// decreases: `push` adds 1 in sparse mode and `materialize_at` only raises it; the dense
    /// `push`, which sets it to `dense.len()`, does not run here, since mod.rs calls
    /// `enable_sparse()` whenever `uses_sparse()` holds, and `r10_is_closed_internal` returns
    /// `false` before reading this map when it does not. So two reservations never overlap.
    /// A range is inserted only in walk/r10_forward.rs, and only where `lo < hi`. No test
    /// checks this directly. A sorted `Vec` with
    /// `insert` cost O(k) per range kept out of order (an outer forward kept after its inner
    /// ones), O(k^2) in all; the map costs O(log k) per insert and per lookup.
    pub closed_internal_ranges: BTreeMap<usize, usize>,
    pub forcing: bool,
}

impl R10State {
    pub fn new_for_ck() -> Self {
        let cfg = set_config().unwrap_or_default();
        R10State {
            cfg,
            stats: R10Stats::default(),
            pending_levels: vec![PendingLevel::default()],
            open_by_level: vec![Vec::new()],
            sig_summaries: HashMap::new(),
            forwards: Vec::new(),
            root_watchers: HashMap::new(),
            open_watchers: HashMap::new(),
            deferred_open: HashMap::new(),
            key_watchers: HashMap::new(),
            closed_internal_ranges: BTreeMap::new(),
            forcing: false,
        }
    }

    /// Takes open forward `fid` off the per-root counts as it leaves `Open` (forced or kept), in
    /// O(roots it watches). Its entries in `root_watchers` and `key_watchers` stay; readers skip
    /// them by status.
    pub fn close_counts(&mut self, fid: usize) {
        let f = &self.forwards[fid];
        for r in &f.watched_roots {
            if let Some(n) = self.open_watchers.get_mut(r) {
                *n -= 1;
            }
        }
        for r in &f.has_any_need_on {
            if let Some(n) = self.deferred_open.get_mut(r) {
                *n -= 1;
            }
        }
    }

    #[inline]
    pub fn uses_sparse(&self) -> bool {
        self.cfg.store_mode == StoreMode::SparseM62
    }

    pub fn ensure_level(&mut self, level: usize) {
        while self.pending_levels.len() <= level {
            self.pending_levels.push(PendingLevel::default());
        }
        while self.open_by_level.len() <= level {
            self.open_by_level.push(Vec::new());
        }
    }

    pub fn on_class_pushed(&mut self, level: usize, id: usize) {
        self.ensure_level(level);
        self.pending_levels[level].push_class_o1(id);
    }

    #[inline]
    pub fn barrier_skipped(&self, name: &'static str) -> bool {
        self.cfg.skip_barrier == Some(name)
    }
}

// ===========================================================================
// Sparse Class Store (`M62`)
// ===========================================================================

mod store {
    use std::collections::HashMap;
    use std::ops::{Index, IndexMut};

    /// What a layer saved for a class at its first write there: the class and what `overlay`
    /// held for it before (a value and the depth of the layer that wrote it), or `None` when
    /// the class read through to the committed store.
    type Saved<C> = (usize, Option<(C, usize)>);

    /// Sparse class store: dense `Vec` before the first reserved range (and always under the
    /// negative control `StoreMode::BrokenNoCounterAdvance`), O(1) sparse `HashMap` for IDs
    /// above `dense.len()`.
    ///
    /// # Trial layers (row CHECK-uf-no-speculative-writes)
    ///
    /// The committed forest (`dense` and `sparse`) only grows. A tried repair works in a
    /// layer ([`Self::begin_layer`]): while one is open, the first write to a class in the
    /// innermost layer copies the class as that layer sees it into `overlay`, and every read
    /// and write after goes to the copy, so the committed forest is read and never written. A
    /// layer that fails is dropped ([`Self::drop_layer`]) and the classes read as they did
    /// before it; one that holds is merged into the layer around it, or into the committed
    /// forest when it is the outermost ([`Self::commit_layer`]). The author, 2026-11-21:
    /// "Union-find is supposed to be a write-only data structure -- speculative results must
    /// not be written there, especially because Zed is supposed to be highly concurrent."
    ///
    /// What a trial still writes to the committed store: a class it makes ([`Self::push`])
    /// keeps its id, since a type the trial gives back may name it, and the id counter is
    /// never wound back; the class is stored as made (a root of its own, of every value) and
    /// its later writes go to the layer. No class that existed before the trial points to it
    /// after a dropped layer, since a link writes the child's `parent` and that write went to
    /// the layer; so the partition of the classes made before the trial is the one before
    /// it, and each class made in it is a singleton. A class the trial materializes at a
    /// reserved id ([`Self::materialize_at`]) is likewise stored fresh, since R10 keeps the
    /// forward that reserved it forced for good. So every id in `overlay` has a class in the
    /// committed store, and the overlay never decides whether an id is materialized.
    ///
    /// Options weighed, for cost, concurrency (two attempts never see each other's writes)
    /// and determinism (batch and single-file checking agree):
    ///
    /// | option | cost of a find, a union | concurrency | score |
    /// |---|---|---|---|
    /// | overlay per attempt (used) | the forest's, plus one hash lookup per class read while a layer is open, and one copy of a class at its first write in a layer | the committed forest is only read during an attempt, so attempts on separate layers over one forest see only their own writes | 9 |
    /// | persistent union-find, Conchon and Filliâtre 2007 | O(log N) find by rank, plus rerooting: a find on an older version costs the Diff nodes between versions | reads write: rerooting reassigns cells all over the array, and the paper says it is "not thread-safe" | 3 |
    /// | copy the forest per attempt | O(N) per attempt | separate copies | 0 |
    /// | undo log (before) | the forest's, plus one copy per `touch` | an attempt writes the committed forest and undoes it after; a second reader sees the speculative writes | 1 |
    ///
    /// Conchon and Filliâtre, "A persistent union-find data structure", ML Workshop 2007,
    /// doi:10.1145/1292535.1292541, checked 2026-11-20 from the authors' copy
    /// (usr.lmf.cnrs.fr/~jcf/ftp/publis/puf-wml07.pdf, read in full with pdftotext): Sec. 2.2,
    /// persistent arrays by Baker's rerooting, "The reroot operation has a cost proportional
    /// to the number of Diff nodes that must be followed to reach the Arr node", and "if we
    /// manipulate simultaneously several versions of a single persistent array then
    /// efficiency will decrease"; Sec. 6, "it is not thread-safe. Indeed, the assignment in
    /// function union is atomic but assigments in function set are not (function reroot
    /// makes a lot of assigments all over the data structure)". Departure: none, since it is
    /// not used. The layers here are semi-persistent in the paper's sense (only the newest
    /// version is changed, and a version is given up in the order it was made), which is the
    /// use Sec. 5 measures; they need no rerooting because a dropped layer is never read again.
    ///
    /// Cost, proved. Let a layer be open at depth d (0 the outermost). (1) A read of class k
    /// is one test of `overlay.is_empty()` and, when not empty, one hash lookup: O(1) expected.
    /// (2) A write to k: when `overlay[k]` was not made by the innermost layer, the entry of
    /// an outer layer (if any) moves into the innermost layer's record and a clone of the
    /// class as read goes into `overlay`: one clone per class per layer, at its first write
    /// there; every later write in the layer is a lookup. (3) Dropping a layer of r records
    /// puts back r entries, O(r). (4) Committing it into the layer around it costs O(r): each
    /// record either is dropped (the outer layer already holds its own record of k, made
    /// when it first wrote k) or moves into the outer list; into the committed forest, O(r)
    /// writes. So a find costs the forest's bound times O(1) expected (O(log N) by rank, see
    /// [`crate::check::Class`]) and a union O(1) more, with one clone per class per layer;
    /// the undo log cloned a class at every `touch`, at least as often. Test:
    /// `a_dropped_layer_leaves_the_store_as_before` and its siblings in this module, and
    /// `zedc_check`'s `a_failed_trial_leaves_the_class_forest_as_before`; they compare
    /// contents, so they cannot catch a cost bound being missed, which the benches in
    /// COMPLEXITY.md row F236 measure.
    pub(in crate::check) struct Classes<C> {
        dense: Vec<C>,
        sparse: HashMap<usize, C>,
        logical_len: usize,
        sparse_enabled: bool,
        /// The value of each class written in an open layer, with the depth of the layer that
        /// wrote it last. Empty while no layer is open.
        overlay: HashMap<usize, (C, usize)>,
        /// One record per open layer, the outermost first: for each class the layer wrote,
        /// in the order it first wrote it, what `overlay` held for it before (`None` when the
        /// class read through to the committed store).
        layers: Vec<Vec<Saved<C>>>,
        /// How many [`Self::begin_through`] are open: while one is, reads and writes go to the
        /// committed store, past every layer.
        through: usize,
    }

    impl<C> Default for Classes<C> {
        fn default() -> Self {
            Classes {
                dense: Vec::new(),
                sparse: HashMap::new(),
                logical_len: 0,
                sparse_enabled: false,
                overlay: HashMap::new(),
                layers: Vec::new(),
                through: 0,
            }
        }
    }

    impl<C> Classes<C> {
        /// Reads and writes go to the committed store until the matching
        /// [`Self::end_through`], past every open layer: for R10's deferred work (forcing a
        /// forward, making and naming a kept forward's internal classes), which records
        /// what the checker without forwards (E) records when the call is first checked, so
        /// it is no part of the trial that happens to force it and must outlive it. R10 marks
        /// such a forward forced for good (`ForwardStatus::Forced`); a forced forward's needs
        /// dropped with a trial would be lost to every later read. The work reads the
        /// committed classes too, so what it writes depends on no speculative write.
        ///
        /// A class an open layer already holds a copy of does not see a write made through
        /// (its copy is read first); a debug assertion at each write through refuses one.
        /// Why none happens:
        /// a trial's first write to a root is preceded by [`crate::check::Ck::touch`], which
        /// forces the forwards watching it (R10 barrier f6), and a merge forces both roots
        /// before it links them (f3); so a forward is forced before any layer copies its
        /// root. Test: the whole suite, whose builds keep debug assertions on (Cargo.toml
        /// `[profile.dev]`).
        pub fn begin_through(&mut self) {
            self.through += 1;
        }

        /// Ends a [`Self::begin_through`].
        pub fn end_through(&mut self) {
            self.through -= 1;
        }
    }

    impl<C: Clone> Classes<C> {
        /// Opens a layer: the writes until it ends go to it ([`Self`], "Trial layers").
        pub fn begin_layer(&mut self) {
            self.layers.push(Vec::new());
        }

        /// The number of open layers (tests, and `Ck::lower`, which keeps no bound under one).
        pub fn layer_depth(&self) -> usize {
            self.layers.len()
        }

        /// Drops the innermost layer: every class it wrote reads as it did before the layer
        /// began, the last write first undone. O(classes it wrote).
        pub fn drop_layer(&mut self) {
            let record = self.layers.pop().expect("an open layer to drop");
            for (k, before) in record.into_iter().rev() {
                match before {
                    Some(entry) => self.overlay.insert(k, entry),
                    None => self.overlay.remove(&k),
                };
            }
        }

        /// Keeps the innermost layer's writes: merged into the layer around it, or written to
        /// the committed store when it is the outermost. O(classes it wrote). Proof that the
        /// layer around it can still drop them: for each class k the inner layer wrote, the
        /// outer layer must end with a record of what `overlay` held for k before the outer
        /// layer first wrote it. If the inner record's saved entry was made by the outer layer
        /// (depth `d - 1`), the outer layer wrote k before, so its own record already holds
        /// that, and the inner record is dropped; otherwise the outer layer never wrote k, and
        /// the inner record's saved entry is exactly what `overlay` held before the outer
        /// layer, so it moves to the outer list. Either way `overlay[k]` now belongs to the
        /// outer layer.
        pub fn commit_layer(&mut self) {
            let record = self.layers.pop().expect("an open layer to commit");
            let Some(outer) = self.layers.len().checked_sub(1) else {
                for (k, _) in record {
                    let (c, _) = self.overlay.remove(&k).expect("a written class");
                    self.store(k, c);
                }
                debug_assert!(
                    self.overlay.is_empty(),
                    "every overlay entry is the layer's"
                );
                return;
            };
            for (k, before) in record {
                self.overlay.get_mut(&k).expect("a written class").1 = outer;
                if before.as_ref().is_none_or(|(_, d)| *d != outer) {
                    self.layers[outer].push((k, before));
                }
            }
        }

        /// Writes `c` at `k` in the committed store.
        fn store(&mut self, k: usize, c: C) {
            if k < self.dense.len() {
                self.dense[k] = c;
            } else if k == self.dense.len() && self.sparse.is_empty() {
                self.dense.push(c);
            } else {
                self.sparse.insert(k, c);
            }
        }

        /// The class at `k` in the committed store, if it has one.
        #[inline]
        fn committed(&self, k: usize) -> Option<&C> {
            match k < self.dense.len() {
                true => Some(&self.dense[k]),
                false => self.sparse.get(&k),
            }
        }

        /// Makes the innermost layer own an entry of `overlay` for `k`, copied from what it
        /// reads now: (2) of the cost proof at [`Self`]. `c` is the class to store when `k`
        /// has none yet ([`Self::materialize_at`]).
        fn own(&mut self, k: usize, c: Option<C>) {
            let d = self.layers.len() - 1;
            if self.overlay.get(&k).is_some_and(|(_, at)| *at == d) {
                if let Some(c) = c {
                    self.overlay.insert(k, (c, d));
                }
                return;
            }
            let before = self.overlay.remove(&k);
            let now = match c {
                Some(c) => c,
                None => match &before {
                    Some((c, _)) => c.clone(),
                    None => self.committed(k).cloned().unwrap_or_else(|| {
                        panic!(
                            "M62 VIOLATION: premature write of unmaterialized internal class ${k}"
                        )
                    }),
                },
            };
            self.layers[d].push((k, before));
            self.overlay.insert(k, (now, d));
        }
    }

    impl<C> Classes<C> {
        pub fn enable_sparse(&mut self) {
            self.sparse_enabled = true;
        }

        #[inline]
        pub fn len(&self) -> usize {
            if self.sparse_enabled {
                self.logical_len
            } else {
                self.dense.len()
            }
        }

        #[inline]
        pub fn alloc_count(&self) -> usize {
            self.dense.len() + self.sparse.len()
        }

        #[inline]
        pub fn push(&mut self, c: C) {
            if !self.sparse_enabled {
                self.dense.push(c);
                self.logical_len = self.dense.len();
                return;
            }
            let id = self.logical_len;
            self.logical_len += 1;
            if id == self.dense.len() {
                self.dense.push(c);
            } else {
                self.sparse.insert(id, c);
            }
        }

        #[inline]
        pub fn reserve_ids_o1(&mut self, count: usize) -> usize {
            let lo = self.logical_len;
            self.logical_len += count;
            lo
        }

        #[inline]
        pub fn is_materialized(&self, k: usize) -> bool {
            // The overlay holds only ids the committed store holds ([`Classes::own`]).
            if !self.sparse_enabled {
                return k < self.dense.len();
            }
            k < self.dense.len() || self.sparse.contains_key(&k)
        }

        /// The ids of the classes that have a record, in increasing order. A walk over every
        /// class (`0..len()`) costs the logical length, which D keeps equal to E's (quadratic
        /// on the chains) and would read classes D never made; this costs O(m log m) in the m
        /// classes made (dense ids, then the sorted sparse ids, all above the dense ones). An
        /// open layer adds no id ([`Classes::materialize_at`]).
        pub fn materialized_ids(&self) -> Vec<usize> {
            let mut ids: Vec<usize> = (0..self.dense.len()).collect();
            let mut rest: Vec<usize> = self.sparse.keys().copied().collect();
            rest.sort_unstable();
            ids.extend(rest);
            ids
        }
    }

    impl<C: Clone> Classes<C> {
        /// Stores `c` at the reserved id `id`. A class new to the store goes to the committed
        /// store even in an open layer, as [`Self::push`] does ([`Self`], "Trial layers"): R10
        /// records a forced forward as forced for good (`ForwardStatus::Forced`, mod.rs
        /// `r10_force`) and reads its exit ids without asking whether they were made
        /// (r10_forward.rs), so a materialization dropped with a layer would leave a forward
        /// whose classes are missing. Only an id that already holds a class is written in the
        /// layer. The logical length is raised either way: it counts ids handed out, which are
        /// never handed out twice.
        #[inline]
        pub fn materialize_at(&mut self, id: usize, c: C) {
            if self.through == 0 && !self.layers.is_empty() && self.is_materialized(id) {
                self.own(id, Some(c));
            } else {
                // Only through mode reaches here with a copy in a layer: otherwise a copy means
                // a materialized id, taken by the branch above. Such a write would be hidden by
                // the copy, so it must not happen (the argument at `begin_through`).
                debug_assert!(
                    !self.overlay.contains_key(&id),
                    "a write through to class {id}, which an open layer holds a copy of"
                );
                self.store(id, c);
            }
            if id >= self.logical_len {
                self.logical_len = id + 1;
            }
        }
    }

    impl<C> Index<usize> for Classes<C> {
        type Output = C;
        #[inline]
        fn index(&self, k: usize) -> &C {
            // An open layer's copy first: (1) of the cost proof at `Classes`.
            if self.through == 0
                && !self.overlay.is_empty()
                && let Some((c, _)) = self.overlay.get(&k)
            {
                return c;
            }
            if k < self.dense.len() {
                return &self.dense[k];
            }
            self.sparse.get(&k).unwrap_or_else(|| {
                panic!("M62 VIOLATION: premature read of unmaterialized internal class ${k}")
            })
        }
    }

    impl<C: Clone> IndexMut<usize> for Classes<C> {
        #[inline]
        fn index_mut(&mut self, k: usize) -> &mut C {
            // In an open layer the write goes to the layer's copy, made at the layer's first
            // write to `k`: (2) of the cost proof at `Classes`. The committed store is not
            // written while a layer is open.
            if !self.layers.is_empty() {
                if self.through == 0 {
                    self.own(k, None);
                    return &mut self.overlay.get_mut(&k).expect("owned just now").0;
                }
                debug_assert!(
                    !self.overlay.contains_key(&k),
                    "a write through to class {k}, which an open layer holds a copy of"
                );
            }
            if k < self.dense.len() {
                return &mut self.dense[k];
            }
            self.sparse.get_mut(&k).unwrap_or_else(|| {
                panic!("M62 VIOLATION: premature write of unmaterialized internal class ${k}")
            })
        }
    }

    /// Trial layers (row CHECK-uf-no-speculative-writes): each test compares the committed
    /// store, field by field, before and after.
    #[cfg(test)]
    mod tests {
        use super::Classes;

        type Snapshot = (Vec<i64>, Vec<(usize, i64)>, usize);

        /// The committed store: dense part, sorted sparse part, logical length.
        fn committed(s: &Classes<i64>) -> Snapshot {
            let mut sparse: Vec<(usize, i64)> = s.sparse.iter().map(|(k, v)| (*k, *v)).collect();
            sparse.sort_unstable();
            (s.dense.clone(), sparse, s.logical_len)
        }

        /// Four dense classes 0..4 holding 10, 11, 12, 13, a reserved range 4..8 with 6
        /// materialized (holding 16).
        fn store() -> Classes<i64> {
            let mut s = Classes::default();
            s.enable_sparse();
            for v in 10..14 {
                s.push(v);
            }
            let lo = s.reserve_ids_o1(4);
            s.materialize_at(lo + 2, 16);
            s
        }

        #[test]
        fn a_dropped_layer_leaves_the_store_as_before() {
            let mut s = store();
            let before = committed(&s);
            s.begin_layer();
            s[1] = 100;
            s[6] = 106;
            s[1] += 1;
            assert_eq!(
                (s[1], s[6], s[0]),
                (101, 106, 10),
                "the layer reads its own writes"
            );
            assert_eq!(
                committed(&s),
                before,
                "the committed store is not written in a layer"
            );
            s.drop_layer();
            assert_eq!(committed(&s), before);
            assert_eq!((s[1], s[6]), (11, 16));
            assert!(s.overlay.is_empty());
        }

        #[test]
        fn a_class_made_in_a_dropped_layer_stays_as_made() {
            let mut s = store();
            s.begin_layer();
            s.push(20);
            let id = s.len() - 1;
            s[id] = 21;
            s.materialize_at(5, 15);
            s[5] = 55;
            s.drop_layer();
            assert_eq!(
                (s[id], s[5]),
                (20, 15),
                "made as given, the layer's writes dropped"
            );
            assert!(s.is_materialized(5) && s.is_materialized(id));
            let (dense, sparse, _) = committed(&s);
            assert_eq!(dense, vec![10, 11, 12, 13]);
            assert!(sparse.contains(&(6, 16)));
        }

        #[test]
        fn a_committed_layer_is_written_through() {
            let mut s = store();
            s.begin_layer();
            s[2] = 102;
            s[6] = 106;
            s.commit_layer();
            assert!(s.overlay.is_empty() && s.layer_depth() == 0);
            let (dense, sparse, _) = committed(&s);
            assert_eq!(dense, vec![10, 11, 102, 13]);
            assert_eq!(sparse, vec![(6, 106)]);
        }

        #[test]
        fn an_inner_layer_committed_then_the_outer_dropped_leaves_the_store_as_before() {
            let mut s = store();
            let before = committed(&s);
            s.begin_layer();
            s[0] = 1000;
            s.begin_layer();
            s[0] = 2000;
            s[3] = 2003;
            s.commit_layer();
            assert_eq!((s[0], s[3]), (2000, 2003));
            s.drop_layer();
            assert_eq!(committed(&s), before);
            assert_eq!((s[0], s[3]), (10, 13));
            assert!(s.overlay.is_empty());
        }

        #[test]
        fn an_inner_layer_dropped_then_the_outer_committed_keeps_only_the_outer_writes() {
            let mut s = store();
            s.begin_layer();
            s[0] = 1000;
            s.begin_layer();
            s[0] = 2000;
            s[3] = 2003;
            s.drop_layer();
            assert_eq!(
                (s[0], s[3]),
                (1000, 13),
                "the outer layer's write reads again"
            );
            s.commit_layer();
            assert_eq!(committed(&s).0, vec![1000, 11, 12, 13]);
        }

        #[test]
        fn three_layers_unwind_in_order() {
            let mut s = store();
            let before = committed(&s);
            s.begin_layer();
            s[1] = 1;
            s.begin_layer();
            s[1] = 2;
            s.begin_layer();
            s[1] = 3;
            s[2] = 3;
            s.commit_layer();
            s.commit_layer();
            assert_eq!((s[1], s[2]), (3, 3));
            s.drop_layer();
            assert_eq!(committed(&s), before);
            assert!(s.overlay.is_empty());
        }

        /// Negative control: without a layer a write reaches the committed store, so the
        /// comparisons above can fail.
        #[test]
        fn a_write_outside_a_layer_changes_the_store() {
            let mut s = store();
            let before = committed(&s);
            s[1] = 100;
            assert_ne!(committed(&s), before);
        }
    }
}
