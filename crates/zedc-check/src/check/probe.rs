//! Counters for row FAIL-map-chain-step0 AND the sparse class store, M63 pending slots, and
//! Round 10 fixed-D state (`R10State`, `R10Config`, `R10Stats`, `CalleeSummary`, `OpenForward`).
//!
//! Kept as a leaf module (names no item of `check/mod.rs` or `check/walk.rs`) so `zedc-check`
//! has no import cycle (`tests/steps/s_01f_import_graph`).

#![allow(missing_docs)]

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use zedc_syntax::lex::Span;
use zedc_types::ty::{FwdVarStep, NeedKind, Sig, Ty};

#[cfg(not(any(test, feature = "forward-probe")))]
pub(super) use off::Classes;

#[cfg(any(test, feature = "forward-probe"))]
pub(super) use on::Classes;
#[cfg(any(test, feature = "forward-probe"))]
pub use on::last_report;

#[cfg(any(test, feature = "forward-probe"))]
mod hooks;
#[cfg(test)]
mod tests;

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
    pub enabled: bool,
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
    /// Barrier skip control (`"f1"`..`"f8"`, `"N4"`).
    pub skip_barrier: Option<&'static str>,
    /// Admission conditions dropped for negative controls (`"#7'"`, `"#14"`, `"#19"`, `"#27"`, etc.).
    pub drop_conds: HashSet<String>,
}

impl Default for R10Config {
    fn default() -> Self {
        R10Config {
            enabled: true,
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
        }
    }
}

impl R10Config {
    pub fn eager() -> Self {
        R10Config {
            enabled: false,
            ..R10Config::default()
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
// way to turn off D or pick a negative control but `ZED_DISABLE_D`.
#[cfg(any(test, feature = "forward-probe"))]
thread_local! {
    static NEXT_CONFIG: RefCell<Option<R10Config>> = const { RefCell::new(None) };
    static PERSISTENT_CONFIG: RefCell<Option<R10Config>> = const { RefCell::new(None) };
}

thread_local! {
    static LAST_STATS: RefCell<R10Stats> = RefCell::new(R10Stats::default());
}

#[cfg(any(test, feature = "forward-probe"))]
pub fn set_next_config(cfg: R10Config) {
    NEXT_CONFIG.with(|c| *c.borrow_mut() = Some(cfg));
}

/// The configuration a test set for the next check, or for every check on this thread.
#[cfg(any(test, feature = "forward-probe"))]
fn set_config() -> Option<R10Config> {
    NEXT_CONFIG
        .with(|c| c.borrow_mut().take())
        .or_else(|| PERSISTENT_CONFIG.with(|c| c.borrow().clone()))
}

/// None: a production build takes no configuration from code.
#[cfg(not(any(test, feature = "forward-probe")))]
fn set_config() -> Option<R10Config> {
    None
}

#[cfg(any(test, feature = "forward-probe"))]
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
    /// Connected groups of visible (`used_param_vars` + exit vars) variables tied by needs (`unfixed_args`).
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
    pub held_classes: BTreeSet<Arc<str>>,
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
    /// stays listed until [`Ck::r10_force_root`] next empties the root's list, and readers skip
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
    /// Class ranges `lo..hi` of kept forwards, by `lo` (disjoint). A sorted `Vec` with
    /// `insert` cost O(k) per range kept out of order (an outer forward kept after its inner
    /// ones), O(k^2) in all; the map costs O(log k) per insert and per lookup.
    pub closed_internal_ranges: BTreeMap<usize, usize>,
    pub forcing: bool,
}

impl R10State {
    pub fn new_for_ck() -> Self {
        let cfg = set_config().unwrap_or_else(|| {
            #[cfg(any(test, feature = "forward-probe"))]
            {
                if std::env::var_os("ZED_ENABLE_D").is_some() {
                    R10Config::default()
                } else {
                    R10Config::eager()
                }
            }
            #[cfg(not(any(test, feature = "forward-probe")))]
            {
                if std::env::var_os("ZED_DISABLE_D").is_some() {
                    R10Config::eager()
                } else {
                    R10Config::default()
                }
            }
        });
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
        self.cfg.enabled && self.cfg.store_mode == StoreMode::SparseM62
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
        if self.cfg.enabled {
            self.ensure_level(level);
            self.pending_levels[level].push_class_o1(id);
        }
    }

    #[inline]
    pub fn barrier_skipped(&self, name: &'static str) -> bool {
        self.cfg.skip_barrier == Some(name)
    }
}

// ===========================================================================
// Release Sparse Store (when `probe` counters are compiled out)
// ===========================================================================

#[cfg(not(any(test, feature = "forward-probe")))]
mod off {
    use std::collections::HashMap;
    use std::ops::{Index, IndexMut};

    /// Lean sparse class store for production builds: dense `Vec` when eager or before the first
    /// reserved range, O(1) sparse `HashMap` for IDs above `dense.len()`.
    pub(in crate::check) struct Classes<C> {
        dense: Vec<C>,
        sparse: HashMap<usize, C>,
        logical_len: usize,
        sparse_enabled: bool,
    }

    impl<C> Default for Classes<C> {
        fn default() -> Self {
            Classes {
                dense: Vec::new(),
                sparse: HashMap::new(),
                logical_len: 0,
                sparse_enabled: false,
            }
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
        pub fn materialize_at(&mut self, id: usize, c: C) {
            if id < self.dense.len() {
                self.dense[id] = c;
            } else if id == self.dense.len() && self.sparse.is_empty() {
                self.dense.push(c);
            } else {
                self.sparse.insert(id, c);
            }
            if id >= self.logical_len {
                self.logical_len = id + 1;
            }
        }

        #[inline]
        pub fn is_materialized(&self, k: usize) -> bool {
            if !self.sparse_enabled {
                return k < self.dense.len();
            }
            k < self.dense.len() || self.sparse.contains_key(&k)
        }

        /// The ids of the classes that have a record, in increasing order. A walk over every
        /// class (`0..len()`) costs the logical length, which D keeps equal to E's (quadratic
        /// on the chains) and would read classes D never made; this costs O(m log m) in the m
        /// classes made (dense ids, then the sorted sparse ids, all above the dense ones).
        pub fn materialized_ids(&self) -> Vec<usize> {
            let mut ids: Vec<usize> = (0..self.dense.len()).collect();
            let mut rest: Vec<usize> = self.sparse.keys().copied().collect();
            rest.sort_unstable();
            ids.extend(rest);
            ids
        }
    }

    impl<C> Index<usize> for Classes<C> {
        type Output = C;
        #[inline]
        fn index(&self, k: usize) -> &C {
            if k < self.dense.len() {
                return &self.dense[k];
            }
            self.sparse.get(&k).unwrap_or_else(|| {
                panic!("M62 VIOLATION: premature read of unmaterialized internal class ${k}")
            })
        }
    }

    impl<C> IndexMut<usize> for Classes<C> {
        #[inline]
        fn index_mut(&mut self, k: usize) -> &mut C {
            if k < self.dense.len() {
                return &mut self.dense[k];
            }
            self.sparse.get_mut(&k).unwrap_or_else(|| {
                panic!("M62 VIOLATION: premature write of unmaterialized internal class ${k}")
            })
        }
    }
}

// ===========================================================================
// Test / Forward-Probe Store (supports both STEP0 eager probe and SparseM62)
// ===========================================================================

#[cfg(any(test, feature = "forward-probe"))]
mod on {
    use std::cell::RefCell;
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
    use std::io::Write;
    use std::ops::{Index, IndexMut};
    use std::panic::Location;

    thread_local! {
        static LAST: RefCell<String> = const { RefCell::new(String::new()) };
    }

    /// The report of the last `Ck` dropped on this thread.
    pub fn last_report() -> String {
        LAST.with(|l| l.borrow().clone())
    }

    /// What the store reads of a class: its parent, and the fields D says a forward never
    /// writes on a class that existed at the call, each shown as text.
    pub(in crate::check) trait Watched {
        fn parent(&self) -> usize;
        fn scalars(&self) -> Vec<(&'static str, String)>;
    }

    /// The classes, with the counters beside them AND sparse storage for `SparseM62`.
    pub(in crate::check) struct Classes<C> {
        pub(in crate::check::probe) v: Vec<C>,
        pub(in crate::check::probe) sparse: HashMap<usize, C>,
        pub(in crate::check::probe) logical_len: usize,
        pub(in crate::check::probe) sparse_enabled: bool,
        pub(in crate::check::probe) probe: RefCell<Probe>,
    }

    impl<C> Default for Classes<C> {
        fn default() -> Self {
            Classes {
                v: Vec::new(),
                sparse: HashMap::new(),
                logical_len: 0,
                sparse_enabled: false,
                probe: RefCell::default(),
            }
        }
    }

    impl<C> Classes<C> {
        pub fn enable_sparse(&mut self) {
            self.sparse_enabled = true;
        }

        pub fn alloc_count(&self) -> usize {
            self.v.len() + self.sparse.len()
        }

        pub fn reserve_ids_o1(&mut self, count: usize) -> usize {
            let lo = self.logical_len;
            self.logical_len += count;
            lo
        }

        pub fn materialize_at(&mut self, id: usize, c: C) {
            if id < self.v.len() {
                self.v[id] = c;
            } else if id == self.v.len() && self.sparse.is_empty() {
                self.v.push(c);
            } else {
                self.sparse.insert(id, c);
            }
            if id >= self.logical_len {
                self.logical_len = id + 1;
            }
        }

        pub fn is_materialized(&self, k: usize) -> bool {
            if !self.sparse_enabled {
                return k < self.v.len();
            }
            k < self.v.len() || self.sparse.contains_key(&k)
        }

        /// The ids of the classes that have a record, in increasing order (see the copy of
        /// this store without the probe).
        pub fn materialized_ids(&self) -> Vec<usize> {
            let mut ids: Vec<usize> = (0..self.v.len()).collect();
            let mut rest: Vec<usize> = self.sparse.keys().copied().collect();
            rest.sort_unstable();
            ids.extend(rest);
            ids
        }

        /// A named event at class `k`, for each open forward that watches it.
        pub fn event(&mut self, k: usize, what: &'static str) {
            if !self.sparse_enabled {
                self.probe.get_mut().event(k, what);
            }
        }
    }

    impl<C: Watched> Classes<C> {
        pub fn len(&self) -> usize {
            if self.sparse_enabled {
                self.logical_len
            } else {
                self.v.len()
            }
        }

        pub fn push(&mut self, c: C) {
            if !self.sparse_enabled {
                self.v.push(c);
                self.logical_len = self.v.len();
                return;
            }
            let id = self.logical_len;
            self.logical_len += 1;
            if id == self.v.len() {
                self.v.push(c);
            } else {
                self.sparse.insert(id, c);
            }
        }

        /// The root of `k` by the parents, without counting the reads.
        pub(in crate::check::probe) fn raw_find(&self, mut k: usize) -> usize {
            loop {
                let p = if k < self.v.len() {
                    self.v[k].parent()
                } else {
                    self.sparse[&k].parent()
                };
                if p == k {
                    return k;
                }
                k = p;
            }
        }
    }

    impl<C: Watched> Index<usize> for Classes<C> {
        type Output = C;
        #[track_caller]
        fn index(&self, k: usize) -> &C {
            if !self.sparse_enabled {
                self.probe.borrow_mut().hit(k, Location::caller());
                return &self.v[k];
            }
            if k < self.v.len() {
                return &self.v[k];
            }
            self.sparse.get(&k).unwrap_or_else(|| {
                let loc = Location::caller();
                panic!(
                    "M62 VIOLATION: premature read of unmaterialized internal class ${k} at {}:{}",
                    loc.file(),
                    loc.line()
                )
            })
        }
    }

    impl<C: Watched> IndexMut<usize> for Classes<C> {
        #[track_caller]
        fn index_mut(&mut self, k: usize) -> &mut C {
            if !self.sparse_enabled {
                let p = self.probe.get_mut();
                p.hit(k, Location::caller());
                if p.recording > 0 && k < p.rec_lo && !p.snaps.contains_key(&k) {
                    p.snaps.insert(k, self.v[k].scalars());
                }
                return &mut self.v[k];
            }
            if k < self.v.len() {
                return &mut self.v[k];
            }
            self.sparse.get_mut(&k).unwrap_or_else(|| {
                let loc = Location::caller();
                panic!(
                    "M62 VIOLATION: premature write of unmaterialized internal class ${k} at {}:{}",
                    loc.file(),
                    loc.line()
                )
            })
        }
    }

    impl<C> Drop for Classes<C> {
        fn drop(&mut self) {
            if self.sparse_enabled {
                return;
            }
            let text = self.probe.get_mut().report();
            if let Ok(path) = std::env::var("ZED_FORWARD_PROBE") {
                let who = std::thread::current().name().unwrap_or("-").to_string();
                let mut out = String::new();
                for line in text.lines() {
                    out.push_str(&format!("{who}\t{line}\n"));
                }
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

    pub(in crate::check::probe) type Site = (char, &'static str, u32);

    pub(in crate::check::probe) struct Fwd {
        pub call: String,
        pub level: usize,
        pub size: usize,
        pub lo: usize,
        pub hi: usize,
        pub keys: HashMap<usize, HashSet<u64>>,
        pub watched: BTreeSet<usize>,
        pub sites: Vec<Site>,
        pub seen: HashSet<Site>,
        pub end: Option<&'static str>,
    }

    #[derive(Default)]
    pub(in crate::check::probe) struct Probe {
        pub recording: usize,
        pub rec_lo: usize,
        pub snaps: HashMap<usize, Vec<(&'static str, String)>>,
        pub keys: Vec<(usize, u64)>,
        pub fwds: Vec<Fwd>,
        pub internal: HashMap<usize, Vec<usize>>,
        pub roots: HashMap<usize, Vec<usize>>,
        pub admit: BTreeMap<String, u64>,
        pub scalar: BTreeMap<&'static str, u64>,
        pub same_use: u64,
        pub errors: u64,
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

        pub fn add(&mut self, f: usize, site: Site) {
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
                let tag = match tag == 'W' && self.fwds[f].keys.contains_key(&k) {
                    true => 'R',
                    false => tag,
                };
                self.add(f, (tag, file, at.line()));
            }
        }

        pub fn event(&mut self, k: usize, what: &'static str) {
            if self.recording > 0 {
                return;
            }
            for (_, f) in self.watchers(k) {
                self.add(f, ('E', what, 0));
            }
        }

        fn report(&mut self) -> String {
            let mut s = String::new();
            let admit: Vec<String> = (self.admit.iter())
                .map(|(k, n)| format!("{k}={n}"))
                .collect();
            s.push_str(&format!("A {}\n", admit.join(" ")));
            let scalar: Vec<String> = (self.scalar.iter())
                .map(|(k, n)| format!("{k}={n}"))
                .collect();
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
}
