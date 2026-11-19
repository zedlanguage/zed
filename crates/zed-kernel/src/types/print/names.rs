//! The names a printed type makes up: its type variables, `T`, `U`, `V`, `W`, `T5`, …, and the
//! definitions a message lifts out of it, `Part1`, `Part2`, … ([`crate::types::defs`]; DESIGN.md
//! sec:diagnostics, "Types in a message"). Every place that makes up such a name picks it with
//! [`fresh_name`], so all of them follow one rule: a made-up name is the next of its sequence
//! that the program does not bind ([`ProgramNames`]) and that the caller's `taken` does not hold,
//! such as a name the message already writes. The two sequences share no name: a name of the
//! form `[A-Z][0-9]*` is a type variable and names nothing else (QUESTIONS Q23, plan row
//! TYPEVAR-names), so a definition printed as `type T1 = …;`, as before, would not read back.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Which sequence a made-up name comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Names {
    /// A signature's own type variables: `T`, `U`, `V`, `W`, `T5`, `T6`, ….
    Variables,
    /// The definitions of a printed type: `Part1`, `Part2`, ….
    Definitions,
}

/// The letters the variables are named first.
const LETTERS: [&str; 4] = ["T", "U", "V", "W"];

impl Names {
    /// The `n`th name of the sequence, counted from 0: `T` or `Part1` first. From `n = 4` on the
    /// variables are `T{n + 1}`.
    pub fn nth<S: From<&'static str> + From<String>>(self, n: usize) -> S {
        match (self, n) {
            (Names::Variables, 0..4) => LETTERS[n].into(),
            (Names::Variables, _) => format!("T{}", n + 1).into(),
            (Names::Definitions, _) => format!("Part{}", n + 1).into(),
        }
    }
}

/// The names a program binds that a sequence could give: for each, the letter's place, or the
/// number `k - 1` of a name `T{k}` or `Part{k}` (`k` at least 1, written without a leading zero).
enum Place {
    Letter(usize),
    Numbered(usize),
    Part(usize),
}

/// The number `k - 1` of `rest` written as a `k` of at least 1 with no leading zero.
fn number(rest: &str) -> Option<usize> {
    if rest.starts_with('0') || !rest.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let k: usize = rest.parse().ok()?;
    Some(k - 1)
}

fn place(name: &str) -> Option<Place> {
    if let Some(i) = LETTERS.iter().position(|&l| l == name) {
        return Some(Place::Letter(i));
    }
    if let Some(rest) = name.strip_prefix("Part") {
        return number(rest).map(Place::Part);
    }
    number(name.strip_prefix('T')?).map(Place::Numbered)
}

/// For each `n` of `numbered`, the first `m > n` not in it: a run of bound names is stepped over
/// at once. Each run is walked once, from its first, so `O(k)` for `k` numbers.
fn run_ends(numbered: &HashSet<usize>) -> HashMap<usize, usize> {
    let mut ends = HashMap::with_capacity(numbered.len());
    for &n in numbered {
        if n > 0 && numbered.contains(&(n - 1)) {
            continue;
        }
        let mut end = n + 1;
        while numbered.contains(&end) {
            end += 1;
        }
        ends.extend((n..end).map(|k| (k, end)));
    }
    ends
}

/// The names of [`Names`] a program binds, as [`ProgramNames`] holds them.
#[derive(Default, Debug)]
struct Held {
    /// Whether the program binds each of `T`, `U`, `V`, `W`.
    letters: [bool; 4],
    /// For each `n` such that the program binds `T{n + 1}`, the first `m > n` such that it
    /// binds none of `T{n + 1}` to `T{m}`: a run of bound names is stepped over at once.
    ends: HashMap<usize, usize>,
    /// Sorted indices `n >= 4` where the program binds `T{n + 1}`.
    sorted_numbered: Vec<usize>,
    /// Prefix sums of `sorted_numbered`: `prefix_sums[i]` is the sum of `sorted_numbered[..i]`.
    prefix_sums: Vec<u128>,
    /// The same for the names `Part{n + 1}`.
    part_ends: HashMap<usize, usize>,
}

/// Summary of `count` consecutive [`Names::Variables`] picks starting at `start_n`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FreshVarSpanStats {
    /// Value of `n` immediately after picking the `count`th variable.
    pub end_n: usize,
    /// Bitmask (`0..4`) of which of `T, U, V, W` were picked.
    pub letter_mask: u8,
    /// Number of `T{m + 1}` (`m >= 4`) variables picked.
    pub numbered_count: usize,
    /// Sum of `m` (`m >= 4`) over all `T{m + 1}` variables picked.
    pub numbered_index_sum: u128,
}

/// Immutable `O(1)`-cloneable snapshot of [`ProgramNames`] currently active on this thread,
/// stored in compact signatures so post-check `Sig::digest()` and `FwdNeed::decode()` remain
/// identical after `ProgramNames` is dropped.
#[derive(Clone, Debug, Default)]
pub struct HeldVarSnapshot(Arc<Held>);

impl HeldVarSnapshot {
    /// Whether `other` is this same snapshot, not only an equal one: O(1).
    pub fn same(&self, other: &HeldVarSnapshot) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Returns an `O(1)` snapshot of the [`ProgramNames`] currently active on this thread.
pub fn current_held_var_snapshot() -> HeldVarSnapshot {
    HELD.with_borrow(|held| HeldVarSnapshot(held.clone()))
}

thread_local! {
    /// The names of the program being checked on this thread ([`ProgramNames`]).
    static HELD: RefCell<Arc<Held>> = RefCell::default();
}

/// The names a program binds, which no made-up name takes while it is held: a type a message
/// prints is read in the program's scope, where `T` already names the program's own `T`
/// (DESIGN.md sec:diagnostics, "Types in a message"). Dropping it puts back the names held
/// before, so a check started inside another, as of an operator alone, leaves them as it found
/// them.
pub struct ProgramNames(Arc<Held>);

impl ProgramNames {
    /// Holds `names`, the names the program binds, on this thread until it is dropped. Only
    /// those a [`Names`] sequence gives matter, so the table is as large as they are. `O(k)`
    /// for `k` names.
    pub fn hold<'n>(names: impl IntoIterator<Item = &'n str>) -> ProgramNames {
        let mut held = Held::default();
        let (mut numbered, mut parts) = (HashSet::new(), HashSet::new());
        for p in names.into_iter().filter_map(place) {
            match p {
                Place::Letter(i) => held.letters[i] = true,
                Place::Numbered(n) => {
                    numbered.insert(n);
                }
                Place::Part(n) => {
                    parts.insert(n);
                }
            }
        }
        held.ends = run_ends(&numbered);
        let mut sorted: Vec<usize> = numbered.into_iter().filter(|&n| n >= 4).collect();
        sorted.sort_unstable();
        let mut prefix = Vec::with_capacity(sorted.len() + 1);
        prefix.push(0u128);
        for &x in &sorted {
            prefix.push(prefix[prefix.len() - 1] + x as u128);
        }
        held.sorted_numbered = sorted;
        held.prefix_sums = prefix;
        held.part_ends = run_ends(&parts);
        ProgramNames(HELD.replace(Arc::new(held)))
    }
}

impl Drop for ProgramNames {
    fn drop(&mut self) {
        HELD.set(std::mem::take(&mut self.0));
    }
}

/// A skip set of variable names prepared once for many spans ([`fresh_variable_span_stats_indexed`]):
/// whether each of `T`, `U`, `V`, `W` is in it, and the sorted places `m >= 4` of its names
/// `T{m + 1}` with their prefix sums. Names no [`Names::Variables`] pick can give (`x`, `T0`,
/// `T1` to `T4`) are left out, as are places the program-name snapshot it was made against
/// already skips, so no place is subtracted twice. Names the sequence cannot give are never
/// asked of it, so [`SkipIndex::contains`] answers exactly for every name a pick can give.
// Complexity tradeoff (closed-sibling repair, step 1): the naive version, as before, read and
// sorted the whole skip set at every span, O(s log s) per span, so `generalize` naming r runs of
// a signature whose skip set holds s names cost O(r·s log s): 11.3 times the work at 8n for n
// runs against n names (`r10_generalize_runs_against_a_wide_skip_set_scale`). Used: one sort per
// skip set, O(s log s), then O(log(2 + h + s)·(log(2 + h) + log(2 + s))) per span (h program
// names; [`fresh_variable_span_stats_indexed`] binary-searches a count). Given up: the index is
// built against one program-name snapshot, so a span must be asked with that snapshot.
#[derive(Clone, Debug)]
pub struct SkipIndex {
    letters: [bool; 4],
    numbered: Vec<usize>,
    prefix: Vec<u128>,
}

/// The empty index: it skips no name. Its prefix sums hold the one sum of no places, as an
/// index [`SkipIndex::new`] makes does, so a span read against it finds `prefix[0]`.
impl Default for SkipIndex {
    fn default() -> Self {
        SkipIndex {
            letters: [false; 4],
            numbered: Vec::new(),
            prefix: vec![0],
        }
    }
}

impl SkipIndex {
    /// The index of `skip_names` against the snapshot `held`: O(s log s) for s names.
    pub fn new<'a>(skip_names: impl IntoIterator<Item = &'a str>, held: &HeldVarSnapshot) -> Self {
        let held = &*held.0;
        let mut letters = [false; 4];
        let mut numbered = Vec::new();
        for s in skip_names {
            match place(s) {
                Some(Place::Letter(i)) => letters[i] = true,
                Some(Place::Numbered(m)) if m >= 4 && !held.ends.contains_key(&m) => {
                    numbered.push(m);
                }
                _ => {}
            }
        }
        numbered.sort_unstable();
        numbered.dedup();
        let mut prefix = Vec::with_capacity(numbered.len() + 1);
        prefix.push(0u128);
        for &m in &numbered {
            prefix.push(prefix[prefix.len() - 1] + m as u128);
        }
        SkipIndex {
            letters,
            numbered,
            prefix,
        }
    }

    /// Whether the index skips `name`, for a name a [`Names::Variables`] pick not held by the
    /// snapshot can give: O(log s).
    pub fn contains(&self, name: &str) -> bool {
        match place(name) {
            Some(Place::Letter(i)) => self.letters[i],
            Some(Place::Numbered(m)) => self.numbered.binary_search(&m).is_ok(),
            _ => false,
        }
    }
}

/// Advances past `count` fresh [`Names::Variables`] picks starting from `start_n`, skipping
/// `held` and the names of `skip`, which must have been made against `held`: a binary search,
/// over a range of at most h + s places, on the count of names neither skips below a place,
/// each count O(log h + log s), so O(log(2 + h + s)·(log(2 + h) + log(2 + s))) for h held and
/// s skipped names (landing round 3, Claude F2 and Codex).
pub fn fresh_variable_span_stats_indexed(
    start_n: usize,
    count: usize,
    skip: &SkipIndex,
    held: &HeldVarSnapshot,
) -> FreshVarSpanStats {
    if count == 0 {
        return FreshVarSpanStats {
            end_n: start_n,
            letter_mask: 0,
            numbered_count: 0,
            numbered_index_sum: 0,
        };
    }
    let held = &*held.0;
    let mut n = start_n;
    let mut rem = count;
    let mut letter_mask = 0u8;
    while n < 4 && rem > 0 {
        if !held.letters[n] && !skip.letters[n] {
            letter_mask |= 1u8 << n;
            rem -= 1;
        }
        n += 1;
    }
    if rem == 0 {
        return FreshVarSpanStats {
            end_n: n,
            letter_mask,
            numbered_count: 0,
            numbered_index_sum: 0,
        };
    }
    let skip_num = &skip.numbered;
    let p_n = held.sorted_numbered.partition_point(|&x| x < n);
    let s_n = skip_num.partition_point(|&x| x < n);
    let unblocked = |hi: usize| -> usize {
        let p_hi = held.sorted_numbered.partition_point(|&x| x < hi);
        let s_hi = skip_num.partition_point(|&x| x < hi);
        (hi - n) - (p_hi - p_n) - (s_hi - s_n)
    };
    let mut lo = n + rem;
    let mut hi = n + rem + (held.sorted_numbered.len() - p_n) + (skip_num.len() - s_n);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if unblocked(mid) >= rem {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    let p_hi = held.sorted_numbered.partition_point(|&x| x < lo);
    let s_hi = skip_num.partition_point(|&x| x < lo);
    let len = (lo - n) as u128;
    let arith = (n as u128 + lo as u128 - 1) * len / 2;
    let held_sum = if held.prefix_sums.is_empty() {
        0
    } else {
        held.prefix_sums[p_hi] - held.prefix_sums[p_n]
    };
    let skip_sum = skip.prefix[s_hi] - skip.prefix[s_n];
    FreshVarSpanStats {
        end_n: lo,
        letter_mask,
        numbered_count: rem,
        numbered_index_sum: arith - held_sum - skip_sum,
    }
}

/// Like [`fresh_name`], but skipping the captured [`HeldVarSnapshot`] instead of thread-local `HELD`.
pub fn fresh_name_with_held<S>(
    names: Names,
    n: &mut usize,
    held: &HeldVarSnapshot,
    taken: impl Fn(&str) -> bool,
) -> S
where
    S: From<&'static str> + From<String> + std::ops::Deref<Target = str>,
{
    let held = &*held.0;
    loop {
        let ends = match (names, *n) {
            (Names::Variables, 0..4) if held.letters[*n] => {
                *n += 1;
                continue;
            }
            (Names::Variables, 0..4) => None,
            (Names::Variables, _) => Some(&held.ends),
            (Names::Definitions, _) => Some(&held.part_ends),
        };
        if let Some(&end) = ends.and_then(|e| e.get(n)) {
            *n = end;
        }
        let name: S = names.nth(*n);
        *n += 1;
        if !taken(&name) {
            break name;
        }
    }
}

/// The next name of `names` from the `n`th on that the program being checked does not bind
/// ([`ProgramNames`]) and `taken` does not hold, with `n` moved past it. Every place that makes
/// up a name for a printed type picks it here. A run of names the program binds is stepped
/// over at once, so a pick costs `O(1)` beside the names `taken` holds, however many names the
/// program binds.
pub fn fresh_name<S>(names: Names, n: &mut usize, taken: impl Fn(&str) -> bool) -> S
where
    S: From<&'static str> + From<String> + std::ops::Deref<Target = str>,
{
    HELD.with_borrow(|held| {
        loop {
            let ends = match (names, *n) {
                (Names::Variables, 0..4) if held.letters[*n] => {
                    *n += 1;
                    continue;
                }
                (Names::Variables, 0..4) => None,
                (Names::Variables, _) => Some(&held.ends),
                (Names::Definitions, _) => Some(&held.part_ends),
            };
            if let Some(&end) = ends.and_then(|e| e.get(n)) {
                *n = end;
            }
            let name: S = names.nth(*n);
            *n += 1;
            if !taken(&name) {
                break name;
            }
        }
    })
}

/// A run of [`Names::Variables`] names: the `count` picks from `start_n` on that neither `held`
/// nor `skip` takes, as [`fresh_name_with_held`] makes them one by one. A compact signature
/// keeps the names of a block of internal variables as a few runs, not one name each.
#[derive(Clone, Debug)]
pub struct NameRun {
    /// The place the picks start from.
    pub start_n: usize,
    /// How many names the run holds.
    pub count: usize,
    /// The names the picks skip beside `held`.
    pub skip: Arc<SkipIndex>,
    /// The program names the picks skip.
    pub held: HeldVarSnapshot,
}

impl NameRun {
    /// The place just past its last name.
    pub fn end_n(&self) -> usize {
        fresh_variable_span_stats_indexed(self.start_n, self.count, &self.skip, &self.held).end_n
    }

    /// The place of its first name at or after place `p`.
    fn first_at(&self, p: usize) -> usize {
        fresh_variable_span_stats_indexed(p, 1, &self.skip, &self.held).end_n - 1
    }

    /// Its names, in order: O(count).
    pub fn names<S>(&self) -> Vec<S>
    where
        S: From<&'static str> + From<String> + std::ops::Deref<Target = str>,
    {
        let mut n = self.start_n;
        (0..self.count)
            .map(|_| {
                fresh_name_with_held(Names::Variables, &mut n, &self.held, |s| {
                    self.skip.contains(s)
                })
            })
            .collect()
    }
}

/// The place of a name a [`Names::Variables`] pick can give: `T`, `U`, `V`, `W` at 0 to 3 and
/// `T{m + 1}` at `m` from 4 on.
fn var_place(name: &str) -> Option<usize> {
    match place(name)? {
        Place::Letter(i) => Some(i),
        Place::Numbered(m) if m >= 4 => Some(m),
        _ => None,
    }
}

/// Whether the program binds the name at place `p`.
fn held_at(held: &Held, p: usize) -> bool {
    if p < 4 {
        held.letters[p]
    } else {
        held.ends.contains_key(&p)
    }
}

/// How many places in `lo..hi` neither `held` nor `skip` takes (`usize::MAX` for `hi =
/// usize::MAX`): O(log h + log s) by the sorted places of each. `skip` leaves out the places
/// `held` takes ([`SkipIndex::new`]), so no place is counted out twice.
fn names_between(lo: usize, hi: usize, skip: &SkipIndex, held: &HeldVarSnapshot) -> usize {
    if hi == usize::MAX {
        return usize::MAX;
    }
    let held = &*held.0;
    let letters = (lo..hi.min(4))
        .filter(|&p| !held.letters[p] && !skip.letters[p])
        .count();
    let a = lo.max(4);
    if hi <= a {
        return letters;
    }
    let count_in = |v: &[usize]| v.partition_point(|&x| x < hi) - v.partition_point(|&x| x < a);
    letters + (hi - a) - count_in(&held.sorted_numbered) - count_in(&skip.numbered)
}

/// One name to give, or the runs of names to give, as [`rename_apart`] takes and gives them.
#[derive(Clone, Debug)]
pub enum NameItem {
    /// One name.
    Name(Arc<str>),
    /// The names of runs, in order.
    Runs(Vec<NameRun>),
}

/// The names of `items` made apart, in order: each name is kept unless an item before took it,
/// and is otherwise given the next [`Names::Variables`] name from 0 on that no item holds, no
/// name given before is, and the program does not bind ([`ProgramNames`]). This is the rule
/// the checker names the variables of a finished signature by, one name at a time; here a run
/// of names is given as runs of names, kept or fresh.
///
/// The runs must have been made against the program names held now, as every run of one
/// check is: a place is taken out as the program's own by the snapshot held now.
// Complexity tradeoff (closed-sibling repair, step 4): the naive version, as written in
// `finished_with` before, gives one name at a time, so a block of L internal variables kept as
// a few runs is written out in full, O(L) for each signature that holds it, and O(n·L) for n
// functions that each hold the one before. Used: the places items hold and the places given so
// far are each kept as sorted intervals (`BTreeMap`, start to end), merged where they overlap
// or touch, and a run is cut only where it meets an interval of places given before.
//
// Cost of one run, with k intervals in all. Each pass of the loop in `Renamer::run` gives at
// least one run: the place q a pass starts at is a name of the run (`first_at`), so a pass at
// an interval of `given` gives c >= 1 fresh names, and a pass elsewhere gives the kept stretch.
// Since `given` is merged where intervals touch, two passes in a row at intervals of `given`
// have between them only places the run skips or the program binds. So a run with t kept
// stretches and s skipped or bound places in its range makes at most 2t + 1 + s passes, each
// O(log k), and the fresh loop's jumps over intervals of `used` cost O(log k) each, at most
// one per interval of `used` in all, since `n` only grows. The work is then O(log k) times
// the input (V names, and 1 + s per run) plus the runs given. Before `given` was merged, a run
// over names given one at a time met each of them: v names under m such runs gave m·2v runs
// (test `many_runs_over_names_given_one_at_a_time_give_few_runs`). The number of passes h is
// not bounded by the skip sets alone: a run whose range a sibling run took before it meets one
// interval with an empty skip set (test `a_run_is_cut_only_where_it_meets_a_name_given`).
// Bound on the kept stretches: the sum of t over all runs is at most V + 2 times the sum of
// (1 + s). (The bound V + the sum of (1 + s) once written here is false: m - 1 runs over
// [2 + 4i, 4 + 4i) and then one over [0, 4m - 2) keep 2m - 1 stretches with V = 0 and s = 0;
// test `runs_over_runs_keep_up_to_twice_the_runs`.) Proof (landing round 3, Gemini L3-G3;
// Codex reached the same bound by another route). Let U be the union of the intervals of
// `used`, and P the number of intervals of `given` that meet U; P starts at 0 and is never
// negative. (a) A name adds at most 1 to P. (b) A fresh stretch lies outside U, so it makes no
// new interval that meets U; it can only extend one or join two: it adds at most 0. (c) Take a
// run with kept stretches K_1, ..., K_t and s skipped or bound places in its range. K_j adds
// its 1 + s_j pieces (s_j skipped places inside it), each in U, less L_j + R_j, where L_j (R_j)
// is 1 when its first (last) piece joins an interval of `given` that meets U on its left
// (right). For j >= 2, L_j = 0 only when the place just before K_j is skipped or bound and
// outside every kept stretch; for j <= t - 1, R_j = 0 likewise for the place just after it.
// Each such place is counted at most twice, so the run adds at most
// t + s_in - 2(t - 1) + 2 s_out <= 2 - t + 2s to P, that is t + (its change of P) <= 2 + 2s.
// Summing (a), (b), (c) over the whole call with P >= 0 at the end gives the bound. So the
// passes and the jumps are O(V + sum of (1 + s)) in all, each O(log k). Tradeoff: a run with
// many kept stretches costs O(log k) for each, against O(1) for each name in the naive
// version.
//
// Proof that it gives the names the naive version gives:
// (1) No two intervals of `given` overlap, since each insert merges with every interval it
//     overlaps or touches; merging touching intervals adds no place to their union. A kept
//     stretch runs from a name not given to before the next interval of `given` and is cut at
//     its run's skipped places; a fresh stretch runs from `n`, outside `used`, to before the
//     next interval of `used`, and `n` only grows, so fresh stretches lie above every earlier
//     one.
// (2) Every place in an interval of `given` that the program does not bind is a name given:
//     a kept piece holds only its run's names between its cuts, and a fresh stretch holds every
//     name it may take between its ends. So a name is given before exactly when its place lies
//     in an interval of `given` (for a place the program binds, or a name with no place, the
//     set `given_names` is asked instead).
// (3) `used` is built once and only `given` is written after; each fresh pick leaves `n` just
//     past it, so every name given at or above `n` was kept, and a kept name is an item's name,
//     in `used`. Above `n`, then, `used` holds every name given, and the next fresh name is
//     the next place at or above `n` outside `used` that the program does not bind: the fresh
//     loop jumps over each interval of `used` and counts the places between.
// (4) A run's names that lie in one interval of `given` are all given before, by (2), and get
//     the next fresh names in order; its names before the next interval are none of them given
//     before and are kept. No fresh name is one of the run's own names, which lie in `used`.
pub fn rename_apart(items: &[NameItem]) -> Vec<NameItem> {
    let held = current_held_var_snapshot();
    let mut r = Renamer {
        empty: Arc::new(SkipIndex::default()),
        held,
        used: std::collections::BTreeMap::new(),
        given: std::collections::BTreeMap::new(),
        given_names: HashSet::new(),
        n: 0,
    };
    for item in items {
        match item {
            NameItem::Name(s) => {
                if let Some(p) = var_place(s).filter(|&p| !held_at(&r.held.0, p)) {
                    r.use_range(p, p + 1);
                }
            }
            NameItem::Runs(runs) => {
                for run in runs.iter().filter(|run| run.count > 0) {
                    let end = run.end_n();
                    let start = run.first_at(run.start_n);
                    cut_at_skips(start, end, &run.skip, |a, b| r.use_range(a, b));
                }
            }
        }
    }
    items
        .iter()
        .map(|item| match item {
            NameItem::Name(s) => NameItem::Name(r.name(s)),
            NameItem::Runs(runs) => {
                let mut out = Vec::new();
                for run in runs {
                    r.run(run, &mut out);
                }
                NameItem::Runs(out)
            }
        })
        .collect()
}

/// Calls `f` on each stretch of `start..end` between the places `skip` skips: O(1 + s) for
/// the s skipped places in it, found by binary search.
fn cut_at_skips(start: usize, end: usize, skip: &SkipIndex, mut f: impl FnMut(usize, usize)) {
    let letters = (start..end.min(4)).filter(|&p| skip.letters[p]);
    let lo = skip.numbered.partition_point(|&x| x < start.max(4));
    let hi = skip.numbered.partition_point(|&x| x < end);
    let mut at = start;
    for h in letters.chain(skip.numbered[lo..hi].iter().copied()) {
        if at < h {
            f(at, h);
        }
        at = h + 1;
    }
    if at < end {
        f(at, end);
    }
}

/// The state of [`rename_apart`]: the places the items hold, the places given, and the next
/// place a fresh name may take.
struct Renamer {
    empty: Arc<SkipIndex>,
    held: HeldVarSnapshot,
    /// The places the items hold, as disjoint intervals, start to end, merged where they meet;
    /// a place the program binds may lie inside one.
    used: std::collections::BTreeMap<usize, usize>,
    /// The places given, as disjoint intervals; every place in one that the program does not
    /// bind is given.
    given: std::collections::BTreeMap<usize, usize>,
    /// The names given that have no place or whose place the program binds.
    given_names: HashSet<Arc<str>>,
    n: usize,
}

impl Renamer {
    fn use_range(&mut self, a: usize, b: usize) {
        Self::add_range(&mut self.used, a, b);
    }

    /// Adds `a..b` to `map`, merged with every interval it overlaps or touches: O((1 + j) log k)
    /// for the j intervals merged, each of which it removes, so O(log k) amortized per call.
    fn add_range(map: &mut std::collections::BTreeMap<usize, usize>, a: usize, b: usize) {
        let (mut lo, mut hi) = (a, b);
        while let Some((&s, &e)) = map.range(..=hi).next_back() {
            if e < lo {
                break;
            }
            lo = lo.min(s);
            hi = hi.max(e);
            map.remove(&s);
        }
        map.insert(lo, hi);
    }

    /// The end of the interval of `map` that holds place `p`, if one does.
    fn end_at(map: &std::collections::BTreeMap<usize, usize>, p: usize) -> Option<usize> {
        map.range(..=p)
            .next_back()
            .map(|(_, &e)| e)
            .filter(|&e| e > p)
    }

    /// Gives `c` fresh names, as runs pushed on `out`.
    fn fresh(&mut self, mut c: usize, out: &mut Vec<NameRun>) {
        while c > 0 {
            if let Some(e) = Self::end_at(&self.used, self.n) {
                self.n = e;
                continue;
            }
            let u = self
                .used
                .range(self.n..)
                .next()
                .map_or(usize::MAX, |(&s, _)| s);
            let m = c.min(names_between(self.n, u, &self.empty, &self.held));
            if m == 0 {
                self.n = u;
                continue;
            }
            let run = NameRun {
                start_n: self.n,
                count: m,
                skip: self.empty.clone(),
                held: self.held.clone(),
            };
            let end = run.end_n();
            Self::add_range(&mut self.given, run.first_at(self.n), end);
            out.push(run);
            self.n = end;
            c -= m;
        }
    }

    fn name(&mut self, s: &Arc<str>) -> Arc<str> {
        let free = match var_place(s).filter(|&p| !held_at(&self.held.0, p)) {
            Some(p) if Self::end_at(&self.given, p).is_none() => {
                Self::add_range(&mut self.given, p, p + 1);
                true
            }
            Some(_) => false,
            None => self.given_names.insert(s.clone()),
        };
        if free {
            return s.clone();
        }
        let mut out = Vec::with_capacity(1);
        self.fresh(1, &mut out);
        Names::Variables.nth(out[0].end_n() - 1)
    }

    fn run(&mut self, run: &NameRun, out: &mut Vec<NameRun>) {
        let mut rem = run.count;
        if rem == 0 {
            return;
        }
        let mut q = run.first_at(run.start_n);
        loop {
            let c = match Self::end_at(&self.given, q) {
                Some(y) => {
                    let c = rem.min(names_between(q, y, &run.skip, &run.held));
                    self.fresh(c, out);
                    q = y;
                    c
                }
                None => {
                    let t = self.given.range(q..).next().map_or(usize::MAX, |(&s, _)| s);
                    let c = rem.min(names_between(q, t, &run.skip, &run.held));
                    let kept = NameRun {
                        start_n: q,
                        count: c,
                        skip: run.skip.clone(),
                        held: run.held.clone(),
                    };
                    let end = kept.end_n();
                    let given = &mut self.given;
                    cut_at_skips(q, end, &run.skip, |a, b| {
                        Self::add_range(given, a, b);
                    });
                    out.push(kept);
                    q = end;
                    c
                }
            };
            rem -= c;
            if rem == 0 {
                return;
            }
            q = run.first_at(q);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn picks(names: Names, k: usize, taken: impl Fn(&str) -> bool) -> Vec<String> {
        let mut n = 0;
        (0..k).map(|_| fresh_name(names, &mut n, &taken)).collect()
    }

    #[test]
    fn with_nothing_held_the_sequences_are_as_before() {
        assert_eq!(
            picks(Names::Variables, 6, |_| false),
            ["T", "U", "V", "W", "T5", "T6"]
        );
        assert_eq!(
            picks(Names::Definitions, 3, |_| false),
            ["Part1", "Part2", "Part3"]
        );
    }

    #[test]
    fn the_program_names_are_skipped_in_each_sequence() {
        let _names = ProgramNames::hold([
            "T", "V", "T2", "T3", "T5", "T05", "T0", "x", "Part2", "Part3", "Part03", "Part0",
        ]);
        assert_eq!(
            picks(Names::Variables, 4, |_| false),
            ["U", "W", "T6", "T7"]
        );
        // `T2` and `T3` are variables: they do not move the definitions.
        assert_eq!(
            picks(Names::Definitions, 3, |_| false),
            ["Part1", "Part4", "Part5"]
        );
        // A name the caller holds is skipped too: a definition `Part4` the message writes.
        assert_eq!(
            picks(Names::Definitions, 3, |w| w == "Part4"),
            ["Part1", "Part5", "Part6"]
        );
    }

    #[test]
    fn a_hold_inside_another_gives_the_outer_names_back() {
        let _outer = ProgramNames::hold(["Part1"]);
        {
            let _inner = ProgramNames::hold(["Part2"]);
            assert_eq!(picks(Names::Definitions, 2, |_| false), ["Part1", "Part3"]);
        }
        assert_eq!(picks(Names::Definitions, 2, |_| false), ["Part2", "Part3"]);
    }

    /// The names of `items`, each run written out.
    fn written_out(items: &[NameItem]) -> Vec<Vec<String>> {
        (items.iter())
            .map(|item| match item {
                NameItem::Name(s) => vec![s.to_string()],
                NameItem::Runs(runs) => runs.iter().flat_map(|r| r.names::<String>()).collect(),
            })
            .collect()
    }

    /// [`rename_apart`] as the checker did it before, one name at a time.
    fn one_at_a_time(items: &[NameItem]) -> Vec<Vec<String>> {
        let names = written_out(items);
        let used: HashSet<String> = names.iter().flatten().cloned().collect();
        let mut taken: HashSet<String> = HashSet::new();
        let mut n = 0;
        (names.into_iter())
            .map(|item| {
                (item.into_iter())
                    .map(|name| {
                        if taken.insert(name.clone()) {
                            return name;
                        }
                        let name: String = fresh_name(Names::Variables, &mut n, |s| {
                            used.contains(s) || taken.contains(s)
                        });
                        taken.insert(name.clone());
                        name
                    })
                    .collect()
            })
            .collect()
    }

    /// A fixed-seed generator (xorshift64).
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, k: u64) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % k) as usize
        }
    }

    /// A name a pick may give, or one it may not.
    fn some_name(rng: &mut Rng) -> String {
        match rng.below(10) {
            0 => ["a", "T1", "T4", "Part2"][rng.below(4)].to_string(),
            _ => Names::Variables.nth::<String>(rng.below(40)),
        }
    }

    /// Random names and runs, the runs made against the program names held now, given apart
    /// both ways: each name the same.
    #[test]
    fn runs_are_named_apart_as_one_name_at_a_time() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for round in 0..3000 {
            let held: Vec<String> = (0..rng.below(4)).map(|_| some_name(&mut rng)).collect();
            let _program = ProgramNames::hold(held.iter().map(String::as_str));
            let snap = current_held_var_snapshot();
            let items: Vec<NameItem> = (0..1 + rng.below(8))
                .map(|_| {
                    if rng.below(2) == 0 {
                        return NameItem::Name(some_name(&mut rng).into());
                    }
                    let skip: Vec<String> =
                        (0..rng.below(12)).map(|_| some_name(&mut rng)).collect();
                    let skip = Arc::new(SkipIndex::new(skip.iter().map(String::as_str), &snap));
                    let runs = (0..1 + rng.below(3))
                        .map(|_| NameRun {
                            start_n: rng.below(30),
                            count: rng.below(14),
                            skip: skip.clone(),
                            held: snap.clone(),
                        })
                        .collect();
                    NameItem::Runs(runs)
                })
                .collect();
            assert_eq!(
                written_out(&rename_apart(&items)),
                one_at_a_time(&items),
                "round {round}: items {items:?}, program names {held:?}"
            );
        }
    }

    /// A run all of whose names an item before took is given fresh names as one run, which
    /// steps over the names the items hold; a name taken by a run is given the next fresh one.
    #[test]
    fn a_run_is_cut_only_where_it_meets_a_name_given() {
        let snap = current_held_var_snapshot();
        let skip = Arc::new(SkipIndex::default());
        let run = |start_n, count| NameRun {
            start_n,
            count,
            skip: skip.clone(),
            held: snap.clone(),
        };
        let items = [
            NameItem::Runs(vec![run(0, 1000)]),
            NameItem::Runs(vec![run(0, 1000)]),
            NameItem::Name("T501".into()),
            NameItem::Runs(vec![run(2000, 1000)]),
            NameItem::Name("T2501".into()),
        ];
        let out = rename_apart(&items);
        let NameItem::Runs(second) = &out[1] else {
            panic!("runs")
        };
        assert_eq!(second.len(), 1, "{second:?}");
        assert_eq!((second[0].start_n, second[0].count), (1000, 1000));
        assert!(
            matches!(&out[2], NameItem::Name(s) if &**s == "T3001"),
            "{:?}",
            out[2]
        );
        assert_eq!(written_out(&out), one_at_a_time(&items));
    }

    /// `v` names given one at a time at every other place of `0..2v`, then `m` runs over all of
    /// `0..2v`. The first run is kept between the names; every later run meets names given
    /// before across its whole range and is given one fresh run. Each step of a run gives at
    /// least one run, so the runs given bound the work: with the places given kept as touching
    /// intervals, unmerged, each later run met 2v of them, m·2v runs in all.
    #[test]
    fn many_runs_over_names_given_one_at_a_time_give_few_runs() {
        let snap = current_held_var_snapshot();
        let skip = Arc::new(SkipIndex::default());
        let (v, m) = (200, 200);
        let mut items: Vec<NameItem> = (0..v)
            .map(|i| NameItem::Name(Names::Variables.nth::<String>(2 * i).into()))
            .collect();
        items.extend((0..m).map(|_| {
            NameItem::Runs(vec![NameRun {
                start_n: 0,
                count: 2 * v,
                skip: skip.clone(),
                held: snap.clone(),
            }])
        }));
        let out = rename_apart(&items);
        let runs: usize = (out.iter())
            .map(|item| match item {
                NameItem::Name(_) => 0,
                NameItem::Runs(runs) => runs.len(),
            })
            .sum();
        assert!(runs <= 2 * v + 2 * m, "{runs} runs for v = {v}, m = {m}");
        assert_eq!(written_out(&out), one_at_a_time(&items));
    }

    /// Landing review round 3 (Codex L3.Codex-bound, Gemini L3-G3): `m - 1` runs at
    /// `[2 + 4i, 4 + 4i)`, then one run over `[0, 4m - 2)`, with no names and nothing skipped.
    /// The last run keeps the m stretches between the earlier runs, so the runs keep 2m - 1
    /// stretches in all: more than V + Σ(1 + s) = m, which the comment at [`rename_apart`] once
    /// conjectured, and at most V + 2·Σ(1 + s) = 2m, which it proves.
    #[test]
    fn runs_over_runs_keep_up_to_twice_the_runs() {
        let snap = current_held_var_snapshot();
        let skip = Arc::new(SkipIndex::default());
        for m in [2, 3, 10, 100] {
            let run = |start_n, count| NameRun {
                start_n,
                count,
                skip: skip.clone(),
                held: snap.clone(),
            };
            let mut items: Vec<NameItem> = (0..m - 1)
                .map(|i| NameItem::Runs(vec![run(2 + 4 * i, 2)]))
                .collect();
            items.push(NameItem::Runs(vec![run(0, 4 * m - 2)]));
            let out = rename_apart(&items);
            let NameItem::Runs(last) = &out[m - 1] else {
                panic!("runs")
            };
            // The last run's kept stretches start below 4m - 2; its fresh ones at or above.
            let kept = last.iter().filter(|r| r.start_n < 4 * m - 2).count();
            assert_eq!(m - 1 + kept, 2 * m - 1, "m = {m}: {last:?}");
            assert!(m - 1 + kept <= 2 * m, "the proved bound");
            assert_eq!(written_out(&out), one_at_a_time(&items));
        }
    }
}
