//! The exact bounds of a threshold-implication component (DESIGN.md sec:domains, item (2) of
//! the tests that hold disjunctions): every part is `x + k*w <= a || y - m*w >= b`, an upper
//! bound on one name or a lower bound on another, `w` one name for the whole component (the
//! *hub*), and every base atom on a name other than the hub has one of the same two shapes.
//!
//! Fix the hub at `c`. A part then reads "if `x >= a - k*c + 1` then `y >= b + m*c`", and two
//! values of the names that both pass give two more that pass when each name takes the smaller
//! of its two values, or each the larger. So the values that pass have a least member, found by
//! raising lower bounds along the parts, and a greatest, found by lowering upper bounds along
//! the parts read backward, and these are the exact bounds of every name. With every `k` and
//! `m` at least 0, raising `c` only raises the least member and lowers the greatest, so the
//! hub's values that pass are its least value `p` up to some `c*`, found by a binary search,
//! and every other name's bounds are those at `p`; with every `k` and `m` at most 0 the same
//! holds with the ends swapped, and with both signs a hub of two values is solved at each value.
//!
//! A hub value that is unbounded is handled as a value past every constant: the propagation
//! then compares terms `s*T + k` with `T` above every integer, so the bounds at an unbounded
//! end are the limits of the bounds there.
//!
//! Proof of the claims above, step by step at the code that relies on each: why the least and
//! greatest members exist and the propagation finds them, at `members`; why a run at an
//! unbounded end gives the limit, at `At`; why the hub's values that pass are `p..=c*` and
//! the names' bounds are those at `p`, and why the searches end, at `rising`; the mirror at
//! [`solve`]; the join at `mixed`. The smaller-of-two step, checked: for two points `s` and
//! `t` that pass and `u` their componentwise minimum, `u_x` is `s_x` or `t_x`, so it is one of
//! `x`'s values; `x <= U` holds at `u` because `u_x <= s_x`; `y >= L` holds because both
//! `s_y` and `t_y` are at least `L`; and a part `x <= U || y >= L` holds because either both
//! `s_y, t_y >= L`, or one of them, say `s_y`, is below `L`, so `s_x <= U` and `u_x <= U`. The
//! maximum is the same with the arms' roles swapped. `members` does not use this step; it
//! proves directly that its result is the least point.
//!
//! Tests: `l01_39_scope_relations::xst::threshold` compares [`solve`] with enumeration on
//! 5,000 random components per sign case (`components_of_*_equal_enumeration`,
//! `components_with_both_signs_and_a_hub_of_two_values_equal_enumeration`); they cannot catch
//! a fault that needs names of more than 6 values, a hub of more than 4 values, more than 5
//! parts or a coefficient outside `-2..=2`, or a fault at an unbounded end, which only the
//! two hand-built tests `an_unbounded_hub_is_searched_by_doubling` and
//! `an_unbounded_hub_below_is_searched_by_doubling` reach.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use zedc_int::int::{Int, Num};
use zedc_lattice::interval::{End, IntervalSet};
use zedc_presburger::presburger::{Atom, Formula, Lin, Rel};

/// `x + k*w <= a`: an upper bound on name `x` that the hub moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Upper {
    /// The name, an index into [`System::names`].
    pub x: usize,
    /// The hub's coefficient.
    pub k: Int,
    /// The constant.
    pub a: Int,
}

/// `y - m*w >= b`: a lower bound on name `y` that the hub moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lower {
    /// The name, an index into [`System::names`].
    pub y: usize,
    /// The hub's coefficient, negated.
    pub m: Int,
    /// The constant.
    pub b: Int,
}

/// A component: each name's values, the hub's, and the atoms.
#[derive(Clone, Debug)]
pub struct System {
    /// The values of each name other than the hub.
    pub names: Vec<IntervalSet>,
    /// The values of the hub.
    pub hub: IntervalSet,
    /// The parts, each `upper || lower` with the two on different names.
    pub parts: Vec<(Upper, Lower)>,
    /// The base atoms that are upper bounds.
    pub uppers: Vec<Upper>,
    /// The base atoms that are lower bounds.
    pub lowers: Vec<Lower>,
}

/// What [`solve`] finds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    /// No values pass.
    Empty,
    /// The least and greatest value of each name that pass, and the hub's values that pass.
    Bounds {
        /// Each name's least and greatest value.
        names: Vec<(End, End)>,
        /// The hub's values.
        hub: IntervalSet,
        /// Whether every value of each name's own values between its least and greatest is
        /// taken by some point that passes, so that those values, met with `names`, are the
        /// exact values of the name that pass. `false` when that is not shown: a value
        /// between the ends may then pass or not ([`solve`], `filled`).
        filled: bool,
    },
    /// The hub has three or more values and the coefficients have both signs: each value is
    /// solved exactly, but the values can be many (plan row S4-hub-mixed).
    MixedHub,
}

/// A value of the propagation: `s*T + k`, `T` above every integer, or an infinity. `s` is 0
/// when the hub has a value; it is not 0 only at an unbounded end of the hub. The derived order
/// is the order of the values.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Val {
    NegInf,
    Fin(Int, Int),
    PosInf,
}

/// Where the hub is: at a value, or past every integer below or above.
///
/// Why a run of [`members`] at `Above` is the limit of its runs at `Value(c)` as `c` grows (and
/// `Below` as `c` falls, with `c = -T`). Every value the run makes is `a + k*c` from
/// [`At::plus`], an end of a name's values, or a value [`ceil`] or [`floor`] passes through, so
/// each is `s*c + k` with `s` a coefficient of the component or 0; the run only compares such
/// values with each other and with the ends of the names' finitely many pieces. Two affine
/// functions of `c` compare the same way for all `c` past the point where they cross, and that
/// way is the order of `(s, k)` pairs, which is the derived order of [`Val`] (`s` first: for
/// `T` above every integer, `s*T + k < s'*T + k'` exactly when `s < s'`, or `s = s'` and
/// `k < k'`). [`ceil`] at `s > 0` gives the value itself when the name's values are unbounded
/// above (for large `c` the last piece holds it) and nothing otherwise (it is past the greatest
/// value); at `s < 0` the least finite end, or the value itself when the values are unbounded
/// below; [`floor`] the mirror. So past the largest of the finitely many crossing points, the
/// run at `Value(c)` takes every branch the symbolic run takes, and its results are the symbolic
/// ones with `T = c`: `None` at once, or `s*c + k` at every name, whose limit is `k` for
/// `s = 0` and the infinity of the sign of `s` otherwise, which [`end`] gives.
#[derive(Clone, Copy, Debug)]
enum At<'a> {
    Value(&'a Int),
    Below,
    Above,
}

impl At<'_> {
    /// `a + k*c` at this hub value.
    fn plus(&self, a: &Int, k: &Int) -> Val {
        match self {
            At::Value(c) => Val::Fin(Int::ZERO, a + &(k * *c)),
            At::Above => Val::Fin(k.clone(), a.clone()),
            At::Below => Val::Fin(-k, a.clone()),
        }
    }
}

fn int(n: &Num) -> Int {
    Int::from(n)
}

/// The least member of `d` at or above `v`; `None` when there is none.
fn ceil(d: &IntervalSet, v: &Val) -> Option<Val> {
    match v {
        Val::NegInf => Some(match d.first()? {
            (End::Fin(lo), _) => Val::Fin(Int::ZERO, int(lo)),
            _ => Val::NegInf,
        }),
        Val::PosInf => None,
        Val::Fin(s, k) => match s.cmp(&Int::ZERO) {
            Ordering::Greater => match d.last()? {
                (_, End::PosInf) => Some(v.clone()),
                _ => None,
            },
            Ordering::Less => match d.first()? {
                (End::Fin(lo), _) => Some(Val::Fin(Int::ZERO, int(lo))),
                _ => Some(v.clone()),
            },
            Ordering::Equal => {
                let x = End::Fin(Num::from(k));
                // The first piece whose upper end is at or above `x`.
                let (lo, _) = d.piece_at_or_above(&x)?;
                Some(if *lo <= x {
                    v.clone()
                } else {
                    match lo {
                        End::Fin(lo) => Val::Fin(Int::ZERO, int(lo)),
                        _ => unreachable!("a piece after a finite end starts finite"),
                    }
                })
            }
        },
    }
}

/// The greatest member of `d` at or below `v`; `None` when there is none. [`ceil`] with the
/// order reversed, case for case: `+inf` gives the last piece's upper end; `-inf` nothing; a
/// value past every integer above (`s > 0`) the last piece's finite upper end, or itself when
/// `d` is unbounded above; one below every integer (`s < 0`) itself when `d` is unbounded
/// below, else nothing; a finite value itself when a piece holds it, else the upper end of the
/// nearest piece below it.
///
/// Complexity tradeoff: naive version, `ceil(&d.neg(), &-v)` negated back, O(P) for P pieces
/// because `IntervalSet::neg` builds the whole negated set; [`members`] calls this once per base
/// upper bound and once per backward firing, so N atoms on a name of P pieces cost O(N * P)
/// (PROOF audit proofdoc4b, entry 37a8466a1). Used: the O(log P) lookups `last`, `first` and
/// `piece_at_or_below`. Test: `threshold::tests::bench::
/// many_upper_bounds_on_a_name_of_many_pieces_cost_near_linear_time` (cost); the enumeration
/// corpora of `l01_39_scope_relations::xst::threshold` check the answers on bounded sets with
/// holes (the case `s = 0`); the other cases rest on the case-for-case reading against
/// [`ceil`] above, as no test is known to reach them.
fn floor(d: &IntervalSet, v: &Val) -> Option<Val> {
    match v {
        Val::PosInf => Some(match d.last()? {
            (_, End::Fin(hi)) => Val::Fin(Int::ZERO, int(hi)),
            _ => Val::PosInf,
        }),
        Val::NegInf => None,
        Val::Fin(s, k) => match s.cmp(&Int::ZERO) {
            Ordering::Less => match d.first()? {
                (End::NegInf, _) => Some(v.clone()),
                _ => None,
            },
            Ordering::Greater => match d.last()? {
                (_, End::Fin(hi)) => Some(Val::Fin(Int::ZERO, int(hi))),
                _ => Some(v.clone()),
            },
            Ordering::Equal => {
                let x = End::Fin(Num::from(k));
                // The last piece whose lower end is at or below `x`.
                let (_, hi) = d.piece_at_or_below(&x)?;
                Some(if *hi >= x {
                    v.clone()
                } else {
                    match hi {
                        End::Fin(hi) => Val::Fin(Int::ZERO, int(hi)),
                        _ => unreachable!("a piece before a finite end ends finite"),
                    }
                })
            }
        },
    }
}

/// The least or greatest end of `d` as a value; `None` when `d` is empty.
fn end_of(d: &IntervalSet, least: bool) -> Option<Val> {
    let (lo, hi) = d.bounds()?;
    Some(match if least { lo } else { hi } {
        End::NegInf => Val::NegInf,
        End::PosInf => Val::PosInf,
        End::Fin(n) => Val::Fin(Int::ZERO, int(n)),
    })
}

/// The least and the greatest member of the values that pass with the hub at `at`, or `None`
/// when no value passes there. In time O(N log N) for N atoms: each name's parts are sorted by
/// threshold, and each part fires once in each direction.
///
/// Proof, with the hub at a value `c` (an unbounded end is the limit of these runs, see
/// [`At`]). Let S be the points, one value per name, that lie in each name's values and pass
/// every atom at `c`.
/// (a) Every point of S is at or above `lo` at every step: `lo` starts at each name's least
///   value; a base `y >= r` sets `lo[y]` to the least member of `y`'s values at or above
///   `max(lo[y], r)`, which every point of S has or exceeds; a part `x <= t - 1 || y >= r`
///   fires only when `t <= lo[x]`, so every point of S fails its upper arm and so has
///   `y >= r`, and `lo[y]` rises to the least member at or above `r`. A `None` from [`ceil`]
///   means `y` has no value at or above a bound every point of S needs, so S is empty.
/// (b) When the forward loop ends, every part with `t <= lo[x]` has `lo[y] >= r`: `next[x]`
///   passes a part only after firing it, which leaves `lo[y] >= r`, and `lo` only rises after;
///   each rise of `lo[x]` pushes `x` again, so after the last rise of `lo[x]` the loop scans
///   `fire[x]`, sorted by `t`, past every `t <= lo[x]`. The work list starts with every name.
/// (c) `hi`, after the base upper bounds and before the backward loop, is each name's greatest
///   value under its base upper bounds; [`floor`] giving `None` there means no value of `x`
///   passes them, so S is empty. If some `lo[x] > hi[x]`, every point of S would have a value
///   above every value of `x` that passes `x`'s base upper bounds, so S is empty. Otherwise
///   the point `lo` is in S: each `lo[x]` is one of `x`'s values (from [`ceil`] or
///   [`end_of`]), at most `hi[x]` so under every base upper bound, and at or above every base
///   lower bound by the first loop; a part holds by its upper arm when `t > lo[x]`, and by (b)
///   when `t <= lo[x]`. A name left at `-inf` (its values unbounded below and nothing raised
///   it) is taken at any value of it below every constant at `c`: it then passes every upper
///   arm on it, it has no base lower bound (that would have made `lo` finite), and a part
///   whose lower arm is on it either fired, which would have made `lo` finite, or holds by its
///   upper arm. So S is not empty and `lo` is its componentwise infimum, attained where
///   finite.
/// (d) The backward loop is (a) to (c) with the order reversed: a part read as "`y <= r - 1`
///   forces `x <= s`" fires when `hi[y] < r`, so every point of S is at or below `hi`, and
///   `hi` is in S by the argument of (c) with the arms swapped (its lower bounds hold since
///   `hi >= lo` and `lo` passes them). As S is not empty here, the [`floor`] in that loop
///   cannot give `None`: it would mean no value of `x` lies at or above a point of S at `x`.
/// Cost: the sorts are O(N log N); each part is fired at most once per loop because `next`
/// only advances; a name is pushed once at the start and once per firing that raised it, so
/// O(n + N) pops; each [`ceil`] and [`floor`] is one O(log P) lookup in the name's P pieces.
fn members(sys: &System, at: At<'_>) -> Option<(Vec<Val>, Vec<Val>)> {
    let n = sys.names.len();
    // The least member: raise lower bounds.
    let mut lo: Vec<Val> = Vec::with_capacity(n);
    for d in &sys.names {
        lo.push(end_of(d, true)?);
    }
    for l in &sys.lowers {
        let v = ceil(&sys.names[l.y], &lo[l.y].clone().max(at.plus(&l.b, &l.m)))?;
        lo[l.y] = v;
    }
    // Each part as "if x reaches t then y >= r": by x, sorted by t.
    let mut fire: Vec<Vec<(Val, usize, Val)>> = vec![Vec::new(); n];
    for (up, low) in &sys.parts {
        let t = at.plus(&(&up.a + &Int::ONE), &-&up.k);
        fire[up.x].push((t, low.y, at.plus(&low.b, &low.m)));
    }
    for f in &mut fire {
        f.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    }
    let mut next = vec![0usize; n];
    let mut work: Vec<usize> = (0..n).collect();
    while let Some(x) = work.pop() {
        while let Some((t, y, r)) = fire[x].get(next[x]) {
            if *t > lo[x] {
                break;
            }
            next[x] += 1;
            if *r > lo[*y] {
                lo[*y] = ceil(&sys.names[*y], r)?;
                work.push(*y);
            }
        }
    }
    // The greatest member: lower upper bounds.
    let mut hi: Vec<Val> = Vec::with_capacity(n);
    for d in &sys.names {
        hi.push(end_of(d, false)?);
    }
    for u in &sys.uppers {
        let v = floor(&sys.names[u.x], &hi[u.x].clone().min(at.plus(&u.a, &-&u.k)))?;
        hi[u.x] = v;
    }
    if lo.iter().zip(&hi).any(|(l, h)| l > h) {
        return None;
    }
    // Each part read backward as "if y falls below r then x <= s": by y, sorted by r, the
    // greatest first.
    let mut back: Vec<Vec<(Val, usize, Val)>> = vec![Vec::new(); n];
    for (up, low) in &sys.parts {
        back[low.y].push((at.plus(&low.b, &low.m), up.x, at.plus(&up.a, &-&up.k)));
    }
    for f in &mut back {
        f.sort_unstable_by(|a, b| b.0.cmp(&a.0));
    }
    let mut next = vec![0usize; n];
    let mut work: Vec<usize> = (0..n).collect();
    while let Some(y) = work.pop() {
        while let Some((r, x, s)) = back[y].get(next[y]) {
            if hi[y] >= *r {
                break;
            }
            next[y] += 1;
            if *s < hi[*x] {
                hi[*x] = floor(&sys.names[*x], s)?;
                work.push(*x);
            }
        }
    }
    // The least member passes every atom when it is below every upper bound, so values pass;
    // the greatest is then a member too, and at or above the least.
    debug_assert!(lo.iter().zip(&hi).all(|(l, h)| l <= h));
    Some((lo, hi))
}

/// A value of the propagation as an end: a value past every integer is an infinity.
fn end(v: &Val) -> End {
    match v {
        Val::NegInf => End::NegInf,
        Val::PosInf => End::PosInf,
        Val::Fin(s, k) => match s.cmp(&Int::ZERO) {
            Ordering::Less => End::NegInf,
            Ordering::Greater => End::PosInf,
            Ordering::Equal => End::Fin(Num::from(k)),
        },
    }
}

/// The signs of the hub's coefficients: whether any is above 0, and whether any is below.
fn signs(sys: &System) -> (bool, bool) {
    let ks = sys
        .parts
        .iter()
        .flat_map(|(u, l)| [&u.k, &l.m])
        .chain(sys.uppers.iter().map(|u| &u.k))
        .chain(sys.lowers.iter().map(|l| &l.m));
    let mut out = (false, false);
    for k in ks {
        match k.cmp(&Int::ZERO) {
            Ordering::Greater => out.0 = true,
            Ordering::Less => out.1 = true,
            Ordering::Equal => {}
        }
    }
    out
}

/// `sys` with the hub negated: every `k` and `m` negated and the hub's values too.
fn mirrored(sys: &System) -> System {
    System {
        names: sys.names.clone(),
        hub: sys.hub.neg(),
        parts: sys
            .parts
            .iter()
            .map(|(u, l)| {
                (
                    Upper {
                        k: -&u.k,
                        ..u.clone()
                    },
                    Lower {
                        m: -&l.m,
                        ..l.clone()
                    },
                )
            })
            .collect(),
        uppers: sys
            .uppers
            .iter()
            .map(|u| Upper {
                k: -&u.k,
                ..u.clone()
            })
            .collect(),
        lowers: sys
            .lowers
            .iter()
            .map(|l| Lower {
                m: -&l.m,
                ..l.clone()
            })
            .collect(),
    }
}

/// The exact bounds of every name of `sys`, and the hub's values, that pass every atom.
///
/// In time O(N log N log W) for N atoms, W the width of the hub's values: each propagation is
/// O(N log N), and the binary search for the hub's greatest value that passes makes O(log W)
/// of them.
///
/// Every coefficient at most 0: `mirrored` is the component in `w' = -w`, whose
/// coefficients are at least 0 (`x + k*w = x + (-k)*w'`), so `rising` solves it; the names'
/// bounds are the same, and the hub's values are negated back. A coefficient of 0 counts as
/// neither sign, so a component with all coefficients 0 goes to `rising`, where (1) of its
/// proof holds with equality. The mirror adds O(N + P) for the hub's P pieces
/// (`IntervalSet::neg`), once.
///
/// `filled` (FAIL-preimage-threshold-hull-unrefused): the answer gives each name's least and
/// greatest value only, and the values between them can leave holes, in two ways. (i) A cycle
/// of parts through a name: on `x` in `0..=2` and `z` in `0..=1`, the parts
/// `x <= 0 || z >= 1` and `z <= 0 || x >= 2` read "x >= 1 forces z >= 1, which forces
/// x >= 2", so x = 1 passes nowhere and x takes {0, 2}, where the bounds give `0..=2`.
/// (ii) A hub of two values with both signs, at `mixed`: `x + 1 <= 3w <= x + 2` with w in
/// `1..=2` takes x in {1, 2} at w = 1 and {4} at w = 2, and their join `1..=4` holds 3.
/// `filled` is true when neither can happen, and then the values that pass of each name `x`
/// are exactly `x`'s own values met with `[lo, hi]`. Proof, with no cycle of parts (no
/// sequence of parts each with its lower arm's name the next one's upper arm's name, the last
/// back to the first; `acyclic`). Fix the hub at `c` and take `v`, one of `x`'s values with
/// `lo_x <= v <= hi_x`, `lo` and `hi` the least and greatest members at `c` (`members`).
/// Run the forward loop of `members` again from `lo` with `lo_x` raised to `v` (a member of
/// `x`'s values, at or above `lo_x`). Call the result `q`. (1) Only names reached from `x`
/// along parts are raised (a name is pushed only when a part from a raised name fires), and
/// `x` is not among them, as that would close a cycle; so `q_x = v`. (2) `q <= hi`: `hi` is a
/// point that passes with `hi_x >= v`, so it lies at or above the point the loop starts from,
/// and each firing raises a name to the least member at or above a bound that every point
/// that passes with `x >= v` meets ((a) of `members` for the points with `x >= v`). (3) `q`
/// passes: each value is one of its name's values (from `ceil` or the start); the base
/// upper bounds hold since `q <= hi` and `hi` meets them, and they only grow easier lower
/// down; the base lower bounds hold since `q >= lo`; a part holds by its upper arm when its
/// threshold is above its name's value, and otherwise it fired ((b) of `members`, every name
/// raised being pushed again), so its lower arm holds. So `v` passes at `c`. Over the hub's
/// values: with every coefficient at least 0 the points that pass are those at `p` (`rising`,
/// step (3)), so the claim at `p` is the claim; when the hub has no least value, the values of
/// `x` that pass at `c` grow as `c` falls and each is `x`'s own values met with an interval,
/// so their union is `x`'s own values met with the union of those intervals, an interval whose
/// ends are the limits `rising` gives; the mirror changes neither the names nor the parts; and
/// at `mixed`, each hub value gives such a set, and `filled` there also asks that their union
/// leave no value of `x` between the two intervals. A cycle need not leave a hole, so `false`
/// is "not shown", not "a hole": the caller then projects the parts one by one
/// ([`crate::product`], `project_threshold`). Cost: `acyclic` is O(n + N), below the solve.
/// Tests: `l01_39_scope_relations::xst::threshold`, the corpora (each `filled` answer checked
/// against every value by enumeration) and `a_cycle_of_parts_is_not_filled`;
/// `product::tests::a_threshold_hull_with_a_hole_is_not_kept`.
pub fn solve(sys: &System) -> Answer {
    if sys.hub.is_empty() || sys.names.iter().any(IntervalSet::is_empty) {
        return Answer::Empty;
    }
    let answer = match signs(sys) {
        (true, true) => mixed(sys),
        (false, true) => match rising(&mirrored(sys)) {
            Answer::Bounds { names, hub, filled } => Answer::Bounds {
                names,
                hub: hub.neg(),
                filled,
            },
            a => a,
        },
        _ => rising(sys),
    };
    match answer {
        Answer::Bounds { names, hub, filled } => Answer::Bounds {
            names,
            hub,
            filled: filled && acyclic(sys),
        },
        a => a,
    }
}

/// Whether no cycle of parts runs through the names: the graph with an edge from each part's
/// upper arm's name to its lower arm's name has no cycle. Kahn's algorithm (A. B. Kahn,
/// "Topological sorting of large networks", Commun. ACM 5(11), 558-562, 1962,
/// doi:10.1145/368996.369025): a graph has no cycle exactly when repeatedly removing a node
/// with no edge in removes every node. O(n + N) for n names and N parts.
fn acyclic(sys: &System) -> bool {
    let n = sys.names.len();
    let mut into = vec![0usize; n];
    let mut out: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (up, low) in &sys.parts {
        out[up.x].push(low.y);
        into[low.y] += 1;
    }
    let mut ready: Vec<usize> = (0..n).filter(|&v| into[v] == 0).collect();
    let mut removed = 0;
    while let Some(v) = ready.pop() {
        removed += 1;
        for &w in &out[v] {
            into[w] -= 1;
            if into[w] == 0 {
                ready.push(w);
            }
        }
    }
    removed == n
}

/// Whether some value of `d` lies strictly between the two ranges `a` and `b` and in
/// neither, so that the join of the two ranges holds a value of `d` their union does not.
fn leaves_gap(d: &IntervalSet, a: &(End, End), b: &(End, End)) -> bool {
    let (a, b) = if a.0 <= b.0 { (a, b) } else { (b, a) };
    if a.1 >= b.0 {
        return false;
    }
    let (End::Fin(h), End::Fin(l)) = (&a.1, &b.0) else {
        // An infinite end on the inner side of two ranges that do not meet does not arise;
        // answered "a gap", which only sends the component to the parts.
        return true;
    };
    let above = End::Fin(Num::from(&(&int(h) + &Int::ONE)));
    match d.piece_at_or_above(&above) {
        Some((lo, _)) => lo.clone().max(above) < End::Fin(l.clone()),
        None => false,
    }
}

/// A hub with coefficients of both signs: solved at each value when it has two or fewer.
/// Exact: the points that pass are the union of S(c) over the hub's values `c`, so each name's
/// least value is the least of its least values at each `c` that passes ([`members`]) and its
/// greatest the greatest, and the hub's values that pass are those `c`. The loop that lists
/// the values stops at the third, so it costs O(1) whatever the hub's width. Test:
/// `components_with_both_signs_and_a_hub_of_two_values_equal_enumeration`.
fn mixed(sys: &System) -> Answer {
    let mut values: Vec<Int> = Vec::new();
    for (lo, hi) in sys.hub.pieces() {
        let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
            return Answer::MixedHub;
        };
        let (lo, hi) = (int(lo), int(hi));
        let mut c = lo;
        while c <= hi {
            if values.len() == 2 {
                return Answer::MixedHub;
            }
            values.push(c.clone());
            c = &c + &Int::ONE;
        }
    }
    let mut names: Option<Vec<(End, End)>> = None;
    let mut hub = IntervalSet::empty();
    // Whether no value of a name lies between its ranges at the two hub values (`filled` at
    // [`solve`], case (ii)).
    let mut filled = true;
    for c in &values {
        let Some((lo, hi)) = members(sys, At::Value(c)) else {
            continue;
        };
        let these: Vec<(End, End)> = lo.iter().zip(&hi).map(|(l, h)| (end(l), end(h))).collect();
        names = Some(match names {
            None => these,
            Some(was) => {
                filled &= (sys.names.iter().zip(&was).zip(&these))
                    .all(|((d, a), b)| !leaves_gap(d, a, b));
                was.into_iter()
                    .zip(these)
                    .map(|((l0, h0), (l1, h1))| (l0.min(l1), h0.max(h1)))
                    .collect()
            }
        });
        hub = hub.join(&IntervalSet::point(Num::from(c)));
    }
    match names {
        Some(names) => Answer::Bounds { names, hub, filled },
        None => Answer::Empty,
    }
}

/// Every coefficient at least 0: raising the hub only raises the least member and lowers the
/// greatest, so the hub's values that pass are its least value `p` up to some `c*`.
///
/// Proof. Write S(c) for the points that pass with the hub at the integer `c` (as at
/// [`members`]), over every integer `c`, in the hub's values or not. (1) For `c <= c'`,
/// S(c') is within S(c): with `k, m >= 0`, `x + k*c <= x + k*c' <= a` and
/// `y - m*c >= y - m*c' >= b`, so every atom and arm that holds at `c'` holds at `c`. (2) So
/// the integers `c` with S(c) not empty are all those up to some `c*` (or all, or none), and
/// the hub's values that pass are the hub's values at or below `c*`, the `cut` below. (3) The
/// names' bounds are those over the union of S(c) for the hub's values `c` that pass; by (1)
/// that union is S(p) when `p` is finite, and the least and greatest members at `p` are its
/// bounds by [`members`]. When the hub has no least value, the union is the union of S(c) as
/// `c` falls, which grows, so its bounds are the limits of the bounds at `c`, which the run at
/// `At::Below` gives ([`At`]). (4) The search for `start`: when `members(sys, Below)` passed
/// (else `Empty` above), the run at `Value(c)` passes for every `c` below the crossing points
/// ([`At`]), so doubling `step` downward from `min(q, 0)` reaches such a `c` after O(log D)
/// runs, D the distance from 0 to that point; `start <= q` so `start` is one of the hub's
/// values or below them, and it passes. (5) The search for the top: when `q` is finite, `start`
/// passes and `q` fails, so [`search`] finds `c*` by (2); when the hub is unbounded above and
/// the run at `Above` passes, every large `c` passes ([`At`]) and with (2) every `c` does, so
/// there is no cut; otherwise every large `c` fails, so doubling `step` from `start` ends after
/// O(log D) runs, and [`search`] finds `c*` between `start`, which passes, and `fail`, which
/// does not. `search` asks only values between the two, which by (2) pass on a prefix.
/// Tests: `an_unbounded_hub_is_searched_by_doubling`, `a_wide_finite_hub_is_searched`, and the
/// corpora (see the module header for what they cannot catch).
fn rising(sys: &System) -> Answer {
    let (p, q) = sys
        .hub
        .bounds()
        .map(|(p, q)| (p.clone(), q.clone()))
        .expect("the hub has values");
    let least: Option<Int> = match &p {
        End::Fin(p) => Some(int(p)),
        _ => None,
    };
    let at_p = least.as_ref().map_or(At::Below, At::Value);
    let Some((lo, hi)) = members(sys, at_p) else {
        return Answer::Empty;
    };
    let names: Vec<(End, End)> = lo.iter().zip(&hi).map(|(l, h)| (end(l), end(h))).collect();
    let passes = |c: &Int| members(sys, At::Value(c)).is_some();
    // A value that passes, to search from: `p`, or below the least constant when the hub has
    // no least value, found by doubling downward (each value below one that passes passes).
    // Complexity tradeoff: the search for the hub's greatest value that passes makes O(log W)
    // propagations, W the width of the hub's values (or the distance to the value where the
    // answer stops changing when the hub is unbounded), so the cost is O(N log N log W) and
    // not O(N log N). Why: whether a hub value passes depends on the whole component, and the
    // least member is not a function of the hub that one propagation could carry along.
    // Trigger: a hub whose values that pass end inside a wide interval. Test:
    // `l01_39_scope_relations::xst::threshold::the_hub_search_scales_with_the_digits_of_its_width`.
    // COMPLEXITY.md row S4-ti. A complete solution carries the least member as a piecewise
    // linear function of the hub through one propagation.
    let start: Int = match &p {
        End::Fin(p) => int(p),
        _ => {
            let mut c = match &q {
                End::Fin(q) => int(q).min(Int::ZERO),
                _ => Int::ZERO,
            };
            let mut step = Int::ONE;
            while !passes(&c) {
                c = &c - &step;
                step = &step + &step;
            }
            c
        }
    };
    // The greatest value that passes, by doubling upward when the hub has no greatest value
    // and the values past every integer do not pass, then halving.
    let top: Option<Int> = match &q {
        End::Fin(q) => {
            let q = int(q);
            if passes(&q) {
                Some(q)
            } else {
                Some(search(start, q, passes))
            }
        }
        _ if members(sys, At::Above).is_some() => None,
        _ => {
            let mut step = Int::ONE;
            let mut fail = &start + &step;
            while passes(&fail) {
                step = &step + &step;
                fail = &start + &step;
            }
            Some(search(start, fail, passes))
        }
    };
    let cut = match top {
        Some(t) => IntervalSet::range(End::NegInf, End::Fin(Num::from(&t))),
        None => IntervalSet::top(),
    };
    Answer::Bounds {
        names,
        hub: sys.hub.meet(&cut),
        filled: true,
    }
}

/// The greatest value in `pass..fail` that passes, when `pass` passes and `fail` does not.
fn search(pass: Int, fail: Int, passes: impl Fn(&Int) -> bool) -> Int {
    zed_collections::search::last_true(pass, &fail - &Int::ONE, passes)
}

/// A bound that one atom of a component puts on a name: an upper bound `x + k*w <= a` or a
/// lower bound `y - m*w >= b`, with `k` or `m` 0 when the atom does not mention the hub.
enum Bound {
    Upper(Arc<str>, Int, Int),
    Lower(Arc<str>, Int, Int),
}

/// The term of a constraint `t >= 0` that `f` is, when `f` is one: `t >= 0` itself, or
/// `-t - 1 >= 0` for `!(t >= 0)`.
fn at_least_zero(f: &Formula) -> Option<Lin> {
    let (t, negated) = ge_term(f)?;
    Some(if negated {
        Lin {
            terms: t.terms.iter().map(|(a, k)| (a.clone(), -k)).collect(),
            constant: &-&t.constant - &Int::ONE,
        }
    } else {
        t.clone()
    })
}

/// The term of an inequality, with whether the formula negates it.
fn ge_term(f: &Formula) -> Option<(&Lin, bool)> {
    match f {
        Formula::Con(c) if c.rel == Rel::Ge => Some((&c.lin, false)),
        Formula::Not(n) => match &**n {
            Formula::Con(c) if c.rel == Rel::Ge => Some((&c.lin, true)),
            _ => None,
        },
        _ => None,
    }
}

/// The bound that `t >= 0` puts on a name other than `hub`, its other name being `hub`; `None`
/// when `t` has another shape. A bound on the hub alone is `Err` with the hub's values it keeps.
fn bound(t: &Lin, hub: Option<&Arc<str>>) -> Option<Result<Bound, IntervalSet>> {
    let mut on: Option<(&Arc<str>, &Int)> = None;
    let mut h = Int::ZERO;
    for (a, k) in &t.terms {
        let Atom::Sym(n) = a else {
            return None;
        };
        if Some(n) == hub {
            h = k.clone();
        } else if on.replace((n, k)).is_some() {
            return None;
        }
    }
    let Some((x, kx)) = on else {
        // On the hub alone: `h*w + c >= 0`, `h` 1 or -1.
        let c = Num::from(&t.constant);
        return match h {
            h if h == Int::ONE => Some(Err(IntervalSet::range(
                End::Fin(Num::from(&-&t.constant)),
                End::PosInf,
            ))),
            h if h == -&Int::ONE => Some(Err(IntervalSet::range(End::NegInf, End::Fin(c)))),
            _ => None,
        };
    };
    // `x + h*w + c >= 0` is `x - (-h)*w >= -c`; `-x + h*w + c >= 0` is `x + (-h)*w <= c`.
    if *kx == Int::ONE {
        Some(Ok(Bound::Lower(x.clone(), -&h, -&t.constant)))
    } else if *kx == -&Int::ONE {
        Some(Ok(Bound::Upper(x.clone(), -&h, t.constant.clone())))
    } else {
        None
    }
}

/// A component read from its conjuncts, before the names' values are known.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shape {
    /// The names other than the hub, in the order [`Upper::x`] and [`Lower::y`] index.
    pub names: Vec<Arc<str>>,
    /// The hub, when an atom mentions one.
    pub hub: Option<Arc<str>>,
    /// The hub's values that its own atoms keep.
    hub_values: IntervalSet,
    parts: Vec<(Upper, Lower)>,
    uppers: Vec<Upper>,
    lowers: Vec<Lower>,
}

impl Shape {
    /// The component with each name's values as `values` gives them.
    pub fn system(&self, values: impl Fn(&Arc<str>) -> IntervalSet) -> System {
        System {
            names: self.names.iter().map(&values).collect(),
            hub: match &self.hub {
                Some(w) => values(w).meet(&self.hub_values),
                None => IntervalSet::single(0),
            },
            parts: self.parts.clone(),
            uppers: self.uppers.clone(),
            lowers: self.lowers.clone(),
        }
    }
}

/// The conjuncts `gs` as a threshold-implication component, when they are one: each a
/// constraint (an equality being two) or a disjunction of two, of the shapes `x + k*w <= a` and
/// `y - m*w >= b` with one hub `w`, each disjunction an upper bound on one name and a lower
/// bound on another. In time O(N log N) for N atoms.
pub fn shape(gs: &[Arc<Formula>]) -> Option<Shape> {
    // The hub: the name every atom of two names shares.
    let mut hubs: Option<BTreeSet<Arc<str>>> = None;
    let mut atoms: Vec<(usize, Lin)> = Vec::new();
    let mut ors: Vec<bool> = Vec::new();
    for (i, g) in gs.iter().enumerate() {
        let lins: Vec<Lin> = match &**g {
            Formula::Con(c) if c.rel == Rel::Eq => {
                let neg = Lin {
                    terms: c.lin.terms.iter().map(|(a, k)| (a.clone(), -k)).collect(),
                    constant: -&c.lin.constant,
                };
                vec![c.lin.clone(), neg]
            }
            Formula::Or(cases) if cases.len() == 2 => {
                vec![at_least_zero(&cases[0])?, at_least_zero(&cases[1])?]
            }
            f => vec![at_least_zero(f)?],
        };
        ors.push(matches!(&**g, Formula::Or(_)));
        for t in lins {
            let names: BTreeSet<Arc<str>> = t
                .terms
                .keys()
                .map(|a| match a {
                    Atom::Sym(n) => Some(n.clone()),
                    _ => None,
                })
                .collect::<Option<_>>()?;
            if names.len() > 2 {
                return None;
            }
            if names.len() == 2 {
                hubs = Some(match hubs {
                    None => names,
                    Some(h) => h.intersection(&names).cloned().collect(),
                });
            }
            atoms.push((i, t));
        }
    }
    let candidates: Vec<Option<Arc<str>>> = match hubs {
        None => vec![None],
        Some(h) => h.into_iter().map(Some).collect(),
    };
    candidates
        .into_iter()
        .find_map(|hub| read(&atoms, &ors, hub))
}

/// [`shape`] with the hub `hub`.
fn read(atoms: &[(usize, Lin)], ors: &[bool], hub: Option<Arc<str>>) -> Option<Shape> {
    let mut index: BTreeMap<Arc<str>, usize> = BTreeMap::new();
    let mut names: Vec<Arc<str>> = Vec::new();
    let mut at = |x: &Arc<str>| {
        *index.entry(x.clone()).or_insert_with(|| {
            names.push(x.clone());
            names.len() - 1
        })
    };
    let mut out = Shape {
        names: Vec::new(),
        hub: hub.clone(),
        hub_values: IntervalSet::top(),
        parts: Vec::new(),
        uppers: Vec::new(),
        lowers: Vec::new(),
    };
    let mut i = 0;
    while i < atoms.len() {
        let (g, t) = &atoms[i];
        if ors[*g] {
            let (_, s) = &atoms[i + 1];
            let (Ok(one), Ok(two)) = (bound(t, hub.as_ref())?, bound(s, hub.as_ref())?) else {
                return None;
            };
            let (up, low) = match (one, two) {
                (Bound::Upper(x, k, a), Bound::Lower(y, m, b))
                | (Bound::Lower(y, m, b), Bound::Upper(x, k, a)) => ((x, k, a), (y, m, b)),
                _ => return None,
            };
            if up.0 == low.0 {
                return None;
            }
            out.parts.push((
                Upper {
                    x: at(&up.0),
                    k: up.1,
                    a: up.2,
                },
                Lower {
                    y: at(&low.0),
                    m: low.1,
                    b: low.2,
                },
            ));
            i += 2;
        } else {
            match bound(t, hub.as_ref())? {
                Err(w) => out.hub_values = out.hub_values.meet(&w),
                Ok(Bound::Upper(x, k, a)) => out.uppers.push(Upper { x: at(&x), k, a }),
                Ok(Bound::Lower(y, m, b)) => out.lowers.push(Lower { y: at(&y), m, b }),
            }
            i += 1;
        }
    }
    out.names = names;
    Some(out)
}

/// A unit-slope threshold row, read without building a component or copying its domains.
pub struct LeafRow {
    /// The name of the arm `x + w <= a`.
    pub x: Arc<str>,
    /// The name of the arm `y - w >= b`.
    pub y: Arc<str>,
    /// The name `w` both arms share.
    pub hub: Arc<str>,
    /// The bound `a` of `x + w <= a`.
    pub upper: Int,
    /// The bound `b` of `y - w >= b`.
    pub lower: Int,
}

/// Reads `x + w <= a || y - w >= b`, with three distinct names.
pub fn leaf_row(g: &Formula) -> Option<LeafRow> {
    let Formula::Or(arms) = g else { return None };
    let [a, b] = arms.as_slice() else { return None };
    let ((a, _), (b, _)) = (ge_term(a)?, ge_term(b)?);
    if a.terms.len() != 2 || b.terms.len() != 2 {
        return None;
    }
    let mut common = a.terms.keys().filter(|n| b.terms.contains_key(*n));
    let Atom::Sym(hub) = common.next()? else {
        return None;
    };
    if common.next().is_some() {
        return None;
    }
    let (Ok(a), Ok(b)) = (
        bound(&at_least_zero(&arms[0])?, Some(hub))?,
        bound(&at_least_zero(&arms[1])?, Some(hub))?,
    ) else {
        return None;
    };
    let (x, k, upper, y, m, lower) = match (a, b) {
        (Bound::Upper(x, k, a), Bound::Lower(y, m, b))
        | (Bound::Lower(y, m, b), Bound::Upper(x, k, a)) => (x, k, a, y, m, b),
        _ => return None,
    };
    (k == Int::ONE && m == Int::ONE).then(|| LeafRow {
        x,
        y,
        hub: hub.clone(),
        upper,
        lower,
    })
}

#[cfg(test)]
mod tests {
    mod bench;
}
