//! The two bounds of VERIFY-classed-charge-refusals (b22-eqsrest4, b76c672c7), tested at their
//! corners and against the behavior each replaced: the room of `size` values within which
//! [`shared_cells`] lists a cell's classes (fix A), and the `spare` within which
//! [`cells_cover`] asks a classed piece one value at a time (fix B).

use super::*;

/// `s == 2·t` with `0 <= t <= n`: the cell of `s` at any point is the class `0 mod 2` over
/// `[0, 2n]`, `n + 1` values, and the part has 3 constraints whatever `n` is.
pub(super) fn evens(n: i64) -> Formula {
    Formula::and(vec![
        eq(&[("s", 1), ("t", -2)], 0),
        ge(&[("t", 1)], 0),
        ge(&[("t", -1)], n),
    ])
}

/// [`shared_cells`] on `f` for `s` alone in `h`, at the given `size`: the points it holds at
/// the end, its answer for `s` (if any), and its units.
pub(super) fn shared_for_s(
    f: &Formula,
    h: IntervalSet,
    size: u64,
) -> (usize, Option<IntervalSet>, u64) {
    let s = a("s");
    let want: BTreeMap<&Atom, IntervalSet> = [(&s, h)].into_iter().collect();
    let mut points = Vec::new();
    let mut out = HashMap::new();
    let mut work = Work {
        used: 0,
        limit: u64::MAX,
        solver: SOLVER,
    };
    shared_cells(f, size, want, &mut points, &mut out, &mut work).expect("no limit");
    (points.len(), out.get(&s).cloned(), work.used)
}

/// [`cells_cover`] of `s` in `h` on `f`, with no limit: its answer, its units and the
/// questions it asked.
pub(super) fn cover_s(f: &Formula, h: &IntervalSet) -> (Classed, u64, u64) {
    let mut work = Work {
        used: 0,
        limit: u64::MAX,
        solver: SOLVER,
    };
    let mut points = Vec::new();
    let mut cache = PartCache::default();
    let asked = EXACT_QUESTIONS.get();
    let (set, _) = cells_cover(
        f,
        &a("s"),
        h,
        constraints(f),
        &factors(f),
        &mut points,
        &mut cache,
        &mut work,
    )
    .expect("no limit");
    (set, work.used, EXACT_QUESTIONS.get() - asked)
}

/// `s == m·t` with `0 <= t <= k`: the cell of `s` in `[0, m·k]` is the class `0 mod m`.
pub(super) fn multiples(m: i64, k: i64) -> Formula {
    Formula::and(vec![
        eq(&[("s", 1), ("t", -m)], 0),
        ge(&[("t", 1)], 0),
        ge(&[("t", -1)], k),
    ])
}

/// An attempt to break fix B's bound, "each range taken from a plain set splits at most one
/// gap range": a gap made by cutting a class from a range. `[0, m·k]` less the class `0 mod m`
/// is the `m - 1` classes `1..m mod m` ([`classes::cut`]), each of `k` values, more than
/// `spare` (2) for `k >= 3`. Those pieces never reach the class question: the cell's stride
/// asks its residues (one question, none found) and `outside` drops them all. The answer is the
/// class at every `m` and `k`, with fix B on and off, in at most two questions.
#[test]
fn a_gap_cut_by_a_class_is_dropped_by_its_stride_not_asked_by_piece() {
    for m in [2i64, 3, 16, 128] {
        for k in [1i64, 2, 3, 8] {
            let f = multiples(m, k);
            let h = IntervalSet::of(0, m * k);
            let want = Classed::new(h.clone(), Congruence::new(Num::from(m), Num::ZERO));
            for off in [false, true] {
                SPARE_OFF.set(off);
                let (set, used, asked) = cover_s(&f, &h);
                SPARE_OFF.set(false);
                assert_eq!(set, want, "m {m} k {k} spare off {off}");
                assert!(asked <= 2, "m {m} k {k}: {asked} questions, {used} units");
            }
        }
    }
}

/// Fix A's room at its corner: the class of `s`'s cell, `n + 1` values, is listed at
/// `size = n + 1` and dropped at `size = n`. Listed, the gap of `s` in `[0, 2n]` is the odd
/// values, and its question (`s` in `[1, 1]`) finds no point; dropped, the gap is all of
/// `[0, 2n]` and its question finds one. With [`CLASS_ROOM_OFF`] the class is listed at both.
#[test]
fn a_shared_cell_lists_its_classes_while_their_values_fit_in_size() {
    let n = 10;
    let f = evens(n);
    let h = IntervalSet::of(0, 2 * n);
    let fits = shared_for_s(&f, h.clone(), n as u64 + 1);
    let past = shared_for_s(&f, h.clone(), n as u64);
    CLASS_ROOM_OFF.set(true);
    let unbounded = shared_for_s(&f, h, n as u64);
    CLASS_ROOM_OFF.set(false);
    println!("size n + 1: {fits:?}; size n: {past:?}; size n, no room: {unbounded:?}");
    assert_eq!(
        fits.0, 1,
        "listed: the odd value 1 has no point, nothing found"
    );
    assert_eq!(past.0, 2, "dropped: a point in [0, 2n] found");
    assert_eq!(unbounded.0, 1, "no room: listed as at n + 1");
}

/// Listed or dropped, the answer for `s` is the same: the even values of `[0, 2n]`, at sizes
/// on both sides of the room and with the room off.
#[test]
fn a_shared_cell_listed_or_dropped_gives_one_answer() {
    for n in [1i64, 2, 5, 40, 1000] {
        let f = evens(n);
        let want = Classed::new(
            IntervalSet::of(0, 2 * n),
            Congruence::new(Num::from(2), Num::ZERO),
        );
        for off in [false, true] {
            CLASS_ROOM_OFF.set(off);
            let found = (vec![Ok(IntervalSet::of(0, 2 * n))], vec![]);
            let (got, _) = exact_each(&f, &[a("s")], found, SOLVER).met();
            CLASS_ROOM_OFF.set(false);
            assert_eq!(got.len(), 1);
            assert_eq!(got[0], Ok(want.met()), "n {n}, room off {off}");
        }
    }
}
