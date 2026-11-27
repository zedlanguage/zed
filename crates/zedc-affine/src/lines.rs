//! Lines in the plane: the upper envelope of a set of lines (the convex hull trick) and the
//! floor sum, which counts the integer points under a line. Moved here from their single
//! copies (DRY-affine-crate-2026-11-26, batch 4): the envelope from zedc-presburger's
//! `presburger.rs`, which `extend`'s `hull_of`, `unit_interval` and `UpperHull` called, and the
//! floor sum from zedc-solvers' `twovar`, whose lower envelope `least` now calls
//! [`upper_envelope_by`] too in place of its own loop. The floor sum itself is now
//! zed-numtheory's (FLOORSUM-bits); [`floor_sum`] here takes it on `Int`.

use zed_numtheory::floor_sum_i128;
use zedc_int::int::Int;

/// The upper envelope of `lines`, sorted by slope and within a slope by intercept, with
/// `same_slope` telling whether two have one slope and `not_above(a, b, c)` whether `b`, of a
/// slope between those of `a` and `c`, is nowhere above both: the indices of the lines on it,
/// in order of slope. Of one slope only the last, the highest, can be on it.
///
/// Why `not_above` decides it: line `b` between `a` and `c` (slopes `pa < pb < pc`) is under
/// `max(a, c)` everywhere when at the crossing of `a` and `c` it is under `a`, because `b - a`
/// rises in `x` (`pb > pa`) and `b - c` falls (`pb < pc`): at or left of the crossing `b - a`
/// is at most its value there, at most 0; at or right of it `b - c` is at most its value there,
/// which equals that of `b - a`, as `a = c` there. A line popped is under the envelope of the
/// lines kept and of those still to come, which only rise further to the right, so it never
/// returns.
///
/// Complexity tradeoff: naive version, each line tested against every pair of the others,
/// O(n³) tests. Used: the monotone chain (Andrew, "Another efficient algorithm for convex
/// hulls in two dimensions", IPL 9(5), 1979, doi:10.1016/0020-0190(79)90072-3, read
/// 2026-11-21; sec. 3 builds a point hull, this is its dual on lines) on the sorted lines,
/// each index pushed and popped at most once, O(n) tests after the caller's O(n log n) sort.
/// Tradeoffs: none.
pub fn upper_envelope_by<T>(
    lines: &[T],
    same_slope: impl Fn(&T, &T) -> bool,
    not_above: impl Fn(&T, &T, &T) -> bool,
) -> Vec<usize> {
    let mut hull: Vec<usize> = Vec::new();
    for j in 0..lines.len() {
        let c = &lines[j];
        if lines.get(j + 1).is_some_and(|next| same_slope(next, c)) {
            continue;
        }
        while let [.., a, b] = hull[..] {
            if not_above(&lines[a], &lines[b], c) {
                hull.pop();
            } else {
                break;
            }
        }
        hull.push(j);
    }
    hull
}

/// [`upper_envelope_by`] on integer lines `p·x + q`, `line` giving `(p, q)` of each, with the
/// test [`not_above`]. Called by zedc-presburger's `envelope`, `extend`'s `hull_of` and
/// `UpperHull::of`, whose upper hull of points `(p, q)` is this envelope of lines `p·x + q`.
pub fn upper_envelope<T>(lines: &[T], line: impl Fn(&T) -> (&Int, &Int)) -> Vec<usize> {
    upper_envelope_by(
        lines,
        |a, b| line(a).0 == line(b).0,
        |a, b, c| not_above(line(a), line(b), line(c)),
    )
}

/// Whether `b` lies on or below the line from `a` to `c`, for `a.0 < b.0 < c.0`: the cross
/// product of `b - a` and `c - a` is at least 0. In the dual picture, where the point `(p, q)`
/// stands for the line `p·x + q`, it says that line `b` is nowhere above both `a` and `c`:
/// at the crossing `x = (qa - qc) / (pc - pa)` of `a` and `c`, `b` is under `a` when
/// `(pb - pa)·(qa - qc) <= (qa - qb)·(pc - pa)`, the differences of slopes above zero so that
/// the cross-multiplied form keeps the order, and that is this test.
///
/// `#[inline]`: it is not generic, so without it Rust compiles it once here and does not inline
/// it into the generic [`upper_envelope`] that callers in other crates instantiate (common brief
/// item 5, 2026-11-26).
#[inline]
pub fn not_above(a: (&Int, &Int), b: (&Int, &Int), c: (&Int, &Int)) -> bool {
    let (bx, by) = (b.0 - a.0, b.1 - a.1);
    let (cx, cy) = (c.0 - a.0, c.1 - a.1);
    &bx * &cy >= &by * &cx
}

/// `Σ ⌊(a·i + b) / m⌋` for `i` from 0 below `n`, with `m` above zero and `n` at least zero:
/// `zed_numtheory::floor_sum_i128` when the four fit in `i128` and no step overflows, else
/// `zed_numtheory::floor_sum`, whose bit cost is stated there (FLOORSUM-bits).
///
/// # Panics
///
/// If `m <= 0` or `n < 0`.
pub fn floor_sum(n: &Int, m: &Int, a: &Int, b: &Int) -> Int {
    if let (Some(n), Some(m), Some(a), Some(b)) =
        (n.to_i128(), m.to_i128(), a.to_i128(), b.to_i128())
        && let Some(s) = floor_sum_i128(n, m, a, b)
    {
        return s.into();
    }
    zed_numtheory::floor_sum(&n.big(), &m.big(), &a.big(), &b.big()).into()
}
