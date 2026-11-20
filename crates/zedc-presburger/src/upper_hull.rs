//! The upper convex hull of points `(x, y)` with integer coordinates, kept in a persistent
//! vector so that copies share it, built at once from sorted points and kept as points enter
//! (PERF-l139-ray-hull, moved here from `zedc-preimage`'s `RayHull` so that other crates can
//! use it).

pub use crate::presburger::not_above;
use crate::presburger::upper_envelope;
use zed_collections::search::first_true;
use zedc_int::int::Int;

/// The upper convex hull of a set of points, as its vertices from least `x` to greatest, no
/// three on a line, of each `x` only the point of greatest `y`.
///
/// Complexity tradeoff: naive version, the hull built again from all `R` points at each new
/// point, O(R) each (O(R log R) unsorted). Used: [`UpperHull::of`] builds it once by the
/// monotone chain (A. M. Andrew, "Another efficient algorithm for convex hulls in two
/// dimensions", Information Processing Letters 9(5), 1979), O(R) on sorted points, and
/// [`UpperHull::insert`] takes a point in O(log^2 R): two binary searches for the vertices it
/// hides and a split of the persistent vector (`imbl::Vector`, O(log R) per index and per
/// split). Tradeoffs: a point cannot be taken out; a caller whose points leave builds the hull
/// again.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct UpperHull(imbl::Vector<(Int, Int)>);

impl UpperHull {
    /// The hull of `points`, given in increasing order of `(x, y)`, in O(R) for R points:
    /// the upper hull of the points `(p, q)` is the upper envelope of the lines `p·x + q`
    /// ([`not_above`]), which `presburger::upper_envelope` finds by the monotone chain.
    pub fn of<'a>(points: impl Iterator<Item = &'a (Int, Int)>) -> UpperHull {
        let points: Vec<&(Int, Int)> = points.collect();
        let on = upper_envelope(&points, |p| (&p.0, &p.1));
        UpperHull(on.into_iter().map(|i| points[i].clone()).collect())
    }

    /// The vertices, from least `x` to greatest.
    pub fn vertices(&self) -> &imbl::Vector<(Int, Int)> {
        &self.0
    }

    /// Takes in the point `(x, y)` in O(log^2 R): the vertices it hides are a run on each side
    /// of it, each run found by a binary search, and cut out by splitting the vector.
    ///
    /// Why runs: on the left, the vertex `h_t` stays if the slope of the edge into it is
    /// greater than the slope from it to the new point `P`. The slope from `h_t` to `P` is a
    /// mean of the slope of the edge out of `h_t` and the slope from `h_(t+1)` to `P`, and the
    /// edge slopes fall from left to right; so a vertex that goes has every later one on the
    /// left go too, and those that stay are a prefix. The right side is the mirror image.
    pub fn insert(&mut self, x: &Int, y: &Int) {
        let v = &self.0;
        let m = v.len();
        fn pair(h: &(Int, Int)) -> (&Int, &Int) {
            (&h.0, &h.1)
        }
        let (left_end, right_start) = match v.binary_search_by(|h| h.0.cmp(x)) {
            Ok(i) if &v[i].1 >= y => return,
            Ok(i) => (i, i + 1),
            Err(i) => {
                if i > 0 && i < m && not_above(pair(&v[i - 1]), (x, y), pair(&v[i])) {
                    return;
                }
                (i, i)
            }
        };
        // The first vertex on the left that goes: `h_t` with the turn `h_(t-1), h_t, P` not
        // to the right.
        let lo = first_true(1, left_end, |&t| {
            not_above(pair(&v[t - 1]), pair(&v[t]), (x, y))
        })
        .min(left_end);
        // The first vertex on the right that stays.
        let hi = first_true(right_start, m, |&s| {
            s + 1 == m || !not_above((x, y), pair(&v[s]), pair(&v[s + 1]))
        });
        let mut left = self.0.clone();
        let right = left.split_off(hi);
        left.truncate(lo);
        left.push_back((x.clone(), y.clone()));
        left.append(right);
        self.0 = left;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The hull by its definition: of each `x` the point of greatest `y`, kept when no two
    /// others of those points, one on each side, have it on or below the line between them.
    /// O(R^3), for the small sets of the test.
    fn hull_by_definition(points: &[(i64, i64)]) -> Vec<(Int, Int)> {
        let mut top: Vec<(i64, i64)> = Vec::new();
        for &(x, y) in points {
            match top.iter_mut().find(|p| p.0 == x) {
                Some(p) => p.1 = p.1.max(y),
                None => top.push((x, y)),
            }
        }
        top.sort_unstable();
        let big = |p: &(i64, i64)| (Int::from(p.0), Int::from(p.1));
        let kept = top.iter().filter(|b| {
            !top.iter().any(|a| {
                a.0 < b.0
                    && top.iter().any(|c| {
                        let (a, b, c) = (big(a), big(b), big(c));
                        b.0 < c.0 && not_above((&a.0, &a.1), (&b.0, &b.1), (&c.0, &c.1))
                    })
            })
        });
        kept.map(big).collect()
    }

    /// [`UpperHull::of`] on the sorted points and [`UpperHull::insert`] point by point in the
    /// order drawn give the hull by its definition, on 600 random sets of up to 14 points
    /// in `-5..=5` squared (repeats, points on one `x` and points on a line included).
    #[test]
    fn the_hull_built_at_once_and_point_by_point_is_the_hull() {
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut rng = |n: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % n
        };
        for _ in 0..600 {
            let points: Vec<(i64, i64)> = (0..1 + rng(14))
                .map(|_| (rng(11) as i64 - 5, rng(11) as i64 - 5))
                .collect();
            let want = hull_by_definition(&points);
            let mut sorted: Vec<(Int, Int)> = (points.iter())
                .map(|&(x, y)| (Int::from(x), Int::from(y)))
                .collect();
            sorted.sort_unstable();
            let built = UpperHull::of(sorted.iter());
            assert_eq!(
                built.vertices().iter().cloned().collect::<Vec<_>>(),
                want,
                "{points:?}"
            );
            let mut grown = UpperHull::default();
            for &(x, y) in &points {
                grown.insert(&Int::from(x), &Int::from(y));
            }
            assert_eq!(grown, built, "{points:?}");
        }
    }

    /// An empty hull has no vertex, and one point is its own hull.
    #[test]
    fn the_hull_of_no_point_and_of_one_point() {
        assert!(UpperHull::of([].iter()).vertices().is_empty());
        let mut h = UpperHull::default();
        h.insert(&Int::from(3), &Int::from(-2));
        assert_eq!(h, UpperHull::of([(Int::from(3), Int::from(-2))].iter()));
    }
}
