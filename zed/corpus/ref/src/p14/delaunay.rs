//! A Delaunay triangulation of distinct points by the divide and conquer of Guibas and Stolfi
//! (ACM Trans. Graphics 4(2), 1985, section 8) on their quad-edge structure. The two predicates
//! are integer determinants, so no point is misplaced by rounding. With four or more points on
//! one circle the triangulation is one of several; with all points on a line it is their path.
//! Either way it holds every edge whose closed disk on it as diameter holds no other point.
//! O(n log n) predicates. A deleted edge's slot is reused, so the mesh never holds more slots
//! than the most edges alive at once. While two halves are merged the live edges are those of
//! two triangulations and the edges joining them, at most 6n; after the last merge they are
//! those of one triangulation of n points, at most 3n - 6 by Euler's formula.

use num_bigint::BigInt;
use num_traits::Signed;

/// A point (x, y).
pub type Point = (BigInt, BigInt);

/// Whether a, b, c turn counterclockwise.
fn ccw(a: &Point, b: &Point, c: &Point) -> bool {
    let det = (&b.0 - &a.0) * (&c.1 - &a.1) - (&b.1 - &a.1) * (&c.0 - &a.0);
    det.is_positive()
}

/// Whether d lies strictly inside the circle through a, b, c, which turn counterclockwise.
///
/// The sign of the 3 by 3 determinant of the rows (x, y, x² + y²) of a - d, b - d and c - d,
/// expanded along its last column. Every number in it has at most 4b + 8 bits when every
/// coordinate has at most b bits, |x| < 2^b (COMPLEXITY.md F39):
/// - each difference, such as ax = a.x - d.x: |ax| ≤ 2(2^b - 1) < 2^(b + 1), so b + 1 bits;
/// - each product of two differences, such as bx · cy or ax · ax: < 2^(b + 1) · 2^(b + 1) =
///   2^(2b + 2), so 2b + 2 bits;
/// - each 2 by 2 minor, such as bx · cy - cx · by, and each lift ax² + ay²: a sum or difference
///   of two such products, < 2 · 2^(2b + 2) = 2^(2b + 3), so 2b + 3 bits;
/// - each of the three cofactor terms, a lift times a minor: < 2^(2b + 3) · 2^(2b + 3) =
///   2^(4b + 6), so 4b + 6 bits; the two sums on the way to the total are below 2 · 2^(4b + 6)
///   and 3 · 2^(4b + 6);
/// - the determinant, the sum of the three terms: < 3 · 2^(4b + 6) < 4 · 2^(4b + 6) = 2^(4b + 8),
///   so 4b + 8 bits, and a sign.
///
/// The numbers are `BigInt`, so no width is fixed and none can overflow; the bound is the cost
/// of each test, O(M(4b + 8)) = O(M(b)) bit operations with M(b) the cost of multiplying b-bit
/// integers.
fn in_circle(a: &Point, b: &Point, c: &Point, d: &Point) -> bool {
    let (ax, ay) = (&a.0 - &d.0, &a.1 - &d.1);
    let (bx, by) = (&b.0 - &d.0, &b.1 - &d.1);
    let (cx, cy) = (&c.0 - &d.0, &c.1 - &d.1);
    let lift = |x: &BigInt, y: &BigInt| x * x + y * y;
    let det = lift(&ax, &ay) * (&bx * &cy - &cx * &by)
        + lift(&bx, &by) * (&cx * &ay - &ax * &cy)
        + lift(&cx, &cy) * (&ax * &by - &bx * &ay);
    det.is_positive()
}

/// The quarter-edge one turn counterclockwise from `e`; four make a quad-edge, an undirected
/// edge with its dual.
fn rot(e: usize) -> usize {
    (e & !3) | ((e + 1) & 3)
}

/// `e` reversed.
fn sym(e: usize) -> usize {
    e ^ 2
}

/// The quarter-edge one turn clockwise from `e`.
fn rot_inv(e: usize) -> usize {
    (e & !3) | ((e + 3) & 3)
}

/// A subdivision of the plane, quarter-edge `4q + r` the `r`th rotation of quad-edge `q`.
struct Mesh<'a> {
    sites: &'a [Point],
    /// The next quarter-edge counterclockwise around the origin of each.
    onext: Vec<usize>,
    /// The site each primal quarter-edge leaves; the dual ones hold 0, never read.
    org: Vec<usize>,
    deleted: Vec<bool>,
    /// The deleted quad-edges, whose slots the next new edges take.
    free: Vec<usize>,
}

impl Mesh<'_> {
    fn org(&self, e: usize) -> &Point {
        &self.sites[self.org[e]]
    }

    fn dest(&self, e: usize) -> &Point {
        self.org(sym(e))
    }

    fn oprev(&self, e: usize) -> usize {
        rot(self.onext[rot(e)])
    }

    fn lnext(&self, e: usize) -> usize {
        rot(self.onext[rot_inv(e)])
    }

    fn rprev(&self, e: usize) -> usize {
        self.onext[sym(e)]
    }

    /// A new edge from site `a` to site `b`, joined to nothing.
    fn make_edge(&mut self, a: usize, b: usize) -> usize {
        let Some(q) = self.free.pop() else {
            let e = self.onext.len();
            self.onext.extend([e, e + 3, e + 2, e + 1]);
            self.org.extend([a, 0, b, 0]);
            self.deleted.push(false);
            return e;
        };
        let e = 4 * q;
        self.onext[e..e + 4].copy_from_slice(&[e, e + 3, e + 2, e + 1]);
        self.org[e..e + 4].copy_from_slice(&[a, 0, b, 0]);
        self.deleted[q] = false;
        e
    }

    /// Joins the rings around the origins of `a` and `b` if they are apart, or splits them.
    fn splice(&mut self, a: usize, b: usize) {
        let (alpha, beta) = (rot(self.onext[a]), rot(self.onext[b]));
        self.onext.swap(a, b);
        self.onext.swap(alpha, beta);
    }

    /// A new edge from the destination of `a` to the origin of `b`, in the face left of both.
    fn connect(&mut self, a: usize, b: usize) -> usize {
        let e = self.make_edge(self.org[sym(a)], self.org[b]);
        self.splice(e, self.lnext(a));
        self.splice(sym(e), b);
        e
    }

    fn delete(&mut self, e: usize) {
        self.splice(e, self.oprev(e));
        self.splice(sym(e), self.oprev(sym(e)));
        self.deleted[e / 4] = true;
        self.free.push(e / 4);
    }

    /// Whether site `x` lies right of `e`.
    fn right_of(&self, x: &Point, e: usize) -> bool {
        ccw(x, self.dest(e), self.org(e))
    }

    fn left_of(&self, x: &Point, e: usize) -> bool {
        ccw(x, self.org(e), self.dest(e))
    }

    /// Triangulates sites `lo..hi`, at least two, and returns the counterclockwise convex hull
    /// edge out of the leftmost site and the clockwise one out of the rightmost.
    fn triangulate(&mut self, lo: usize, hi: usize) -> (usize, usize) {
        match hi - lo {
            2 => {
                let a = self.make_edge(lo, lo + 1);
                return (a, sym(a));
            }
            3 => {
                let a = self.make_edge(lo, lo + 1);
                let b = self.make_edge(lo + 1, lo + 2);
                self.splice(sym(a), b);
                let s = &self.sites[lo..hi];
                if ccw(&s[0], &s[1], &s[2]) {
                    self.connect(b, a);
                    return (a, sym(b));
                }
                if ccw(&s[0], &s[2], &s[1]) {
                    let c = self.connect(b, a);
                    return (sym(c), c);
                }
                return (a, sym(b));
            }
            _ => {}
        }
        let mid = lo + (hi - lo) / 2;
        let (mut ldo, mut ldi) = self.triangulate(lo, mid);
        let (mut rdi, mut rdo) = self.triangulate(mid, hi);
        // The lower common tangent of the two hulls.
        loop {
            if self.left_of(self.org(rdi), ldi) {
                ldi = self.lnext(ldi);
            } else if self.right_of(self.org(ldi), rdi) {
                rdi = self.rprev(rdi);
            } else {
                break;
            }
        }
        let mut basel = self.connect(sym(rdi), ldi);
        if self.org[ldi] == self.org[ldo] {
            ldo = sym(basel);
        }
        if self.org[rdi] == self.org[rdo] {
            rdo = basel;
        }
        // Zips the halves together from the tangent up.
        loop {
            let valid = |m: &Self, e: usize, basel: usize| m.right_of(m.dest(e), basel);
            let mut lcand = self.onext[sym(basel)];
            if valid(self, lcand, basel) {
                while in_circle(
                    self.dest(basel),
                    self.org(basel),
                    self.dest(lcand),
                    self.dest(self.onext[lcand]),
                ) {
                    let t = self.onext[lcand];
                    self.delete(lcand);
                    lcand = t;
                }
            }
            let mut rcand = self.oprev(basel);
            if valid(self, rcand, basel) {
                while in_circle(
                    self.dest(basel),
                    self.org(basel),
                    self.dest(rcand),
                    self.dest(self.oprev(rcand)),
                ) {
                    let t = self.oprev(rcand);
                    self.delete(rcand);
                    rcand = t;
                }
            }
            let (l_valid, r_valid) = (valid(self, lcand, basel), valid(self, rcand, basel));
            if !l_valid && !r_valid {
                break;
            }
            let right = !l_valid
                || r_valid
                    && in_circle(
                        self.dest(lcand),
                        self.org(lcand),
                        self.org(rcand),
                        self.dest(rcand),
                    );
            basel = if right {
                self.connect(rcand, sym(basel))
            } else {
                self.connect(sym(basel), sym(lcand))
            };
        }
        (ldo, rdo)
    }
}

/// The edges of a Delaunay triangulation of `sites`, which are distinct and sorted by (x, y), as
/// pairs of their indices.
pub fn edges(sites: &[Point]) -> Vec<(usize, usize)> {
    if sites.len() < 2 {
        return Vec::new();
    }
    let mut mesh = Mesh {
        sites,
        onext: Vec::new(),
        org: Vec::new(),
        deleted: Vec::new(),
        free: Vec::new(),
    };
    mesh.triangulate(0, sites.len());
    let kept = (0..mesh.deleted.len()).filter(|&q| !mesh.deleted[q]);
    kept.map(|q| (mesh.org[4 * q], mesh.org[4 * q + 2]))
        .collect()
}
