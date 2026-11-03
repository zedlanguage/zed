//! 14 single-linkage clustering to k clusters: the closest pair of points in different clusters,
//! ties broken by (distance², smaller label, larger label) in natural tuple order; the larger
//! label is renamed to the smaller. n - k merges (none if k >= n). A cluster goes by its label.
//!
//! Each cluster keeps its distance to every other and which of them comes first by that key. On
//! merging b into a, a's key to any c is at most b's, since a < b, so c's nearest is either
//! unchanged or a, which one comparison decides. Only a's own nearest needs a scan of its row.

use std::cmp::Ordering;
use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use crate::zedrt::{at, parse_int};

/// The distances between clusters, each pair once.
struct Distances {
    n: usize,
    cells: Vec<BigInt>,
}

impl Distances {
    fn cell(&self, x: usize, y: usize) -> usize {
        let (i, j) = (x.min(y), x.max(y));
        i * (2 * self.n - i - 1) / 2 + j - i - 1
    }

    fn at(&self, x: usize, y: usize) -> &BigInt {
        &self.cells[self.cell(x, y)]
    }

    /// Orders the pairs (c, x) and (c, y) by distance, smaller label, larger label.
    fn order(&self, c: usize, x: usize, y: usize) -> Ordering {
        let labels = |o: usize| (c.min(o), c.max(o));
        let by_distance = self.at(c, x).cmp(self.at(c, y));
        by_distance.then_with(|| labels(x).cmp(&labels(y)))
    }

    /// Orders the pairs (c, x) and (d, y) likewise.
    fn order_pairs(&self, (c, x): (usize, usize), (d, y): (usize, usize)) -> Ordering {
        let by_distance = self.at(c, x).cmp(self.at(d, y));
        by_distance.then_with(|| (c.min(x), c.max(x)).cmp(&(d.min(y), d.max(y))))
    }
}

/// The squared distance of every pair of `pts`.
fn squared_distances(pts: &[Vec<BigInt>]) -> Result<Vec<BigInt>, String> {
    let mut cells = Vec::with_capacity(pts.len() * pts.len().saturating_sub(1) / 2);
    for (i, p) in pts.iter().enumerate() {
        for q in &pts[i + 1..] {
            let dx = at(p, 0)? - at(q, 0)?;
            let dy = at(p, 1)? - at(q, 1)?;
            cells.push(&dx * &dx + &dy * &dy);
        }
    }
    Ok(cells)
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let k = parse_int(at(lines, 0)?)?;
    let mut pts = Vec::new();
    for l in &lines[1..] {
        let point = l.split(' ').map(parse_int);
        pts.push(point.collect::<Result<Vec<BigInt>, String>>()?);
    }
    let n = pts.len();
    let mut label: Vec<usize> = (0..n).collect();
    let merges = (BigInt::from(n) - k).max(BigInt::zero());
    if !merges.is_zero() {
        let mut d = Distances {
            n,
            cells: squared_distances(&pts)?,
        };
        let mut alive: Vec<usize> = (0..n).collect();
        let nearest_of = |d: &Distances, alive: &[usize], c: usize| {
            let others = alive.iter().copied().filter(|&x| x != c);
            others.min_by(|&x, &y| d.order(c, x, y))
        };
        let mut nearest: Vec<usize> = alive
            .iter()
            .map(|&c| nearest_of(&d, &alive, c).unwrap_or(c))
            .collect();
        // Past the number of points the loop stops at its error, so a size no `usize` holds is
        // as good as any other.
        for _ in 0..merges.to_usize().unwrap_or(usize::MAX) {
            if alive.len() < 2 {
                return Err("min() of no pairs".into());
            }
            let first = |x: &usize, y: &usize| d.order_pairs((*x, nearest[*x]), (*y, nearest[*y]));
            let c = alive.iter().copied().min_by(first).expect("two are alive");
            let (a, b) = (c.min(nearest[c]), c.max(nearest[c]));
            alive.retain(|&x| x != b);
            for &c in alive.iter().filter(|&&c| c != a) {
                let (ab, bc) = (d.cell(a, c), d.cell(b, c));
                if d.cells[bc] < d.cells[ab] {
                    d.cells.swap(ab, bc);
                }
                if nearest[c] == b || d.order(c, a, nearest[c]) != Ordering::Greater {
                    nearest[c] = a;
                }
            }
            nearest[a] = nearest_of(&d, &alive, a).unwrap_or(a);
            for l in &mut label {
                if *l == b {
                    *l = a;
                }
            }
        }
    }
    let mut clusters: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for (i, &c) in label.iter().enumerate() {
        clusters.entry(c).or_default().push(i.to_string());
    }
    for (c, members) in clusters {
        say!(out, "{c}: {}", members.join(" "));
    }
    Ok(())
}
