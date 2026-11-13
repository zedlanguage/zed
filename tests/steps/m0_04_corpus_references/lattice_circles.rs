//! Reference 14 on lattice points of circles. Many pairs of such points lie at one distance, and
//! four or more points on one circle make the Delaunay triangulation one of several, so the
//! merges of a level are many ties that the key (distance², smaller label, larger label) alone
//! decides. Each point set is checked three ways: against the corpus program read literally
//! (every pair at every merge), against a minimum spanning tree found by Prim's method, and
//! against itself moved by a symmetry of the lattice, which keeps every distance and label but
//! changes which triangulation the reference builds.

use std::collections::BTreeMap;
use std::fmt::Write;

use super::{cluster_text, p14_oracle, splitmix};

type Pt = (i64, i64);

/// The lattice points of the circle x² + y² = `r2` about `center`, by x, then y.
fn circle(r2: i64, center: Pt) -> Vec<Pt> {
    let r = r2.isqrt();
    let mut points = Vec::new();
    for x in -r..=r {
        let y = (r2 - x * x).isqrt();
        if x * x + y * y == r2 {
            points.push((center.0 + x, center.1 - y));
            if y != 0 {
                points.push((center.0 + x, center.1 + y));
            }
        }
    }
    points
}

/// The point sets: single circles with 4 to 48 points, rings about one center, circles of one
/// radius about nearby centers, which share points, and circles with their center and copies of
/// some points.
fn point_sets() -> Vec<(&'static str, Vec<Pt>)> {
    let o = (0, 0);
    let mut sets: Vec<(&'static str, Vec<Pt>)> = vec![
        ("r² = 1", circle(1, o)),
        ("r² = 2", circle(2, o)),
        ("r² = 5", circle(5, o)),
        ("r² = 25", circle(25, o)),
        ("r² = 65", circle(65, o)),
        ("r² = 325", circle(325, o)),
        ("r² = 1105", circle(1105, (3, -2))),
        ("r² = 5525", circle(5525, o)),
    ];
    let rings = [5, 10, 20, 25, 50].iter().flat_map(|&r2| circle(r2, o));
    sets.push(("rings r² = 5, 10, 20, 25, 50", rings.collect()));
    let rings = [25, 50, 100].iter().flat_map(|&r2| circle(r2, (-1, 4)));
    sets.push(("rings r² = 25, 50, 100", rings.collect()));
    let centers = [(0, 0), (10, 0), (5, 5), (3, 4)];
    let shared = centers.iter().flat_map(|&c| circle(25, c));
    sets.push(("r² = 25 about four centers", shared.collect()));
    let mut copies = circle(65, o);
    copies.extend([(0, 0), (0, 0), (1, 8), (-7, -4), (1, 8)]);
    sets.push(("r² = 65 with its center and copies", copies));
    sets
}

/// `points` as built, reversed, and in two orders drawn at random.
fn orders(points: &[Pt]) -> Vec<Vec<Pt>> {
    let shuffled = |seed: u64| {
        let mut keyed: Vec<(u64, Pt)> = (0..)
            .zip(points)
            .map(|(i, &p)| (splitmix(seed, i), p))
            .collect();
        keyed.sort_unstable();
        keyed.into_iter().map(|(_, p)| p).collect()
    };
    let reversed = points.iter().rev().copied().collect();
    vec![points.to_vec(), reversed, shuffled(1), shuffled(2)]
}

fn d2(p: Pt, q: Pt) -> i64 {
    (p.0 - q.0).pow(2) + (p.1 - q.1).pow(2)
}

/// Reference 14's input for `k` clusters of `points`.
fn input(k: i64, points: &[Pt]) -> String {
    points.iter().fold(format!("{k}\n"), |mut s, (x, y)| {
        writeln!(s, "{x} {y}").expect("writing to a String");
        s
    })
}

/// The output for the cluster labels `label`: each cluster by its label, with its points.
fn output(label: &[usize]) -> String {
    let mut clusters: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for (i, &l) in label.iter().enumerate() {
        clusters.entry(l).or_default().push(i.to_string());
    }
    clusters.iter().fold(String::new(), |mut s, (l, members)| {
        writeln!(s, "{l}: {}", members.join(" ")).expect("writing to a String");
        s
    })
}

/// The corpus program read literally: at each merge the least (distance², smaller label, larger
/// label) over every pair of points in different clusters, the larger label renamed to the
/// smaller. Item m of the result is the output after m merges, for m from 0 to n - 1.
/// O(n³), for small sets only.
fn literal_outputs(points: &[Pt]) -> Vec<String> {
    let n = points.len();
    let mut label: Vec<usize> = (0..n).collect();
    let mut outputs = vec![output(&label)];
    for _ in 1..n {
        let mut best = None;
        for i in 0..n {
            for j in i + 1..n {
                let (a, b) = (label[i].min(label[j]), label[i].max(label[j]));
                if a != b {
                    let key = (d2(points[i], points[j]), a, b);
                    best = Some(best.map_or(key, |m: (i64, usize, usize)| m.min(key)));
                }
            }
        }
        let (_, a, b) = best.expect("two clusters while fewer than n - 1 merges are made");
        label.iter_mut().filter(|l| **l == b).for_each(|l| *l = a);
        outputs.push(output(&label));
    }
    outputs
}

/// The edge weights (squared distances) of a minimum spanning tree of `points`, by Prim's method
/// on all pairs. O(n²).
fn spanning_tree_weights(points: &[Pt]) -> Vec<i64> {
    let n = points.len();
    let mut in_tree = vec![false; n];
    let mut nearest = vec![i64::MAX; n];
    let mut weights = Vec::new();
    if n == 0 {
        return weights;
    }
    nearest[0] = 0;
    for step in 0..n {
        let next = (0..n)
            .filter(|&v| !in_tree[v])
            .min_by_key(|&v| nearest[v])
            .expect("a point outside the tree");
        in_tree[next] = true;
        if step > 0 {
            weights.push(nearest[next]);
        }
        for v in 0..n {
            if !in_tree[v] {
                nearest[v] = nearest[v].min(d2(points[next], points[v]));
            }
        }
    }
    weights
}

/// Checks that the clusters `out` prints for `points` and `k` are a spanning forest of least
/// weight: k clusters (n if k > n), each named by its least point and listing its points in
/// rising order, every point in one, and the weights of the clusters' own minimum spanning trees
/// adding to the n - k least weights of a minimum spanning tree of all the points. Kruskal's
/// method stopped at k parts gives such a forest whatever order it takes ties in, and any forest
/// of n - k edges weighs at least that much.
fn check_forest(what: &str, k: usize, points: &[Pt], out: &str) {
    let n = points.len();
    let mut seen = vec![false; n];
    let mut forest = 0;
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines.len(),
        k.min(n),
        "{what}, k = {k}: the clusters\n{out}"
    );
    for line in lines {
        let (label, members) = line.split_once(": ").expect("a cluster line");
        let members: Vec<usize> = members
            .split(' ')
            .map(|m| m.parse().expect("a point index"))
            .collect();
        assert_eq!(label, members[0].to_string(), "{what}, k = {k}: {line}");
        assert!(members.is_sorted(), "{what}, k = {k}: {line}");
        for &m in &members {
            assert!(!seen[m], "{what}, k = {k}: point {m} twice\n{out}");
            seen[m] = true;
        }
        let own: Vec<Pt> = members.iter().map(|&m| points[m]).collect();
        forest += spanning_tree_weights(&own).iter().sum::<i64>();
    }
    assert!(
        seen.iter().all(|&s| s),
        "{what}, k = {k}: a point is missing\n{out}"
    );
    let mut weights = spanning_tree_weights(points);
    weights.sort_unstable();
    let least: i64 = weights[..n.saturating_sub(k)].iter().sum();
    assert_eq!(forest, least, "{what}, k = {k}: the forest weight\n{out}");
}

/// The 12 points of x² + y² = 25 counterclockwise from (5, 0). Neighbors are 2 or 10 apart in
/// squared distance by turns, so the first four merges join 1 and 2, 4 and 5, 7 and 8, 10 and
/// 11. All eight pairs of neighbors left are at 10. The least key among them is that of
/// clusters 0 and 1, and after it cluster 0 keeps the least key, (10, 0, 3), then (10, 0, 4):
/// it grows counterclockwise only, although its pair with cluster 10 is at the same distance.
#[test]
fn clustering_a_lattice_circle_grows_the_least_cluster_first() {
    let input = "5\n5 0\n4 3\n3 4\n0 5\n-3 4\n-4 3\n-5 0\n-4 -3\n-3 -4\n0 -5\n3 -4\n4 -3\n";
    let want = "0: 0 1 2 3 4 5\n6: 6\n7: 7 8\n9: 9\n10: 10 11\n";
    assert_eq!(cluster_text(input), (want.to_string(), Ok(())));
}

/// Every set and order, every k from 1 to n + 1: the output is that of the program read
/// literally, and the clusters are a spanning forest of least weight.
#[test]
fn clustering_of_lattice_circles_agrees_with_the_program_read_literally() {
    let mut checked = 0;
    for (what, points) in point_sets() {
        for (o, points) in orders(&points).iter().enumerate() {
            let what = format!("{what}, order {o}");
            let literal = literal_outputs(points);
            let n = points.len();
            for k in 1..=n + 1 {
                let (out, result) = cluster_text(&input(k as i64, points));
                assert_eq!(result, Ok(()), "{what}, k = {k}");
                assert_eq!(out, literal[n.saturating_sub(k)], "{what}, k = {k}");
                check_forest(&what, k, points, &out);
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 1252);
}

/// The 8 symmetries of the square lattice, each after a stretch by `scale` and before a shift.
fn moved(points: &[Pt], symmetry: usize, scale: i64, shift: Pt) -> Vec<Pt> {
    let turn = |(x, y): Pt| match symmetry % 4 {
        0 => (x, y),
        1 => (-y, x),
        2 => (-x, -y),
        _ => (y, -x),
    };
    let flip = |(x, y): Pt| if symmetry < 4 { (x, y) } else { (y, x) };
    let place = |(x, y): Pt| (x * scale + shift.0, y * scale + shift.1);
    points.iter().map(|&p| place(flip(turn(p)))).collect()
}

/// Moving every point by a symmetry of the lattice, a stretch or a shift keeps every distance in
/// order and every label, so the output stays the same, although the points sort into another
/// order and the reference builds another of the triangulations of points on one circle.
#[test]
fn clustering_of_lattice_circles_does_not_change_when_the_points_move_together() {
    let shifts = [(0, 0), (17, -40), (-1_000_003, 999_983)];
    for (what, points) in point_sets() {
        for (o, points) in orders(&points).iter().take(2).enumerate() {
            let n = points.len();
            let outputs: Vec<String> = (1..=n)
                .map(|k| cluster_text(&input(k as i64, points)).0)
                .collect();
            for (symmetry, scale, shift) in (0..8).flat_map(|s| {
                [1, 3]
                    .into_iter()
                    .flat_map(move |c| shifts.map(|t| (s, c, t)))
            }) {
                let image = moved(points, symmetry, scale, shift);
                for k in 1..=n {
                    let (out, result) = cluster_text(&input(k as i64, &image));
                    assert_eq!(result, Ok(()));
                    assert_eq!(
                        out,
                        outputs[k - 1],
                        "{what}, order {o}, k = {k}, symmetry {symmetry}, scale {scale}, \
                         shift {shift:?}"
                    );
                }
            }
        }
    }
}

/// Four rings about one center, 208 points, each ring with 32 to 64 points: the output is that
/// of the O(n²) form, and the clusters are a spanning forest of least weight.
#[test]
fn clustering_of_wide_lattice_rings_agrees_with_its_quadratic_form() {
    let rings = [1105, 5525, 27625, 32045];
    let points: Vec<Pt> = rings.iter().flat_map(|&r2| circle(r2, (0, 0))).collect();
    assert_eq!(points.len(), 208);
    for (o, points) in orders(&points).iter().enumerate() {
        for k in [1, 2, 3, 4, 5, 9, 33, 52, 104, 150, 207] {
            let text = input(k as i64, points);
            let mut want = String::new();
            let oracle = p14_oracle::run(&super::input_lines(&text), &mut want);
            let (out, result) = cluster_text(&text);
            assert_eq!((&out, result), (&want, oracle), "order {o}, k = {k}");
            check_forest(&format!("rings, order {o}"), k, points, &out);
        }
    }
}
