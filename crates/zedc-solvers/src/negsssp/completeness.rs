//! Completeness tests of Duong's search (row TEST-complete-crates, author P189): the growth of a
//! ball past its first shell (\[D\] Lemma 4.4), the heavy split when no shell is empty, the
//! ordered merge of children that share vertices (\[D\] Theorem 3.1), and the whole search on
//! weights large enough that a ball's step `δ₀` is more than one unit. Expected results are the
//! lemmas' statements and the definition of a potential, checked against Bellman–Ford. The case
//! list is `crates/zedc-solvers/COMPLETENESS.md`.

use super::*;

/// Edges `u → (v, w)` with machine weights, as [`potential`] takes them.
fn graph(out: &[Vec<(usize, i64)>]) -> Vec<Vec<(usize, Int)>> {
    out.iter()
        .map(|edges| edges.iter().map(|&(v, w)| (v, Int::from(w))).collect())
        .collect()
}

/// Bellman–Ford on the subgraph of `out` induced by `set`, from labels 0: the least weight of a
/// walk ending at each vertex of `set`, in its order, or `None` when that subgraph has a
/// negative cycle (a label still falling after `|set|` passes).
fn bellman_ford(out: &[Vec<(usize, i64)>], set: &[usize]) -> Option<Vec<Int>> {
    let mut place = vec![usize::MAX; out.len()];
    for (k, &v) in set.iter().enumerate() {
        place[v] = k;
    }
    let mut d = vec![Int::ZERO; set.len()];
    for _ in 0..=set.len() {
        let mut fell = false;
        for &u in set {
            for &(v, w) in &out[u] {
                if place[v] == usize::MAX {
                    continue;
                }
                let to = &d[place[u]] + &Int::from(w);
                if to < d[place[v]] {
                    d[place[v]] = to;
                    fell = true;
                }
            }
        }
        if !fell {
            return Some(d);
        }
    }
    None
}

/// Whether `p`, given in the order of `set`, is a potential of the subgraph of `out` induced by
/// `set`: `p(v) <= p(u) + w` on each of its edges.
fn holds(out: &[Vec<(usize, i64)>], set: &[usize], p: &[Int]) -> bool {
    let mut place = vec![usize::MAX; out.len()];
    for (k, &v) in set.iter().enumerate() {
        place[v] = k;
    }
    set.iter().all(|&u| {
        out[u]
            .iter()
            .all(|&(v, w)| place[v] == usize::MAX || p[place[v]] <= &p[place[u]] + &Int::from(w))
    })
}

/// xorshift64 from the run's seed for `test`, made odd since 0 stays at 0.
fn random(test: &str) -> impl FnMut(u64) -> u64 {
    let mut state = crate::seed::seed(test) | 1;
    move |k| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state % k
    }
}

/// The radii with `δ₀ = d / scale`.
fn radii<'a>(m: u64, l: u64, scale: &'a Int, d: &'a Int) -> Radii<'a> {
    Radii { m, l, scale, d }
}

/// Offers `v` at distance `x`.
fn feed(ball: &mut Ball, v: usize, x: i64, mass: &[u64], at: &Radii) -> Fed {
    ball.feed(Some((v, &Int::from(x))), mass, at)
}

#[test]
fn a_ball_takes_its_core_up_to_t_steps_and_its_shell_up_to_one_more_inclusive() {
    // δ₀ = 4: a vertex at distance x is in the ball of radius t·δ₀ for t = ⌈x / 4⌉.
    let (scale, d) = (Int::ONE, Int::from(4));
    let at = radii(1000, 1, &scale, &d);
    let mass = [10, 1, 1, 1];
    let mut ball = Ball::default();
    // Radius 0 holds the vertices at distance 0 only.
    assert!(matches!(feed(&mut ball, 0, 0, &mass, &at), Fed::Took));
    assert!(matches!(feed(&mut ball, 1, 0, &mass, &at), Fed::Took));
    assert_eq!(
        (ball.core.clone(), ball.core_mass, ball.closed),
        (vec![0, 1], 11, false)
    );
    // Distance 4 = δ₀ is at the edge of radius δ₀: the shell, which closes the core.
    assert!(matches!(feed(&mut ball, 2, 4, &mass, &at), Fed::Took));
    assert!(ball.closed && !ball.heavy);
    assert_eq!((ball.shell.clone(), ball.shell_mass), (vec![2], 1));
    // Distance 5 is past it: the shell is complete, and light against the core:
    // 24·L·1 = 24 <= 11·⌊log₂(1000 / 11)⌋ = 66.
    assert!(matches!(feed(&mut ball, 3, 5, &mass, &at), Fed::Light));
    assert_eq!(
        (ball.core, ball.shell, ball.t),
        (vec![0, 1], vec![2], Int::ZERO)
    );
}

#[test]
fn a_shell_too_heavy_for_its_core_joins_it_and_the_next_shell_is_tested() {
    let (scale, d) = (Int::ONE, Int::ONE);
    let at = radii(1000, 1, &scale, &d);
    // Core 1, shells of 10 at distances 1 and 2, then a gap to distance 5.
    let mass = [1, 10, 10, 1];
    let mut ball = Ball::default();
    assert!(matches!(feed(&mut ball, 0, 0, &mass, &at), Fed::Took));
    assert!(matches!(feed(&mut ball, 1, 1, &mass, &at), Fed::Took));
    // Distance 2 completes the shell {1}: 24·10 > 1·⌊log₂ 1000⌋ = 9, so the shell joins the
    // core and the ball's radius grows to δ₀; distance 2 is then the next shell.
    assert!(matches!(feed(&mut ball, 2, 2, &mass, &at), Fed::Took));
    assert_eq!(
        (ball.core.clone(), ball.core_mass, ball.t.clone()),
        (vec![0, 1], 11, Int::ONE)
    );
    assert_eq!((ball.shell.clone(), ball.shell_mass), (vec![2], 10));
    // Distance 5 completes the shell {2}: 240 > 11·⌊log₂(1000 / 11)⌋ = 66, so it joins, the
    // radius grows to 2·δ₀, and the next shell (distance 3) is empty, so light.
    assert!(matches!(feed(&mut ball, 3, 5, &mass, &at), Fed::Light));
    assert_eq!(
        (ball.core, ball.core_mass, ball.shell, ball.t),
        (vec![0, 1, 2], 21, vec![], Int::from(2))
    );
    assert!(!ball.heavy);
}

#[test]
fn a_ball_whose_core_reaches_an_eighth_of_the_mass_is_heavy_at_once_or_after_growing() {
    let (scale, d) = (Int::ONE, Int::ONE);
    let at = radii(80, 1, &scale, &d);
    // The core at radius 0 already holds 10 = 80 / 8: heavy as it closes.
    let mut ball = Ball::default();
    assert!(matches!(feed(&mut ball, 0, 0, &[10, 1], &at), Fed::Took));
    assert!(matches!(feed(&mut ball, 1, 1, &[10, 1], &at), Fed::Heavy));
    assert!(ball.closed && ball.heavy && ball.shell.is_empty());
    // A core of 1 at closing, light; its shell of 9 is too heavy to leave (24·9 > 1·6), and
    // joined to the core it makes 10: heavy.
    let mut ball = Ball::default();
    assert!(matches!(feed(&mut ball, 0, 0, &[1, 9], &at), Fed::Took));
    assert!(matches!(feed(&mut ball, 1, 1, &[1, 9], &at), Fed::Took));
    assert!(matches!(ball.feed(None, &[1, 9], &at), Fed::Heavy));
    assert!(ball.heavy);
    assert_eq!(
        (ball.core, ball.core_mass, ball.t),
        (vec![0, 1], 10, Int::ONE)
    );
}

#[test]
fn the_end_of_the_search_completes_the_core_and_then_the_shell() {
    let (scale, d) = (Int::ONE, Int::ONE);
    let at = radii(1000, 2, &scale, &d);
    // The search ends inside the core: the core closes light and its shell is empty.
    let mut ball = Ball::default();
    assert!(matches!(feed(&mut ball, 0, 0, &[3], &at), Fed::Took));
    assert!(matches!(ball.feed(None, &[3], &at), Fed::Light));
    assert!(ball.closed && ball.shell.is_empty());
    // The search ends inside the shell: a light shell, kept.
    // 24·2·1 = 48 <= 8·⌊log₂ 125⌋ = 48.
    let mut ball = Ball::default();
    assert!(matches!(feed(&mut ball, 0, 0, &[8, 1], &at), Fed::Took));
    assert!(matches!(feed(&mut ball, 1, 1, &[8, 1], &at), Fed::Took));
    assert!(matches!(ball.feed(None, &[8, 1], &at), Fed::Light));
    assert_eq!((ball.core, ball.shell), (vec![0], vec![1]));
}

#[test]
fn the_radius_step_is_d_over_scale_rounded_up_to_whole_steps() {
    // δ₀ = 8 / 3: distance 2 is within one step, distance 3 within two (3·3/8 rounds up to 2).
    let (scale, d) = (Int::from(3), Int::from(8));
    let at = radii(1000, 1, &scale, &d);
    let mass = [10, 1, 1];
    let mut ball = Ball::default();
    assert!(matches!(feed(&mut ball, 0, 0, &mass, &at), Fed::Took));
    assert!(matches!(feed(&mut ball, 1, 2, &mass, &at), Fed::Took));
    assert_eq!(ball.shell, vec![1]);
    assert!(matches!(feed(&mut ball, 2, 3, &mass, &at), Fed::Light));
}

/// A star of `k` leaves around vertex 0, the edge to leaf `i` of clipped weight `dist[i - 1]`.
fn star(dist: &[i64]) -> Vec<Vec<(usize, Int)>> {
    let mut out = vec![Vec::new(); dist.len() + 1];
    out[0] = (1..=dist.len()).map(|v| (v, Int::ZERO)).collect();
    out
}

#[test]
fn the_heavy_split_with_no_empty_shell_cuts_at_the_lightest_shell_the_first_among_equals() {
    // N_h = 384·L, and L = ⌈log₂ M₀⌉ = 16 for this star: 6,147 leaves, each of mass 1 + λ = 5,
    // the center 6,147 + 4, so M₀ = 36,886.
    let n_h = 6144;
    // δ_h = d / (32·N_h) = 1, so a leaf at distance x is in shell index x, and the shells of
    // (Δ, 2Δ] are indices N_h + 1 to 2·N_h, shell j holding index N_h + j + 1. One leaf inside
    // Δ, two in shell 0, one in each other shell, one past 2Δ.
    let mut dist = vec![5, n_h + 1, n_h + 1];
    dist.extend((n_h + 2)..=(2 * n_h));
    dist.push(2 * n_h + 1);
    let out = star(&dist);
    let g = Graph::new(&out);
    let progress = Progress::default();
    let mut solver = Solver::new(&g, &progress, || Ok::<(), Infallible>(()));
    assert_eq!(solver.n_h, n_h as u64);
    let d = solver.scale_h.clone();
    solver.ell = dist.iter().map(|&x| Int::from(x)).collect();
    let x: Vec<usize> = (0..out.len()).collect();
    let id = solver.stamp(&x);
    let Ok(cover) = solver.heavy(&x, id, 0, &d) else {
        panic!("the heavy split stopped")
    };
    // Every shell holds a leaf; shell 0 holds two, so shell 1 (index N_h + 2, leaf 4) is the
    // lightest, the first of the 6,143 that weigh one leaf. The core going out is the center,
    // leaf 1 and shell 0's leaves 2 and 3; the pad adds leaf 4. Going in, the center reaches
    // only itself, the core.
    let leaves = out.len() - 1;
    assert_eq!(cover.len(), 3);
    assert_eq!(cover[0], (vec![1, 2, 3, 4], false));
    assert_eq!(cover[1], (vec![0], true));
    assert_eq!(cover[2], ((4..=leaves).collect::<Vec<_>>(), false));
}

#[test]
fn the_heavy_split_cuts_at_the_first_empty_shell() {
    // As above, with the leaf of shell 1 moved past 2Δ: shell 1 is the first empty one.
    let n_h = 6144;
    let mut dist = vec![5, n_h + 1, n_h + 1, 2 * n_h + 1];
    dist.extend((n_h + 3)..=(2 * n_h));
    dist.push(2 * n_h + 1);
    let out = star(&dist);
    let g = Graph::new(&out);
    let progress = Progress::default();
    let mut solver = Solver::new(&g, &progress, || Ok::<(), Infallible>(()));
    assert_eq!(solver.n_h, n_h as u64);
    let d = solver.scale_h.clone();
    solver.ell = dist.iter().map(|&x| Int::from(x)).collect();
    let x: Vec<usize> = (0..out.len()).collect();
    let id = solver.stamp(&x);
    let Ok(cover) = solver.heavy(&x, id, 0, &d) else {
        panic!("the heavy split stopped")
    };
    // The core holds indices up to N_h + 1 and the pad, shell 1, is empty.
    let leaves = out.len() - 1;
    assert_eq!(cover[0], (vec![1, 2, 3], false));
    assert_eq!(cover[1], (vec![0], true));
    assert_eq!(cover[2], ((4..=leaves).collect::<Vec<_>>(), false));
}

/// [`Solver::merge`] of the children `cover` of all of `out`, each child given the potential
/// Bellman–Ford finds on it, with the weights `c` of the graph's own edges.
fn merged(out: &[Vec<(usize, i64)>], cover: &[Vec<usize>]) -> Option<Vec<Int>> {
    let big = graph(out);
    let g = Graph::new(&big);
    let progress = Progress::default();
    let mut solver = Solver::new(&g, &progress, || Ok::<(), Infallible>(()));
    solver.c = g.w.clone();
    let solved: Vec<(Vec<usize>, Vec<Int>)> = cover
        .iter()
        .map(|y| {
            let p = bellman_ford(out, y).expect("each child has a potential");
            (y.clone(), p)
        })
        .collect();
    let x: Vec<usize> = (0..out.len()).collect();
    match solver.merge(&x, &solved) {
        Ok(p) => Some(p),
        Err(Stop::Negative) => None,
        Err(Stop::Tick(never)) => match never {},
    }
}

#[test]
fn a_merge_of_children_that_share_vertices_gives_a_potential_of_the_whole() {
    // A path 0 → 1 → 2 → 3 of weights -3, 2, -4, covered by {0, 1, 2} and {1, 2, 3}: vertices
    // 1 and 2 are in both, so each has a prefix and a suffix chain of two places.
    let out = vec![vec![(1, -3)], vec![(2, 2)], vec![(3, -4)], vec![]];
    let p = merged(&out, &[vec![0, 1, 2], vec![1, 2, 3]]).expect("the path has no cycle");
    let x: Vec<usize> = (0..4).collect();
    assert!(holds(&out, &x, &p), "{p:?}");
    // The same cover in the other order, and three children in one vertex.
    let p = merged(&out, &[vec![1, 2, 3], vec![0, 1, 2]]).expect("the path has no cycle");
    assert!(holds(&out, &x, &p), "{p:?}");
    let p = merged(&out, &[vec![0, 1], vec![1, 2], vec![1, 3], vec![2, 3]]).unwrap();
    assert!(holds(&out, &x, &p), "{p:?}");
}

#[test]
fn a_merge_reports_the_negative_cycle_no_child_holds() {
    // The cycle 0 → 1 → 2 → 0 weighs -1, and each child holds two of its three vertices.
    let out = vec![vec![(1, -2)], vec![(2, 1)], vec![(0, 0)]];
    assert_eq!(bellman_ford(&out, &[0, 1, 2]), None);
    assert_eq!(merged(&out, &[vec![0, 1], vec![1, 2], vec![2, 0]]), None);
}

#[test]
fn merges_of_random_overlapping_covers_agree_with_bellman_ford() {
    let mut below = random("merges_of_random_overlapping_covers_agree_with_bellman_ford");
    let (mut found, mut negative, mut shared) = (0, 0, 0);
    for _ in 0..3000 {
        let n = 2 + below(7) as usize;
        let mut out: Vec<Vec<(usize, i64)>> = vec![Vec::new(); n];
        for _ in 0..below(3 * n as u64) {
            let (u, v) = (below(n as u64) as usize, below(n as u64) as usize);
            if u != v {
                out[u].push((v, below(14) as i64 - 5));
            }
        }
        // Up to four children, each vertex in at least one, each child with a potential.
        let k = 1 + below(4) as usize;
        let mut cover: Vec<Vec<usize>> = vec![Vec::new(); k];
        for v in 0..n {
            let mut placed = false;
            for child in &mut cover {
                if below(2) == 0 {
                    child.push(v);
                    placed = true;
                }
            }
            if !placed {
                cover[below(k as u64) as usize].push(v);
            }
        }
        cover.retain(|y| !y.is_empty());
        if cover.iter().any(|y| bellman_ford(&out, y).is_none()) {
            continue;
        }
        if cover.iter().map(Vec::len).sum::<usize>() > n {
            shared += 1;
        }
        let x: Vec<usize> = (0..n).collect();
        match (bellman_ford(&out, &x), merged(&out, &cover)) {
            (Some(_), Some(p)) => {
                assert!(holds(&out, &x, &p), "{out:?} {cover:?} {p:?}");
                found += 1;
            }
            (None, None) => negative += 1,
            (expected, got) => {
                panic!("{out:?} {cover:?}: Bellman–Ford {expected:?}, merge {got:?}")
            }
        }
    }
    assert!(
        found > 300 && negative > 100 && shared > 300,
        "{found} {negative} {shared}"
    );
}

#[test]
fn large_weights_give_the_least_walk_weights_of_bellman_ford() {
    // Weights up to 2^40 in magnitude make `W`, and so `δ₀ = d₀ / (32·N₀)` with `d₀ >= n·W`,
    // many units wide, so that balls grow past their first shell, and long negative paths
    // make BF-Dijkstra run out of units so that Duong's recursion runs.
    let mut below = random("large_weights_give_the_least_walk_weights_of_bellman_ford");
    let (mut found, mut negative) = (0, 0);
    for round in 0..400 {
        let n = 2 + below(24) as usize;
        let scale = 1i64 << (10 + below(31));
        // A path of negative edges, then edges of either sign.
        let mut out: Vec<Vec<(usize, i64)>> = (0..n)
            .map(|u| match u {
                0 => Vec::new(),
                _ => vec![(u - 1, -(below(scale as u64) as i64) - 1)],
            })
            .collect();
        for _ in 0..below(2 * n as u64) {
            let (u, v) = (below(n as u64) as usize, below(n as u64) as usize);
            let w = below(4 * scale as u64) as i64 - if round % 2 == 0 { 0 } else { scale };
            out[u].push((v, w));
        }
        let x: Vec<usize> = (0..n).collect();
        let expected = bellman_ford(&out, &x);
        let got = potential_alone(&graph(&out));
        assert_eq!(got, expected, "{out:?}");
        match got {
            Some(_) => found += 1,
            None => negative += 1,
        }
    }
    assert!(found > 50 && negative > 50, "{found} {negative}");
}

#[test]
fn weights_just_above_minus_w_over_2_grow_balls_and_keep_the_answers_of_bellman_ford() {
    // With `n + 1 = 32` and a path of edges of weight `-A = -2^30`, the first step's `W` is
    // `32·A = 2^35`; an edge of weight `-B = -(2^29 - 1)` has `c = 32·(-B) + W/2 = 32`, far
    // within `δ₀`, so balls reach vertices one such edge apart as shells and grow over them.
    // The path's 30 negative edges make BF-Dijkstra run out of units, so the recursion runs.
    // An edge to a higher vertex closes a negative cycle with the path, since every such
    // edge weighs less than `A`; even rounds have none, odd rounds may.
    let mut below =
        random("weights_just_above_minus_w_over_2_grow_balls_and_keep_the_answers_of_bellman_ford");
    let n = 31;
    let (a, b) = (1i64 << 30, (1i64 << 29) - 1);
    let (mut found, mut negative) = (0, 0);
    for round in 0..40 {
        let mut out: Vec<Vec<(usize, i64)>> = (0..n)
            .map(|u| match u {
                0 => Vec::new(),
                _ => vec![(u - 1, -a)],
            })
            .collect();
        for _ in 0..below(3 * n as u64) {
            let (mut u, mut v) = (below(n as u64) as usize, below(n as u64) as usize);
            // In even rounds every edge goes to a lower vertex, as the path does: no cycle.
            if round % 2 == 0 {
                if u == v {
                    continue;
                }
                if u < v {
                    (u, v) = (v, u);
                }
            }
            let w = match below(3) {
                0 => -b,
                1 => -b + below(4) as i64,
                _ => below(a as u64) as i64,
            };
            out[u].push((v, w));
        }
        let x: Vec<usize> = (0..n).collect();
        let expected = bellman_ford(&out, &x);
        assert_eq!(potential_alone(&graph(&out)), expected, "{out:?}");
        match expected {
            Some(_) => found += 1,
            None => negative += 1,
        }
    }
    assert!(found > 0 && negative > 0, "{found} {negative}");
}
