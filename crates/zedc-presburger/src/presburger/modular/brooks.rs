//! A three-color witness for graphs of maximum degree three. This is the
//! block decomposition and reverse tree coloring of Baetz and Wood,
//! arXiv:1401.8023, Lemmata 1--3. A four-clique gives no witness.
use std::collections::VecDeque;

type Edge = (usize, usize);

// Complexity tradeoff: searching color assignments takes exponential time.
// Iterative block decomposition and one tree ordering per block take O(v + e)
// graph visits; sorting each block's vertices costs O((v + e) log v) in total.
// No colorable subcubic graph is given up. Larger degrees give no verdict.
// Tests: pncx_brooks_subcubic_oracle and pncx_prism_core_scale.
pub(super) fn color(adj: &[Vec<usize>]) -> Option<Vec<usize>> {
    let n = adj.len();
    if adj
        .iter()
        .any(|row| row.len() > 3 || row.iter().any(|&v| v >= n))
    {
        return None;
    }
    let blocks = blocks(adj, None)?;
    let vertices: Vec<_> = blocks.iter().map(|b| vertices(b)).collect();
    let mut incident = vec![Vec::new(); n];
    for (i, vs) in vertices.iter().enumerate() {
        for &v in vs {
            incident[v].push(i);
        }
    }
    let mut colors = vec![None; n];
    let mut seen = vec![false; blocks.len()];
    let mut index = vec![0; n];
    for start in 0..blocks.len() {
        if seen[start] {
            continue;
        }
        seen[start] = true;
        let mut todo = VecDeque::from([(start, None)]);
        while let Some((block, anchor)) = todo.pop_front() {
            let vs = &vertices[block];
            for (i, &v) in vs.iter().enumerate() {
                index[v] = i;
            }
            let mut local = vec![Vec::new(); vs.len()];
            for &(a, b) in &blocks[block] {
                local[index[a]].push(index[b]);
                local[index[b]].push(index[a]);
            }
            let own = if let Some(root) = local.iter().position(|row| row.len() < 3) {
                tree_coloring(&local, root, None)?
            } else {
                regular_block(&local)?
            };
            let shift = match anchor {
                Some(a) => (colors[a]? + 3usize - own[index[a]]) % 3,
                None => 0,
            };
            for (i, &v) in vs.iter().enumerate() {
                let c = (own[i] + shift) % 3;
                if colors[v].is_some_and(|old| old != c) {
                    return None;
                }
                colors[v] = Some(c);
                for &b in &incident[v] {
                    if !seen[b] {
                        seen[b] = true;
                        todo.push_back((b, Some(v)));
                    }
                }
            }
        }
    }
    // A vertex absent from every block is isolated.
    Some(colors.into_iter().map(|c| c.unwrap_or(0)).collect())
}

fn vertices(edges: &[Edge]) -> Vec<usize> {
    let mut out: Vec<_> = edges.iter().flat_map(|&(a, b)| [a, b]).collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// Tarjan's edge stack, with explicit DFS frames. All indices below come from
/// rows checked by color, or from its own local adjacency lists. The clock is
/// at most the length of an allocated Vec<Vec<usize>>, hence cannot overflow.
fn blocks(adj: &[Vec<usize>], excluded: Option<usize>) -> Option<Vec<Vec<Edge>>> {
    let n = adj.len();
    let mut entered = vec![usize::MAX; n];
    let mut low = vec![0; n];
    let mut parent = vec![usize::MAX; n];
    let mut clock = 0;
    let mut edges = Vec::new();
    let mut out = Vec::new();
    for start in 0..n {
        if Some(start) == excluded || entered[start] != usize::MAX {
            continue;
        }
        entered[start] = clock;
        low[start] = clock;
        clock += 1;
        let mut stack = vec![(start, 0usize)];
        while let Some((v, next)) = stack.last_mut() {
            let v = *v;
            if *next < adj[v].len() {
                let w = adj[v][*next];
                *next += 1;
                if Some(w) == excluded {
                    continue;
                }
                if entered[w] == usize::MAX {
                    parent[w] = v;
                    edges.push((v, w));
                    entered[w] = clock;
                    low[w] = clock;
                    clock += 1;
                    stack.push((w, 0));
                } else if w != parent[v] && entered[w] < entered[v] {
                    low[v] = low[v].min(entered[w]);
                    edges.push((v, w));
                }
            } else {
                stack.pop();
                let p = parent[v];
                if p != usize::MAX {
                    low[p] = low[p].min(low[v]);
                    if low[v] >= entered[p] {
                        let mut block = Vec::new();
                        loop {
                            let edge = edges.pop()?;
                            block.push(edge);
                            if edge == (p, v) {
                                break;
                            }
                        }
                        out.push(block);
                    }
                }
            }
        }
    }
    Some(out)
}

/// This block is biconnected and cubic. K4 is the sole obstruction. Find the
/// two vertices of Lemma 3 by inspecting the blocks after removing x, rather
/// than trying pairs of vertices and testing connectivity for each pair.
fn regular_block(adj: &[Vec<usize>]) -> Option<Vec<usize>> {
    let n = adj.len();
    if n == 4 {
        return None;
    }
    let x = 0;
    let parts = blocks(adj, Some(x))?;
    let (a, b, root) = if parts.len() == 1 {
        let mut pair = None;
        for &v in &adj[x] {
            for &b in &adj[v] {
                if b != x && !adj[x].contains(&b) {
                    pair = Some((x, b, v));
                    break;
                }
            }
            if pair.is_some() {
                break;
            }
        }
        pair?
    } else {
        let sets: Vec<_> = parts.iter().map(|b| vertices(b)).collect();
        let mut occurrences = vec![0; n];
        for vs in &sets {
            for &v in vs {
                occurrences[v] += 1;
            }
        }
        let mut ends = Vec::new();
        for vs in sets {
            if vs.iter().filter(|&&v| occurrences[v] > 1).count() != 1 {
                continue;
            }
            if let Some(a) = vs
                .into_iter()
                .find(|&v| occurrences[v] == 1 && adj[x].contains(&v))
            {
                ends.push(a);
            }
        }
        ends.sort_unstable();
        let (&a, &b) = (ends.first()?, ends.get(1)?);
        (a, b, x)
    };
    tree_coloring(adj, root, Some((a, b)))
}

/// Reverse discovery order leaves a parent uncolored at every vertex except
/// the root. The root has degree below three, or has two neighbors precolored
/// alike. Each choice is thus among three colors without backtracking.
fn tree_coloring(adj: &[Vec<usize>], root: usize, pair: Option<Edge>) -> Option<Vec<usize>> {
    let n = adj.len();
    let mut colors = vec![None; n];
    let mut seen = vec![false; n];
    let expected = if let Some((a, b)) = pair {
        if a == b || adj.get(a)?.contains(&b) {
            return None;
        }
        colors[a] = Some(0usize);
        colors[b] = Some(0usize);
        seen[a] = true;
        seen[b] = true;
        n.checked_sub(2)?
    } else {
        n
    };
    if *seen.get(root)? {
        return None;
    }
    seen[root] = true;
    let mut todo = vec![root];
    let mut order = Vec::new();
    while let Some(v) = todo.pop() {
        order.push(v);
        for &w in &adj[v] {
            if !seen[w] {
                seen[w] = true;
                todo.push(w);
            }
        }
    }
    if order.len() != expected {
        return None;
    }
    for v in order.into_iter().rev() {
        let mut used = [false; 3];
        for &w in &adj[v] {
            if let Some(c) = colors[w] {
                used[c] = true;
            }
        }
        colors[v] = (0..3).find(|&c| !used[c]);
        colors[v]?;
    }
    colors.into_iter().collect()
}

/// A universal vertex takes the third color exactly when the other vertices
/// form a bipartite graph. O(v+e) graph visits; no assignment search.
// Complexity tradeoff: a cubic-only witness misses even wheels. One degree
// check and one bipartite walk give their coloring, rather than repeated
// single-variable refinements. No earlier witness is lost. Tests:
// pncx_coloring_small_graphs_match_enumeration, pncx_wheel_core_scale.
pub(super) fn universal(adj: &[Vec<usize>]) -> Option<Vec<usize>> {
    let n = adj.len();
    let v = adj
        .iter()
        .position(|row| row.len().checked_add(1) == Some(n))?;
    let mut colors = vec![None; n];
    colors[v] = Some(2usize);
    for start in 0..n {
        if colors[start].is_some() {
            continue;
        }
        colors[start] = Some(0);
        let mut todo = vec![start];
        while let Some(a) = todo.pop() {
            let next = 1usize.checked_sub(colors[a]?)?;
            for &b in adj.get(a)? {
                if b == v {
                    continue;
                }
                match *colors.get(b)? {
                    Some(c) if c != next => return None,
                    Some(_) => {}
                    None => {
                        colors[b] = Some(next);
                        todo.push(b);
                    }
                }
            }
        }
    }
    colors.into_iter().collect()
}
