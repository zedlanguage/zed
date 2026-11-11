// Lays the plan out with d3-dag's Sugiyama layout, in the shape layout.ts
// gives the page (see Layout there).

import { coordCenter, decrossDfs, graph, layerSeparation, layeringSimplex, sugiyama, twolayerAgg } from "d3-dag";
import { narrow } from "./narrow.ts";
import type { Graph, Layout, Point } from "./layout.ts";

const PAD = 20;
const GAP: [number, number] = [26, 54];

// The Sugiyama operators after layering (layers below), and whether narrow.ts
// places each layer again after d3-dag's coordinates.
export interface Operators { decross: any; coord: any; narrow: boolean }

// Complexity tradeoff, measured on the plan of 2026-11-10 (1,661 nodes, 2,580
// edges; load 19 to 37 on 32 cores) and on the 4,000-node test graph
// (synthetic.ts). Crossings are proper crossings of the drawn polylines.
// - Layering: network simplex (an integer program, under 1.5 s here and about
//   5 s at 4,000 nodes) gives 11,306 px of height and 3,868 dummies. Longest path
//   gives 11,528 px but 11,376 dummies, so every later step is slower and
//   edges run long.
// - Crossing reduction: optimal decrossing (decrossOpt, an integer program
//   over every pair in a layer) did not finish in 60 s. Two-layer sweeps with
//   the greedy order cost about 0.6 s per pass here and 5 s per pass at
//   4,000 nodes; 1, 2, 4 and 24 passes gave 23,397, 21,714, 21,300 and 20,979
//   crossings (narrowed). 4 is past the point where more passes stop paying.
//   The median order (twolayerAgg) gave 22,000 to 24,000 at the same cost.
//   Depth-first order alone gave 62,644.
// - Coordinates: simplex (the d3-dag default, a linear program over nodes and
//   dummies) and quadratic did not finish in 60 s. Greedy took 3 s here and
//   29 s at 4,000 nodes (57,580 px wide here, 218,872 there). Center is
//   linear but leaves edges slanting (36,640 px wide, 8.5 million px of
//   horizontal edge run). So the coordinates come from center and narrow.ts
//   places every layer again within the widest packed layer, as it does for
//   ELK: 33,742 x 11,306 px, 21,300 crossings, 5.5 million px of horizontal
//   edge run, 5.7 s in all, and 27 s at 4,000 nodes. ELK with narrow.ts gave
//   28,725 x 16,792 px, 26,871 crossings, 7.0 million px, 12 s, and 39 s at 4,000.
// - Layers (layers below, 2026-11-11, the author's rule): simplex, every
//   source moved directly above its highest child, nodes moved to the least
//   crowded layer of their slack while that keeps them in a layer with fewer
//   nodes than the one they left, and rows of more than 1.5 times the median
//   count split in two. On the plan of 2026-11-11 (1,690 nodes, 2,617
//   edges) simplex puts 139 nodes in its widest layer, 10 to 19 of its 104
//   hold about half the nodes, and the median layer has 17. Simplex already
//   puts every source directly above its highest child on the plan and the
//   test graphs, so that step moved nothing there. Measured at load 61 to 69
//   on 32 cores, all at once, so the times are rough; rows, the most boxes in
//   a row, the widest row in px, width x height px, crossings of the drawn
//   edges, total edge span in rows, time:
//                                 rows  most  widest  w x h px          cross  span    time
//     plan, before (width rule)    104   56   14,766  14,838 x 11,528  30,154   9,217  14.6 s
//     plan, counts, no split       104   28    9,026   9,178 x 11,602  35,432  21,882   5.4 s
//     plan, counts and split       128   21    6,136   6,364 x 14,146  33,705  28,495   8.1 s
//     500 nodes, before             47   13    3,454   3,660 x  6,128  17,862   4,687   4.1 s
//     500 nodes, counts             47   12    3,524   3,564 x  6,128  19,055   5,432   2.1 s
//     4,000 nodes, before          372   14    4,150   4,198 x 48,698 197,065  48,594  50.9 s
//     4,000 nodes, counts          372   12    4,340   4,508 x 48,698 220,417  72,660  24.1 s
//   "Before" is the width rule this replaces (moves priced by the sum of
//   squared layer widths in px plus edge span, penalty 1, 2026-11-10). No
//   row of the test graphs is long enough to split. On the plan the counts
//   take the widest row from 56 boxes to 21 and the picture from 14,838 px
//   wide to 6,364, for 12 % more crossings and three times the edge span
//   (count balancing moves nodes with no regard to their edges' length).
//   The times fell mostly through the crossing count of decrossSweeps below,
//   not the layering: balanced layers have about three times the pieces of
//   long edges, and d3-dag's count made the plan's layout take 35 s.
// - Edges shortened within full rows (balanceLayers below, the author's
//   spring rule, 2026-11-11), after the count balancing: on the live plan of
//   2026-11-11 (1,682 nodes, 2,650 edges, load 33 to 54) the crossings fell
//   from 32,032 to 30,454 and the edge span from 24,314 to 22,479 rows, at
//   126 rows and at most 27 boxes in a row both; 59 sources that sat more
//   than one row above their highest child with a row with room between now
//   sit as low as a row with room allows (0 left). 1 / (2K + 1), the weight
//   of the counts against the edge lengths, against 1, 1/4 and 1/16: 30,454,
//   31,472, 30,424 and 31,207 crossings, 22,479, 22,673, 22,473 and 22,481
//   rows of span, 0, 21, 3 and 0 such sources.
// - From an earlier layout (Layout.layers, fromPrevious and decrossSeeded
//   below): the layers start from the earlier ones instead of simplex, the
//   order in each layer from the earlier picture, and the layout runs once,
//   after the split. Measured on the live plan of 2026-11-11 (1,682 nodes)
//   and a plan-shaped graph of 4,000, at load 40 to 47 with up to three runs
//   at once, so the times are rough:
//     - From a layout from scratch, one node added: the plan 5.4 s against
//       7.8 s from scratch, 29,810 crossings against 29,984, 134 nodes whose
//       row or place among their row-mates changed; 4,000 nodes 18.4 s
//       against 8.6 s, 179,642 crossings against 195,770. The time is the
//       seeded passes, each removing a few crossings left by the sweeps from
//       scratch (twolayerAgg then greedy swaps), which greedy swaps alone
//       improve on.
//     - From that layout, the same graph: no node moved, the same crossings,
//       2.9 s and 5.6 s. One more node added: 12 of 1,683 nodes moved, 2.3 s,
//       29,818 crossings; 18 of 4,001, 5.0 s, 179,343 crossings. The page
//       lays each graph out from the last layout, so this is the usual case.
//     - With 5 % of the nodes changed (42 removed, 42 added with an edge from
//       and to nodes far apart), from a layout from scratch: 32,069 crossings
//       against 27,857 from scratch (the method before: 35,454 against
//       32,432); the layers keep 104 rows where the fresh layout has 101.
//   A layout from an earlier one depends on it, not only on the graph.
export const operators: Operators = {
  decross: decrossSweeps([decrossDfs().topDown(true), decrossDfs().topDown(false)], 4),
  coord: coordCenter(),
  narrow: true,
};

// Edges to unknown nodes are dropped. d3-dag needs a graph without cycles, so
// a depth-first search in the input order reverses each edge back to a node on
// its path, and that edge is drawn upward, as ELK draws it. Two edges between
// the same pair of nodes (or one each way in a cycle) are laid out once and
// both drawn on that route. An edge from a node to itself is drawn as a loop
// on the node's right side.
// prev is the layering of an earlier layout (Layout.layers), from which the
// layers start instead of network simplex (see layers below), and prevAt its
// boxes' centers, from which the order in each layer starts (decrossSeeded
// below) and each node of a split row keeps the half it was in (splitRows).
export function d3dagLayout(g: Graph, ops: Operators = operators, prev?: Record<string, number>, prevAt?: Record<string, { x: number; y: number }>, prevEdges?: Layout["edges"], prevK?: number): Omit<Layout, "key"> {
  const known = new Map(g.nodes.map((n, i) => [n.id, i]));
  const edges = g.edges.filter(([a, b]) => known.has(a) && known.has(b));
  const out: number[][] = g.nodes.map(() => []);
  for (const [a, b] of edges) if (a !== b) out[known.get(a)!].push(known.get(b)!);
  const back = new Set<string>();
  // 0: not seen, 1: on the path, 2: finished.
  const mark = new Uint8Array(g.nodes.length);
  for (let r = 0; r < g.nodes.length; r++) {
    if (mark[r]) continue;
    const stack: [number, number][] = [[r, 0]];
    mark[r] = 1;
    while (stack.length) {
      const top = stack[stack.length - 1];
      const [v, i] = top;
      if (i === out[v].length) { mark[v] = 2; stack.pop(); continue; }
      top[1]++;
      const w = out[v][i];
      if (mark[w] === 1) back.add(`${v} ${w}`);
      else if (mark[w] === 0) { mark[w] = 1; stack.push([w, 0]); }
    }
  }
  // The pair of nodes an edge is laid out between, top to bottom, and whether it was turned.
  const pair = (a: string, b: string): [number, number, boolean] => {
    const s = known.get(a)!, t = known.get(b)!;
    return back.has(`${s} ${t}`) ? [t, s, true] : [s, t, false];
  };

  const dag = graph<{ id: string; w: number; h: number }, undefined>();
  const nodes = g.nodes.map((n) => dag.node({ id: n.id, w: n.w, h: n.h }));
  const links = new Map<string, any>();
  for (const [a, b] of edges) {
    if (a === b) continue;
    const [s, t] = pair(a, b);
    const k = `${s} ${t}`;
    if (!links.has(k)) links.set(k, dag.link(nodes[s], nodes[t]));
  }
  const index = new Map(nodes.map((n, i) => [n, i]));
  const parents = nodes.map((n) => [...n.parents()].map((p) => index.get(p)!));
  const children = nodes.map((n) => [...n.children()].map((c) => index.get(c)!));
  const { y: balanced, K: rowLimitUsed } = layers(dag, nodes, parents, children, prev, prevK);
  // sugiyama with the layers fixed: d3-dag 1.2.2 calls layering(graph,
  // layerSeparation) and takes the value returned as the last layer's index.
  const run = (y: Int32Array, decross: any) => sugiyama()
    .layering(() => { let last = 0; nodes.forEach((n, i) => { n.y = y[i]; last = Math.max(last, y[i]); }); return last; })
    .decross(decross)
    .coord(ops.coord)
    .nodeSize((n: any) => [n.data.w, n.data.h])
    .gap(GAP)(dag as any);
  const had = (n: any) => prev && prevAt && Object.hasOwn(prevAt, n.data.id) && Object.hasOwn(prev, n.data.id);
  // A piece of a long edge starts where the earlier drawing of that edge
  // crossed its layer's earlier height (the mean y of the layer's nodes), so
  // the seeded order is the earlier picture's order.
  const route = new Map<string, Point[]>();
  for (const e of prevEdges ?? []) {
    const p = e.points;
    if (e.from !== e.to && p.length) route.set(`${e.from} ${e.to}`, p[0].y <= p[p.length - 1].y ? p : [...p].reverse());
  }
  const alongIn = (rows: Int32Array) => {
    if (!prevAt || !prevEdges) return undefined;
    const sum = new Map<number, [number, number]>();
    nodes.forEach((n, i) => { if (had(n)) { const v = sum.get(rows[i]) ?? [0, 0]; v[0] += prevAt[n.data.id].y; v[1]++; sum.set(rows[i], v); } });
    return (s: number, t: number, l: number) => {
      const ids = [nodes[s].data.id, nodes[t].data.id];
      const p = route.get(`${ids[0]} ${ids[1]}`) ?? route.get(`${ids[1]} ${ids[0]}`);
      const h = sum.get(l);
      if (!p || !h) return NaN;
      const yy = h[0] / h[1];
      if (yy < p[0].y || yy > p[p.length - 1].y) return NaN;
      // The first point at or below yy, by binary search: a route has a point
      // in each layer it crosses, so a scan would be O(span) per piece and
      // O(span^2) per edge; this is O(log span) per piece.
      let lo = 1, hi = p.length - 1;
      while (lo < hi) { const mid = (lo + hi) >> 1; if (p[mid].y >= yy) hi = mid; else lo = mid + 1; }
      return p[lo - 1].x + ((yy - p[lo - 1].y) / (p[lo].y - p[lo - 1].y || 1)) * (p[lo].x - p[lo - 1].x);
    };
  };
  const seedX = () => Float64Array.from(nodes, (n) => (had(n) ? prevAt![n.data.id].x : NaN));
  // From an earlier layout the x that splitRows reads is the seeded one (see
  // seedPlaces), and the layout runs once, after the split; from scratch it
  // runs on the unsplit layers first to find x.
  // Complexity tradeoff: a run is a crossing reduction and a placement, about
  // 0.5 s on the plan of 2026-11-11 from a seed; the seeded x costs
  // O(n + m log d).
  let width = 0, height = 0;
  let x: Float64Array;
  if (prevAt) x = seedPlaces(seedX(), parents, children);
  else {
    ({ width, height } = run(balanced, ops.decross));
    x = Float64Array.from(nodes, (n) => n.x);
  }
  // A node in the lower of the two rows its earlier layer was drawn in is 1,
  // in the upper or a row not split 0, and a node with no earlier place -1.
  let half: Int8Array | undefined;
  if (prevAt && prev) {
    const top = new Map<number, number>();
    for (const n of nodes) if (had(n)) top.set(prev[n.data.id], Math.min(top.get(prev[n.data.id]) ?? Infinity, prevAt[n.data.id].y));
    half = Int8Array.from(nodes, (n) => (had(n) ? (prevAt[n.data.id].y > top.get(prev[n.data.id])! ? 1 : 0) : -1));
  }
  const split = splitRows(balanced, x, half);
  // From an earlier layout, the rows after the split start from the earlier
  // picture in the same way, so that a relayout moves few nodes.
  if (prevAt) {
    const rows = split ?? balanced;
    ({ width, height } = run(rows, decrossSeeded(index, x, rows, alongIn(rows))));
  } else if (split) ({ width, height } = run(split, decrossFrom(index, x, split)));

  // Left sides and tops, and each link's route from the source's bottom to
  // the target's top. d3-dag's points run from the source's center to the
  // target's center through one point in each layer between.
  let kids = nodes.map((n) => ({ id: n.data.id, x: n.x - n.data.w / 2, y: n.y - n.data.h / 2, width: n.data.w, height: n.data.h }));
  const routes = new Map<string, Point[]>();
  for (const [k, link] of links) {
    const p: Point[] = link.points.map(([x, y]: [number, number]) => ({ x, y }));
    const [s, t] = k.split(" ").map(Number);
    p[0] = { x: p[0].x, y: kids[s].y + kids[s].height };
    p[p.length - 1] = { x: p[p.length - 1].x, y: kids[t].y };
    routes.set(k, p);
  }
  let w = width;
  if (ops.narrow) {
    // narrow reads an ELK layout: each point in a layer between is a short
    // vertical run through the layer's middle, which it takes for an edge lane.
    const ks = [...links.keys()];
    const placed = narrow({
      children: kids,
      edges: ks.map((k, i) => {
        const [s, t] = k.split(" ").map(Number);
        const p = routes.get(k)!;
        return {
          id: `e${i}`, sources: [kids[s].id], targets: [kids[t].id],
          sections: [{ startPoint: p[0], endPoint: p[p.length - 1], bendPoints: p.slice(1, -1).flatMap((q) => [{ x: q.x, y: q.y - 1 }, { x: q.x, y: q.y + 1 }]) }],
        };
      }),
    });
    kids = placed.children;
    placed.edges.forEach((e, i) => {
      const sec = e.sections![0];
      routes.set(ks[i], [sec.startPoint, ...(sec.bendPoints ?? []), sec.endPoint]);
    });
    w = 0;
    for (const c of kids) w = Math.max(w, c.x + c.width);
    for (const p of routes.values()) for (const q of p) w = Math.max(w, q.x);
  }

  const boxes: Layout["boxes"] = {};
  for (const c of kids) boxes[c.id] = { x: c.x + c.width / 2 + PAD, y: c.y + c.height / 2 + PAD, w: c.width, h: c.height };
  const drawn: Layout["edges"] = [];
  for (const [a, b] of edges) {
    if (a === b) {
      const A = boxes[a], x = A.x + A.w / 2, d = GAP[0] / 2;
      drawn.push({ from: a, to: b, points: [{ x, y: A.y - 8 }, { x: x + d, y: A.y - 8 }, { x: x + d, y: A.y + 8 }, { x, y: A.y + 8 }] });
      continue;
    }
    const [s, t, flip] = pair(a, b);
    const p = routes.get(`${s} ${t}`)!.map((q) => ({ x: q.x + PAD, y: q.y + PAD }));
    if (flip) p.reverse();
    drawn.push({ from: a, to: b, points: p });
  }
  const kept: Record<string, number> = {};
  nodes.forEach((n, i) => { kept[n.data.id] = balanced[i]; });
  return { w: w + 2 * PAD, h: height + 2 * PAD, boxes, edges: drawn, layers: kept, rowLimit: rowLimitUsed };
}

// The layers, top = 0, every edge going down at least one layer, and K, the
// row limit they were balanced at. With no earlier layering, or none of whose
// nodes is still in the graph, they come from network simplex, every source is
// put directly above its highest child (lowerSources), nodes move to less
// crowded layers until none can (balanceCounts), and K is the split rule's
// row limit of those layers (rowLimit). Otherwise they start from the earlier
// layering (fromPrevious), which does the same for added sources only, and K
// is the earlier one, prevK, times the number of nodes over the earlier number
// (prev's size), rounded down: for an unchanged graph the same K. Then nodes
// move to shorten their edges into rows with room (balanceLayers). If that
// leaves the rows' own limit below K, balancing runs again at that limit,
// so no row is over the split rule's limit of the result; and empty layers are
// dropped (compactLayers).
// An unchanged graph keeps its layers: balanceLayers ended on them at K, the
// loop ended with their limit at K or more, and from them K is the same. With
// balanceCounts on the earlier path too, or K taken from the rows each time,
// it did not: on the plan of 2026-11-10 K went 25, 27, 25, 27 ... (moves
// each round) when recomputed from the result, and from an unchanged graph
// 14 nodes moved.
// The result is what Layout.layers keeps, and K Layout.rowLimit; splitRows
// then splits the most crowded rows for the picture only.
// Complexity tradeoff: each round of the loop is one balanceLayers run and K
// falls by at least one per round, so at most K rounds; on the plan, the live
// plan of 2026-11-11 and plan-shaped graphs of 1000 and 4000 nodes it ran
// once. Running balanceLayers at one fixed K would leave rows over the split
// limit whenever the result's median falls.
export function layers(dag: any, nodes: any[], parents: number[][], children: number[][], prev?: Record<string, number>, prevK?: number): { y: Int32Array; K: number } {
  let y = prev ? fromPrevious(nodes.map((n) => (Object.hasOwn(prev, n.data.id) ? prev[n.data.id] : undefined)), parents, children) : null;
  let K: number;
  if (!y) {
    layeringSimplex()(dag, layerSeparation);
    y = Int32Array.from(nodes, (n) => n.y);
    lowerSources(y, parents, children);
    balanceCounts(y, parents, children);
    K = rowLimit(y);
  } else K = prevK === undefined ? rowLimit(y) : Math.max(1, Math.floor((prevK * nodes.length) / Object.keys(prev!).length));
  for (;;) {
    balanceLayers(y, parents, children, K);
    const k = rowLimit(y);
    if (k >= K) break;
    K = k;
  }
  compactLayers(y);
  return { y, K };
}

// Layers for the graph from an earlier layering, old[i] being node i's
// earlier layer or undefined for a node added since; null when no node has
// one. With the earlier top layer as layer 0 and H the larger of the earlier
// number of layers and the number of nodes on the longest path, each node has
// an earliest layer (the nodes on the longest path from a source to it, less
// one) and a latest (H - 1 less the nodes on the longest path from it to a
// sink). Each node's earlier layer is moved into that range, and then, in
// topological order, below its lowest parent if an edge added (or turned)
// since would point up or sideways; that pushes it and, by the same rule, its
// descendants down. An added node starts at its earliest layer. Last, an added
// source goes one layer above its highest child.
// The layers stay within H: a node's layer is at most its latest, as its
// moved earlier layer is, and its parents' layers are at most their latest,
// which are below its own. Without the range an added edge from a deep node to
// a high one pushed the high one's descendants below the deep one: on a
// plan-shaped graph of 4,000 nodes one such edge took 372 layers to 694 (a
// layout from scratch has 372) and the layout from 10 s to 32 s. A valid
// earlier layering of an unchanged graph lies within the range already, so it
// is kept. Removed nodes and edges need nothing: removing one never makes an
// edge point up.
// Complexity tradeoff: O(n + m) for a topological order and three sweeps over
// every edge. A worklist from the added edges alone would touch only the nodes
// pushed down, but finding the added edges (a set difference with the earlier
// graph) is O(n + m) already, and the range needs every longest path, so it
// would not change the order of the cost; the balancing passes after it cost
// O((n + m) log L) each.
export function fromPrevious(old: (number | undefined)[], parents: number[][], children: number[][]): Int32Array | null {
  const n = old.length;
  let top = Infinity, bottom = -Infinity;
  for (const v of old) if (v !== undefined) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  if (top === Infinity) return null;
  const order = new Int32Array(n);
  const waiting = Int32Array.from(parents, (p) => p.length);
  let len = 0;
  for (let i = 0; i < n; i++) if (!waiting[i]) order[len++] = i;
  for (let k = 0; k < len; k++) for (const c of children[order[k]]) if (--waiting[c] === 0) order[len++] = c;
  const early = new Int32Array(n), late = new Int32Array(n);
  let H = bottom - top + 1;
  for (const v of order) for (const c of children[v]) early[c] = Math.max(early[c], early[v] + 1);
  for (const v of order) H = Math.max(H, early[v] + 1);
  late.fill(H - 1);
  for (let k = n - 1; k >= 0; k--) { const v = order[k]; for (const c of children[v]) late[v] = Math.min(late[v], late[c] - 1); }
  const y = new Int32Array(n);
  for (const v of order) {
    const was = old[v];
    let at = was === undefined ? early[v] : Math.min(Math.max(was - top, early[v]), late[v]);
    for (const p of parents[v]) at = Math.max(at, y[p] + 1);
    y[v] = at;
  }
  for (let i = 0; i < n; i++) {
    if (old[i] !== undefined || parents[i].length || !children[i].length) continue;
    let hi = Infinity;
    for (const c of children[i]) hi = Math.min(hi, y[c]);
    y[i] = hi - 1;
  }
  return y;
}

// Puts every source (a node with no parents) one layer above its highest
// child. A source's children are not sources, so moving one source changes no
// other source's place, and one pass in any order gives every source its
// place. A node with neither parents nor children stays where it is.
export function lowerSources(y: Int32Array, parents: number[][], children: number[][]): void {
  for (let i = 0; i < y.length; i++) {
    if (parents[i].length || !children[i].length) continue;
    let hi = Infinity;
    for (const c of children[i]) hi = Math.min(hi, y[c]);
    y[i] = hi - 1;
  }
}

// Moves nodes, one at a time, into the least crowded layer of their slack, the
// layers below their lowest parent and above their highest child within the
// current top and bottom layers, so every edge still goes down and the number
// of layers does not grow. With c[l] the number of nodes in layer l, node i
// moves from layer a to the layer b of its slack with the fewest nodes only
// if c[b] + 1 < c[a]: it then lands in a layer that, with it, still holds
// fewer nodes than the layer it left did. Of several layers with the fewest
// nodes it takes the one that shortens its edges most (the topmost if it has
// more parents than children, the bottommost if fewer), and with as many
// parents as children, the nearest (the upper one of two equally near).
// Each pass takes the nodes of the most crowded layers first, as counted at
// the pass's start, and passes repeat until one moves nothing; it returns the
// number of passes. onMove, if given, sees each move, for tests. Taking the
// nodes in index order instead gave the same widest layers but more total edge
// span: 22,144 against 21,788 layers on the plan of 2026-11-11 and 100,152
// against 68,875 on the 4,000-node test graph.
//
// It ends: a move changes sum c[l]^2 by (c[b] + 1)^2 - c[b]^2 + (c[a] - 1)^2 -
// c[a]^2 = 2 (c[b] - c[a] + 1) <= -2. That sum is an integer between n^2 / L
// and n^2 (n nodes, L layers), so there are at most (S0 - n^2 / L) / 2 moves,
// S0 the sum at the start, and at most one pass more than moves. No pass count
// is set.
//
// Complexity tradeoff: scanning each node's slack costs O(n L) per pass, as
// the slack can span every layer. A segment tree over c answers the least count
// in a range and the first or last layer at or below a count in O(log L), and
// a move updates it in O(log L), so a pass costs O((n + m) log L). The bound on
// moves above is quadratic in n in the worst case (a sum near n^2 when most
// nodes start in one layer), but the passes measured are few: 13 passes and
// 1,936 moves on the plan of 2026-11-10 (1,661 nodes, sum of squares 106,111
// to 32,361), 12 and 1,961 on the plan of 2026-11-11 (1,690 nodes), 3 and 82
// on the plan-shaped graph of 1,000 nodes and 3 and 329 at 4,000. The
// scaling test in d3dag.test.ts times it at 4,000 and 32,000 nodes.
export function balanceCounts(y: Int32Array, parents: number[][], children: number[][], onMove?: (i: number, from: number, to: number) => void): number {
  const n = y.length;
  if (!n) return 0;
  let top = Infinity, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const L = bottom - top + 1;
  const c = new Counts(L);
  for (let i = 0; i < n; i++) c.add(y[i] - top, 1);
  let passes = 0;
  for (let moved = true; moved;) {
    moved = false;
    passes++;
    // The nodes of the most crowded layers first, as counted at the start of
    // the pass, by a counting sort (O(n + L)); in index order within a count.
    const start = new Int32Array(n + 2);
    for (let i = 0; i < n; i++) start[n - c.at(y[i] - top) + 1]++;
    for (let k = 1; k <= n + 1; k++) start[k] += start[k - 1];
    const order = new Int32Array(n);
    for (let i = 0; i < n; i++) order[start[n - c.at(y[i] - top)]++] = i;
    for (const i of order) {
      const a = y[i] - top;
      let lo = 0, hi = L - 1;
      for (const q of parents[i]) lo = Math.max(lo, y[q] - top + 1);
      for (const k of children[i]) hi = Math.min(hi, y[k] - top - 1);
      const m = c.min(lo, hi);
      if (m + 1 >= c.at(a)) continue;
      const d = parents[i].length - children[i].length;
      let b: number;
      if (d > 0) b = c.first(lo, hi, m);
      else if (d < 0) b = c.last(lo, hi, m);
      else {
        const up = a > lo ? c.last(lo, a - 1, m) : -1;
        const down = a < hi ? c.first(a + 1, hi, m) : -1;
        b = up < 0 ? down : down < 0 || a - up <= down - a ? up : down;
      }
      c.add(a, -1);
      c.add(b, 1);
      y[i] = b + top;
      onMove?.(i, a + top, b + top);
      moved = true;
    }
  }
  return passes;
}

// Moves nodes, one at a time, within their slack (the layers below their
// lowest parent and above their highest child, within the current top and
// bottom layers), so every edge still goes down and the number of layers does
// not grow. The author's rule (2026-11-11): each edge pulls its two ends
// together like a spring, so a node with more edges up than down is pulled
// up and one with more down than up is pulled down, by how much the moves
// shorten its edges; a move to a less crowded row is better than one to a
// more crowded row; and no node moves into a full row. With c[l] the number
// of nodes in layer l, a row is full at K nodes (rowLimit below: the split
// rule's 1.5 times the median count), and the moves lower
//   F = (2K + 1) * (sum of edge lengths in layers) + sum over l of c[l]^2.
// Node i, with P parents and C children, from layer a to layer b changes the
// first sum by s (b - a), s = P - C, and the second by 2 (c[b] - c[a] + 1).
// A move must land in a row with room (c[b] <= K - 1) and either leave a full
// row (c[a] > K, where the starting layers can have more than K) or lower F.
// Of the allowed layers it takes the one where F is least; of equals, the
// topmost if s > 0, the bottommost if s < 0 and the nearest if s = 0.
// Since 2 (c[b] - c[a] + 1) <= 2 (K - 1) < 2K + 1 when b has room, any move
// that shortens the edges lowers F, whatever the counts: a source (s = -C)
// moves down to the lowest row with room above its highest child, and a node
// pulled up as far as its slack allows. The counts decide only between moves
// that change the edge lengths equally, as for a node with as many parents as
// children: it moves to the least crowded layer if, with it, that holds fewer
// nodes than the layer it left.
// Each pass takes the nodes of the most crowded layers first, as counted at
// the pass's start, and passes repeat until one moves nothing; it returns the
// number of passes. onMove, if given, sees each move, for tests.
//
// It ends, with no pass count set. Let Q = sum over l of max(0, c[l] - K)^2.
// A move out of a row over K (c[a] > K) lowers Q: into a row with room by
// 2 (c[a] - K) - 1 >= 1; into the least crowded layer, at c[b] >= K with
// c[b] + 1 < c[a], by 2 (c[a] - c[b] - 1) >= 2. Every other move starts in a
// row of at most K and ends in one of at most K, so it leaves Q as it was,
// and it lowers the integer F by at least 1. F lies between 0 and
// F_max = (2K + 1) m (L - 1) + n^2 for m edges, so there are at most Q0 moves
// out of rows over K, at most F_max other moves between two of those, and so
// at most Q0 + (Q0 + 1) F_max moves, with at most one pass more than moves.
// On the plan of 2026-11-11, after balanceCounts, one layer holds 30 nodes at
// K = 27, so Q0 = 9.
// That bound is quadratic or worse in n. The number of passes can be linear in
// n: in the chain of d3dag.test.ts ("a chain of moves"), each pass can move
// only the next node of a chain, as each move frees the row the next one
// needs.
//
// Complexity tradeoff: scanning each node's slack costs O(n L) per pass, as
// the slack can span every layer. A segment tree over c answers the least
// count in a range and the first or last layer at or below a count in
// O(log L), and a move updates it in O(log L); the best layer for a node with
// s != 0 is found by Counts.bestLayer in at most K steps of O(log L). A pass
// then costs O((n + m) log L + n K log L).
export function balanceLayers(y: Int32Array, parents: number[][], children: number[][], K: number, onMove?: (i: number, from: number, to: number) => void, W = 2 * K + 1): number {
  const n = y.length;
  if (!n) return 0;
  let top = Infinity, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const L = bottom - top + 1;
  const c = new Counts(L);
  for (let i = 0; i < n; i++) c.add(y[i] - top, 1);
  let passes = 0;
  for (let moved = true; moved;) {
    moved = false;
    passes++;
    // The nodes of the most crowded layers first, as counted at the start of
    // the pass, by a counting sort (O(n + L)); in index order within a count.
    const start = new Int32Array(n + 2);
    for (let i = 0; i < n; i++) start[n - c.at(y[i] - top) + 1]++;
    for (let k = 1; k <= n + 1; k++) start[k] += start[k - 1];
    const order = new Int32Array(n);
    for (let i = 0; i < n; i++) order[start[n - c.at(y[i] - top)]++] = i;
    for (const i of order) {
      const a = y[i] - top;
      let lo = 0, hi = L - 1;
      for (const q of parents[i]) lo = Math.max(lo, y[q] - top + 1);
      for (const k of children[i]) hi = Math.min(hi, y[k] - top - 1);
      if (lo > hi) continue;
      const s = W * (parents[i].length - children[i].length);
      const ca = c.at(a);
      let b: number;
      if (s === 0) {
        // Only the counts matter: a move needs c[b] + 1 < c[a], which leaves
        // room in b when a is not full.
        const m = c.min(lo, hi);
        if (m + 1 >= ca) continue;
        const up = a > lo ? c.last(lo, a - 1, m) : -1;
        const down = a < hi ? c.first(a + 1, hi, m) : -1;
        b = up < 0 ? down : down < 0 || a - up <= down - a ? up : down;
      } else {
        // f(b) = 2 c[b] + s b, so the change in F is f(b) - f(a) + 2.
        b = c.bestLayer(lo, hi, s, 2, ca > K ? Infinity : 2 * ca + s * a - 2, K - 1);
        if (b < 0 && ca > K) {
          // Out of a full row with no room in the slack: to the least crowded
          // layer if, with it, it holds fewer nodes than a did.
          const m = c.min(lo, hi);
          if (m + 1 < ca) b = s > 0 ? c.first(lo, hi, m) : c.last(lo, hi, m);
        }
        if (b < 0) continue;
      }
      c.add(a, -1);
      c.add(b, 1);
      y[i] = b + top;
      onMove?.(i, a + top, b + top);
      moved = true;
    }
  }
  return passes;
}

// The row-size limit of the author's split rule (splitRows): a row is full
// at floor(1.5 x median) nodes, the median of the counts of the nonempty
// layers of y, the mean of the two middle counts when their number is even.
// Complexity tradeoff: O(n + L log L), sorting the counts; a selection
// algorithm would give O(n + L), a difference of microseconds here.
export function rowLimit(y: Int32Array): number {
  const c = new Map<number, number>();
  for (const v of y) c.set(v, (c.get(v) ?? 0) + 1);
  const s = Int32Array.from(c.values()).sort();
  const L = s.length;
  if (!L) return 1;
  const median = L % 2 ? s[(L - 1) / 2] : (s[L / 2 - 1] + s[L / 2]) / 2;
  return Math.max(1, Math.floor(1.5 * median));
}

// Node counts per layer in a segment tree of minimums.
class Counts {
  private size = 1;
  private t: Int32Array;
  constructor(L: number) {
    while (this.size < L) this.size *= 2;
    this.t = new Int32Array(2 * this.size).fill(0x7fffffff);
    for (let l = 0; l < L; l++) this.t[this.size + l] = 0;
    for (let k = this.size - 1; k > 0; k--) this.t[k] = Math.min(this.t[2 * k], this.t[2 * k + 1]);
  }
  at(l: number): number { return this.t[this.size + l]; }
  add(l: number, d: number): void {
    let k = this.size + l;
    this.t[k] += d;
    for (k >>= 1; k; k >>= 1) this.t[k] = Math.min(this.t[2 * k], this.t[2 * k + 1]);
  }
  // The least count in layers lo..hi.
  min(lo: number, hi: number): number {
    let r = 0x7fffffff;
    for (let a = lo + this.size, b = hi + this.size + 1; a < b; a >>= 1, b >>= 1) {
      if (a & 1) r = Math.min(r, this.t[a++]);
      if (b & 1) r = Math.min(r, this.t[--b]);
    }
    return r;
  }
  // The layer b in lo..hi with at most cap nodes and the least f(b) = w c[b]
  // + s b below `below`, the topmost of equals for s > 0 and the bottommost
  // for s < 0, or -1 if no such f(b) is below it. For s > 0 that layer has fewer nodes than every layer
  // above it in lo..hi (a layer above with as few would have a smaller f), so
  // it is one of the layers where the count, read from lo down, reaches a new
  // least value; for s < 0 likewise read from hi up. Those layers are visited
  // in order, each found by `first` (or `last`) with the largest count that
  // could still bring f below the best so far, T = min(cap, ceil((B - s b) /
  // w) - 1) at the next layer b. Each layer visited has at most T nodes, and
  // the next T is below that layer's count whether or not it improved B, so
  // the counts visited fall strictly: at most cap + 1 visits, each O(log L).
  // Complexity tradeoff: scanning every layer of the slack is O(L) per node
  // and O(n L) per pass, which the whole-spine test in d3dag.test.ts showed
  // growing 87 times at 8n. A segment tree of f for each distinct s would
  // answer in O(log L) but cost O(S log L) per move for S distinct values
  // of s. This walk is O((cap + 1) log L); its worst case needs a node whose
  // slack holds a staircase of layers of cap, cap - 1, ..., 0 nodes.
  bestLayer(lo: number, hi: number, s: number, w: number, below: number, cap: number): number {
    let B = below, best = -1;
    for (let cur = s > 0 ? lo : hi; s > 0 ? cur <= hi : cur >= lo;) {
      const T = Math.min(cap, Math.ceil((B - s * cur) / w) - 1);
      if (T < 0) break;
      const b = s > 0 ? this.first(cur, hi, T) : this.last(lo, cur, T);
      if (b < 0) break;
      const f = w * this.at(b) + s * b;
      if (f < B) { B = f; best = b; }
      cur = s > 0 ? b + 1 : b - 1;
    }
    return best;
  }
  // The first (last) layer in lo..hi with at most m nodes, or -1.
  first(lo: number, hi: number, m: number, k = 1, l = 0, r = this.size - 1): number {
    if (r < lo || l > hi || this.t[k] > m) return -1;
    if (l === r) return l;
    const mid = (l + r) >> 1;
    const left = this.first(lo, hi, m, 2 * k, l, mid);
    return left >= 0 ? left : this.first(lo, hi, m, 2 * k + 1, mid + 1, r);
  }
  last(lo: number, hi: number, m: number, k = 1, l = 0, r = this.size - 1): number {
    if (r < lo || l > hi || this.t[k] > m) return -1;
    if (l === r) return l;
    const mid = (l + r) >> 1;
    const right = this.last(lo, hi, m, 2 * k + 1, mid + 1, r);
    return right >= 0 ? right : this.last(lo, hi, m, 2 * k, l, mid);
  }
}

// Drops empty layers and puts the top layer at 0, keeping the order of the
// layers; returns the number of layers. An edge that went down still goes down.
export function compactLayers(y: Int32Array): number {
  if (!y.length) return 0;
  let top = Infinity, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const to = new Int32Array(bottom - top + 1);
  for (const v of y) to[v - top] = 1;
  let k = 0;
  for (let l = 0; l < to.length; l++) to[l] = to[l] ? k++ : -1;
  for (let i = 0; i < y.length; i++) y[i] = to[y[i] - top];
  return k;
}

// The author's rule (2026-11-11): a row with more than 1.5 times the median
// number of nodes per row is split in two. An empty row goes in directly below
// it, which moves every later row down one, and every other node of the row,
// in its order from left to right (x), moves into it, starting with the
// second; given half (a node's half in an earlier layout, 1 lower, 0 upper,
// -1 none), a node keeps its earlier half, and one with none takes the other
// half from the node to its left, so a relayout does not move every node to
// the right of an added one to the other half. No edge joins two nodes of one row, and every child of a split row's
// node was at least one row below it, so it is now at least two rows below the
// split row and one below the new row: every edge still goes down. The median
// is of the rows of y (compacted, so none is empty), the mean of the two
// middle counts when the number of rows is even. Returns the new rows, or null
// if no row is split. Rows are not split again: the cutoff is the author's,
// for one split of each long row.
// Complexity tradeoff: O(n log n) for sorting the counts and each split row by
// x, against O(n) with a selection algorithm for the median; n log n is
// milliseconds here.
export function splitRows(y: Int32Array, x: ArrayLike<number>, half?: Int8Array): Int32Array | null {
  const n = y.length;
  let L = 0;
  for (const v of y) L = Math.max(L, v + 1);
  const c = new Int32Array(L);
  for (const v of y) c[v]++;
  const sorted = Int32Array.from(c).sort();
  const median = L % 2 ? sorted[(L - 1) / 2] : (sorted[L / 2 - 1] + sorted[L / 2]) / 2;
  const shift = new Int32Array(L);
  let s = 0;
  for (let l = 0; l < L; l++) { shift[l] = s; if (c[l] > 1.5 * median) s++; }
  if (!s) return null;
  const out = new Int32Array(n);
  const rows = new Map<number, number[]>();
  for (let i = 0; i < n; i++) {
    out[i] = y[i] + shift[y[i]];
    if (c[y[i]] > 1.5 * median) {
      let r = rows.get(y[i]);
      if (!r) rows.set(y[i], (r = []));
      r.push(i);
    }
  }
  for (const r of rows.values()) {
    r.sort((p, q) => x[p] - x[q] || p - q);
    let last = 1;
    for (const i of r) {
      last = half && half[i] >= 0 ? half[i] : 1 - last;
      out[i] += last;
    }
  }
  return out;
}

// Crossing reduction for the rows after splitRows, starting from the order of
// the run before the split: each node at its x there, each piece of a long edge
// at the point of the straight line between its ends' x in its row, so the
// rows that were not split start as they were and a split row's halves keep
// their order. Two-layer sweeps then improve on it (SPLIT_PASSES).
const SPLIT_PASSES = 4;
function decrossFrom(index: Map<any, number>, x: Float64Array, y: Int32Array): any {
  const at = (s: any): number => {
    if (s.data.role === "node") return x[index.get(s.data.node)!];
    const a = index.get(s.data.link.source)!, b = index.get(s.data.link.target)!;
    return x[a] + ((s.data.layer - y[a]) / (y[b] - y[a])) * (x[b] - x[a]);
  };
  const start = (rows: any[][]) => {
    for (const row of rows) {
      const k = new Map(row.map((s) => [s, at(s)]));
      row.sort((p, q) => k.get(p)! - k.get(q)!);
    }
  };
  return decrossSweeps([start], SPLIT_PASSES);
}

// Each node's starting x for a layout from an earlier one (the author's rule,
// 2026-11-11): prevX[i] is node i's earlier x, NaN for a node added since. An
// added node starts at the median x of its neighbors already placed, taken in
// breadth-first order from the nodes with an earlier x, so a chain of added
// nodes is placed from its placed end in; one that no placed node reaches goes
// to the right, in index order. Removed nodes are not in the graph, so they
// drop out.
// Complexity tradeoff: O(n + m log d), a sort of each added node's placed
// neighbors for the median; a barycenter (mean) would save the sort but lets
// one far neighbor pull the node across the picture.
export function seedPlaces(prevX: Float64Array, parents: number[][], children: number[][]): Float64Array {
  const n = prevX.length;
  const x = Float64Array.from(prevX);
  // Breadth-first from every node with an earlier x, with a visited set.
  const seen = new Uint8Array(n);
  const queue = new Int32Array(n);
  let len = 0;
  for (let i = 0; i < n; i++) if (!Number.isNaN(x[i])) { seen[i] = 1; queue[len++] = i; }
  let right = -Infinity;
  for (let i = 0; i < n; i++) if (!Number.isNaN(x[i])) right = Math.max(right, x[i]);
  if (right === -Infinity) right = 0;
  for (let k = 0; k < len; k++) {
    const v = queue[k];
    if (Number.isNaN(x[v])) {
      const xs: number[] = [];
      for (const u of parents[v]) if (!Number.isNaN(x[u])) xs.push(x[u]);
      for (const u of children[v]) if (!Number.isNaN(x[u])) xs.push(x[u]);
      xs.sort((p, q) => p - q);
      x[v] = xs.length % 2 ? xs[(xs.length - 1) / 2] : (xs[xs.length / 2 - 1] + xs[xs.length / 2]) / 2;
    }
    for (const u of parents[v]) if (!seen[u]) { seen[u] = 1; queue[len++] = u; }
    for (const u of children[v]) if (!seen[u]) { seen[u] = 1; queue[len++] = u; }
  }
  for (let i = 0; i < n; i++) if (Number.isNaN(x[i])) x[i] = right + 1 + i;
  return x;
}

// Crossing reduction from an earlier layout's order: each node starts at x
// (seedPlaces), each piece of a long edge where along says the earlier drawing
// of its edge crossed its layer, or else on the straight line between its
// ends' x. Each layer is sorted by these, which keeps the earlier
// left-to-right order of the nodes kept. Then passes of greedy adjacent swaps
// (sweeper with no base, so a pass changes the order only where a swap lowers
// the crossings between two layers), each a sweep down and one up, run until a
// pass does not lower the crossings below the fewest seen, and the order with
// the fewest, the seeded one included, is kept: the result never has more
// crossings than the seeded order. No pass count is set: the crossings are a
// nonnegative integer that falls at each pass but the last, so there are at
// most (crossings of the seed) + 1 passes; on the plan of 2026-11-11 a one-node
// change took 22 passes, the last 18 removing one to seven crossings each.
// Complexity tradeoff: the sort is O(N log w) for N pieces; the median order
// (twolayerAgg) as a base would place each layer from the layer above, which
// discards the earlier order and moves most nodes (it is what decrossSweeps
// does from scratch); a pass costs what sweeper's steps cost, and the count
// O(E log w).
export function decrossSeeded(index: Map<any, number>, x: Float64Array, y: Int32Array, along?: (s: number, t: number, l: number) => number): any {
  const at = (s: any): number => {
    if (s.data.role === "node") return x[index.get(s.data.node)!];
    const a = index.get(s.data.link.source)!, b = index.get(s.data.link.target)!;
    const e = along ? along(a, b, s.data.layer) : NaN;
    return Number.isNaN(e) ? x[a] + ((s.data.layer - y[a]) / (y[b] - y[a])) * (x[b] - x[a]) : e;
  };
  return (layers: any[][]) => {
    for (const row of layers) {
      const k = new Map(row.map((s) => [s, at(s)]));
      row.sort((p, q) => k.get(p)! - k.get(q)!);
    }
    let best = crossings(layers), kept = layers.map((l) => l.slice());
    const step = sweeper(layers);
    for (;;) {
      for (let k = 0; k + 1 < layers.length; k++) step(k + 1, true);
      for (let k = layers.length - 1; k > 0; k--) step(k - 1, false);
      const now = crossings(layers);
      if (now >= best) break;
      best = now;
      kept = layers.map((l) => l.slice());
    }
    layers.splice(0, layers.length, ...kept);
  };
}

// d3-dag's decrossTwoLayer, with the crossings counted in O(E log w) instead
// of by its nested loop. For each initial order (inits), up to `passes`
// passes, each a sweep down the layers then one up, each followed by a count
// of crossings; a pass that changes no layer ends that init's passes, and the
// order with the fewest crossings seen, the starting one included, is kept.
// This is d3-dag 1.2.2's algorithm step for step (its function X$), so it gives
// the same orders; only the count differs in cost.
// Complexity tradeoff: d3-dag counts the crossings between two layers by
// comparing every pair of nodes in the upper layer and every pair of their
// children, O(w^2 d^2) for w nodes (and pieces of long edges) per layer of
// degree d; on the plan of 2026-11-11 that count took 34 of 43 s of the layout,
// as balanced layers have about three times the pieces of long edges. Here the
// edges between two layers are sorted by their upper then lower position and
// the crossings are the inversions of the lower positions, counted with a
// Fenwick tree in O(E log w) for E edges (Barth, Juenger and Mutzel 2004).
export function decrossSweeps(inits: ((layers: any[][]) => void)[], passes: number): (layers: any[][]) => void {
  const agg = twolayerAgg();
  return (layers) => {
    let best = crossings(layers), kept = layers.map((l) => l.slice());
    for (const init of inits) {
      init(layers);
      const step = sweeper(layers, agg);
      let changed = true;
      for (let p = 0; p < passes && changed; p++) {
        changed = false;
        for (let k = 0; k + 1 < layers.length; k++) if (step(k + 1, true)) changed = true;
        let now = crossings(layers);
        if (now < best) { best = now; kept = layers.map((l) => l.slice()); }
        for (let k = layers.length - 1; k > 0; k--) if (step(k - 1, false)) changed = true;
        now = crossings(layers);
        if (now < best) { best = now; kept = layers.map((l) => l.slice()); }
      }
    }
    layers.splice(0, layers.length, ...kept);
  };
}

// d3-dag 1.2.2's twolayerGreedy with scan off (its functions M5 and M7), step
// for step, as one two-layer step of a sweep: step(k, true) orders layer k
// against layer k - 1 above it, step(k, false) against layer k + 1 below, and
// returns whether layer k changed. After the base step (if any), in a range of
// the layer it swaps the adjacent pair whose swap removes the most crossings
// (the first such pair on a tie, none if no swap removes any), then does the
// same in the two parts left and right of the swap. The gain of swapping u, v
// is the sum over their neighbors a of u, b of v of sign(pos a - pos b) times
// the two edge counts. The layers' pieces and edges do not change while the
// steps run, only their order.
// Complexity tradeoff: d3-dag forms each pair's gain with a nested loop over
// the two neighbor lists, O(du dv), rebuilding the lists and a map of the
// fixed layer's positions on each call; on the plan of 2026-11-11 that was
// 60 % of a relayout. Here each piece gets an integer id and its neighbors'
// ids once, O(N + E) for N pieces; a step reads the neighbors' positions from
// an array and sorts each list, O(E_k log d) for the E_k edges at layer k,
// and a gain is a merge of the two sorted lists, O(du + dv), kept for the
// later scans that meet the same pair, as d3-dag keeps them. The orders are
// the same.
function sweeper(layers: any[][], base?: (top: any[], bottom: any[], down: boolean) => void): (k: number, down: boolean) => boolean {
  const id = new Map<any, number>();
  for (const l of layers) for (const s of l) id.set(s, id.size);
  const nbr = (s: any, up: boolean): [Int32Array, Float64Array] => {
    const list = [...(up ? s.parentCounts() : s.childCounts())];
    return [Int32Array.from(list, (e: any) => id.get(e[0])!), Float64Array.from(list, (e: any) => e[1])];
  };
  const ups: [Int32Array, Float64Array][] = [], downs: [Int32Array, Float64Array][] = [];
  for (const l of layers) for (const s of l) { ups.push(nbr(s, true)); downs.push(nbr(s, false)); }
  const pos = new Int32Array(id.size);
  const place = (k: number) => layers[k].forEach((s, i) => { pos[id.get(s)!] = i; });
  layers.forEach((_, k) => place(k));
  return (k, down) => {
    const f = down ? k - 1 : k + 1;
    const was = layers[k].slice();
    if (base) {
      if (down) base(layers[f], layers[k], true);
      else base(layers[k], layers[f], false);
    }
    const layer = layers[k];
    const w = layer.length;
    const ids = Int32Array.from(layer, (s) => id.get(s)!);
    // Each piece's neighbors in layer f, as positions sorted, with counts, in
    // two flat arrays: piece i's are at off[i] ..< off[i + 1]. Most pieces are
    // pieces of long edges, with one neighbor and nothing to sort.
    const lists = down ? ups : downs;
    const off = new Int32Array(w + 1);
    for (let i = 0; i < w; i++) off[i + 1] = off[i] + lists[ids[i]][0].length;
    const P = new Float64Array(off[w]), C = new Float64Array(off[w]);
    for (let i = 0; i < w; i++) {
      const [us, cs] = lists[ids[i]];
      const o = off[i];
      if (us.length === 1) { P[o] = pos[us[0]]; C[o] = cs[0]; continue; }
      const order = Array.from(us, (_, q) => q).sort((p, q) => pos[us[p]] - pos[us[q]]);
      order.forEach((q, r) => { P[o + r] = pos[us[q]]; C[o + r] = cs[q]; });
    }
    const known = new Map<number, number>();
    const gain = (iu: number, iv: number) => {
      const key = iu * w + iv;
      const had = known.get(key);
      if (had !== undefined) return had;
      const a0 = off[iu], a1 = off[iu + 1], b0 = off[iv], b1 = off[iv + 1];
      let total = 0, below = 0, j = b0, all = 0;
      for (let q = b0; q < b1; q++) all += C[q];
      for (let i = a0; i < a1; i++) {
        while (j < b1 && P[j] < P[i]) below += C[j++];
        let same = 0;
        for (let q = j; q < b1 && P[q] === P[i]; q++) same += C[q];
        total += C[i] * (below - (all - below - same));
      }
      known.set(key, total);
      return total;
    };
    // The layer as indices into ids, so that the scans read no map.
    const ord = Int32Array.from(ids, (_, i) => i);
    const stack: [number, number][] = [[0, w]];
    for (let r = stack.pop(); r; r = stack.pop()) {
      const [lo, hi] = r;
      if (lo >= hi) continue;
      let most = 0, best = hi;
      for (let i = lo; i < hi - 1; i++) {
        const g = gain(ord[i], ord[i + 1]);
        if (g > most) { most = g; best = i; }
      }
      if (best !== hi) {
        const s = ord[best + 1];
        ord[best + 1] = ord[best];
        ord[best] = s;
        stack.push([lo, best + 1], [best + 1, hi]);
      }
    }
    const before = layer.slice();
    for (let i = 0; i < w; i++) layer[i] = before[ord[i]];
    place(k);
    return layer.some((s, q) => was[q] !== s);
  };
}

// Crossings between each two adjacent layers, each edge counted with its
// multiplicity, as d3-dag counts them.
export function crossings(layers: any[][]): number {
  let total = 0;
  for (let k = 0; k + 1 < layers.length; k++) {
    const below = new Map(layers[k + 1].map((s, i) => [s, i]));
    const w = layers[k + 1].length;
    const tree = new Float64Array(w + 1);
    let seen = 0;
    for (const s of layers[k]) {
      const out: [number, number][] = [];
      for (const [c, n] of s.childCounts()) out.push([below.get(c)!, n]);
      out.sort((a, b) => a[0] - b[0]);
      // Edges of earlier upper nodes ending right of c cross this one; edges
      // of the same node do not, so they are added after all are counted.
      for (const [c, n] of out) {
        let atMost = 0;
        for (let i = c + 1; i > 0; i -= i & -i) atMost += tree[i];
        total += n * (seen - atMost);
      }
      for (const [c, n] of out) {
        for (let i = c + 1; i <= w; i += i & -i) tree[i] += n;
        seen += n;
      }
    }
  }
  return total;
}
