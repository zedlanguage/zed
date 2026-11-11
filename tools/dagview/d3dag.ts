// Lays the plan out with d3-dag's Sugiyama layout, in the shape layout.ts
// gives the page (see Layout there).

import { coordCenter, decrossDfs, graph, layerSeparation, layeringSimplex, sugiyama, twolayerAgg, twolayerGreedy } from "d3-dag";
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
// - From an earlier layout (Layout.layers, fromPrevious below): the layers
//   start from the earlier ones instead of simplex, which saves the simplex
//   time (about 0.5 s on the plan, 5 s at 4,000 nodes); crossing reduction
//   and coordinates, most of the time, run in full. One added edge at 4,000
//   nodes, load 35 to 39: 10.6 s against 12.1 s from scratch for an edge
//   that changes no layer, 7.4 s against 12.3 s for one from the deepest node
//   to a high one, both with 372 rows and within 0.5 % of the crossings; at
//   500 nodes 0.5 s against 0.7 s and 0.7 s against 0.9 s. A layout from the
//   earlier layers depends on them, not only on the graph.
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
// layers start instead of network simplex (see layers below).
export function d3dagLayout(g: Graph, ops: Operators = operators, prev?: Record<string, number>): Omit<Layout, "key"> {
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
  const balanced = layers(dag, nodes, parents, children, prev);
  // sugiyama with the layers fixed: d3-dag 1.2.2 calls layering(graph,
  // layerSeparation) and takes the value returned as the last layer's index.
  const run = (y: Int32Array, decross: any) => sugiyama()
    .layering(() => { let last = 0; nodes.forEach((n, i) => { n.y = y[i]; last = Math.max(last, y[i]); }); return last; })
    .decross(decross)
    .coord(ops.coord)
    .nodeSize((n: any) => [n.data.w, n.data.h])
    .gap(GAP)(dag as any);
  let { width, height } = run(balanced, ops.decross);
  const x = Float64Array.from(nodes, (n) => n.x);
  const split = splitRows(balanced, x);
  if (split) ({ width, height } = run(split, decrossFrom(index, x, split)));

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
  return { w: w + 2 * PAD, h: height + 2 * PAD, boxes, edges: drawn, layers: kept };
}

// The layers, top = 0, every edge going down at least one layer. With no
// earlier layering, or none of whose nodes is still in the graph, they come
// from network simplex, and every source is put directly above its highest
// child (lowerSources); otherwise they start from the earlier layering
// (fromPrevious), which does the same for added sources only, so that an
// unchanged graph keeps its layers. Then nodes move to less crowded layers
// until none can (balanceCounts) and empty layers are dropped (compactLayers).
// The result is what Layout.layers keeps; splitRows then splits the most
// crowded rows for the picture only.
export function layers(dag: any, nodes: any[], parents: number[][], children: number[][], prev?: Record<string, number>): Int32Array {
  let y = prev ? fromPrevious(nodes.map((n) => (Object.hasOwn(prev, n.data.id) ? prev[n.data.id] : undefined)), parents, children) : null;
  if (!y) {
    layeringSimplex()(dag, layerSeparation);
    y = Int32Array.from(nodes, (n) => n.y);
    lowerSources(y, parents, children);
  }
  balanceCounts(y, parents, children);
  compactLayers(y);
  return y;
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
// second. No edge joins two nodes of one row, and every child of a split row's
// node was at least one row below it, so it is now at least two rows below the
// split row and one below the new row: every edge still goes down. The median
// is of the rows of y (compacted, so none is empty), the mean of the two
// middle counts when the number of rows is even. Returns the new rows, or null
// if no row is split. Rows are not split again: the cutoff is the author's,
// for one split of each long row.
// Complexity tradeoff: O(n log n) for sorting the counts and each split row by
// x, against O(n) with a selection algorithm for the median; n log n is
// milliseconds here.
export function splitRows(y: Int32Array, x: ArrayLike<number>): Int32Array | null {
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
    for (let k = 1; k < r.length; k += 2) out[r[k]]++;
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
  const order = twolayerGreedy().base(twolayerAgg());
  return (layers) => {
    let best = crossings(layers), kept = layers.map((l) => l.slice());
    for (const init of inits) {
      init(layers);
      let changed = true;
      for (let p = 0; p < passes && changed; p++) {
        changed = false;
        for (let k = 0; k + 1 < layers.length; k++) {
          const was = layers[k + 1].slice();
          order(layers[k], layers[k + 1], true);
          if (layers[k + 1].some((s, q) => was[q] !== s)) changed = true;
        }
        let now = crossings(layers);
        if (now < best) { best = now; kept = layers.map((l) => l.slice()); }
        for (let k = layers.length - 1; k > 0; k--) {
          const was = layers[k - 1].slice();
          order(layers[k - 1], layers[k], false);
          if (layers[k - 1].some((s, q) => was[q] !== s)) changed = true;
        }
        now = crossings(layers);
        if (now < best) { best = now; kept = layers.map((l) => l.slice()); }
      }
    }
    layers.splice(0, layers.length, ...kept);
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
