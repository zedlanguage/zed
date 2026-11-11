// Lays the plan out with d3-dag's Sugiyama layout, in the shape layout.ts
// gives the page (see Layout there).

import { coordCenter, decrossTwoLayer, graph, layeringSimplex, sugiyama } from "d3-dag";
import { narrow } from "./narrow.ts";
import type { Graph, Layout, Point } from "./layout.ts";

const PAD = 20;
const GAP: [number, number] = [26, 54];

// The three Sugiyama operators, and whether narrow.ts places each layer again
// after d3-dag's coordinates.
export interface Operators { layering: any; decross: any; coord: any; narrow: boolean }

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
// - Rebalancing (layeringBalanced below, measured 2026-11-10 at load 60 to 80;
//   layers 10 to 19 of simplex's 104 held about half the boxes, up to 139 in
//   one). Width x height px, crossings, horizontal edge run, total edge span
//   in layers, and the widest layer in boxes:
//     simplex alone              33,742 x 11,306  21,300  5.5 M   6,448  139
//     Gansner et al.'s balance   33,112 x 11,306  21,637  5.3 M   6,448  134
//     penalty 8                  32,040 x 11,380  22,237  4.9 M   6,570  129
//     penalty 4                  25,124 x 11,380  25,403  4.7 M   7,287   99
//     penalty 2                  18,162 x 11,454  31,418  4.4 M   8,340   70
//     penalty 1                  14,962 x 11,528  29,586  4.1 M   9,058   56
//     penalty 0.5                13,326 x 11,602  30,358  4.0 M   9,575   48
//     penalty 0                   8,864 x 11,898  35,063  4.5 M  22,168   26
//   Penalty 1 is where the curve bends: from 4 to 1 the picture loses 10,000
//   px of width for about 4,000 more crossings, from 1 to 0.5 only 1,600 px.
//   Penalty 0 nearly triples the span and took 51 s. Eight decrossing passes
//   instead of four took three times as long for 28,467 crossings at penalty 1.
//   Crossings do not fall steadily with the penalty (penalty 2 has more than
//   1); the two-layer sweeps are heuristic. Layering with rebalancing took 0.7
//   to 2.4 s, simplex alone 0.7 to 2.3 s. Nikolov and Tarassov's promote
//   layering only makes moves that cut the number of dummies, and simplex
//   already has the fewest, so it would change nothing here.
export const operators: Operators = {
  layering: layeringBalanced(1),
  decross: decrossTwoLayer().passes(4),
  coord: coordCenter(),
  narrow: true,
};

// Edges to unknown nodes are dropped. d3-dag needs a graph without cycles, so
// a depth-first search in the input order reverses each edge back to a node on
// its path, and that edge is drawn upward, as ELK draws it. Two edges between
// the same pair of nodes (or one each way in a cycle) are laid out once and
// both drawn on that route. An edge from a node to itself is drawn as a loop
// on the node's right side.
export function d3dagLayout(g: Graph, ops: Operators = operators): Omit<Layout, "key"> {
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
  const { width, height } = sugiyama()
    .layering(ops.layering)
    .decross(ops.decross)
    .coord(ops.coord)
    .nodeSize((n: any) => [n.data.w, n.data.h])
    .gap(GAP)(dag as any);

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
  return { w: w + 2 * PAD, h: height + 2 * PAD, boxes, edges: drawn };
}

// A layering for d3-dag's sugiyama: network simplex, then rebalance below,
// which moves nodes out of the widest layers. It reads the box widths from the
// node data and assumes d3-dag's own layer separation, one layer between a node
// and its child, which sugiyama passes (d3-dag 1.2.2 calls
// layering(graph, layerSeparation) and takes the value returned as the last
// layer's index).
export function layeringBalanced(penalty: number) {
  const simplex = layeringSimplex();
  return (dag: any, sep: any): number => {
    simplex(dag, sep);
    const nodes: any[] = [...dag.nodes()];
    const index = new Map(nodes.map((n, i) => [n, i]));
    const y = Int32Array.from(nodes, (n) => n.y);
    const box = Int32Array.from(nodes, (n) => Math.round(n.data.w) + GAP[0]);
    const parents = nodes.map((n) => [...n.parents()].map((p: any) => index.get(p)!));
    const children = nodes.map((n) => [...n.children()].map((c: any) => index.get(c)!));
    rebalance(y, box, parents, children, GAP[0], penalty);
    let top = Infinity, bottom = 0;
    for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
    nodes.forEach((n, i) => { n.y = y[i] - top; });
    return bottom - top;
  };
}

// Moves nodes between layers, one at a time, each within its slack: below its
// lowest parent and above its highest child, so every edge still goes down at
// least one layer and the number of layers stays the same. B[l] is the width
// in px of the boxes in layer l, each with the gap after it, and S is the
// total edge span in layers. A node moves to the layer in its slack where
//   Phi = sum over layers of B[l]^2 + p * S,  p = round(penalty * 2 * lane * mean B),
// is lowest, if that is lower than where it is. The sum of squares falls when a
// box leaves a wide layer for a narrower one; p prices one layer of added span
// as one edge lane (lane px) added to a layer of mean width. Phi is a
// non-negative integer that every move lowers by at least 1, so the passes
// end, at the first pass that moves nothing; no pass count or width bound is
// set.
//
// The lanes are left out of B on purpose. With them in, a box leaving a
// crowded layer adds a lane per edge through the crowded layers next to it, so
// each single move looked worse than staying, and the search stopped with the
// widest layer at 30,114 px of 36,626 on the plan of 2026-11-10; with them out
// it went to 21,056 px (lanes counted) and the picture from 33,742 to 14,972 px
// wide (see operators above).
//
// Complexity tradeoff: a move changes two layers, so its change in Phi is
// 2 * box * (B[to] - B[from] + box) + p * (parents - children) * (to - from),
// O(1) for each layer in the slack, and a pass costs O(n + m + total slack).
// Finding the layering of least width outright is NP-hard; moving one node with
// the rest fixed is the step of Gansner et al.'s balancing, which moves only
// nodes whose span does not change, by node count, in one pass.
export function rebalance(y: Int32Array, box: Int32Array, parents: number[][], children: number[][], lane: number, penalty: number): void {
  const n = y.length;
  if (!n) return;
  let layers = 0;
  for (const v of y) layers = Math.max(layers, v + 1);
  const B = new Float64Array(layers);
  let total = 0;
  for (let i = 0; i < n; i++) { B[y[i]] += box[i]; total += box[i]; }
  const p = Math.round(penalty * 2 * lane * (total / layers));
  for (let moved = true; moved;) {
    moved = false;
    for (let i = 0; i < n; i++) {
      let lo = 0, hi = layers - 1;
      for (const q of parents[i]) lo = Math.max(lo, y[q] + 1);
      for (const c of children[i]) hi = Math.min(hi, y[c] - 1);
      const a = y[i], w = box[i], net = p * (parents[i].length - children[i].length);
      let best = 0, to = a;
      for (let b = lo; b <= hi; b++) {
        if (b === a) continue;
        const delta = 2 * w * (B[b] - B[a] + w) + net * (b - a);
        if (delta < best) { best = delta; to = b; }
      }
      if (to === a) continue;
      B[a] -= w; B[to] += w; y[i] = to;
      moved = true;
    }
  }
}
