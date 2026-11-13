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
// - Sources pinned (2026-11-11, the author's rule: a source sits directly
//   above its highest child, never higher). balanceCounts and balanceLayers
//   moved sources like other nodes, up into emptier rows, and the earlier path
//   lowered only added sources, so in the final layers of the live plan of
//   2026-11-11 (1,707 nodes, 2,693 edges) 141 of 327 sources sat more than one
//   layer above their highest child (up to 22), and 173 in the drawn rows (up
//   to 45). Now (until 2026-11-13, see below) no balancing pass moves a source; lowerSources places them
//   after balanceCounts; balanceLayers leaves alone a source's only highest
//   child; and spreadSources moves a source together with its only highest
//   child out of a row over K. Old and new run at once, load 24 to 26, so the
//   times are rough; source gaps (largest), drawn rows, most boxes in a drawn
//   row, width x height px, crossings of the drawn edges, time:
//                           gaps     rows  most  w x h px          cross   time
//     live, before        141 (22)   135   25    6,190 x 14,296  31,220  3.1 s
//     live, after           0        113   30    8,104 x 11,964  26,275  2.7 s
//     plan, before        130 (23)   104   27    8,862 x 11,824  29,598  1.8 s
//     plan, after           0        105   28    8,756 x 11,930  25,983  2.6 s
//     4,000 nodes, before   0        372   15    4,444 x 48,698 196,145  8.1 s
//     4,000 nodes, after    0        372   15    4,594 x 48,698 200,045  8.3 s
//   The most boxes in a drawn row rise on the live plan from 25 to 30: 27
//   sources have SCALE-cover as their only child, so any layout under the rule
//   puts them in one row, and 3 over L1.41-harness sit in the same layer.
//   Crossings fall by 16 % on the live plan, as no source pulls long edges up,
//   and rise by 2 % on the 4,000-node graph. With sources pinned and nothing
//   else, the most boxes in a drawn row were 37 on the live plan; spreadSources
//   brought it to 30. Spreading once after the loop instead of inside it
//   broke the fixed point: an unchanged graph moved 1,400 of 1,661 nodes.
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
// - Wide rows staggered (2026-11-13, the author's rule: when a row is wide,
//   moving a node to a less full row comes before the spring of its edges,
//   at a cost growing with the square of the excess). The live plan of
//   2026-11-13 (2,077 nodes, 3,193 edges) had a drawn row of 52 boxes from
//   scratch, and 83 in the page's saved layout, whose K had fallen to 11 (see
//   layers). Now balanceLayers moves sources out of rows over K, as Q, the
//   sum of squared excesses, is lowered before F; makeRoom inserts the rows
//   they go to directly above the row they leave; and K from an earlier
//   layout is rounded to the nearest. Three methods were compared, each from
//   scratch, run several at once at load 36 to 51, so the times are rough:
//   (1) this one, (2) the pinned sources of a row over K dealt round-robin
//   over the ceil(c / K) rows above their child, after the loop, (3) the
//   split rule's limit lowered from 1.5 to 1 times the median. Drawn rows,
//   most boxes in a drawn row (most nodes in a layer), w x h px, crossings of
//   the drawn edges, edge span in layers, time:
//                          rows  most       w x h px          cross   span    time
//     live 13, before       138  52 (56)  14,470 x 15,206  35,112  20,014   7.4 s
//     live 13, (1)          139  27 (27)   8,962 x 15,312  33,379  25,165   4.4 s
//     live 13, (2)          135  36 (63)  11,148 x 14,962  35,913  20,248  10.3 s
//     live 13, (3)          154  52 (56)  14,542 x 16,828  36,697  21,587  10.9 s
//     plan, before          105  28 (32)   8,756 x 11,930  25,983  15,620   6.0 s
//     plan, (1)             117  24 (24)   7,638 x 13,202  22,900  17,266   3.6 s
//     plan, (2)             112  27 (36)   8,032 x 12,672  25,092  15,742   8.1 s
//     plan, (3)             141  28 (32)   8,828 x 15,820  25,314  17,945   8.6 s
//     live 11, before       113  30 (37)   8,914 x 12,630  26,373  16,774   5.8 s
//     live 11, (1)          125  25 (25)   7,702 x 13,902  25,021  17,885   3.4 s
//     500 nodes, all but (3) 47  15 (15)   3,600 x  6,128  18,084   4,977   1.0 to 1.7 s
//     500 nodes, (3)         50  11 (14)   3,520 x  6,446  18,784   5,395   2.0 s
//     4,000 nodes, before   372  15 (15)   4,594 x 48,698 200,045  53,645  12.0 s
//     4,000 nodes, (1)      376  15 (15)   4,660 x 49,122 200,982  53,904   9.7 s
//     4,000 nodes, (2)      372  15 (15)   4,594 x 48,698 200,045  53,645  14.2 s
//     4,000 nodes, (3)      378  11 (13)   4,000 x 49,218 210,488  55,127  18.2 s
//   (2) moves sources into rows already full (a layer of 63); (3) splits more
//   rows but cannot split a row of pinned sources further (splitRows splits
//   once). (1) leaves no layer over K on these graphs, takes the live plan
//   from 14,470 px wide to 8,962 at the same height, and has fewer crossings,
//   for 26 % more edge span; raised sources sit at most 3 layers above their
//   child (70 of them on live 13). Inserting the rooms only above the top
//   layer instead gave the same widest row within one (28), but 124 rows,
//   52,362 crossings, and sources up to 32 layers above their child. Letting
//   sources move with no room inserted left the 25 top layers of live 13 at
//   35 or 36 nodes. The saved layout of live 13 at K = 11 is discarded, as
//   METHOD in layout.ts changed.
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
  // Draws layers balanced at row limit rowLimitUsed, seeded from the earlier
  // layout or from scratch.
  const draw = (balanced: Int32Array, rowLimitUsed: number, seeded: boolean): Omit<Layout, "key"> => {
    // From an earlier layout the x that splitRows reads is the seeded one (see
    // seedPlaces), and the layout runs once, after the split; from scratch it
    // runs on the unsplit layers first to find x.
    // Complexity tradeoff: a run is a crossing reduction and a placement, about
    // 0.5 s on the plan of 2026-11-11 from a seed; the seeded x costs
    // O(n + m log d).
    let width = 0, height = 0;
    let x: Float64Array;
    if (seeded) x = seedPlaces(seedX(), parents, children);
    else {
      ({ width, height } = run(balanced, ops.decross));
      x = Float64Array.from(nodes, (n) => n.x);
    }
    // A node in the lower of the two rows its earlier layer was drawn in is 1,
    // in the upper or a row not split 0, and a node with no earlier place -1.
    let half: Int8Array | undefined;
    if (seeded) {
      const top = new Map<number, number>();
      for (const n of nodes) if (had(n)) top.set(prev![n.data.id], Math.min(top.get(prev![n.data.id]) ?? Infinity, prevAt![n.data.id].y));
      half = Int8Array.from(nodes, (n) => (had(n) ? (prevAt![n.data.id].y > top.get(prev![n.data.id])! ? 1 : 0) : -1));
    }
    const split = splitRows(balanced, x, half, parents, children);
    // From an earlier layout, the rows after the split start from the earlier
    // picture in the same way, so that a relayout moves few nodes.
    if (seeded) {
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
  };

  // From an earlier layout with its K, the layers at that K (see layers) are
  // drawn from the earlier picture and kept if the drawing is within BAND and
  // the rows within ROOM of what the graph needs, so an unchanged graph keeps
  // its layout and a small change moves few nodes. Otherwise, and with no earlier layout, the graph is laid out from
  // scratch at the K fitLayers chooses, and drawn; while the drawing is
  // outside BAND, e (the drawn w/h over the estimate, shapeOf) corrects the
  // estimate and fitLayers chooses again. It stops at a K already drawn, or
  // when the estimate says the new K would come no nearer the band than the
  // best drawing so far (as for a graph whose longest path is too long for
  // the band), and keeps the drawing nearest the band (distance from it,
  // measured as a ratio; of equals the earlier). There are at most as many
  // drawings as values of K; from scratch the plans of 2026-11-10, 11 and 13
  // and the plan-shaped graphs of 500 and 4,000 nodes each took one.
  // The earlier layers are never kept outside the band: before, the rows
  // only grew (fromPrevious keeps at least the earlier number of layers) and K
  // only fell (see layersAt), so the page's relayouts drew the live plan
  // taller each time (1:21 on 2026-11-13). From scratch the rows can shrink
  // back toward the longest path.
  const size = sizesOf(nodes);
  const ratio = (l: Omit<Layout, "key">) => l.w / l.h;
  const old = prev ? fromPrevious(nodes.map((n) => (Object.hasOwn(prev, n.data.id) ? prev[n.data.id] : undefined)), parents, children) : null;
  let best: Omit<Layout, "key"> | undefined, e = 1;
  let base: Int32Array | undefined;
  const scratch = () => (base ??= scratchLayers(dag, nodes, parents, children));
  if (old) {
    const { y, K } = prevK === undefined ? fitLayers(old, size, parents, children, 1) : { K: scaledK(prevK, nodes.length, prev!), y: layersAt(old, parents, children, scaledK(prevK, nodes.length, prev!)) };
    const R = counts(y).length;
    if (R <= ROOM * pathNodes(parents, children) || R <= ROOM * counts(fitLayers(scratch(), size, parents, children, 1).y).length) {
      best = draw(y, K, !!prevAt);
      if (!outside(ratio(best))) return best;
    }
  }
  scratch();
  const drawnAt = new Set<number>();
  for (;;) {
    const f = fitLayers(base!, size, parents, children, e);
    if (drawnAt.has(f.K) || (best && outside(f.ratio) >= outside(ratio(best)))) break;
    drawnAt.add(f.K);
    const l = draw(f.y, f.K, false);
    if (!best || outside(ratio(l)) < outside(ratio(best))) best = l;
    if (!outside(ratio(l))) break;
    e = ratio(l) / (f.ratio / e);
  }
  return best!;
}

// The most rows an earlier layering keeps, as a multiple of the rows the
// graph needs: the larger of its longest path (in nodes) and the rows of a
// layout from scratch at the K fitLayers chooses. fromPrevious never gives
// rows back (it keeps at least the earlier number), so without this bound the
// rows grow with each relayout while the drawing stays in BAND: on the
// plan-shaped graph of 500 nodes 48 rows became 60 in 20 relayouts (longest
// path 46), its edges longer by as much. 1.25 is the bound the task set
// (row count at most 1.25 x the longest path, or the count the shape needs);
// it leaves room for the earlier layers to hold while nodes come and go.
const ROOM = 1.25;

// The number of nodes on the longest path, by a topological order.
// Complexity: O(n + m).
function pathNodes(parents: number[][], children: number[][]): number {
  const n = parents.length;
  const waiting = Int32Array.from(parents, (p) => p.length), depth = new Int32Array(n).fill(1), order: number[] = [];
  for (let i = 0; i < n; i++) if (!waiting[i]) order.push(i);
  let most = 0;
  for (let k = 0; k < order.length; k++) {
    const v = order[k];
    most = Math.max(most, depth[v]);
    for (const c of children[v]) { depth[c] = Math.max(depth[c], depth[v] + 1); if (--waiting[c] === 0) order.push(c); }
  }
  return most;
}

// How far w/h r lies outside BAND, as a ratio: 0 inside, log(BAND[0] / r)
// below and log(r / BAND[1]) above, so that 1:5 and 2:1 (a factor of two
// from the band's ends) count alike.
function outside(r: number): number {
  return Math.max(0, Math.log(BAND[0] / r), Math.log(r / BAND[1]));
}

// The shape the author asked for (2026-11-13): "find some sort of constraint
// that forces the DAG into an approximately 1:2 w:h ratio", and then "1:2.5 is
// also acceptable". So the drawn width over height (Layout.w / Layout.h) is
// held to [0.4, 0.6], and 0.4 counts as fully inside, not as its edge. A
// layout outside the band is corrected toward 1:2 (TARGET); one inside it is
// kept, and rows are never inserted only to move w/h from 0.4 toward 0.5.
// Within the band fewer rows would be better still (shorter edges, fewer
// crossings), but finding the largest K within it took probes growing with
// log K (see fitLayers), so the first K found within it is kept. A graph
// whose longest path alone makes it taller than 1:2.5 is drawn with the
// fewest rows the layering gives (the nearest shape it can reach).
export const BAND: [number, number] = [0.4, 0.6];
const TARGET = 0.5;

// The layers, top = 0, every edge going down at least one layer, every source
// (no parents, some children) exactly one layer above its highest child unless
// that layer holds K nodes, and K, the row limit they were balanced at.
// From an earlier layering with its K (prev, prevK) they start from it
// (fromPrevious, which puts an added source directly above its highest
// child), at K = prevK times the number of nodes over the earlier number,
// rounded to the nearest: for an unchanged graph the same layers and K.
// Otherwise they start from base layers (scratchLayers, or fromPrevious when
// prev comes without a K) and K is chosen for the shape (fitLayers).
// d3dagLayout then draws them and, if the drawing is outside BAND, lays the
// graph out from scratch with K corrected by the drawn shape.
export function layers(dag: any, nodes: any[], parents: number[][], children: number[][], prev?: Record<string, number>, prevK?: number, work?: Work): { y: Int32Array; K: number } {
  const old = prev ? fromPrevious(nodes.map((n) => (Object.hasOwn(prev, n.data.id) ? prev[n.data.id] : undefined)), parents, children, work) : null;
  if (old && prevK !== undefined) {
    const K = scaledK(prevK, nodes.length, prev!);
    return { y: layersAt(old, parents, children, K, work), K };
  }
  const base = old ?? scratchLayers(dag, nodes, parents, children, work);
  const { y, K } = fitLayers(base, sizesOf(nodes), parents, children, 1, work);
  return { y, K };
}

// The earlier row limit for n nodes: prevK times n over the earlier number of
// nodes, rounded to the nearest, so a one-node change keeps K both ways (it
// was rounded down until 2026-11-13, and each removed and re-added node took
// one off it).
function scaledK(prevK: number, n: number, prev: Record<string, number>): number {
  return Math.max(1, Math.round((prevK * n) / Object.keys(prev).length));
}

// Box widths and heights by node index.
function sizesOf(nodes: any[]): { w: Float64Array; h: Float64Array } {
  return { w: Float64Array.from(nodes, (n) => n.data.w), h: Float64Array.from(nodes, (n) => n.data.h) };
}

// Layers from scratch, before any row limit: network simplex, then nodes other
// than sources moved to less crowded layers until none can (balanceCounts),
// then every source put directly above its highest child (lowerSources).
// None of it depends on K, so fitLayers tries every K from the same base.
export function scratchLayers(dag: any, nodes: any[], parents: number[][], children: number[][], work?: Work): Int32Array {
  // network simplex is d3-dag's and its steps are not counted.
  layeringSimplex()(dag, layerSeparation);
  const y = Int32Array.from(nodes, (n) => n.y);
  balanceCounts(y, parents, children, undefined, work);
  lowerSources(y, parents, children, work);
  return y;
}

// The layers at row limit K from base (left as it is): makeRoom inserts empty
// layers above each row over K, then, until neither moves a node, nodes move
// to less full rows and to shorten their edges into rows with room
// (balanceLayers) and sources move with their only highest child out of rows
// over K (spreadSources); last, empty layers are dropped (compactLayers),
// which keeps the order of the layers.
// The two rules of the author's and how they meet (see balanceLayers): a
// source sits directly above its highest child (2026-11-11), and a row over K
// sheds nodes into less full rows before any edge is shortened (2026-11-13).
// The second overrides the first only for rows over K. A source leaves the
// row above its child only to leave a row over K, for a row with room further
// up, and the spring of its edge brings it back down whenever a row nearer
// its child has room; spreadSources moves a source only with its only
// highest child. balanceLayers never moves a source's only highest child
// (another highest child may move, as one stays), and a child moving up to
// the layer below a source becomes one of its highest children.
// lowerSources runs only from scratch: on the earlier path it would put back
// every source that left a row over K, refilling that row, and the passes
// would then move different sources out of it, so an unchanged graph would
// not keep its layers. A source whose child moved since is brought down by
// balanceLayers instead, as far as rows with room allow.
// An unchanged graph keeps its layers: they are a fixed point at their K,
// balanceLayers and spreadSources each making no move, and makeRoom inserts
// nothing where no row is over K. With balanceCounts on the earlier path too
// it did not: from an unchanged graph 14 nodes moved.
// Until 2026-11-13 a second, outer loop lowered K to the split rule's limit
// of the result (1.5 x the median count, rowLimit) and ran again whenever
// that was below K. The rows makeRoom inserts lower the median, so K only
// fell, and the next layout started from that K: on the live plan K went
// from 27 to 4 over the page's relayouts, 774 rows against a longest path of
// 114, 3,868 x 82,548 px (w/h 0.047), edge spans median 8, 90th percentile
// 181 and max 703 rows. Its only purpose was to keep rows under the split
// limit; K now comes from the shape, so the loop is gone.
// Complexity tradeoff: the loop alternates balanceLayers and spreadSources
// (see each for its cost) and ends as both lower the same (Q, F) (see
// spreadSources); makeRoom is O(n + L) and inserts at most n / K layers. Each
// call ends where it can move nothing, so the loop stops at the first call
// after the first that moves nothing (returns 1); until
// DAGVIEW-spread-scaling it ran pairs until a pair moved nothing, one call
// more, which changes no layer. Measured then, on the plan and the live plan
// of 2026-11-11 the loop ran 4 pairs in all, with 11 passes of balanceLayers
// (384 to 417 moves, 56 to 69 ms) and 9 to 10 of spreadSources (28 to 36
// moves, 45 ms); on the plan-shaped graph of 4,000 nodes 2 pairs, 6 and 2
// passes. On the wide family of aspect.test.ts, with K growing with n,
// layersAt now grows 9.2 to 10.2 times in steps at 8n (d3dag.test.ts).
export function layersAt(base: Int32Array, parents: number[][], children: number[][], K: number, work?: Work): Int32Array {
  const y = Int32Array.from(base);
  makeRoom(y, K, work);
  // Each call ends where it can move nothing, so once a call after the first
  // moves nothing (returns 1, or 0 for no nodes), neither can move: the other
  // ended at these same layers.
  for (let k = 0; ; k++) if ((k % 2 ? spreadSources(y, parents, children, K, undefined, undefined, work) : balanceLayers(y, parents, children, K, undefined, undefined, work)) <= 1 && k > 0) break;
  compactLayers(y, work);
  return y;
}

// The width and height the page would draw layers y at, estimated without
// drawing (a drawing costs a crossing reduction and a placement, 0.5 to 3 s
// on the live plan): the rows splitRows draws (with the nodes in index order
// for x), each row's height its tallest box with GAP[1] between rows, and the
// width that of the widest row packed as narrow.ts packs it, the box widths
// with GAP[0] between them and LANE for each edge passing through the row.
// The estimate ignores the order of nodes and lanes in a row (a lane between
// two boxes takes 16 px of the 26 between them in narrow.ts), so d3dagLayout
// corrects it by the drawn shape (see fitLayers). Measured against the
// drawing on the live plan of 2026-11-13, the plan of 2026-11-10 and the
// plan-shaped graph of 500 nodes at K from 6 to 50: the height exact, the
// width 1 to 5 percent over (drawn over estimated w/h 0.957 to 0.991), and 9
// percent over on the 500-node graph at K = 6 (0.912).
// Complexity tradeoff: O(n log n + m), the sorts of splitRows and one pass
// over the edges with a difference array for the lanes; counting each edge's
// lanes row by row would cost the total edge span, O(m L).
const LANE = 8;
export function shapeOf(y: Int32Array, size: { w: ArrayLike<number>; h: ArrayLike<number> }, parents: number[][], children: number[][], work?: Work): { w: number; h: number } {
  const n = y.length;
  if (!n) return { w: 2 * PAD, h: 2 * PAD };
  const rows = splitRows(y, Int32Array.from({ length: n }, (_, i) => i), undefined, parents, children) ?? y;
  let R = 0;
  for (const v of rows) R = Math.max(R, v + 1);
  const sum = new Float64Array(R), tall = new Float64Array(R), count = new Int32Array(R), lanes = new Int32Array(R + 1);
  let m = 0;
  for (let i = 0; i < n; i++) {
    const r = rows[i];
    sum[r] += size.w[i];
    tall[r] = Math.max(tall[r], size.h[i]);
    count[r]++;
    for (const c of children[i]) { m++; if (rows[c] > r + 1) { lanes[r + 1]++; lanes[rows[c]]--; } }
  }
  let w = 0, h = GAP[1] * (R - 1), run = 0;
  for (let r = 0; r < R; r++) {
    run += lanes[r];
    w = Math.max(w, sum[r] + GAP[0] * (count[r] - 1) + LANE * run);
    h += tall[r];
  }
  // splitRows sorts the counts and each split row: about n log2 n comparisons.
  if (work) work.steps += 3 * n + m + 2 * R + Math.ceil(n * Math.log2(n + 1));
  return { w: w + 2 * PAD, h: h + 2 * PAD };
}

// The layers from base at a row limit K whose estimated w/h, times e (the
// drawn w/h over the estimate, measured by d3dagLayout; 1 before any
// drawing), lies within BAND, K at most the most nodes in a layer of base,
// beyond which makeRoom inserts nothing. A larger K means fewer, fuller rows,
// so w/h grows with K. If even the largest K is under BAND[0] (a longest path
// too long for the band), that K is taken: the fewest rows, the nearest
// shape; if no K lands within BAND (w/h jumps over it between two adjacent
// K), the larger K under it.
// The first probe is at the K where boxes of the mean size give w/h = TARGET,
// in rows of K boxes and max(rows of base, n / K) rows, by bisection on that
// formula. The estimate ignores the lanes of edges passing through a row, so
// it guesses too large a K (32 for 25 and 92 for 68 on the graphs of the
// scaling test in aspect.test.ts). Each probe outside BAND narrows the
// interval (K_lo, known under BAND or 1; K_hi, known over it or past the
// largest K), and the next probe is where w/h ~ K^2 from this probe puts
// TARGET, K' = K sqrt(TARGET / (w/h)), within the interval; after two probes
// in a row that did not halve it, its middle. w/h is not monotone in K in
// theory (balanceLayers is a heuristic), so the result is not proven the
// nearest; d3dagLayout checks the drawing.
// Complexity tradeoff: each probe is a layersAt and a shapeOf, O((n + m) log
// L) per balancing pass. Trying every K would be O(K_max) probes: 29.8 times
// the steps at 8n in the scaling test (the negative control). Bisection for
// the largest K within BAND, the first version of this, needs O(log K_max)
// probes: 8 at 4,000 nodes and 10 at 32,000, 13.6 times the steps, over the
// limit of 10.5. Stopping at the first probe within BAND took 3 probes at
// 4,000, 8,000, 32,000 and 64,000 nodes, 9.16 times the steps at 8n, and
// one drawing from scratch on the plans of 2026-11-10, 11 and 13. It gives
// up some rows within the band: K 23 against 25 (w/h 0.487 against 0.595)
// at 4,000 nodes, 64 against 68 at 32,000.
export function fitLayers(base: Int32Array, size: { w: ArrayLike<number>; h: ArrayLike<number> }, parents: number[][], children: number[][], e: number, work?: Work): { y: Int32Array; K: number; ratio: number } {
  const n = base.length;
  const probed = new Map<number, { y: Int32Array; ratio: number }>();
  const probe = (K: number) => {
    let p = probed.get(K);
    if (!p) {
      const y = layersAt(base, parents, children, K, work);
      const s = shapeOf(y, size, parents, children, work);
      probed.set(K, (p = { y, ratio: (e * s.w) / s.h }));
    }
    return p;
  };
  const c = counts(base);
  let most = 1, wide = 0, tall = 0;
  for (const v of c) most = Math.max(most, v);
  for (let i = 0; i < n; i++) { wide += size.w[i]; tall += size.h[i]; }
  const pitchW = n ? wide / n + GAP[0] : 1, pitchH = n ? tall / n + GAP[1] : 1;
  const guessed = (K: number) => (e * K * pitchW) / (Math.max(c.length, Math.ceil(n / K)) * pitchH);
  // The guess grows with K: the largest K in [1, most] where it is at most
  // TARGET, by bisection on the formula.
  let a = 1, b = most;
  while (a < b) { const k = (a + b + 1) >> 1; if (guessed(k) <= TARGET) a = k; else b = k - 1; }
  if (work) work.steps += n + c.length + Math.ceil(Math.log2(most + 1));
  let lo = 1, hi = most + 1, K = a, slow = 0;
  for (;;) {
    const width = hi - lo, r = probe(K).ratio;
    if (r >= BAND[0] && r <= BAND[1]) return { K, ...probe(K) };
    if (r < BAND[0]) lo = K; else hi = K;
    if (hi - lo <= 1) break;
    // w/h ~ K^2 put at TARGET from this probe, or, after two probes in a row
    // that did not halve the interval, its middle.
    slow = 2 * (hi - lo) > width ? slow + 1 : 0;
    K = Math.min(hi - 1, Math.max(lo + 1, slow >= 2 ? (lo + hi) >> 1 : Math.round(K * Math.sqrt(TARGET / r))));
  }
  return { K: lo, ...probe(lo) };
}

// The node count of each layer of y (top at its least value).
function counts(y: Int32Array): Int32Array {
  let top = Infinity, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const c = new Int32Array(y.length ? bottom - top + 1 : 0);
  for (const v of y) c[v - top]++;
  return c;
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
export function fromPrevious(old: (number | undefined)[], parents: number[][], children: number[][], work?: Work): Int32Array | null {
  const n = old.length;
  let top = Infinity, bottom = -Infinity;
  for (const v of old) if (v !== undefined) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  if (top === Infinity) return null;
  const order = new Int32Array(n);
  const waiting = Int32Array.from(parents, (p) => p.length);
  let len = 0;
  for (let i = 0; i < n; i++) if (!waiting[i]) order[len++] = i;
  let m = 0;
  for (let k = 0; k < len; k++) for (const c of children[order[k]]) { m++; if (--waiting[c] === 0) order[len++] = c; }
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
  // Eight sweeps over the nodes and at most four over the edges.
  if (work) work.steps += 8 * n + 4 * m;
  return y;
}

// Puts every source (a node with no parents) one layer above its highest
// child. A source's children are not sources, so moving one source changes no
// other source's place, and one pass in any order gives every source its
// place. A node with neither parents nor children stays where it is.
// Returns the number of sources moved.
export function lowerSources(y: Int32Array, parents: number[][], children: number[][], work?: Work): number {
  let moved = 0, steps = y.length;
  for (let i = 0; i < y.length; i++) {
    if (!isSource(i, parents, children)) continue;
    let hi = Infinity;
    steps += children[i].length;
    for (const c of children[i]) hi = Math.min(hi, y[c]);
    if (y[i] !== hi - 1) moved++;
    y[i] = hi - 1;
  }
  if (work) work.steps += steps;
  return moved;
}

// Elementary steps, for the scaling tests (d3dag.test.ts, decross.test.ts):
// a function given one adds to steps the work it did, each node or edge read,
// each layer of a linear sweep, each node of a segment tree visited and each
// comparison of a sort. The tests compare the steps at n and 8n instead of the
// time: under parallel load a time ratio at 32,000 nodes measured cache and
// CPU contention as much as the algorithm (a plain O(n + m) pass reached 13
// to 28 times at 8n, against 11 alone; batch 133, 2026-11-11). Unused, it
// costs a local integer count in each loop and one test at the end.
export interface Work { steps: number }

// A source here is a node with no parents and at least one child: lowerSources
// puts it directly above its highest child, balanceCounts never moves it, and
// balanceLayers moves it only out of a row over K or, with the spring of its
// edges, down toward that child (see balanceLayers).
function isSource(i: number, parents: number[][], children: number[][]): boolean {
  return !parents[i].length && children[i].length > 0;
}

// Moves nodes other than sources, one at a time, into the least crowded layer
// of their slack, the layers below their lowest parent and above their highest
// child within the current top and bottom layers, so every edge still goes
// down and the number of layers does not grow. Sources are neither moved nor
// counted: lowerSources places them afterward, directly above their highest
// child, wherever that is, so the slack of a child of a source starts at layer
// 1, leaving layer 0 for the source. With c[l] the number of other nodes in
// layer l, node i
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
// nodes start in one layer), but the passes measured are few: 12 passes and
// 1,428 moves on the plan of 2026-11-10 (1,661 nodes, sum of squares of the
// nodes other than sources 63,883 to 20,807) and 3 and 90 on the plan-shaped
// graph of 1,000 nodes. Counting sources too, before they were left alone: 13
// and 1,936 on the same plan, 3 and 82 at 1,000 nodes. The scaling test in
// d3dag.test.ts counts its steps (Work) at 4,000 and 32,000 nodes.
export function balanceCounts(y: Int32Array, parents: number[][], children: number[][], onMove?: (i: number, from: number, to: number) => void, work?: Work): number {
  const n = y.length;
  if (!n) return 0;
  let top = Infinity, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const L = bottom - top + 1;
  const c = countsFor(L, work);
  for (let i = 0; i < n; i++) if (!isSource(i, parents, children)) c.add(y[i] - top, 1);
  // A pass reads every node and the edges of every node other than a
  // source: perPass steps, the same in each pass, so the loop below counts
  // nothing per node (see Work).
  let perPass = 4 * n;
  if (work) for (let i = 0; i < n; i++) if (!isSource(i, parents, children)) perPass += parents[i].length + children[i].length;
  let passes = 0, steps = 2 * n;
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
    steps += perPass;
    for (const i of order) {
      if (isSource(i, parents, children)) continue;
      const a = y[i] - top;
      let lo = 0, hi = L - 1;
      for (const q of parents[i]) lo = Math.max(lo, isSource(q, parents, children) ? 1 : y[q] - top + 1);
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
  if (work) work.steps += steps;
  return passes;
}

// Moves nodes, one at a time, within their slack (the layers below their
// lowest parent and above their highest child, within layer 0, or the top
// layer if it is above 0, and the bottom layer), so every edge still goes down
// and the number of layers does not grow. A node that is the only highest
// child of a source (the one child in the layer directly below it) is not
// moved, so a source directly above its highest child stays there unless it
// moves itself.
// Two rules of the author's, and how they meet. The source rule (2026-11-11):
// a source sits directly above its highest child. The row rule (2026-11-13):
// a node of a row over K moves to a less full row before its edges are
// shortened. The second wins, and only for rows over K: a source moves only
// out of a row over K (Q falls), up into a row with room (makeRoom inserts
// those directly above a row over K), or down, by the spring of its edge,
// toward its child into a row with room; it never moves up out of a row of K
// or fewer, as that lowers neither Q nor F. So a source sits directly above
// its highest child unless that row holds K nodes. The spring rule
// (2026-11-11): each edge pulls its two ends
// together like a spring, so a node with more edges up than down is pulled
// up and one with more down than up is pulled down, by how much the moves
// shorten its edges; a move to a less crowded row is better than one to a
// more crowded row; and no node moves into a full row. With c[l] the number
// of nodes in layer l, a row is full at K nodes (K from the shape, see
// fitLayers; until 2026-11-13 the split rule's 1.5 times the median count),
// and the moves lower
//   F = (2K + 1) * (sum of edge lengths in layers) + sum over l of c[l]^2.
// Node i, with P parents and C children, from layer a to layer b changes the
// first sum by s (b - a), s = P - C, and the second by 2 (c[b] - c[a] + 1).
// A move must land in a row with room (c[b] <= K - 1) and either leave a full
// row (c[a] > K, where the starting layers can have more than K) or lower F.
// Of the allowed layers it takes the one where F is least; of equals, the
// topmost if s > 0, the bottommost if s < 0 and the nearest if s = 0.
// Since 2 (c[b] - c[a] + 1) <= 2 (K - 1) < 2K + 1 when b has room, any move
// that shortens the edges lowers F, whatever the counts: a node with more
// children than parents moves down to the lowest row with room above its
// highest child, and one with more parents up as far as its slack allows.
// The counts decide only between moves
// that change the edge lengths equally, as for a node with as many parents as
// children: it moves to the least crowded layer if, with it, that holds fewer
// nodes than the layer it left.
// The first round reads every node, those of the most crowded layers first,
// as counted at the start; each later round reads again only the nodes whose
// move a change in the round before may have allowed (see the complexity
// note below), until a round moves nothing. It returns the number of rounds,
// 1 if nothing moved, and ends where no node can move. onMove, if given, sees
// each move, for tests.
//
// It ends, with no pass count set. Let Q = sum over l of max(0, c[l] - K)^2.
// A move out of a row over K (c[a] > K) lowers Q: into a row with room by
// 2 (c[a] - K) - 1 >= 1; into the least crowded layer, at c[b] >= K with
// c[b] + 1 < c[a], by 2 (c[a] - c[b] - 1) >= 2. Every other move starts in a
// row of at most K and ends in one of at most K, so it leaves Q as it was,
// and it lowers the integer F by at least 1. F lies between 0 and
// F_max = (2K + 1) m (L - 1) + n^2 for m edges, so there are at most Q0 moves
// out of rows over K, at most F_max other moves between two of those, and so
// at most Q0 + (Q0 + 1) F_max moves, with at most one round more than moves.
// After balanceCounts and lowerSources, Q0 = 1,554 on the plan of 2026-11-10
// (K = 24, 15 rows over it, the widest 54, sources gathered in it) and 1,289 on
// the live plan of 2026-11-11 (K = 25). Moving sources too keeps the
// argument, which holds for any node. makeRoom changes the layers between
// calls, not during one, so each call keeps it.
// That bound is quadratic or worse in n. The number of rounds can be linear in
// n: in the chain of d3dag.test.ts ("a chain of moves"), each round can move
// only the next node of a chain, as each move frees the row the next one
// needs.
//
// Complexity tradeoff: scanning each node's slack costs O(n L) per read, as
// the slack can span every layer. A segment tree over c answers the least
// count in a range and the first or last layer at or below a count in
// O(log L), and a move updates it in O(log L); the best layer for a node with
// s != 0 is found by Counts.bestLayer in at most K steps of O(log L). The
// number of highest children of each source (highest) costs O(n + m) per
// call and O(deg) per move to keep (a moved source's own count O(C) for its
// C children).
// Which nodes to read again. The naive method, used until
// DAGVIEW-spread-scaling, reads every node in each pass until a pass moves
// nothing: O((n + m) log L + n K log L) a pass, and the passes grow with n
// (a move frees or fills a row that lets another move), so layersAt on the
// wide plan-shaped family of aspect.test.ts grew 10.6 to 17.2 times in steps
// at 8n. Here, as in a worklist solver of dataflow equations [Kildall73], a
// node is read again only when something its move depends on changed:
//   - its slack: a parent's slack widens only when i moved down out of the
//     row above it (i may have been its highest child), a child's only when
//     i moved up; a source's children are held while it has one highest
//     child, so they are read again when that changes or the source moves;
//   - the counts: a read that moves nothing leaves waits for the least change
//     of c[a] (a rise, by a hash map on (layer, count)) or of a count in its
//     slack (a fall, on the O(log L) segment-tree nodes covering the slack,
//     by a hash map on (tree node, count), fired on the path above a layer
//     that falls) that could allow a move; the conditions are derived at
//     each site below. A rise elsewhere never allows a move, nor does a
//     slack that shrinks.
// A read costs O(deg + K log L) as before, a wait O(log L) to make and O(1)
// to fire; each wait fires at most once, and a read made after it voids it
// (ver), so the waits cost no more than the reads that made them. A move
// queues O(deg) nodes. In all O((n + M deg) (K + 1) log L) for M moves,
// against O(passes (n + m) K log L). On the wide family with K = row / 4 and
// row / 2 (4 seeds each, K growing with n as fitLayers chooses it) layersAt
// grows 9.2 to 10.2 times at 8n; at K = 23 for both sizes 12.6 to 13.3 times,
// against 10.4 to 16.9 before, as the excess over K per node grows with n
// there (0.51 to 0.83), and so must the moves. On k sources sharing one child
// after makeRoom (d3dag.test.ts) the steps grow 10.4 times at 8k, the log L
// of the tree; scanning the slack instead grew 57.9 times, and reading again
// every parent of a shared child to test whether its slack widened 62.3
// times (each run once as a control, not kept).
export function balanceLayers(y: Int32Array, parents: number[][], children: number[][], K: number, onMove?: (i: number, from: number, to: number) => void, W = 2 * K + 1, work?: Work): number {
  const n = y.length;
  if (!n) return 0;
  let top = 0, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const L = bottom - top + 1;
  const c = countsFor(L, work);
  for (let i = 0; i < n; i++) c.add(y[i] - top, 1);
  const high = highest(y, parents, children, work);
  let rounds = 0, steps = 2 * n;
  // ver[i] counts the reads of i; a wait holds the version it was made at,
  // so a later read of i voids it.
  const ver = new Int32Array(n);
  // queued[i] = r if i is queued for round r; next holds round r + 1.
  const queued = new Int32Array(n);
  let next: number[] = [];
  const queue = (i: number) => { if (queued[i] !== rounds + 1) { queued[i] = rounds + 1; next.push(i); } };
  // Waits on a rise, key l * (n + 2) + v: nodes of layer l to read again
  // when c[l] rises to v. Waits on a fall, key t * 2S + k for node k of a
  // segment tree over the layers: nodes to read again when a layer under k
  // falls to t. Counts change by 1 per move, so a count that passes a value
  // reaches it.
  let S = 1;
  while (S < L) S *= 2;
  const depth = Math.log2(S) + 1;
  const rises = new Map<number, number[]>(), falls = new Map<number, number[]>();
  const hold = (m: Map<number, number[]>, key: number, i: number) => {
    const w = m.get(key);
    if (w) w.push(i, ver[i]); else m.set(key, [i, ver[i]]);
  };
  const wake = (m: Map<number, number[]>, key: number) => {
    const w = m.get(key);
    if (!w) return;
    m.delete(key);
    steps += w.length / 2;
    for (let j = 0; j < w.length; j += 2) if (ver[w[j]] === w[j + 1]) queue(w[j]);
  };
  const onRise = (i: number, l: number, v: number) => { steps++; hold(rises, l * (n + 2) + v, i); };
  const onFall = (i: number, lo: number, hi: number, t: number) => {
    if (t < 0) return;
    for (let x = lo + S, z = hi + S + 1; x < z; x >>= 1, z >>= 1) {
      steps++;
      if (x & 1) hold(falls, t * 2 * S + x++, i);
      if (z & 1) hold(falls, t * 2 * S + --z, i);
    }
  };
  // i, in layer a with slack lo..hi, moves once c[a] - c[l] >= 2 for a layer
  // l of its slack other than a, or, with room >= 0, once a layer of the
  // slack falls to room. With g = c[a] - (the least count of those layers),
  // that takes r rises of a and f falls of the least with r + f >= 2 - g.
  // Waiting for d = ceil((2 - g) / 2) of either misses none, as r, f <= d - 1
  // give r + f <= 2d - 2 < 2 - g.
  const gap = (i: number, a: number, lo: number, hi: number, room: number) => {
    const m = Math.min(a > lo ? c.min(lo, a - 1) : Infinity, a < hi ? c.min(a + 1, hi) : Infinity);
    if (m === Infinity) return;
    const ca = c.at(a), d = Math.ceil((2 - (ca - m)) / 2);
    onRise(i, a, ca + d);
    onFall(i, lo, hi, Math.max(room, m - d));
  };
  // Reads node i: moves it if a move is allowed, else leaves waits for the
  // counts that would allow one. Returns whether it moved.
  const read = (i: number): boolean => {
    ver[i]++;
    steps += 4 + 2 * parents[i].length + children[i].length;
    if (parents[i].some((q) => isSource(q, parents, children) && y[q] === y[i] - 1 && high[q] === 1)) return false;
    const a = y[i] - top;
    let lo = 0, hi = L - 1;
    for (const q of parents[i]) lo = Math.max(lo, y[q] - top + 1);
    for (const k of children[i]) hi = Math.min(hi, y[k] - top - 1);
    if (lo > hi) return false;
    const s = W * (parents[i].length - children[i].length);
    const ca = c.at(a);
    let b: number;
    if (s === 0) {
      // Only the counts matter: a move needs c[b] + 1 < c[a], which leaves
      // room in b when a is not full.
      const m = c.min(lo, hi);
      if (m + 1 >= ca) { gap(i, a, lo, hi, -1); return false; }
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
        else gap(i, a, lo, hi, K - 1);
      } else if (b < 0) {
        // |s| >= 2K + 1 outweighs any difference of counts, so with c[a] <= K
        // i moves iff a layer of its slack on the side its edges pull it to
        // has room: it waits for one to fall to K - 1, or for a to pass K.
        onRise(i, a, K + 1);
        if (s > 0) onFall(i, lo, a - 1, K - 1); else onFall(i, a + 1, hi, K - 1);
      }
      if (b < 0) return false;
    }
    c.add(a, -1);
    c.add(b, 1);
    steps += depth + 1;
    for (let k = a + S; k; k >>= 1) wake(falls, c.at(a) * 2 * S + k);
    wake(rises, b * (n + 2) + c.at(b));
    // A parent's slack widens only if i was its one highest child and moved
    // down, a child's only if i was its one lowest parent and moved up. Both
    // are queued on the direction alone: testing "one highest child" scans
    // the parent's children, O(n) a move when n sources share a child, and
    // grew 62.3 times at 8k on sharedChild (d3dag.test.ts); a needless read
    // costs O(deg + K log L) and moves nothing.
    steps += parents[i].length;
    for (const q of parents[i]) {
      if (b > a) queue(q);
      if (!isSource(q, parents, children)) continue;
      const was = high[q];
      if (a === y[q] - top + 1) high[q]--;
      if (b === y[q] - top + 1) high[q]++;
      // q's children are held below it only while it has one highest child.
      if ((was === 1) !== (high[q] === 1)) { steps += children[q].length; for (const k of children[q]) queue(k); }
    }
    if (b < a) { steps += children[i].length; for (const k of children[i]) queue(k); }
    queue(i);
    y[i] = b + top;
    // A source that moved has new highest children: O(C) for its C children.
    // They need no read for it: moved up, they are queued above; it cannot
    // move down while a child is directly below it, so a move down holds
    // children, never frees one.
    if (isSource(i, parents, children)) {
      high[i] = 0;
      steps += children[i].length;
      for (const k of children[i]) if (y[k] === y[i] + 1) high[i]++;
    }
    onMove?.(i, a + top, b + top);
    return true;
  };
  // Round 1 reads every node, those of the most crowded layers first, as
  // counted at the start, by a counting sort (O(n + L)); in index order
  // within a count. Each later round reads the nodes queued in the one
  // before, in the order queued.
  const start = new Int32Array(n + 2);
  for (let i = 0; i < n; i++) start[n - c.at(y[i] - top) + 1]++;
  for (let k = 1; k <= n + 1; k++) start[k] += start[k - 1];
  const first = new Int32Array(n);
  for (let i = 0; i < n; i++) first[start[n - c.at(y[i] - top)]++] = i;
  steps += n;
  for (let order: ArrayLike<number> = first; order.length; ) {
    rounds++;
    for (let j = 0; j < order.length; j++) read(order[j]);
    order = next;
    next = [];
  }
  if (work) work.steps += steps;
  return rounds;
}

// high[q] for each source q: the number of its children in the layer directly
// below it, its highest children. O(n + m).
function highest(y: Int32Array, parents: number[][], children: number[][], work?: Work): Int32Array {
  const high = new Int32Array(y.length);
  let steps = y.length;
  for (let q = 0; q < y.length; q++) if (isSource(q, parents, children)) for (const k of children[q]) { steps++; if (y[k] === y[q] + 1) high[q]++; }
  if (work) work.steps += steps;
  return high;
}

// Moves a node i whose parents' layer above it is over K (c[a - 1] > K, for
// i in layer a) together with the sources it is the only highest child of
// (its carried sources, w of them, in layer a - 1), so that i lands in layer b
// and they in b - 1: each source stays directly above its highest child, and a
// row over K that sources share is relieved, which balanceLayers cannot do as
// it moves neither sources nor their only highest children. Every edge still
// goes down: b lies above i's children and the carried sources' other
// children, below i's other parents, and b - 1 >= 0. A move is taken only if
// it lowers balanceLayers' Q (the squared excess of rows over K) or keeps Q
// and lowers its F (W times the sum of edge lengths plus the sum of squared
// counts), counted exactly over the rows the move changes (a - 1, a, b - 1 and
// b), with s, the change in edge length per layer moved, +1 for each other
// parent of i, -1 for each child of i and -1 for each other child of a carried
// source (the edge from a carried source to i keeps its length). Candidates,
// in this order, the first that lowers (Q, F) taken: first the nearer and the
// farther of the nearest layers above and below where b - 1 and b have room
// for the move (neither holds more than K - w nodes); only if neither lowers
// (Q, F), b = a - 1 (i into the sources' own row, they into the one above),
// then the nearer and the farther of the nearest layers where neither b nor
// b - 1 holds c[a - 1] - w nodes or more. Passes repeat until one moves
// nothing; it returns the number of passes. onMove, if given, sees each move
// of i.
//
// It ends, with no pass count set: every move lowers (Q, F) in the order of
// first Q then F, as every move of balanceLayers does, Q and F are integers
// at least 0, and F <= F_max as in balanceLayers. So the moves of the two
// together are at most Q0 + (Q0 + 1) F_max, and the loop in layers that runs
// them in turn until neither moves ends. The candidates are a choice of three,
// not the best layer: a move ends where Q or F is lower, so the order of
// trying them changes the result, not the ending.
//
// Complexity tradeoff: scanning every layer of i's slack for the best b is
// O(L) per node and O(n L) per pass. A segment tree over pair(l) = max(c[l -
// 1], c[l]) gives the nearest layer above or below where both b - 1 and b hold
// fewer than a bound in O(log L); a move changes six of its entries, each
// O(log L). A source is carried only by its one highest child, so the carried
// sources' edges are read once per pass: a pass costs O((n + m) + n log L).
// The candidates with room come first, as of DAGVIEW-spread-scaling: tried
// first, b = a - 1 moves a source into the row above, which is then over K
// in turn, so a source moved again and again. On crowdedSources of
// d3dag.test.ts (k sources in one row) that order made 18 passes and 48,912
// moves at k = 4,000 and 24 passes and 559,780 at 32,000 (12 to 17.5 moves a
// source, 14.19 times the steps); with room first, 2 passes and one move a
// source at both sizes, 372,762 and 3,637,168 steps (9.76 times). The layouts
// of the plan, the live plan and the plan-shaped graph of 4,000 nodes came
// out the same either way. fix updates the tree only where pair(l) changed,
// as each update is O(log L) and an entry a move touches can keep its value.
export function spreadSources(y: Int32Array, parents: number[][], children: number[][], K: number, onMove?: (i: number, from: number, to: number) => void, W = 2 * K + 1, work?: Work): number {
  const n = y.length;
  if (!n) return 0;
  let top = Infinity, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const L = bottom - top + 1;
  const c = new Int32Array(L);
  for (let i = 0; i < n; i++) c[y[i] - top]++;
  const pair = (l: number) => (l ? Math.max(c[l - 1], c[l]) : 0x3fffffff);
  const p = countsFor(L, work);
  for (let l = 0; l < L; l++) p.add(l, pair(l));
  const fix = (l: number) => { if (l < 0 || l >= L) return; const d = pair(l) - p.at(l); if (d) p.add(l, d); };
  const over = (v: number) => (v > K ? (v - K) * (v - K) : 0);
  const high = highest(y, parents, children, work);
  const carried: number[] = [], isCarried = new Uint8Array(n);
  const rows: number[] = [], delta: number[] = [];
  let passes = 0, steps = 2 * n + L;
  for (let moved = true; moved;) {
    moved = false;
    passes++;
    // Each node is read once a pass.
    steps += n;
    for (let i = 0; i < n; i++) {
      if (!parents[i].length) continue;
      const a = y[i] - top;
      if (c[a - 1] <= K) continue;
      // The sources that have i as their only highest child move with it.
      for (const q of carried) isCarried[q] = 0;
      // The step counts of a crowded node are added only when counting: as
      // plain adds they cost 0.9 percent more instructions in this function
      // (DAGVIEW-counter-cost, 2026-11-11).
      if (work) steps += carried.length + children[i].length + parents[i].length;
      carried.length = 0;
      let lo = 1, hi = L - 1, s = 0;
      for (const k of children[i]) { hi = Math.min(hi, y[k] - top - 1); s--; }
      for (const q of parents[i]) {
        if (parents[q].length || y[q] !== y[i] - 1 || high[q] !== 1) { lo = Math.max(lo, y[q] - top + 1); s++; continue; }
        carried.push(q);
        isCarried[q] = 1;
        if (work) steps += children[q].length;
        for (const k of children[q]) if (k !== i) { hi = Math.min(hi, y[k] - top - 1); s--; }
      }
      const w = carried.length;
      if (!w) continue;
      // The exact change in Q and F (balanceLayers) over the rows touched by
      // a move to b; true if it lowers Q, or keeps Q and lowers F.
      const lowers = (b: number) => {
        if (b < 0) return false;
        rows.length = 0; delta.length = 0;
        const touch = (l: number, d: number) => { const k = rows.indexOf(l); if (k >= 0) delta[k] += d; else { rows.push(l); delta.push(d); } };
        touch(a, -1); touch(a - 1, -w); touch(b, 1); touch(b - 1, w);
        let dQ = 0, dF = W * s * (b - a);
        for (let k = 0; k < rows.length; k++) {
          const v = c[rows[k]], u = v + delta[k];
          dQ += over(u) - over(v);
          dF += u * u - v * v;
        }
        return dQ < 0 || (dQ === 0 && dF < 0);
      };
      // Candidates, in two rounds, the second only if the first finds no
      // move: first the nearer and the farther of the nearest layers above
      // and below where b - 1 and b have room for the move (neither holds
      // more than K - w nodes); then the layer of the sources themselves, and
      // the nearer and the farther of the nearest layers where neither b - 1
      // nor b holds c[a - 1] - w nodes or more.
      const nearest = (T: number) => {
        const up = T >= 0 && a - 1 > lo ? p.last(lo, a - 2, T) : -1;
        const down = T >= 0 && a < hi ? p.first(a + 1, hi, T) : -1;
        return up < 0 || (down >= 0 && down - a < a - up) ? [down, up] : [up, down];
      };
      let b = -1;
      for (let round = 0; b < 0 && round < 2; round++) {
        const ts = round ? [a - 1 >= lo ? a - 1 : -1, ...nearest(c[a - 1] - w - 1)] : nearest(K - w);
        // Each candidate tried (t >= 0) is 4 steps, counted here so that no
        // closure writes steps, which would keep it in memory, not a register.
        for (const t of ts) {
          if (work && t >= 0) steps += 4;
          if (lowers(t)) { b = t; break; }
        }
      }
      if (b < 0) continue;
      for (let k = 0; k < rows.length; k++) c[rows[k]] += delta[k];
      y[i] = b + top;
      if (work) steps += carried.length + parents[i].length;
      for (const q of carried) y[q] = b + top - 1;
      for (const q of parents[i]) {
        if (parents[q].length || isCarried[q]) continue;
        if (a + top === y[q] + 1) high[q]--;
        if (b + top === y[q] + 1) high[q]++;
      }
      for (const l of [a - 1, a, a + 1, b - 1, b, b + 1]) fix(l);
      onMove?.(i, a + top, b + top);
      moved = true;
    }
  }
  if (work) work.steps += steps;
  return passes;
}

// The row-size limit of the author's split rule (splitRows): a row is full
// at floor(1.5 x median) nodes, the median of the counts of the nonempty
// layers of y, the mean of the two middle counts when their number is even.
// Complexity tradeoff: O(n + L log L), sorting the counts; a selection
// algorithm would give O(n + L), a difference of microseconds here.
export function rowLimit(y: Int32Array, work?: Work): number {
  const c = new Map<number, number>();
  for (const v of y) c.set(v, (c.get(v) ?? 0) + 1);
  const s = Int32Array.from(c.values()).sort();
  const L = s.length;
  // The sort is the engine's, so its comparisons are taken as L log2 L.
  if (work) work.steps += y.length + L * Math.ceil(Math.log2(L + 1));
  if (!L) return 1;
  const median = L % 2 ? s[(L - 1) / 2] : (s[L / 2 - 1] + s[L / 2]) / 2;
  return Math.max(1, Math.floor(1.5 * median));
}

// Node counts per layer in a segment tree of minimums. It counts no steps;
// countsFor gives a CountedCounts when the caller passed a Work.
class Counts {
  protected size = 1;
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

// Counts that adds to work.steps the tree nodes it visits (see Work), for the
// scaling tests. The layout passes no Work and uses Counts, which keeps
// nothing: counting in Counts itself cost 5 to 9 percent more instructions
// in spreadSources, balanceCounts and layers (DAGVIEW-counter-cost,
// 2026-11-11). first and last recurse through this.first and this.last, so
// each node they visit is counted. add and min count by the bounds of Counts'
// own loops (add the depth of the tree, min the same walk up from lo and hi),
// so a change to either loop in Counts must change its count here too.
class CountedCounts extends Counts {
  private readonly work: Work;
  private readonly depth: number;
  constructor(L: number, work: Work) {
    super(L);
    this.work = work;
    this.depth = Math.log2(this.size);
    work.steps += 2 * this.size;
  }
  add(l: number, d: number): void {
    super.add(l, d);
    this.work.steps += this.depth;
  }
  min(lo: number, hi: number): number {
    for (let a = lo + this.size, b = hi + this.size + 1; a < b; a = (a + (a & 1)) >> 1, b = (b - (b & 1)) >> 1) this.work.steps++;
    return super.min(lo, hi);
  }
  first(lo: number, hi: number, m: number, k = 1, l = 0, r = this.size - 1): number {
    this.work.steps++;
    return super.first(lo, hi, m, k, l, r);
  }
  last(lo: number, hi: number, m: number, k = 1, l = 0, r = this.size - 1): number {
    this.work.steps++;
    return super.last(lo, hi, m, k, l, r);
  }
}

const countsFor = (L: number, work?: Work): Counts => (work ? new CountedCounts(L, work) : new Counts(L));

// The author's rule (2026-11-13): a wide row's nodes stagger up or down into
// less full rows, and that takes priority over the spring of their edges.
// makeRoom inserts, directly above each layer l holding c[l] > K nodes,
// ceil((c[l] - K) / K) empty layers, enough to hold its excess in rows of K;
// returns the number inserted (at most n / K, as ceil((c - K) / K) <= c / K).
// Every layer moves down by the empty layers inserted above it and above every
// layer over it, so the order of the layers is kept and every edge still goes
// down; the empty layers above the top one become layers 0 and on, which
// balanceLayers counts from. balanceLayers then fills them: a source in a row
// over K moves to the lowest row with room above its highest child, now a few
// layers up, and other nodes whose slack reaches them follow (see layers).
// Before (2026-11-11), a source stayed directly above its highest child
// whatever the count, so 80 sources over one child made a row of 81; and
// letting balanceLayers move sources within the existing layers alone left
// every row above such a child full (on the live plan of 2026-11-13, the 25
// top layers at 35 or 36 nodes against K = 27).
// Complexity tradeoff: O(n + L), a count per layer and one sweep. Inserting
// the empty layers only above the top layer took the same O(n + L) but put
// raised sources up to 32 layers above their child, against 3 here: 52,362
// crossings against 33,379 on the live plan of 2026-11-13 (top comment). Run
// once per round of layers, not in each balanceLayers call, so every move of
// the inner loop still lowers (Q, F) and the loop ends (see balanceLayers).
export function makeRoom(y: Int32Array, K: number, work?: Work): number {
  const n = y.length;
  if (!n) return 0;
  let top = Infinity, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const count = new Int32Array(bottom - top + 1);
  for (const v of y) count[v - top]++;
  // shift[l]: the empty layers inserted above layer l and every layer above it.
  const shift = new Int32Array(count.length);
  let added = 0;
  for (let l = 0; l < count.length; l++) {
    if (count[l] > K) added += Math.ceil((count[l] - K) / K);
    shift[l] = added;
  }
  if (added) for (let i = 0; i < n; i++) y[i] += shift[y[i] - top];
  if (work) work.steps += 3 * n + 2 * count.length;
  return added;
}

// Drops empty layers and puts the top layer at 0, keeping the order of the
// layers; returns the number of layers. An edge that went down still goes down.
export function compactLayers(y: Int32Array, work?: Work): number {
  if (!y.length) return 0;
  let top = Infinity, bottom = -Infinity;
  for (const v of y) { top = Math.min(top, v); bottom = Math.max(bottom, v); }
  const to = new Int32Array(bottom - top + 1);
  for (const v of y) to[v - top] = 1;
  let k = 0;
  for (let l = 0; l < to.length; l++) to[l] = to[l] ? k++ : -1;
  for (let i = 0; i < y.length; i++) y[i] = to[y[i] - top];
  if (work) work.steps += 3 * y.length + 2 * to.length;
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
// Given parents and children, sources stay directly above their highest child
// in the drawn rows: a source in a split row goes to its lower half, and of a
// source's highest children in a split row the leftmost goes to the upper
// half; the other nodes of a split row then fill the upper half to half the
// row, evenly from left to right. Without that rule, 173 sources of the live
// plan of 2026-11-11 were more than one drawn row above their highest child
// where the layers had 141.
// Complexity tradeoff: O(n log n + m) for sorting the counts and each split
// row by x and reading each source's children once, against O(n + m) with a
// selection algorithm for the median; n log n is milliseconds here.
export function splitRows(y: Int32Array, x: ArrayLike<number>, half?: Int8Array, parents?: number[][], children?: number[][]): Int32Array | null {
  const n = y.length;
  let L = 0;
  for (const v of y) L = Math.max(L, v + 1);
  const c = new Int32Array(L);
  for (const v of y) c[v]++;
  const sorted = Int32Array.from(c).sort();
  const median = L % 2 ? sorted[(L - 1) / 2] : (sorted[L / 2 - 1] + sorted[L / 2]) / 2;
  const rows = new Map<number, number[]>();
  for (let i = 0; i < n; i++) {
    if (c[y[i]] > 1.5 * median) {
      let r = rows.get(y[i]);
      if (!r) rows.set(y[i], (r = []));
      r.push(i);
    }
  }
  // 1 for a node going to the lower half, 0 for the upper, -1 not decided.
  const lower = new Int8Array(n).fill(-1);
  // A source in a split row is directly above its highest child only from the
  // lower half, and a child in a split row only from the upper half, so every
  // source of a split row goes to the lower half, and for every source whose
  // children in the layer just below are in a split row, the leftmost of them
  // goes to the upper half. Children are never sources, so no node is asked
  // for both halves.
  if (children) {
    for (let i = 0; i < n; i++) {
      if (!isSource(i, parents!, children)) continue;
      if (c[y[i]] > 1.5 * median) lower[i] = 1;
      let pick = -1;
      for (const k of children[i]) {
        if (y[k] !== y[i] + 1 || !(c[y[k]] > 1.5 * median)) continue;
        if (pick < 0 || x[k] < x[pick] || (x[k] === x[pick] && k < pick)) pick = k;
      }
      if (pick >= 0) lower[pick] = 0;
    }
  }
  for (const r of rows.values()) {
    r.sort((p, q) => x[p] - x[q] || p - q);
    // The other nodes, F of them in x order, fill the upper half to half the
    // row, ceil(|r| / 2), spread evenly from left to right: free node j goes up
    // when floor((j + 1) u / F + 1/2) > floor(j u / F + 1/2), for u of them going up. With
    // no forced node that is every other node, starting with the first. Given
    // half, a node keeps its earlier half and one with none takes the other
    // half from the node to its left.
    let up = Math.ceil(r.length / 2), F = 0;
    for (const i of r) if (lower[i] === 0) up--; else if (lower[i] < 0) F++;
    const u = Math.max(0, Math.min(F, up));
    let j = 0, last = 1;
    for (const i of r) {
      if (lower[i] >= 0) continue;
      if (half) last = half[i] >= 0 ? half[i] : 1 - last;
      else last = Math.floor((2 * (j + 1) * u + F) / (2 * F)) > Math.floor((2 * j * u + F) / (2 * F)) ? 0 : 1;
      lower[i] = last;
      j++;
    }
  }
  // A row is split only if both halves get a node. A row whose nodes all go
  // to one half (a row of sources all go to the lower) stays one row: split,
  // it would leave an empty row, and over row 0 no edge passes through it,
  // a layer d3-dag rejects.
  const both = new Uint8Array(L);
  for (const [l, r] of rows) if (r.some((i) => lower[i] === 0) && r.some((i) => lower[i] === 1)) both[l] = 1;
  const shift = new Int32Array(L);
  let s = 0;
  for (let l = 0; l < L; l++) { shift[l] = s; s += both[l]; }
  if (!s) return null;
  const out = new Int32Array(n);
  for (let i = 0; i < n; i++) out[i] = y[i] + shift[y[i]] + (both[y[i]] ? lower[i] : 0);
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
// O(E log w). work, if given, counts the steps (see Work) of the sorts, the
// sweeps and the counts, each call of along as one.
export function decrossSeeded(index: Map<any, number>, x: Float64Array, y: Int32Array, along?: (s: number, t: number, l: number) => number, work?: Work): any {
  const at = (s: any): number => {
    if (s.data.role === "node") return x[index.get(s.data.node)!];
    const a = index.get(s.data.link.source)!, b = index.get(s.data.link.target)!;
    const e = along ? along(a, b, s.data.layer) : NaN;
    return Number.isNaN(e) ? x[a] + ((s.data.layer - y[a]) / (y[b] - y[a])) * (x[b] - x[a]) : e;
  };
  return (layers: any[][]) => {
    let steps = 0, N = 0;
    for (const row of layers) {
      const k = new Map(row.map((s) => [s, at(s)]));
      row.sort(work ? (p, q) => (work.steps++, k.get(p)! - k.get(q)!) : (p, q) => k.get(p)! - k.get(q)!);
      N += row.length;
    }
    let best = crossings(layers, work), kept = layers.map((l) => l.slice());
    const step = sweeper(layers, undefined, work);
    steps += 3 * N;
    for (;;) {
      for (let k = 0; k + 1 < layers.length; k++) step(k + 1, true);
      for (let k = layers.length - 1; k > 0; k--) step(k - 1, false);
      const now = crossings(layers, work);
      if (now >= best) break;
      best = now;
      kept = layers.map((l) => l.slice());
      steps += N;
    }
    layers.splice(0, layers.length, ...kept);
    if (work) work.steps += steps;
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
// the same. work, if given, counts the steps (see Work), the base step's not.
function sweeper(layers: any[][], base?: (top: any[], bottom: any[], down: boolean) => void, work?: Work): (k: number, down: boolean) => boolean {
  const id = new Map<any, number>();
  for (const l of layers) for (const s of l) id.set(s, id.size);
  let setup = 2 * id.size;
  const nbr = (s: any, up: boolean): [Int32Array, Float64Array] => {
    const list = [...(up ? s.parentCounts() : s.childCounts())];
    setup += list.length;
    return [Int32Array.from(list, (e: any) => id.get(e[0])!), Float64Array.from(list, (e: any) => e[1])];
  };
  const ups: [Int32Array, Float64Array][] = [], downs: [Int32Array, Float64Array][] = [];
  for (const l of layers) for (const s of l) { ups.push(nbr(s, true)); downs.push(nbr(s, false)); }
  const pos = new Int32Array(id.size);
  const place = (k: number) => layers[k].forEach((s, i) => { pos[id.get(s)!] = i; });
  layers.forEach((_, k) => place(k));
  if (work) work.steps += setup;
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
    // The slices, ids, offsets, the reorder, place and the comparison with
    // was, each a sweep of the layer, and each neighbor read once.
    let steps = 7 * w + off[w];
    const P = new Float64Array(off[w]), C = new Float64Array(off[w]);
    for (let i = 0; i < w; i++) {
      const [us, cs] = lists[ids[i]];
      const o = off[i];
      if (us.length === 1) { P[o] = pos[us[0]]; C[o] = cs[0]; continue; }
      const order = Array.from(us, (_, q) => q).sort(work ? (p, q) => (work.steps++, pos[us[p]] - pos[us[q]]) : (p, q) => pos[us[p]] - pos[us[q]]);
      order.forEach((q, r) => { P[o + r] = pos[us[q]]; C[o + r] = cs[q]; });
    }
    const known = new Map<number, number>();
    const gain = (iu: number, iv: number) => {
      const key = iu * w + iv;
      const had = known.get(key);
      if (had !== undefined) return had;
      const a0 = off[iu], a1 = off[iu + 1], b0 = off[iv], b1 = off[iv + 1];
      let total = 0, below = 0, j = b0, all = 0, read = 0;
      for (let q = b0; q < b1; q++) all += C[q];
      for (let i = a0; i < a1; i++) {
        while (j < b1 && P[j] < P[i]) below += C[j++];
        let same = 0, q = j;
        for (; q < b1 && P[q] === P[i]; q++) same += C[q];
        read += q - j;
        total += C[i] * (below - (all - below - same));
      }
      // Counted into work, not steps: a closure that writes steps keeps it out
      // of a register for the whole step.
      if (work) work.steps += a1 - a0 + 2 * (b1 - b0) + read;
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
      steps += hi - lo;
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
    if (work) work.steps += steps;
    return layer.some((s, q) => was[q] !== s);
  };
}

// Crossings between each two adjacent layers, each edge counted with its
// multiplicity, as d3-dag counts them. work, if given, counts the steps (see
// Work): each piece and edge read, each comparison of a sort and each node of
// the Fenwick tree visited.
export function crossings(layers: any[][], work?: Work): number {
  let total = 0, steps = 0;
  for (let k = 0; k + 1 < layers.length; k++) {
    const below = new Map(layers[k + 1].map((s, i) => [s, i]));
    const w = layers[k + 1].length;
    const tree = new Float64Array(w + 1);
    let seen = 0;
    steps += 2 * w;
    for (const s of layers[k]) {
      const out: [number, number][] = [];
      for (const [c, n] of s.childCounts()) out.push([below.get(c)!, n]);
      out.sort(work ? (a, b) => (work.steps++, a[0] - b[0]) : (a, b) => a[0] - b[0]);
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
      // The Fenwick tree nodes the two loops above visit, walked again only
      // when counting: a count inside them cost 1.3 percent more
      // instructions in decrossSeeded (DAGVIEW-counter-cost, 2026-11-11). A
      // change to either loop must change its walk here too.
      if (work) {
        steps += 1 + out.length;
        for (const [c] of out) {
          for (let i = c + 1; i > 0; i -= i & -i) steps++;
          for (let i = c + 1; i <= w; i += i & -i) steps++;
        }
      }
    }
  }
  if (work) work.steps += steps;
  return total;
}
