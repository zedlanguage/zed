// Times one layout of a plan-shaped graph of 1,000 nodes and 2,700 edges, one
// of 4,000 nodes and 10,800 edges (see synthetic.ts), and one of the plan as
// /api/state gave it on 2026-11-10 (plan-graph-2026-11-10.json: 1,661 nodes,
// 2,580 edges, the sizes the page asks for).
//
// d3-dag (operators in d3dag.ts): 3.5 to 6 s, 27 s and 5.7 s at load 30 to
// 37; 19 s, 45 s and 14 s at load 60 (2026-11-10). ELK, the method before,
// took 13 s, 39 s and 8 to 15 s at load 33, and the 4,000-node layout did not
// finish in 60 s at load 56 to 82.
//
// With the layers rebalanced by width (2026-11-10): 8.8 s, 43 s and 9.9 s at
// load 60. With the layers balanced by count, long rows split and the faster
// crossing count (layers and decrossSweeps in d3dag.ts, 2026-11-11): 3.5 s,
// 20 s and 6.9 s at load 50 to 60.
//
// Each must also come out no wider for its height than it did when the count
// balancing was added (2026-11-11): 4,014 x 12,058 px (0.333), 4,508 x 48,698
// (0.0926) and the plan 6,390 x 14,516 (0.440). The width rule before it gave
// 4,092 x 12,058, 4,198 x 48,698 and 14,962 x 11,528; simplex layers alone: 4,576 x 12,058, 4,868 x 48,698 and 33,742 x 11,306. With d3-dag's
// greedy coordinates and no narrowing the plan was 57,580 x 11,306; ELK gave
// 4,795 x 12,058, 4,749 x 48,822 and 28,725 x 16,792.
//
// With edges shortened within rows of at most the split limit (balanceLayers
// in d3dag.ts, 2026-11-11) the limits were raised: 4,230 x 12,058 (0.351),
// 4,444 x 48,698 (0.0913) and the plan 8,862 x 11,824 (0.749). The plan is
// wider because its rows now fill to the split limit and none is over it, so
// none is split: 104 rows, 11,824 px high against 14,516. On the live plan of
// 2026-11-11 (1,682 nodes) the width did not change: 7,550 px before and
// after, 126 rows, as rows over the limit that no move can empty are split
// as before. The spring weight does not change it: with W = 1, 4, 16 and
// 2K + 1 in balanceLayers the plan was 8,844 to 8,888 px wide.
//
// With every source directly above its highest child (lowerSources,
// spreadSources and the source rule of splitRows in d3dag.ts, 2026-11-11) the
// limits stand: 4,322 x 12,058 (0.358), 4,594 x 48,698 (0.0943, close to its
// limit of 0.095) and the plan 8,756 x 11,930 (0.734), at load 20 to 30.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { describe, test } from "node:test";
import { layoutInWorker } from "./layout.ts";
import type { Graph } from "./layout.ts";
import { planLike } from "./synthetic.ts";

const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;
const cases: [string, () => Graph, number][] = [
  ["a plan-shaped graph of 1000 nodes and 2700 edges", () => planLike(1000, 2700), 0.37],
  ["a plan-shaped graph of 4000 nodes and 10800 edges", () => planLike(4000, 10800), 0.095],
  ["the plan of 2026-11-10", () => plan, 0.77],
];

// The three run at once, each in its own worker, so the file takes as long as the largest.
describe("layout time", { concurrency: true }, () => {
  for (const [name, make, ratio] of cases) {
    test(`${name} is laid out within 60 s, top to bottom and narrow, every node placed and every edge drawn`, { timeout: 60_000 }, async () => {
      const g = make();
      const t0 = Date.now();
      const l = await layoutInWorker(g);
      console.log(`${name}: ${Date.now() - t0} ms, ${Math.round(l.w)} x ${Math.round(l.h)} px`);
      assert.equal(Object.keys(l.boxes).length, g.nodes.length);
      for (const n of g.nodes) assert.ok(l.boxes[n.id], `${n.id} has no place`);
      for (const [a, b] of g.edges) assert.ok(l.boxes[a].y < l.boxes[b].y, `${a} -> ${b} points upward`);
      assert.equal(l.edges.length, g.edges.length);
      const drawn = new Set(l.edges.map((e) => `${e.from} ${e.to}`));
      for (const [a, b] of g.edges) assert.ok(drawn.has(`${a} ${b}`), `${a} -> ${b} is not drawn`);
      for (const e of l.edges) assert.ok(e.points.length >= 2 && e.points.every((p) => Number.isFinite(p.x) && Number.isFinite(p.y)));
      assert.ok(l.w / l.h < ratio, `width / height ${(l.w / l.h).toFixed(3)} is not under ${ratio}`);
    });
  }
});
