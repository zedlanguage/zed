// Times one layout of a plan-shaped graph of 1,000 nodes and 2,700 edges and
// one of 4,000 nodes and 10,800 edges (see synthetic.ts). With network-simplex
// node placement the 1,000-node layout had not finished after 300 s (stopped
// there, load 17 to 24 on 32 cores, 2026-11-07); the plan of 2026-11-07 took
// 240 s. With the options in layout.ts they took 5 to 11 s and 19 to 25 s at
// load 33 to 37.

import assert from "node:assert/strict";
import { describe, test } from "node:test";
import { layoutInWorker } from "./layout.ts";
import { planLike } from "./synthetic.ts";

// The two run at once, each in its own worker, so the file takes as long as the larger.
describe("layout time", { concurrency: true }, () => {
  for (const [n, e] of [[1000, 2700], [4000, 10800]]) {
    test(`a plan-shaped graph of ${n} nodes and ${e} edges is laid out within 60 s, top to bottom`, { timeout: 60_000 }, async () => {
      const g = planLike(n, e);
      const t0 = Date.now();
      const l = await layoutInWorker(g);
      console.log(`${n} nodes, ${e} edges: ${Date.now() - t0} ms, ${Math.round(l.w)} x ${Math.round(l.h)} px`);
      assert.equal(Object.keys(l.boxes).length, n);
      for (const [a, b] of g.edges) assert.ok(l.boxes[a].y < l.boxes[b].y, `${a} -> ${b} points upward`);
      assert.equal(l.edges.length, e);
    });
  }
});
