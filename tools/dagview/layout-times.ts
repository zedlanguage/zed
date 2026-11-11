// For layout-time.test.ts (d3-dag) and layout-time-elk.test.ts: times one
// layout of a plan-shaped graph of 1,000 nodes and 2,700 edges and one of
// 4,000 nodes and 10,800 edges (see synthetic.ts), and one of the plan
// as /api/state gave it on 2026-11-10 (plan-graph-2026-11-10.json: 1,661
// nodes, 2,580 edges, the sizes the page asks for), by each layout method.
//
// ELK: with network-simplex node placement the 1,000-node layout had not
// finished after 300 s (stopped there, load 17 to 24 on 32 cores, 2026-11-07);
// the plan of 2026-11-07 took 240 s. With the options in layout.ts they took 5
// to 11 s and 19 to 25 s at load 33 to 37; with the second pass (layoutTwice)
// 4.5 s and 19 s at load 8 to 10, and 13 s and 39 s at load 33 (2026-11-10),
// the plan of 2026-11-10 8 to 15 s. At load 56 to 65 the 4,000-node layout
// did not finish in 60 s even alone (2026-11-10), nor at load 76 to 82 before
// d3-dag was added.
// d3-dag (operators in d3dag.ts): 3.5 to 6 s, 27 s and 5.7 s at load 30 to
// 37; 19 s, 45 s and 14 s at load 60.
//
// Each must also come out no wider for its height than it did when the method
// was chosen. ELK, 2026-11-07: 4,795 x 12,058 px (0.40) and 4,749 x 48,822 px
// (0.097), and on 2026-11-10 the plan 28,725 x 16,792 (1.71); Brandes-Koepf
// placement alone gave 34,412 x 12,130 (2.8) and 76,965 x 48,804 (1.6).
// d3-dag, 2026-11-10: 4,576 x 12,058 (0.38), 4,868 x 48,698 (0.0999) and the
// plan 33,742 x 11,306 (2.98); with d3-dag's greedy coordinates and no
// narrowing the plan was 57,580 x 11,306 (5.1).

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { describe, test } from "node:test";
import { layoutInWorker } from "./layout.ts";
import type { Graph, Method } from "./layout.ts";
import { planLike } from "./synthetic.ts";

const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;
const cases: [string, () => Graph, Record<Method, number>][] = [
  ["a plan-shaped graph of 1000 nodes and 2700 edges", () => planLike(1000, 2700), { elk: 0.41, d3dag: 0.39 }],
  ["a plan-shaped graph of 4000 nodes and 10800 edges", () => planLike(4000, 10800), { elk: 0.1, d3dag: 0.101 }],
  ["the plan of 2026-11-10", () => plan, { elk: 1.75, d3dag: 3.0 }],
];

// The cases of one method run at once, each in its own worker, so a file takes
// as long as its largest; each method has its own file, so that at load 35 on
// 32 cores neither file takes more than 60 s (all six at once in one file did).
export function layoutTimes(method: Method): void {
  describe(`layout time, ${method}`, { concurrency: true }, () => {
    for (const [name, make, ratio] of cases) {
      test(`${name} is laid out by ${method} within 60 s, top to bottom and narrow, every node placed and every edge drawn`, { timeout: 60_000 }, async () => {
        const g = { ...make(), method };
        const t0 = Date.now();
        const l = await layoutInWorker(g);
        console.log(`${method}, ${name}: ${Date.now() - t0} ms, ${Math.round(l.w)} x ${Math.round(l.h)} px`);
        assert.equal(Object.keys(l.boxes).length, g.nodes.length);
        for (const n of g.nodes) assert.ok(l.boxes[n.id], `${n.id} has no place`);
        for (const [a, b] of g.edges) assert.ok(l.boxes[a].y < l.boxes[b].y, `${a} -> ${b} points upward`);
        assert.equal(l.edges.length, g.edges.length);
        const drawn = new Set(l.edges.map((e) => `${e.from} ${e.to}`));
        for (const [a, b] of g.edges) assert.ok(drawn.has(`${a} ${b}`), `${a} -> ${b} is not drawn`);
        for (const e of l.edges) assert.ok(e.points.length >= 2 && e.points.every((p) => Number.isFinite(p.x) && Number.isFinite(p.y)));
        assert.ok(l.w / l.h < ratio[method], `width / height ${(l.w / l.h).toFixed(3)} is not under ${ratio[method]}`);
      });
    }
  });
}
