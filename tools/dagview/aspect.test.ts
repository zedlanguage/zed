// DAGVIEW-aspect: the drawn shape is held to the band w/h in [0.4, 0.6]
// (BAND in d3dag.ts). The 20-relayout tests are in aspect-live.test.ts,
// aspect-plan.test.ts and aspect-synthetic.test.ts, and the relayout from
// layers as tall as the page drew on 2026-11-13 in aspect-tall.test.ts.
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { balanceCounts, balanceLayers, d3dagLayout, fitLayers, fromPrevious, layersAt, lowerSources, makeRoom, operators, spreadSources } from "./d3dag.ts";
import type { Work } from "./d3dag.ts";
import { inBand } from "./generations.ts";
import type { Graph, Layout } from "./layout.ts";
import { planLike } from "./synthetic.ts";

const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;

const again = (g: Graph, l: Omit<Layout, "key">) =>
  d3dagLayout(g, operators, l.layers, Object.fromEntries(Object.entries(l.boxes).map(([id, b]) => [id, { x: b.x, y: b.y }])), l.edges, l.rowLimit);

// The first relayout after a layout from scratch keeps the layers, K and the
// height, but moves boxes sideways: from scratch the order within each row
// starts from d3-dag's, on a relayout from the earlier positions, so a
// different crossing-reduction result is placed. That was so before this
// change too (on the plan 1,465 of 1,509 boxes moved, by up to 3,734 px);
// from then on the layout is a fixed point, which the second check asserts.
// The width is the widest drawn row, and splitRows picks the drawn rows from
// those x, so it can change too: on main at ca7c70736 planLike(n, 2.7n) kept
// it only at n = 500 of 300, 400, 450, 500, 550, 600, 700 and 800, by up to
// 54 px (DAGVIEW-spread-scaling); the relayout is held to the band instead,
// until DAGVIEW-first-relayout-x makes the first relayout keep the x.
// Compared as JSON, as assert.deepEqual on a mismatch of layouts this size
// spends minutes building its message.
test("an unchanged graph laid out again keeps its layers, row limit and height, and from a relayout the layout exactly: the plan and a plan-shaped graph of 500 nodes", () => {
  for (const [what, g] of [["the plan", plan], ["a plan-shaped graph of 500 nodes", planLike(500, 1350)]] as const) {
    const l0 = d3dagLayout(g);
    inBand(l0, what);
    const l1 = again(g, l0);
    assert.ok(JSON.stringify(l1.layers) === JSON.stringify(l0.layers), `${what}: layers changed`);
    assert.equal(l1.rowLimit, l0.rowLimit, what);
    assert.equal(l1.h, l0.h, what);
    inBand(l1, `${what}, relaid out`);
    assert.ok(JSON.stringify(again(g, l1)) === JSON.stringify(l1), `${what}: the layout changed on a second relayout`);
  }
});

// Rows of w = sqrt(0.54 n) nodes of 210 x 52 px (one row per layer would
// draw about 1:0.83), and 2.7 n edges as planLike draws them: 3 in 4 from
// the one or two rows above, 1 in 4 from up to 30 rows above. Unlike
// planLike, whose rows are 10 nodes at every n so that its longest path
// fixes the height and K stays near 22, here K grows with n (23 at 4,000
// nodes, 64 at 32,000), so the search for K is measured where it grows.
function wide(n: number, seed = 12345) {
  const row = Math.round(Math.sqrt(0.54 * n));
  const rand = (k: number) => { seed = (Math.imul(seed, 1103515245) + 12345) >>> 0; return (seed >>> 8) % k; };
  const parents: number[][] = Array.from({ length: n }, () => []), children: number[][] = Array.from({ length: n }, () => []);
  const seen = new Set<number>();
  for (let m = 0; m < 2.7 * n;) {
    const to = row + rand(n - row), back = 1 + (rand(4) < 3 ? rand(2) : rand(30)), fromRow = Math.floor(to / row) - back;
    if (fromRow < 0) continue;
    const from = fromRow * row + rand(row);
    if (seen.has(from * n + to)) continue;
    seen.add(from * n + to);
    parents[to].push(from);
    children[from].push(to);
    m++;
  }
  // Longest-path layers balanced as from scratch (balanceCounts,
  // lowerSources), without network simplex, which is d3-dag's and not counted.
  const y = fromPrevious(new Array(n).fill(0), parents, children)!;
  balanceCounts(y, parents, children);
  lowerSources(y, parents, children);
  return { y, parents, children, row, size: { w: new Float64Array(n).fill(210), h: new Float64Array(n).fill(52) } };
}

test("fitLayers scales as n log n: graphs of 4,000 and 32,000 nodes whose row limit grows with n, under 10.5 times the steps at 8n", () => {
  const r = [4000, 32000].map((n) => {
    const b = wide(n);
    const work: Work = { steps: 0 };
    const t0 = performance.now();
    const f = fitLayers(b.y, b.size, b.parents, b.children, 1, work);
    return { n, K: f.K, ratio: f.ratio, steps: work.steps, ms: performance.now() - t0 };
  });
  const q = r[1].steps / r[0].steps;
  // The negative control, run once and not kept: trying every K from 1 up
  // while the estimate is within BAND took 37.3 million steps at 4,000 nodes
  // and 1,114 million at 32,000, 29.8 times. A search for the largest K
  // within BAND (bisection guided by the same guess) took 13.6 times, as its
  // probes grew with log K (8 to 10).
  console.log(`fitLayers: ${r.map((x) => `n ${x.n}: K ${x.K}, estimated w/h ${x.ratio.toFixed(3)}, ${x.steps} steps, ${x.ms.toFixed(0)} ms`).join("; ")}; ratio ${q.toFixed(2)}, limit 10.5`);
  for (const x of r) assert.ok(x.ratio >= 0.4 && x.ratio <= 0.6, `n ${x.n}: estimated w/h ${x.ratio.toFixed(3)}`);
  assert.ok(q < 10.5, `ratio ${q.toFixed(2)}`);
});

// layersAt on the wide graphs at K = row / 4 and row / 2, so that K grows
// with n as fitLayers chooses it (row / 2 is 23 at 4,000 nodes and 66 at
// 32,000; fitLayers takes 23 and 64). At a K fixed for both sizes the excess
// over K per node grows with n (0.51 to 0.83 at K = 23), and with it the
// moves any method must make, so no limit near n log n holds there. The
// negative control, run once and not kept: on main before
// DAGVIEW-spread-scaling, where balanceLayers read every node each pass until
// a pass moved nothing, these four took 11.27, 10.85, 11.87 and 15.19 times
// the steps at 8n.
test("layersAt scales as n log n on the wide graphs: 4,000 and 32,000 nodes, K = row / 4 and row / 2, seeds 12345 and 777, under 10.5 times the steps at 8n", () => {
  const out: string[] = [];
  for (const seed of [12345, 777]) for (const f of [0.25, 0.5]) {
    const r = [4000, 32000].map((n) => {
      const b = wide(n, seed);
      const K = Math.round(f * b.row);
      const work: Work = { steps: 0 };
      const y = layersAt(b.y, b.parents, b.children, K, work);
      for (let i = 0; i < n; i++) for (const k of b.children[i]) assert.ok(y[i] < y[k], `edge ${i} -> ${k} does not go down`);
      return { K, steps: work.steps };
    });
    const q = r[1].steps / r[0].steps;
    out.push(`seed ${seed}, K ${r[0].K} and ${r[1].K}: ${r[0].steps} and ${r[1].steps} steps, ratio ${q.toFixed(2)}`);
    assert.ok(q < 10.5, out[out.length - 1]);
  }
  console.log(`layersAt on wide graphs: ${out.join("; ")}; limit 10.5`);
});

// balanceLayers reads a node again only when a change may allow it to move
// (see its complexity note), so it must still end where no node can move:
// one more call moves nothing and returns 1. Wide graphs of 2,000 nodes on
// four seeds at four K, after makeRoom, and again after the whole loop of
// layersAt (with spreadSources, whose moves change the counts). The waits
// were found to miss moves twice while this was built, each caught here: a
// node whose own row rose while a row of its slack fell, and a child released
// by a moved source. Dropping either wait on a fall fails it too (run once as
// a control, not kept).
test("balanceLayers ends where no node can move: a second call makes no move, on wide graphs of 2,000 nodes, four seeds, K = 4, row / 4, row / 2 and row", () => {
  for (const seed of [12345, 777, 4242, 9001]) {
    const b = wide(2000, seed);
    for (const K of [4, Math.round(b.row / 4), Math.round(b.row / 2), b.row]) {
      const y = Int32Array.from(b.y);
      makeRoom(y, K);
      balanceLayers(y, b.parents, b.children, K);
      assert.equal(balanceLayers(y, b.parents, b.children, K, (i, from, to) => assert.fail(`seed ${seed}, K ${K}: node ${i} moved ${from} -> ${to}`)), 1);
      const z = layersAt(b.y, b.parents, b.children, K);
      assert.equal(balanceLayers(z, b.parents, b.children, K, (i, from, to) => assert.fail(`seed ${seed}, K ${K}, after layersAt: node ${i} moved ${from} -> ${to}`)), 1);
      assert.equal(spreadSources(z, b.parents, b.children, K, (i, from, to) => assert.fail(`seed ${seed}, K ${K}, after layersAt: spreadSources moved ${i} ${from} -> ${to}`)), 1);
    }
  }
});

test("layersAt on an empty graph gives no layers, and on a single node puts it in layer 0", () => {
  assert.equal(layersAt(new Int32Array(0), [], [], 3).length, 0);
  assert.deepEqual([...layersAt(Int32Array.from([5]), [[]], [[]], 3)], [0]);
});
