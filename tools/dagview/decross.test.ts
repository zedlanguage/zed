// Crossing reduction from an earlier order (decrossSeeded in d3dag.ts) scales
// as n log n on a graph of fixed depth and growing width; d3-dag's own
// two-layer greedy sweep, which counts crossings by comparing every pair of
// nodes in a layer, is the negative control and does not.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { decrossTwoLayer, twolayerGreedy } from "d3-dag";
import { crossings, decrossSeeded } from "./d3dag.ts";

// L layers of w nodes; node p of layer l has children p - 2 and p + 1 of
// layer l + 1 (clamped to the layer), so the picture in order of p has few
// crossings. The seed is p moved by up to 3 places at random (a fixed
// generator), as an earlier layout's order is near a good one. The nodes are
// stand-ins for d3-dag's sugiyama nodes: the fields decrossSeeded and d3-dag's
// decrossTwoLayer read.
function wide(L: number, w: number) {
  const n = L * w;
  const y = Int32Array.from({ length: n }, (_, i) => Math.floor(i / w));
  const x = new Float64Array(n);
  const children: number[][] = [], parents: number[][] = Array.from({ length: n }, () => []);
  let r = 12345;
  const random = () => { r = (r * 1103515245 + 12345) & 0x7fffffff; return r / 0x7fffffff; };
  for (let i = 0; i < n; i++) {
    const l = y[i], p = i % w;
    x[i] = p + (random() - 0.5) * 6;
    children.push(l + 1 < L ? [...new Set([-2, 1].map((d) => (l + 1) * w + Math.min(w - 1, Math.max(0, p + d))))] : []);
  }
  children.forEach((cs, i) => { for (const c of cs) parents[c].push(i); });
  const s: any[] = Array.from({ length: n }, (_, i) => ({ data: { role: "node", node: i } }));
  s.forEach((v, i) => {
    v.childCounts = () => children[i].map((c) => [s[c], 1]);
    v.parentCounts = () => parents[i].map((c) => [s[c], 1]);
    v.children = () => children[i].map((c) => s[c]);
    v.parents = () => parents[i].map((c) => s[c]);
  });
  const layers = Array.from({ length: L }, (_, l) => s.slice(l * w, (l + 1) * w));
  return { layers, x, y, index: new Map(s.map((_, i) => [i, i])) };
}

// The least time of three runs, each on a fresh graph made before timing.
function best(make: () => () => void): number {
  let t = Infinity;
  for (let k = 0; k < 3; k++) {
    const run = make();
    const t0 = performance.now();
    run();
    t = Math.min(t, performance.now() - t0);
  }
  return t;
}

test("crossing reduction from a seeded order scales as n log n in the layer width: 12 layers of 150 and of 1200 nodes; d3-dag's two-layer greedy sweep from the same order (the negative control) grows as the width squared", () => {
  const L = 12, w = 150;
  const seeded = (k: number) => () => { const g = wide(L, k); return () => decrossSeeded(g.index, g.x, g.y)(g.layers); };
  const ours = [w, 8 * w].map((k) => best(seeded(k)));
  // The result is no worse than the seed.
  const g = wide(L, 8 * w);
  for (const row of g.layers) row.sort((p: any, q: any) => g.x[p.data.node] - g.x[q.data.node]);
  const before = crossings(g.layers);
  decrossSeeded(g.index, g.x, g.y)(g.layers);
  const after = crossings(g.layers);
  assert.ok(after <= before, `${after} crossings after, ${before} before`);
  const control = [w, 8 * w].map((k) => {
    const h = wide(L, k);
    for (const row of h.layers) row.sort((p: any, q: any) => h.x[p.data.node] - h.x[q.data.node]);
    const t0 = performance.now();
    decrossTwoLayer().order(twolayerGreedy()).inits([]).passes(1)(h.layers as any);
    return performance.now() - t0;
  });
  // 8 times the nodes at n log n is 8 log(8n) / log n times the time, about
  // 10; the limit is twice that, and more when the 1-minute load is above the
  // 32 cores. The control's ratio, 64 if its pair count were all its time,
  // measured 33 to 39 at loads 28 to 46, and must be above the limit without
  // the load allowance, as load slows both of its runs.
  const load = Number(readFileSync("/proc/loadavg", "utf8").split(" ")[0]);
  const base = 2 * 8 * (Math.log2(8 * w * L) / Math.log2(w * L)), limit = base * Math.max(1, load / 32);
  const ratio = ours[1] / ours[0], controlRatio = control[1] / control[0];
  console.log(`seeded: ${ours[0].toFixed(1)} and ${ours[1].toFixed(1)} ms (ratio ${ratio.toFixed(1)}), crossings ${before} -> ${after}; d3-dag greedy: ${control[0].toFixed(1)} and ${control[1].toFixed(1)} ms (ratio ${controlRatio.toFixed(1)}); limit ${limit.toFixed(1)} at load ${load}`);
  assert.ok(ratio < limit, `seeded ratio ${ratio.toFixed(1)}`);
  assert.ok(controlRatio > base, `control ratio ${controlRatio.toFixed(1)}: the test would not tell n log n from w^2`);
});
