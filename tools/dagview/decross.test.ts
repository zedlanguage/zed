// Crossing reduction from an earlier order (decrossSeeded in d3dag.ts) scales
// as n log n on a graph of fixed depth and growing width; d3-dag's own
// two-layer greedy sweep, which counts crossings by comparing every pair of
// nodes in a layer, is the negative control and does not.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { decrossTwoLayer, twolayerGreedy } from "d3-dag";
import { crossings, decrossSeeded } from "./d3dag.ts";
import type { Work } from "./d3dag.ts";

// L layers of w nodes; node p of layer l has children p - 2 and p + 1 of
// layer l + 1 (clamped to the layer), so the picture in order of p has few
// crossings. The seed is p moved by up to 3 places at random (a fixed
// generator), as an earlier layout's order is near a good one. The nodes are
// stand-ins for d3-dag's sugiyama nodes: the fields decrossSeeded and d3-dag's
// decrossTwoLayer read. reads, if given, counts each call of the neighbor
// lists and each neighbor in them: d3-dag's code is not ours to count, and its
// costly loops, the pairs of its crossing count and of its greedy gains, each
// read a neighbor list per step.
function wide(L: number, w: number, reads?: Work) {
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
  const read = (list: number[]) => { if (reads) reads.steps += 1 + list.length; return list.map((c) => [s[c], 1]); };
  s.forEach((v, i) => {
    v.childCounts = () => read(children[i]);
    v.parentCounts = () => read(parents[i]);
    v.children = () => children[i].map((c) => s[c]);
    v.parents = () => parents[i].map((c) => s[c]);
  });
  const layers = Array.from({ length: L }, (_, l) => s.slice(l * w, (l + 1) * w));
  return { layers, x, y, index: new Map(s.map((_, i) => [i, i])) };
}

// The steps and the time of one run on a graph made before it, after a run on
// another graph of the same size, so that the time is not that of the first,
// unoptimized run. The test compares the steps: a ratio of times measured
// contention under parallel load (merge batch 131, 2026-11-11: the control's
// ratio fell to 18.3, under its bound, with nothing changed). The time is
// only logged.
function measured(make: (work: Work) => () => void): { steps: number; ms: number } {
  make({ steps: 0 })();
  const work = { steps: 0 };
  const run = make(work);
  work.steps = 0;
  const t0 = performance.now();
  run();
  return { steps: work.steps, ms: performance.now() - t0 };
}

test("crossing reduction from a seeded order scales as n log n in the layer width: 12 layers of 150 and of 1200 nodes; d3-dag's two-layer greedy sweep from the same order (the negative control) grows as the width squared", () => {
  const L = 12, w = 150;
  const seeded = (k: number) => (work: Work) => { const g = wide(L, k); return () => decrossSeeded(g.index, g.x, g.y, undefined, work)(g.layers); };
  const ours = [w, 8 * w].map((k) => measured(seeded(k)));
  // The result is no worse than the seed.
  const g = wide(L, 8 * w);
  for (const row of g.layers) row.sort((p: any, q: any) => g.x[p.data.node] - g.x[q.data.node]);
  const before = crossings(g.layers);
  decrossSeeded(g.index, g.x, g.y)(g.layers);
  const after = crossings(g.layers);
  assert.ok(after <= before, `${after} crossings after, ${before} before`);
  // The control's steps are its reads of neighbor lists (wide), the seeded
  // path's those of decrossSeeded (Work in d3dag.ts).
  const greedy = (k: number) => (reads: Work) => {
    const h = wide(L, k, reads);
    for (const row of h.layers) row.sort((p: any, q: any) => h.x[p.data.node] - h.x[q.data.node]);
    return () => decrossTwoLayer().order(twolayerGreedy()).inits([]).passes(1)(h.layers as any);
  };
  const control = [w, 8 * w].map((k) => measured(greedy(k)));
  // 8 times the nodes at n log n is 8 log(8n) / log n times the steps, about
  // 10; the limit is twice that. The control's pair loops grow as w^2, 64
  // times, and its ratio must be above the limit.
  const load = readFileSync("/proc/loadavg", "utf8").split(" ")[0];
  const limit = 2 * 8 * (Math.log2(8 * w * L) / Math.log2(w * L));
  const ratio = ours[1].steps / ours[0].steps, controlRatio = control[1].steps / control[0].steps;
  const show = (r: { steps: number; ms: number }[]) => `${r[0].steps} and ${r[1].steps} steps (ratio ${(r[1].steps / r[0].steps).toFixed(2)}), ${r[0].ms.toFixed(1)} and ${r[1].ms.toFixed(1)} ms (ratio ${(r[1].ms / r[0].ms).toFixed(1)})`;
  console.log(`seeded: ${show(ours)}, crossings ${before} -> ${after}; d3-dag greedy: ${show(control)}; step limit ${limit.toFixed(1)}; load ${load}`);
  assert.ok(ratio < limit, `seeded: ${show(ours)}`);
  assert.ok(controlRatio > limit, `control: ${show(control)}: the test would not tell n log n from w^2`);
});
