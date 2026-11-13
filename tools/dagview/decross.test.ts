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
  // 8 times the nodes at n log n is 8 log(8n) / log n times the steps, 10.2
  // here; the limit is the standing 10.5. Before DAGVIEW-seeded-scale every
  // pass rebuilt all the gains and the passes grew from 4 to 5, so the ratio
  // was 10.73, and the limit was twice n log n (20.4). The control's pair
  // loops grow as w^2, 64 times, and its ratio must be above the limit.
  const load = readFileSync("/proc/loadavg", "utf8").split(" ")[0];
  const limit = 10.5;
  const ratio = ours[1].steps / ours[0].steps, controlRatio = control[1].steps / control[0].steps;
  const show = (r: { steps: number; ms: number }[]) => `${r[0].steps} and ${r[1].steps} steps (ratio ${(r[1].steps / r[0].steps).toFixed(2)}), ${r[0].ms.toFixed(1)} and ${r[1].ms.toFixed(1)} ms (ratio ${(r[1].ms / r[0].ms).toFixed(1)})`;
  console.log(`seeded: ${show(ours)}, crossings ${before} -> ${after}; d3-dag greedy: ${show(control)}; step limit ${limit.toFixed(1)}; load ${load}`);
  assert.ok(ratio < limit, `seeded: ${show(ours)}`);
  assert.ok(controlRatio > limit, `control: ${show(control)}: the test would not tell n log n from w^2`);
});

// Two layers of w nodes; node p of the top layer has the one child p of the
// bottom layer, and the seed puts the bottom layer in the order 1 0 3 2 5 4
// ..., each pair crossed. One greedy step uncrosses every pair, and each swap
// splits off the two pieces before it, so a sweep that rescans the rest of
// the range after each swap reads w^2 / 4 pairs (DAGVIEW-aspect-plan-time).
function pairs(w: number) {
  const n = 2 * w;
  const y = Int32Array.from({ length: n }, (_, i) => (i < w ? 0 : 1));
  const x = Float64Array.from({ length: n }, (_, i) => (i < w ? i : (i - w) ^ 1));
  const s: any[] = Array.from({ length: n }, (_, i) => ({ data: { role: "node", node: i } }));
  s.forEach((v, i) => {
    v.childCounts = () => (i < w ? [[s[w + i], 1]] : []);
    v.parentCounts = () => (i < w ? [] : [[s[i - w], 1]]);
  });
  const layers = [s.slice(0, w), s.slice(w)];
  for (const row of layers) row.sort((p: any, q: any) => x[p.data.node] - x[q.data.node]);
  return { layers, x, y, index: new Map(s.map((_, i) => [i, i])) };
}

test("a greedy step that swaps many pairs scales as n log n in the layer width: two layers of 2048 and of 16384 nodes, every pair of the seed crossed", () => {
  const w = 2048;
  const run = (k: number) => (work: Work) => { const g = pairs(k); return () => decrossSeeded(g.index, g.x, g.y, undefined, work)(g.layers); };
  const ours = [w, 8 * w].map((k) => measured(run(k)));
  const g = pairs(8 * w);
  const before = crossings(g.layers);
  decrossSeeded(g.index, g.x, g.y)(g.layers);
  assert.equal(before, 4 * w);
  assert.equal(crossings(g.layers), 0);
  // 8 times the nodes at n log n is 8 log(8n) / log n times the steps, 10
  // here; the scan of the rest of the range after each swap grows 64 times.
  const ratio = ours[1].steps / ours[0].steps;
  const load = readFileSync("/proc/loadavg", "utf8").split(" ")[0];
  console.log(`pairs: ${ours[0].steps} and ${ours[1].steps} steps (ratio ${ratio.toFixed(2)}), ${ours[0].ms.toFixed(1)} and ${ours[1].ms.toFixed(1)} ms; load ${load}`);
  assert.ok(ratio < 10.5, `pairs: step ratio ${ratio.toFixed(2)}`);
});

// Small layers: none, one and two nodes, odd widths and ties. Each case is a
// top layer in order and a bottom layer whose seed order is given; the
// greedy step swaps the leftmost pair of the largest gain first, as d3-dag's
// twolayerGreedy does, so a tie keeps the left pair.
test("the greedy step on small layers: empty, one node, two nodes, odd widths, ties", () => {
  const cases: [number[], number[][], number[], number][] = [
    // bottom seed order, each bottom node's parents, the order after, crossings after
    [[], [], [], 0],
    [[0], [[0]], [0], 0],
    [[0, 1], [[0], [1]], [0, 1], 0],
    [[1, 0], [[0], [1]], [0, 1], 0],
    [[1, 0, 2], [[0], [1], [2]], [0, 1, 2], 0],
    // The step swaps 2 1, then 2 0, and splits the range there, so 1 0 stays,
    // as in d3-dag; the sweep up then puts the top layer in the order 1 0 2.
    [[2, 1, 0], [[0], [1], [2]], [1, 0, 2], 0],
    // 0 and 1 share both parents: no order is better, the seed stays.
    [[1, 0], [[0, 1], [0, 1]], [1, 0], 1],
  ];
  for (const [seed, parentsOf, after, left] of cases) {
    const w = seed.length, top = Math.max(1, ...parentsOf.flat().map((p) => p + 1));
    const n = top + w;
    const y = Int32Array.from({ length: n }, (_, i) => (i < top ? 0 : 1));
    const x = Float64Array.from({ length: n }, (_, i) => (i < top ? i : seed.indexOf(i - top)));
    const s: any[] = Array.from({ length: n }, (_, i) => ({ data: { role: "node", node: i } }));
    s.forEach((v, i) => {
      v.childCounts = () => (i < top ? parentsOf.flatMap((ps, b) => (ps.includes(i) ? [[s[top + b], 1]] : [])) : []);
      v.parentCounts = () => (i < top ? [] : parentsOf[i - top].map((p) => [s[p], 1]));
    });
    const layers = [s.slice(0, top), s.slice(top)];
    for (const row of layers) row.sort((p: any, q: any) => x[p.data.node] - x[q.data.node]);
    decrossSeeded(new Map(s.map((_, i) => [i, i])), x, y)(layers);
    const got = layers[1].map((v: any) => v.data.node - top);
    assert.deepEqual(got, after, `seed ${seed}`);
    assert.equal(crossings(layers), left, `seed ${seed}`);
  }
});

// A pass that leaves more crossings than the best order before it is rolled
// back. Here the second pass puts node 4 right of node 2 in the middle layer
// (order 2 4 3), which has more crossings than 4 2 3 after the first pass, so
// 4 2 3 is the result. Without the roll-back the result is 2 4 3. The graph
// was found by a search over small random graphs (DAGVIEW-seeded-scale); the
// earlier form, which copied the best order, gives the same.
test("the passes keep the best order: a pass that leaves more crossings is undone", () => {
  const x = [97, 14, 25, 87, 6, 86, 82];
  const children = [[2, 3], [4], [6], [5], [5], [], []];
  const n = x.length, parents: number[][] = Array.from({ length: n }, () => []);
  children.forEach((cs, i) => { for (const c of cs) parents[c].push(i); });
  const y = Int32Array.from({ length: n }, (_, i) => (i < 2 ? 0 : i < 5 ? 1 : 2));
  const s: any[] = Array.from({ length: n }, (_, i) => ({ data: { role: "node", node: i } }));
  s.forEach((v, i) => {
    v.childCounts = () => children[i].map((c) => [s[c], 1]);
    v.parentCounts = () => parents[i].map((c) => [s[c], 1]);
  });
  const layers = [s.slice(0, 2), s.slice(2, 5), s.slice(5)];
  decrossSeeded(new Map(s.map((_, i) => [i, i])), Float64Array.from(x), y)(layers);
  assert.deepEqual(layers.map((l) => l.map((v: any) => v.data.node)), [[1, 0], [4, 2, 3], [6, 5]]);
  assert.equal(crossings(layers), 1);
});
