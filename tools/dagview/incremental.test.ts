// Lays the plan of 2026-11-10 out, then two changed graphs both from that
// layout's layers (Layout.layers, see layers in d3dag.ts) and from scratch,
// and logs how far apart they come out: rows, the most boxes in a row, and
// crossings of the drawn edges.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { describe, test } from "node:test";
import { layoutInWorker } from "./layout.ts";
import type { Graph, Layout } from "./layout.ts";

const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;

// Rows, the most boxes in one row and the crossings of the drawn edges: in
// the band between each two adjacent rows each edge is a segment from its x
// in the upper row to its x in the lower, and two segments cross when their
// ends are in opposite orders. Segments sharing an end do not cross.
// Complexity tradeoff: comparing every pair of segments in a band is O(s^2)
// for s segments; sorting by the upper end and counting, with a Fenwick tree,
// the earlier segments whose lower end lies strictly to the right is
// O(s log s).
export function drawnStats(l: Layout) {
  const ys = [...new Set(Object.values(l.boxes).map((b) => Math.round(b.y)))].sort((a, b) => a - b);
  const row = new Map(ys.map((y, i) => [y, i]));
  const count = new Array(ys.length).fill(0);
  for (const b of Object.values(l.boxes)) count[row.get(Math.round(b.y))!]++;
  const bands: [number, number][][] = ys.map(() => []);
  for (const e of l.edges) {
    if (e.from === e.to) continue;
    const A = l.boxes[e.from], B = l.boxes[e.to];
    const [s, t, p] = A.y < B.y ? [A, B, e.points] : [B, A, [...e.points].reverse()];
    const xAt = (y: number) => {
      for (let k = 1; k < p.length; k++) if (y <= p[k].y) return p[k - 1].x + ((y - p[k - 1].y) / (p[k].y - p[k - 1].y || 1)) * (p[k].x - p[k - 1].x);
      return p[p.length - 1].x;
    };
    const rs = row.get(Math.round(s.y))!, rt = row.get(Math.round(t.y))!;
    let x0 = s.x;
    for (let r = rs + 1; r <= rt; r++) {
      const x1 = r === rt ? t.x : xAt(ys[r]);
      bands[r - 1].push([x0, x1]);
      x0 = x1;
    }
  }
  let crossings = 0;
  for (const b of bands) {
    b.sort((p, q) => p[0] - q[0]);
    const ends = [...new Set(b.map((s) => s[1]))].sort((p, q) => p - q);
    const rank = new Map(ends.map((x, i) => [x, i + 1]));
    const tree = new Int32Array(ends.length + 1);
    let seen = 0;
    for (let i = 0; i < b.length;) {
      let j = i;
      while (j < b.length && b[j][0] === b[i][0]) j++;
      for (let k = i; k < j; k++) {
        let atMost = 0;
        for (let q = rank.get(b[k][1])!; q > 0; q -= q & -q) atMost += tree[q];
        crossings += seen - atMost;
      }
      for (let k = i; k < j; k++) {
        for (let q = rank.get(b[k][1])!; q <= ends.length; q += q & -q) tree[q]++;
        seen++;
      }
      i = j;
    }
  }
  return { rows: ys.length, widest: Math.max(...count), crossings };
}

// Two changed plans: one added edge (from a node in a late row to one in an
// early row it cannot reach, so the edge points up in the earlier layers and
// pushes its target and their descendants down), and a batch: every 97th node
// and every 53rd edge removed, ten nodes added, each with an edge in and out.
function changed(base: Layout): [string, Graph][] {
  const layer = base.layers!;
  const out = new Map(plan.nodes.map((n) => [n.id, [] as string[]]));
  for (const [a, b] of plan.edges) out.get(a)!.push(b);
  const ids = plan.nodes.map((n) => n.id);
  const deep = [...ids].sort((p, q) => layer[q] - layer[p] || (p < q ? -1 : 1))[0];
  const reaches = (v: string) => {
    const seen = new Set([v]), stack = [v];
    while (stack.length) for (const w of out.get(stack.pop()!)!) if (!seen.has(w)) { seen.add(w); stack.push(w); }
    return seen.has(deep);
  };
  const up = ids.find((v) => layer[v] < layer[deep] - 2 && !reaches(v))!;
  const edge: [string, string] = [deep, up];
  const kept = new Set(ids.filter((_, i) => i % 97 !== 5));
  return [
    ["one added edge", { nodes: plan.nodes, edges: [...plan.edges, edge] }],
    ["a batch of changes", {
      nodes: [...plan.nodes.filter((_, i) => i % 97 !== 5), ...Array.from({ length: 10 }, (_, k) => ({ id: `NEW${k}`, w: 210, h: 52 }))],
      edges: [...plan.edges.filter(([a, b], i) => i % 53 !== 7 && kept.has(a) && kept.has(b)), ...(kept.has(deep) && kept.has(up) ? [edge] : []), ...Array.from({ length: 10 }, (_, k): [string, string] => [`NEW${k}`, ids[200 + 31 * k]]), ...Array.from({ length: 10 }, (_, k): [string, string] => [ids[10 + 7 * k], `NEW${k}`])],
    }],
  ];
}

describe("layout from an earlier layout", () => {
  test("the plan changed by one edge, and by a batch, is laid out from its earlier layers with every edge pointing down, and the result is logged against a layout from scratch", { timeout: 60_000 }, async () => {
    const base = await layoutInWorker(plan);
    assert.ok(base.layers && Object.keys(base.layers).length === plan.nodes.length);
    const runs = changed(base).flatMap(([what, g]) => [
      (async () => { const t0 = Date.now(); const l = await layoutInWorker(g, base); return { what, g, from: "the earlier layers", l, ms: Date.now() - t0 }; })(),
      (async () => { const t0 = Date.now(); const l = await layoutInWorker(g); return { what, g, from: "scratch", l, ms: Date.now() - t0 }; })(),
    ]);
    const load = readFileSync("/proc/loadavg", "utf8").split(" ")[0];
    for (const { what, g, from, l, ms } of await Promise.all(runs)) {
      for (const n of g.nodes) assert.ok(l.boxes[n.id], `${n.id} has no place`);
      // Neither change adds a cycle, so every edge goes down.
      for (const [a, b] of g.edges) assert.ok(l.boxes[a].y < l.boxes[b].y, `${a} -> ${b} points upward`);
      const s = drawnStats(l);
      console.log(`${what}, from ${from}: ${s.rows} rows, at most ${s.widest} boxes in a row, ${s.crossings} crossings, ${Math.round(l.w)} x ${Math.round(l.h)} px, ${ms} ms at load ${load}`);
    }
  });
});
