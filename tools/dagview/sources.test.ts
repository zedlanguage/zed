// The author's rules: a source (a node with no needs) sits directly above its
// highest child (2026-11-11), unless that row would hold more than the row
// limit, K = Layout.rowLimit; then it may stagger into a less full row higher
// up (2026-11-13). So a source more than one layer above its highest child is
// allowed only where the layer directly above that child holds K nodes or
// more. Checked on the final layout as the page draws it: Layout.layers and the
// drawn rows (box centers), from scratch and from an earlier layout after
// edits; a source allowed above in the layers is not checked in the rows.

import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { d3dagLayout, operators } from "./d3dag.ts";
import type { Graph, Layout } from "./layout.ts";
import { planLike } from "./synthetic.ts";

const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;
// The graph the page posted for the live plan on 2026-11-11 (1,707 nodes),
// built from /api/state as client.ts builds it.
const live = JSON.parse(readFileSync(new URL("./live-graph-2026-11-11.json", import.meta.url), "utf8")) as Graph;

// A spine 0 -> ... -> 11, and in each of layers 1 to 3 `wide` fillers
// (parent spine l - 1, child spine l + 1); then s sources each with one child
// x_j in layer 10 (parent spine 9, child spine 11). Simplex puts the sources
// in layer 9; the rows above 9 except 1 to 3 hold one node each, so
// balancing the sources as other nodes moved them up into those rows.
function deepSources(s: number, wide: number) {
  const edges: [number, number][] = [];
  const y: number[] = [];
  for (let l = 0; l <= 11; l++) { y.push(l); if (l) edges.push([l - 1, l]); }
  for (let l = 1; l <= 3; l++) for (let f = 0; f < wide; f++) { const v = y.length; y.push(l); edges.push([l - 1, v], [v, l + 1]); }
  for (let j = 0; j < s; j++) { const x = y.length; y.push(10); edges.push([9, x], [x, 11]); const v = y.length; y.push(9); edges.push([v, x]); }
  const ids = y.map((_, i) => `n${i}`);
  return { nodes: ids.map((id) => ({ id, w: 210, h: 52 })), edges: edges.map(([a, b]): [string, string] => [ids[a], ids[b]]) } as Graph;
}

// Each source with children of g (no edge in from another node, some out)
// whose highest child is not exactly one row below it in row; [id, gap].
function finalGaps(g: Graph, row: (id: string) => number): [string, number][] {
  const ids = new Set(g.nodes.map((n) => n.id));
  const hasParent = new Set<string>(), kids = new Map<string, string[]>();
  for (const [a, b] of g.edges) {
    if (a === b || !ids.has(a) || !ids.has(b)) continue;
    hasParent.add(b);
    (kids.get(a) ?? kids.set(a, []).get(a)!).push(b);
  }
  const out: [string, number][] = [];
  for (const [a, ks] of kids) {
    if (hasParent.has(a)) continue;
    const gap = Math.min(...ks.map(row)) - row(a);
    if (gap !== 1) out.push([a, gap]);
  }
  return out;
}

// The rows as drawn: boxes in the same row share a center height.
function drawnRow(l: Layout): (id: string) => number {
  const ys = [...new Set(Object.values(l.boxes).map((b) => Math.round(b.y)))].sort((a, b) => a - b);
  const at = new Map(ys.map((v, i) => [v, i]));
  return (id) => at.get(Math.round(l.boxes[id].y))!;
}

// The sources of finalGaps in Layout.layers that the row limit does not
// allow: the layer directly above the highest child holds fewer than K nodes.
function pinGaps(g: Graph, l: Omit<Layout, "key">): [string, number][] {
  const L = l.layers!, count = new Map<number, number>();
  for (const v of Object.values(L)) count.set(v, (count.get(v) ?? 0) + 1);
  return finalGaps(g, (id) => L[id]).filter(([id, gap]) => gap < 1 || (count.get(L[id] + gap - 1) ?? 0) < l.rowLimit!);
}

function finalProperty(name: string, g: Graph, l: Omit<Layout, "key">): void {
  const inLayers = pinGaps(g, l);
  const raised = new Set(finalGaps(g, (id) => l.layers![id]).map(([id]) => id));
  const inRows = finalGaps(g, drawnRow(l as Layout)).filter(([id]) => !raised.has(id));
  assert.deepEqual(inLayers, [], `${name}: sources not directly above their highest child in Layout.layers`);
  assert.deepEqual(inRows, [], `${name}: sources not directly above their highest child in the drawn rows`);
}

test("in the final layout of the plan, of the live plan of 2026-11-11, of a plan-shaped graph and of sources whose child sits deep, every source sits directly above its highest child unless that row is full, in Layout.layers and in the drawn rows", () => {
  for (const [name, g] of [["the plan", plan], ["the live plan", live], ["a plan-shaped graph of 1000 nodes", planLike(1000, 2700)], ["12 sources over deep children", deepSources(12, 6)]] as const) {
    const t0 = Date.now();
    const l = d3dagLayout(g);
    finalProperty(name, g, l);
    const r = drawnRow(l as Layout);
    const per = new Map<number, number>();
    for (const n of g.nodes) per.set(r(n.id), (per.get(r(n.id)) ?? 0) + 1);
    console.log(`${name}: ${per.size} rows, widest ${Math.max(...per.values())}, ${Date.now() - t0} ms`);
  }
});

test("the property check fires: a source two layers above its child is reported, in the layers and in the drawn rows, and one layer above is not; two above is allowed when the row above the child is full", () => {
  // Chain a -> b -> c and source s with child c, laid out by hand.
  const g: Graph = { nodes: ["a", "b", "c", "s"].map((id) => ({ id, w: 210, h: 52 })), edges: [["a", "b"], ["b", "c"], ["s", "c"]] };
  const at = (L: Record<string, number>) => ({ w: 0, h: 0, edges: [], layers: L, boxes: Object.fromEntries(Object.entries(L).map(([id, l]) => [id, { x: 0, y: 100 * l + 26, w: 210, h: 52 }])) }) as unknown as Layout;
  finalProperty("s one layer above c", g, at({ a: 0, b: 1, c: 2, s: 1 }));
  const up = at({ a: 0, b: 1, c: 2, s: 0 });
  assert.deepEqual(finalGaps(g, (id) => up.layers![id]), [["s", 2]]);
  assert.deepEqual(finalGaps(g, drawnRow(up)), [["s", 2]]);
  assert.deepEqual(pinGaps(g, { ...up, rowLimit: 2 }), [["s", 2]]);
  // The layer above c (layer 1) holds b alone: full at K = 1.
  assert.deepEqual(pinGaps(g, { ...up, rowLimit: 1 }), []);
});

test("from an earlier layout of the live plan: unchanged it keeps its layers; after an added source with a deep child, an added edge from a source to a deep node, a removed child and a batch of changes, every source sits directly above its highest child unless that row is full, in Layout.layers and in the drawn rows", () => {
  const base = d3dagLayout(live);
  finalProperty("the live plan", live, base);
  const at = Object.fromEntries(Object.entries(base.boxes).map(([id, b]) => [id, { x: b.x, y: b.y }]));
  const again = (h: Graph) => d3dagLayout(h, operators, base.layers, at, base.edges, base.rowLimit);
  assert.deepEqual(again(live).layers, base.layers);
  const L = base.layers!;
  const ids = live.nodes.map((n) => n.id);
  const deep = [...ids].sort((p, q) => L[q] - L[p] || (p < q ? -1 : 1));
  const hasParent = new Set(live.edges.map(([, b]) => b));
  const sources = ids.filter((id) => !hasParent.has(id) && live.edges.some(([a]) => a === id)).sort((p, q) => L[p] - L[q] || (p < q ? -1 : 1));
  const s0 = sources[0];
  const kidOf = live.edges.find(([a]) => a === s0)![1];
  const cases: [string, Graph][] = [
    ["an added source with a deep child", { nodes: [...live.nodes, { id: "NEWSRC", w: 210, h: 52 }], edges: [...live.edges, ["NEWSRC", deep[5]]] }],
    ["an added edge from the highest source to a deep node", { nodes: live.nodes, edges: [...live.edges, [s0, deep[0]]] }],
    ["the highest source's child removed", { nodes: live.nodes.filter((n) => n.id !== kidOf), edges: live.edges.filter(([a, b]) => a !== kidOf && b !== kidOf) }],
    ["a batch", {
      nodes: [...live.nodes.filter((_, i) => i % 97 !== 5), ...Array.from({ length: 10 }, (_, k) => ({ id: `NEW${k}`, w: 210, h: 52 }))],
      edges: [...live.edges.filter((_, i) => i % 53 !== 7), ...Array.from({ length: 10 }, (_, k): [string, string] => [`NEW${k}`, deep[3 * k]])],
    }],
  ];
  for (const [what, h] of cases) finalProperty(what, h, again(h));
});
