import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { graph, layerSeparation, layeringSimplex } from "d3-dag";
import { balanceCounts, compactLayers, fromPrevious, layers, lowerSources, splitRows } from "./d3dag.ts";
import type { Graph } from "./layout.ts";
import { planLike } from "./synthetic.ts";

const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;

// A d3-dag graph of g, with each edge back to a node on a depth-first path
// dropped, so it has no cycle (d3dag.ts turns those edges round instead), and
// each node's parents and children by index.
export function dagOf(g: Graph) {
  const dag = graph<{ id: string; w: number; h: number }, undefined>();
  const nodes = g.nodes.map((n) => dag.node({ ...n }));
  const at = new Map(g.nodes.map((n, i) => [n.id, i]));
  const out: number[][] = g.nodes.map(() => []);
  for (const [a, b] of g.edges) if (a !== b && at.has(a) && at.has(b)) out[at.get(a)!].push(at.get(b)!);
  const mark = new Uint8Array(nodes.length);
  const seen = new Set<string>();
  for (let r = 0; r < nodes.length; r++) {
    if (mark[r]) continue;
    const stack: [number, number][] = [[r, 0]];
    mark[r] = 1;
    while (stack.length) {
      const top = stack[stack.length - 1];
      const [v, i] = top;
      if (i === out[v].length) { mark[v] = 2; stack.pop(); continue; }
      top[1]++;
      const w = out[v][i];
      if (mark[w] === 1) continue;
      if (!seen.has(`${v} ${w}`)) { seen.add(`${v} ${w}`); dag.link(nodes[v], nodes[w]); }
      if (!mark[w]) { mark[w] = 1; stack.push([w, 0]); }
    }
  }
  const index = new Map(nodes.map((n, i) => [n, i]));
  const parents = nodes.map((n) => [...n.parents()].map((p) => index.get(p)!));
  const children = nodes.map((n) => [...n.children()].map((c) => index.get(c)!));
  return { dag, nodes, parents, children };
}

export function edgesDown(y: Int32Array, children: number[][]): void {
  for (let i = 0; i < y.length; i++) for (const c of children[i]) assert.ok(y[c] >= y[i] + 1, `edge ${i} (layer ${y[i]}) -> ${c} (layer ${y[c]}) does not go down`);
}

export function counts(y: Int32Array): number[] {
  let L = 0;
  for (const v of y) L = Math.max(L, v + 1);
  const c = new Array(L).fill(0);
  for (const v of y) c[v]++;
  return c;
}

const simplexOf = (g: Graph) => {
  const d = dagOf(g);
  layeringSimplex()(d.dag as any, layerSeparation);
  return { ...d, y: Int32Array.from(d.nodes, (n: any) => n.y) };
};

test("lowerSources puts a source one layer above its highest child and leaves a node with no edges where it is", () => {
  // 0 -> 2 and 0 -> 3, with 2 in layer 4 and 3 in layer 5; 1 has no edges; 2 -> 3.
  const y = Int32Array.from([0, 2, 4, 5]);
  lowerSources(y, [[], [], [0], [0, 2]], [[2, 3], [], [3], []]);
  assert.deepEqual([...y], [3, 2, 4, 5]);
});

test("after lowerSources every source of the plan and of a plan-shaped graph sits directly above its highest child", () => {
  for (const g of [plan, planLike(1000, 2700)]) {
    const { y, parents, children } = simplexOf(g);
    lowerSources(y, parents, children);
    for (let i = 0; i < y.length; i++) {
      if (parents[i].length || !children[i].length) continue;
      assert.equal(y[i], Math.min(...children[i].map((c) => y[c])) - 1);
    }
    edgesDown(y, children);
  }
});

test("count balancing ends; each move lowers the sum of squared layer counts by at least 2 and lands in a layer still below the count of the one left; no edge points up", () => {
  for (const [name, g] of [["the plan", plan], ["a plan-shaped graph of 1000 nodes", planLike(1000, 2700)]] as const) {
    const { y, parents, children } = simplexOf(g);
    lowerSources(y, parents, children);
    const before = counts(y);
    const c = new Map<number, number>();
    for (const v of y) c.set(v, (c.get(v) ?? 0) + 1);
    let sq = 0;
    for (const k of c.values()) sq += k * k;
    const sq0 = sq;
    let moves = 0;
    const passes = balanceCounts(y, parents, children, (_i, from, to) => {
      const a = c.get(from)!, b = c.get(to) ?? 0;
      assert.ok(b + 1 < a, `a move from a layer of ${a} to one of ${b}`);
      c.set(from, a - 1);
      c.set(to, b + 1);
      let now = 0;
      for (const k of c.values()) now += k * k;
      assert.ok(now <= sq - 2, `sum of squares ${sq} -> ${now}`);
      sq = now;
      moves++;
    });
    edgesDown(y, children);
    assert.ok(moves <= (sq0 - sq) / 2 && passes <= moves + 1);
    // The layering is a fixed point: one more call makes one pass and no move.
    assert.equal(balanceCounts(y, parents, children, () => assert.fail("moved after convergence")), 1);
    const after = counts(y);
    console.log(`${name}: ${passes} passes, ${moves} moves, sum of squares ${sq0} -> ${sq}, widest layer ${Math.max(...before)} -> ${Math.max(...after)} nodes`);
    assert.ok(Math.max(...after) < Math.max(...before));
  }
});

test("count balancing leaves alone a node whose least crowded layer would, with it, reach the count of its own", () => {
  // Two chains 0 -> 1 -> 2 and 3 -> 4 -> 5 with no slack, and node 6 with no
  // edges in layer 1: counts 2, 3, 2. Moving 6 would make a layer of 3 out of
  // one of 3, so nothing moves.
  const y = Int32Array.from([0, 1, 2, 0, 1, 2, 1]);
  const parents = [[], [0], [1], [], [3], [4], []];
  const children = [[1], [2], [], [4], [5], [], []];
  assert.equal(balanceCounts(y, parents, children, () => assert.fail("moved")), 1);
  assert.deepEqual([...y], [0, 1, 2, 0, 1, 2, 1]);
});

// A spine 0 -> 1 -> ... -> L-1, one node per layer and none with slack;
// fillers, each between spine nodes p and p + 2, so fixed in layer p + 1; and
// one more node with the parents and children given, starting in layer at.
// Returns the layer count balancing moves that node to.
function moverEndsIn(L: number, fill: [number, number][], ps: number[], cs: number[], at: number): number {
  const y = [...Array(L).keys()];
  const parents: number[][] = y.map((l) => (l ? [l - 1] : []));
  const children: number[][] = y.map((l) => (l < L - 1 ? [l + 1] : []));
  for (const [p, k] of fill) for (let j = 0; j < k; j++) {
    const f = y.length;
    y.push(p + 1); parents.push([p]); children.push([p + 2]); children[p].push(f); parents[p + 2].push(f);
  }
  const m = y.length;
  y.push(at); parents.push(ps); children.push(cs);
  for (const p of ps) children[p].push(m);
  for (const c of cs) parents[c].push(m);
  const z = Int32Array.from(y);
  balanceCounts(z, parents, children);
  edgesDown(z, children);
  return z[m];
}

test("of the least crowded layers of its slack, a node with more parents than children takes the topmost (its edges shortest), not the nearest", () => {
  // Parents 0 and 1: slack 2 to 5. Layer 4 holds the node and two fillers;
  // layers 2, 3 and 5 hold 1 each.
  assert.equal(moverEndsIn(6, [[3, 2]], [0, 1], [], 4), 2);
});

test("of the least crowded layers of its slack, a node with more children than parents takes the bottommost", () => {
  // Children 4 and 5: slack 0 to 3. Layer 1 is crowded; 0, 2 and 3 hold 1 each.
  assert.equal(moverEndsIn(6, [[0, 2]], [], [4, 5], 1), 3);
});

test("of the least crowded layers of its slack, a node with as many parents as children takes the nearest, the upper of two equally near", () => {
  // Parent 0, child 5: slack 1 to 4. From the crowded layer 2, layers 1 and 3
  // are equally near and 4 farther.
  assert.equal(moverEndsIn(6, [[1, 2]], [0], [5], 2), 1);
  // From the crowded layer 1, 2 is nearer than 3 and 4.
  assert.equal(moverEndsIn(6, [[0, 2]], [0], [5], 1), 2);
});

test("count balancing an empty graph changes nothing", () => {
  assert.equal(balanceCounts(new Int32Array(0), [], []), 0);
});

test("compactLayers drops empty layers and puts the top at 0", () => {
  const y = Int32Array.from([-1, 1, 1, 4]);
  assert.equal(compactLayers(y), 3);
  assert.deepEqual([...y], [0, 1, 1, 2]);
});

test("a row of three times the median count is split into two rows, every other node by x moving to a new row below it", () => {
  // Rows 0 to 3 of 2, 6, 2 and 2 nodes: median 2, and row 1 has 6 > 3.
  const y = Int32Array.from([0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]);
  const x = [0, 1, 50, 10, 40, 20, 30, 0, 0, 1, 0, 1];
  const s = splitRows(y, x)!;
  // In x order row 1 is 7, 3, 5, 6, 4, 2; 3, 6 and 2 go to the new row 2.
  assert.deepEqual([...s], [0, 0, 2, 2, 1, 1, 2, 1, 3, 3, 4, 4]);
});

test("a row of exactly 1.5 times the median count is not split", () => {
  // Rows of 2, 3, 2 and 2 nodes: median 2, and 3 is not more than 3.
  const y = Int32Array.from([0, 0, 1, 1, 1, 2, 2, 3, 3]);
  assert.equal(splitRows(y, [0, 1, 0, 1, 2, 0, 1, 0, 1]), null);
  // With an even number of rows the median is the mean of the two middle
  // counts: 2, 4, 4 and 7 have median 4, and 7 > 6 is split.
  const z = Int32Array.from([0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3]);
  assert.ok(splitRows(z, z.map((_, i) => i)));
});

test("after balancing and splitting the plan no edge points up", () => {
  const { dag, nodes, parents, children } = dagOf(plan);
  const y = layers(dag, nodes, parents, children);
  const s = splitRows(y, nodes.map((_, i) => i))!;
  assert.ok(s, "the plan has a row to split");
  edgesDown(s, children);
});

// The layers of g by id, from scratch or from prev.
function layersOf(g: Graph, prev?: Record<string, number>) {
  const { dag, nodes, parents, children } = dagOf(g);
  const y = layers(dag, nodes, parents, children, prev);
  edgesDown(y, children);
  const byId: Record<string, number> = {};
  g.nodes.forEach((n, i) => { byId[n.id] = y[i]; });
  return { y, byId };
}

// An edge from a node to one in a higher layer that cannot reach it, so the
// edge adds no cycle and points up in the old layering.
function upwardEdge(g: Graph, byId: Record<string, number>): [string, string] {
  const out = new Map(g.nodes.map((n) => [n.id, [] as string[]]));
  for (const [a, b] of g.edges) out.get(a)?.push(b);
  const ids = g.nodes.map((n) => n.id).sort((p, q) => byId[q] - byId[p] || (p < q ? -1 : 1));
  const deep = ids[0];
  for (const v of [...ids].reverse()) {
    if (byId[v] >= byId[deep] - 2) break;
    const seen = new Set([v]), stack = [v];
    while (stack.length) for (const w of out.get(stack.pop()!) ?? []) if (!seen.has(w)) { seen.add(w); stack.push(w); }
    if (!seen.has(deep)) return [deep, v];
  }
  throw new Error("no upward edge without a cycle");
}

test("from an earlier layering: an unchanged graph keeps its layers; one added edge, one added node, a removed node and a batch of changes give valid layers, the same each time", () => {
  for (const [name, g] of [["the plan", plan], ["a plan-shaped graph of 1000 nodes", planLike(1000, 2700)]] as const) {
    const base = layersOf(g);
    assert.deepEqual(layersOf(g, base.byId).byId, base.byId);
    const ids = g.nodes.map((n) => n.id);
    const up = upwardEdge(g, base.byId);
    const cases: [string, Graph][] = [
      ["one added edge", { nodes: g.nodes, edges: [...g.edges, up] }],
      ["one added node", { nodes: [...g.nodes, { id: "NEW", w: 210, h: 52 }], edges: [...g.edges, [ids[3], "NEW"], ["NEW", ids[500]]] }],
      ["one removed node", { nodes: g.nodes.filter((n) => n.id !== ids[100]), edges: g.edges.filter(([a, b]) => a !== ids[100] && b !== ids[100]) }],
      ["a batch", {
        nodes: [...g.nodes.filter((_, i) => i % 97 !== 5), ...Array.from({ length: 10 }, (_, k) => ({ id: `NEW${k}`, w: 210, h: 52 }))],
        edges: [...g.edges.filter((_, i) => i % 53 !== 7), up, ...Array.from({ length: 10 }, (_, k): [string, string] => [`NEW${k}`, ids[200 + 31 * k]]), ...Array.from({ length: 10 }, (_, k): [string, string] => [ids[10 + 7 * k], `NEW${k}`])],
      }],
    ];
    for (const [what, h] of cases) {
      const t0 = Date.now();
      const inc = layersOf(h, base.byId);
      const ms = Date.now() - t0;
      assert.deepEqual(layersOf(h, base.byId).byId, inc.byId, `${what}: not the same twice`);
      const t1 = Date.now();
      const full = layersOf(h);
      const fullMs = Date.now() - t1;
      const ci = counts(inc.y), cf = counts(full.y);
      // No more layers than the earlier layering had or the longest path needs.
      const d = dagOf(h);
      const longest = counts(fromPrevious(h.nodes.map(() => 0), d.parents, d.children)!).length;
      assert.ok(ci.length <= Math.max(counts(base.y).length, longest), `${what}: ${ci.length} layers`);
      console.log(`${name}, ${what}: from the earlier layers ${ci.length} layers, widest ${Math.max(...ci)} nodes, ${ms} ms; from scratch ${cf.length} layers, widest ${Math.max(...cf)}, ${fullMs} ms`);
    }
  }
});

test("from an earlier layering, an added edge from a deep node to a high one moves the deep node up rather than everything below the high one down", () => {
  // Chains 0 -> 1 -> 2 -> 3 and 5 -> 6 -> 7 -> 8 in layers 0 to 3, and node 4
  // with parent 0 in layer 3. The edge 4 -> 5 is added. The longest path,
  // 0 4 5 6 7 8, has 6 nodes; pushing 5 to 8 below 4 would make 8 layers.
  const old = [0, 1, 2, 3, 3, 0, 1, 2, 3];
  const parents = [[], [0], [1], [2], [0], [4], [5], [6], [7]];
  const children = [[1, 4], [2], [3], [], [5], [6], [7], [8], []];
  const y = fromPrevious(old, parents, children)!;
  edgesDown(y, children);
  assert.deepEqual([...y], [0, 1, 2, 3, 1, 2, 3, 4, 5]);
});

test("fromPrevious gives null when no node has an earlier layer", () => {
  assert.equal(fromPrevious([undefined, undefined], [[], [0]], [[1], []]), null);
});

// The least time of three runs of f on inputs made before timing.
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

// A pass of balanceCounts costs O((n + m) log L) and the passes stay few (3
// to 13 measured), so 8 times the graph should take about 8 log(8n) / log n
// times as long. The limit is twice that, and more when the 1-minute load
// average is above the 32 cores.
function scalingLimit(n: number): number {
  const load = Number(readFileSync("/proc/loadavg", "utf8").split(" ")[0]);
  return 2 * 8 * (Math.log2(8 * n) / Math.log2(n)) * Math.max(1, load / 32);
}

// A spine of n / 2 nodes, one per layer, and n / 2 nodes each with the
// spine's first node as parent and its last as child, all starting in the
// spine's middle layer: every one of them has the whole spine as slack. A
// version that scans each node's slack layer by layer, O(n L) per pass, took
// 87 times as long at 8n here (run once as a control, not kept).
function wideSlack(n: number) {
  const L = n / 2;
  const y = Int32Array.from({ length: n }, (_, i) => (i < L ? i : L / 2));
  const parents: number[][] = [], children: number[][] = [];
  for (let i = 0; i < n; i++) {
    parents.push(i < L ? (i ? [i - 1] : []) : [0]);
    children.push(i < L ? (i < L - 1 ? [i + 1] : []) : [L - 1]);
  }
  for (let i = L; i < n; i++) { children[0].push(i); parents[L - 1].push(i); }
  return { y, parents, children };
}

test("count balancing and layering from an earlier layering scale as n log n: plan-shaped graphs of 4000 and 32000 nodes, and 4000 and 32000 nodes of whole-spine slack", () => {
  const n = 4000;
  const graphs = [n, 8 * n].map((k) => {
    const g = planLike(k, Math.round(2.7 * k));
    const d = dagOf(g);
    // Longest-path layers, as fromPrevious gives them from an earlier layering with every node in layer 0.
    const y0 = fromPrevious(g.nodes.map(() => 0), d.parents, d.children)!;
    const byId: Record<string, number> = {};
    g.nodes.forEach((v, i) => { byId[v.id] = y0[i]; });
    return { d, y0, byId, wide: wideSlack(k) };
  });
  const balance = graphs.map(({ d, y0 }) => best(() => { const y = Int32Array.from(y0); return () => balanceCounts(y, d.parents, d.children); }));
  const again = graphs.map(({ d, byId }) => best(() => () => layers(d.dag, d.nodes, d.parents, d.children, byId)));
  const wide = graphs.map(({ wide: w }) => best(() => { const y = Int32Array.from(w.y); return () => balanceCounts(y, w.parents, w.children); }));
  const limit = scalingLimit(n);
  const show = (t: number[]) => `${t[0].toFixed(1)} and ${t[1].toFixed(1)} ms (ratio ${(t[1] / t[0]).toFixed(1)})`;
  console.log(`balanceCounts ${show(balance)}; layers from earlier layers ${show(again)}; whole-spine slack ${show(wide)}; limit ${limit.toFixed(1)}`);
  for (const [what, t] of [["balanceCounts", balance], ["layers", again], ["whole-spine slack", wide]] as const) assert.ok(t[1] / t[0] < limit, `${what}: ratio ${(t[1] / t[0]).toFixed(1)}`);
});
