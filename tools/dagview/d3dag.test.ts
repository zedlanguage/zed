import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { graph, layerSeparation, layeringSimplex } from "d3-dag";
import { balanceCounts, balanceLayers, compactLayers, fromPrevious, layers, lowerSources, rowLimit, splitRows, spreadSources } from "./d3dag.ts";
import type { Work } from "./d3dag.ts";
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

// The layers of the nodes that are not sources (sources, nodes with no parents
// and some children, are placed by lowerSources and not counted by balanceCounts).
const notSources = (y: Int32Array, parents: number[][], children: number[][]) => y.filter((_, i) => parents[i].length || !children[i].length);

test("count balancing ends; each move lowers the sum of squared layer counts of the nodes other than sources by at least 2 and lands in a layer still below the count of the one left; with the sources placed after it no edge points up", () => {
  for (const [name, g] of [["the plan", plan], ["a plan-shaped graph of 1000 nodes", planLike(1000, 2700)]] as const) {
    const { y, parents, children } = simplexOf(g);
    const before = counts(notSources(y, parents, children));
    const c = new Map<number, number>();
    for (const v of notSources(y, parents, children)) c.set(v, (c.get(v) ?? 0) + 1);
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
    assert.ok(moves <= (sq0 - sq) / 2 && passes <= moves + 1);
    // The layering is a fixed point: one more call makes one pass and no move.
    assert.equal(balanceCounts(y, parents, children, () => assert.fail("moved after convergence")), 1);
    const after = counts(notSources(y, parents, children));
    lowerSources(y, parents, children);
    edgesDown(y, children);
    console.log(`${name}: ${passes} passes, ${moves} moves, sum of squares ${sq0} -> ${sq}, widest layer ${Math.max(...before)} -> ${Math.max(...after)} nodes`);
    assert.ok(Math.max(...after) < Math.max(...before));
  }
});

test("count balancing leaves alone a node whose least crowded layer would, with it, reach the count of its own", () => {
  // Source 7 in layer -1 with children 0, 3 and 6; two chains 0 -> 1 -> 2 and
  // 3 -> 4 -> 5 with no slack, and node 6, with no children, in layer 1:
  // counts 2, 3, 2 without the source. Moving 6 (to layer 0 or 2; not to -1,
  // as its source must stay above it) would make a layer of 3 out of one of
  // 3, so nothing moves.
  const y = Int32Array.from([0, 1, 2, 0, 1, 2, 1, -1]);
  const parents = [[7], [0], [1], [7], [3], [4], [7], []];
  const children = [[1], [2], [], [4], [5], [], [], [0, 3, 6]];
  assert.equal(balanceCounts(y, parents, children, () => assert.fail("moved")), 1);
  assert.deepEqual([...y], [0, 1, 2, 0, 1, 2, 1, -1]);
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
  // Parent 0, children 4 and 5: slack 1 to 3. Layer 1 is crowded; 2 and 3
  // hold 1 each. (A node with no parents is a source and does not move.)
  assert.equal(moverEndsIn(6, [[0, 2]], [0], [4, 5], 1), 3);
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

test("after layers on the plan no edge points up, every source sits directly above its highest child, and the layers are a fixed point: balanceLayers and spreadSources at K each make one pass and no move", () => {
  const { dag, nodes, parents, children } = dagOf(plan);
  const { y, K } = layers(dag, nodes, parents, children);
  edgesDown(y, children);
  assert.deepEqual(sourceGaps(y, parents, children), []);
  const z = Int32Array.from(y);
  assert.equal(balanceLayers(z, parents, children, K, () => assert.fail("balanceLayers moved")), 1);
  assert.equal(spreadSources(z, parents, children, K, () => assert.fail("spreadSources moved")), 1);
  // Sources pinned above their highest child can leave rows over the split
  // limit (27 boxes or more are forced in the row of SCALE-cover's 27
  // sources); splitRows splits those for drawing.
  const c = counts(y);
  console.log(`plan: K = ${K}, ${c.length} layers, widest ${Math.max(...c)}, rows over the split limit ${c.filter((v) => v > rowLimit(y)).length}`);
});

test("splitting keeps every edge pointing down", () => {
  const { dag, nodes, parents, children } = dagOf(plan);
  layeringSimplex()(dag as any, layerSeparation);
  const y = Int32Array.from(nodes, (n: any) => n.y);
  const s = splitRows(y, nodes.map((_, i) => i))!;
  assert.ok(s, "the simplex layers of the plan have a row to split");
  edgesDown(s, children);
});

// The layers of g by id and their row limit, from scratch or from prev and its row limit.
function layersOf(g: Graph, prev?: Record<string, number>, prevK?: number) {
  const { dag, nodes, parents, children } = dagOf(g);
  const { y, K } = layers(dag, nodes, parents, children, prev, prevK);
  edgesDown(y, children);
  const byId: Record<string, number> = {};
  g.nodes.forEach((n, i) => { byId[n.id] = y[i]; });
  return { y, byId, K };
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
    assert.deepEqual(layersOf(g, base.byId, base.K).byId, base.byId);
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
      const inc = layersOf(h, base.byId, base.K);
      const ms = Date.now() - t0;
      assert.deepEqual(layersOf(h, base.byId, base.K).byId, inc.byId, `${what}: not the same twice`);
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

// The steps (Work in d3dag.ts) and the time of one run of run on inputs made
// before it, after a run of warm on its own inputs, so that the time is not
// that of the first, unoptimized run. The scaling tests below compare the steps: a ratio of times at
// 8n and n, even the least of five runs, measured cache and CPU contention
// under parallel load (batch 133, 2026-11-11: balanceCounts 27.5 to 31.4 and
// layers 31.9 against a limit of 25.5 to 31 at load 31 to 42, where a plain
// O(n + m) pass reached 13 to 28); the steps do not depend on the load. The
// time is only logged.
function measured(warm: () => void, run: (work: Work) => void): { steps: number; ms: number } {
  warm();
  const work = { steps: 0 };
  const t0 = performance.now();
  run(work);
  return { steps: work.steps, ms: performance.now() - t0 };
}

// A pass of balanceCounts costs O((n + m) log L) and the passes stay few (3
// to 13 measured), so 8 times the graph should take about 8 log(8n) / log n
// times the steps. The limit is twice that.
function scalingLimit(n: number): number {
  return 2 * 8 * (Math.log2(8 * n) / Math.log2(n));
}

// The ratio of steps at 8n to n, and the log line of a pair of measurements.
const ratio = (r: { steps: number }[]) => r[1].steps / r[0].steps;
const show = (r: { steps: number; ms: number }[]) => `${r[0].steps} and ${r[1].steps} steps (ratio ${ratio(r).toFixed(2)}), ${r[0].ms.toFixed(1)} and ${r[1].ms.toFixed(1)} ms (ratio ${(r[1].ms / r[0].ms).toFixed(1)})`;

// A spine of n / 2 nodes, one per layer, and n / 2 nodes each with the
// spine's first node as parent and its last as child, all starting in the
// spine's middle layer: every one of them has the whole spine as slack. A
// version that scans each node's slack layer by layer, O(n L) per pass, took
// 87 times as long at 8n here (run once as a control, not kept); see the
// scaling test below for its steps.
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
  const balance = graphs.map(({ d, y0 }) => { const y = Int32Array.from(y0); return measured(() => balanceCounts(Int32Array.from(y0), d.parents, d.children), (w) => balanceCounts(y, d.parents, d.children, undefined, w)); });
  const again = graphs.map(({ d, byId }) => measured(() => layers(d.dag, d.nodes, d.parents, d.children, byId), (w) => layers(d.dag, d.nodes, d.parents, d.children, byId, undefined, w)));
  const wide = graphs.map(({ wide: g }) => { const y = Int32Array.from(g.y); return measured(() => balanceCounts(Int32Array.from(g.y), g.parents, g.children), (w) => balanceCounts(y, g.parents, g.children, undefined, w)); });
  const limit = scalingLimit(n);
  console.log(`balanceCounts ${show(balance)}; layers from earlier layers ${show(again)}; whole-spine slack ${show(wide)}; step limit ${limit.toFixed(1)}`);
  for (const [what, r] of [["balanceCounts", balance], ["layers", again], ["whole-spine slack", wide]] as const) assert.ok(ratio(r) < limit, `${what}: ${show(r)}`);
});

// A spine of k / 4 nodes, one per layer, and k sources q_j in layer 1, each
// with one child x_j in layer 2; x_j has parent spine 0 and child the last
// spine node, so it can move anywhere between. Rows 1 and 2 hold k + 1 nodes.
function crowdedSources(k: number) {
  const D = k / 4, n = D + 2 * k;
  const y = new Int32Array(n);
  const edges: [number, number][] = [];
  for (let l = 0; l < D; l++) { y[l] = l; if (l) edges.push([l - 1, l]); }
  for (let j = 0; j < k; j++) { const x = D + 2 * j; y[x] = 2; y[x + 1] = 1; edges.push([0, x], [x, D - 1], [x + 1, x]); }
  return { y, ...adjacency(n, edges) };
}

test("spreadSources on k sources crowded into one row spreads them to rows of at most K, each still directly above its child, and scales as n log n: k = 4000 and 32000", () => {
  const K = 16;
  const r = [4000, 32000].map((k) => {
    const g = crowdedSources(k);
    const h = crowdedSources(k);
    const m = measured(() => spreadSources(h.y, h.parents, h.children, K), (w) => spreadSources(g.y, g.parents, g.children, K, undefined, undefined, w));
    edgesDown(g.y, g.children);
    assert.deepEqual(sourceGaps(g.y, g.parents, g.children), []);
    assert.ok(Math.max(...counts(g.y)) <= K);
    return m;
  });
  const limit = scalingLimit(4000);
  console.log(`spreadSources on crowded sources: ${show(r)}; step limit ${limit.toFixed(1)}`);
  assert.ok(ratio(r) < limit, show(r));
});

// The sources (no parents, some children) whose highest child is not exactly
// one layer below them: [index, gap].
function sourceGaps(y: Int32Array, parents: number[][], children: number[][]): [number, number][] {
  const out: [number, number][] = [];
  for (let i = 0; i < y.length; i++) {
    if (parents[i].length || !children[i].length) continue;
    const gap = Math.min(...children[i].map((k) => y[k])) - y[i];
    if (gap !== 1) out.push([i, gap]);
  }
  return out;
}

// parents and children of a graph given as edges between n numbered nodes.
function adjacency(n: number, edges: [number, number][]) {
  const parents: number[][] = Array.from({ length: n }, () => []), children: number[][] = Array.from({ length: n }, () => []);
  for (const [a, b] of edges) { children[a].push(b); parents[b].push(a); }
  return { parents, children };
}

// The staircase: a spine with node l in layer l (l = 0 to k + 2); mover j
// (j = 1 to k) in layer j + 1, with parent spine j - 1 and child spine j + 2,
// so its slack is layers j and j + 1; and l - 1 fillers in layer l (l = 2 to
// k + 1), with parent spine l - 1 and child spine l + 1, which cannot move.
// Layer l holds l + 1 nodes, layer 1 one. Mover j can move up only once mover
// j - 1 has left layer j, and as the pass takes the most crowded layers first,
// mover j comes before mover j - 1: one move per pass.
function staircase(k: number) {
  const edges: [number, number][] = [];
  const y: number[] = [];
  for (let l = 0; l <= k + 2; l++) { y.push(l); if (l) edges.push([l - 1, l]); }
  for (let j = 1; j <= k; j++) { const v = y.length; y.push(j + 1); edges.push([j - 1, v], [v, j + 2]); }
  for (let l = 2; l <= k + 1; l++) for (let f = 0; f < l - 1; f++) { const v = y.length; y.push(l); edges.push([l - 1, v], [v, l + 1]); }
  return { y: Int32Array.from(y), ...adjacency(y.length, edges) };
}

const sumSq = (y: Int32Array) => counts(y).reduce((s, c) => s + c * c, 0);

test("DAG-balance-bound: balanceCounts on the staircase makes one move per pass, k moves in k + 1 passes, each lowering the sum of squared counts by exactly 2, which meets the bound passes <= moves + 1 <= (sum of squares at the start) / 2 + 1", () => {
  for (const k of [10, 40, 160]) {
    const { y, parents, children } = staircase(k);
    const s0 = sumSq(y);
    let moves = 0;
    const passes = balanceCounts(y, parents, children, () => { moves++; });
    edgesDown(y, children);
    const n = y.length;
    console.log(`staircase k = ${k}: ${n} nodes, ${passes} passes, ${moves} moves, sum of squares ${s0} -> ${sumSq(y)}`);
    assert.equal(moves, k);
    assert.equal(passes, k + 1);
    assert.equal(s0 - sumSq(y), 2 * k);
    assert.ok(passes <= moves + 1 && moves <= s0 / 2);
  }
});

// The chain for balanceLayers at row limit K: spine node l in layer l (l = 0
// to k + 3); mover j (j = 1 to k) in layer j + 2, with parents spine j - 1 and
// spine j and child spine j + 3, so its slack is layers j + 1 and j + 2 and
// its edges pull it up; and K - 2 fixed fillers in each of layers 2 to k + 2.
// Layer 2 holds K - 1 nodes and layers 3 to k + 2 hold K, so only mover 1 has
// room above it, and each move makes room for the next mover. Mover k has the
// lowest index, so in each pass the movers are taken from k down to 1.
function chain(k: number, K: number) {
  const edges: [number, number][] = [];
  const y: number[] = [];
  for (let l = 0; l <= k + 3; l++) { y.push(l); if (l) edges.push([l - 1, l]); }
  const first = y.length;
  for (let j = k; j >= 1; j--) { const v = y.length; y.push(j + 2); edges.push([j - 1, v], [j, v], [v, j + 3]); }
  for (let l = 2; l <= k + 2; l++) for (let f = 0; f < K - 2; f++) { const v = y.length; y.push(l); edges.push([l - 1, v], [v, l + 1]); }
  return { y: Int32Array.from(y), first, ...adjacency(y.length, edges) };
}

test("DAG-balance-bound: balanceLayers on the chain makes one move per pass, k moves in k + 1 passes, so the passes grow linearly with the graph, within the bound moves <= Q0 + (Q0 + 1) F_max", () => {
  const K = 5;
  for (const k of [10, 40, 160]) {
    const { y, parents, children } = chain(k, K);
    const n = y.length, m = children.reduce((s, c) => s + c.length, 0), L = counts(y).length;
    let moves = 0;
    const passes = balanceLayers(y, parents, children, K, () => { moves++; });
    edgesDown(y, children);
    const Q0 = 0, Fmax = (2 * K + 1) * m * (L - 1) + n * n;
    console.log(`chain k = ${k}, K = ${K}: ${n} nodes, ${passes} passes, ${moves} moves; bound ${Q0 + (Q0 + 1) * Fmax} moves`);
    assert.equal(moves, k);
    assert.equal(passes, k + 1);
    assert.ok(Math.max(...counts(y)) <= K);
  }
});

test("DAG-balance-bound: a row over K at the start (Q0 > 0) is emptied to K and the moves stay within Q0 + (Q0 + 1) F_max", () => {
  // Spine 0 -> 1 -> 2 -> 3 -> 4; 12 nodes with parent spine 0 and child spine
  // 4 all in layer 2, so layer 2 holds 13 at K = 6.
  const K = 6, edges: [number, number][] = [[0, 1], [1, 2], [2, 3], [3, 4]];
  const y = [0, 1, 2, 3, 4];
  for (let v = 5; v < 17; v++) { y.push(2); edges.push([0, v], [v, 4]); }
  const { parents, children } = adjacency(y.length, edges);
  const Y = Int32Array.from(y);
  const over = counts(Y).reduce((s, c) => s + Math.max(0, c - K) ** 2, 0);
  let moves = 0;
  balanceLayers(Y, parents, children, K, () => { moves++; });
  edgesDown(Y, children);
  const n = Y.length, m = edges.length, L = 5, Fmax = (2 * K + 1) * m * (L - 1) + n * n;
  assert.equal(over, 49);
  assert.ok(Math.max(...counts(Y)) <= K, `counts ${counts(Y)}`);
  assert.ok(moves <= over + (over + 1) * Fmax);
});

// Spine 0 -> 1 -> ... -> 6; three sources p (each with children spine 1 and
// x) in layer 0; x with child spine 6 in layer 5; and `full` fixed fillers
// in layer 1 (parent spine 0, child spine 2). x has three edges up and one
// down, as S.3-cost-presburger has more parents than children.
function pulledUp(full: number) {
  const edges: [number, number][] = [];
  const y: number[] = [];
  for (let l = 0; l <= 6; l++) { y.push(l); if (l) edges.push([l - 1, l]); }
  const x = 7;
  y.push(5);
  for (let p = 0; p < 3; p++) { const v = y.length; y.push(0); edges.push([v, 1], [v, x]); }
  edges.push([x, 6]);
  for (let f = 0; f < full; f++) { const v = y.length; y.push(1); edges.push([0, v], [v, 2]); }
  return { y: Int32Array.from(y), x, edges };
}

// The same graph upside down: every edge reversed and layer l made 6 - l.
const mirrored = (g: { y: Int32Array; edges: [number, number][] }) => ({ y: g.y.map((l) => 6 - l), edges: g.edges.map(([a, b]): [number, number] => [b, a]) });

test("the spring rule: a node with more parents than children moves up to the row below its lowest parent; the mirror graph moves it down to the row above its highest child; a full row is not entered", () => {
  const K = 4;
  for (const [what, full, want] of [["room in row 1", 0, 1], ["row 1 full", K, 2]] as const) {
    const g = pulledUp(full);
    const { parents, children } = adjacency(g.y.length, g.edges);
    const y = Int32Array.from(g.y);
    const before = counts(y);
    balanceLayers(y, parents, children, K, (_i, _a, b) => { assert.ok(counts(y)[b] <= K, `${what}: a move filled layer ${b} past ${K}`); });
    edgesDown(y, children);
    assert.equal(y[g.x], want, `${what}: up`);
    const h = mirrored(g);
    const r = adjacency(h.y.length, h.edges);
    const z = Int32Array.from(h.y);
    balanceLayers(z, r.parents, r.children, K);
    edgesDown(z, r.children);
    assert.equal(z[g.x], 6 - want, `${what}: down`);
    for (const [l, c] of counts(y).entries()) assert.ok(c <= Math.max(K, before[l]), `${what}: layer ${l} holds ${c}`);
  }
});

test("balanceLayers and balanceCounts never move a source; lowerSources puts it in the row above its child whether the rows between have room or are full", () => {
  // Spine 0 -> 1 -> 2 -> 3; source s = 4 in layer 0 with child spine 3; `fill`
  // fixed fillers in each of layers 1 and 2.
  const K = 3;
  for (const fill of [0, K - 1]) {
    const edges: [number, number][] = [[0, 1], [1, 2], [2, 3], [4, 3]];
    const y = [0, 1, 2, 3, 0];
    for (const l of [1, 2]) for (let f = 0; f < fill; f++) { const v = y.length; y.push(l); edges.push([l - 1, v], [v, l + 1]); }
    const { parents, children } = adjacency(y.length, edges);
    const Y = Int32Array.from(y);
    balanceLayers(Y, parents, children, K, (i) => assert.notEqual(i, 4, "balanceLayers moved the source"));
    balanceCounts(Y, parents, children, (i) => assert.notEqual(i, 4, "balanceCounts moved the source"));
    assert.equal(Y[4], 0);
    lowerSources(Y, parents, children);
    edgesDown(Y, children);
    assert.equal(Y[4], Y[3] - 1, `with ${fill} fillers per row`);
  }
});

test("on the plan balanceCounts leaves sources above their highest child (it moves the children, not the sources); lowerSources then puts every one directly above, and balanceLayers keeps them there; no move of balanceLayers fills a row past K except the move out of a fuller row", () => {
  const { dag, nodes, parents, children } = dagOf(plan);
  layeringSimplex()(dag as any, layerSeparation);
  const y = Int32Array.from(nodes, (n: any) => n.y);
  balanceCounts(y, parents, children);
  const before = sourceGaps(y, parents, children).length;
  lowerSources(y, parents, children);
  assert.deepEqual(sourceGaps(y, parents, children), []);
  const K = rowLimit(y);
  let top = Infinity;
  for (const v of y) top = Math.min(top, v);
  const c = counts(y.map((v) => v - top));
  let fallbacks = 0;
  balanceLayers(y, parents, children, K, (_i, a, b) => {
    a -= top; b -= top;
    if (c[b] + 1 > K) { assert.ok(c[b] + 1 < c[a], `a move to layer ${b} of ${c[b]} from one of ${c[a]}`); fallbacks++; }
    c[a]--; c[b]++;
  });
  assert.deepEqual(sourceGaps(y, parents, children), []);
  console.log(`plan: K = ${K}; sources above their highest child by more than one layer after balanceCounts ${before}; ${fallbacks} moves out of rows over K into rows at K or more`);
  assert.ok(before > 0, "control: balanceCounts leaves sources where they were while their children move");
});
