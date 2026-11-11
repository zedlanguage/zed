import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { graph, layerSeparation, layeringSimplex } from "d3-dag";
import { layeringBalanced, rebalance } from "./d3dag.ts";
import type { Graph } from "./layout.ts";
import { planLike } from "./synthetic.ts";

const LANE = 26;
const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;

// A d3-dag graph of g, with each edge back to a node on a depth-first path
// dropped, so it has no cycle (d3dag.ts turns those edges round instead).
function dagOf(g: Graph) {
  const dag = graph<{ id: string; w: number; h: number }, undefined>();
  const nodes = new Map(g.nodes.map((n) => [n.id, dag.node({ ...n })]));
  const out = new Map(g.nodes.map((n) => [n.id, [] as string[]]));
  for (const [a, b] of g.edges) if (a !== b && nodes.has(a) && nodes.has(b)) out.get(a)!.push(b);
  const mark = new Map<string, number>();
  const seen = new Set<string>();
  for (const n of g.nodes) {
    if (mark.has(n.id)) continue;
    const stack: [string, number][] = [[n.id, 0]];
    mark.set(n.id, 1);
    while (stack.length) {
      const top = stack[stack.length - 1];
      const [v, i] = top;
      if (i === out.get(v)!.length) { mark.set(v, 2); stack.pop(); continue; }
      top[1]++;
      const w = out.get(v)![i];
      if (mark.get(w) === 1) continue;
      if (!seen.has(`${v} ${w}`)) { seen.add(`${v} ${w}`); dag.link(nodes.get(v)!, nodes.get(w)!); }
      if (!mark.has(w)) { mark.set(w, 1); stack.push([w, 0]); }
    }
  }
  return dag;
}

// Every edge goes down at least one layer and the value returned is the last
// layer; gives the widest layer in px, boxes and lanes counted.
function check(dag: any, last: number): number {
  const W = new Array(last + 1).fill(0);
  let top = Infinity;
  for (const n of dag.nodes()) {
    assert.ok(Number.isInteger(n.y) && n.y >= 0 && n.y <= last, `layer ${n.y} of ${n.data.id}`);
    top = Math.min(top, n.y);
    W[n.y] += n.data.w + LANE;
    for (const c of n.children()) {
      assert.ok(c.y >= n.y + 1, `${n.data.id} (layer ${n.y}) > ${c.data.id} (layer ${c.y})`);
      for (let l = n.y + 1; l < c.y; l++) W[l] += LANE;
    }
  }
  assert.equal(top, 0);
  return Math.max(...W);
}

test("rebalancing the plan keeps every edge going down and makes the widest layer narrower than simplex's", () => {
  const before = dagOf(plan);
  const simplexWidest = check(before, layeringSimplex()(before as any, layerSeparation));
  const after = dagOf(plan);
  const t0 = Date.now();
  const widest = check(after, layeringBalanced(1)(after, layerSeparation));
  console.log(`plan: widest layer ${simplexWidest} px with simplex, ${widest} px rebalanced, ${Date.now() - t0} ms`);
  assert.ok(widest < simplexWidest, `${widest} px is not narrower than ${simplexWidest} px`);
  // 36,626 and 21,030 px when the penalty was chosen (2026-11-10).
  assert.ok(widest <= 21_030, `${widest} px is wider than the 21,030 px measured when the penalty was chosen`);
});

test("rebalancing a plan-shaped graph of 1000 nodes keeps every edge going down and ends", () => {
  const dag = dagOf(planLike(1000, 2700));
  check(dag, layeringBalanced(1)(dag, layerSeparation));
});

test("rebalancing moves a box out of a crowded layer into its slack and leaves a node without slack where it is", () => {
  // Layers 0 to 3. Node 0 is at the top and node 4 at the bottom; 1, 2 and 3 sit
  // in layer 1 with nothing below them but 4, so one or two of them can go down;
  // 5 and 6 are a chain from 0 to 4 with no slack.
  const y = Int32Array.from([0, 1, 1, 1, 3, 1, 2]);
  const box = Int32Array.from([236, 236, 236, 236, 236, 236, 236]);
  const parents = [[], [0], [0], [0], [1, 2, 3, 6], [0], [5]];
  const children = [[1, 2, 3, 5], [4], [4], [4], [], [6], [4]];
  rebalance(y, box, parents, children, LANE, 0);
  for (let i = 0; i < y.length; i++) for (const c of children[i]) assert.ok(y[c] >= y[i] + 1);
  assert.equal(y[0], 0);
  assert.equal(y[4], 3);
  assert.equal(y[5], 1);
  assert.equal(y[6], 2);
  const inLayer1 = [1, 2, 3].filter((i) => y[i] === 1).length;
  assert.ok(inLayer1 < 3, `layer 1 still holds ${inLayer1} of nodes 1 to 3`);
});

test("rebalancing an empty graph changes nothing", () => {
  rebalance(new Int32Array(0), new Int32Array(0), [], [], LANE, 1);
});
