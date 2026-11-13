// Relayouts of a changing graph, for the shape tests (aspect*.test.ts): the
// graph is laid out from scratch, then changed and laid out again from the
// earlier layout `gens` times, as the page does when the plan changes. Each
// generation removes three nodes and three edges and adds three nodes (each
// on a new edge from a node to another lower down, through it) and three
// edges, each from a node to one in a lower layer, so no edge points up in
// the earlier layers. The same arguments give the same generations.

import assert from "node:assert/strict";
import { BAND, d3dagLayout, operators } from "./d3dag.ts";
import type { Graph, Layout } from "./layout.ts";

type Drawn = Omit<Layout, "key">;

// The number of nodes on the longest path of g, its edges taken as given (the
// test graphs have no cycle).
export function pathNodes(g: Graph): number {
  const at = new Map(g.nodes.map((n, i) => [n.id, i]));
  const kids: number[][] = g.nodes.map(() => []), waiting = new Int32Array(g.nodes.length);
  for (const [a, b] of g.edges) { const s = at.get(a), t = at.get(b); if (s === undefined || t === undefined || s === t) continue; kids[s].push(t); waiting[t]++; }
  const depth = new Int32Array(g.nodes.length).fill(1), order: number[] = [];
  g.nodes.forEach((_, i) => { if (!waiting[i]) order.push(i); });
  let most = 0;
  for (let k = 0; k < order.length; k++) {
    const v = order[k];
    most = Math.max(most, depth[v]);
    for (const c of kids[v]) { depth[c] = Math.max(depth[c], depth[v] + 1); if (--waiting[c] === 0) order.push(c); }
  }
  return most;
}

// The parents and children of each node by index, edges taken as given.
export function adjacency(g: Graph) {
  const at = new Map(g.nodes.map((n, i) => [n.id, i]));
  const parents: number[][] = g.nodes.map(() => []), children: number[][] = g.nodes.map(() => []);
  for (const [a, b] of g.edges) { const s = at.get(a), t = at.get(b); if (s === undefined || t === undefined || s === t) continue; children[s].push(t); parents[t].push(s); }
  return { parents, children };
}

// The number of layers of a layout.
export const rowsOf = (l: Drawn) => new Set(Object.values(l.layers!)).size;

// Edge spans in layers: median, 90th percentile and max.
export function spans(g: Graph, l: Drawn) {
  const L = l.layers!;
  const s = g.edges.filter(([a, b]) => a !== b && a in L && b in L).map(([a, b]) => Math.abs(L[b] - L[a])).sort((p, q) => p - q);
  const at = (f: number) => s[Math.min(s.length - 1, Math.floor(f * s.length))];
  return { median: at(0.5), p90: at(0.9), max: s[s.length - 1] };
}

export function inBand(l: Drawn, what: string) {
  const r = l.w / l.h;
  assert.ok(r >= BAND[0] && r <= BAND[1], `${what}: w/h ${r.toFixed(3)} (${Math.round(l.w)} x ${Math.round(l.h)}) outside [${BAND[0]}, ${BAND[1]}]`);
}

// Runs the generations, checking each final layout: w/h within BAND every
// generation, and after the last the row count at most 1.25 times the larger
// of the longest path and the rows of a layout of the same graph from
// scratch (the count the shape needs).
export function relayouts(g: Graph, gens: number, what: string): string {
  let seed = 7;
  const rand = (k: number) => { seed = (Math.imul(seed, 1103515245) + 12345) >>> 0; return seed % k; };
  let l = d3dagLayout(g);
  inBand(l, `${what}, from scratch`);
  const first = `${rowsOf(l)} rows, w/h ${(l.w / l.h).toFixed(3)}`;
  for (let gen = 1; gen <= gens; gen++) {
    const L = l.layers!;
    const gone = new Set<string>();
    for (let k = 0; k < 3; k++) gone.add(g.nodes[rand(g.nodes.length)].id);
    const edges = [...g.edges];
    for (let k = 0; k < 3; k++) edges.splice(rand(edges.length), 1);
    const nodes = g.nodes.filter((n) => !gone.has(n.id));
    const kept = edges.filter(([a, b]) => !gone.has(a) && !gone.has(b));
    for (let k = 0; k < 3; k++) {
      const id = `G${gen}_${k}`, p = nodes[rand(nodes.length)].id, c = nodes[rand(nodes.length)].id;
      nodes.push({ id, w: 210, h: 52 });
      if (L[p] < L[c]) kept.push([p, id], [id, c]); else kept.push([c, id], [id, p]);
    }
    for (let k = 0; k < 3; k++) {
      const a = nodes[rand(nodes.length)].id, b = nodes[rand(nodes.length)].id;
      if (L[a] !== undefined && L[b] !== undefined && L[a] !== L[b]) kept.push(L[a] < L[b] ? [a, b] : [b, a]);
    }
    g = { nodes, edges: kept };
    const at = Object.fromEntries(Object.entries(l.boxes).map(([id, b]) => [id, { x: b.x, y: b.y }]));
    l = d3dagLayout(g, operators, l.layers, at, l.edges, l.rowLimit);
    inBand(l, `${what}, generation ${gen}`);
  }
  const fresh = d3dagLayout(g);
  inBand(fresh, `${what}, generation ${gens} from scratch`);
  const lp = pathNodes(g), R = rowsOf(l), need = Math.max(lp, rowsOf(fresh));
  assert.ok(R <= 1.25 * need, `${what}: ${R} rows after ${gens} relayouts, over 1.25 x ${need} (longest path ${lp}, ${rowsOf(fresh)} rows from scratch)`);
  const s = spans(g, l);
  return `${what}: ${first} from scratch; after ${gens} relayouts ${R} rows (longest path ${lp}, ${rowsOf(fresh)} from scratch), w/h ${(l.w / l.h).toFixed(3)}, K ${l.rowLimit}, edge spans median ${s.median}, 90th percentile ${s.p90}, max ${s.max}`;
}
