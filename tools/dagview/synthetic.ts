// A synthetic graph shaped like the plan, for the layout timing tests: n nodes
// in rows of ten, each edge from a node to one in an earlier row, three in four
// from the one or two rows just before (a step needs the step before it) and
// one in four from up to thirty rows back (now and then a far earlier one).
// The live plan of 2026-11-07 has 1,000 nodes in 97 rows. The same arguments
// give the same graph.

import type { Graph } from "./layout.ts";

export function planLike(n: number, edges: number): Graph {
  // mulberry32, in 32-bit integer steps.
  let seed = 12345;
  const rand = (k: number) => {
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return Math.floor((((t ^ (t >>> 14)) >>> 0) / 4294967296) * k);
  };
  const row = 10;
  const nodes = Array.from({ length: n }, (_, i) => ({ id: `N${i}`, w: i % 50 === 0 ? 330 : 210, h: i % 50 === 0 ? 168 : 52 }));
  const seen = new Set<string>();
  const out: [string, string][] = [];
  while (out.length < edges) {
    const to = row + rand(n - row);
    const back = 1 + (rand(4) < 3 ? rand(2) : rand(30));
    const fromRow = Math.floor(to / row) - back;
    if (fromRow < 0) continue;
    const from = fromRow * row + rand(row);
    const key = `${from} ${to}`;
    if (seen.has(key)) continue;
    seen.add(key);
    out.push([`N${from}`, `N${to}`]);
  }
  return { nodes, edges: out };
}
