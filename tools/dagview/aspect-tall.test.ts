// DAGVIEW-aspect: the relayout from a layout as tall as the page drew on
// 2026-11-13 comes back within the shape band (BAND in d3dag.ts).
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { d3dagLayout, fromPrevious, layersAt, operators } from "./d3dag.ts";
import { adjacency, inBand, pathNodes, rowsOf, spans } from "./generations.ts";
import type { Graph } from "./layout.ts";

const live = JSON.parse(readFileSync(new URL("./live-graph-2026-11-11.json", import.meta.url), "utf8")) as Graph;

test("from earlier layers of the live plan at row limit 4, as the page had drawn it on 2026-11-13 (rows far over the longest path), the relayout comes back within [0.4, 0.6] and to at most 1.25 x its longest path in rows", () => {
  // Longest-path layers at K = 4: no row over 4 nodes, the rows makeRoom
  // inserts kept, as the page's layers were after K had fallen to 4.
  const { parents, children } = adjacency(live);
  const y = layersAt(fromPrevious(live.nodes.map(() => 0), parents, children)!, parents, children, 4);
  const tall = Object.fromEntries(live.nodes.map((n, i) => [n.id, y[i]]));
  const lp = pathNodes(live), before = new Set(y).size;
  assert.ok(before > 3 * lp, `the earlier layers have ${before} rows, longest path ${lp}`);
  const l = d3dagLayout(live, operators, tall, undefined, undefined, 4);
  const s = spans(live, l);
  console.log(`live plan from earlier layers at K = 4 (${before} rows): ${rowsOf(l)} rows (longest path ${lp}), ${Math.round(l.w)} x ${Math.round(l.h)}, w/h ${(l.w / l.h).toFixed(3)}, K ${l.rowLimit}, edge spans median ${s.median}, 90th percentile ${s.p90}, max ${s.max}`);
  inBand(l, "live plan from K = 4");
  assert.ok(rowsOf(l) <= 1.25 * lp, `${rowsOf(l)} rows, longest path ${lp}`);
});
