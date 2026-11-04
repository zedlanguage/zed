import assert from "node:assert/strict";
import { test } from "node:test";
import { graphKey, Layouts, layoutInWorker } from "./layout.ts";
import type { Graph, Layout } from "./layout.ts";

const graph: Graph = {
  nodes: [
    { id: "A", w: 210, h: 52 },
    { id: "B", w: 330, h: 147 },
    { id: "C", w: 210, h: 52 },
    { id: "D", w: 210, h: 52 },
  ],
  // C and D form a cycle; the edge to X names no node.
  edges: [["A", "B"], ["B", "C"], ["C", "D"], ["D", "C"], ["A", "X"]],
};

test("the worker lays out every node at its size, top to bottom, and draws each known edge", async () => {
  const l = await layoutInWorker(graph);
  assert.equal(l.key, graphKey(graph));
  assert.deepEqual(Object.keys(l.boxes).sort(), ["A", "B", "C", "D"]);
  assert.equal(l.boxes.B.w, 330);
  assert.equal(l.boxes.B.h, 147);
  assert.ok(l.boxes.A.y < l.boxes.B.y && l.boxes.B.y < l.boxes.C.y);
  for (const b of Object.values(l.boxes)) {
    assert.ok(b.x - b.w / 2 >= 0 && b.x + b.w / 2 <= l.w && b.y - b.h / 2 >= 0 && b.y + b.h / 2 <= l.h);
  }
  assert.deepEqual(l.edges.map((e) => `${e.from}>${e.to}`).sort(), ["A>B", "B>C", "C>D", "D>C"]);
  for (const e of l.edges) assert.ok(e.points.length >= 2);
});

test("the same graph gives the same layout", async () => {
  assert.deepEqual(await layoutInWorker(graph), await layoutInWorker(graph));
});

test("aborting a layout terminates its worker", async () => {
  const stop = new AbortController();
  const run = layoutInWorker(graph, stop.signal);
  stop.abort();
  await assert.rejects(run, /layout stopped/);
});

test("the last layout is served while a newer graph is laid out, and a newer graph stops the running layout", async () => {
  const started: string[] = [];
  const stopped: string[] = [];
  const finish: (() => void)[] = [];
  const layouts = new Layouts((g, signal) => {
    const id = g.nodes[0].id;
    started.push(id);
    return new Promise<Layout>((resolve, reject) => {
      signal.addEventListener("abort", () => (stopped.push(id), reject(new Error("stopped"))));
      finish.push(() => resolve({ key: "", w: 1, h: 1, boxes: {}, edges: [] }));
    });
  });
  const g = (id: string): Graph => ({ nodes: [{ id, w: 1, h: 1 }], edges: [] });
  const settle = () => new Promise((r) => setImmediate(r));

  assert.deepEqual(layouts.request("direct", g("one")), { layout: null, fresh: false });
  finish.shift()!();
  await settle();
  assert.equal(layouts.request("direct", g("one")).fresh, true);
  layouts.request("direct", g("two"));
  layouts.request("direct", g("three"));
  // "two" stopped as soon as "three" was asked for, and "three" started in its place.
  assert.deepEqual(stopped, ["two"]);
  await settle();
  assert.deepEqual(started, ["one", "two", "three"]);
  const stale = layouts.request("direct", g("three"));
  assert.equal(stale.fresh, false);
  assert.equal(stale.layout?.key, graphKey(g("one")));
  // Asking again for the graph being laid out does not stop it.
  assert.deepEqual(stopped, ["two"]);
  // A stopped layout that resolves anyway is not kept.
  finish.shift()!();
  await settle();
  assert.equal(layouts.request("direct", g("three")).layout?.key, graphKey(g("one")));
  finish.shift()!();
  await settle();
  const now = layouts.request("direct", g("three"));
  assert.equal(now.fresh, true);
  assert.equal(now.layout?.key, graphKey(g("three")));
  assert.deepEqual(started, ["one", "two", "three"]);
  // A stopped layout is not reported as failed.
  assert.equal(layouts.request("direct", g("two")).error, undefined);
  // Each edge mode keeps its own layout.
  assert.deepEqual(layouts.request("all", g("three")), { layout: null, fresh: false });
});

test("finished layouts are saved and a saved layout is served at startup", async () => {
  const g: Graph = { nodes: [{ id: "A", w: 1, h: 1 }], edges: [] };
  const saves: Record<string, Layout>[] = [];
  const first = new Layouts(() => Promise.resolve({ key: "", w: 1, h: 1, boxes: {}, edges: [] }), {}, (d) => saves.push(d));
  first.request("direct", g);
  await new Promise((r) => setImmediate(r));
  assert.equal(saves.length, 1);
  assert.equal(saves[0].direct.key, graphKey(g));
  // A restart with the saved layouts serves it at once without laying out again.
  let calls = 0;
  const second = new Layouts(() => (calls++, Promise.reject(new Error("no"))), JSON.parse(JSON.stringify(saves[0])));
  assert.equal(second.request("direct", g).fresh, true);
  assert.equal(calls, 0);
});

test("a failed layout is reported and not retried for the same graph", async () => {
  let calls = 0;
  const layouts = new Layouts(() => {
    calls++;
    return Promise.reject(new Error("no"));
  });
  const g: Graph = { nodes: [{ id: "A", w: 1, h: 1 }], edges: [] };
  const errors = console.error;
  console.error = () => {};
  try {
    layouts.request("direct", g);
    await new Promise((r) => setImmediate(r));
    assert.ok(layouts.request("direct", g).error);
    assert.equal(calls, 1);
  } finally {
    console.error = errors;
  }
});
