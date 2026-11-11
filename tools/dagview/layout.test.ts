import assert from "node:assert/strict";
import { test } from "node:test";
import { graphKey, Layouts, layoutInWorker, METHODS } from "./layout.ts";
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

for (const method of METHODS) {
  const g: Graph = { ...graph, method };
  test(`the worker lays out every node at its size, top to bottom, and draws each known edge (${method})`, async () => {
    const l = await layoutInWorker(g);
    assert.equal(l.key, graphKey(g));
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

  test(`the same graph gives the same layout (${method})`, async () => {
    assert.deepEqual(await layoutInWorker(g), await layoutInWorker(g));
  });
}

test("a graph with no method is laid out by the first method, and each method has its own key", () => {
  assert.equal(METHODS[0], "d3dag");
  assert.equal(graphKey(graph), graphKey({ ...graph, method: "d3dag" }));
  assert.notEqual(graphKey({ ...graph, method: "d3dag" }), graphKey({ ...graph, method: "elk" }));
});

test("d3-dag: each edge runs from its source's bottom to its target's top, an edge of a cycle is drawn upward, and repeated edges and loops are drawn", async () => {
  const g: Graph = {
    nodes: [...graph.nodes, { id: "E", w: 210, h: 52 }, { id: "F", w: 210, h: 52 }],
    edges: [...graph.edges, ["A", "D"], ["E", "E"], ["A", "B"]],
    method: "d3dag",
  };
  const l = await layoutInWorker(g);
  // E stands alone; F has no edges at all.
  assert.deepEqual(Object.keys(l.boxes).sort(), ["A", "B", "C", "D", "E", "F"]);
  assert.deepEqual(l.edges.map((e) => `${e.from}>${e.to}`).sort(), ["A>B", "A>B", "A>D", "B>C", "C>D", "D>C", "E>E"]);
  const near = (a: number, b: number) => Math.abs(a - b) < 1e-6;
  for (const e of l.edges) {
    const s = l.boxes[e.from], t = l.boxes[e.to], p = e.points, a = p[0], z = p[p.length - 1];
    for (const q of p) assert.ok(q.x >= 0 && q.x <= l.w && q.y >= 0 && q.y <= l.h, `${e.from}>${e.to} leaves the chart`);
    if (e.from === e.to) {
      assert.ok(near(a.x, s.x + s.w / 2) && near(z.x, s.x + s.w / 2), "a loop starts and ends on the right side");
      continue;
    }
    // A cycle (C, D) is broken by drawing one of its edges upward.
    const up = s.y > t.y;
    assert.ok(near(a.y, up ? s.y - s.h / 2 : s.y + s.h / 2), `${e.from}>${e.to} starts off its source`);
    assert.ok(near(z.y, up ? t.y + t.h / 2 : t.y - t.h / 2), `${e.from}>${e.to} ends off its target`);
    assert.ok(Math.abs(a.x - s.x) <= s.w / 2 && Math.abs(z.x - t.x) <= t.w / 2);
  }
  assert.equal(l.edges.filter((e) => l.boxes[e.from].y > l.boxes[e.to].y).length, 1);
  // A to D crosses the layers of B and C, so it bends there.
  assert.ok(l.edges.find((e) => e.from === "A" && e.to === "D")!.points.length > 2);
  // Boxes in one layer do not overlap.
  const bs = Object.values(l.boxes);
  for (const p of bs) for (const q of bs) {
    if (p !== q && Math.abs(p.y - q.y) < (p.h + q.h) / 2) assert.ok(Math.abs(p.x - q.x) >= (p.w + q.w) / 2, "two boxes overlap");
  }
});

test("d3-dag: an empty graph and a single node are laid out", async () => {
  const empty = await layoutInWorker({ nodes: [], edges: [], method: "d3dag" });
  assert.deepEqual([empty.boxes, empty.edges], [{}, []]);
  const one = await layoutInWorker({ nodes: [{ id: "A", w: 210, h: 52 }], edges: [], method: "d3dag" });
  assert.deepEqual(Object.keys(one.boxes), ["A"]);
});

test("the last layout is served while a newer graph is laid out; a running layout finishes, then the newest graph asked for meanwhile is laid out", async () => {
  const started: string[] = [];
  const finish: (() => void)[] = [];
  const layouts = new Layouts((g) => {
    started.push(g.nodes[0].id);
    return new Promise<Layout>((resolve) => finish.push(() => resolve({ key: "", w: 1, h: 1, boxes: {}, edges: [] })));
  });
  const g = (id: string): Graph => ({ nodes: [{ id, w: 1, h: 1 }], edges: [] });
  const settle = () => new Promise((r) => setImmediate(r));

  assert.deepEqual(layouts.request("direct", g("one")), { layout: null, fresh: false });
  finish.shift()!();
  await settle();
  assert.equal(layouts.request("direct", g("one")).fresh, true);
  layouts.request("direct", g("two"));
  layouts.request("direct", g("three"));
  layouts.request("direct", g("four"));
  // "two" keeps running; only the newest graph asked for meanwhile waits.
  assert.deepEqual(started, ["one", "two"]);
  const stale = layouts.request("direct", g("four"));
  assert.equal(stale.fresh, false);
  assert.equal(stale.layout?.key, graphKey(g("one")));
  finish.shift()!();
  await settle();
  // "two" is served as the last finished layout while "four" is laid out.
  assert.equal(layouts.request("direct", g("four")).layout?.key, graphKey(g("two")));
  assert.deepEqual(started, ["one", "two", "four"]);
  finish.shift()!();
  await settle();
  const now = layouts.request("direct", g("four"));
  assert.equal(now.fresh, true);
  assert.equal(now.layout?.key, graphKey(g("four")));
  assert.deepEqual(started, ["one", "two", "four"]);
  // Each edge mode keeps its own layout.
  assert.deepEqual(layouts.request("all", g("four")), { layout: null, fresh: false });
});

test("a graph that changes faster than it is laid out still gets a layout within two layout times", async () => {
  const T = 90;
  const layouts = new Layouts(() => new Promise<Layout>((resolve) => setTimeout(() => resolve({ key: "", w: 1, h: 1, boxes: {}, edges: [] }), T)));
  const g = (id: number): Graph => ({ nodes: [{ id: `n${id}`, w: 1, h: 1 }], edges: [] });
  const t0 = Date.now();
  let served: Layout | null = null;
  for (let i = 0; Date.now() - t0 < 2 * T && served === null; i++) {
    served = layouts.request("direct", g(i)).layout;
    await new Promise((r) => setTimeout(r, T / 3));
  }
  assert.ok(served, `no layout published within ${2 * T} ms`);
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
  // A layout saved by an older layout method, whose key was the graph alone, is laid out again.
  const old = new Layouts(() => (calls++, Promise.reject(new Error("no"))), { direct: { ...saves[0].direct, key: JSON.stringify(g) } });
  assert.equal(old.request("direct", g).fresh, false);
  assert.equal(calls, 1);
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

test("status reports on a mode without asking for a layout or replacing the graph asked for", async () => {
  const finish: (() => void)[] = [];
  const started: string[] = [];
  const layouts = new Layouts((g) => {
    started.push(g.nodes[0].id);
    return new Promise<Layout>((resolve) => finish.push(() => resolve({ key: "", w: 1, h: 1, boxes: {}, edges: [] })));
  });
  const g = (id: string): Graph => ({ nodes: [{ id, w: 1, h: 1 }], edges: [] });
  const settle = () => new Promise((r) => setImmediate(r));

  assert.deepEqual(layouts.status("direct", 0), { fresh: false, ageMs: null, runningMs: null, waiting: false, failed: false });
  layouts.request("direct", g("one"));
  layouts.request("direct", g("two"));
  const t = Date.now();
  const s = layouts.status("direct", t + 5000);
  assert.equal(s.fresh, false);
  assert.ok(s.runningMs !== null && s.runningMs >= 5000);
  assert.equal(s.waiting, true);
  // Asking for status starts nothing and leaves "two" waiting.
  assert.deepEqual(started, ["one"]);
  finish.shift()!();
  await settle();
  assert.deepEqual(started, ["one", "two"]);
  assert.equal(layouts.status("direct").fresh, false);
  finish.shift()!();
  await settle();
  const done = layouts.status("direct", Date.now() + 1000);
  assert.equal(done.fresh, true);
  assert.ok(done.ageMs !== null && done.ageMs >= 1000);
  assert.equal(done.runningMs, null);
  assert.equal(done.waiting, false);
  // The other mode is untouched.
  assert.deepEqual(layouts.status("all", 0), { fresh: false, ageMs: null, runningMs: null, waiting: false, failed: false });
});
