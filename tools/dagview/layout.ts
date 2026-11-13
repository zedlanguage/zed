// Lays the plan out with d3-dag (d3dag.ts), which narrow.ts then narrows.
// One layout of the plan of 2026-11-10 (1,661 nodes, 2,580 edges) takes 5 to
// 14 s of one core, by the load. It runs in a worker, off the request path,
// and the page shows the last finished layout until the new one is ready.

import { createHash } from "node:crypto";
import { Worker } from "node:worker_threads";

export interface Box { id: string; w: number; h: number }
export interface Graph { nodes: Box[]; edges: [string, string][] }
export interface Point { x: number; y: number }
export interface Layout {
  key: string;
  w: number;
  h: number;
  // Centers, as the page draws them.
  boxes: Record<string, { x: number; y: number; w: number; h: number }>;
  edges: { from: string; to: string; points: Point[] }[];
  // When the server finished it, in ms since 1970; absent in layouts saved
  // before this was kept.
  at?: number;
  // Each node's layer, top = 0, before splitRows (d3dag.ts), from which the
  // next layout of a changed graph starts; absent in layouts saved before it
  // was kept.
  layers?: Record<string, number>;
  // The row limit those layers were balanced at (layers in d3dag.ts), from
  // which the next layout of a changed graph starts; absent before it was kept.
  rowLimit?: number;
}

// Names the layout method in each key, so a layout saved by an older method is
// not taken for a layout of the same graph by this one. Change it whenever the
// layout changes.
const METHOD = "d3-dag 1.2.2 count-balanced layers then edges shortened within full rows of K, K for a drawn w/h in [0.4, 0.6] toward 1:2, rows over K staggered into rows inserted above them first, every source directly above its highest child unless that row is full, rows over 1.5 x median split, the earlier layers kept only within that band and 1.25 x the rows needed, row limit rounded and order 2026-11-13b";

// What a layout depends on: the node ids, each node's size and the edges.
// Nodes are sorted by id and edges by their two ids, so the order the plan
// lists them in, and any other field a caller sends, changes neither the key
// nor the layout; a repeated edge is kept, since each is drawn.
// Complexity tradeoff: sorting is O(n log n + m log m) for n nodes and m edges,
// a few ms on the plan, against a layout of seconds; keying on the graph as
// sent (O(n + m)) lays the same graph out again whenever its order changes.
export function sortedGraph(g: Graph): Graph {
  const by = (a: string, b: string) => (a < b ? -1 : a > b ? 1 : 0);
  return {
    nodes: g.nodes.map((n) => ({ id: n.id, w: n.w, h: n.h })).sort((p, q) => by(p.id, q.id)),
    edges: g.edges.map(([a, b]): [string, string] => [a, b]).sort((p, q) => by(p[0], q[0]) || by(p[1], q[1])),
  };
}

// The method and a SHA-256 of the sorted graph: the page gets the key with
// every layout, and a hash keeps it short (the sorted graph of the plan is
// about 140 KB).
export function graphKey(g: Graph): string {
  return `${METHOD} ${createHash("sha256").update(JSON.stringify(sortedGraph(g))).digest("hex")}`;
}

// Runs one layout in a fresh worker, so a slow layout never holds up a poll.
// The 64 MB stack was set for ELK, which overflowed the default one; it is
// kept, as d3-dag has not been run on the plan without it.
// prev, an earlier layout, gives the layers, their row limit, the
// left-to-right order and the halves of split rows (its boxes' centers and
// edge routes) to start from if this method made it.
export function layoutInWorker(g: Graph, prev?: Layout): Promise<Layout> {
  const layers = prev?.key.startsWith(`${METHOD} `) ? prev.layers : undefined;
  const at = layers ? Object.fromEntries(Object.entries(prev!.boxes).map(([id, b]) => [id, { x: b.x, y: b.y }])) : undefined;
  return new Promise((resolve, reject) => {
    const w = new Worker(new URL("./layout-worker.ts", import.meta.url), { workerData: { g, layers, at, edges: layers ? prev!.edges : undefined, rowLimit: layers ? prev!.rowLimit : undefined }, resourceLimits: { stackSizeMb: 64 } });
    w.once("message", (l: Layout) => resolve(l));
    w.once("error", reject);
    w.once("exit", (code) => code !== 0 && reject(new Error(`layout worker exited with ${code}`)));
  });
}

// Keeps, for each edge mode, the newest finished layout and the newest graph
// asked for. One layout runs at a time and always runs to the end, because the
// live graph changes more often than it can be laid out: stopping a layout for a
// newer graph would never publish one. A graph asked for while another runs
// replaces any older request for its mode, so the next layout is of the newest graph.
// The finished layouts are passed to `save` and given back at startup, so a
// restarted server shows the last chart while it lays out the current one.
// `status` reports on a mode without asking for anything, so a check of
// freshness does not replace the page's request.
export class Layouts {
  private done = new Map<string, Layout>();
  private want = new Map<string, { key: string; graph: Graph }>();
  private failed = new Map<string, string>();
  private asked = new Map<string, string>();
  private running: { mode: string; key: string; at: number } | null = null;

  private compute: (g: Graph, prev?: Layout) => Promise<Layout>;
  private save: (done: Record<string, Layout>) => void;

  constructor(
    compute: (g: Graph, prev?: Layout) => Promise<Layout>,
    saved: Record<string, Layout> = {},
    save: (done: Record<string, Layout>) => void = () => {},
  ) {
    this.compute = compute;
    this.save = save;
    for (const [mode, l] of Object.entries(saved)) this.done.set(mode, l);
  }

  request(mode: string, graph: Graph): { layout: Layout | null; fresh: boolean; error?: string } {
    graph = sortedGraph(graph);
    const key = graphKey(graph);
    this.asked.set(mode, key);
    const have = this.done.get(mode) ?? null;
    if (have?.key === key) return { layout: have, fresh: true };
    if (this.failed.get(mode) === key) return { layout: have, fresh: false, error: "layout failed; see the server log" };
    // The graph being laid out is the newest asked for, so nothing waits behind it.
    if (this.running?.mode === mode && this.running.key === key) this.want.delete(mode);
    else this.want.set(mode, { key, graph });
    void this.pump();
    return { layout: have, fresh: false };
  }

  // For the last graph asked for in this mode: whether the finished layout is
  // of it, how old the finished layout is, how long the layout running in this
  // mode has run, whether a graph waits, and whether its layout failed.
  status(mode: string, now = Date.now()): { fresh: boolean; ageMs: number | null; runningMs: number | null; waiting: boolean; failed: boolean } {
    const have = this.done.get(mode);
    const asked = this.asked.get(mode);
    return {
      fresh: have !== undefined && have.key === asked,
      ageMs: have?.at === undefined ? null : now - have.at,
      runningMs: this.running?.mode === mode ? now - this.running.at : null,
      waiting: this.want.has(mode),
      failed: asked !== undefined && this.failed.get(mode) === asked,
    };
  }

  private async pump(): Promise<void> {
    if (this.running) return;
    const next = this.want.entries().next();
    if (next.done) return;
    const [mode, { key, graph }] = next.value;
    this.want.delete(mode);
    this.running = { mode, key, at: Date.now() };
    try {
      const l = await this.compute(graph, this.done.get(mode));
      this.done.set(mode, { ...l, key, at: Date.now() });
      this.save(Object.fromEntries(this.done));
    } catch (err) {
      console.error(`layout of ${mode} failed:`, err);
      this.failed.set(mode, key);
    } finally {
      this.running = null;
    }
    void this.pump();
  }
}
