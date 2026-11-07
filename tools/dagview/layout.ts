// Lays the plan out with ELK (layered, network-simplex node placement), which
// keeps the chart narrow: on the plan of 2026-11-03 it is 15,190 px wide where
// dagre's placement was 38,237 px.
// One layout of the whole plan takes most of a minute of one core, so it runs
// in a worker, off the request path, and the page shows the last finished
// layout until the new one is ready.

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
}

const options = {
  "elk.algorithm": "layered",
  "elk.direction": "DOWN",
  "elk.padding": "[top=20,left=20,bottom=20,right=20]",
  "elk.spacing.nodeNode": "26",
  "elk.layered.spacing.nodeNodeBetweenLayers": "54",
  "elk.spacing.edgeNode": "8",
  "elk.spacing.edgeEdge": "8",
  "elk.layered.nodePlacement.strategy": "NETWORK_SIMPLEX",
};

export function graphKey(g: Graph): string {
  return JSON.stringify(g);
}

// Edges to unknown nodes are dropped; a cycle in the plan is broken by ELK,
// which draws the reversed edge upward.
export function elkGraph(g: Graph) {
  const known = new Set(g.nodes.map((n) => n.id));
  return {
    id: "root",
    layoutOptions: options,
    children: g.nodes.map((n) => ({ id: n.id, width: n.w, height: n.h })),
    edges: g.edges
      .filter(([a, b]) => known.has(a) && known.has(b))
      .map(([a, b], i) => ({ id: `e${i}`, sources: [a], targets: [b] })),
  };
}

export function fromElk(key: string, out: any): Layout {
  const boxes: Layout["boxes"] = {};
  for (const c of out.children) boxes[c.id] = { x: c.x + c.width / 2, y: c.y + c.height / 2, w: c.width, h: c.height };
  const edges: Layout["edges"] = [];
  for (const e of out.edges) {
    for (const s of e.sections ?? []) {
      edges.push({ from: e.sources[0], to: e.targets[0], points: [s.startPoint, ...(s.bendPoints ?? []), s.endPoint] });
    }
  }
  return { key, w: out.width, h: out.height, boxes, edges };
}

// Runs one layout in a fresh worker, so a slow layout never holds up a poll.
// ELK recurses deeply: on the plan of 2026-11-07 with all edges (991 nodes, 3,400 edges) it overflowed the
// worker's default stack after 10 s; with 64 MB it ran for 60 s without overflowing.
export function layoutInWorker(g: Graph): Promise<Layout> {
  return new Promise((resolve, reject) => {
    const w = new Worker(new URL("./layout-worker.ts", import.meta.url), { workerData: g, resourceLimits: { stackSizeMb: 64 } });
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
export class Layouts {
  private done = new Map<string, Layout>();
  private want = new Map<string, { key: string; graph: Graph }>();
  private failed = new Map<string, string>();
  private running: { mode: string; key: string } | null = null;

  private compute: (g: Graph) => Promise<Layout>;
  private save: (done: Record<string, Layout>) => void;

  constructor(
    compute: (g: Graph) => Promise<Layout>,
    saved: Record<string, Layout> = {},
    save: (done: Record<string, Layout>) => void = () => {},
  ) {
    this.compute = compute;
    this.save = save;
    for (const [mode, l] of Object.entries(saved)) this.done.set(mode, l);
  }

  request(mode: string, graph: Graph): { layout: Layout | null; fresh: boolean; error?: string } {
    const key = graphKey(graph);
    const have = this.done.get(mode) ?? null;
    if (have?.key === key) return { layout: have, fresh: true };
    if (this.failed.get(mode) === key) return { layout: have, fresh: false, error: "layout failed; see the server log" };
    // The graph being laid out is the newest asked for, so nothing waits behind it.
    if (this.running?.mode === mode && this.running.key === key) this.want.delete(mode);
    else this.want.set(mode, { key, graph });
    void this.pump();
    return { layout: have, fresh: false };
  }

  private async pump(): Promise<void> {
    if (this.running) return;
    const next = this.want.entries().next();
    if (next.done) return;
    const [mode, { key, graph }] = next.value;
    this.want.delete(mode);
    this.running = { mode, key };
    try {
      const l = await this.compute(graph);
      this.done.set(mode, { ...l, key });
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
