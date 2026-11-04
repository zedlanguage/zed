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
export function layoutInWorker(g: Graph): Promise<Layout> {
  return new Promise((resolve, reject) => {
    const w = new Worker(new URL("./layout-worker.ts", import.meta.url), { workerData: g });
    w.once("message", (l: Layout) => resolve(l));
    w.once("error", reject);
    w.once("exit", (code) => code !== 0 && reject(new Error(`layout worker exited with ${code}`)));
  });
}

// Keeps, for each edge mode, the newest finished layout and the newest graph
// asked for. One layout runs at a time; a graph asked for while another runs
// replaces any older request for its mode, so no stale layout is computed.
export class Layouts {
  private done = new Map<string, Layout>();
  private want = new Map<string, { key: string; graph: Graph }>();
  private failed = new Map<string, string>();
  private busy = false;

  private compute: (g: Graph) => Promise<Layout>;

  constructor(compute: (g: Graph) => Promise<Layout>) {
    this.compute = compute;
  }

  request(mode: string, graph: Graph): { layout: Layout | null; fresh: boolean; error?: string } {
    const key = graphKey(graph);
    const have = this.done.get(mode) ?? null;
    if (have?.key === key) return { layout: have, fresh: true };
    if (this.failed.get(mode) === key) return { layout: have, fresh: false, error: "layout failed; see the server log" };
    this.want.set(mode, { key, graph });
    void this.pump();
    return { layout: have, fresh: false };
  }

  private async pump(): Promise<void> {
    if (this.busy) return;
    const next = this.want.entries().next();
    if (next.done) return;
    const [mode, { key, graph }] = next.value;
    this.busy = true;
    try {
      const l = await this.compute(graph);
      this.done.set(mode, { ...l, key });
    } catch (err) {
      console.error(`layout of ${mode} failed:`, err);
      this.failed.set(mode, key);
    } finally {
      if (this.want.get(mode)?.key === key) this.want.delete(mode);
      this.busy = false;
    }
    void this.pump();
  }
}
