// Lays the plan out with d3-dag (d3dag.ts, the default) or with ELK (layered:
// network-simplex layering, layer-sweep crossing reduction, Brandes-Koepf
// node placement, edges from one node merged),
// narrows the result (narrow.ts) and has ELK route the edges again for the new
// places (layoutTwice). One layout of the plan of 2026-11-07 (1,100 nodes, 1,800
// direct edges) takes 3 to 4 s of one core, and 15 s with all 3,650 edges. It
// runs in a worker, off the request path, and the page shows the last finished
// layout until the new one is ready.

import { Worker } from "node:worker_threads";
import { narrow } from "./narrow.ts";

export interface Box { id: string; w: number; h: number }
// The layout methods; the page picks one and the server falls back to the first.
export const METHODS = ["d3dag", "elk"] as const;
export type Method = (typeof METHODS)[number];
export interface Graph { nodes: Box[]; edges: [string, string][]; method?: Method }
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
}

const options = {
  "elk.algorithm": "layered",
  "elk.direction": "DOWN",
  "elk.padding": "[top=20,left=20,bottom=20,right=20]",
  "elk.spacing.nodeNode": "26",
  "elk.layered.spacing.nodeNodeBetweenLayers": "54",
  "elk.spacing.edgeNode": "8",
  "elk.spacing.edgeEdge": "8",
  // Complexity tradeoff: ELK's network-simplex node placement recomputes every
  // cut value after each pivot, O(n) per pivot and about O(n^2) in all, over a
  // graph of the nodes, one dummy per layer an edge crosses and one node per
  // edge (about 20,000 on the plan of 2026-11-07): it took 240 s on the direct
  // edges. Brandes-Koepf placement is O(n) in the
  // nodes and dummies and takes under 1 s on the same graph. What it gives up:
  // network simplex minimizes the total horizontal stretch of edges, so it gave a
  // chart 20,900 px wide; Brandes-Koepf aligns each node with a median neighbor
  // and balances four such alignments, which leaves gaps and gives about
  // 45,000 px (84,300 px without merged edges). Tried and rejected: linear segments
  // (29,600 px wide, but its placement grows faster than linear: 42 s of a 97 s
  // layout at 4,000 nodes) and simple placement (12,000 px wide, but most edges
  // are pushed to the sides of their layer: 10,300 bends against 4,100).
  // narrow.ts then takes the width out of the Brandes-Koepf placement.
  "elk.layered.nodePlacement.strategy": "BRANDES_KOEPF",
  // Edges leaving one node, or entering one, share a trunk, so the long edges of
  // a busy node take one lane through each layer instead of one each; fewer
  // dummies leave less for crossing reduction to sort. What it gives up: where
  // the trunk splits, which edge goes where is read at the split, not along the
  // whole line.
  "elk.layered.mergeEdges": "true",
  // ELK runs its greedy-switch crossing step only on graphs of fewer than 40
  // nodes (greedySwitch.activationThreshold); turning it off lays every graph
  // out the same way at every size.
  "elk.layered.crossingMinimization.greedySwitch.type": "OFF",
  // Complexity tradeoff: crossing reduction starts from `thoroughness` random
  // orders and keeps the best; each start sweeps the layers and counts every
  // crossing after each sweep, so the time is thoroughness times the sweeps.
  // ELK also stops network-simplex layering after 4 * thoroughness * sqrt(n)
  // pivots per component. What 2 starts give up against ELK's 7: the best of
  // fewer random tries. On the plan of 2026-11-07 that cost nothing (direct
  // edges: the same layout, 4.6 s against 6.0 s; all edges: 61,700 crossings
  // against 78,100, 12 s against 23 s), and the 4,000-node test graph took
  // 25 s against 67 s at load 37. With 1 the direct edges came out with
  // 16,500 crossings against 9,400.
  "elk.layered.thoroughness": "2",
};

// Names the layout method in each key, so a layout saved by an older method is
// not taken for a layout of the same graph by this one. Change it whenever the
// layout changes.
const METHOD: Record<Method, string> = { elk: "narrowed 2026-11-07", d3dag: "d3-dag 1.2.2 narrowed 2026-11-10" };

export function graphKey(g: Graph): string {
  return `${METHOD[g.method ?? METHODS[0]]} ${JSON.stringify({ nodes: g.nodes, edges: g.edges })}`;
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

// The second pass keeps the first pass's layers and orders (interactive
// layering and crossing reduction read them from the places narrow gave) and
// its node places, and routes the edges. ELK reads the input bend points for
// the order of edge lanes without turning them for direction DOWN, so the
// second pass runs in ELK's own direction, RIGHT, on the graph turned on its
// side, and its result is turned back.
//
// Complexity tradeoff: the second pass adds to the first an O(m log m)
// placement (narrow.ts) and an ELK pass with no layering, crossing or placement
// search: on the plan of 2026-11-07 with direct edges 0.05 s and 0.9 s to the
// first pass's 2.4 s, with all edges 0.2 s and 2.7 s to 12.2 s, and on the
// 4,000-node test graph 0.3 s and 4.3 s to 21 s (load 16 to 25). What it buys,
// against the first pass alone: direct edges 14,720 x 13,050 px against
// 56,172 x 11,504, 12,418 crossings against 12,767, 9,962 bends against 4,170;
// all edges 14,538 x 11,362 against 43,076 x 11,324, 9,970 crossings against
// 60,006, 62,744 bends against 36,666. Bends rise because edges bend to fit
// the narrower width. Tried and rejected: ELK's other layerings, placements and
// compactions in one pass (the best, simple placement, gave 15,070 x 19,076 px
// with 17,649 crossings and 10,854 bends), and shifting Brandes-Koepf's
// straight vertical blocks whole (the blocks alone need 56,000 px).
export async function layoutTwice(elk: { layout(g: any): Promise<any> }, g: Graph): Promise<any> {
  const first = await elk.layout(elkGraph(g));
  const c = narrow(first);
  const side = (p: Point) => ({ x: p.y, y: p.x });
  const out = await elk.layout({
    id: "root",
    layoutOptions: {
      ...options,
      "elk.direction": "RIGHT",
      "elk.layered.cycleBreaking.strategy": "INTERACTIVE",
      "elk.layered.layering.strategy": "INTERACTIVE",
      "elk.layered.crossingMinimization.strategy": "INTERACTIVE",
      "elk.layered.nodePlacement.strategy": "INTERACTIVE",
    },
    children: c.children.map((k) => ({ id: k.id, x: k.y, y: k.x, width: k.height, height: k.width })),
    edges: c.edges.map((e) => ({
      ...e,
      sections: (e.sections ?? []).map((s) => ({ ...s, startPoint: side(s.startPoint), endPoint: side(s.endPoint), bendPoints: (s.bendPoints ?? []).map(side) })),
    })),
  });
  return {
    width: out.height,
    height: out.width,
    children: out.children.map((k: any) => ({ id: k.id, x: k.y, y: k.x, width: k.height, height: k.width })),
    edges: out.edges.map((e: any) => ({
      ...e,
      sections: (e.sections ?? []).map((s: any) => ({ startPoint: side(s.startPoint), endPoint: side(s.endPoint), bendPoints: (s.bendPoints ?? []).map(side) })),
    })),
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
// `status` reports on a mode without asking for anything, so a check of
// freshness does not replace the page's request.
export class Layouts {
  private done = new Map<string, Layout>();
  private want = new Map<string, { key: string; graph: Graph }>();
  private failed = new Map<string, string>();
  private asked = new Map<string, string>();
  private running: { mode: string; key: string; at: number } | null = null;

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
      const l = await this.compute(graph);
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
