// Narrows a finished layout, given in the shape ELK gives one (direction DOWN;
// d3dag.ts converts d3-dag's layout to it). Written for ELK's Brandes-Koepf
// placement, which keeps each node and each long edge on one straight vertical
// line where it can, and those lines push one another sideways into a
// staircase: on the plan of 2026-11-07 the chart was 56,000 px wide while its
// widest layer, packed, needs 14,600 px. d3-dag's center coordinates leave a
// similar width. `narrow` keeps the layers and the order within each layer,
// and places every layer again within the width of the widest packed layer,
// letting edges bend where they must.

// Spacing within a layer: between nodes (GAP[0] in d3dag.ts), a node and an edge, two edges.
const NODE_NODE = 26;
const EDGE_NODE = 8;
const EDGE_EDGE = 8;

// Complexity tradeoff: each sweep places every layer once, given its neighbors
// in the layers above and below; a sweep costs O(m log m) in the objects
// (nodes and edge lanes) and pieces of edge between them. More sweeps move each
// node closer to its neighbors and lose crossings. On the plan of 2026-11-07
// (direct edges) 0, 2, 4, 8 and 16 sweeps gave 13,737, 12,480, 12,454, 12,418
// and 12,136 crossings in 19 to 72 ms; on the 1,000-node test graph 2 to 16
// sweeps gave 2,890 to 3,430 crossings and 0 gave 5,714. 8 is past the point
// where more sweeps stop paying.
const SWEEPS = 8;

// Weights of a piece of edge when a layer is placed: a piece between two edge
// lanes counts most, so long edges stay straight and their bends gather near
// the nodes they join.
const W_LANE_LANE = 8;
const W_NODE_LANE = 2;
const W_NODE_NODE = 1;

interface Pt { x: number; y: number }
interface Section { id?: string; startPoint: Pt; endPoint: Pt; bendPoints?: Pt[] }
interface Kid { id: string; x: number; y: number; width: number; height: number }
interface Edge { id: string; sources: string[]; targets: string[]; sections?: Section[] }
// A connection of an edge to an object: a node (with the connection's offset
// from the node's left side) or an edge lane (offset 0).
interface Stop { o: number; off: number }

export function narrow(out: { children: Kid[]; edges: Edge[] }): { children: Kid[]; edges: Edge[] } {
  const kids = out.children;
  // Layers: nodes whose vertical extents overlap.
  const byTop = kids.map((_, i) => i).sort((a, b) => kids[a].y - kids[b].y);
  const layer: number[] = new Array(kids.length);
  const top: number[] = [], bot: number[] = [];
  for (const i of byTop) {
    const c = kids[i], L = top.length - 1;
    if (L >= 0 && c.y < bot[L]) { layer[i] = L; bot[L] = Math.max(bot[L], c.y + c.height); }
    else { top.push(c.y); bot.push(c.y + c.height); layer[i] = L + 1; }
  }
  const nl = top.length;
  const mid = top.map((t, k) => (t + bot[k]) / 2);
  // Objects: the nodes, then one lane for each vertical run of edge through a layer's middle.
  const x0 = kids.map((c) => c.x), w = kids.map((c) => c.width), isNode = kids.map(() => true);
  const index = new Map(kids.map((c, i) => [c.id, i]));
  const laneAt = new Map<string, number>();
  const lane = (k: number, x: number) => {
    // Merged edges share a lane, so lanes at one place in one layer are one object.
    const key = `${k} ${Math.round(x * 4)}`;
    let o = laneAt.get(key);
    if (o === undefined) { o = layer.length; layer.push(k); x0.push(x); w.push(0); isNode.push(false); laneAt.set(key, o); }
    return o;
  };
  const firstMidBelow = (y: number) => {
    let lo = 0, hi = nl;
    while (lo < hi) { const m = (lo + hi) >> 1; if (mid[m] < y) lo = m + 1; else hi = m; }
    return lo;
  };
  const stops: Stop[][] = out.edges.map((e) => {
    const s = index.get(e.sources[0])!, t = index.get(e.targets[0])!;
    const st: Stop[] = [];
    for (const sec of e.sections ?? []) {
      const p = [sec.startPoint, ...(sec.bendPoints ?? []), sec.endPoint];
      st.push({ o: s, off: p[0].x - kids[s].x });
      for (let i = 1; i < p.length; i++) {
        if (Math.abs(p[i].x - p[i - 1].x) > 0.01) continue;
        const y1 = Math.min(p[i].y, p[i - 1].y), y2 = Math.max(p[i].y, p[i - 1].y);
        const ks: number[] = [];
        for (let k = firstMidBelow(y1); k < nl && mid[k] <= y2; k++) if (k !== layer[s] && k !== layer[t]) ks.push(k);
        if (p[i].y < p[i - 1].y) ks.reverse();
        for (const k of ks) st.push({ o: lane(k, p[i].x), off: 0 });
      }
      st.push({ o: t, off: p[p.length - 1].x - kids[t].x });
    }
    return st;
  });
  const n = layer.length;
  // Each piece of edge between two stops, seen from both ends.
  const pieces: { o: number; myOff: number; itsOff: number; wt: number }[][] = Array.from({ length: n }, () => []);
  for (const st of stops) for (let i = 1; i < st.length; i++) {
    const a = st[i - 1], b = st[i];
    const wt = isNode[a.o] && isNode[b.o] ? W_NODE_NODE : isNode[a.o] || isNode[b.o] ? W_NODE_LANE : W_LANE_LANE;
    pieces[a.o].push({ o: b.o, myOff: a.off, itsOff: b.off, wt });
    pieces[b.o].push({ o: a.o, myOff: b.off, itsOff: a.off, wt });
  }
  const rows: number[][] = Array.from({ length: nl }, () => []);
  for (let o = 0; o < n; o++) rows[layer[o]].push(o);
  for (const r of rows) r.sort((a, b) => x0[a] - x0[b]);
  const sep = (a: number, b: number) => (isNode[a] && isNode[b] ? NODE_NODE : isNode[a] || isNode[b] ? EDGE_NODE : EDGE_EDGE);
  // The width: that of the widest layer packed at the least spacing, the least
  // any placement that keeps the layers and orders can have.
  let width = 0;
  for (const r of rows) {
    let s = 0;
    for (let i = 0; i < r.length; i++) s += w[r[i]] + (i ? sep(r[i - 1], r[i]) : 0);
    width = Math.max(width, s);
  }
  let minX = Infinity, maxX = -Infinity;
  for (let o = 0; o < n; o++) { minX = Math.min(minX, x0[o]); maxX = Math.max(maxX, x0[o] + w[o]); }
  const scale = maxX > minX ? width / (maxX - minX) : 0;
  const x = new Float64Array(n);
  for (let o = 0; o < n; o++) x[o] = (x0[o] - minX) * scale;

  // Places one layer as near its targets as it can, by weighted least squares,
  // keeping its order and spacing and staying within [0, width]: with
  // y_i = x_i - (the packed offset of i), the order and spacing say y is
  // nondecreasing, which pool-adjacent-violators solves in O(k); clamping the
  // pools to the range then keeps y nondecreasing.
  const placeRow = (r: number[], t: Float64Array, wt: Float64Array) => {
    const k = r.length;
    if (k === 0) return;
    const off = new Float64Array(k);
    for (let i = 1; i < k; i++) off[i] = off[i - 1] + w[r[i - 1]] + sep(r[i - 1], r[i]);
    const pv: number[] = [], pw: number[] = [], pn: number[] = [];
    for (let i = 0; i < k; i++) {
      let v = t[i] - off[i], vw = wt[i], cnt = 1;
      while (pv.length && pv[pv.length - 1] >= v) {
        const v2 = pv.pop()!, w2 = pw.pop()!;
        v = (v * vw + v2 * w2) / (vw + w2);
        vw += w2;
        cnt += pn.pop()!;
      }
      pv.push(v); pw.push(vw); pn.push(cnt);
    }
    const hi = width - (off[k - 1] + w[r[k - 1]]);
    for (let p = 0, i = 0; p < pv.length; p++) {
      const v = Math.min(hi, Math.max(0, pv[p]));
      for (let j = 0; j < pn[p]; j++, i++) x[r[i]] = v + off[i];
    }
  };
  for (const r of rows) placeRow(r, Float64Array.from(r, (o) => x[o]), new Float64Array(r.length).fill(1));
  for (let s = 0; s < SWEEPS; s++) {
    for (let q = 0; q < nl; q++) {
      const r = rows[s % 2 === 0 ? q : nl - 1 - q];
      const t = new Float64Array(r.length), wt = new Float64Array(r.length);
      for (let i = 0; i < r.length; i++) {
        const o = r[i];
        // An object with no edges stays where it is, held lightly.
        if (pieces[o].length === 0) { t[i] = x[o]; wt[i] = 0.01; continue; }
        // The weighted median of the places that would make each of its pieces vertical.
        const c = pieces[o].map((p) => [x[p.o] + p.itsOff - p.myOff, p.wt]).sort((a, b) => a[0] - b[0]);
        let total = 0;
        for (const p of c) total += p[1];
        let acc = 0, j = 0;
        while (acc + c[j][1] < total / 2) acc += c[j++][1];
        t[i] = acc + c[j][1] === total / 2 && j + 1 < c.length ? (c[j][0] + c[j + 1][0]) / 2 : c[j][0];
        wt[i] = total;
      }
      placeRow(r, t, wt);
    }
  }
  // Each lane is given as two bend points, where the edge enters and leaves the layer.
  return {
    children: kids.map((c, i) => ({ id: c.id, x: x[i], y: c.y, width: c.width, height: c.height })),
    edges: out.edges.map((e, j) => {
      const st = stops[j];
      const bendPoints: Pt[] = [];
      for (let i = 1; i < st.length - 1; i++) {
        const o = st[i].o;
        bendPoints.push({ x: x[o], y: top[layer[o]] }, { x: x[o], y: bot[layer[o]] });
      }
      const a = st[0], b = st[st.length - 1];
      return {
        id: e.id, sources: e.sources, targets: e.targets,
        sections: st.length === 0 ? [] : [{
          id: `${e.id}s`,
          startPoint: { x: x[a.o] + a.off, y: kids[a.o].y + kids[a.o].height },
          endPoint: { x: x[b.o] + b.off, y: kids[b.o].y },
          bendPoints,
        }],
      };
    }),
  };
}
