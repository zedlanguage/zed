// The page: reads /api/state when the server reports a change on /api/events,
// and once a minute while visible for the durations and the load; asks the
// server for a layout (/api/layout, laid out with ELK), draws it. It does no
// work between those. The view (pan and zoom) survives every update; a new
// layout is asked for only when the set of nodes, the set of expanded nodes or
// the edge mode changes, and the last layout stays on screen until it arrives.

interface Sub { name: string; role: string; lastAt: number; text: string }
interface Node {
  id: string; level: number; title: string; short: string; size: string; hard: boolean;
  needs: string[]; planned: boolean; state: "unstarted" | "active" | "done" | "waiting" | "blocked"; ready: boolean;
  pushed: boolean; awaitingBatch: boolean; startedAt: number | null; lastAt: number | null;
  runtimeMs: number | null; retries: number; rejections: number; role: string; attempt: string;
  lastText: string; logLines: number; lastTests: string; subs: Sub[]; note: string; questions?: string[];
}
interface LogLine { at: number; time: string; label: string; text: string }
interface State {
  now: number; nodes: Node[]; direct: Record<string, string[]>; log: LogLine[]; warnings: string[];
  machine: { load: string; lock: string; origin: string | null; main: string | null; ahead: number };
}
interface Point { x: number; y: number }
interface Layout {
  key: string; w: number; h: number;
  boxes: Record<string, { x: number; y: number; w: number; h: number }>;
  edges: { from: string; to: string; points: Point[] }[];
}

const TICK_MS = 60_000;
const WIDE = 330;
const NARROW = 210;

function el<K extends keyof HTMLElementTagNameMap>(tag: K, cls = "", text = ""): HTMLElementTagNameMap[K] {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text) e.textContent = text;
  return e;
}

function duration(ms: number | null): string {
  if (ms === null) return "–";
  const s = Math.max(0, Math.floor(ms / 1000));
  const h = Math.floor(s / 3600);
  const m = Math.floor((s % 3600) / 60);
  if (h > 0) return `${h}h ${String(m).padStart(2, "0")}m`;
  if (m > 0) return `${m}m ${String(s % 60).padStart(2, "0")}s`;
  return `${s}s`;
}

const top = el("header");
const title = el("h1", "", "Zed plan");
const counts = el("div", "counts");
const machine = el("div", "machine");
const search = el("input");
search.type = "search";
search.placeholder = "Find a node";
search.setAttribute("aria-label", "Find a node");
const tools = el("div", "tools");
function button(label: string, help: string, act: () => void): HTMLButtonElement {
  const b = el("button", "", label);
  b.title = help;
  b.addEventListener("click", act);
  tools.append(b);
  return b;
}
const legend = el("div", "legend");
for (const [cls, label] of [
  ["done", "● completed"], ["done awaiting", "● completed, not pushed"], ["active", "◐ in progress"],
  ["ready", "○ ready to start"], ["unstarted", "○ waiting"], ["waiting", "◌ deferred"], ["blocked", "◌ blocked"],
]) legend.append(el("span", `chip ${cls}`, label));
top.append(title, counts, search, tools, machine, legend);

const stage = el("main");
const world = el("div", "world");
const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
const nodeLayer = el("div", "nodes");
world.append(svg, nodeLayer);
stage.append(world);

const side = el("aside");
const detail = el("section", "detail");
const logBox = el("section", "log");
side.append(detail, logBox);
document.body.append(top, stage, side);

let current: State | null = null;
let selected: string | null = null;
let allEdges = false;
// The last request the server answered with a layout of exactly that graph,
// the key of the layout on screen, and why the layout on screen is not current.
let freshBody = "";
let drawnKey = "";
let layoutNote = "";
let positions = new Map<string, { x: number; y: number; w: number; h: number }>();
let extent = { w: 1, h: 1 };
const view = { x: 0, y: 0, k: 1 };
let placed = false;
const cards = new Map<string, HTMLElement>();
// What each card was last filled from; an unchanged card that shows no
// durations is not filled again.
const filledFrom = new Map<string, string>();

function applyView(): void {
  world.style.transform = `translate(${view.x}px,${view.y}px) scale(${view.k})`;
}

function fit(ids?: string[]): void {
  const boxes = (ids ?? [...positions.keys()]).flatMap((id) => {
    const p = positions.get(id);
    return p ? [p] : [];
  });
  if (boxes.length === 0) return;
  const x0 = Math.min(...boxes.map((b) => b.x - b.w / 2));
  const x1 = Math.max(...boxes.map((b) => b.x + b.w / 2));
  const y0 = Math.min(...boxes.map((b) => b.y - b.h / 2));
  const y1 = Math.max(...boxes.map((b) => b.y + b.h / 2));
  const r = stage.getBoundingClientRect();
  const pad = 40;
  view.k = Math.min(1, (r.width - pad * 2) / Math.max(1, x1 - x0), (r.height - pad * 2) / Math.max(1, y1 - y0));
  view.x = (r.width - (x1 + x0) * view.k) / 2;
  view.y = (r.height - (y1 + y0) * view.k) / 2;
  applyView();
}

function zoomAt(cx: number, cy: number, factor: number): void {
  const k = view.k * factor;
  view.x = cx - ((cx - view.x) / view.k) * k;
  view.y = cy - ((cy - view.y) / view.k) * k;
  view.k = k;
  applyView();
}

stage.addEventListener("wheel", (ev) => {
  ev.preventDefault();
  const r = stage.getBoundingClientRect();
  zoomAt(ev.clientX - r.left, ev.clientY - r.top, Math.exp(-ev.deltaY * 0.0015));
}, { passive: false });

let drag: { x: number; y: number } | null = null;
stage.addEventListener("pointerdown", (ev) => {
  drag = { x: ev.clientX, y: ev.clientY };
  stage.setPointerCapture(ev.pointerId);
});
stage.addEventListener("pointermove", (ev) => {
  if (!drag) return;
  view.x += ev.clientX - drag.x;
  view.y += ev.clientY - drag.y;
  drag = { x: ev.clientX, y: ev.clientY };
  applyView();
});
stage.addEventListener("pointerup", (ev) => {
  const d = drag;
  drag = null;
  const near = d !== null && Math.abs(ev.clientX - d.x) < 3 && Math.abs(ev.clientY - d.y) < 3;
  stage.releasePointerCapture(ev.pointerId);
  if (!near) return;
  const hit = document.elementsFromPoint(ev.clientX, ev.clientY)
    .find((e) => e instanceof HTMLElement && e.dataset.id) as HTMLElement | undefined;
  select(hit?.dataset.id ?? null);
});

function centerOf(): Point {
  const r = stage.getBoundingClientRect();
  return { x: r.width / 2, y: r.height / 2 };
}
button("+", "Zoom in", () => { const c = centerOf(); zoomAt(c.x, c.y, 1.3); });
button("−", "Zoom out", () => { const c = centerOf(); zoomAt(c.x, c.y, 1 / 1.3); });
button("Fit all", "Show the whole DAG", () => fit());
button("In progress", "Show the nodes in progress and their neighbors", () => fit(focusIds()));
const edgesButton = button("Direct edges", "Switch between direct dependencies and every edge", () => {
  allEdges = !allEdges;
  edgesButton.textContent = allEdges ? "All edges" : "Direct edges";
  const s = current;
  if (s) void relayout(s).then(() => render(s), () => render(s));
});
search.addEventListener("input", () => {
  const q = search.value.trim().toLowerCase();
  for (const [id, card] of cards) {
    const n = current?.nodes.find((x) => x.id === id);
    const hit = q !== "" && n !== undefined && (id.toLowerCase().includes(q) || n.title.toLowerCase().includes(q));
    card.classList.toggle("found", hit);
  }
});
search.addEventListener("keydown", (ev) => {
  if (ev.key !== "Enter") return;
  const found = [...cards].filter(([, c]) => c.classList.contains("found")).map(([id]) => id);
  if (found.length > 0) fit(found);
});

function focusIds(): string[] {
  if (!current) return [];
  const active = current.nodes.filter((n) => n.state === "active");
  const ids = new Set(active.map((n) => n.id));
  for (const n of current.nodes) {
    if (n.ready) ids.add(n.id);
  }
  return ids.size > 0 ? [...ids] : current.nodes.map((n) => n.id);
}

function edgesOf(s: State): [string, string][] {
  const out: [string, string][] = [];
  for (const n of s.nodes) {
    for (const need of allEdges ? n.needs : s.direct[n.id] ?? []) out.push([need, n.id]);
  }
  return out;
}

function heightOf(n: Node): number {
  if (n.state !== "active") return 52;
  return 126 + n.subs.length * 21;
}

// Asks for the layout of the graph s shows. The server answers at once with
// its newest layout for the edge mode, which may be of an older graph while it
// lays out this one; the page draws that and asks again when the server
// reports the layout finished.
async function relayout(s: State): Promise<void> {
  const graph = {
    nodes: s.nodes.map((n) => ({ id: n.id, w: n.state === "active" ? WIDE : NARROW, h: heightOf(n) })),
    edges: edgesOf(s),
  };
  const body = JSON.stringify({ mode: allEdges ? "all" : "direct", graph });
  if (body === freshBody) return;
  const res = await fetch("/api/layout", { method: "POST", body });
  if (!res.ok) throw new Error(String(res.status));
  const answer = await res.json() as { layout: Layout | null; fresh: boolean; error?: string };
  if (answer.fresh) freshBody = body;
  layoutNote = answer.fresh ? "" : answer.error ?? "laying out";
  if (answer.layout && answer.layout.key !== drawnKey) draw(answer.layout, s);
}

function draw(l: Layout, s: State): void {
  drawnKey = l.key;
  extent = { w: l.w, h: l.h };
  positions = new Map(Object.entries(l.boxes));
  svg.setAttribute("width", String(extent.w));
  svg.setAttribute("height", String(extent.h));
  nodeLayer.style.width = `${extent.w}px`;
  nodeLayer.style.height = `${extent.h}px`;
  svg.replaceChildren();
  const stateOf = new Map(s.nodes.map((n) => [n.id, n.state]));
  for (const e of l.edges) {
    const pts = e.points;
    const path = document.createElementNS("http://www.w3.org/2000/svg", "path");
    let d = `M${pts[0].x},${pts[0].y}`;
    for (let i = 1; i < pts.length - 1; i++) {
      const mx = (pts[i].x + pts[i + 1].x) / 2;
      const my = (pts[i].y + pts[i + 1].y) / 2;
      d += ` Q${pts[i].x},${pts[i].y} ${mx},${my}`;
    }
    const end = pts[pts.length - 1];
    d += ` L${end.x},${end.y}`;
    path.setAttribute("d", d);
    path.dataset.from = e.from;
    path.dataset.to = e.to;
    path.setAttribute("class", stateOf.get(e.from) === "done" ? "edge met" : "edge");
    svg.append(path);
  }
  highlight();
}

function highlight(): void {
  for (const p of svg.querySelectorAll("path")) {
    const on = selected !== null && (p.dataset.from === selected || p.dataset.to === selected);
    p.classList.toggle("lit", on);
  }
}

function stat(parent: HTMLElement, label: string, value: string, cls = ""): HTMLElement {
  const box = el("div", `stat ${cls}`);
  box.append(el("b", "", value), el("span", "", label));
  parent.append(box);
  return box;
}

function fill(card: HTMLElement, n: Node, now: number): void {
  const head = el("div", "head");
  head.append(el("span", "code", n.id));
  if (n.size) head.append(el("span", "size", n.size));
  if (n.hard) {
    const hard = el("span", "hard", "hard");
    hard.title = "Hard: a cross-review round decides the design";
    head.append(hard);
  }
  // Not a row of plan_dag.md: an id first seen in the running log or the ledger.
  if (!n.planned) head.append(el("span", "size", "added"));
  card.replaceChildren(head, el("div", "label", n.short));
  if (n.state !== "active") {
    if (n.awaitingBatch) card.append(el("div", "tag", "not pushed"));
    return;
  }
  const stats = el("div", "stats");
  stat(stats, "runtime", duration(n.startedAt === null ? null : now - n.startedAt));
  stat(stats, "retries", String(n.retries), n.retries > 0 ? "warn" : "");
  stat(stats, "rejected", String(n.rejections), n.rejections > 0 ? "bad" : "");
  stat(stats, "last update", n.lastAt === null ? "–" : `${duration(now - n.lastAt)} ago`);
  card.append(stats);
  const now_ = el("div", "doing");
  if (n.role) now_.append(el("span", "role", `${n.role} #${n.attempt}`));
  if (n.lastTests) now_.append(el("span", "tests", n.lastTests));
  card.append(now_);
  if (n.subs.length > 0) {
    const subs = el("div", "subs");
    for (const sub of n.subs) {
      const row = el("div", "sub");
      row.append(el("b", "", sub.name), el("span", "", sub.text));
      row.title = sub.text;
      subs.append(row);
    }
    card.append(subs);
  } else {
    const text = el("div", "status", n.lastText || n.note);
    text.title = n.lastText || n.note;
    card.append(text);
  }
}

function render(s: State): void {
  current = s;
  const active = s.nodes.filter((n) => n.state === "active");
  const live = new Set(s.nodes.map((n) => n.id));
  for (const [id, card] of cards) {
    if (!live.has(id)) {
      card.remove();
      cards.delete(id);
      filledFrom.delete(id);
    }
  }
  for (const n of s.nodes) {
    let card = cards.get(n.id);
    if (!card) {
      card = el("article");
      card.dataset.id = n.id;
      cards.set(n.id, card);
      nodeLayer.append(card);
    }
    // A node the layout on screen does not hold yet waits for the next one.
    const p = positions.get(n.id);
    card.style.display = p ? "" : "none";
    if (!p) continue;
    const found = card.classList.contains("found");
    card.className = `node ${n.state}${n.ready ? " ready" : ""}${n.awaitingBatch ? " awaiting" : ""}` +
      `${n.id === selected ? " selected" : ""}${found ? " found" : ""}`;
    card.style.left = `${p.x - p.w / 2}px`;
    card.style.top = `${p.y - p.h / 2}px`;
    card.style.width = `${p.w}px`;
    card.style.height = `${p.h}px`;
    card.title = n.title;
    const from = JSON.stringify(n);
    if (n.state === "active" || filledFrom.get(n.id) !== from) {
      fill(card, n, s.now);
      filledFrom.set(n.id, from);
    }
  }
  if (!placed && positions.size > 0) {
    placed = true;
    fit(focusIds());
  }

  const done = s.nodes.filter((n) => n.state === "done").length;
  const ready = s.nodes.filter((n) => n.ready).length;
  const total = s.nodes.length;
  counts.replaceChildren();
  stat(counts, "completed", `${done} / ${total}`);
  stat(counts, "in progress", String(active.length));
  stat(counts, "ready", String(ready));
  const held = s.nodes.filter((n) => n.state === "waiting" || n.state === "blocked").length;
  stat(counts, "waiting", String(total - done - active.length - ready - held));
  stat(counts, "deferred", String(held));
  stat(counts, "not pushed", String(s.nodes.filter((n) => n.awaitingBatch).length));
  stat(counts, "retries", String(s.nodes.reduce((a, n) => a + n.retries, 0)));
  // An older server sends no warnings.
  const warnings = s.warnings ?? [];
  if (warnings.length > 0) stat(counts, "override warnings", String(warnings.length), "warn").title = warnings.join("\n");
  machine.replaceChildren();
  stat(machine, "load", s.machine.load);
  stat(machine, "merge lock", s.machine.lock || "free");
  stat(machine, "main / origin", `${s.machine.main ?? "?"} / ${s.machine.origin ?? "?"}`);
  stat(machine, "commits ahead", String(s.machine.ahead));

  logBox.replaceChildren(el("h2", "", "Running log"));
  for (const line of s.log) {
    const row = el("div", "line");
    row.append(el("time", "", line.time.slice(11)), el("b", "", line.label), el("span", "", line.text));
    logBox.append(row);
  }
  if (selected) void showDetail(selected);
}

async function showDetail(id: string): Promise<void> {
  const n = current?.nodes.find((x) => x.id === id);
  if (!n) {
    detail.replaceChildren();
    return;
  }
  const lines = await (await fetch(`/api/log?id=${encodeURIComponent(id)}`)).json() as LogLine[];
  if (selected !== id) return;
  detail.replaceChildren(el("h2", "", n.id), el("p", "", n.title));
  const facts = el("div", "stats");
  const named: Record<string, string> = { active: "in progress", done: "completed", waiting: "deferred", blocked: "blocked" };
  stat(facts, "state", named[n.state] ?? (n.ready ? "ready" : "waiting"));
  stat(facts, "runtime", duration(n.runtimeMs));
  stat(facts, "retries", String(n.retries));
  stat(facts, "rejected", String(n.rejections));
  stat(facts, "log lines", String(n.logLines));
  detail.append(facts);
  if (n.needs.length > 0) detail.append(el("p", "needs", `Needs: ${n.needs.join(", ")}`));
  if (n.questions?.length) detail.append(el("p", "needs", `Held by the author's questions: ${n.questions.join(", ")}`));
  if (n.note) detail.append(el("p", "needs", n.note));
  for (const line of lines.slice(-30).reverse()) {
    const row = el("div", "line");
    row.append(el("time", "", line.time.slice(11)), el("b", "", line.label.replace(/^.*?:/, "")), el("span", "", line.text));
    detail.append(row);
  }
}

function select(id: string | null): void {
  selected = id;
  for (const [cid, card] of cards) card.classList.toggle("selected", cid === id);
  highlight();
  if (id) void showDetail(id);
  else detail.replaceChildren();
}

let lastGood = 0;
function lost(): void {
  title.textContent = lastGood === 0 ? "Zed plan: no server" : `Zed plan: server lost ${duration(Date.now() - lastGood)} ago`;
  title.classList.add("lost");
}

// One read at a time; a change reported during a read is read after it.
let reading = false;
let again = false;
async function refresh(): Promise<void> {
  if (reading) {
    again = true;
    return;
  }
  reading = true;
  try {
    const res = await fetch("/api/state");
    if (!res.ok) throw new Error(String(res.status));
    const s = await res.json() as State;
    await relayout(s);
    render(s);
    lastGood = Date.now();
    title.textContent = layoutNote ? `Zed plan: ${layoutNote}` : "Zed plan";
    title.classList.remove("lost");
  } catch {
    lost();
  }
  reading = false;
  if (again) {
    again = false;
    void refresh();
  }
}

// The browser reconnects by itself after the server restarts, and each
// connection starts with a read, so nothing is missed while it was down.
const events = new EventSource("/api/events");
events.addEventListener("open", () => void refresh());
// A hidden page reads nothing; it reads once when shown again.
events.addEventListener("message", () => {
  if (document.visibilityState === "visible") void refresh();
});
events.addEventListener("error", () => lost());
setInterval(() => {
  if (document.visibilityState === "visible") void refresh();
}, TICK_MS);
document.addEventListener("visibilitychange", () => {
  if (document.visibilityState === "visible") void refresh();
});
