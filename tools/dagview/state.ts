// Turns the plan, the running log and the ledger into the state of each node.
// Pure functions only: server.ts reads the files and asks git.

export interface PlanRow {
  id: string;
  level: number;
  title: string;
  size: string;
  hard: boolean;
  needs: string[];
}

export interface LogEntry {
  at: number;
  time: string;
  label: string;
  id: string; // the label's item, before aliases
  role: string;
  attempt: string;
  text: string;
}

export interface LedgerEntry {
  id: string;
  state: string;
  by?: string;
  started?: string;
  note?: string;
  commit?: string;
}

export interface Override {
  state?: "done" | "active" | "unstarted";
  note?: string;
  title?: string;
  started?: string;
}

export interface Sub {
  name: string;
  role: string;
  lastAt: number;
  text: string;
}

export type NodeState = "unstarted" | "active" | "done";

export interface ViewNode {
  id: string;
  level: number;
  title: string;
  short: string;
  size: string;
  hard: boolean;
  needs: string[];
  planned: boolean;
  state: NodeState;
  ready: boolean; // unstarted, and everything it needs is merged
  pushed: boolean; // done, and on origin/main as far as the ledger tells
  awaitingBatch: boolean;
  startedAt: number | null;
  lastAt: number | null;
  runtimeMs: number | null;
  retries: number;
  rejections: number;
  role: string;
  attempt: string;
  lastText: string;
  logLines: number;
  lastTests: string;
  subs: Sub[];
  note: string;
}

// Table cells may hold a `|` inside code, so the cells are counted from both ends.
export function parsePlan(markdown: string): PlanRow[] {
  const lines = markdown.split("\n");
  const start = lines.findIndex((l) => l.startsWith("## Items by level"));
  if (start < 0) return [];
  const rows: PlanRow[] = [];
  for (let i = start + 1; i < lines.length && !lines[i].startsWith("## "); i++) {
    const line = lines[i];
    if (!line.startsWith("|")) continue;
    const p = line.split("|");
    const n = p.length;
    if (n < 9) continue;
    const level = Number(p[1].trim());
    if (!Number.isInteger(level) || p[1].trim() === "") continue;
    const needs = p[n - 3].trim();
    rows.push({
      id: p[2].trim(),
      level,
      title: p.slice(3, n - 5).join("|").trim().replaceAll("\\", ""),
      size: p[n - 5].trim(),
      hard: p[n - 4].trim() === "yes",
      needs: needs === "none" || needs === "" ? [] : needs.split(/,\s*/),
    });
  }
  return rows;
}

export function parseLog(text: string): LogEntry[] {
  const out: LogEntry[] = [];
  for (const line of text.split("\n")) {
    const m = /^(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) \| ([^|]+?) \| (.*)$/.exec(line);
    if (!m) continue;
    const label = /^(.+):([a-z]+)#(.*)$/.exec(m[2]);
    out.push({
      at: Date.parse(m[1].replace(" ", "T")),
      time: m[1],
      label: m[2],
      id: label ? label[1] : m[2],
      role: label ? label[2] : "",
      attempt: label ? label[3] : "",
      text: m[3],
    });
  }
  return out;
}

export function parseLedger(text: string): LedgerEntry[] {
  const out: LedgerEntry[] = [];
  for (const line of text.split("\n")) {
    if (line.trim() === "") continue;
    try {
      out.push(JSON.parse(line) as LedgerEntry);
    } catch {
      // An agent may be part way through an append; the next poll reads it.
    }
  }
  return out;
}

// "T2-eval-repair" is T2-eval, "lr2" is LR2, and the XV-* checks are parts of XE2.
export function resolveId(raw: string, known: Map<string, string>): { id: string; sub: string } | null {
  if (raw === "orchestrator") return null;
  const xv = /^XV-(.+)$/.exec(raw);
  if (xv) return { id: "XE2", sub: xv[1] };
  const bare = raw.replace(/-repair$/, "").replace(/^T14-plan$/, "T14");
  return { id: known.get(bare.toLowerCase()) ?? bare, sub: "" };
}

export function shortLabel(title: string): string {
  const text = title.replace(/^Done:\s*/, "").replaceAll("`", "");
  const head = text.split(/[:;(]| - /)[0].trim();
  // A head of one word, such as "S18", names a section and says nothing alone.
  const clause = head.includes(" ") ? head : text;
  if (clause.length <= 38) return clause;
  let out = "";
  for (const word of clause.split(" ")) {
    if ((out + " " + word).length > 36) break;
    out = out === "" ? word : out + " " + word;
  }
  return (out === "" ? clause.slice(0, 36) : out) + "…";
}

function ledgerTime(started: string | undefined, fallbackDay: string): number | null {
  if (!started) return null;
  const full = /^\d{4}-\d\d-\d\d[ T]\d\d:\d\d/.test(started) ? started : `${fallbackDay} ${started}`;
  const at = Date.parse(full.replace(" ", "T"));
  return Number.isNaN(at) ? null : at;
}

export interface Inputs {
  plan: PlanRow[];
  log: LogEntry[];
  ledger: LedgerEntry[];
  overrides: Record<string, Override>;
  onOrigin: (commit: string) => boolean;
  now: number;
}

export function buildNodes(inp: Inputs): ViewNode[] {
  const known = new Map<string, string>();
  for (const r of inp.plan) known.set(r.id.toLowerCase(), r.id);

  const logs = new Map<string, { entry: LogEntry; sub: string }[]>();
  for (const entry of inp.log) {
    const r = resolveId(entry.id, known);
    if (!r) continue;
    if (!logs.has(r.id)) logs.set(r.id, []);
    logs.get(r.id)!.push({ entry, sub: r.sub });
  }
  const ledger = new Map<string, LedgerEntry[]>();
  for (const e of inp.ledger) {
    const id = resolveId(e.id, known)?.id ?? e.id;
    if (!ledger.has(id)) ledger.set(id, []);
    ledger.get(id)!.push(e);
  }

  const rows = [...inp.plan];
  const planned = new Set(rows.map((r) => r.id));
  for (const id of new Set([...logs.keys(), ...ledger.keys()])) {
    if (!planned.has(id)) rows.push({ id, level: -1, title: inp.overrides[id]?.title ?? id, size: "", hard: false, needs: [] });
  }

  const states = new Map<string, NodeState>();
  for (const r of rows) {
    const ov = inp.overrides[r.id]?.state;
    const last = ledger.get(r.id)?.at(-1);
    const lines = logs.get(r.id) ?? [];
    let s: NodeState = "unstarted";
    if (ov) s = ov;
    else if (r.title.startsWith("Done:")) s = "done";
    else if (last?.state === "fixed" || last?.state === "done") s = "done";
    else if (last?.state === "fixing") s = "active";
    else if (last?.state === "abandoned") s = "unstarted";
    else if (lines.some((l) => l.entry.role === "merge" && /\bon main\b|merged/.test(l.entry.text))) s = "done";
    else if (lines.length > 0) s = "active";
    states.set(r.id, s);
  }

  return rows.map((r) => {
    const lines = logs.get(r.id) ?? [];
    const ledgerLines = ledger.get(r.id) ?? [];
    const lastLedger = ledgerLines.at(-1);
    const state = states.get(r.id)!;

    const day = lines[0]?.entry.time.slice(0, 10) ?? inp.log[0]?.time.slice(0, 10) ?? "";
    const times = [
      ...lines.map((l) => l.entry.at),
      ...[...ledgerLines.map((e) => e.started), inp.overrides[r.id]?.started]
        .map((t) => ledgerTime(t, day))
        .filter((t): t is number => t !== null),
    ];
    const startedAt = times.length > 0 ? Math.min(...times) : null;
    const lastAt = times.length > 0 ? Math.max(...times) : null;

    const workers = new Set<string>();
    let rejections = 0;
    let lastTests = "";
    for (const { entry } of lines) {
      if (entry.role === "impl" || entry.role === "repair") workers.add(`${entry.role}#${entry.attempt}`);
      if (entry.role === "verify" && /NOT accepted|ok=false|rejected/i.test(entry.text)) rejections++;
      const tests = /(\d+) pieces,? (\d+) failed/.exec(entry.text);
      if (tests) lastTests = `${tests[1]} pieces, ${tests[2]} failed`;
    }

    const subs = new Map<string, Sub>();
    for (const { entry, sub } of lines) {
      if (sub !== "") subs.set(sub, { name: sub, role: entry.role, lastAt: entry.at, text: entry.text });
    }

    const last = lines.at(-1)?.entry;
    const note = inp.overrides[r.id]?.note ?? lastLedger?.note ?? "";
    // A "done" line after the batch test names no commit; the merge's "fixed" line before it does.
    const commit = state === "done" ? ledgerLines.findLast((e) => e.commit)?.commit : undefined;
    const noCommit = state === "done" && !commit;
    const onOrigin = commit ? inp.onOrigin(commit) : noCommit;
    return {
      id: r.id,
      level: r.level,
      title: r.title,
      short: shortLabel(r.title),
      size: r.size,
      hard: r.hard,
      needs: r.needs,
      planned: planned.has(r.id),
      state,
      ready: state === "unstarted" && r.needs.every((n) => states.get(n) === "done"),
      pushed: state === "done" && onOrigin,
      awaitingBatch: state === "done" && !onOrigin,
      startedAt,
      lastAt,
      runtimeMs: startedAt === null || lastAt === null ? null : (state === "active" ? inp.now : lastAt) - startedAt,
      retries: Math.max(0, workers.size - 1),
      rejections,
      role: last?.role ?? "",
      attempt: last?.attempt ?? "",
      lastText: last?.text ?? "",
      logLines: lines.length,
      lastTests,
      subs: [...subs.values()],
      note,
    };
  });
}

// Edges to draw when only direct dependencies are wanted: a need that another
// need already implies is left out. Ancestors are built once per node, in
// topological order, so each node is visited once.
export function directNeeds(nodes: { id: string; needs: string[] }[]): Map<string, string[]> {
  const byId = new Map(nodes.map((n) => [n.id, n]));
  const ancestors = new Map<string, Set<string>>();
  const pending: { id: string; next: number }[] = [];
  for (const root of nodes) {
    if (ancestors.has(root.id)) continue;
    pending.push({ id: root.id, next: 0 });
    while (pending.length > 0) {
      const top = pending[pending.length - 1];
      const needs = (byId.get(top.id)?.needs ?? []).filter((n) => byId.has(n));
      if (top.next < needs.length) {
        const need = needs[top.next++];
        if (!ancestors.has(need)) pending.push({ id: need, next: 0 });
        continue;
      }
      const all = new Set<string>();
      for (const need of needs) {
        all.add(need);
        for (const a of ancestors.get(need) ?? []) all.add(a);
      }
      ancestors.set(top.id, all);
      pending.pop();
    }
  }
  const out = new Map<string, string[]>();
  for (const n of nodes) {
    const needs = n.needs.filter((x) => byId.has(x));
    out.set(n.id, needs.filter((x) => !needs.some((y) => y !== x && ancestors.get(y)?.has(x))));
  }
  return out;
}
