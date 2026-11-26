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
  agent?: string;
  started?: string;
  // When the line was written: orchestrator lines use `at`, some older lines `ts`.
  at?: string;
  ts?: string;
  note?: string;
  // A line with state "note", or with no state, says only this.
  what?: string;
  commit?: unknown;
  // A merge of several commits lists them all, in this repository or in the spec repository.
  commits?: unknown;
  // The items it needs, and the items that need it; every line adds to the others. An edge between
  // two plan rows belongs in the needs column of the plan row, so these hold the edges of an item with
  // no plan row.
  needs?: string[];
  feeds?: string[];
  // Take back an edge an earlier line of the same item gave in needs or feeds (the ledger is
  // append-only, so this is how a redundant or wrong ledger edge is removed). Lines apply in ledger
  // order: a later needs or feeds gives the edge again.
  unneeds?: string[];
  unfeeds?: string[];
  // Not a step of Zed (the viewer, the test harness, an edit to the plan): no box is drawn and no
  // edge names it, while its ledger and log lines stay as history. The last of the item's own lines
  // (its id, not a label such as "A:merge") that says true or false decides.
  outside?: boolean;
  // For an item outside the graph: the item that took over its work, which a feed into it goes to.
  replacedBy?: string;
  // The title of an item with no plan row.
  title?: string;
  // Why a done item has no commit (a study, a review, a change outside git); board-check.sh counts
  // it as evidence.
  evidence?: string;
}

export interface Sub {
  name: string;
  role: string;
  lastAt: number;
  text: string;
}

// Waiting and blocked nodes are never ready. A blocked node waits on an author question; a dropped item
// is no node at all.
export type NodeState = "unstarted" | "active" | "done" | "waiting" | "blocked";

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
  questions: string[]; // the unanswered author questions that hold it
}

// A row splits at each `|` not written `\|`, as zed-tools' table.rs splits it (the plan tool's
// rule); a `\|` in the title reads as `|`, and every other backslash stays. This is a second copy
// of that splitter because the server cannot run the plan tool: the release `plan` in the main
// checkout is not rebuilt when main moves, and on 2026-11-19 it did not start at all (exit 127, its
// libstd gone with the old toolchain). A row with a stray `|` in its title, which the plan tool
// refuses, is still read: its cells are counted from both ends. board-check-rows.mjs imports this.
export function parsePlan(markdown: string): PlanRow[] {
  const lines = markdown.split("\n");
  const start = lines.findIndex((l) => l.startsWith("## Items by level"));
  if (start < 0) return [];
  const rows: PlanRow[] = [];
  for (let i = start + 1; i < lines.length && !lines[i].startsWith("## "); i++) {
    const line = lines[i];
    if (!line.startsWith("|")) continue;
    const p = line.split(/(?<!\\)\|/);
    const n = p.length;
    if (n < 9) continue;
    const level = Number(p[1].trim());
    if (!Number.isInteger(level) || p[1].trim() === "") continue;
    const needs = p[n - 3].trim();
    rows.push({
      id: p[2].trim(),
      level,
      title: p.slice(3, n - 5).join("|").trim().replaceAll("\\|", "|"),
      size: p[n - 5].trim(),
      hard: p[n - 4].trim() === "yes",
      needs: needs === "none" || needs === "" ? [] : needs.split(/,\s*/),
    });
  }
  return rows;
}

// A label "A:impl#1" or "A:orchestrator": the item, then a role that starts with a small letter, then an
// attempt. The log and the ledger read a label the same way, so "CD-xr:LAZY-hub-unsolved", whose part after
// the colon is no role, is one item in both.
const rolePattern = /^([^:#]+):([a-z][^#]*?)(?:#(.*))?$/;

// A label that is one item's own id: no role and no list.
export const ownLabel = (raw: string): boolean => !rolePattern.test(raw) && !/[,+]/.test(raw);

export function parseLog(text: string): LogEntry[] {
  const out: LogEntry[] = [];
  for (const line of text.split("\n")) {
    const m = /^(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d) \| ([^|]+?) \| (.*)$/.exec(line);
    if (!m) continue;
    // "A:impl#1", and "A:orchestrator" or "A:code-sweep" with no attempt: all three are lines of A.
    // "A, B:orchestrator", "A+B:merge#1" or "A, B" is a line of A and a line of B.
    const label = rolePattern.exec(m[2]);
    for (const id of (label ? label[1] : m[2]).split(/\s*[,+]\s*/)) {
      out.push({
        at: Date.parse(m[1].replace(" ", "T")),
        time: m[1],
        label: m[2],
        id,
        role: label ? label[2] : "",
        attempt: label?.[3] ?? "",
        text: m[3],
      });
    }
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

// The commits a ledger line names, from `commit` and from `commits`. Agents write a hash, a list,
// "a+b", "zed:a b", or an object keyed by repository, so every hash-shaped word in them counts.
export function ledgerCommits(e: LedgerEntry): string[] {
  const out = new Set<string>();
  const pending: unknown[] = [e.commit, e.commits];
  for (let i = 0; i < pending.length; i++) {
    const v = pending[i];
    if (typeof v === "string") for (const m of v.matchAll(/(?<![0-9a-z])[0-9a-f]{7,40}(?![0-9a-z])/g)) out.add(m[0]);
    else if (typeof v === "object" && v !== null) pending.push(...Object.values(v));
  }
  return [...out];
}

// The commits on a branch (origin/main), as a sorted list of full hashes, so
// that an abbreviated hash from the ledger is looked up by its prefix.
// Complexity tradeoff: asking git `merge-base --is-ancestor` for each commit
// forks a process per commit and repository on every request for the state
// (about 1,100 forks and 38 s at load 60 on 2026-11-12, for the 543 ledger
// commits never pushed); this list costs one `git rev-list` of the commits new
// since the last tip when the branch moves, O(n + k log k) to merge k new ones
// into n, and O(log n) per lookup.
export class CommitList {
  tip = "";
  private sorted: string[] = [];

  // Replaces the list, as after a branch moved to a tip that does not descend
  // from the old one.
  reset(hashes: string[], tip: string): void {
    this.sorted = [];
    this.add(hashes, tip);
  }

  // Merges new hashes in; one already in the list is kept once.
  add(hashes: string[], tip: string): void {
    const add = hashes.map((h) => h.trim().toLowerCase()).filter((h) => h !== "").sort();
    const out: string[] = [];
    let i = 0, j = 0;
    while (i < this.sorted.length || j < add.length) {
      const next = j === add.length || (i < this.sorted.length && this.sorted[i] <= add[j]) ? this.sorted[i++] : add[j++];
      if (out[out.length - 1] !== next) out.push(next);
    }
    this.sorted = out;
    this.tip = tip;
  }

  // Whether a commit on the branch starts with this hash of 7 to 40 hex digits.
  has(hash: string): boolean {
    if (!/^[0-9a-f]{7,40}$/.test(hash)) return false;
    let lo = 0, hi = this.sorted.length;
    while (lo < hi) {
      const mid = (lo + hi) >> 1;
      if (this.sorted[mid] < hash) lo = mid + 1;
      else hi = mid;
    }
    return lo < this.sorted.length && this.sorted[lo].startsWith(hash);
  }

  get size(): number {
    return this.sorted.length;
  }
}

// A line with state "note", or with no state, does not change the node's state.
const stateless = (e: LedgerEntry) => typeof e.state !== "string" || e.state === "note";

// "T2-eval-repair" is T2-eval, "lr2" is LR2, and the XV-* checks are parts of XE2.
export function resolveId(raw: string, known: Map<string, string>): { id: string; sub: string } | null {
  if (raw === "orchestrator") return null;
  const xv = /^XV-(.+)$/.exec(raw);
  if (xv) return { id: "XE2", sub: xv[1] };
  // "-repair" is dropped only when the rest is a plan row, so an item named "MSG-forwarded-repair" keeps its name.
  const plan = (id: string) => id.replace(/^T14-plan$/, "T14");
  const unrepaired = plan(raw.replace(/-repair$/, ""));
  const bare = known.has(unrepaired.toLowerCase()) ? unrepaired : plan(raw);
  return { id: known.get(bare.toLowerCase()) ?? bare, sub: "" };
}

// The items a ledger id names: "STRNAN-spec:merge" is STRNAN-spec, and "A+B" or "A, B" is A and B.
export function ledgerItems(raw: string, known: Map<string, string>): string[] {
  const label = rolePattern.exec(raw);
  const ids = (label ? label[1] : raw)
    .split(/\s*[,+]\s*/)
    .map((part) => resolveId(part, known)?.id ?? "")
    .filter((id) => id !== "");
  return [...new Set(ids)];
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
  onOrigin: (commit: string) => boolean;
  now: number;
  // Item to the unanswered questions that hold it (parseQuestions).
  held?: Map<string, string[]>;
}

// The nodes, and the problems board-check.sh prints: edges dagview leaves out and labels that name no item.
export interface BoardState {
  nodes: ViewNode[];
  problems: string[];
  dropped: string[]; // the dropped items the plan or the ledger names, which are no nodes
  outside: string[]; // the items the ledger takes outside the graph, which are no nodes
}

// The items each unanswered author question holds, from the table under "## Which plan steps each
// question holds up" in QUESTIONS.md: item id to question ids. A cell that starts "Nothing" or "see"
// holds nothing; a parenthesis, the text after ";" or ":", and an item reached "through it" are notes, not
// holds (an item that needs a held one waits through its needs). "L30.1 to L30.3" is a range. A question
// whose section carries an "**Answer (" paragraph is answered and holds nothing.
export function parseQuestions(markdown: string): Map<string, string[]> {
  const lines = markdown.split("\n");
  const answered = new Set<string>();
  let section = "";
  for (const l of lines) {
    const h = /^#{2,4} ([A-Z]+\d+):/.exec(l);
    if (h) section = h[1];
    else if (/^#{1,4} /.test(l)) section = "";
    else if (section && l.startsWith("**Answer (")) answered.add(section);
  }
  const held = new Map<string, string[]>();
  const start = lines.findIndex((l) => l.startsWith("## Which plan steps each question holds up"));
  if (start < 0) return held;
  let i = start + 1;
  while (i < lines.length && !lines[i].startsWith("|")) i++;
  for (i += 2; i < lines.length && lines[i].startsWith("|"); i++) {
    const cells = lines[i].split("|").map((c) => c.trim());
    const [q, steps] = [cells[1], cells[2] ?? ""];
    if (answered.has(q) || /^(nothing|see)\b/i.test(steps)) continue;
    let text = steps.split(/[;:]/)[0];
    while (/\([^()]*\)/.test(text)) text = text.replace(/\([^()]*\)/g, "");
    text = text.replace(/\bthrough (it|them)\b[^,]*/g, "");
    text = text.replace(/\b([A-Za-z][\w-]*\.)(\d+) to \1(\d+)\b/g, (_, p: string, a: string, b: string) =>
      Array.from({ length: Math.max(0, Number(b) - Number(a) + 1) }, (_, k) => p + (Number(a) + k)).join(", "));
    for (const id of text.match(/\b[A-Z][A-Za-z0-9]*(?:[.-][A-Za-z0-9]+)*\b/g) ?? []) {
      // An id has a digit or a dash, or is all capitals, as the row FPWARN (DAGVIEW-held-digitless):
      // heldRows keeps such a word only when it is a plan row's id, so DESIGN in a cell holds nothing.
      if (!/[\d-]/.test(id) && !/^[A-Z]{2,}$/.test(id)) continue;
      if (!held.has(id)) held.set(id, []);
      if (!held.get(id)!.includes(q)) held.get(id)!.push(q);
    }
  }
  return held;
}

export function buildNodes(inp: Inputs): ViewNode[] {
  return buildGraph(inp).nodes;
}

// The held items (parseQuestions) by plan row: an id the plan has, in any
// case, is that row; a DESIGN sub-step the plan has no row for, a row id with
// a lowercase letter added ("L10.3b"), is its row ("L10.3"). Any other id is
// kept as written (an item the ledger alone names), except a word of capitals
// alone, which parseQuestions keeps for rows such as FPWARN: it is kept only when
// it is a plan row's id as written, since such a word is as likely plain text in
// capitals (DESIGN, DAG).
export function heldRows(held: Map<string, string[]> | undefined, known: Map<string, string>): Map<string, string[]> {
  const out = new Map<string, string[]>();
  for (const [raw, qs] of held ?? []) {
    if (/^[A-Z]{2,}$/.test(raw) && known.get(raw.toLowerCase()) !== raw) continue;
    const sub = /^(.*\d)[a-z]$/.exec(raw);
    const id = known.get(raw.toLowerCase()) ?? (sub ? known.get(sub[1].toLowerCase()) : undefined) ?? raw;
    const list = out.get(id) ?? [];
    for (const q of qs) if (!list.includes(q)) list.push(q);
    out.set(id, list);
  }
  return out;
}

export function buildGraph(inp: Inputs): BoardState {
  const known = new Map<string, string>();
  for (const r of inp.plan) known.set(r.id.toLowerCase(), r.id);
  const problems: string[] = [];
  const held = heldRows(inp.held, known);

  // The label an item is named by when nothing else names it, for the problem that reports it.
  const labelOf = new Map<string, string>();
  const logs = new Map<string, { entry: LogEntry; sub: string }[]>();
  for (const entry of inp.log) {
    const r = resolveId(entry.id, known);
    if (!r) continue;
    if (!logs.has(r.id)) logs.set(r.id, []);
    logs.get(r.id)!.push({ entry, sub: r.sub });
    // The orchestrator's bookkeeping (status, plan and lock lines) names no task.
    if (entry.role !== "orchestrator" && !labelOf.has(r.id)) labelOf.set(r.id, entry.label);
  }
  // Only a ledger line whose id is the item's own makes the item a node; a line of a label such as
  // "A:merge" or "A+B" goes to each item it names.
  const ledger = new Map<string, LedgerEntry[]>();
  const ownLines = new Map<string, LedgerEntry[]>();
  for (const e of inp.ledger) {
    // A line without a string id (an agent wrote "item" for "id") names no item; report it, do not fail.
    if (typeof e.id !== "string") {
      problems.push(`LEDGER LINE WITH NO ID: ${JSON.stringify(e).slice(0, 120)}`);
      continue;
    }
    const ids = ledgerItems(e.id, known);
    for (const id of ids) {
      if (!ledger.has(id)) ledger.set(id, []);
      ledger.get(id)!.push(e);
      if (ownLabel(e.id)) {
        if (!ownLines.has(id)) ownLines.set(id, []);
        ownLines.get(id)!.push(e);
      } else if (!labelOf.has(id)) labelOf.set(id, e.id);
    }
  }
  // The last of the item's own lines that gives the field as the type asked for.
  const lastOwn = <T,>(id: string, field: "outside" | "replacedBy" | "title", type: string): T | undefined =>
    ownLines.get(id)?.findLast((e) => typeof e[field] === type)?.[field] as T | undefined;

  const outside = (id: string) => lastOwn<boolean>(id, "outside", "boolean") === true;
  // A dropped item is no node, and a need on it counts as met: the ledger's last state says dropped, or
  // the plan row's title starts "Done: Dropped".
  const droppedRows = new Set(inp.plan.filter((r) => /^Done: Dropped\b/.test(r.title)).map((r) => r.id));
  const dropped = (id: string): boolean =>
    droppedRows.has(id) || ledger.get(id)?.findLast((e) => !stateless(e))?.state === "dropped";
  const gone = (id: string) => outside(id) || dropped(id);
  const rows = inp.plan.filter((r) => !gone(r.id));
  const planned = new Set(rows.map((r) => r.id));
  // A label alone makes no node: an item needs a plan row or a ledger line of its own.
  for (const id of new Set([...logs.keys(), ...ledger.keys()])) {
    if (planned.has(id) || gone(id)) continue;
    if (ownLines.has(id)) rows.push({ id, level: -1, title: lastOwn<string>(id, "title", "string") ?? id, size: "", hard: false, needs: [] });
    else if (labelOf.has(id)) problems.push(`LABEL WITH NO ITEM: ${id} (from "${labelOf.get(id)}"; give it a ledger line)`);
  }
  const nodeIds = new Set(rows.map((r) => r.id));

  const states = new Map<string, NodeState>();
  for (const r of rows) {
    const last = ledger.get(r.id)?.findLast((e) => !stateless(e));
    const ls = last?.state;
    const lines = logs.get(r.id) ?? [];
    let s: NodeState = "unstarted";
    // A done row's title starts with the word "Done": most write "Done: ...", some "Done (<agent>,
    // <date>): ...", "Done by <agent> ..." or "Done in <commit> ..." (as the plan tool's conflicts.rs
    // reads them; DAGVIEW-done-rows-active).
    if (/^Done\b/.test(r.title)) s = "done";
    // Only a merge or the orchestrator finishes a node: an impl, repair, verify or probe agent's
    // "done" means its own attempt ended, and the item may still be rejected and repaired.
    else if ((ls === "fixed" || ls === "done") && !/:(impl|repair|verify|probe)#/.test(last!.by ?? last!.agent ?? "")) s = "done";
    // Since 2026-11-12 an impl agent merges its own work, so its "fixed" line finishes the node
    // once every commit it names is on origin/main.
    else if ((ls === "fixed" || ls === "done") && ledgerCommits(last!).length > 0 && ledgerCommits(last!).every((c) => inp.onOrigin(c))) s = "done";
    else if (ls === "fixed" || ls === "done" || ls === "verified") s = "active";
    else if (ls === "merged") s = "done";
    else if (ls === "blocked") s = "blocked";
    else if (ls === "waiting" || ls === "deferred") s = "waiting";
    else if (ls === "fixing" || ls === "drafting" || ls === "merging") s = "active";
    else if (ls === "abandoned") s = "unstarted";
    // An item the ledger lists as open is not active, whatever the log says about it.
    // "unsolved" (an agent gave up after its rounds) and "todo" (a follow-up an agent filed) wait for a
    // new attempt; "ready" (a branch handed to the orchestrator to merge) waits on the merge.
    else if (ls === "open" || ls === "queued" || ls === "unsolved" || ls === "todo") s = "unstarted";
    else if (ls === "ready") s = "waiting";
    else if (ls === "running" || ls === "started" || ls === "active") s = "active";
    else if (lines.some((l) => l.entry.role === "merge" && /\bon main\b|merged/.test(l.entry.text))) s = "done";
    else if (lines.length > 0) s = "active";
    // An unanswered author question holds an item that is not yet done or under way.
    if ((s === "unstarted" || s === "waiting") && held.has(r.id)) s = "blocked";
    states.set(r.id, s);
  }

  // Edges come from the plan rows and the ledger lines, and each source adds to the other. An edge
  // between two plan rows is written in the plan row's needs column; the ledger holds the edges of an
  // item with no plan row. A feed into an item outside the graph goes to the item its ledger line
  // names in replacedBy.
  const replaced = (f: string): string | null => {
    const seen = new Set<string>();
    while (outside(f)) {
      const next = lastOwn<string>(f, "replacedBy", "string");
      if (next === undefined || seen.has(f)) return null;
      seen.add(f);
      f = next;
    }
    return f;
  };
  const own = new Map<string, string[]>();
  const fed = new Map<string, string[]>();
  // An agent may write a bare string for one id; it is read as that id, not dropped (29 ledger
  // lines had one by 2026-11-25, and five of their edges were missing from the graph).
  const list = (x: unknown): string[] =>
    typeof x === "string" ? [x] : Array.isArray(x) ? x.filter((s) => typeof s === "string") : [];
  for (const [id, es] of ledger) {
    if (!nodeIds.has(id)) continue;
    // The item's needs and feeds after its lines in order, each unneeds or unfeeds taking back what
    // the lines before it gave. Sets keep this linear in the number of ids the lines name.
    const needSet = new Set<string>();
    const feedSet = new Set<string>();
    for (const e of es) {
      for (const n of list(e.needs)) needSet.add(n);
      for (const n of list(e.unneeds)) needSet.delete(n);
      for (const f of list(e.feeds)) feedSet.add(f);
      for (const f of list(e.unfeeds)) feedSet.delete(f);
    }
    own.set(id, [...needSet]);
    for (const f of feedSet) {
      const to = replaced(f);
      if (to !== null && dropped(to)) continue;
      if (to === null) {
        problems.push(`FEED INTO OUTSIDE ITEM: ${id} feeds ${f} (give ${f} a replacedBy in a ledger line of its own, or remove the feed)`);
        continue;
      }
      if (!fed.has(to)) fed.set(to, []);
      fed.get(to)!.push(id);
    }
  }
  for (let i = 0; i < rows.length; i++) {
    const r = rows[i];
    const all = new Set([...r.needs, ...(own.get(r.id) ?? []), ...(fed.get(r.id) ?? [])]);
    rows[i] = { ...r, needs: [...all].filter((n) => n !== r.id && !gone(n)) };
  }

  const nodes = rows.map((r): ViewNode => {
    const lines = logs.get(r.id) ?? [];
    const ledgerLines = ledger.get(r.id) ?? [];
    const lastLedger = ledgerLines.at(-1);
    const state = states.get(r.id)!;

    const day = lines[0]?.entry.time.slice(0, 10) ?? inp.log[0]?.time.slice(0, 10) ?? "";
    const times = [
      ...lines.map((l) => l.entry.at),
      ...ledgerLines
        .flatMap((e) => [e.started, e.at, e.ts])
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
    const note = lastLedger?.note ?? (lastLedger && stateless(lastLedger) ? lastLedger.what : undefined) ?? "";
    // A "done" line after the batch test names no commit; the merge's "fixed" line before it does.
    const commitLine = state === "done" ? ledgerLines.findLast((e) => ledgerCommits(e).length > 0) : undefined;
    const commits = commitLine ? ledgerCommits(commitLine) : [];
    const onOrigin = commits.length > 0 ? commits.every((c) => inp.onOrigin(c)) : state === "done";
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
      questions: held.get(r.id) ?? [],
    };
  });
  const listed = [...new Set([...inp.plan.map((r) => r.id), ...ledger.keys()])];
  const droppedIds = listed.filter((id) => !outside(id) && dropped(id));
  return { nodes, problems: [...new Set(problems)], dropped: droppedIds, outside: listed.filter(outside) };
}

// Problems in the shape of the graph: a cycle of needs, and a need that a
// longer path already implies (the graph must be its own transitive
// reduction, so the viewer draws every edge). Ancestors are built once per
// node, in topological order, with an explicit stack; a need back into a node
// still on the stack closes a cycle, which is reported and not followed.
// Complexity tradeoff: the ancestor sets cost O(n·a) time and memory for a the
// mean number of ancestors. No near-linear method is known: transitive
// reduction is as hard as transitive closure (Aho, Garey and Ullman, 1972).
export function shapeProblems(nodes: { id: string; needs: string[] }[]): string[] {
  const byId = new Map(nodes.map((n) => [n.id, n]));
  const ancestors = new Map<string, Set<string>>();
  const onStack = new Set<string>();
  const pending: { id: string; next: number }[] = [];
  const problems: string[] = [];
  for (const root of nodes) {
    if (ancestors.has(root.id)) continue;
    pending.push({ id: root.id, next: 0 });
    onStack.add(root.id);
    while (pending.length > 0) {
      const top = pending[pending.length - 1];
      const needs = (byId.get(top.id)?.needs ?? []).filter((n) => byId.has(n));
      if (top.next < needs.length) {
        const need = needs[top.next++];
        if (onStack.has(need)) {
          const from = pending.findIndex((p) => p.id === need);
          problems.push(`CYCLE OF NEEDS: ${pending.slice(from).map((p) => p.id).join(" -> ")} -> ${need}`);
        } else if (!ancestors.has(need)) {
          pending.push({ id: need, next: 0 });
          onStack.add(need);
        }
        continue;
      }
      const all = new Set<string>();
      for (const need of needs) {
        all.add(need);
        for (const a of ancestors.get(need) ?? []) all.add(a);
      }
      ancestors.set(top.id, all);
      onStack.delete(top.id);
      pending.pop();
    }
  }
  for (const n of nodes) {
    const needs = n.needs.filter((x) => byId.has(x));
    for (const x of needs) {
      const via = needs.find((y) => y !== x && ancestors.get(y)?.has(x));
      if (via !== undefined) problems.push(`REDUNDANT NEED: ${n.id} needs ${x}, already implied through ${via}; remove the edge`);
    }
  }
  return problems;
}
