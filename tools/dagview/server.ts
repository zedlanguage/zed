// Serves the live plan view on http://127.0.0.1:4317 (PORT overrides the port).
// Run with `node server.ts`. Node strips the types; nothing is compiled.
//
// Reads, on each request for the state: docs/plan_dag.md, wt/running-log.md,
// wt/ledger.jsonl, wt/dag-overrides.json, the author's open questions in
// wt/zed0-review/pass2/QUESTIONS.md, wt/merge.lock/owner, /proc/loadavg and git. Lays the plan out when the page posts its graph to /api/layout (see
// layout.ts). It watches those files and the main and origin/main refs, and
// tells the page over /api/events when one changes or a layout finishes, so an
// idle page and server do no work.

import { execFile } from "node:child_process";
import { watch } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import { createServer } from "node:http";
import type { IncomingMessage, ServerResponse } from "node:http";
import { stripTypeScriptTypes } from "node:module";
import { basename, dirname, join, resolve } from "node:path";
import { promisify } from "node:util";
import { buildGraph, shapeProblems, ledgerCommits, overrideWarnings, parseLedger, parseLog, parsePlan, parseQuestions, resolveId } from "./state.ts";
import type { Override } from "./state.ts";
import { Layouts, METHODS, layoutInWorker } from "./layout.ts";
import type { Graph, Method } from "./layout.ts";

const here = import.meta.dirname;
const repo = process.env.DAGVIEW_REPO ?? resolve(here, "../..");
const work = process.env.DAGVIEW_WT ?? resolve(repo, "../wt");
// Ledger lines also name commits of the spec repository.
const spec = process.env.DAGVIEW_SPEC ?? resolve(repo, "../zed");
const questions = process.env.DAGVIEW_QUESTIONS ?? join(work, "zed0-review/pass2/QUESTIONS.md");
const port = Number(process.env.PORT ?? 4317);
const run = promisify(execFile);

async function text(path: string): Promise<string> {
  try {
    return await readFile(path, "utf8");
  } catch {
    return "";
  }
}

async function git(...args: string[]): Promise<string | null> {
  return gitIn(repo, ...args);
}

async function gitIn(dir: string, ...args: string[]): Promise<string | null> {
  try {
    return (await run("git", ["-C", dir, ...args])).stdout.trim();
  } catch {
    return null;
  }
}

// Whether a commit is on origin/main never changes back, so a yes is kept.
const onOriginMemo = new Set<string>();
let originSeen = "";

async function originCommits(commits: string[], origin: string): Promise<void> {
  if (origin === originSeen && commits.every((c) => onOriginMemo.has(c))) return;
  originSeen = origin;
  await Promise.all(
    commits
      .filter((c) => !onOriginMemo.has(c))
      .map(async (c) => {
        for (const dir of [repo, spec]) {
          if ((await gitIn(dir, "merge-base", "--is-ancestor", c, "origin/main")) !== null) {
            onOriginMemo.add(c);
            break;
          }
        }
      }),
  );
}

async function state() {
  const [plan, logText, ledgerText, overridesText, questionsText, lock, loadavg, origin, main, ahead] = await Promise.all([
    text(join(repo, "docs/plan_dag.md")),
    text(join(work, "running-log.md")),
    text(join(work, "ledger.jsonl")),
    text(join(work, "dag-overrides.json")),
    text(questions),
    text(join(work, "merge.lock/owner")),
    text("/proc/loadavg"),
    git("rev-parse", "--short", "origin/main"),
    git("rev-parse", "--short", "main"),
    git("rev-list", "--count", "origin/main..main"),
  ]);
  const log = parseLog(logText);
  const ledger = parseLedger(ledgerText);
  let overrides: Record<string, Override> = {};
  try {
    overrides = JSON.parse(overridesText) as Record<string, Override>;
  } catch {
    // No file, or one being written: the next poll reads it.
  }
  await originCommits(ledger.flatMap(ledgerCommits), origin ?? "");
  const now = Date.now();
  const { nodes, problems, dropped } = buildGraph({
    plan: parsePlan(plan),
    log,
    ledger,
    overrides,
    onOrigin: (c) => onOriginMemo.has(c),
    now,
    held: parseQuestions(questionsText),
  });
  return {
    now,
    nodes,
    log: log.slice(-60).reverse(),
    warnings: overrideWarnings(overrides),
    problems: [...problems, ...shapeProblems(nodes)],
    dropped,
    machine: {
      load: loadavg.split(" ").slice(0, 3).join(" "),
      lock: lock.trim(),
      origin,
      main,
      ahead: Number(ahead ?? 0),
    },
  };
}

const page = `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><title>Zed plan</title>
<meta name="viewport" content="width=device-width, initial-scale=1">
<link rel="stylesheet" href="/style.css"></head>
<body><script type="module" src="/client.js"></script></body></html>`;

// The pages listening on /api/events. A change is sent once its burst of file
// events has been quiet for a quarter second.
const listeners = new Set<ServerResponse>();
let changeTimer: ReturnType<typeof setTimeout> | null = null;
function changed(): void {
  if (changeTimer) clearTimeout(changeTimer);
  changeTimer = setTimeout(() => {
    changeTimer = null;
    for (const res of listeners) res.write("data: change\n\n");
  }, 250);
}

// Directories are watched, not files: sed -i and git replace a file by
// renaming a new one over it, which a watch on the old file never reports.
function watchNames(dir: string, names: string[]): void {
  try {
    watch(dir, (_, name) => {
      if (name !== null && names.includes(String(name))) changed();
    });
  } catch (err) {
    console.error(`not watching ${dir}:`, err);
  }
}
watchNames(join(repo, "docs"), ["plan_dag.md"]);
watchNames(work, ["running-log.md", "ledger.jsonl", "dag-overrides.json", "merge.lock"]);
watchNames(join(work, "merge.lock"), ["owner"]);
watchNames(dirname(questions), [basename(questions)]);
for (const dir of [repo, spec]) {
  watchNames(join(dir, ".git"), ["packed-refs"]);
  watchNames(join(dir, ".git/refs/heads"), ["main"]);
  watchNames(join(dir, ".git/refs/remotes/origin"), ["main"]);
}

const savedLayouts = join(work, "dagview-layouts.json");
const layouts = new Layouts(
  layoutInWorker,
  JSON.parse(await readFile(savedLayouts, "utf8").catch(() => "{}")),
  (done) => {
    changed();
    void writeFile(savedLayouts, JSON.stringify(done)).catch((err) => console.error(`saving layouts failed:`, err));
  },
);

async function body(req: IncomingMessage): Promise<string> {
  const parts: Buffer[] = [];
  for await (const part of req) parts.push(part as Buffer);
  return Buffer.concat(parts).toString("utf8");
}

const server = createServer(async (req, res) => {
  const url = new URL(req.url ?? "/", "http://localhost");
  const send = (type: string, body: string, status = 200) => {
    res.writeHead(status, { "content-type": type, "cache-control": "no-store" });
    res.end(body);
  };
  try {
    switch (url.pathname) {
      case "/":
        return send("text/html; charset=utf-8", page);
      case "/style.css":
        return send("text/css; charset=utf-8", await readFile(join(here, "style.css"), "utf8"));
      case "/client.js":
        return send(
          "text/javascript; charset=utf-8",
          stripTypeScriptTypes(await readFile(join(here, "client.ts"), "utf8")),
        );
      case "/api/events":
        res.writeHead(200, { "content-type": "text/event-stream", "cache-control": "no-store" });
        res.write("retry: 2000\n\n");
        listeners.add(res);
        req.on("close", () => listeners.delete(res));
        return;
      case "/api/state":
        return send("application/json", JSON.stringify(await state()));
      case "/api/layout": {
        // Each method keeps its own layouts, so switching back and forth in
        // the page does not lay out again; with no method, the default (METHODS[0]).
        const slot = (mode: string, method: Method) => `${mode} ${method}`;
        const known = (m: unknown): m is Method => METHODS.includes(m as Method);
        // GET /api/layout?mode=all&method=elk only reports; see Layouts.status.
        if (req.method === "GET") {
          const method = url.searchParams.get("method") ?? METHODS[0];
          if (!known(method)) return send("text/plain", `no layout method ${method}`, 400);
          return send("application/json", JSON.stringify(layouts.status(slot(url.searchParams.get("mode") ?? "all", method))));
        }
        const { mode, graph, method = METHODS[0] } = JSON.parse(await body(req)) as { mode: string; graph: Graph; method?: string };
        if (!known(method)) return send("text/plain", `no layout method ${method}`, 400);
        return send("application/json", JSON.stringify(layouts.request(slot(mode, method), { nodes: graph.nodes, edges: graph.edges, method })));
      }
      case "/api/log": {
        const id = url.searchParams.get("id") ?? "";
        const known = new Map(parsePlan(await text(join(repo, "docs/plan_dag.md"))).map((r) => [r.id.toLowerCase(), r.id]));
        const lines = parseLog(await text(join(work, "running-log.md"))).filter((e) => resolveId(e.id, known)?.id === id);
        return send("application/json", JSON.stringify(lines));
      }
      default:
        return send("text/plain", "not found", 404);
    }
  } catch (err) {
    return send("text/plain", String(err), 500);
  }
});

server.listen(port, "127.0.0.1", () => console.log(`http://127.0.0.1:${port}/`));
