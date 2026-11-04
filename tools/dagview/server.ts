// Serves the live plan view on http://127.0.0.1:4317 (PORT overrides the port).
// Run with `node server.ts`. Node strips the types; nothing is compiled.
//
// Reads, on each poll: docs/plan_dag.md, wt/running-log.md, wt/ledger.jsonl,
// wt/dag-overrides.json, wt/merge.lock/owner, /proc/loadavg and git. Lays the
// plan out when the page posts its graph to /api/layout (see layout.ts).

import { execFile } from "node:child_process";
import { readFile, writeFile } from "node:fs/promises";
import { createServer } from "node:http";
import type { IncomingMessage } from "node:http";
import { stripTypeScriptTypes } from "node:module";
import { join, resolve } from "node:path";
import { promisify } from "node:util";
import { buildNodes, directNeeds, ledgerCommits, overrideWarnings, parseLedger, parseLog, parsePlan, resolveId } from "./state.ts";
import type { Override } from "./state.ts";
import { Layouts, layoutInWorker } from "./layout.ts";
import type { Graph } from "./layout.ts";

const here = import.meta.dirname;
const repo = process.env.DAGVIEW_REPO ?? resolve(here, "../..");
const work = process.env.DAGVIEW_WT ?? resolve(repo, "../wt");
// Ledger lines also name commits of the spec repository.
const spec = process.env.DAGVIEW_SPEC ?? resolve(repo, "../zed");
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
  const [plan, logText, ledgerText, overridesText, lock, loadavg, origin, main, ahead] = await Promise.all([
    text(join(repo, "docs/plan_dag.md")),
    text(join(work, "running-log.md")),
    text(join(work, "ledger.jsonl")),
    text(join(work, "dag-overrides.json")),
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
  const nodes = buildNodes({
    plan: parsePlan(plan),
    log,
    ledger,
    overrides,
    onOrigin: (c) => onOriginMemo.has(c),
    now,
  });
  const direct = directNeeds(nodes);
  return {
    now,
    nodes,
    direct: Object.fromEntries(direct),
    log: log.slice(-60).reverse(),
    warnings: overrideWarnings(overrides),
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

const savedLayouts = join(work, "dagview-layouts.json");
const layouts = new Layouts(
  layoutInWorker,
  JSON.parse(await readFile(savedLayouts, "utf8").catch(() => "{}")),
  (done) => void writeFile(savedLayouts, JSON.stringify(done)).catch((err) => console.error(`saving layouts failed:`, err)),
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
      case "/api/state":
        return send("application/json", JSON.stringify(await state()));
      case "/api/layout": {
        const { mode, graph } = JSON.parse(await body(req)) as { mode: string; graph: Graph };
        return send("application/json", JSON.stringify(layouts.request(mode, graph)));
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
