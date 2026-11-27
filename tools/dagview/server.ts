// Serves the live plan view on http://127.0.0.1:4317 (PORT overrides the port).
// Run with `node server.ts`. Node strips the types; nothing is compiled.
//
// Reads, on each request for the state: docs/plan_dag.md, wt/running-log.md,
// wt/ledger.jsonl, the author's open questions in
// wt/zed0-review/pass2/QUESTIONS.md, the end of wt/landings.log, /proc/loadavg and git
// (five small commands, and one rev-list of new commits when origin/main moves). Lays the plan out when the page posts its graph to /api/layout (see
// layout.ts). It watches those files and the main and origin/main refs, and
// tells the page over /api/events when one changes or a layout finishes, so an
// idle page and server do no work.

import { execFile } from "node:child_process";
import { watch } from "node:fs";
import { open, readFile, writeFile } from "node:fs/promises";
import { createServer } from "node:http";
import type { IncomingMessage, ServerResponse } from "node:http";
import { stripTypeScriptTypes } from "node:module";
import { basename, dirname, join, resolve } from "node:path";
import { promisify } from "node:util";
import { buildGraph, CommitList, lastLanding, shapeProblems, parseLedger, parseLog, parsePlan, parseQuestions, resolveId } from "./state.ts";
import { Layouts, layoutInWorker } from "./layout.ts";
import type { Graph } from "./layout.ts";

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

// The last `bytes` bytes of a file that only grows by appends (landings.log, 83 kB on 2026-11-27
// and one line a landing), so a request for the state reads O(1) of it, not the whole history.
async function tailText(path: string, bytes: number): Promise<string> {
  let f;
  try {
    f = await open(path, "r");
    const { size } = await f.stat();
    const start = Math.max(0, size - bytes);
    const buf = Buffer.alloc(size - start);
    const { bytesRead } = await f.read(buf, 0, buf.length, start);
    return buf.subarray(0, bytesRead).toString("utf8");
  } catch {
    return "";
  } finally {
    await f?.close();
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

// The commits on origin/main of each repository (see CommitList). When the
// tip moves forward only the commits since the old tip are listed; a tip
// that does not descend from the old one (a forced push) lists them all.
// Updates run one at a time, so two requests never list the same range twice.
const onOrigin = new Map([repo, spec].map((dir) => [dir, new CommitList()]));
let originUpdate: Promise<void> = Promise.resolve();

function updateOrigin(): Promise<void> {
  originUpdate = originUpdate.then(() =>
    Promise.all(
      [...onOrigin].map(async ([dir, list]) => {
        const tip = await gitIn(dir, "rev-parse", "origin/main");
        if (tip === null || tip === list.tip) return;
        const forward = list.tip !== "" && (await gitIn(dir, "merge-base", "--is-ancestor", list.tip, tip)) !== null;
        try {
          const { stdout } = await run("git", ["-C", dir, "rev-list", forward ? `${list.tip}..${tip}` : tip], { maxBuffer: 1 << 28 });
          const hashes = stdout.split("\n");
          if (forward) list.add(hashes, tip);
          else list.reset(hashes, tip);
        } catch (err) {
          console.error(`listing origin/main in ${dir} failed:`, err);
        }
      }),
    ).then(() => {}),
  );
  return originUpdate;
}

async function state() {
  const [plan, logText, ledgerText, questionsText, landings, loadavg, origin, main, ahead] = await Promise.all([
    text(join(repo, "docs/plan_dag.md")),
    text(join(work, "running-log.md")),
    text(join(work, "ledger.jsonl")),
    text(questions),
    // A landing line is about 120 bytes; 4 kB holds the last thirty.
    tailText(join(work, "landings.log"), 4096),
    text("/proc/loadavg"),
    git("rev-parse", "--short", "origin/main"),
    git("rev-parse", "--short", "main"),
    git("rev-list", "--count", "origin/main..main"),
  ]);
  const log = parseLog(logText);
  const ledger = parseLedger(ledgerText);
  await updateOrigin();
  const now = Date.now();
  const { nodes, problems, dropped, outside } = buildGraph({
    plan: parsePlan(plan),
    log,
    ledger,
    onOrigin: (c) => [...onOrigin.values()].some((l) => l.has(c)),
    now,
    held: parseQuestions(questionsText),
  });
  return {
    now,
    nodes,
    log: log.slice(-60).reverse(),
    problems: [...problems, ...shapeProblems(nodes)],
    dropped,
    outside,
    machine: {
      load: loadavg.split(" ").slice(0, 3).join(" "),
      landing: lastLanding(landings),
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
watchNames(work, ["running-log.md", "ledger.jsonl", "landings.log"]);
watchNames(dirname(questions), [basename(questions)]);
for (const dir of [repo, spec]) {
  watchNames(join(dir, ".git"), ["packed-refs"]);
  watchNames(join(dir, ".git/refs/heads"), ["main"]);
  watchNames(join(dir, ".git/refs/remotes/origin"), ["main"]);
}

const savedLayouts = join(work, "dagview-layouts.json");
// Each layout run is logged, so the log shows how often and for which graph one runs.
const layouts = new Layouts(
  async (g, prev) => {
    const t0 = Date.now();
    console.log(`${new Date(t0).toISOString()} layout started: ${g.nodes.length} nodes, ${g.edges.length} edges`);
    const l = await layoutInWorker(g, prev);
    console.log(`${new Date().toISOString()} layout finished in ${Date.now() - t0} ms: ${l.key}`);
    return l;
  },
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
        // GET /api/layout?mode=all only reports; see Layouts.status.
        if (req.method === "GET") return send("application/json", JSON.stringify(layouts.status(url.searchParams.get("mode") ?? "all")));
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
