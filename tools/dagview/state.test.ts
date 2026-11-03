import assert from "node:assert/strict";
import { test } from "node:test";
import { buildNodes, directNeeds, parseLedger, parseLog, parsePlan, resolveId, shortLabel } from "./state.ts";

const plan = `# Plan
## Items by level

| Level | Id | Title | Size | Hard | Needs | Paths |
|---|---|---|---|---|---|---|
| 0 | A | First item: with detail | S | no | none | \`a.rs\` |
| 0 | LR2 | Second | M | yes | none |  |
| 1 | B | A pipe in code, O(|Ty|), and \\| escaped | L | no | A, LR2 | \`b.rs\` |
| 2 | C | Third | M | no | B, A |  |

## Next
| 9 | Z | Not an item | S | no | none |  |
`;

test("plan rows keep their columns when a title holds a pipe", () => {
  const rows = parsePlan(plan);
  assert.deepEqual(rows.map((r) => r.id), ["A", "LR2", "B", "C"]);
  assert.equal(rows[2].title, "A pipe in code, O(|Ty|), and | escaped");
  assert.deepEqual(rows[2].needs, ["A", "LR2"]);
  assert.equal(rows[1].hard, true);
});

test("log lines split into item, role and attempt, and text may hold a bar", () => {
  const [a, b, c] = parseLog(
    "2026-11-02 10:00:00 | A:repair#2 | one | two\n" +
      "2026-11-02 10:00:01 | orchestrator | started\nnot a log line\n" +
      "2026-11-02 10:00:02 | DART-RS:verify#x | ok=false\n",
  );
  assert.deepEqual([a.id, a.role, a.attempt, a.text], ["A", "repair", "2", "one | two"]);
  assert.equal(b.role, "");
  assert.equal(c.attempt, "x");
});

test("a half-written ledger line is skipped", () => {
  assert.equal(parseLedger('{"id":"A","state":"fixed"}\n{"id":"B","sta').length, 1);
});

test("aliases reach the plan's ids", () => {
  const known = new Map([["lr2", "LR2"], ["t2-eval", "T2-eval"]]);
  assert.equal(resolveId("lr2", known)?.id, "LR2");
  assert.equal(resolveId("T2-eval-repair", known)?.id, "T2-eval");
  assert.deepEqual(resolveId("XV-Q8", known), { id: "XE2", sub: "Q8" });
  assert.equal(resolveId("orchestrator", known), null);
});

test("short labels stop at a clause and at a word", () => {
  assert.equal(shortLabel("Done: tests no longer fail"), "tests no longer fail");
  assert.equal(shortLabel("First item: with detail"), "First item");
  assert.equal(shortLabel("S18: Omega loop"), "S18: Omega loop");
  assert.ok(shortLabel("word ".repeat(30)).endsWith("…"));
  assert.ok(shortLabel("word ".repeat(30)).length <= 37);
});

const inputs = (log: string, ledger: string, onOrigin = (_: string) => true) => ({
  plan: parsePlan(plan),
  log: parseLog(log),
  ledger: parseLedger(ledger),
  overrides: {},
  onOrigin,
  now: Date.parse("2026-11-02T11:00:00"),
});
const by = (nodes: ReturnType<typeof buildNodes>) => new Map(nodes.map((n) => [n.id, n]));

test("states follow the ledger, then the log, and readiness follows needs", () => {
  const nodes = by(buildNodes(inputs(
    "2026-11-02 10:00:00 | B:impl#1 | start\n",
    '{"id":"A","state":"fixed","commit":"c1"}\n{"id":"LR2","state":"fixing"}\n{"id":"LR2","state":"fixed","commit":"c2"}\n',
  )));
  assert.equal(nodes.get("A")!.state, "done");
  assert.equal(nodes.get("LR2")!.state, "done");
  assert.equal(nodes.get("B")!.state, "active");
  assert.equal(nodes.get("C")!.state, "unstarted");
  assert.equal(nodes.get("C")!.ready, false);
  assert.equal(by(buildNodes(inputs("", '{"id":"A","state":"fixed"}\n{"id":"LR2","state":"fixed"}\n'))).get("B")!.ready, true);
});

test("a merged commit not on origin is done but not pushed", () => {
  const n = by(buildNodes(inputs("", '{"id":"A","state":"fixed","commit":"c1"}\n', () => false))).get("A")!;
  assert.equal(n.state, "done");
  assert.equal(n.pushed, false);
  assert.equal(n.awaitingBatch, true);
});

test("a done line after the batch test keeps the fixed line's commit, and git says pushed", () => {
  const led = '{"id":"A","state":"fixed","commit":"c1","note":"awaiting batch test"}\n{"id":"A","state":"done","note":"pushed"}\n';
  const n = by(buildNodes(inputs("2026-11-02 10:00:00 | A:merge#1 | lock taken\n", led, (c) => c === "c1"))).get("A")!;
  assert.equal(n.state, "done");
  assert.equal(n.pushed, true);
  assert.equal(n.note, "pushed");
  const behind = by(buildNodes(inputs("", led, () => false))).get("A")!;
  assert.equal(behind.awaitingBatch, true);
});

test("a ledger time in ISO form with a zone counts", () => {
  const led = '{"id":"A","state":"fixed","commit":"c1","started":"2026-11-02T10:00:00Z"}\n';
  assert.equal(by(buildNodes(inputs("", led))).get("A")!.startedAt, Date.parse("2026-11-02T10:00:00Z"));
});

test("a repair after a fixed line makes the node active again", () => {
  const led = '{"id":"A","state":"fixed","commit":"c1"}\n{"id":"A","state":"fixing"}\n';
  assert.equal(by(buildNodes(inputs("", led))).get("A")!.state, "active");
});

test("a done line from a repair or verify agent does not finish the node; a merge's does", () => {
  const rep = '{"id":"A","state":"done","by":"A:repair#2","commit":"c1"}\n';
  assert.equal(by(buildNodes(inputs("", rep))).get("A")!.state, "active");
  const imp = '{"id":"A","status":"done","state":"fixed","agent":"A:impl#1"}\n';
  assert.equal(by(buildNodes(inputs("", imp))).get("A")!.state, "active");
  const mer = rep + '{"id":"A","state":"fixed","by":"A:merge#1","commit":"c2"}\n';
  assert.equal(by(buildNodes(inputs("", mer))).get("A")!.state, "done");
});

test("retries, rejections, runtime and last tests come from the log", () => {
  const n = by(buildNodes(inputs(
    "2026-11-02 10:00:00 | A:impl#1 | start\n" +
      "2026-11-02 10:10:00 | A:verify#1 | NOT accepted\n" +
      "2026-11-02 10:20:00 | A:repair#2 | run_tests: 91 pieces, 0 failed\n" +
      "2026-11-02 10:30:00 | A:repair#3 | start\n",
    "",
  ))).get("A")!;
  assert.equal(n.retries, 2);
  assert.equal(n.rejections, 1);
  assert.equal(n.runtimeMs, 3600_000);
  assert.equal(n.lastTests, "91 pieces, 0 failed");
  assert.equal(n.role, "repair");
});

test("the XV checks appear as parts of XE2, and unplanned ids get a node", () => {
  const nodes = by(buildNodes(inputs(
    "2026-11-02 10:00:00 | XV-Q8:verify#1 | one\n2026-11-02 10:01:00 | XV-Q8:verify#1 | two\n2026-11-02 10:01:00 | XV-Q9:verify#1 | three\n",
    "",
  )));
  const x = nodes.get("XE2")!;
  assert.equal(x.planned, false);
  assert.deepEqual(x.subs.map((s) => [s.name, s.text]), [["Q8", "two"], ["Q9", "three"]]);
});

test("an override wins over the log", () => {
  const inp = { ...inputs("2026-11-02 10:00:00 | A:impl#1 | start\n", ""), overrides: { A: { state: "done" as const } } };
  assert.equal(by(buildNodes(inp)).get("A")!.state, "done");
});

test("directNeeds drops a need that another need implies", () => {
  const d = directNeeds(parsePlan(plan));
  assert.deepEqual(d.get("C"), ["B"]);
  assert.deepEqual(d.get("B"), ["A", "LR2"]);
});

test("directNeeds on a shared chain visits each node once", () => {
  const nodes = Array.from({ length: 3000 }, (_, i) => ({
    id: `n${i}`,
    needs: i === 0 ? [] : i === 1 ? ["n0"] : [`n${i - 1}`, `n${i - 2}`],
  }));
  assert.deepEqual(directNeeds(nodes).get("n2999"), ["n2998"]);
});

test("override needs and feeds connect an added item", () => {
  const inp = inputs("2026-11-02 10:00:00 | X:impl#1 | start\n", "");
  inp.overrides = { X: { needs: ["A"], feeds: ["C"] } };
  const nodes = by(buildNodes(inp));
  assert.deepEqual(nodes.get("X")!.needs, ["A"]);
  assert.deepEqual(nodes.get("C")!.needs, ["B", "A", "X"]);
  assert.equal(nodes.get("C")!.ready, false);
});

test("a label with no attempt is a line of its item, and bookkeeping draws no box", () => {
  const [a, b] = parseLog(
    "2026-11-02 10:00:00 | B:code-sweep | finder done\n2026-11-02 10:00:01 | T14-cell-len:merge (orchestrator) | merged\n",
  );
  assert.deepEqual([a.id, a.role, a.attempt], ["B", "code-sweep", ""]);
  assert.deepEqual([b.id, b.role], ["T14-cell-len", "merge (orchestrator)"]);
  const nodes = by(buildNodes(inputs(
    "2026-11-02 10:00:00 | B:orchestrator | lock taken\n2026-11-02 10:00:01 | STATUS:orchestrator | lock taken\n" +
      "2026-11-02 10:00:02 | Y:orchestrator | started\n",
    '{"id":"Y","state":"fixing"}\n',
  )));
  assert.equal(nodes.get("B")!.logLines, 1);
  assert.equal(nodes.has("STATUS"), false);
  assert.equal(nodes.has("B:orchestrator"), false);
  assert.equal(nodes.get("Y")!.state, "active");
});

test("a ledger line carries edges too, and a bare string is not a list", () => {
  const nodes = by(buildNodes(inputs(
    "",
    '{"id":"W","state":"open","needs":["B"],"feeds":["C"]}\n{"id":"V","state":"open","needs":"A","feeds":"C"}\n',
  )));
  assert.deepEqual(nodes.get("W")!.needs, ["B"]);
  assert.deepEqual(nodes.get("C")!.needs, ["B", "A", "W"]);
  assert.deepEqual(nodes.get("V")!.needs, []);
});

test("a ledger line's own time counts toward the runtime", () => {
  const led =
    '{"id":"A","state":"running","at":"2026-11-02T10:00:00Z"}\n' +
    '{"id":"A","state":"fixing","ts":"2026-11-02T11:00:00Z"}\n';
  const a = by(buildNodes(inputs("", led))).get("A")!;
  assert.equal(a.startedAt, Date.parse("2026-11-02T10:00:00Z"));
  assert.equal(a.lastAt, Date.parse("2026-11-02T11:00:00Z"));
});
