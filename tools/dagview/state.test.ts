import assert from "node:assert/strict";
import { test } from "node:test";
import { buildGraph, buildNodes, directNeeds, ledgerCommits, overrideWarnings, parseLedger, parseQuestions, parseLog, parsePlan, resolveId, shortLabel } from "./state.ts";

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
    '{"id":"A","state":"fixed","commit":"c111111"}\n{"id":"LR2","state":"fixing"}\n{"id":"LR2","state":"fixed","commit":"c222222"}\n',
  )));
  assert.equal(nodes.get("A")!.state, "done");
  assert.equal(nodes.get("LR2")!.state, "done");
  assert.equal(nodes.get("B")!.state, "active");
  assert.equal(nodes.get("C")!.state, "unstarted");
  assert.equal(nodes.get("C")!.ready, false);
  assert.equal(by(buildNodes(inputs("", '{"id":"A","state":"fixed"}\n{"id":"LR2","state":"fixed"}\n'))).get("B")!.ready, true);
});

test("a merged commit not on origin is done but not pushed", () => {
  const n = by(buildNodes(inputs("", '{"id":"A","state":"fixed","commit":"c111111"}\n', () => false))).get("A")!;
  assert.equal(n.state, "done");
  assert.equal(n.pushed, false);
  assert.equal(n.awaitingBatch, true);
});

test("a done line after the batch test keeps the fixed line's commit, and git says pushed", () => {
  const led = '{"id":"A","state":"fixed","commit":"c111111","note":"awaiting batch test"}\n{"id":"A","state":"done","note":"pushed"}\n';
  const n = by(buildNodes(inputs("2026-11-02 10:00:00 | A:merge#1 | lock taken\n", led, (c) => c === "c111111"))).get("A")!;
  assert.equal(n.state, "done");
  assert.equal(n.pushed, true);
  assert.equal(n.note, "pushed");
  const behind = by(buildNodes(inputs("", led, () => false))).get("A")!;
  assert.equal(behind.awaitingBatch, true);
});

test("a ledger time in ISO form with a zone counts", () => {
  const led = '{"id":"A","state":"fixed","commit":"c111111","started":"2026-11-02T10:00:00Z"}\n';
  assert.equal(by(buildNodes(inputs("", led))).get("A")!.startedAt, Date.parse("2026-11-02T10:00:00Z"));
});

test("a repair after a fixed line makes the node active again", () => {
  const led = '{"id":"A","state":"fixed","commit":"c111111"}\n{"id":"A","state":"fixing"}\n';
  assert.equal(by(buildNodes(inputs("", led))).get("A")!.state, "active");
});

test("a done line from a repair or verify agent does not finish the node; a merge's does", () => {
  const rep = '{"id":"A","state":"done","by":"A:repair#2","commit":"c111111"}\n';
  assert.equal(by(buildNodes(inputs("", rep))).get("A")!.state, "active");
  const imp = '{"id":"A","status":"done","state":"fixed","agent":"A:impl#1"}\n';
  assert.equal(by(buildNodes(inputs("", imp))).get("A")!.state, "active");
  const mer = rep + '{"id":"A","state":"fixed","by":"A:merge#1","commit":"c222222"}\n';
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

test("the XV checks appear as parts of XE2, and an unplanned id with a ledger line gets a node", () => {
  const nodes = by(buildNodes(inputs(
    "2026-11-02 10:00:00 | XV-Q8:verify#1 | one\n2026-11-02 10:01:00 | XV-Q8:verify#1 | two\n2026-11-02 10:01:00 | XV-Q9:verify#1 | three\n",
    '{"id":"XE2","state":"fixing"}\n',
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

test("directNeeds ends on a cycle of needs", () => {
  const d = directNeeds([
    { id: "a", needs: ["b"] },
    { id: "b", needs: ["a"] },
    { id: "c", needs: ["a", "b"] },
  ]);
  assert.deepEqual(d.get("a"), ["b"]);
  assert.deepEqual(d.get("b"), ["a"]);
});

test("override needs and feeds connect an added item", () => {
  const inp = inputs("2026-11-02 10:00:00 | X:impl#1 | start\n", "");
  inp.overrides = { X: { needs: ["A"], feeds: ["C"] } };
  const nodes = by(buildNodes(inp));
  assert.deepEqual(nodes.get("X")!.needs, ["A"]);
  assert.deepEqual(nodes.get("C")!.needs, ["B", "A", "X"]);
  assert.equal(nodes.get("C")!.ready, false);
});

test("override needs add to the needs of the item's own ledger lines, and notNeeds removes one", () => {
  const inp = inputs("", '{"id":"X","state":"open","needs":["A","C"],"feeds":["B"]}\n');
  inp.overrides = { X: { needs: ["LR2"] } };
  assert.deepEqual(by(buildNodes(inp)).get("X")!.needs, ["LR2", "A", "C"]);
  inp.overrides = { X: { needs: ["LR2"], notNeeds: ["C"] } };
  const nodes = by(buildNodes(inp));
  assert.deepEqual(nodes.get("X")!.needs, ["LR2", "A"]);
  assert.ok(nodes.get("B")!.needs.includes("X"));
});

test("notNeeds removes a ledger feed into the item, but override needs do not", () => {
  const inp = inputs("", '{"id":"X","state":"open","feeds":["Y"]}\n{"id":"Y","state":"done"}\n');
  inp.overrides = { Y: { needs: [] }, W: { feeds: ["Y"] } };
  assert.ok(by(buildNodes(inp)).get("Y")!.needs.includes("X"));
  inp.overrides = { Y: { notNeeds: ["X"] }, W: { feeds: ["Y"] } };
  const g = buildGraph(inp);
  assert.deepEqual(by(g.nodes).get("Y")!.needs, ["W"]);
  assert.deepEqual(g.problems, []);
});

test("an item outside Zed draws no box, whether a plan row, the ledger or the log names it, and no edge names it", () => {
  const inp = inputs(
    "2026-11-02 10:00:00 | X:impl#1 | start\n2026-11-02 10:00:01 | V:impl#1 | start\n",
    '{"id":"X","state":"done","needs":["A"],"feeds":["C"]}\n{"id":"V","state":"done","feeds":["B"]}\n{"id":"LR2","state":"fixed","commit":"c1"}\n',
  );
  inp.overrides = { A: { outside: true }, X: { outside: true }, V: { outside: true, feeds: ["C"] } };
  const nodes = by(buildNodes(inp));
  assert.deepEqual([...nodes.keys()].sort(), ["B", "C", "LR2"]);
  assert.deepEqual(nodes.get("B")!.needs, ["LR2"]);
  assert.deepEqual(nodes.get("C")!.needs, ["B"]);
  assert.equal(nodes.get("B")!.ready, true);
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

test("an item the ledger lists as open stays unstarted though the log mentions it", () => {
  const log = "2026-11-02 10:00:01 | A:orchestrator | waits for B\n";
  const led = '{"id":"A","state":"open","needs":["B"]}\n';
  assert.equal(by(buildNodes(inputs(log, led))).get("A")!.state, "unstarted");
});

test("a waiting or deferred item is never ready, though everything it needs is done", () => {
  const met = '{"id":"A","state":"fixed"}\n{"id":"LR2","state":"fixed"}\n';
  for (const st of ["waiting", "deferred"]) {
    const b = by(buildNodes(inputs("2026-11-02 10:00:00 | B:impl#1 | start\n", met + `{"id":"B","state":"${st}"}\n`))).get("B")!;
    assert.equal(b.state, "waiting");
    assert.equal(b.ready, false);
  }
});

test("a waiting or blocked override is never ready", () => {
  for (const st of ["waiting", "blocked"] as const) {
    const inp = { ...inputs("", '{"id":"A","state":"fixed"}\n{"id":"LR2","state":"fixed"}\n'), overrides: { B: { state: st } } };
    const b = by(buildNodes(inp)).get("B")!;
    assert.equal(b.state, st);
    assert.equal(b.ready, false);
  }
});

test("a dropped item is no node, whether the ledger, an override or a plan row drops it, and a need on it counts as met", () => {
  const inp = inputs("", '{"id":"A","state":"dropped"}\n{"id":"X","state":"open","needs":["A"]}\n');
  const nodes = by(buildNodes(inp));
  assert.equal(nodes.has("A"), false);
  assert.deepEqual(nodes.get("B")!.needs, ["LR2"]);
  assert.deepEqual(nodes.get("X")!.needs, []);
  assert.equal(nodes.get("X")!.ready, true);
  inp.overrides = { LR2: { state: "dropped" } };
  assert.equal(by(buildNodes(inp)).has("LR2"), false);
  assert.equal(by(buildNodes(inp)).get("B")!.ready, true);
  inp.overrides = {};
  inp.plan = inp.plan.map((r) => (r.id === "LR2" ? { ...r, title: "Done: Dropped, moved into A" } : r));
  assert.deepEqual(by(buildNodes(inp)).get("B")!.needs, []);
  assert.equal(by(buildNodes(inp)).has("LR2"), false);
});

test("the questions table gives each held item its unanswered questions", () => {
  const md = `# Questions
| Q1 | Not this table | same |

## Which plan steps each question holds up

Text.

| Question | Steps held up | Rows an answer would add |
|---|---|---|
| A6 | ATOM-payload-sub |  |
| A2 | ORDER-keypath, and through it L6.11 |  |
| Q34 | L25.1, L30.1 to L30.3 |  |
| A31 | Nothing (CAST-menu-check is ready with option 2 in effect) |  |
| A36 | L10.3 and CHECKED-float (the cast's atom); S.1 counts 45 catalog rows as gaps until answered |  |
| Q51 | L33.2 (L7.15 under D) | PORT-process |
| Q41 | see Q11 |  |
| A46 | The rest of EMPTY-overlap-chain: the parts the fast path does not cover |  |
| A26 | XMARK-rows, ATOM-payload-sub |  |

## Q34: Which compiler hosts the language server

**Holds up.** L25.1.

### A26: Are the two rows right?

**Answer (author, 2026-11-06).** 1: keep both rows.

### A27: Next question
`;
  assert.deepEqual(Object.fromEntries(parseQuestions(md)), {
    "ATOM-payload-sub": ["A6"],
    "ORDER-keypath": ["A2"],
    "L25.1": ["Q34"],
    "L30.1": ["Q34"],
    "L30.2": ["Q34"],
    "L30.3": ["Q34"],
    "L10.3": ["A36"],
    "CHECKED-float": ["A36"],
    "L33.2": ["Q51"],
    "EMPTY-overlap-chain": ["A46"],
  });
});

test("an item an unanswered question holds, or whose ledger says blocked, is blocked; other waiting stays waiting", () => {
  const inp = inputs(
    "",
    '{"id":"A","state":"fixed","commit":"c111111"}\n{"id":"LR2","state":"waiting"}\n{"id":"B","state":"blocked"}\n{"id":"X","state":"waiting","note":"waits on QUESTIONS A6"}\n',
  );
  inp.held = new Map([["X", ["A6"]], ["A", ["A6"]], ["C", ["Q1"]]]);
  const nodes = by(buildNodes(inp));
  assert.equal(nodes.get("X")!.state, "blocked");
  assert.equal(nodes.get("C")!.state, "blocked");
  assert.equal(nodes.get("C")!.ready, false);
  assert.equal(nodes.get("B")!.state, "blocked");
  assert.equal(nodes.get("LR2")!.state, "waiting");
  assert.equal(nodes.get("A")!.state, "done");
});

test("merged is done, and verified, drafting, merging and a probe's done are active", () => {
  const st = (led: string) => by(buildNodes(inputs("", led))).get("A")!.state;
  assert.equal(st('{"id":"A","state":"merged","commit":"c111111"}\n'), "done");
  assert.equal(st('{"id":"A","state":"verified"}\n'), "active");
  assert.equal(st('{"id":"A","state":"drafting"}\n'), "active");
  assert.equal(st('{"id":"A","state":"merging"}\n'), "active");
  assert.equal(st('{"id":"A","state":"done","by":"A:probe#1"}\n'), "active");
  assert.equal(st('{"id":"A","state":"done","by":"orchestrator"}\n'), "done");
  assert.equal(st('{"id":"A","state":"done","by":"A:merge#1"}\n'), "done");
});

test("a note line, or a line with no state, keeps the state and gives the note", () => {
  const led = '{"id":"A","state":"fixed","commit":"c111111"}\n{"id":"A","state":"note","what":"checked by hand"}\n';
  const a = by(buildNodes(inputs("", led))).get("A")!;
  assert.equal(a.state, "done");
  assert.equal(a.note, "checked by hand");
  const bare = by(buildNodes(inputs("", '{"id":"A","state":"running"}\n{"id":"A","what":"half way"}\n'))).get("A")!;
  assert.equal(bare.state, "active");
  assert.equal(bare.note, "half way");
});

test("a line's commits list counts, and the node is pushed only when all of them are", () => {
  assert.deepEqual(ledgerCommits({ id: "A", state: "fixed", commit: "c111111", commits: ["c111111", "c222222"] }), ["c111111", "c222222"]);
  // The shapes agents have written in the ledger.
  assert.deepEqual(
    ledgerCommits({ id: "A", state: "fixed", commit: ["c333333", "zed:c444444"], commits: "c555555+c666666, report (zed)" }).sort(),
    ["c333333", "c444444", "c555555", "c666666"],
  );
  assert.deepEqual(ledgerCommits({ id: "A", state: "fixed", commit: { zed: "c777777", "zed-impl": "abcdef0" } }), ["c777777", "abcdef0"]);
  assert.deepEqual(ledgerCommits({ id: "A", state: "fixed", commit: null, commits: [1] }), []);
  const led = '{"id":"A","state":"fixed","commits":["c111111","c222222"]}\n';
  const all = by(buildNodes(inputs("", led, () => true))).get("A")!;
  assert.equal(all.pushed, true);
  const some = by(buildNodes(inputs("", led, (c) => c === "c111111"))).get("A")!;
  assert.equal(some.pushed, false);
  assert.equal(some.awaitingBatch, true);
});

test("an override written with status is named in the warnings", () => {
  const ov = { A: { state: "done" }, B: { status: "done" }, C: "not an object" } as unknown as Record<string, never>;
  assert.deepEqual(overrideWarnings(ov), ['override B uses "status", which is ignored; write "state"']);
});

test("a label naming several items with commas is a line of each, not an item of its own", () => {
  const [a, b] = parseLog("2026-11-04 00:14:14 | L2.3, PRE-stack | started: repair-runner\n");
  assert.deepEqual([a.id, b.id], ["L2.3", "PRE-stack"]);
  const [c, d] = parseLog("2026-11-04 00:14:15 | A, B:merge#1 | merged\n");
  assert.deepEqual([c.id, c.role, c.attempt, d.id, d.role], ["A", "merge", "1", "B", "merge"]);
  const nodes = by(buildNodes(inputs("2026-11-02 10:00:00 | A, LR2 | started\n", "")));
  assert.equal(nodes.has("A, LR2"), false);
  assert.equal(nodes.get("A")!.logLines, 1);
  assert.equal(nodes.get("LR2")!.logLines, 1);
});

test("ledger feeds into an item with override needs count, whatever the source's state", () => {
  const inp = inputs(
    "",
    '{"id":"X","state":"fixed","by":"X:merge#1","commit":"c111111","feeds":["Y"]}\n' +
      '{"id":"Z","state":"open","feeds":["Y"]}\n{"id":"Y","state":"open"}\n',
  );
  inp.overrides = { Y: { needs: ["A"] } };
  const g = buildGraph(inp);
  assert.deepEqual(by(g.nodes).get("Y")!.needs, ["A", "X", "Z"]);
  assert.deepEqual(g.problems, []);
});

test("a feed into an outside item goes to its replacedBy item, and without one is reported", () => {
  const inp = inputs("", '{"id":"X","state":"open","feeds":["O","P","C"]}\n{"id":"V","state":"done","feeds":["C","O"]}\n');
  inp.overrides = { O: { outside: true, replacedBy: "Q" }, Q: { outside: true, replacedBy: "LR2" }, P: { outside: true }, V: { outside: true } };
  const g = buildGraph(inp);
  assert.deepEqual(g.problems, ["FEED INTO OUTSIDE ITEM: X feeds P (give P a replacedBy override, or remove the feed)"]);
  const nodes = by(g.nodes);
  assert.deepEqual(nodes.get("LR2")!.needs, ["X"]);
  assert.ok(nodes.get("C")!.needs.includes("X"));
  inp.overrides.Q.replacedBy = "O";
  assert.deepEqual(buildGraph(inp).problems.length, 2);
});

test("notNeeds removes a plan row's need, and one that matches no edge is reported", () => {
  const inp = inputs("", '{"id":"X","state":"fixed","by":"orchestrator","feeds":["C"]}\n');
  inp.overrides = { C: { notNeeds: ["A", "LR2"] }, W: { feeds: ["C"] }, NONE: { notNeeds: ["A"] } };
  const g = buildGraph(inp);
  assert.deepEqual(by(g.nodes).get("C")!.needs, ["B", "W", "X"]);
  assert.deepEqual(g.problems, ["NOT-NEEDS MATCHES NO EDGE: C notNeeds LR2", "NOT-NEEDS MATCHES NO EDGE: NONE notNeeds A (NONE is no node)"]);
});

test("a ledger id with a colon or joined with + is a line of each item it names", () => {
  const g = buildGraph(inputs(
    "2026-11-02 10:00:00 | A+LR2:impl#1 | started\n",
    '{"id":"A:merge","state":"merged","commit":"c111111","needs":["A"]}\n' +
      '{"id":"A+LR2","state":"note","what":"merge label","feeds":["C"]}\n{"id":"B+Q","state":"note","feeds":["C"]}\n',
  ));
  const nodes = by(g.nodes);
  assert.deepEqual([...nodes.keys()].sort(), ["A", "B", "C", "LR2"]);
  assert.equal(nodes.get("A")!.state, "done");
  assert.deepEqual(nodes.get("A")!.needs, []);
  assert.deepEqual(nodes.get("C")!.needs, ["B", "A", "LR2"]);
  assert.equal(nodes.get("LR2")!.logLines, 1);
  assert.deepEqual(g.problems, ['LABEL WITH NO ITEM: Q (from "B+Q"; give it a ledger line or an override)']);
});

test("a log label alone makes no node, and one not written by the orchestrator is reported", () => {
  const g = buildGraph(inputs(
    "2026-11-02 10:00:00 | Q:orch | lock taken\n2026-11-02 10:00:01 | R | merged\n" +
      "2026-11-02 10:00:02 | S:orchestrator | status\n2026-11-02 10:00:03 | T:impl#1 | start\n",
    '{"id":"T","state":"fixing"}\n',
  ));
  const nodes = by(g.nodes);
  assert.deepEqual(["Q", "R", "S"].map((id) => nodes.has(id)), [false, false, false]);
  assert.equal(nodes.get("T")!.state, "active");
  assert.deepEqual(g.problems, [
    'LABEL WITH NO ITEM: Q (from "Q:orch"; give it a ledger line or an override)',
    'LABEL WITH NO ITEM: R (from "R"; give it a ledger line or an override)',
  ]);
});
