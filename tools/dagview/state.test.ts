import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { buildGraph, buildNodes, CommitList, lastLanding, ledgerCommits, parseLedger, parseQuestions, parseLog, parsePlan, resolveId, shapeProblems, shortLabel } from "./state.ts";

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

test("a backslash not before a bar stays in the title", () => {
  const rows = parsePlan(
    "## Items by level\n| 0 | D | at `f64 \\ \\| rat`, `&` and `\\`, `\\u{1B}` | S | no | none |  |\n",
  );
  assert.equal(rows[0].title, "at `f64 \\ | rat`, `&` and `\\`, `\\u{1B}`");
  assert.deepEqual([rows[0].size, rows[0].needs], ["S", []]);
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
  // An item whose own name ends in "-repair" keeps it: only a repair of a plan row is that row.
  assert.equal(resolveId("MSG-forwarded-repair", known)?.id, "MSG-forwarded-repair");
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

test("a done line from a repair or verify agent with a commit not on origin does not finish the node; a merge's does", () => {
  const rep = '{"id":"A","state":"done","by":"A:repair#2","commit":"c111111"}\n';
  assert.equal(by(buildNodes(inputs("", rep, () => false))).get("A")!.state, "active");
  const imp = '{"id":"A","status":"done","state":"fixed","agent":"A:impl#1"}\n';
  assert.equal(by(buildNodes(inputs("", imp))).get("A")!.state, "active");
  const mer = rep + '{"id":"A","state":"fixed","by":"A:merge#1","commit":"c222222"}\n';
  assert.equal(by(buildNodes(inputs("", mer))).get("A")!.state, "done");
});

test("an impl agent's fixed line finishes the node once all its commits are on origin", () => {
  const led = '{"id":"A","state":"fixed","by":"A:impl#1","commits":["c111111","zed:c222222"]}\n';
  const on = (set: string[]) => (c: string) => set.includes(c);
  assert.equal(by(buildNodes(inputs("", led, on(["c111111", "c222222"])))).get("A")!.state, "done");
  assert.equal(by(buildNodes(inputs("", led, on(["c111111"])))).get("A")!.state, "active");
  const bare = '{"id":"A","state":"fixed","by":"A:impl#1"}\n';
  assert.equal(by(buildNodes(inputs("", bare, () => true))).get("A")!.state, "active");
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

test("shapeProblems reports a need that another need implies", () => {
  const p = shapeProblems([
    { id: "a", needs: [] },
    { id: "b", needs: ["a"] },
    { id: "c", needs: ["a", "b"] },
  ]);
  assert.deepEqual(p, ["REDUNDANT NEED: c needs a, already implied through b; remove the edge"]);
});

test("shapeProblems is empty on a reduced graph", () => {
  assert.deepEqual(shapeProblems([{ id: "a", needs: [] }, { id: "b", needs: ["a"] }, { id: "c", needs: ["b"] }]), []);
});

test("shapeProblems on a shared chain visits each node once", () => {
  const nodes = Array.from({ length: 3000 }, (_, i) => ({
    id: `n${i}`,
    needs: i === 0 ? [] : i === 1 ? ["n0"] : [`n${i - 1}`, `n${i - 2}`],
  }));
  const p = shapeProblems(nodes);
  assert.equal(p.length, 2998);
  assert.ok(p.includes("REDUNDANT NEED: n2999 needs n2997, already implied through n2998; remove the edge"));
});

test("shapeProblems reports a cycle of needs and ends", () => {
  const p = shapeProblems([
    { id: "a", needs: ["b"] },
    { id: "b", needs: ["a"] },
    { id: "c", needs: ["a"] },
  ]);
  assert.ok(p.some((x) => x.startsWith("CYCLE OF NEEDS: ")), p.join("; "));
});

test("ledger needs and feeds connect an item with no plan row", () => {
  const inp = inputs("2026-11-02 10:00:00 | X:impl#1 | start\n", '{"id":"X","state":"note","needs":["A"],"feeds":["C"]}\n');
  const nodes = by(buildNodes(inp));
  assert.deepEqual(nodes.get("X")!.needs, ["A"]);
  assert.deepEqual(nodes.get("C")!.needs, ["B", "A", "X"]);
  assert.equal(nodes.get("C")!.ready, false);
});

test("the needs of an item's ledger lines add up", () => {
  const inp = inputs("", '{"id":"X","state":"open","needs":["A","C"],"feeds":["B"]}\n{"id":"X","state":"note","needs":["LR2"]}\n');
  const nodes = by(buildNodes(inp));
  assert.deepEqual(nodes.get("X")!.needs, ["A", "C", "LR2"]);
  assert.ok(nodes.get("B")!.needs.includes("X"));
});

test("a later line's unneeds and unfeeds take back an earlier line's edge, and a still later line gives it again", () => {
  const taken = inputs("", '{"id":"X","state":"open","needs":["A","LR2"],"feeds":["B","C"]}\n{"id":"X","state":"note","unneeds":["LR2"],"unfeeds":["C"]}\n');
  const nodes = by(buildNodes(taken));
  assert.deepEqual(nodes.get("X")!.needs, ["A"]);
  assert.ok(nodes.get("B")!.needs.includes("X"));
  assert.ok(!nodes.get("C")!.needs.includes("X"));
  const again = inputs("", '{"id":"X","state":"open","feeds":["C"]}\n{"id":"X","state":"note","unfeeds":["C"]}\n{"id":"X","state":"note","feeds":["C"]}\n');
  assert.ok(by(buildNodes(again)).get("C")!.needs.includes("X"));
});

test("an item outside Zed draws no box, whether a plan row, the ledger or the log names it, and no edge names it", () => {
  const inp = inputs(
    "2026-11-02 10:00:00 | X:impl#1 | start\n2026-11-02 10:00:01 | V:impl#1 | start\n",
    '{"id":"X","state":"done","needs":["A"],"feeds":["C"]}\n{"id":"V","state":"done","feeds":["B"]}\n{"id":"LR2","state":"fixed","commit":"c1"}\n' +
      '{"id":"A","state":"note","outside":true}\n{"id":"X","state":"note","outside":true}\n{"id":"V","state":"note","outside":true,"feeds":["C"]}\n',
  );
  const nodes = by(buildNodes(inp));
  assert.deepEqual([...nodes.keys()].sort(), ["B", "C", "LR2"]);
  assert.deepEqual(nodes.get("B")!.needs, ["LR2"]);
  assert.deepEqual(nodes.get("C")!.needs, ["B"]);
  assert.equal(nodes.get("B")!.ready, true);
  assert.deepEqual(buildGraph(inp).outside.sort(), ["A", "V", "X"]);
});

test("the last of an item's own ledger lines that says outside decides, and a label's line does not count", () => {
  const inp = inputs(
    "",
    '{"id":"X","state":"open","outside":true}\n{"id":"X","state":"open","outside":false}\n' +
      '{"id":"A:merge","state":"note","outside":true}\n{"id":"X","state":"note"}\n',
  );
  const nodes = by(buildNodes(inp));
  assert.ok(nodes.has("X"));
  assert.ok(nodes.has("A"));
  inp.ledger.push({ id: "X", state: "note", outside: true });
  assert.equal(by(buildNodes(inp)).has("X"), false);
});

test("a log label whose part after the colon is no role is one item, and a ledger line of that id names it", () => {
  const inp = inputs(
    "2026-11-02 10:00:00 | CD-xr:LAZY-hub | pushed\n2026-11-02 10:00:01 | A:merge#1 | merged\n",
    '{"id":"CD-xr:LAZY-hub","state":"note","outside":true}\n',
  );
  const g = buildGraph(inp);
  assert.equal(by(g.nodes).has("CD-xr"), false);
  assert.equal(by(g.nodes).has("CD-xr:LAZY-hub"), false);
  assert.deepEqual(g.problems, []);
  assert.deepEqual(g.outside, ["CD-xr:LAZY-hub"]);
});

test("an item with no plan row takes its title from its last ledger line that gives one", () => {
  const inp = inputs(
    "",
    '{"id":"X","state":"open","title":"Old"}\n{"id":"X","state":"note","title":"New"}\n{"id":"X","state":"note"}\n' +
      '{"id":"A","state":"note","title":"Not a plan title"}\n',
  );
  const nodes = by(buildNodes(inp));
  assert.equal(nodes.get("X")!.title, "New");
  assert.equal(nodes.get("A")!.title, "First item: with detail");
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

test("a ledger line carries edges too, and a bare string is one id", () => {
  const nodes = by(buildNodes(inputs(
    "",
    '{"id":"W","state":"open","needs":["B"],"feeds":["C"]}\n{"id":"V","state":"open","needs":"A","feeds":"C"}\n',
  )));
  assert.deepEqual(nodes.get("W")!.needs, ["B"]);
  assert.ok(nodes.get("C")!.needs.includes("W"));
  assert.ok(nodes.get("C")!.needs.includes("V"));
  assert.deepEqual(nodes.get("V")!.needs, ["A"]);
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

test("a plan row whose title starts with the word Done is done, whatever follows it and whatever the ledger says", () => {
  // DAGVIEW-done-rows-active: "Done (xr-cover1, 2026-11-18): ..." showed as active after a "started" line.
  const led = '{"id":"A","state":"started"}\n';
  for (const title of ["Done: x", "Done (xr-cover1, 2026-11-18): x", "Done by bundle-types7 (2026-11-17): x", "Done in 1ecadc5bf: x"]) {
    const inp = inputs("", led);
    inp.plan = inp.plan.map((r) => (r.id === "A" ? { ...r, title } : r));
    assert.equal(by(buildNodes(inp)).get("A")!.state, "done", title);
  }
  const inp = inputs("", led);
  inp.plan = inp.plan.map((r) => (r.id === "A" ? { ...r, title: "Doneness of the walk" } : r));
  assert.equal(by(buildNodes(inp)).get("A")!.state, "active");
});

test("a waiting or deferred item is never ready, though everything it needs is done", () => {
  const met = '{"id":"A","state":"fixed"}\n{"id":"LR2","state":"fixed"}\n';
  for (const st of ["waiting", "deferred"]) {
    const b = by(buildNodes(inputs("2026-11-02 10:00:00 | B:impl#1 | start\n", met + `{"id":"B","state":"${st}"}\n`))).get("B")!;
    assert.equal(b.state, "waiting");
    assert.equal(b.ready, false);
  }
});

test("a waiting or blocked ledger state is never ready", () => {
  for (const st of ["waiting", "blocked"] as const) {
    const b = by(buildNodes(inputs("", `{"id":"A","state":"fixed"}\n{"id":"LR2","state":"fixed"}\n{"id":"B","state":"${st}"}\n`))).get("B")!;
    assert.equal(b.state, st);
    assert.equal(b.ready, false);
  }
});

test("a dropped item is no node, whether the ledger or a plan row drops it, and a need on it counts as met", () => {
  const inp = inputs("", '{"id":"A","state":"dropped"}\n{"id":"X","state":"open","needs":["A"]}\n');
  const nodes = by(buildNodes(inp));
  assert.equal(nodes.has("A"), false);
  assert.deepEqual(nodes.get("B")!.needs, ["LR2"]);
  assert.deepEqual(nodes.get("X")!.needs, []);
  assert.equal(nodes.get("X")!.ready, true);
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

test("ledger feeds into an item with ledger needs count, whatever the source's state", () => {
  const inp = inputs(
    "",
    '{"id":"X","state":"fixed","by":"X:merge#1","commit":"c111111","feeds":["Y"]}\n' +
      '{"id":"Z","state":"open","feeds":["Y"]}\n{"id":"Y","state":"open","needs":["A"]}\n',
  );
  const g = buildGraph(inp);
  assert.deepEqual(by(g.nodes).get("Y")!.needs, ["A", "X", "Z"]);
  assert.deepEqual(g.problems, []);
});

test("a feed into an outside item goes to its replacedBy item, and without one is reported", () => {
  const inp = inputs(
    "",
    '{"id":"X","state":"open","feeds":["O","P","C"]}\n{"id":"V","state":"done","feeds":["C","O"]}\n' +
      '{"id":"O","state":"note","outside":true,"replacedBy":"Q"}\n{"id":"Q","state":"note","outside":true,"replacedBy":"LR2"}\n' +
      '{"id":"P","state":"note","outside":true}\n{"id":"V","state":"note","outside":true}\n',
  );
  const g = buildGraph(inp);
  assert.deepEqual(g.problems, ["FEED INTO OUTSIDE ITEM: X feeds P (give P a replacedBy in a ledger line of its own, or remove the feed)"]);
  const nodes = by(g.nodes);
  assert.deepEqual(nodes.get("LR2")!.needs, ["X"]);
  assert.ok(nodes.get("C")!.needs.includes("X"));
  // The last replacedBy decides; a loop of replacements is reported like a missing one.
  inp.ledger.push({ id: "Q", state: "note", replacedBy: "O" });
  assert.deepEqual(buildGraph(inp).problems.length, 2);
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
  assert.deepEqual(g.problems, ['LABEL WITH NO ITEM: Q (from "B+Q"; give it a ledger line)']);
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
    'LABEL WITH NO ITEM: Q (from "Q:orch"; give it a ledger line)',
    'LABEL WITH NO ITEM: R (from "R"; give it a ledger line)',
  ]);
});

test("a log label naming items with spaces is a line of each; a note in parentheses and, in a list, a word that starts with a small letter are no items (DAG-problem-report-cleanup)", () => {
  const ids = (label: string) => parseLog(`2026-11-04 00:14:14 | ${label} | started\n`).map((e) => e.id);
  assert.deepEqual(ids("PROOF-a PROOF-b PROOF-c:impl#1"), ["PROOF-a", "PROOF-b", "PROOF-c"]);
  assert.deepEqual(ids("PERF-a PREC-b"), ["PERF-a", "PREC-b"]);
  assert.deepEqual(ids("LOOP-boundary-spec merge"), ["LOOP-boundary-spec"]);
  assert.deepEqual(ids("ADDR-param-names agent"), ["ADDR-param-names"]);
  // "+3": the label's item and three more, which it does not name.
  assert.deepEqual(ids("FAIL-odd+3:scope-seeds:impl#1"), ["FAIL-odd"]);
  assert.deepEqual(ids("units-value-names (P237)"), ["units-value-names"]);
  assert.deepEqual(ids("PRES-a + KERNEL-b"), ["PRES-a", "KERNEL-b"]);
  assert.deepEqual(ids("plan"), ["plan"]);
});

test("a ledger id naming items with spaces is a line of each, not an item of its own (DAG-problem-report-cleanup)", () => {
  const g = buildGraph(inputs("", '{"id":"A LR2","state":"note","feeds":["C"]}\n{"id":"Done: B","state":"note","feeds":["C"]}\n'));
  const nodes = by(g.nodes);
  assert.deepEqual([...nodes.keys()].sort(), ["A", "B", "C", "LR2"]);
  assert.deepEqual(nodes.get("C")!.needs, ["B", "A", "LR2"]);
  assert.deepEqual(g.problems, []);
});

test("a log label that is an agent's name, as a ledger line's by, owner or agent field gives it, is not reported (DAG-problem-report-cleanup)", () => {
  const g = buildGraph(inputs(
    "2026-11-02 10:00:00 | kernel27:impl#1 | start\n2026-11-02 10:00:01 | walk-next | start\n" +
      "2026-11-02 10:00:02 | tools4 | start\n2026-11-02 10:00:03 | plan | landed\n2026-11-02 10:00:04 | BATCH | merged\n",
    '{"id":"A","state":"note","by":"kernel27:impl#1"}\n{"id":"A","state":"note","owner":"walk-next"}\n' +
      '{"id":"A","state":"note","agent":"tools4"}\n{"id":"A","state":"note","by":"BATCH"}\n',
  ));
  // An agent's name starts with a small letter; a by field such as BATCH or DAG-overrides-retire names an item.
  assert.deepEqual(g.problems, [
    'LABEL WITH NO ITEM: plan (from "plan"; give it a ledger line)',
    'LABEL WITH NO ITEM: BATCH (from "BATCH"; give it a ledger line)',
  ]);
});

test("a ledger line without an id is reported, not fatal", () => {
  const g = buildGraph(inputs("", '{"name":"A","state":"ready","time":"2026-11-02T10:00:00Z"}\n{"id":"A","state":"open"}\n'));
  assert.equal(by(g.nodes).get("A")!.state, "unstarted");
  assert.deepEqual(g.problems, ['LEDGER LINE WITH NO ID: {"name":"A","state":"ready","time":"2026-11-02T10:00:00Z"}']);
});

test("a ledger line with no id is read from its row field, which may name several ids split on commas and spaces (DECIDE-ledger-row-field-as-id)", () => {
  const g = buildGraph(inputs("",
    '{"row":"A","state":"blocked"}\n' +
      '{"row":"B LR2, C","state":"waiting"}\n' +
      // A line with an id is read from its id alone: its row does not move LR2.
      '{"id":"C","row":"LR2","state":"blocked"}\n' +
      '{"row":" ","state":"blocked"}\n' +
      '{"row":"NEW-item","state":"blocked","title":"An item only the ledger names"}\n',
  ));
  const nodes = by(g.nodes);
  assert.deepEqual(["A", "B", "LR2", "C", "NEW-item"].map((id) => nodes.get(id)?.state), ["blocked", "waiting", "waiting", "blocked", "blocked"]);
  assert.deepEqual(g.problems, ['LEDGER LINE WITH NO ID: {"row":" ","state":"blocked"}']);
});

test("a ledger line with no id or row is read from its item field, and not from a rows list (DECIDE-ledger-row-field-as-id)", () => {
  const g = buildGraph(inputs("",
    '{"item":"A","state":"blocked"}\n' +
      '{"item":"B LR2","state":"waiting"}\n' +
      // A row comes before an item.
      '{"row":"C","item":"LR2","state":"blocked"}\n' +
      // The only rows lists (2026-11-16) use the L40/L41 numbers from before 908b6b969 swapped them.
      '{"rows":["C"],"state":"waiting"}\n',
  ));
  const nodes = by(g.nodes);
  assert.deepEqual(["A", "B", "LR2", "C"].map((id) => nodes.get(id)?.state), ["blocked", "waiting", "waiting", "blocked"]);
  assert.deepEqual(g.problems, ['LEDGER LINE WITH NO ID: {"rows":["C"],"state":"waiting"}']);
});

test("with a fixture QUESTIONS.md, every plan row an open question holds is blocked, a sub-step id (L10.3b) holds its row, and a row held only by an answered question or by nothing is not", () => {
  const rows = `# Plan
## Items by level

| Level | Id | Title | Size | Hard | Needs | Paths |
|---|---|---|---|---|---|---|
| 0 | S.1d | Held by Q53 | S | no | none |  |
| 0 | L10.3 | Its step L10.3b held by Q53 | S | no | none |  |
| 0 | L33.2 | Held by Q51 | S | no | none |  |
| 0 | L7.4 | Held by A85 | S | no | none |  |
| 1 | L7.5 | Needs L7.4 | S | no | L7.4 |  |
| 0 | L20.1 | Held only by answered A80 | S | no | none |  |
| 0 | L21.1 | Held by nothing (A31) | S | no | none |  |
`;
  const md = readFileSync(new URL("./questions-fixture.md", import.meta.url), "utf8");
  const inp = { ...inputs("", ""), plan: parsePlan(rows), held: parseQuestions(md) };
  const nodes = by(buildNodes(inp));
  const blocked = [...nodes.values()].filter((n) => n.state === "blocked").map((n) => n.id).sort();
  assert.deepEqual(blocked, ["L10.3", "L33.2", "L7.4", "S.1d"]);
  assert.deepEqual(nodes.get("L10.3")!.questions, ["Q53"]);
  assert.deepEqual(nodes.get("L7.4")!.questions, ["A85"]);
  for (const id of ["L20.1", "L21.1"]) {
    assert.equal(nodes.get(id)!.state, "unstarted", id);
    assert.equal(nodes.get(id)!.ready, true, id);
  }
  // L7.5 waits through its need, not on a question.
  assert.equal(nodes.get("L7.5")!.state, "unstarted");
  assert.equal(nodes.get("L7.5")!.ready, false);
});

// DAGVIEW-held-digitless (AUDIT-p184): an id without a digit or a dash, such as the row FPWARN that
// Q53 holds, was never held, so the row showed unstarted; an all-capitals word holds the row of that
// id, and one the plan has no row for (DESIGN) holds nothing and makes no node.
test("an all-capitals word in the questions table holds the plan row of that id, and no other word does", () => {
  const rows = `# Plan
## Items by level

| Level | Id | Title | Size | Hard | Needs | Paths |
|---|---|---|---|---|---|---|
| 0 | FPWARN | The @fpwarn warning | S | no | none |  |
| 0 | DESIGNX | Not named | S | no | none |  |
`;
  const md = `## Which plan steps each question holds up

| Question | Steps held up | Rows an answer would add |
|---|---|---|
| Q53 | FPWARN (parts 4 to 6), the DESIGN text, Fpwarn |  |
`;
  const inp = { ...inputs("", ""), plan: parsePlan(rows), held: parseQuestions(md) };
  const nodes = by(buildNodes(inp));
  assert.equal(nodes.get("FPWARN")!.state, "blocked");
  assert.deepEqual(nodes.get("FPWARN")!.questions, ["Q53"]);
  assert.equal(nodes.get("DESIGNX")!.state, "unstarted");
  assert.deepEqual([...nodes.keys()].sort(), ["DESIGNX", "FPWARN"]);
});

test("the commit list finds a commit by any prefix of 7 or more hex digits, and nothing else", () => {
  const l = new CommitList();
  const a = "8646a2b0c1d2e3f4a5b6c7d8e9f0a1b2c3d4e5f6", b = "8646a2c000000000000000000000000000000000", c = "ffff000011112222333344445555666677778888";
  l.reset([b, a, ""], "t1");
  assert.equal(l.size, 2);
  assert.equal(l.has("8646a2b"), true);
  assert.equal(l.has("8646a2c0"), true);
  assert.equal(l.has(a), true);
  // A prefix of a commit not in the list, and words that are not hashes.
  assert.equal(l.has("8646a2d"), false);
  assert.equal(l.has("ffff000"), false);
  assert.equal(l.has("8646a2"), false);
  assert.equal(l.has("8646A2B"), false);
  assert.equal(l.has("zzzzzzz"), false);
  // An add after the tip moved merges the new commits in, each kept once.
  l.add([c, a + "\n"], "t2");
  assert.equal(l.size, 3);
  assert.equal(l.tip, "t2");
  assert.equal(l.has("ffff000"), true);
  // A reset after a forced push forgets the old commits.
  l.reset([c], "t3");
  assert.equal(l.size, 1);
  assert.equal(l.has("8646a2b"), false);
  assert.equal(l.has("ffff0000111"), true);
});

test("the commit list agrees with a scan on random hashes", () => {
  // SHA-1 of the index: distinct, well-mixed hashes.
  const hex = (_: unknown, i: number) => createHash("sha1").update(String(i)).digest("hex");
  const all = Array.from({ length: 2000 }, hex);
  const l = new CommitList();
  l.reset(all.slice(0, 1000), "a");
  l.add(all.slice(900, 1500), "b");
  const on = new Set(all.slice(0, 1500));
  assert.equal(l.size, 1500);
  for (const h of all) for (const k of [7, 12, 40]) assert.equal(l.has(h.slice(0, k)), [...on].some((o) => o.startsWith(h.slice(0, k))), h.slice(0, k));
});

test("an agent's unsolved or todo line leaves the node unstarted; ready leaves it waiting", () => {
  const log = "2026-11-12 10:00:00 | A:impl#1 | round 1 started\n";
  const st = (state: string) => by(buildNodes(inputs(log, `{"id":"A","state":"${state}","by":"CD-xr:A"}\n`))).get("A")!.state;
  assert.equal(st("unsolved"), "unstarted");
  assert.equal(st("todo"), "unstarted");
  assert.equal(st("ready"), "waiting");
  assert.equal(st("running"), "active");
});

test("the last landing is the last whole line of landings.log", () => {
  const a = "14a171065f0ec812f8b6b07449b5a0e9758c0fd2 2026-11-26T22:55:28Z /home/luke/Work/wt/trees/pith-rows wt/pith-rows";
  const b = "a1c20cb6845fbc0a2478955d723e3069faab53fe 2026-11-27T00:33:41Z /home/luke/Work/wt/trees/b22-scale1-b29-l2 wt/b22-scale1-b29-l2";
  assert.equal(lastLanding(`${a}\n${b}\n`), "a1c20cb68 2026-11-27T00:33:41Z wt/b22-scale1-b29-l2");
  // The read starts part way through a line, and the last line is an append still being written.
  assert.equal(lastLanding(`9758c0fd2 2026-11-26T22:55:28Z /x wt/y\n${a}\n${b.slice(0, 50)}`), "14a171065 2026-11-26T22:55:28Z wt/pith-rows");
  assert.equal(lastLanding(""), "");
  assert.equal(lastLanding("short 2026-11-26T22:55:28Z /x wt/y\n"), "");
});
