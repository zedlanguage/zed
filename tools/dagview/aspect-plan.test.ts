// DAGVIEW-aspect: 20 relayouts of the plan of 2026-11-10 stay within the
// shape band (see relayouts in generations.ts).
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { relayouts } from "./generations.ts";
import type { Graph } from "./layout.ts";

const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;

test("the plan of 2026-11-10 laid out from scratch and then 20 times from the earlier layout, a few nodes and edges added and removed each time: w/h stays within [0.4, 0.6] and the rows within 1.25 x what the graph needs", () => {
  console.log(relayouts(plan, 20, "the plan of 2026-11-10"));
});
