// DAGVIEW-aspect: 20 relayouts of the plan of 2026-11-10 stay within the
// shape band (see chain in generations.ts), checked in pieces of two
// generations so that each test stays well under the time cap of 20 s.
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { chain } from "./generations.ts";
import type { Graph } from "./layout.ts";

const plan = JSON.parse(readFileSync(new URL("./plan-graph-2026-11-10.json", import.meta.url), "utf8")) as Graph;
const gens = chain(plan, "the plan of 2026-11-10");

test("the plan of 2026-11-10 laid out from scratch: w/h stays within [0.4, 0.6]", () => {
  gens.through(0);
});
for (const end of [2, 4, 6, 8, 10, 12, 14, 16, 18, 20]) {
  test(`the plan of 2026-11-10, generations ${end - 1} and ${end}, each laid out from the earlier layout with a few nodes and edges added and removed: w/h stays within [0.4, 0.6]`, () => {
    gens.through(end);
  });
}
test("the plan of 2026-11-10, generation 20 laid out from scratch: w/h stays within [0.4, 0.6] and the rows within 1.25 x what the graph needs", () => {
  console.log(gens.finish(20));
});
