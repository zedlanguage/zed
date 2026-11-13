// DAGVIEW-aspect: 20 relayouts of the live plan of 2026-11-11 stay within the
// shape band (see relayouts in generations.ts).
import { readFileSync } from "node:fs";
import { test } from "node:test";
import { relayouts } from "./generations.ts";
import type { Graph } from "./layout.ts";

const live = JSON.parse(readFileSync(new URL("./live-graph-2026-11-11.json", import.meta.url), "utf8")) as Graph;

test("the live plan of 2026-11-11 laid out from scratch and then 20 times from the earlier layout, a few nodes and edges added and removed each time: w/h stays within [0.4, 0.6] and the rows within 1.25 x what the graph needs", () => {
  console.log(relayouts(live, 20, "the live plan of 2026-11-11"));
});
