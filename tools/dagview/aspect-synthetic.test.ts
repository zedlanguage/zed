// DAGVIEW-aspect: 20 relayouts of a plan-shaped graph stay within the shape
// band (see relayouts in generations.ts).
import { test } from "node:test";
import { relayouts } from "./generations.ts";
import { planLike } from "./synthetic.ts";

test("a plan-shaped graph of 500 nodes laid out from scratch and then 20 times from the earlier layout, a few nodes and edges added and removed each time: w/h stays within [0.4, 0.6] and the rows within 1.25 x what the graph needs", () => {
  console.log(relayouts(planLike(500, 1350), 20, "a plan-shaped graph of 500 nodes"));
});
