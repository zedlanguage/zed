// DAGVIEW-aspect: 20 relayouts of a plan-shaped graph stay within the shape
// band (see chain in generations.ts), checked in pieces of five generations
// so that each test stays well under the time cap of 20 s.
import { test } from "node:test";
import { chain } from "./generations.ts";
import { planLike } from "./synthetic.ts";

const gens = chain(planLike(500, 1350), "a plan-shaped graph of 500 nodes");

test("a plan-shaped graph of 500 nodes laid out from scratch and then 5 times from the earlier layout, a few nodes and edges added and removed each time: w/h stays within [0.4, 0.6]", () => {
  gens.through(5);
});
for (const end of [10, 15, 20]) {
  test(`a plan-shaped graph of 500 nodes, generations ${end - 4} to ${end}: w/h stays within [0.4, 0.6]`, () => {
    gens.through(end);
  });
}
test("a plan-shaped graph of 500 nodes, generation 20 laid out from scratch: w/h stays within [0.4, 0.6] and the rows within 1.25 x what the graph needs", () => {
  console.log(gens.finish(20));
});
