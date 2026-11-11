// Runs one layout for layout.ts, by the graph's method, and posts the result back.

import { parentPort, workerData } from "node:worker_threads";
import ELK from "elkjs/lib/elk.bundled.js";
import { d3dagLayout } from "./d3dag.ts";
import { fromElk, graphKey, layoutTwice } from "./layout.ts";
import type { Graph } from "./layout.ts";

const g = workerData as Graph;
const key = graphKey(g);
const l = g.method === "elk" ? fromElk(key, await layoutTwice(new ELK(), g)) : { key, ...d3dagLayout(g) };
parentPort!.postMessage(l);
