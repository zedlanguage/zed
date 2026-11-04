// Runs one ELK layout for layout.ts and posts the result back.

import { parentPort, workerData } from "node:worker_threads";
import ELK from "elkjs/lib/elk.bundled.js";
import { elkGraph, fromElk, graphKey } from "./layout.ts";
import type { Graph } from "./layout.ts";

const g = workerData as Graph;
const out = await new ELK().layout(elkGraph(g));
parentPort!.postMessage(fromElk(graphKey(g), out));
