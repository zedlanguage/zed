// Runs one ELK layout for layout.ts and posts the result back.

import { parentPort, workerData } from "node:worker_threads";
import ELK from "elkjs/lib/elk.bundled.js";
import { fromElk, graphKey, layoutTwice } from "./layout.ts";
import type { Graph } from "./layout.ts";

const g = workerData as Graph;
const out = await layoutTwice(new ELK(), g);
parentPort!.postMessage(fromElk(graphKey(g), out));
