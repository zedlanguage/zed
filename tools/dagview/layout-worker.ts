// Runs one layout for layout.ts and posts the result back.

import { parentPort, workerData } from "node:worker_threads";
import { d3dagLayout } from "./d3dag.ts";
import { graphKey } from "./layout.ts";
import type { Graph } from "./layout.ts";

const { g, layers } = workerData as { g: Graph; layers?: Record<string, number> };
parentPort!.postMessage({ key: graphKey(g), ...d3dagLayout(g, undefined, layers) });
