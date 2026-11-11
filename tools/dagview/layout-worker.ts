// Runs one layout for layout.ts and posts the result back.

import { parentPort, workerData } from "node:worker_threads";
import { d3dagLayout } from "./d3dag.ts";
import { graphKey } from "./layout.ts";
import type { Graph, Layout } from "./layout.ts";

const { g, layers, at, edges, rowLimit } = workerData as { g: Graph; layers?: Record<string, number>; at?: Record<string, { x: number; y: number }>; edges?: Layout["edges"]; rowLimit?: number };
parentPort!.postMessage({ key: graphKey(g), ...d3dagLayout(g, undefined, layers, at, edges, rowLimit) });
