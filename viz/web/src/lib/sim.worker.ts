// Runs the simulator (WebAssembly) off the main thread.
import init, { trace } from '../../../wasm/pkg/mncore_viz_wasm.js';

const ready = init();

export interface TraceRequest {
  id: number;
  testcase: string;
  solution: string;
  focusPe: number;
}

self.onmessage = async (ev: MessageEvent<TraceRequest>) => {
  const { id, testcase, solution, focusPe } = ev.data;
  try {
    await ready;
    const json = trace(testcase, solution, focusPe);
    self.postMessage({ id, json });
  } catch (e) {
    self.postMessage({ id, error: String(e) });
  }
};
