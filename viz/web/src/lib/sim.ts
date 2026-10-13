// Main-thread client of the simulator worker.
import type { Trace, ProblemEntry } from './types';

const worker = new Worker(new URL('./sim.worker.ts', import.meta.url), { type: 'module' });
let nextId = 1;
const pending = new Map<number, { resolve: (t: Trace) => void; reject: (e: Error) => void }>();

worker.onmessage = (ev: MessageEvent<{ id: number; json?: string; error?: string }>) => {
  const p = pending.get(ev.data.id);
  if (!p) return;
  pending.delete(ev.data.id);
  if (ev.data.error !== undefined) p.reject(new Error(ev.data.error));
  else p.resolve(JSON.parse(ev.data.json!) as Trace);
};

/** Simulates `solution` inside `testcase`, recording the MAB that contains `focusPe`. */
export function runTrace(testcase: string, solution: string, focusPe: number): Promise<Trace> {
  const id = nextId++;
  return new Promise((resolve, reject) => {
    pending.set(id, { resolve, reject });
    worker.postMessage({ id, testcase, solution, focusPe });
  });
}

const base = import.meta.env.BASE_URL;

export async function loadIndex(): Promise<ProblemEntry[]> {
  const r = await fetch(`${base}problems/index.json`);
  if (!r.ok) throw new Error('problems/index.json not found: run `npm run sync-problems`');
  return r.json();
}

export async function loadProblem(name: string): Promise<{ testcase: string; solution: string; statement: string }> {
  const get = async (f: string) => {
    const r = await fetch(`${base}problems/${name}/${f}`);
    return r.ok ? r.text() : '';
  };
  const [testcase, solution, statement] = await Promise.all([get('testcase.vsm'), get('main.vsm'), get('problem.md')]);
  return { testcase, solution, statement };
}
