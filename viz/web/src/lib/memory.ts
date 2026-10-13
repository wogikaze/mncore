// Reconstructs the memories of the focus PEs at any line from the trace's writes.
import type { Access, Trace } from './types';

/** Word memories of one unit: loc -> address -> word. */
export type UnitMemory = Map<string, Map<number, number>>;
/** All focus units: unit key ("pe:<index>", "l1b:<index>", "mab:<index>") -> memory. */
export type Memory = Map<string, UnitMemory>;

export function unitKey(a: Access): string {
  if (a.loc === 'l1bm') return `l1b:${a.unit}`;
  if (a.loc === 'matx' || a.loc === 'maty') return `mab:${a.unit}`;
  return `pe:${a.unit}`;
}

/** Word-addressed locations, and how many words one address step covers. */
function wordsPerAddr(loc: string): number {
  // L1BM addresses are long words (2 words); the matrix register addresses physical rows
  // (8 words); T addresses are cycles (4 words); others are words.
  if (loc === 'l1bm') return 2;
  if (loc === 'matx' || loc === 'maty') return 8;
  if (loc === 't') return 4;
  return 1;
}

export function applyWrite(mem: Memory, a: Access) {
  if (!a.write || a.addr === null || a.loc === 'out') return;
  const key = unitKey(a);
  let unit = mem.get(key);
  if (!unit) mem.set(key, (unit = new Map()));
  let m = unit.get(a.loc);
  if (!m) unit.set(a.loc, (m = new Map()));
  const base = a.addr * wordsPerAddr(a.loc);
  a.words.forEach((w, i) => m!.set(base + i, w));
}

/** Memory state after `line` (inclusive), or before the first line when line < 0. */
export class MemoryTimeline {
  private snapshots: Memory[] = [];
  private readonly every = 32;

  constructor(private trace: Trace) {
    let mem: Memory = new Map();
    for (const a of trace.init) applyWrite(mem, a);
    this.snapshots.push(clone(mem));
    trace.lines.forEach((l, i) => {
      for (const a of l.accesses) applyWrite(mem, a);
      if ((i + 1) % this.every === 0) this.snapshots.push(clone(mem));
    });
  }

  at(line: number): Memory {
    const k = Math.min(Math.floor((line + 1) / this.every), this.snapshots.length - 1);
    const mem = clone(this.snapshots[k]);
    for (let i = k * this.every; i <= line && i < this.trace.lines.length; i++) {
      for (const a of this.trace.lines[i].accesses) applyWrite(mem, a);
    }
    return mem;
  }
}

function clone(m: Memory): Memory {
  const out: Memory = new Map();
  for (const [k, unit] of m) {
    const u = new Map<string, Map<number, number>>();
    for (const [loc, words] of unit) u.set(loc, new Map(words));
    out.set(k, u);
  }
  return out;
}

export function read(mem: Memory, unit: string, loc: string, addr: number): number | undefined {
  return mem.get(unit)?.get(loc)?.get(addr);
}
