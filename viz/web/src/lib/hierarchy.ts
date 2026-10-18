// Shared hierarchy and value helpers for the overview, scope detail and dataflow views.
import { category } from './flows.ts';
import { format, type View } from './numbers.ts';
import type { Access, Flow, LineInfo } from './types';

export type ScopeLevel = 'chip' | 'group' | 'l1b' | 'mab' | 'pe';

export const L1B_PER_GROUP = 16;
export const L2B_PER_GROUP = 2;
export const L1B_PER_L2B = 8;
export const MAB_PER_L1B = 16;
export const PE_PER_MAB = 4;
export const MAB_PER_GROUP = L1B_PER_GROUP * MAB_PER_L1B;

export const groupOfMab = (mab: number) => Math.floor(mab / MAB_PER_GROUP);
export const l2bOfMab = (mab: number) => Math.floor(mab / (MAB_PER_L1B * L1B_PER_L2B));
export const l1bOfMab = (mab: number) => Math.floor(mab / MAB_PER_L1B);
export const mabOfGroup = (group: number) => group * MAB_PER_GROUP;
export const mabOfL1b = (l1b: number) => l1b * MAB_PER_L1B;

export interface Activity {
  groups: Map<number, string>;
  l2bs: Map<number, string>;
  l1bs: Map<number, string>;
  cats: Set<string>;
  compute: number;
}

const rank = (c: string) => (c === 'l1' ? 3 : c === 'l2' ? 2 : c === 'offchip' ? 1 : 0);

/** Units touched by a line's flows, keeping the strongest category per unit. */
export function activityOf(flows: Flow[]): Activity {
  const groups = new Map<number, string>();
  const l2bs = new Map<number, string>();
  const l1bs = new Map<number, string>();
  const cats = new Set<string>();
  let compute = 0;
  const put = (m: Map<number, string>, u: number, c: string) => {
    const old = m.get(u);
    if (!old || rank(c) > rank(old)) m.set(u, c);
  };
  for (const f of flows) {
    const c = category(f.from, f.to);
    cats.add(c);
    if (!f.src && !f.dst) {
      compute++;
      continue;
    }
    for (const r of [f.src, f.dst]) {
      if (!r) continue;
      if (r.mem === 'dram' || r.mem === 'pdm') {
        for (const g of r.units) put(groups, g, c);
      } else if (r.mem === 'l2bm') {
        for (const u of r.units) {
          put(l2bs, u, c);
          put(groups, Math.floor(u / L2B_PER_GROUP), c);
        }
      } else if (r.mem === 'l1bm') {
        for (const u of r.units) {
          put(l1bs, u, c);
          put(l2bs, Math.floor(u / L1B_PER_L2B), c);
          put(groups, Math.floor(u / L1B_PER_GROUP), c);
        }
      }
    }
  }
  return { groups, l2bs, l1bs, cats, compute };
}

export function shortWords(words: number[], view: View, n = 2): string {
  const s = format(words.slice(0, n), view).join(' ');
  return s.length > 18 ? `${s.slice(0, 17)}…` : s;
}

export function trim(s: string, n = 12): string {
  return s.length > n ? `${s.slice(0, n - 1)}…` : s;
}

export interface ValueRow {
  loc: string;
  addr: number | null;
  words: number[];
  cycle: number;
  slot: number | null;
  count: number;
}

/** Reads or writes of one PE, collapsed by location/address (cycles counted). */
export function valueRows(accesses: Access[], write: boolean): ValueRow[] {
  const map = new Map<string, ValueRow>();
  for (const a of accesses) {
    if (a.loc === 'out' || a.write !== write) continue;
    const key = `${a.loc}:${a.addr ?? ''}`;
    const cur = map.get(key);
    if (cur) {
      cur.count++;
      cur.cycle = Math.min(cur.cycle, a.cycle);
    } else {
      map.set(key, { loc: a.loc, addr: a.addr, words: a.words, cycle: a.cycle, slot: a.slot, count: 1 });
    }
  }
  return [...map.values()];
}

export interface PeSummary {
  reads: ValueRow[];
  writes: ValueRow[];
  out: string;
  outAll: string;
  outFirst: string;
  dest?: Access;
  readCount: number;
  writeCount: number;
}

export function peSummary(line: LineInfo | undefined, pe: number, view: View): PeSummary {
  const acc = (line?.accesses ?? []).filter((a) => a.unit === pe);
  const outs = acc.filter((a) => a.loc === 'out' && a.write);
  const out = outs[outs.length - 1];
  const writes = acc.filter((a) => a.write && a.loc !== 'out');
  const reads = acc.filter((a) => !a.write);
  const values = out ? format(out.words, view) : [];
  return {
    reads: valueRows(reads, false),
    writes: valueRows(writes, true),
    out: values.slice(0, 2).join(' '),
    outAll: values.join(' '),
    outFirst: values[0] ?? '',
    dest: writes[0],
    readCount: reads.length,
    writeCount: writes.length,
  };
}

/** Human name of a memory/forwarding location. */
export const LOC_NAMES: Record<string, string> = {
  lm0: 'LM0',
  lm1: 'LM1',
  grf0: 'GRF0',
  grf1: 'GRF1',
  t: 'T',
  omr: 'OMR',
  aluf: '$aluf',
  mauf: '$mauf',
  mreadf: '$mreadf',
  lbf: '$lbf',
  l1bm_src: 'L1BM',
  l1bm: 'L1BM',
  matx: '$x',
  maty: '$y',
  out: '結果',
};

export const LEVEL_NAMES: Record<string, string> = {
  dram: 'DRAM',
  pdm: 'PDM',
  l2bm: 'L2BM',
  l1bm: 'L1BM',
  pe: 'PE',
  alu: 'ALU',
  mau: 'MAU',
  matrix: '行列',
};

export function levelName(level: string): string {
  return LEVEL_NAMES[level] ?? level;
}

export function locName(loc: string): string {
  return LOC_NAMES[loc] ?? loc;
}

export function locLabel(loc: string, addr: number | null): string {
  if (addr === null) return locName(loc);
  if (loc === 't') return `T c${addr}`;
  return `${locName(loc)}[${addr}]`;
}
