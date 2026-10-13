// Issue group occupancy per step (SDM 3.6.4), and resource lower bounds of the step count.
import type { Trace } from './types';

/** Rows of the occupancy table, in display order. */
export const GROUPS = [
  { id: 'alu', label: 'ALU' },
  { id: 'mau-calc', label: 'MAU 演算' },
  { id: 'mau-mwrite', label: 'MAU 行列書込' },
  { id: 'mau-mread', label: 'MAU 行列読出' },
  { id: 'l1bm', label: 'L1BM' },
  { id: 'l1bm-turnaround', label: 'L1BM 折返し' },
  { id: 'l2bm', label: 'L2BM' },
  { id: 'l2bmdarw', label: 'l2bmdarw' },
  { id: 'wait', label: 'wait' },
  { id: 'noforward', label: 'noforward' },
  { id: 'mv', label: 'MV' },
  { id: 'nop', label: 'nop' },
] as const;

export const MAU_GROUPS = ['mau-calc', 'mau-mwrite', 'mau-mread'];

export interface Occupancy {
  steps: number;
  /** For each step: group id -> index of the line that uses it. */
  cells: Map<string, number>[];
  /** Line index that occupies each step. */
  lineOf: number[];
  counts: Record<string, number>;
  /** Steps where two MAU groups are used (the most allowed). */
  mauFull: number;
  /** PE steps that use exactly one group. */
  single: number;
  bound: Bound;
}

export interface Bound {
  /** Lower bound of PE steps from resources alone: the busiest group, and MAU's two-group limit. */
  peSteps: number;
  /** Which constraint gives the bound. */
  limitedBy: string;
  /** MV lines, which take one instruction word each. */
  mvLines: number;
  total: number;
}

export function occupancy(trace: Trace): Occupancy {
  const steps = trace.score;
  const cells: Map<string, number>[] = Array.from({ length: steps }, () => new Map());
  const lineOf: number[] = new Array(steps).fill(-1);
  const counts: Record<string, number> = {};
  const bump = (g: string) => (counts[g] = (counts[g] ?? 0) + 1);
  trace.lines.forEach((l, i) => {
    for (let s = l.step; s < l.step + l.words && s < steps; s++) {
      lineOf[s] = i;
      if (l.kind === 'nop') {
        cells[s].set('nop', i);
        bump('nop');
      } else if (l.kind === 'mv') {
        cells[s].set('mv', i);
        bump('mv');
      } else if (l.kind === 'pe') {
        for (const e of l.exprs) {
          cells[s].set(e.group, i);
          bump(e.group);
        }
      }
    }
  });
  let mauFull = 0;
  let single = 0;
  for (const c of cells) {
    if (MAU_GROUPS.filter((g) => c.has(g)).length >= 2) mauFull++;
    const groups = [...c.keys()].filter((g) => g !== 'nop' && g !== 'mv' && g !== 'wait' && g !== 'noforward');
    if (groups.length === 1) single++;
  }
  return { steps, cells, lineOf, counts, mauFull, single, bound: bound(counts) };
}

function bound(counts: Record<string, number>): Bound {
  const c = (g: string) => counts[g] ?? 0;
  let peSteps = 0;
  let limitedBy = '';
  for (const g of ['alu', 'mau-calc', 'mau-mwrite', 'mau-mread', 'l1bm', 'l1bm-turnaround', 'l2bm']) {
    if (c(g) > peSteps) {
      peSteps = c(g);
      limitedBy = g;
    }
  }
  // At most two of the three MAU groups can be issued in a step.
  const mau = Math.ceil((c('mau-calc') + c('mau-mwrite') + c('mau-mread')) / 2);
  if (mau > peSteps) {
    peSteps = mau;
    limitedBy = 'MAU（1ステップに3グループ中2つまで）';
  }
  return { peSteps, limitedBy, mvLines: c('mv'), total: peSteps + c('mv') };
}
