// Traces where a value in a focus PE came from: the expression that wrote it, the inputs that
// expression read, and recursively where those came from.
import type { Access, Trace } from './types';

export interface Origin {
  /** Index of the line that produced the value, or -1 for the testcase's initial data. */
  line: number;
  /** The write (or initial value) that produced it. */
  write: Access;
  /** Text of the producing expression. */
  expr: string;
  /** What the expression read in the same PE and cycle. */
  inputs: Access[];
}

function covers(a: Access, loc: string, addr: number): boolean {
  if (a.loc !== loc || a.addr === null) return false;
  const n = loc === 't' ? 1 : a.words.length;
  return addr >= a.addr && addr < a.addr + n;
}

/** The latest write to (unit, loc, addr) at or before `line`. */
export function producer(trace: Trace, unit: number, loc: string, addr: number, line: number): Origin | null {
  for (let i = Math.min(line, trace.lines.length - 1); i >= 0; i--) {
    const l = trace.lines[i];
    for (let k = l.accesses.length - 1; k >= 0; k--) {
      const a = l.accesses[k];
      if (a.write && a.unit === unit && covers(a, loc, addr)) {
        const exprText = l.exprs[a.expr]?.text ?? l.text;
        const inputs = l.accesses.filter((r) => !r.write && r.expr === a.expr && r.unit === unit && r.cycle === a.cycle);
        return { line: i, write: a, expr: exprText, inputs };
      }
    }
  }
  const init = trace.init.find((a) => a.unit === unit && covers(a, loc, addr));
  return init ? { line: -1, write: init, expr: 'testcase input (d set)', inputs: [] } : null;
}

/**
 * For a forwarding read ($aluf, $mauf, ...) at `line`, the result it forwards: the "out" of
 * the latest earlier line whose expression feeds that register (nop lines do not update it).
 */
export function forwarded(trace: Trace, unit: number, loc: string, cycle: number, line: number): Origin | null {
  for (let i = line - 1; i >= 0; i--) {
    const l = trace.lines[i];
    // nop lines (and non-PE lines) do not update forwarding registers.
    if (l.kind !== 'pe') continue;
    const ei = l.exprs.findIndex((e) => e.fwd === loc);
    if (ei < 0) return null;
    const out = l.accesses.find((a) => a.loc === 'out' && a.expr === ei && a.unit === unit && a.cycle === cycle);
    if (!out) return null;
    const inputs = l.accesses.filter((r) => !r.write && r.expr === ei && r.unit === unit && r.cycle === cycle);
    return { line: i, write: out, expr: l.exprs[ei].text, inputs };
  }
  return null;
}

/** The chain of origins of a value, following the first input at each step (depth-limited). */
export function chain(trace: Trace, unit: number, loc: string, addr: number, line: number, depth = 8): Origin[] {
  const out: Origin[] = [];
  let cur = producer(trace, unit, loc, addr, line);
  while (cur && out.length < depth) {
    out.push(cur);
    const next = cur.inputs[0];
    if (!next) break;
    if (next.addr === null) {
      cur = forwarded(trace, next.unit, next.loc, next.cycle, cur.line);
    } else {
      cur = producer(trace, next.unit, next.loc, next.addr, cur.line - 1);
    }
  }
  return out;
}
