// Types of the trace produced by the simulator (viz/core/src/api.rs).

export type Loc =
  | 'lm0' | 'lm1' | 'grf0' | 'grf1' | 't'
  | 'aluf' | 'mauf' | 'mreadf' | 'lbf'
  | 'omr' | 'bar0' | 'bar1'
  | 'matx' | 'maty'
  | 'l1bm'
  | 'out';

export interface Access {
  /** Index of the expression within its line. */
  expr: number;
  /** Global PE index; L1B index for l1bm; MAB index for matx/maty. */
  unit: number;
  cycle: number;
  loc: Loc;
  write: boolean;
  /** Word address (PE memories), long word address (L1BM), physical row (matrix), entry (omr). */
  addr: number | null;
  /** Words read or written, MSB first. */
  words: number[];
}

export interface Flow {
  from: string;
  to: string;
  longs: number;
  kind: string;
}

export interface ExprInfo {
  text: string;
  unit: 'alu' | 'mau' | 'matrix' | 'mwrite' | 'mread' | 'l1-to-pe' | 'pe-to-l1' | 'l2' | 'wait' | 'noforward' | 'other';
  /** Forwarding register this expression updates. */
  fwd: 'aluf' | 'mauf' | 'mreadf' | 'lbf' | null;
}

export interface LineInfo {
  lineno: number;
  text: string;
  kind: 'pe' | 'nop' | 'mv' | 'mask' | 'debug';
  step: number;
  words: number;
  flows: Flow[];
  exprs: ExprInfo[];
  accesses: Access[];
}

export interface Hazard {
  rule: string;
  kind: 'data race' | 'port conflict';
  res: string;
  addr: number | null;
  from: number;
  to: number;
  distance: number;
  required: number;
}

export interface Nop {
  line: number;
  needed_by: number[];
}

export interface OutputCheck {
  values: number;
  failures: number;
  max_abs_error: number;
  atol: number;
  first_failure: string | null;
}

export interface Trace {
  lines: LineInfo[];
  score: number;
  hazards: Hazard[];
  nops: Nop[];
  focus: number[];
  init: Access[];
  output: OutputCheck;
  error: string | null;
  error_line: number | null;
}

export interface ProblemEntry {
  name: string;
  title: string;
  number: number;
}
