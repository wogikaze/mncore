// Application state shared by the views.
import { loadIndex, loadProblem, runTrace } from './sim';
import { MemoryTimeline, type Memory } from './memory';
import type { ProblemEntry, Trace } from './types';
import type { View } from './numbers';

export interface Selection {
  unit: number;
  loc: string;
  addr: number;
}

class AppState {
  problems = $state<ProblemEntry[]>([]);
  problem = $state('');
  statement = $state('');
  testcase = '';
  solution = $state('');
  trace = $state.raw<Trace | null>(null);
  timeline: MemoryTimeline | null = null;
  /** Index into trace.lines of the line being shown. */
  line = $state(0);
  /** Seconds per step when playing. */
  stepSeconds = $state(1.2);
  focusPe = $state(0);
  view = $state<View>('f32');
  selection = $state<Selection | null>(null);
  loading = $state(false);
  error = $state<string | null>(null);

  /** Memory of the focus PEs before and after the current line. */
  before = $derived.by<Memory>(() => (this.trace && this.timeline ? this.timeline.at(this.line - 1) : new Map()));
  after = $derived.by<Memory>(() => (this.trace && this.timeline ? this.timeline.at(this.line) : new Map()));

  async init() {
    try {
      this.problems = await loadIndex();
    } catch (e) {
      this.error = String(e);
    }
  }

  async open(name: string) {
    this.loading = true;
    this.error = null;
    try {
      const p = await loadProblem(name);
      this.problem = name;
      this.statement = p.statement;
      this.testcase = p.testcase;
      this.solution = p.solution;
      await this.simulate();
    } catch (e) {
      this.error = String(e);
    } finally {
      this.loading = false;
    }
  }

  /** Runs the simulator on the current testcase and solution. */
  async simulate() {
    this.loading = true;
    this.error = null;
    try {
      const t = await runTrace(this.testcase, this.solution, this.focusPe);
      this.timeline = new MemoryTimeline(t);
      this.trace = t;
      this.line = Math.min(this.line, Math.max(0, t.lines.length - 1));
      if (t.error) this.error = t.error;
    } catch (e) {
      this.error = String(e);
      this.trace = null;
    } finally {
      this.loading = false;
    }
  }

  seek(line: number) {
    if (!this.trace) return;
    this.line = Math.max(0, Math.min(this.trace.lines.length - 1, line));
  }

  /** Moves to the next line that occupies steps (skipping mask and debug lines). */
  next() {
    if (!this.trace) return;
    let i = this.line + 1;
    while (i < this.trace.lines.length && this.trace.lines[i].words === 0) i++;
    if (i < this.trace.lines.length) this.line = i;
  }

  prev() {
    if (!this.trace) return;
    let i = this.line - 1;
    while (i > 0 && this.trace.lines[i].words === 0) i--;
    this.line = Math.max(0, i);
  }
}

export const app = new AppState();
