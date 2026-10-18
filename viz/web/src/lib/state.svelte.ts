// Application state shared by the views.
import { loadIndex, loadProblem, runTrace } from './sim';
import { MemoryTimeline, type Memory } from './memory';
import type { Access, ProblemEntry, Selection, Trace } from './types';
import type { View } from './numbers';

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
  /** First PE of the MAB recorded by the simulator. */
  focusPe = $state(0);
  /** Which of the MAB's four PEs the data path and memory views show. */
  peIndex = $state(0);
  view = $state<View>('f32');
  selection = $state<Selection | null>(null);
  loading = $state(false);
  error = $state<string | null>(null);
  /** Guards against an older simulation finishing after a newer one. */
  private run = 0;

  get focusMab(): number {
    return Math.floor(this.focusPe / 4);
  }

  /** The PE shown by the data path and memory views, from the traced MAB. */
  get pe(): number {
    const focus = this.trace?.focus;
    if (focus?.length) return focus[Math.min(this.peIndex, focus.length - 1)];
    return this.focusPe + this.peIndex;
  }

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
    const run = ++this.run;
    this.loading = true;
    this.error = null;
    this.selection = null;
    try {
      const t = await runTrace(this.testcase, this.solution, this.focusPe);
      if (run !== this.run) return;
      this.timeline = new MemoryTimeline(t);
      this.trace = t;
      this.line = Math.min(this.line, Math.max(0, t.lines.length - 1));
      if (t.error) this.error = t.error;
    } catch (e) {
      if (run !== this.run) return;
      this.error = String(e);
      this.trace = null;
    } finally {
      if (run === this.run) this.loading = false;
    }
  }

  /** Records the MAB around `mab` and re-simulates so its four PEs are traced. */
  async setFocusMab(mab: number) {
    if (!Number.isFinite(mab)) return;
    const next = Math.max(0, Math.min(1023, Math.trunc(mab)));
    if (next === this.focusMab) return;
    this.focusPe = next * 4;
    this.peIndex = 0;
    this.selection = null;
    await this.simulate();
  }

  setPeIndex(i: number) {
    if (i === this.peIndex) return;
    this.peIndex = i;
    this.selection = null;
  }

  /** Follows one input of an expression read at `atLine` to its own provenance. */
  followInput(a: Access, atLine: number) {
    this.selection = {
      unit: a.unit,
      loc: a.loc,
      addr: a.addr,
      // A forwarding read is resolved before `atLine`; a memory read shows the state
      // before the line that read it.
      line: a.addr === null ? atLine : atLine - 1,
      cycle: a.cycle,
    };
    this.seek(atLine);
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
