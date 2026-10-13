// Playback: which line is shown and how far its 4 cycles have progressed. Views build paused
// GSAP timelines for the current line and seek them to `progress`, so pausing stops every
// animation and the cycle can be stepped or scrubbed.
import { app } from './state.svelte';

class Player {
  /** Progress through the current line's step, 0 to 1 (cycle c spans c/4 to (c+1)/4). */
  progress = $state(1);
  playing = $state(false);
  private raf = 0;
  private last = 0;

  /** Cycle shown, 0 to 3. */
  get cycle(): number {
    return Math.min(3, Math.floor(this.progress * 4));
  }

  /** Seconds the current line takes when playing. */
  private duration(): number {
    const w = app.trace?.lines[app.line]?.words || 1;
    return app.stepSeconds * Math.min(w, 4);
  }

  play() {
    if (this.playing) return;
    this.playing = true;
    if (this.progress >= 1) this.progress = 0;
    this.last = performance.now();
    const tick = (now: number) => {
      if (!this.playing) return;
      this.progress += (now - this.last) / 1000 / this.duration();
      this.last = now;
      if (this.progress >= 1) {
        const before = app.line;
        app.next();
        if (app.line === before) {
          this.progress = 1;
          this.playing = false;
          return;
        }
        this.progress = 0;
      }
      this.raf = requestAnimationFrame(tick);
    };
    this.raf = requestAnimationFrame(tick);
  }

  pause() {
    this.playing = false;
    cancelAnimationFrame(this.raf);
  }

  toggle() {
    if (this.playing) this.pause();
    else this.play();
  }

  /** Shows a line from its start (or fully when not playing). */
  goto(line: number) {
    app.seek(line);
    this.progress = this.playing ? 0 : 1;
  }

  /** Steps one cycle forward, moving to the next line after cycle 3. */
  nextCycle() {
    this.pause();
    const c = this.progress >= 1 ? 4 : this.cycle + 1;
    if (c >= 4) {
      const before = app.line;
      app.next();
      this.progress = app.line === before ? 1 : 0.125;
    } else this.progress = (c + 0.5) / 4;
  }

  prevCycle() {
    this.pause();
    const c = this.progress >= 1 ? 3 : this.cycle - 1;
    if (c < 0) {
      app.prev();
      this.progress = 3.5 / 4;
    } else this.progress = (c + 0.5) / 4;
  }

  setCycle(c: number) {
    this.pause();
    this.progress = (c + 0.5) / 4;
  }
}

export const player = new Player();
