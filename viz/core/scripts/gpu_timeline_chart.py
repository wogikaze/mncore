#!/usr/bin/env python3
"""Renders a JIT timeline (gpu_run_program GPU_TIMELINE=...) as a Gantt chart.

Usage:
    GPU_TIMELINE=/tmp/timeline.json ./target/release/gpu_run_program \
        benchmarks/mnist_train_step.vsm --engine jit
    python3 scripts/gpu_timeline_chart.py /tmp/timeline.json out.html

The chart is one self-contained HTML file: a Gantt chart (x = time within one
run of one block, one row per operation kind, grid-barrier waits on their own
row), a per-kind total-time bar chart, and a table view.
"""

import json
import sys

# Row order follows the data flow; families pick the color (fixed order).
ROWS = [
    ("mv", "MV（mvp・mvb など）", "mv"),
    ("l2", "L2BM↔L1BM 転送（l2bmd など）", "l2"),
    ("l2_reduce", "L2BM 縮約（l2bmr）", "l2"),
    ("l1_write", "PE→L1BM（l1bmm@ など）", "l1"),
    ("l1_read", "L1BM→PE（l1bmm・l1bmd など）", "l1"),
    ("alu", "ALU（imm・ipassa・fmax など）", "alu"),
    ("bfn", "ブロック浮動小数点（gbfn など）", "alu"),
    ("clear_mreadf", "mreadf のクリア", "alu"),
    ("mau", "MAU（fvadd・fvmul・fvfma）", "mau"),
    ("mat_write", "行列書き込み（gmwrite など）", "mat"),
    ("mat_read", "行列読み出し（gmread など）", "mat"),
    ("mat_mau", "行列 MAU（gmmul・gmfma）", "mat"),
    ("barrier", "grid barrier 待ち", "wait"),
]

FAMILIES = [
    ("alu", "ALU 系"),
    ("mau", "MAU"),
    ("mat", "行列"),
    ("l1", "L1BM"),
    ("l2", "L2BM"),
    ("mv", "MV"),
    ("wait", "grid barrier 待ち"),
]

TEMPLATE = r"""<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<title>GPU JIT 実行タイムライン</title>
<style>
.viz-root {
  color-scheme: light;
  --page: #f9f9f7;
  --surface-1: #fcfcfb;
  --text-primary: #0b0b0b;
  --text-secondary: #52514e;
  --text-muted: #898781;
  --grid: #e1e0d9;
  --axis: #c3c2b7;
  --border: rgba(11, 11, 11, 0.10);
  --fam-alu: #2a78d6;
  --fam-mau: #eb6834;
  --fam-mat: #1baf7a;
  --fam-l1: #eda100;
  --fam-l2: #e87ba4;
  --fam-mv: #008300;
  --fam-wait: #b3b2ab;
}
@media (prefers-color-scheme: dark) {
  :root:where(:not([data-theme="light"])) .viz-root {
    color-scheme: dark;
    --page: #0d0d0d;
    --surface-1: #1a1a19;
    --text-primary: #f0efec;
    --text-secondary: #c3c2b7;
    --text-muted: #898781;
    --grid: #2c2c2a;
    --axis: #383835;
    --border: rgba(255, 255, 255, 0.10);
    --fam-alu: #3987e5;
    --fam-mau: #d95926;
    --fam-mat: #199e70;
    --fam-l1: #c98500;
    --fam-l2: #d55181;
    --fam-mv: #008300;
    --fam-wait: #5c5b57;
  }
}
:root[data-theme="dark"] .viz-root {
  color-scheme: dark;
  --page: #0d0d0d;
  --surface-1: #1a1a19;
  --text-primary: #f0efec;
  --text-secondary: #c3c2b7;
  --text-muted: #898781;
  --grid: #2c2c2a;
  --axis: #383835;
  --border: rgba(255, 255, 255, 0.10);
  --fam-alu: #3987e5;
  --fam-mau: #d95926;
  --fam-mat: #199e70;
  --fam-l1: #c98500;
  --fam-l2: #d55181;
  --fam-mv: #008300;
  --fam-wait: #5c5b57;
}
body { margin: 0; background: var(--page); }
.viz-root {
  font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
  background: var(--page);
  color: var(--text-primary);
  padding: 24px;
  max-width: 1320px;
}
h1 { font-size: 20px; font-weight: 600; margin: 0 0 4px; }
.sub { color: var(--text-secondary); font-size: 13px; margin: 0 0 16px; }
.controls { display: flex; gap: 8px; align-items: center; margin-bottom: 12px; font-size: 13px; color: var(--text-secondary); }
.controls button {
  font: inherit; color: var(--text-primary); background: var(--surface-1);
  border: 1px solid var(--border); border-radius: 6px; padding: 4px 10px; cursor: pointer;
}
.controls button:hover { background: var(--grid); }
.card { background: var(--surface-1); border: 1px solid var(--border); border-radius: 10px; padding: 16px; margin-bottom: 16px; }
.card h2 { font-size: 15px; font-weight: 600; margin: 0 0 2px; }
.card .note { font-size: 12px; color: var(--text-secondary); margin: 0 0 10px; }
.legend { display: flex; flex-wrap: wrap; gap: 14px; font-size: 12px; color: var(--text-secondary); margin: 6px 0 8px; }
.legend span { display: inline-flex; align-items: center; gap: 6px; }
.legend i { width: 12px; height: 12px; border-radius: 3px; display: inline-block; }
svg text { font-family: inherit; }
.tick { fill: var(--text-muted); font-size: 11px; font-variant-numeric: tabular-nums; }
.rowlabel { fill: var(--text-secondary); font-size: 12px; }
.value { fill: var(--text-secondary); font-size: 12px; font-variant-numeric: tabular-nums; }
.tooltip {
  position: fixed; pointer-events: none; display: none; z-index: 10;
  background: var(--surface-1); color: var(--text-primary);
  border: 1px solid var(--border); border-radius: 8px; padding: 8px 10px;
  font-size: 12px; box-shadow: 0 4px 16px rgba(0,0,0,0.12); max-width: 420px;
}
.tooltip .v { font-size: 14px; font-weight: 600; }
.tooltip .k { color: var(--text-secondary); display: flex; align-items: center; gap: 6px; }
.tooltip .k b { width: 12px; height: 2px; display: inline-block; }
.tooltip code { color: var(--text-secondary); font-size: 11px; }
details { font-size: 13px; color: var(--text-secondary); }
table { border-collapse: collapse; margin-top: 8px; font-variant-numeric: tabular-nums; }
th, td { text-align: right; padding: 3px 10px; border-bottom: 1px solid var(--grid); color: var(--text-primary); }
th:first-child, td:first-child { text-align: left; }
th { color: var(--text-secondary); font-weight: 500; }
</style>
</head>
<body>
<div class="viz-root">
  <h1>GPU JIT 実行タイムライン：命令種ごとの所要時間</h1>
  <p class="sub" id="sub"></p>

  <div class="card">
    <h2>ガントチャート（1 回の実行・1 ブロック）</h2>
    <p class="note">横軸は実行開始からの時間（µs）、縦は命令種。各棒は 1 命令で、命令の開始から次の命令の開始までを表します。grid barrier の待ち時間は最下段に分けています。ドラッグで範囲を拡大、ダブルクリックで全体表示。</p>
    <div class="controls">
      <button id="reset">全体を表示</button>
      <span id="range"></span>
    </div>
    <div class="legend" id="legend"></div>
    <svg id="gantt" role="img" aria-label="命令種ごとのガントチャート"></svg>
  </div>

  <div class="card">
    <h2>命令種ごとの合計時間</h2>
    <p class="note">ガントチャートと同じ 1 回の実行での合計。棒の右に合計時間・全体に占める割合・命令数を示します。</p>
    <svg id="totals" role="img" aria-label="命令種ごとの合計時間"></svg>
    <details>
      <summary>表で見る</summary>
      <table id="table"></table>
    </details>
  </div>
  <div class="tooltip" id="tip"></div>
</div>
<script type="application/json" id="data">__DATA__</script>
<script type="application/json" id="rows">__ROWS__</script>
<script type="application/json" id="families">__FAMILIES__</script>
<script>
(() => {
  const data = JSON.parse(document.getElementById('data').textContent);
  const ROWS = JSON.parse(document.getElementById('rows').textContent);
  const FAMILIES = JSON.parse(document.getElementById('families').textContent);
  const NS = 'http://www.w3.org/2000/svg';
  const ops = data.ops;
  const total = ops.length ? ops[ops.length - 1].end : 0;
  const rowIndex = Object.fromEntries(ROWS.map((r, i) => [r[0], i]));
  const famColor = f => `var(--fam-${f})`;
  const fmt = (v, d = 1) => v.toLocaleString('ja-JP', { minimumFractionDigits: d, maximumFractionDigits: d });
  const el = (tag, attrs, parent) => {
    const e = document.createElementNS(NS, tag);
    for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
    if (parent) parent.appendChild(e);
    return e;
  };

  document.getElementById('sub').textContent =
    `${data.program}・${data.words.toLocaleString('ja-JP')} words・${ops.length.toLocaleString('ja-JP')} 命令・` +
    `ブロック ${data.block}（中央値のブロック）・1 回 ${fmt(total, 0)} µs（SM ${fmt(data.ghz, 2)} GHz で換算）`;

  // Intervals per row: the operation itself and, for barrier ops, the wait.
  const segs = [];
  for (const o of ops) {
    if (o.barrier && o.ready > o.start) {
      segs.push({ row: rowIndex.barrier, fam: 'wait', a: o.start, b: o.ready, op: o, wait: true });
    }
    const r = rowIndex[o.kind] ?? rowIndex.alu;
    segs.push({ row: r, fam: ROWS[r][2], a: o.ready, b: o.end, op: o, wait: false });
  }
  const byRow = ROWS.map(() => []);
  for (const s of segs) byRow[s.row].push(s);

  // Legend (families; row labels carry the kind).
  const legend = document.getElementById('legend');
  for (const [f, name] of FAMILIES) {
    const span = document.createElement('span');
    const sw = document.createElement('i');
    sw.style.background = famColor(f);
    span.appendChild(sw);
    span.appendChild(document.createTextNode(name));
    legend.appendChild(span);
  }

  // ---- Gantt ----
  const gantt = document.getElementById('gantt');
  const W = 1280, LEFT = 230, RIGHT = 16, TOP = 8, BAND = 26, BAR = 14, AXIS = 28;
  const H = TOP + BAND * ROWS.length + AXIS;
  gantt.setAttribute('viewBox', `0 0 ${W} ${H}`);
  gantt.setAttribute('width', '100%');
  let view = [0, total];
  const plotW = W - LEFT - RIGHT;
  const xOf = t => LEFT + (t - view[0]) / (view[1] - view[0]) * plotW;
  const tOf = x => view[0] + (x - LEFT) / plotW * (view[1] - view[0]);

  const tip = document.getElementById('tip');
  function showTip(evt, s) {
    tip.replaceChildren();
    const o = s.op;
    const v = document.createElement('div');
    v.className = 'v';
    v.textContent = `${fmt(s.b - s.a, 2)} µs`;
    const k = document.createElement('div');
    k.className = 'k';
    const key = document.createElement('b');
    key.style.background = famColor(s.fam);
    k.appendChild(key);
    k.appendChild(document.createTextNode(s.wait ? `grid barrier 待ち（命令 #${o.i} の前）` : `${ROWS[rowIndex[o.kind] ?? rowIndex.alu][1]}${o.direct ? '・直接書き込み' : ''}`));
    const meta = document.createElement('div');
    meta.className = 'k';
    meta.textContent = `命令 #${o.i}・${fmt(s.a, 2)}〜${fmt(s.b, 2)} µs${o.line ? `・VSM ${o.line} 行目` : ''}`;
    const code = document.createElement('code');
    code.textContent = o.text;
    tip.append(v, k, meta, code);
    tip.style.display = 'block';
    const pad = 14;
    let x = evt.clientX + pad, y = evt.clientY + pad;
    const r = tip.getBoundingClientRect();
    if (x + r.width > innerWidth) x = evt.clientX - r.width - pad;
    if (y + r.height > innerHeight) y = evt.clientY - r.height - pad;
    tip.style.left = `${x}px`;
    tip.style.top = `${y}px`;
  }
  const hideTip = () => { tip.style.display = 'none'; };

  let hoverMark = null;
  function drawGantt() {
    gantt.replaceChildren();
    const grid = el('g', {}, gantt);
    // Time ticks: clean steps.
    const span = view[1] - view[0];
    const raw = span / 8;
    const p = Math.pow(10, Math.floor(Math.log10(raw)));
    const step = [1, 2, 5, 10].map(m => m * p).find(s => s >= raw);
    for (let t = Math.ceil(view[0] / step) * step; t <= view[1] + 1e-9; t += step) {
      const x = xOf(t);
      el('line', { x1: x, x2: x, y1: TOP, y2: TOP + BAND * ROWS.length, stroke: 'var(--grid)', 'stroke-width': 1 }, grid);
      const lbl = el('text', { x, y: TOP + BAND * ROWS.length + 18, 'text-anchor': 'middle', class: 'tick' }, grid);
      lbl.textContent = `${fmt(t, step < 1 ? 2 : 0)} µs`;
    }
    ROWS.forEach((r, i) => {
      const y = TOP + i * BAND;
      el('line', { x1: LEFT, x2: W - RIGHT, y1: y + BAND, y2: y + BAND, stroke: 'var(--grid)', 'stroke-width': 1 }, grid);
      const t = el('text', { x: LEFT - 10, y: y + BAND / 2 + 4, 'text-anchor': 'end', class: 'rowlabel' }, grid);
      t.textContent = r[1];
    });
    el('line', { x1: LEFT, x2: LEFT, y1: TOP, y2: TOP + BAND * ROWS.length, stroke: 'var(--axis)', 'stroke-width': 1 }, grid);
    const clip = el('clipPath', { id: 'plotclip' }, gantt);
    el('rect', { x: LEFT, y: 0, width: plotW, height: H }, clip);
    const marks = el('g', { 'clip-path': 'url(#plotclip)' }, gantt);
    for (const s of segs) {
      if (s.b < view[0] || s.a > view[1]) continue;
      const x0 = xOf(s.a), x1 = xOf(s.b);
      const w = Math.max(1, x1 - x0);
      const y = TOP + s.row * BAND + (BAND - BAR) / 2;
      const rect = el('rect', {
        x: x0, y, width: w, height: BAR, fill: famColor(s.fam), rx: w > 8 ? 3 : 0,
      }, marks);
      rect.__seg = s;
    }
    hoverMark = el('rect', { fill: 'none', stroke: 'var(--text-primary)', 'stroke-width': 1.5, visibility: 'hidden' }, gantt);
    document.getElementById('range').textContent =
      `表示範囲 ${fmt(view[0], 1)}〜${fmt(view[1], 1)} µs`;
  }

  // Hover: nearest segment in the row under the pointer (hit area wider than
  // the 1px marks that most operations are at full scale).
  function svgPoint(evt) {
    const pt = gantt.createSVGPoint();
    pt.x = evt.clientX; pt.y = evt.clientY;
    return pt.matrixTransform(gantt.getScreenCTM().inverse());
  }
  function findSeg(p) {
    const row = Math.floor((p.y - TOP) / BAND);
    if (row < 0 || row >= ROWS.length || p.x < LEFT || p.x > W - RIGHT) return null;
    const t = tOf(p.x);
    const tol = 4 / plotW * (view[1] - view[0]);
    let best = null, bestD = Infinity;
    for (const s of byRow[row]) {
      const d = t < s.a ? s.a - t : t > s.b ? t - s.b : 0;
      if (d < bestD) { bestD = d; best = s; }
    }
    return bestD <= tol ? best : null;
  }
  let drag = null;
  gantt.addEventListener('pointermove', evt => {
    const p = svgPoint(evt);
    if (drag) {
      drag.box.setAttribute('x', Math.min(drag.x, p.x));
      drag.box.setAttribute('width', Math.abs(p.x - drag.x));
      return;
    }
    const s = findSeg(p);
    if (!s) { hideTip(); hoverMark.setAttribute('visibility', 'hidden'); return; }
    const x0 = xOf(s.a), w = Math.max(1, xOf(s.b) - x0);
    hoverMark.setAttribute('x', x0 - 1);
    hoverMark.setAttribute('y', TOP + s.row * BAND + (BAND - BAR) / 2 - 1);
    hoverMark.setAttribute('width', w + 2);
    hoverMark.setAttribute('height', BAR + 2);
    hoverMark.setAttribute('visibility', 'visible');
    showTip(evt, s);
  });
  gantt.addEventListener('pointerleave', () => { hideTip(); hoverMark.setAttribute('visibility', 'hidden'); });
  gantt.addEventListener('pointerdown', evt => {
    const p = svgPoint(evt);
    if (p.x < LEFT) return;
    const box = el('rect', { x: p.x, y: TOP, width: 0, height: BAND * ROWS.length, fill: 'var(--text-muted)', opacity: 0.15 }, gantt);
    drag = { x: p.x, box };
    gantt.setPointerCapture(evt.pointerId);
  });
  gantt.addEventListener('pointerup', evt => {
    if (!drag) return;
    const p = svgPoint(evt);
    const a = tOf(Math.min(drag.x, p.x)), b = tOf(Math.max(drag.x, p.x));
    drag.box.remove();
    drag = null;
    if (Math.abs(xOf(b) - xOf(a)) > 6) {
      view = [Math.max(0, a), Math.min(total, b)];
      drawGantt();
    }
  });
  gantt.addEventListener('dblclick', () => { view = [0, total]; drawGantt(); });
  document.getElementById('reset').addEventListener('click', () => { view = [0, total]; drawGantt(); });
  drawGantt();

  // ---- Totals ----
  const sums = ROWS.map((r, i) => ({
    row: i, name: r[1], fam: r[2],
    us: byRow[i].reduce((a, s) => a + (s.b - s.a), 0),
    n: byRow[i].length,
  })).filter(r => r.n > 0).sort((a, b) => b.us - a.us);
  const tot = document.getElementById('totals');
  const TB = 26, TBAR = 16, TL = 230, TR = 220;
  const TH = sums.length * TB + 8;
  tot.setAttribute('viewBox', `0 0 ${W} ${TH}`);
  tot.setAttribute('width', '100%');
  const maxUs = Math.max(...sums.map(s => s.us));
  const tw = W - TL - TR;
  sums.forEach((s, i) => {
    const y = 4 + i * TB;
    const lbl = el('text', { x: TL - 10, y: y + TB / 2 + 4, 'text-anchor': 'end', class: 'rowlabel' }, tot);
    lbl.textContent = s.name;
    const w = Math.max(1, s.us / maxUs * tw);
    // 4px rounded data end, square at the baseline.
    const h = TBAR, yy = y + (TB - TBAR) / 2, r = Math.min(4, w / 2);
    el('path', {
      d: `M${TL},${yy} H${TL + w - r} Q${TL + w},${yy} ${TL + w},${yy + r} V${yy + h - r} Q${TL + w},${yy + h} ${TL + w - r},${yy + h} H${TL} Z`,
      fill: famColor(s.fam),
    }, tot);
    const v = el('text', { x: TL + w + 8, y: y + TB / 2 + 4, class: 'value' }, tot);
    v.textContent = `${fmt(s.us, 0)} µs（${fmt(s.us / total * 100, 1)}%）・${s.n.toLocaleString('ja-JP')} 回`;
  });
  el('line', { x1: TL, x2: TL, y1: 0, y2: TH, stroke: 'var(--axis)', 'stroke-width': 1 }, tot);

  // ---- Table view ----
  const table = document.getElementById('table');
  const head = table.insertRow();
  for (const h of ['命令種', '合計 (µs)', '割合', '回数', '平均 (µs)']) {
    const th = document.createElement('th');
    th.textContent = h;
    head.appendChild(th);
  }
  for (const s of sums) {
    const tr = table.insertRow();
    for (const v of [s.name, fmt(s.us, 1), `${fmt(s.us / total * 100, 1)}%`, s.n.toLocaleString('ja-JP'), fmt(s.us / s.n, 2)]) {
      tr.insertCell().textContent = v;
    }
  }
})();
</script>
</body>
</html>
"""


def main() -> None:
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    with open(sys.argv[1], encoding="utf-8") as f:
        data = json.load(f)
    # Embedded JSON: keep "</" out of the script element.
    def embed(value: object) -> str:
        return json.dumps(value, ensure_ascii=False).replace("</", "<\\/")
    html = (
        TEMPLATE.replace("__DATA__", embed(data))
        .replace("__ROWS__", embed(ROWS))
        .replace("__FAMILIES__", embed(FAMILIES))
    )
    with open(sys.argv[2], "w", encoding="utf-8") as f:
        f.write(html)


if __name__ == "__main__":
    main()
