// Regression tests for hierarchy activity and per-PE value summaries.
import assert from 'node:assert/strict';
import { test } from 'node:test';

import { activityOf, groupOfMab, l1bOfMab, levelName, peSummary, l2bOfMab } from './hierarchy.ts';
import type { Access, Flow, LineInfo } from './types.ts';

function access(p: Partial<Access> & Pick<Access, 'expr' | 'unit' | 'cycle' | 'loc' | 'write'>): Access {
  return {
    expr: p.expr,
    unit: p.unit,
    cycle: p.cycle,
    loc: p.loc,
    write: p.write,
    addr: p.addr ?? null,
    words: p.words ?? [0],
    slot: p.slot ?? null,
  };
}

const line: LineInfo = {
  lineno: 3,
  text: 'fvmul',
  kind: 'pe',
  step: 1,
  words: 1,
  flows: [],
  exprs: [{ text: 'fvmul', unit: 'mau', fwd: 'mauf', group: 'mau-calc', opcode: 'fvmul', srcs: [], dsts: [] }],
  accesses: [
    access({ expr: 0, unit: 0, cycle: 0, loc: 'lm0', write: false, addr: 0, words: [1, 2], slot: 0 }),
    access({ expr: 0, unit: 0, cycle: 1, loc: 'lm0', write: false, addr: 0, words: [1, 2], slot: 0 }),
    access({ expr: 0, unit: 0, cycle: 0, loc: 'lm1', write: true, addr: 0, words: [3, 4], slot: 0 }),
    access({ expr: 0, unit: 0, cycle: 0, loc: 'out', write: true, words: [3, 4, 0, 0] }),
  ],
};

test('maps MAB numbers to group, L2B and L1B', () => {
  assert.equal(groupOfMab(0), 0);
  assert.equal(groupOfMab(255), 0);
  assert.equal(groupOfMab(256), 1);
  assert.equal(l2bOfMab(128), 1);
  assert.equal(l1bOfMab(16), 1);
  assert.equal(l1bOfMab(63), 3);
});

test('collapses chip flows to the units they touch', () => {
  const flows: Flow[] = [
    {
      from: 'l1bm',
      to: 'pe',
      longs: 4,
      kind: 'broadcast',
      src: { mem: 'l1bm', units: [3, 4], addr: 8, len: 2 },
      dst: null,
    },
    {
      from: 'dram',
      to: 'l2bm',
      longs: 8,
      kind: 'copy',
      src: { mem: 'dram', units: [1], addr: 0, len: 4 },
      dst: { mem: 'l2bm', units: [2], addr: 0, len: 4 },
    },
  ];
  const act = activityOf(flows);
  assert.deepEqual([...act.l1bs.keys()].sort(), [3, 4]);
  assert.deepEqual([...act.l2bs.keys()].sort(), [0, 2]);
  assert.deepEqual([...act.groups.keys()].sort(), [0, 1]);
  assert.equal(act.cats.has('l1'), true);
  assert.equal(act.cats.has('offchip'), true);
});

test('summarizes reads, writes and the expression result of one PE', () => {
  const s = peSummary(line, 0, 'i32');
  assert.equal(s.reads.length, 1);
  assert.equal(s.reads[0].count, 2);
  assert.equal(s.writes.length, 1);
  assert.equal(s.dest?.loc, 'lm1');
  assert.equal(s.out, '3 4');
  assert.equal(s.outFirst, '3');
  assert.equal(s.readCount, 2);
  assert.equal(s.writeCount, 1);
});

test('human level names are stable', () => {
  assert.equal(levelName('l1bm'), 'L1BM');
  assert.equal(levelName('dram'), 'DRAM');
  assert.equal(levelName('unknown'), 'unknown');
});
