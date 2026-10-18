// Regression tests for the provenance walk. Run with `npm test` (Node's built-in runner).
import assert from 'node:assert/strict';
import { test } from 'node:test';

import { chainFrom } from './provenance.ts';
import type { Access, Trace } from './types.ts';

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

function trace(accesses: Access[][]): Trace {
  return {
    lines: accesses.map((a, i) => ({
      lineno: i + 1,
      text: `line ${i + 1}`,
      kind: 'pe',
      step: i,
      words: 1,
      flows: [],
      exprs: [{ text: `expr ${i}`, unit: 'alu', fwd: 'aluf', group: 'alu', opcode: 'imm', srcs: [], dsts: [] }],
      accesses: a,
    })),
    score: accesses.length,
    hazards: [],
    nops: [],
    focus: [0, 1, 2, 3],
    init: [],
    output: { values: 0, failures: 0, max_abs_error: 0, atol: 0, first_failure: null },
    error: null,
    error_line: null,
  };
}

test('destination selection follows its input through a forwarding register', () => {
  const t = trace([
    [
      access({ expr: 0, unit: 0, cycle: 0, loc: 'out', write: true, words: [1, 2, 3, 4] }),
      access({ expr: 0, unit: 0, cycle: 0, loc: 'lm0', write: true, addr: 0, words: [5, 6] }),
    ],
    [
      access({ expr: 0, unit: 0, cycle: 0, loc: 'aluf', write: false, words: [1, 2, 3, 4], slot: 0 }),
      access({ expr: 0, unit: 0, cycle: 0, loc: 'lm1', write: true, addr: 0, words: [9, 9] }),
    ],
  ]);
  const chain = chainFrom(t, { unit: 0, loc: 'lm1', addr: 0, line: 1 });
  assert.equal(chain.length, 2);
  assert.equal(chain[0].line, 1);
  assert.equal(chain[0].inputs.length, 1);
  assert.equal(chain[0].inputs[0].loc, 'aluf');
  assert.equal(chain[1].line, 0);
  assert.equal(chain[1].expr, 'expr 0');
});

test('a forwarding read resolves to the earlier expression that updated it', () => {
  const t = trace([
    [access({ expr: 0, unit: 0, cycle: 0, loc: 'out', write: true, words: [7, 7, 7, 7] })],
    [access({ expr: 0, unit: 0, cycle: 0, loc: 'aluf', write: false, words: [7, 7, 7, 7], slot: 0 })],
  ]);
  const chain = chainFrom(t, { unit: 0, loc: 'aluf', addr: null, cycle: 0, line: 1 });
  assert.equal(chain.length, 1);
  assert.equal(chain[0].line, 0);
  assert.equal(chain[0].write.loc, 'out');
});

test('T addresses are cycles: a write at cycle 0 does not cover cycle 1', () => {
  const t = trace([[access({ expr: 0, unit: 0, cycle: 0, loc: 't', write: true, addr: 0, words: [1, 2, 3, 4] })]]);
  assert.equal(chainFrom(t, { unit: 0, loc: 't', addr: 0, line: 0 }).length, 1);
  assert.equal(chainFrom(t, { unit: 0, loc: 't', addr: 1, line: 0 }).length, 0);
});

test('L1BM addresses are long words: a two-word transfer covers one address', () => {
  const t = trace([[access({ expr: 0, unit: 0, cycle: 0, loc: 'l1bm', write: true, addr: 4, words: [1, 2] })]]);
  assert.equal(chainFrom(t, { unit: 0, loc: 'l1bm', addr: 4, line: 0 }).length, 1);
  assert.equal(chainFrom(t, { unit: 0, loc: 'l1bm', addr: 5, line: 0 }).length, 0);
});

test('a memory read is observed before the line that reads it', () => {
  const t = trace([
    [access({ expr: 0, unit: 0, cycle: 0, loc: 'lm0', write: true, addr: 0, words: [1, 2] })],
    [
      access({ expr: 0, unit: 0, cycle: 0, loc: 'lm0', write: false, addr: 0, words: [1, 2], slot: 0 }),
      access({ expr: 0, unit: 0, cycle: 0, loc: 'lm1', write: true, addr: 0, words: [3, 4] }),
    ],
  ]);
  // Looking at the second line's destination still finds its input; a source read is
  // observed before the line that reads it, so it starts from the state before line 0.
  assert.equal(chainFrom(t, { unit: 0, loc: 'lm1', addr: 0, line: 1 }).length, 2);
  assert.equal(chainFrom(t, { unit: 0, loc: 'lm0', addr: 0, line: -1 }).length, 0);
});
