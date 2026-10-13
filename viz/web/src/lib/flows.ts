// Categories of chip-level flows, shared by the timeline and the chip view.
export const CATEGORY_COLORS: Record<string, string> = {
  offchip: 'var(--c-offchip)',
  l2: 'var(--c-l2)',
  l1: 'var(--c-l1)',
  compute: 'var(--c-compute)',
};

export const CATEGORY_NAMES: Record<string, string> = {
  offchip: 'DRAM/PDM',
  l2: 'L2BM',
  l1: 'L1BM',
  compute: 'PE 演算',
};

export function category(from: string, to: string): string {
  if (from === 'dram' || from === 'pdm' || to === 'dram' || to === 'pdm') return 'offchip';
  if (from === 'l2bm' || to === 'l2bm') return 'l2';
  if (from === 'l1bm' || to === 'l1bm') return 'l1';
  return 'compute';
}
