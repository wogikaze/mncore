// Formatting of MN-Core 2 words. Half precision is sign 1 / exponent 6 / mantissa 9 (not IEEE).

export type View = 'hex' | 'f32' | 'f64' | 'f16' | 'i32';

export function hex(w: number): string {
  return (w >>> 0).toString(16).padStart(8, '0');
}

const buf = new DataView(new ArrayBuffer(8));

export function f32(w: number): number {
  buf.setUint32(0, w >>> 0);
  const exp = (w >>> 23) & 0xff;
  // MN-Core has no subnormals or NaN: exponent 0 is zero, all ones is infinity.
  if (exp === 0) return (w >>> 31) ? -0 : 0;
  if (exp === 0xff) return (w >>> 31) ? -Infinity : Infinity;
  return buf.getFloat32(0);
}

export function f64(hi: number, lo: number): number {
  buf.setUint32(0, hi >>> 0);
  buf.setUint32(4, lo >>> 0);
  const exp = (hi >>> 20) & 0x7ff;
  if (exp === 0) return (hi >>> 31) ? -0 : 0;
  if (exp === 0x7ff) return (hi >>> 31) ? -Infinity : Infinity;
  return buf.getFloat64(0);
}

/** MN-Core half precision: bias 31, 9 mantissa bits. */
export function f16(h: number): number {
  const s = (h >> 15) & 1 ? -1 : 1;
  const e = (h >> 9) & 0x3f;
  const m = h & 0x1ff;
  if (e === 0) return s * 0;
  if (e === 0x3f) return s * Infinity;
  return s * Math.pow(2, e - 31) * (1 + m / 512);
}

export function short(x: number): string {
  if (x === 0) return Object.is(x, -0) ? '-0' : '0';
  if (!isFinite(x)) return x > 0 ? '∞' : '-∞';
  const a = Math.abs(x);
  if (a >= 1e4 || a < 1e-2) return x.toExponential(1).replace('e+', 'e');
  return Number(x.toPrecision(4)).toString();
}

/** Formats a sequence of words in the given view; returns one string per element. */
export function format(words: number[], view: View): string[] {
  switch (view) {
    case 'hex':
      return words.map(hex);
    case 'f32':
      return words.map((w) => short(f32(w)));
    case 'i32':
      return words.map((w) => String(w | 0));
    case 'f64': {
      const out: string[] = [];
      for (let i = 0; i + 1 < words.length; i += 2) out.push(short(f64(words[i], words[i + 1])));
      return out;
    }
    case 'f16':
      return words.flatMap((w) => [short(f16(w >>> 16)), short(f16(w & 0xffff))]);
  }
}

/** Compact human readable count of long words. */
export function volume(longs: number): string {
  const bytes = longs * 8;
  if (bytes >= 1 << 20) return `${(bytes / (1 << 20)).toFixed(1)} MiB`;
  if (bytes >= 1 << 10) return `${(bytes / (1 << 10)).toFixed(1)} KiB`;
  return `${bytes} B`;
}
