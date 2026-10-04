// Hex, decimals, length-prefixed writers and SHA-256 — the byte layer every module shares.
import { sha256 as nobleSha256 } from "@noble/hashes/sha256";

export class SdkError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "MiniSdkError";
  }
}

const DIGITS = "0123456789abcdef";

export function hex(bytes: Uint8Array): string {
  let out = "";
  for (const b of bytes) out += DIGITS[b >> 4] + DIGITS[b & 15];
  return out;
}

/** Strict lowercase hex (the Host's canonical spelling). */
export function unhex(text: string): Uint8Array {
  if (text.length % 2 !== 0) throw new SdkError("hex has odd length");
  if (!/^[0-9a-f]*$/.test(text)) throw new SdkError("hex must be canonical lowercase");
  const out = new Uint8Array(text.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(text.slice(2 * i, 2 * i + 2), 16);
  return out;
}

export function isDecimal(text: string): boolean {
  return /^(0|[1-9][0-9]*)$/.test(text);
}

export function sha256(bytes: Uint8Array): Uint8Array {
  return nobleSha256(bytes);
}

export const utf8 = (s: string): Uint8Array => new TextEncoder().encode(s);

export function concat(...parts: Uint8Array[]): Uint8Array {
  const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
  let at = 0;
  for (const p of parts) {
    out.set(p, at);
    at += p.length;
  }
  return out;
}

export function u32le(n: number): Uint8Array {
  if (!Number.isInteger(n) || n < 0 || n > 0xffffffff) throw new SdkError("field exceeds u32 length");
  const b = new Uint8Array(4);
  new DataView(b.buffer).setUint32(0, n, true);
  return b;
}

export function u64le(n: number): Uint8Array {
  if (!Number.isInteger(n) || n < 0 || n > 2 ** 53) throw new SdkError("length must be an integer ≤ 2^53");
  const b = new Uint8Array(8);
  new DataView(b.buffer).setBigUint64(0, BigInt(n), true);
  return b;
}

/** Byte-order comparison of two strings' UTF-8 encodings (serde_json's BTreeMap order). */
export function utf8Compare(a: string, b: string): number {
  const x = utf8(a);
  const y = utf8(b);
  for (let i = 0; i < Math.min(x.length, y.length); i++) if (x[i] !== y[i]) return x[i] - y[i];
  return x.length - y.length;
}

export function equalBytes(a: Uint8Array, b: Uint8Array): boolean {
  return a.length === b.length && a.every((v, i) => v === b[i]);
}
