// Named identities. Bread's store and derivation function; Mini's path family `mini/<generation>`.
// blake3 derive_key(path, seed64) → Ed25519 seed (RFC 8032). See docs/design/SDK-DESIGN.md §9.
import * as ed from "@noble/ed25519";
import { blake3 } from "@noble/hashes/blake3";
import { sha512 } from "@noble/hashes/sha512";
import { SdkError } from "./bytes.ts";

ed.etc.sha512Sync = (...m: Uint8Array[]) => sha512(ed.etc.concatBytes(...m));

export const BREAD_PATH = "dregg/0";
export const miniPath = (generation: number): string => {
  if (!Number.isInteger(generation) || generation < 0 || generation > 0xffffffff) throw new SdkError("generation must be a u32");
  return `mini/${generation}`;
};

export interface Key {
  /** 32-byte Ed25519 secret seed. Key material. */
  readonly secret: Uint8Array;
  readonly publicKey: Uint8Array;
}

export function derive(seed: Uint8Array, path: string): Key {
  if (seed.length !== 64) throw new SdkError("seed must be 64 bytes");
  const secret = blake3(seed, { context: path });
  return { secret, publicKey: ed.getPublicKey(secret) };
}

export function signRaw(key: Key, message: Uint8Array): Uint8Array {
  return ed.sign(message, key.secret);
}

export function validateName(name: string): void {
  if (!/^[A-Za-z0-9_-]{1,64}$/.test(name)) throw new SdkError(`${JSON.stringify(name)} is not a profile name`);
}

export class Profile {
  readonly name: string;
  readonly #seed: Uint8Array;
  constructor(name: string, seed: Uint8Array) {
    validateName(name);
    if (seed.length !== 64) throw new SdkError("seed must be 64 bytes");
    this.name = name;
    this.#seed = seed.slice();
  }
  miniKey(generation: number): Key {
    return derive(this.#seed, miniPath(generation));
  }
}
