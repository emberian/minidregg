// Named identities. Bread's store and derivation function; Mini's path family `mini/<generation>`.
// blake3 derive_key(path, seed64) → Ed25519 seed (RFC 8032). See docs/design/SDK-DESIGN.md §9.
import * as ed from "@noble/ed25519";
import { blake3 } from "@noble/hashes/blake3";
import { sha512 } from "@noble/hashes/sha512";
import { hex, SdkError, unhex } from "./bytes.ts";
import { call } from "./core.ts";

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

/** Key schemes; the codes are the key record's algorithm codes (native/mini-sdk/src/signer.rs). */
export const SCHEMES = { "ed25519": 1, "hybrid-ed25519-ml-dsa-65": 2 } as const;
export type Scheme = keyof typeof SCHEMES;
export const PUBLIC_KEY_LEN: Record<Scheme, number> = { "ed25519": 32, "hybrid-ed25519-ml-dsa-65": 32 + 1952 };
export const SIGNATURE_LEN: Record<Scheme, number> = { "ed25519": 64, "hybrid-ed25519-ml-dsa-65": 64 + 3309 };

/** A signing key of some scheme; the one interface every signing path takes. */
export interface Signer {
  readonly scheme: Scheme;
  /** The public key in the scheme's wire layout (hybrid: ed[32] || ml[1952]). */
  readonly publicKey: Uint8Array;
  sign(message: Uint8Array): Uint8Array;
}

export function ed25519Signer(key: Key): Signer {
  return { scheme: "ed25519", publicKey: key.publicKey, sign: (m) => signRaw(key, m) };
}

/** Verify in the scheme's wire layout. A hybrid signature verifies only if BOTH halves do;
 * the thrown `SdkError` names the half that failed. */
export function verify(scheme: Scheme, publicKey: Uint8Array, message: Uint8Array, signature: Uint8Array): void {
  call((c) => c.signerVerify(SCHEMES[scheme], hex(publicKey), hex(message), hex(signature)));
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
  /** The Mini signer of `generation` under `scheme`. The hybrid's keys are derived and used
   * inside the Rust core (one ML-DSA-65 implementation, shared with native). */
  signer(generation: number, scheme: Scheme = "ed25519"): Signer {
    if (scheme === "ed25519") return ed25519Signer(this.miniKey(generation));
    miniPath(generation);
    const seedHex = hex(this.#seed);
    const code = SCHEMES[scheme];
    return {
      scheme,
      publicKey: unhex(call((c) => c.signerPublic(seedHex, generation, code))),
      sign: (m) => unhex(call((c) => c.signerSign(seedHex, generation, code, hex(m)))),
    };
  }
}
