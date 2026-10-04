// The Rust core (native/mini-sdk, feature `wasm`, built by `npm run build:core`): the ONE
// implementation of the intent encoder, canonical JSON, lowering and the hybrid ML-DSA-65
// scheme. The TS SDK holds no second copy of these; it spells the JSON in, the core answers.
// There is no fallback: a missing core throws, because a signer that silently used a different
// encoder would sign bytes the Host never admits.
import { createRequire } from "node:module";
import { SdkError } from "./bytes.ts";

/** The wasm-bindgen exports (`native/mini-sdk/src/wasm.rs`). Hex in, hex out; refusals throw strings. */
export interface Core {
  derivePublic(seedHex: string, path: string): string;
  signRaw(seedHex: string, path: string, messageHex: string): string;
  canonicalJson(json: string): string;
  intentBytes(intent: string): string;
  intentIdPreimage(intent: string): string;
  invocationId(intent: string): string;
  lowerIntent(intent: string, lowering: string): string;
  headersDigest(headersJson: string): string;
  explainText(intentJson: string, planJson: string, intentSha: string, planSha: string, headersSha: string): string;
  confirmDigest(invocation: string, attempt: number, intentSha: string, planSha: string, headersSha: string,
    explanationSha: string, nonceHex: string): string;
  signerPublic(seedHex: string, generation: number, scheme: number): string;
  signerSign(seedHex: string, generation: number, scheme: number, messageHex: string): string;
  signerVerify(scheme: number, publicHex: string, messageHex: string, signatureHex: string): void;
}

let installed: Core | undefined;

/** Install a core built for another host (a bundler or browser build of the same wasm). */
export function installCore(core: Core): void {
  installed = core;
}

/** The core: the one installed, else the node build next to this package (`wasm/mini_sdk.js`). */
export function core(): Core {
  if (installed) return installed;
  const path = new URL("../wasm/mini_sdk.js", import.meta.url).pathname;
  try {
    installed = createRequire(import.meta.url)(path) as Core;
  } catch (e) {
    throw new SdkError(`the Rust core is not available at ${path} (run npm run build:core): ${(e as Error).message}`);
  }
  return installed;
}

/** Call into the core, turning its thrown strings into `SdkError`. */
export function call<T>(f: (c: Core) => T): T {
  try {
    return f(core());
  } catch (e) {
    if (e instanceof SdkError) throw e;
    throw new SdkError(typeof e === "string" ? e : (e as Error).message);
  }
}
