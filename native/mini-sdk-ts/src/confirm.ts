// What the member saw, the nonce-bound confirmation, and confirmation-gated signing.
// Mirror of native/mini-sdk/src/{confirm,sign}.rs.
import { concat, equalBytes, hex, sha256, SdkError, u32le, unhex, utf8 } from "./bytes.ts";
import type { Json } from "./contracts.ts";
import { explain, type Explanation } from "./explain.ts";
import { type Key, signRaw } from "./profile.ts";

export const HEADERS_DOMAIN = utf8("MINI/SDK/HEADERS/v1");
export const CONFIRM_DOMAIN = utf8("MINI/SDK/CONFIRM/v1");

export function headersDigest(headers: Uint8Array[]): Uint8Array {
  return sha256(concat(HEADERS_DOMAIN, u32le(headers.length), ...headers.flatMap((h) => [u32le(h.length), h])));
}

export function confirmDigest(invocation: Uint8Array, attempt: number, intentSha: Uint8Array, planSha: Uint8Array,
  headersSha: Uint8Array, explanationSha: Uint8Array, nonce: Uint8Array): Uint8Array {
  for (const d of [invocation, intentSha, planSha, headersSha, explanationSha]) if (d.length !== 32) throw new SdkError("expected 32-byte digests");
  if (nonce.length !== 16) throw new SdkError("nonce must be 16 bytes");
  return sha256(concat(CONFIRM_DOMAIN, invocation, u32le(attempt), intentSha, planSha, headersSha, explanationSha, nonce));
}

export interface Confirmation { digest: Uint8Array; nonce: Uint8Array }

export class Presented {
  readonly invocation: Uint8Array;
  readonly attempt: number;
  readonly intentBin: Uint8Array;
  readonly planBin: Uint8Array;
  readonly headers: Uint8Array[];
  readonly explanation: Explanation;

  /** `invocationId` hex; `intentJson` the retained authoring JSON; `planJson` the local Host's `inspect plan`;
   * `headers` exactly what consent op 222 returned for (intentBin, planBin). */
  constructor(invocationId: string, attempt: number, intentJson: Json, intentBin: Uint8Array, planJson: Json,
    planBin: Uint8Array, headers: Uint8Array[]) {
    if (headers.length === 0) throw new SdkError("consent returned no headers; nothing to sign");
    this.invocation = unhex(invocationId);
    this.attempt = attempt;
    this.intentBin = intentBin;
    this.planBin = planBin;
    this.headers = headers;
    this.explanation = explain(intentJson, planJson, {
      intentSha256: sha256(intentBin), planSha256: sha256(planBin), headersSha256: headersDigest(headers) });
  }

  digest(nonce: Uint8Array): Uint8Array {
    return confirmDigest(this.invocation, this.attempt, sha256(this.intentBin), sha256(this.planBin),
      headersDigest(this.headers), sha256(utf8(this.explanation.text)), nonce);
  }

  /** The member accepted this reading under a fresh one-shot nonce. */
  confirm(nonce: Uint8Array): Confirmation {
    return { digest: this.digest(nonce), nonce: nonce.slice() };
  }
}

/** Sign exactly the consented transaction headers, only under a confirmation of this presentation. */
export function signTransaction(key: Key, presented: Presented, confirmation: Confirmation): Uint8Array[] {
  if (!equalBytes(presented.digest(confirmation.nonce), confirmation.digest)) {
    throw new SdkError("confirmation is for a different presentation; nothing signed");
  }
  return presented.headers.map((h) => signRaw(key, h));
}

/** The JSON list the Host's `signatures` codec (op 9) reads. */
export const signaturesJson = (sigs: Uint8Array[]): string => JSON.stringify(sigs.map(hex));
