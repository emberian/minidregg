// Typed intents over the SHARED-CONTRACTS cuts. The canonical bytes are DEFINED in Lean
// (Kernel/Contracts/Intents.lean, frame DREGG/CONTRACT/INTENT/v1) and implemented once, in
// native/mini-sdk (Rust), which this module reaches through the wasm core: there is no TS encoder.
// The byte layout is documented in native/mini-sdk/src/contracts.rs.
import { SdkError, unhex } from "./bytes.ts";
import { call } from "./core.ts";

export type Json = null | boolean | number | string | Json[] | { [k: string]: Json };
export interface ObjectRef { id: string; domain: string; kind: string }
export interface RevisionRef { object: ObjectRef; root: string }
export interface ArtifactRef { sha256: string; length: number; format: string }
export interface InvokeTarget { revision: RevisionRef; capability: string; observeCapability: string; schemaVersion: string; payload: Json }
export interface Family { route: string; context: string }

interface Base { actor: string; salt: string }
export type Intent = Base & (
  | { cut: "observe"; resource: RevisionRef; projection: string; capability: string }
  | { cut: "invoke"; targets: InvokeTarget[]; family: Family | null }
  | { cut: "reserve"; candidate: ArtifactRef; footprint: ObjectRef[]; law: ArtifactRef; obligation: ArtifactRef }
  | { cut: "install"; candidate: ArtifactRef; preimage: RevisionRef; effects: ArtifactRef; obligation: ArtifactRef }
  | { cut: "release"; result: ArtifactRef; audience: string[]; law: ArtifactRef }
  | { cut: "retire"; obligation: ArtifactRef; evidence: ArtifactRef }
);

export interface Lowering { domain: string; intentNonce: string; commandNonce: string }

const spell = (i: Intent): string => {
  // JSON numbers beyond 2^53 are already rounded by JavaScript; payloads carry big values as decimal strings.
  const text = JSON.stringify(i);
  if (text === undefined) throw new SdkError("intent is not JSON");
  return text;
};

/** Sorted keys (UTF-8 byte order), no whitespace, integers of magnitude <= 2^53 only. */
export function canonicalJson(v: Json): string {
  return call((c) => c.canonicalJson(JSON.stringify(v)));
}

/** The Lean codec's bytes of the intent (`intentCodec.encode`). */
export function intentBytes(i: Intent): Uint8Array {
  return unhex(call((c) => c.intentBytes(spell(i))));
}

/** The bytes hashed into the `InvocationId` (`intentIdPreimage`). */
export function intentIdPreimage(i: Intent): Uint8Array {
  return unhex(call((c) => c.intentIdPreimage(spell(i))));
}

/** SHA-256 of the id preimage, hex: the client's stable name for this one request. */
export function invocationId(i: Intent): string {
  return call((c) => c.invocationId(spell(i)));
}

/** The authoring JSON Host op 7 reads. Only `invoke` has a common native wire. */
export function lower(i: Intent, ctx: Lowering): Json {
  return JSON.parse(call((c) => c.lowerIntent(spell(i), JSON.stringify(ctx)))) as Json;
}
