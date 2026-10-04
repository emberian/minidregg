// Typed intents over the SHARED-CONTRACTS cuts, canonical bytes and InvocationId.
// Byte-for-byte mirror of native/mini-sdk/src/contracts.rs (the encoding is documented there).
// TODO(W2.A): replace with the Lean contract codec's golden vectors when W2.A lands.
import { concat, hex, isDecimal, sha256, SdkError, u32le, u64le, unhex, utf8, utf8Compare } from "./bytes.ts";

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

export const INTENT_DOMAIN = utf8("MINI/SDK/INTENT/v1");
export const INVOCATION_DOMAIN = utf8("MINI/SDK/INVOCATION-ID/v1");
export const ROUTES = ["ordinary", "objectiveMethod", "activityDispatch", "roomRelease", "roomPublish"];
const TAGS = { observe: 1, invoke: 2, reserve: 3, install: 4, release: 5, retire: 6 } as const;

/** Sorted keys (UTF-8 byte order), no whitespace, integers of magnitude ≤ 2^53 only. */
export function canonicalJson(v: Json): string {
  if (v === null || typeof v === "boolean") return JSON.stringify(v);
  if (typeof v === "number") {
    if (!Number.isInteger(v) || Math.abs(v) > 2 ** 53) {
      throw new SdkError("canonical JSON admits only integers of magnitude ≤ 2^53; use a decimal string");
    }
    return String(v === 0 ? 0 : v);
  }
  if (typeof v === "string") return JSON.stringify(v);
  if (Array.isArray(v)) return `[${v.map(canonicalJson).join(",")}]`;
  const keys = Object.keys(v).sort(utf8Compare);
  return `{${keys.map((k) => `${JSON.stringify(k)}:${canonicalJson(v[k])}`).join(",")}}`;
}

class W {
  parts: Uint8Array[] = [];
  raw(b: Uint8Array) { this.parts.push(b); }
  bytes(b: Uint8Array) { this.raw(u32le(b.length)); this.raw(b); }
  str(s: string) { this.bytes(utf8(s)); }
  dec(s: string) {
    if (typeof s !== "string" || !isDecimal(s)) throw new SdkError(`${JSON.stringify(s)} is not a canonical decimal`);
    this.str(s);
  }
  object(o: ObjectRef) { this.dec(o.id); this.dec(o.domain); this.str(o.kind); }
  revision(r: RevisionRef) { this.object(r.object); this.dec(r.root); }
  artifact(a: ArtifactRef) {
    const sha = unhex(a.sha256);
    if (sha.length !== 32) throw new SdkError("sha256 must be 32 bytes");
    this.raw(sha); this.raw(u64le(a.length)); this.str(a.format);
  }
  list<T>(xs: T[], f: (x: T) => void) { this.raw(u32le(xs.length)); xs.forEach(f); }
}

export function intentBytes(i: Intent): Uint8Array {
  const w = new W();
  w.raw(INTENT_DOMAIN);
  const salt = unhex(i.salt);
  if (salt.length !== 16) throw new SdkError("salt must be 16 bytes");
  w.raw(salt);
  w.dec(i.actor);
  const tag = TAGS[i.cut];
  if (!tag) throw new SdkError(`unknown cut ${JSON.stringify(i.cut)}`);
  w.raw(Uint8Array.of(tag));
  switch (i.cut) {
    case "observe": w.revision(i.resource); w.str(i.projection); w.dec(i.capability); break;
    case "invoke":
      if (i.targets.length === 0) throw new SdkError("an invocation names at least one target");
      w.list(i.targets, (t) => {
        w.revision(t.revision); w.dec(t.capability); w.dec(t.observeCapability); w.dec(t.schemaVersion);
        w.str(canonicalJson(t.payload));
      });
      if (i.family === null) w.raw(Uint8Array.of(0));
      else {
        if (!ROUTES.includes(i.family.route)) throw new SdkError(`unknown invocation family route ${JSON.stringify(i.family.route)}`);
        w.raw(Uint8Array.of(1)); w.str(i.family.route); w.bytes(unhex(i.family.context));
      }
      break;
    case "reserve": w.artifact(i.candidate); w.list(i.footprint, (o) => w.object(o)); w.artifact(i.law); w.artifact(i.obligation); break;
    case "install": w.artifact(i.candidate); w.revision(i.preimage); w.artifact(i.effects); w.artifact(i.obligation); break;
    case "release": w.artifact(i.result); w.list(i.audience, (d) => w.dec(d)); w.artifact(i.law); break;
    case "retire": w.artifact(i.obligation); w.artifact(i.evidence); break;
  }
  return concat(...w.parts);
}

/** SHA-256("MINI/SDK/INVOCATION-ID/v1" ‖ canonical intent), hex. */
export function invocationId(i: Intent): string {
  return hex(sha256(concat(INVOCATION_DOMAIN, intentBytes(i))));
}

/** The authoring JSON Host op 7 reads. Only `invoke` has a common native wire. */
export function lower(i: Intent, ctx: Lowering): Json {
  if (i.cut !== "invoke") {
    throw new SdkError(`${i.cut} has no common native wire yet (SHARED-CONTRACTS cut without a source counterpart); not lowered`);
  }
  for (const d of [ctx.domain, ctx.intentNonce, ctx.commandNonce]) if (!isDecimal(d)) throw new SdkError("lowering needs canonical decimals");
  const grants: Json[] = [];
  const wire: Json[] = [];
  for (const t of i.targets) {
    const o = t.revision.object;
    if (o.domain !== ctx.domain) throw new SdkError(`target ${o.id} is governed by domain ${o.domain}, not this deployment's ${ctx.domain}`);
    grants.push({ capability: t.observeCapability, kind: o.kind, target: o.id });
    wire.push({ capability: t.capability, expectedTargetRoot: t.revision.root, kind: o.kind, observeCapability: t.observeCapability,
      payload: t.payload, schemaVersion: t.schemaVersion, target: o.id });
  }
  const command: { [k: string]: Json } = { nonce: ctx.commandNonce, subject: i.actor, targets: wire };
  if (i.family !== null) command.family = { route: i.family.route, contextBytes: i.family.context };
  return { grants, nonce: ctx.intentNonce, purpose: { draft: { command, type: "invoke" }, type: "prepare" }, subject: i.actor };
}
