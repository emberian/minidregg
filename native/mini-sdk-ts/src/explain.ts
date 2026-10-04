// explain(): the faithful reading of what a key is about to sign, over Host-PRESENTED JSON only.
// Byte-identical text to native/mini-sdk/src/explain.rs (differentially tested against its wasm build).
import { hex, unhex, utf8Compare } from "./bytes.ts";
import { canonicalJson, type Json } from "./contracts.ts";

export const PAYLOAD_TYPES = ["scalar", "content", "append", "world", "kindDefinition", "computeFunding", "read"];
export const CONTENT_ACTIONS = ["createDocument", "createContainer", "editElement", "createAtom", "createRun", "editAtom", "link",
  "annotate", "rewrapAtom", "rewrapAnnotation", "unlink", "mark", "unmark", "transclude"];
const HEX_FIELDS = ["payload", "wrapping", "topic", "contextBytes"];
const UNKNOWN = "UNKNOWN";
const BLIND = "do not sign blind";

export interface Bound { intentSha256: Uint8Array; planSha256: Uint8Array; headersSha256: Uint8Array }
export interface Explanation { lines: string[]; text: string; hasUnknown: boolean }

type Obj = { [k: string]: Json };
const isObj = (v: Json | undefined): v is Obj => typeof v === "object" && v !== null && !Array.isArray(v);
/** serde_json `Value[key]`: Null unless an object holding the key. */
const at = (v: Json | undefined, k: string): Json => (isObj(v) && Object.hasOwn(v, k) ? v[k] : null);
const quote = (s: string): string => JSON.stringify(s);
const sortedKeys = (o: Obj): string[] => Object.keys(o).sort(utf8Compare);
const same = (a: Json, b: Json): boolean => {
  try { return canonicalJson(a) === canonicalJson(b); } catch { return false; }
};

function strOf(v: Json): string {
  if (typeof v === "string") return v;
  try { return canonicalJson(v); } catch { return "<non-canonical JSON>"; }
}

function hexField(text: string): string {
  let bytes: Uint8Array;
  try { bytes = unhex(text); } catch { return `${UNKNOWN} non-hex ${quote(text)} — ${BLIND}`; }
  let readable: string | null = null;
  try {
    const s = new TextDecoder("utf-8", { fatal: true }).decode(bytes);
    if (!/[\u0000-\u001f\u007f-\u009f]/.test(s)) readable = s;
  } catch { /* not UTF-8 */ }
  if (readable !== null && bytes.length > 0) return `0x${text} (${bytes.length} bytes, text ${quote(readable)})`;
  return `0x${text} (${bytes.length} bytes)`;
}

function fields(o: Obj, skip: string[]): string {
  const out: string[] = [];
  for (const k of sortedKeys(o)) {
    if (skip.includes(k)) continue;
    const v = o[k];
    out.push(`${k}=${HEX_FIELDS.includes(k) && typeof v === "string" ? hexField(v) : strOf(v)}`);
  }
  return out.join(" ");
}

function payloadLines(payload: Json, lines: string[]): void {
  if (!isObj(payload)) { lines.push(`    ${UNKNOWN} payload ${strOf(payload)} — ${BLIND}`); return; }
  const tv = payload.type;
  const ty = typeof tv === "string" ? tv : "";
  if (!PAYLOAD_TYPES.includes(ty)) { lines.push(`    ${UNKNOWN} payload type ${quote(ty)}: ${strOf(payload)} — ${BLIND}`); return; }
  const actions = Array.isArray(payload.actions) ? payload.actions : null;
  if (ty === "content" && actions) {
    lines.push(`    content: ${actions.length} action(s)`);
    for (const action of actions) {
      if (!isObj(action)) { lines.push(`      ${UNKNOWN} action ${strOf(action)} — ${BLIND}`); continue; }
      const verb = typeof action.type === "string" ? action.type : "";
      if (CONTENT_ACTIONS.includes(verb)) lines.push(`      ${verb} ${fields(action, ["type"])}`);
      else lines.push(`      ${UNKNOWN} content action ${quote(verb)}: ${strOf(action)} — ${BLIND}`);
    }
  } else if (ty === "scalar" && actions) {
    lines.push(`    scalar: ${actions.length} action(s)`);
    for (const action of actions) lines.push(`      ${strOf(action)}`);
  } else {
    lines.push(`    ${ty}: ${fields(payload, ["type"])}`);
  }
}

function intentLines(intent: Json, lines: string[]): void {
  const expect = ["grants", "nonce", "purpose", "subject"];
  if (!isObj(intent)) { lines.push(`${UNKNOWN} intent ${strOf(intent)} — ${BLIND}`); return; }
  for (const k of sortedKeys(intent)) {
    if (!expect.includes(k)) lines.push(`${UNKNOWN} intent field ${quote(k)}=${strOf(intent[k])} — ${BLIND}`);
  }
  const purpose = at(intent, "purpose");
  const draft = at(purpose, "draft");
  const command = at(draft, "command");
  if (at(purpose, "type") !== "prepare" || at(draft, "type") !== "invoke" || !isObj(command)) {
    lines.push(`${UNKNOWN} purpose ${strOf(purpose)} — ${BLIND}`);
    return;
  }
  lines.push(`invoke by subject ${strOf(at(intent, "subject"))} (intent nonce ${strOf(at(intent, "nonce"))}, command nonce ${strOf(at(command, "nonce"))})`);
  if (!same(at(command, "subject"), at(intent, "subject"))) {
    lines.push(`${UNKNOWN} command subject ${strOf(at(command, "subject"))} differs from intent subject — ${BLIND}`);
  }
  for (const k of sortedKeys(command)) {
    if (!["nonce", "subject", "targets", "family"].includes(k)) lines.push(`${UNKNOWN} command field ${quote(k)}=${strOf(command[k])} — ${BLIND}`);
  }
  const grants = at(intent, "grants");
  if (Array.isArray(grants)) {
    for (const g of grants) lines.push(`  observes ${strOf(at(g, "kind"))} ${strOf(at(g, "target"))} with capability ${strOf(at(g, "capability"))}`);
  }
  const targets = at(command, "targets");
  for (const t of Array.isArray(targets) ? targets : []) {
    lines.push(`  writes ${strOf(at(t, "kind"))} ${strOf(at(t, "target"))} at expected root ${strOf(at(t, "expectedTargetRoot"))} with capability ${strOf(at(t, "capability"))} (observe ${strOf(at(t, "observeCapability"))}), schema ${strOf(at(t, "schemaVersion"))}`);
    payloadLines(at(t, "payload"), lines);
  }
  if (Object.hasOwn(command, "family")) {
    const f = command.family;
    const ctx = at(f, "contextBytes");
    lines.push(`  family route ${strOf(at(f, "route"))} context ${hexField(typeof ctx === "string" ? ctx : "?")}`);
  }
}

function planLines(plan: Json, lines: string[]): void {
  const draft = at(plan, "finalizedDraft");
  lines.push(`plan at height ${strOf(at(plan, "height"))} world root ${strOf(at(plan, "worldRoot"))} domain ${strOf(at(plan, "domain"))}: draft ${strOf(at(draft, "type"))}`);
  if (at(draft, "type") !== "invoke") lines.push(`${UNKNOWN} plan draft type ${strOf(at(draft, "type"))} for an invoke intent — ${BLIND}`);
  const slotsV = at(plan, "slots");
  const slots = Array.isArray(slotsV) ? slotsV : [];
  lines.push(`  ${slots.length} signature slot(s)`);
  for (const s of slots) {
    const g = at(s, "signing");
    const fp = at(g, "footprint");
    lines.push(`  role ${strOf(at(s, "role"))} slot ${strOf(at(s, "index"))}: key ${strOf(at(g, "keyId"))} epoch ${strOf(at(g, "keyEpoch"))} valid until height ${strOf(at(g, "validUntil"))}, ${Array.isArray(fp) ? fp.length : 0} footprint cell(s)`);
    if (at(g, "decoded") !== true) lines.push(`  ${UNKNOWN} role ${strOf(at(s, "role"))} slot ${strOf(at(s, "index"))} is not decoded by the local Host — ${BLIND}`);
  }
}

export function explain(intent: Json, plan: Json, bound: Bound): Explanation {
  const lines: string[] = [];
  intentLines(intent, lines);
  planLines(plan, lines);
  lines.push(`bound to [intent ${hex(bound.intentSha256)}] [plan ${hex(bound.planSha256)}] [headers ${hex(bound.headersSha256)}]`);
  return { lines, text: lines.join("\n") + "\n", hasUnknown: lines.some((l) => l.trimStart().startsWith(UNKNOWN)) };
}
