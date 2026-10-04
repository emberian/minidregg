// Byte-for-byte differential: the TS SDK against the FRESHLY BUILT wasm of the Rust offline core,
// on the golden inputs AND on mutated/adversarial inputs the golden file does not hold. Each case
// also asserts its mutation actually changed the input (a falsifier that stopped falsifying is a
// green that means nothing).
import { test } from "node:test";
import assert from "node:assert/strict";
import { canonicalJson, derive, explain, hex, intentBytes, invocationId, lower, signRaw, unhex, sha256, headersDigest, confirmDigest } from "../src/index.ts";
import { fixture, golden as g, oracle } from "./oracle.ts";

const both = (ts: () => string, rs: () => string) => {
  let a: string | Error, b: string | Error;
  try { a = ts(); } catch (x) { a = x as Error; }
  try { b = rs(); } catch (x) { b = new Error(String(x)); }
  if (a instanceof Error || b instanceof Error) {
    assert.ok(a instanceof Error && b instanceof Error, `one side refused, the other did not: ts=${a} rs=${b}`);
    return "refused";
  }
  assert.equal(a, b);
  return a;
};
const clone = <T>(v: T): T => structuredClone(v);

test("derive + sign across paths and messages", () => {
  for (const path of ["dregg/0", "mini/0", "mini/7", "mini/4294967295", "other"]) {
    assert.equal(hex(derive(unhex(g.seed), path).publicKey), oracle.derivePublic(g.seed, path), path);
    for (const m of ["", "00", "02ff9dff".repeat(50)]) {
      assert.equal(hex(signRaw(derive(unhex(g.seed), path), unhex(m))), oracle.signRaw(g.seed, path, m));
    }
  }
});

test("canonical JSON: key order is UTF-8 byte order, escapes match serde_json", () => {
  const cases = [
    { "ｚ": 1, "😀": 2, "z": 3, "é": 4, "": 5, "A": [true, false, null] },
    { s: "\u0000\u0007\b\t\n\f\r\u001b\u007f \"\\/ünï😀" },
    { n: [0, -1, 9007199254740992, -9007199254740992] },
  ];
  for (const c of cases) both(() => canonicalJson(c as never), () => oracle.canonicalJson(JSON.stringify(c)));
  // UTF-16 order would put 😀 before ｚ; UTF-8 order puts ｚ first.
  assert.ok(canonicalJson(cases[0] as never).indexOf("ｚ") < canonicalJson(cases[0] as never).indexOf("😀"));
  for (const bad of [{ f: 1.5 }, { big: 2 ** 53 + 2 }]) {
    assert.equal(both(() => canonicalJson(bad as never), () => oracle.canonicalJson(JSON.stringify(bad))), "refused");
  }
});

test("intent bytes and InvocationId under mutation, including refusals", () => {
  for (const row of g.intents) {
    const base = row.intent;
    const variants: unknown[] = [base];
    const salt = clone(base); salt.salt = "ff" + base.salt.slice(2); variants.push(salt);
    const actor = clone(base); actor.actor = "18446744073709551615"; variants.push(actor);
    const lead = clone(base); lead.actor = "07"; variants.push(lead); // noncanonical decimal: both refuse
    const upper = clone(base); upper.salt = base.salt.toUpperCase(); variants.push(upper); // both refuse
    if (base.cut === "invoke") {
      const fam = clone(base); fam.family = { route: "roomPublish", context: "" }; variants.push(fam);
      const badRoute = clone(base); badRoute.family = { route: "root", context: "00" }; variants.push(badRoute);
      const none = clone(base); none.targets = []; variants.push(none);
      const uni = clone(base); uni.targets[0].payload = { type: "content", actions: [{ type: "createAtom", atom: "1", kind: { type: "text" }, payload: "f09f9880", "ｚ": "😀" }] }; variants.push(uni);
    }
    let distinct = new Set<string>();
    for (const v of variants) {
      const s = JSON.stringify(v);
      const b = both(() => hex(intentBytes(v as never)), () => oracle.intentBytes(s));
      both(() => invocationId(v as never), () => oracle.invocationId(s));
      distinct.add(b);
    }
    assert.ok(distinct.size >= 3, `${row.name}: mutations did not change the bytes`);
  }
});

test("lowering, including refusals", () => {
  for (const row of g.intents) {
    for (const ctx of [g.lowering.context, { ...g.lowering.context, domain: "9" }, { ...g.lowering.context, commandNonce: "1" }]) {
      both(() => canonicalJson(lower(row.intent, ctx)), () => oracle.lowerIntent(JSON.stringify(row.intent), JSON.stringify(ctx)));
    }
  }
});

test("explain text on the real fixture and on adversarial mutations", () => {
  const intent = fixture("intent.json");
  const plan = fixture("plan.json");
  const d = ["11".repeat(32), "22".repeat(32), "33".repeat(32)];
  const mutate: Array<[string, (i: any, p: any) => void]> = [
    ["none", () => {}],
    ["extra intent field", (i) => { i.zz = { nested: [1, "x"] }; }],
    ["unknown action", (i) => { i.purpose.draft.command.targets[0].payload.actions[0].type = "launch"; }],
    ["unknown payload", (i) => { i.purpose.draft.command.targets[1].payload = { type: "teleport", to: "mars" }; }],
    ["non-hex payload", (i) => { i.purpose.draft.command.targets[0].payload.actions[0].payload = "XYZ"; }],
    ["control text", (i) => { i.purpose.draft.command.targets[0].payload.actions[0].payload = "0a07"; }],
    ["C1 control text", (i) => { i.purpose.draft.command.targets[0].payload.actions[0].payload = "c285"; }],
    ["non-UTF-8", (i) => { i.purpose.draft.command.targets[0].payload.actions[0].payload = "ff"; }],
    ["empty payload", (i) => { i.purpose.draft.command.targets[0].payload.actions[0].payload = ""; }],
    ["quote text", (i) => { i.purpose.draft.command.targets[0].payload.actions[0].payload = "22e2809c5c"; }],
    ["family", (i) => { i.purpose.draft.command.family = { route: "objectiveMethod", contextBytes: "6869" }; }],
    ["null family", (i) => { i.purpose.draft.command.family = null; }],
    ["subject mismatch", (i) => { i.purpose.draft.command.subject = "1"; }],
    ["extra command field", (i) => { i.purpose.draft.command.run = { steps: 9 }; }],
    ["scalar payload", (i) => { i.purpose.draft.command.targets[0].payload = { type: "scalar", actions: [{ op: "add", n: 3 }] }; }],
    ["append payload", (i) => { i.purpose.draft.command.targets[0].payload = { type: "append", topic: "6869", payload: "", to: null, ref: null }; }],
    ["not an invoke", (i) => { i.purpose.type = "observe"; }],
    ["intent not an object", (i) => { for (const k of Object.keys(i)) delete i[k]; }],
    ["undecoded slot", (_, p) => { p.slots[2].signing.decoded = false; }],
    ["birth draft", (_, p) => { p.finalizedDraft.type = "birth"; }],
    ["no slots", (_, p) => { delete p.slots; }],
  ];
  const seen = new Set<string>();
  for (const [name, f] of mutate) {
    const i = clone(intent); const p = clone(plan); f(i, p);
    const ts = explain(i, p, { intentSha256: unhex(d[0]), planSha256: unhex(d[1]), headersSha256: unhex(d[2]) }).text;
    const rs = oracle.explainText(JSON.stringify(i), JSON.stringify(p), d[0], d[1], d[2]);
    assert.equal(ts, rs, name);
    assert.ok(!seen.has(ts), `${name}: mutation did not change the reading`);
    seen.add(ts);
  }
});

test("headers and confirmation digests", () => {
  for (const l of [["02ff"], ["", ""], Array.from({ length: 9 }, (_, i) => "ab".repeat(i))]) {
    assert.equal(hex(headersDigest(l.map(unhex))), oracle.headersDigest(JSON.stringify(l)));
  }
  const c = g.confirm;
  for (const attempt of [0, 1, 4294967295]) {
    assert.equal(hex(confirmDigest(unhex(c.invocation), attempt, unhex(c.intentSha256), unhex(c.planSha256), unhex(c.headersSha256),
      unhex(c.explanationSha256), unhex(c.nonce))),
      oracle.confirmDigest(c.invocation, attempt, c.intentSha256, c.planSha256, c.headersSha256, c.explanationSha256, c.nonce));
  }
  assert.equal(hex(sha256(new Uint8Array())), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
});
