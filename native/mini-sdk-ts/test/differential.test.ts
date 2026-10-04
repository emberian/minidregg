// Byte-for-byte differential of what the TS SDK still carries natively (derivation, Ed25519, the
// explain text, the digests) against the FRESHLY BUILT wasm of the Rust offline core, on the golden
// inputs AND on mutated/adversarial inputs the golden file does not hold. Each case also asserts
// its mutation actually changed the input (a falsifier that stopped falsifying is a green that
// means nothing). The intent encoder, canonical JSON, lowering and hybrid scheme are NOT carried in
// TS: they are the core, so there is nothing to differ and the evidence is Lean's vectors
// (golden.test.ts).
import { test } from "node:test";
import assert from "node:assert/strict";
import { canonicalJson, derive, explain, hex, intentBytes, invocationId, signRaw, unhex, sha256, headersDigest, confirmDigest, SdkError } from "../src/index.ts";
import { fixture, golden as g, intentInputs, leanVectors, oracle } from "./support.ts";

const clone = <T>(v: T): T => structuredClone(v);

test("derive + sign across paths and messages", () => {
  for (const path of ["dregg/0", "mini/0", "mini/7", "mini/4294967295", "other"]) {
    assert.equal(hex(derive(unhex(g.seed), path).publicKey), oracle.derivePublic(g.seed, path), path);
    for (const m of ["", "00", "02ff9dff".repeat(50)]) {
      assert.equal(hex(signRaw(derive(unhex(g.seed), path), unhex(m))), oracle.signRaw(g.seed, path, m));
    }
  }
});

test("canonical JSON (the core's): key order is UTF-8 byte order, escapes match serde_json", () => {
  const cases = [
    { "ｚ": 1, "😀": 2, "z": 3, "é": 4, "": 5, "A": [true, false, null] },
    { s: "\u0000\u0007\b\t\n\f\r\u001b\u007f \"\\/ünï😀" },
    { n: [0, -1, 9007199254740992, -9007199254740992] },
  ];
  // UTF-16 order would put 😀 before ｚ; UTF-8 order puts ｚ first.
  const c0 = canonicalJson(cases[0] as never);
  assert.ok(c0.indexOf("ｚ") < c0.indexOf("😀"));
  assert.equal(c0, '{"":5,"A":[true,false,null],"z":3,"é":4,"ｚ":1,"😀":2}');
  assert.equal(canonicalJson(cases[1] as never), '{"s":"\\u0000\\u0007\\b\\t\\n\\f\\r\\u001b\x7f \\"\\\\/ünï😀"}');
  assert.equal(canonicalJson(cases[2] as never), '{"n":[0,-1,9007199254740992,-9007199254740992]}');
  for (const bad of [{ f: 1.5 }, { big: 2 ** 53 + 2 }]) assert.throws(() => canonicalJson(bad as never), /integers/);
});

test("the TS spelling reaches the core unmangled; mutations change the bytes and refusals are SdkErrors", () => {
  const ok = new Set(leanVectors.vectors.filter((v: any) => v.result === "ok").map((v: any) => v.name));
  for (const row of intentInputs) {
    if (!ok.has(row.name) || row.name.startsWith("payload-number")) continue;
    const base = JSON.parse(row.text);
    const salt = clone(base); salt.salt = "ff" + base.salt.slice(2);
    const actor = clone(base); actor.actor = "18446744073709551615";
    const distinct = new Set([hex(intentBytes(base)), hex(intentBytes(salt)), hex(intentBytes(actor))]);
    assert.equal(distinct.size, 3, `${row.name}: mutations did not change the bytes`);
    const lead = clone(base); lead.actor = "07";
    assert.throws(() => intentBytes(lead), SdkError);
    // The core's answers and the TS wrapper's agree (the wrapper adds nothing).
    assert.equal(hex(intentBytes(base)), oracle.intentBytes(JSON.stringify(base)));
    assert.equal(invocationId(base), oracle.invocationId(JSON.stringify(base)));
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
