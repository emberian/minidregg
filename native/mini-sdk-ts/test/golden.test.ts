// The TS SDK recomputes every golden vector independently (no wasm involved).
import { test } from "node:test";
import assert from "node:assert/strict";
import { canonicalJson, confirmDigest, derive, explain, headersDigest, hex, intentBytes, invocationId, lower, signRaw, unhex, sha256 } from "../src/index.ts";
import { fixture, golden as g } from "./oracle.ts";

const seed = unhex(g.seed);
const e = g.expect;

test("derivation: Bread's dregg/0 pin and the Mini path vectors", () => {
  assert.equal(hex(derive(seed, "dregg/0").publicKey), "335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a");
  g.derive.forEach((d: { path: string }, i: number) => assert.equal(hex(derive(seed, d.path).publicKey), e.derive[i], d.path));
});

test("signatures over raw bytes", () => {
  g.sign.forEach((s: { path: string; message: string }, i: number) =>
    assert.equal(hex(signRaw(derive(seed, s.path), unhex(s.message))), e.sign[i]));
});

test("canonical JSON", () => {
  g.canonicalJson.forEach((c: { input: unknown }, i: number) => assert.equal(canonicalJson(c.input as never), e.canonicalJson[i]));
});

test("intent canonical bytes and InvocationId for every cut", () => {
  for (const row of g.intents) {
    assert.equal(hex(intentBytes(row.intent)), e.intents[row.name].bytes, row.name);
    assert.equal(invocationId(row.intent), e.intents[row.name].invocationId, row.name);
  }
});

test("lowering reproduces the real admitted intent.json", () => {
  const row = g.intents.find((r: { name: string }) => r.name === g.lowering.intent);
  const lowered = lower(row.intent, g.lowering.context);
  assert.equal(canonicalJson(lowered), e.lowering);
  assert.deepEqual(lowered, fixture("intent.json"));
});

test("headers digest, explain text, confirmation digest", () => {
  g.headers.forEach((l: string[], i: number) => assert.equal(hex(headersDigest(l.map(unhex))), e.headers[i]));
  const x = explain(fixture("intent.json"), fixture("plan.json"), {
    intentSha256: unhex(g.explain.intentSha256), planSha256: unhex(g.explain.planSha256), headersSha256: unhex(g.explain.headersSha256) });
  assert.equal(x.text, e.explain.text);
  assert.equal(hex(sha256(new TextEncoder().encode(x.text))), e.explain.sha256);
  const c = g.confirm;
  assert.equal(hex(confirmDigest(unhex(c.invocation), c.attempt, unhex(c.intentSha256), unhex(c.planSha256),
    unhex(c.headersSha256), unhex(c.explanationSha256), unhex(c.nonce))), e.confirm);
});
