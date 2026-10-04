// The TS SDK against the golden vectors. Derivation, Ed25519, explain and digests are recomputed
// in TS independently of the Rust core; the intent encoder and the hybrid scheme are the Rust core
// itself (wasm), so for those the evidence is Lean's vectors, not a second implementation.
import { test } from "node:test";
import assert from "node:assert/strict";
import { call, canonicalJson, confirmDigest, derive, explain, headersDigest, hex, intentBytes, intentIdPreimage, invocationId, lower, Profile, SdkError, signRaw, unhex, sha256, verify, type Core } from "../src/index.ts";
import { fixture, golden as g, intentInputs, leanVectors } from "./support.ts";

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

test("intent bytes are LEAN's: every vector Lean's exported entry points emitted, byte for byte", () => {
  assert.equal(leanVectors.vectors.length, intentInputs.length, "lean-intents.json does not cover intents.json; re-emit it");
  let admitted = 0, refused = 0, objectPath = 0;
  leanVectors.vectors.forEach((row: any, i: number) => {
    assert.equal(row.text, intentInputs[i].text, `${row.name}: stale vector file`);
    // The core on the row's exact SOURCE TEXT (what Lean saw): every row, including number spellings
    // JavaScript cannot represent.
    const viaText = (f: (c: Core) => string) => call(f);
    // The object path (what a TS app does): JSON.parse, then the SDK's spelling. A JS number cannot hold
    // `1.0000000000000000001`, `1e400` or 9007199254740993, so a row whose parse is not faithful (the
    // core reads its re-serialization differently from its text) is text-path only.
    const canon = (t: string) => { try { return viaText((c) => c.canonicalJson(t)); } catch { return "refused"; } };
    const parsed = JSON.parse(row.text);
    const object = canon(row.text) === canon(JSON.stringify(parsed)) ? parsed : null;
    if (object) objectPath++;
    if (row.result === "ok") {
      assert.equal(viaText((c) => c.intentBytes(row.text)), row.bytes, row.name);
      assert.equal(viaText((c) => c.intentIdPreimage(row.text)), row.idPreimage, row.name);
      if (object) {
        assert.equal(hex(intentBytes(object)), row.bytes, row.name);
        assert.equal(hex(intentIdPreimage(object)), row.idPreimage, row.name);
        assert.equal(invocationId(object), hex(sha256(unhex(row.idPreimage))), row.name);
      }
      admitted++;
    } else {
      assert.equal(row.result, "refused");
      assert.throws(() => call((c) => c.intentBytes(row.text)), SdkError, `${row.name}: Lean refuses (${row.reason}), the core admits`);
      if (object) assert.throws(() => intentBytes(object), SdkError, row.name);
      refused++;
    }
  });
  assert.ok(admitted >= 25 && refused >= 25, `the vector set lost its teeth: ${admitted} admitted, ${refused} refused`);
  assert.ok(objectPath >= 40, `the object path ran on only ${objectPath} rows`);
});

test("lowering reproduces the real admitted intent.json", () => {
  const row = intentInputs.find((r: { name: string }) => r.name === g.lowering.intent);
  const lowered = lower(JSON.parse(row.text), g.lowering.context);
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

test("signer schemes: Ed25519 and the hybrid, from the profile seed", () => {
  const profile = new Profile("golden", seed);
  const message = unhex(g.signers.message);
  for (const [name, scheme] of [["ed25519", "ed25519"], ["hybrid", "hybrid-ed25519-ml-dsa-65"]] as const) {
    const want = e.signers[name];
    const signer = profile.signer(g.signers.generation, scheme);
    const sig = signer.sign(message);
    assert.equal(hex(signer.publicKey.slice(0, 32)), want.publicKey, name);
    assert.equal(hex(sha256(signer.publicKey)), want.publicKeySha256, name);
    assert.equal(hex(sig.slice(0, 64)), want.signatureEd, name);
    assert.equal(hex(sha256(sig)), want.signatureSha256, name);
    assert.equal(signer.publicKey.length, want.publicKeyLen);
    assert.equal(sig.length, want.signatureLen);
    verify(scheme, signer.publicKey, message, sig);
  }
});
