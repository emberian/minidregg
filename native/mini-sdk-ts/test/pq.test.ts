// The hybrid Ed25519 + ML-DSA-65 scheme through the TS SDK (the Rust core's fips204): sign, verify,
// wrong key, either half tampered, and signing under a confirmation.
import { test } from "node:test";
import assert from "node:assert/strict";
import { Presented, Profile, SdkError, SIGNATURE_LEN, PUBLIC_KEY_LEN, signTransaction, unhex, verify, ed25519Signer, hex } from "../src/index.ts";
import { fixture, golden as g } from "./support.ts";

const H = "hybrid-ed25519-ml-dsa-65" as const;
const profile = (seed = g.seed) => new Profile("pq", unhex(seed));
const msg = new TextEncoder().encode("frame");

test("hybrid sign and verify; widths are fixed; signing is deterministic", () => {
  const s = profile().signer(0, H);
  const sig = s.sign(msg);
  assert.equal(s.scheme, H);
  assert.equal(s.publicKey.length, PUBLIC_KEY_LEN[H]);
  assert.equal(sig.length, SIGNATURE_LEN[H]);
  verify(H, s.publicKey, msg, sig);
  assert.deepEqual(s.sign(msg), sig);
  // The Ed25519 half is the plain Ed25519 signature of the same key.
  const ed = profile().signer(0, "ed25519");
  assert.deepEqual(sig.slice(0, 64), ed.sign(msg));
  assert.deepEqual(s.publicKey.slice(0, 32), ed.publicKey);
});

test("wrong message, wrong key (either half), and either half tampered refuse, naming the half", () => {
  const s = profile().signer(0, H);
  const sig = s.sign(msg);
  assert.throws(() => verify(H, s.publicKey, new TextEncoder().encode("other"), sig), /Ed25519 half does not verify/);
  const edOther = profile(("ff" + g.seed.slice(2))).signer(0, H).publicKey;
  assert.throws(() => verify(H, edOther, msg, sig), /Ed25519 half does not verify/);
  const mlOther = Uint8Array.from(s.publicKey); mlOther.set(profile().signer(1, H).publicKey.slice(32), 32);
  assert.notDeepEqual(mlOther, s.publicKey);
  assert.throws(() => verify(H, mlOther, msg, sig), /ML-DSA-65 half does not verify/);
  for (const [at, want] of [[0, /Ed25519/], [63, /Ed25519/], [64, /ML-DSA-65/], [sig.length - 1, /ML-DSA-65/]] as const) {
    const t = Uint8Array.from(sig); t[at] ^= 1;
    assert.notDeepEqual(t, sig);
    assert.throws(() => verify(H, s.publicKey, msg, t), want, `byte ${at}`);
  }
  assert.throws(() => verify(H, s.publicKey, msg, sig.slice(0, 64)), /signature must be 3373 bytes/);
  assert.throws(() => verify(H, s.publicKey.slice(0, 32), msg, sig), /public key must be 1984 bytes/);
  assert.throws(() => verify("ed25519", s.publicKey.slice(0, 32), msg, sig), SdkError);
});

test("the hybrid signs consented transaction headers under a confirmation, and not without one", () => {
  const s = profile().signer(0, H);
  const headers = [unhex("0102"), unhex("0304")];
  const p = new Presented("07".repeat(32), 1, fixture("intent.json"), unhex("aa"), fixture("plan.json"), unhex("bb"), headers);
  const c = p.confirm(unhex("05".repeat(16)));
  const sigs = signTransaction(s, p, c);
  sigs.forEach((sig, i) => verify(H, s.publicKey, headers[i], sig));
  assert.throws(() => signTransaction(s, p, { ...c, nonce: unhex("06".repeat(16)) }), /different presentation/);
  assert.equal(sigs.every((x) => x.length === 3373), true);
  assert.equal(hex(ed25519Signer(profile().miniKey(0)).publicKey), hex(s.publicKey.slice(0, 32)));
});
