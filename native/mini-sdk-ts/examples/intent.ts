// A worked example: build one typed intent, print its canonical bytes and its digest, sign it under
// both key schemes, verify, and show a tampered signature refuse. It needs no Host, no consent
// process and no network.
//
//     npm run build:core && node examples/intent.ts
//
// It prints the same text as the Rust example (native/mini-sdk/examples/intent.rs); both are pinned
// to native/mini-sdk/examples/intent.expected, and the bytes are cross-checked against the vector
// Lean emitted for this intent (golden/lean-intents.json, row `example-invoke`).
//
// What is NOT shown, because it needs a Host: in the real flow the key signs only header bytes the
// member's local consent process returned, under a Confirmation of what explain() rendered. Here the
// key signs the intent bytes directly, to show the signer interface.
import { hex, intentBytes, intentIdPreimage, invocationId, Profile, sha256, verify, type Intent, type Scheme } from "../src/index.ts";

// One request by one actor: write the text "hello" into a document. The salt makes this ONE request.
const intent: Intent = {
  actor: "12504530369102912422",
  salt: "000102030405060708090a0b0c0d0e0f",
  cut: "invoke",
  family: null,
  targets: [{
    revision: {
      object: { id: "11713997809205700508", domain: "8501", kind: "object" },
      root: "94531388991341573437548127621893842788707596369540381335288917555563780111749",
    },
    capability: "9591460230184716503",
    observeCapability: "9591460230184716503",
    schemaVersion: "9",
    payload: { type: "content", actions: [{ type: "createAtom", atom: "1", kind: { type: "text" }, payload: "68656c6c6f" }] },
  }],
};

// The bytes are the Lean codec's (Kernel/Contracts/Intents.lean), reached through the Rust core.
const bytes = intentBytes(intent);
console.log(`cut            ${intent.cut}`);
console.log(`actor          ${intent.actor}`);
console.log(`intent bytes   ${bytes.length} bytes`);
console.log(`  ${hex(bytes)}`);
console.log(`preimage       ${intentIdPreimage(intent).length} bytes (DREGG/CONTRACT/INTENT-ID/v1 || intent bytes)`);
console.log(`invocation id  ${invocationId(intent)}`);

// A profile is a 64-byte master seed; each key scheme derives its key from it.
const profile = new Profile("example", Uint8Array.from({ length: 64 }, (_, i) => i));
for (const [name, scheme] of [["ed25519", "ed25519"], ["hybrid", "hybrid-ed25519-ml-dsa-65"]] as [string, Scheme][]) {
  const signer = profile.signer(0, scheme);
  const signature = signer.sign(bytes);
  console.log(name);
  console.log(`  public key   ${signer.publicKey.length} bytes, sha256 ${hex(sha256(signer.publicKey))}`);
  console.log(`  signature    ${signature.length} bytes, sha256 ${hex(sha256(signature))}`);
  verify(scheme, signer.publicKey, bytes, signature);
  console.log("  verified     ok");
  const tampered = Uint8Array.from(signature);
  tampered[tampered.length - 1] ^= 1;
  try {
    verify(scheme, signer.publicKey, bytes, tampered);
    throw new Error("a tampered signature verified");
  } catch (e) {
    if (!(e instanceof Error) || e.message === "a tampered signature verified") throw e;
    console.log(`  tampered     refused: ${e.message}`);
  }
}
