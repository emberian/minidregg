import { test } from "node:test";
import assert from "node:assert/strict";
import { Attempt, classify, derive, Presented, signTransaction, unhex } from "../src/index.ts";
import { fixture, golden as g } from "./oracle.ts";

const enc = (s: string) => new TextEncoder().encode(s);
const confirmed = (c: string) => ({ type: "confirmed", confirmation: c, transactionId: "1", eventId: "2", acceptedCount: "3", worldRoot: "4" });
const sealed = () => { const a = Attempt.first("07".repeat(32), "10", "20"); a.prepared(); a.sealed(enc("call")); return a; };

test("lost reply: exact lookup only, never a successor; recovered confirms", () => {
  const a = sealed();
  assert.equal(a.record(enc("call"), { kind: "uncertain", detail: "lost" }).kind, "uncertain");
  assert.throws(() => a.successor("11", "21"), /look it up/);
  assert.throws(() => a.record(enc("other"), { kind: "answered", outcome: confirmed("installed") }), /retained call bytes/);
  const p = a.record(enc("call"), { kind: "answered", outcome: confirmed("recoveredAfterUncertainResponse") });
  assert.equal(p.kind, "confirmed");
  assert.throws(() => a.successor("11", "21"), /confirmed/);
});

test("refused permits a successor with fresh nonces only; unsent-after-uncertain stays uncertain", () => {
  const a = sealed();
  a.record(enc("call"), { kind: "answered", outcome: { type: "refused" } });
  assert.throws(() => a.successor("10", "21"));
  const b = a.successor("11", "21");
  assert.equal(b.number, 2);
  const c = sealed();
  c.record(enc("call"), { kind: "uncertain", detail: "write" });
  assert.equal(c.record(enc("call"), { kind: "unsent", detail: "connect" }).kind, "uncertain");
  assert.equal(classify([confirmed("installed"), { type: "refused" }])?.kind, "confirmed");
  assert.equal(classify([{ type: "pending" }, { type: "refused" }])?.kind, "refused");
  assert.equal(classify([confirmed("maybe")])?.kind, "undecided");
});

test("signing needs the confirmation of this exact presentation", () => {
  const key = derive(unhex(g.seed), "mini/0");
  const p = new Presented("07".repeat(32), 1, fixture("intent.json"), enc("intent"), fixture("plan.json"), enc("plan"), [enc("h1"), enc("h2")]);
  const c = p.confirm(new Uint8Array(16).fill(5));
  assert.equal(signTransaction(key, p, c).length, 2);
  const q = new Presented("07".repeat(32), 2, fixture("intent.json"), enc("intent"), fixture("plan.json"), enc("plan"), [enc("h1"), enc("h2")]);
  assert.throws(() => signTransaction(key, q, c), /different presentation/);
  assert.throws(() => signTransaction(key, p, { ...c, nonce: new Uint8Array(16).fill(6) }), /different presentation/);
});
