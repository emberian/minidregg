// The worked example's output is asserted: examples/intent.ts runs (no Host, no network) and prints
// exactly native/mini-sdk/examples/intent.expected (the text the Rust example prints too), and the
// intent bytes it prints are the bytes Lean emitted for the same intent.
import { test } from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { hex, sha256, unhex } from "../src/index.ts";
import { leanVectors } from "./support.ts";

const here = new URL(".", import.meta.url).pathname;
const run = () => execFileSync(process.execPath, [`${here}../examples/intent.ts`], { encoding: "utf8" });

test("the intent example prints exactly its pinned output (shared with the Rust example)", () => {
  assert.equal(run(), readFileSync(`${here}../../mini-sdk/examples/intent.expected`, "utf8"));
});

test("the example's intent bytes and digest are Lean's", () => {
  const row = leanVectors.vectors.find((v: any) => v.name === "example-invoke");
  assert.equal(row.result, "ok");
  const lines = run().split("\n");
  assert.equal(lines[lines.findIndex((l) => l.startsWith("intent bytes")) + 1].trim(), row.bytes);
  const id = lines.find((l) => l.startsWith("invocation id  "))!.slice("invocation id  ".length);
  assert.equal(id, hex(sha256(unhex(row.idPreimage))));
});
