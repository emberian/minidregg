// Shared test support. The wasm core (`wasm/`, rebuilt by `npm run build:core` before every
// `npm test`) is the Rust implementation; a missing core FAILS, because a differential that
// cannot run proves nothing.
import { readFileSync } from "node:fs";
import { core } from "../src/index.ts";

const here = new URL(".", import.meta.url).pathname;
export const oracle = core();
const read = (rel: string) => JSON.parse(readFileSync(`${here}../../mini-sdk/${rel}`, "utf8"));
export const golden = read("golden/vectors.json");
/** The intent inputs (`{name, text}`: the exact source text), and the bytes (or refusals) Lean's exported entry points produced for them. */
export const intentInputs = read("golden/intents.json");
export const leanVectors = read("golden/lean-intents.json");
export const fixture = (name: string) => read(`tests/fixtures/${name}`);
