// The wasm build of native/mini-sdk (feature `wasm`), rebuilt by `npm run build:oracle` before
// every `npm test`. A missing oracle FAILS: a differential that cannot run proves nothing.
import { createRequire } from "node:module";
import { existsSync, readFileSync } from "node:fs";

const here = new URL(".", import.meta.url).pathname;
const path = `${here}../oracle/mini_sdk.js`;
if (!existsSync(path)) throw new Error(`wasm oracle absent at ${path}: run npm run build:oracle`);
export const oracle = createRequire(import.meta.url)(path);
export const golden = JSON.parse(readFileSync(`${here}../../mini-sdk/golden/vectors.json`, "utf8"));
export const fixture = (name: string) => JSON.parse(readFileSync(`${here}../../mini-sdk/tests/fixtures/${name}`, "utf8"));
