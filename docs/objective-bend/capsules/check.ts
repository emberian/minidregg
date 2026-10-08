import {readFileSync, readdirSync} from "node:fs";
import {createHash} from "node:crypto";
import {dirname, join} from "node:path";
import {fileURLToPath} from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const manifest = JSON.parse(readFileSync(join(here, "manifest.json"), "utf8"));
const expected = ["algebra", "machine", "rewrite"].flatMap(style =>
  [1, 2, 3].map(size => `${style}-${size}k.txt`)).sort();
const actual = readdirSync(here).filter(name => name.endsWith(".txt")).sort();
if (JSON.stringify(actual) !== JSON.stringify(expected) ||
    JSON.stringify(Object.keys(manifest.capsules).sort()) !== JSON.stringify(expected))
  throw Error("Expected exactly three capsule families at three budgets");
for (const name of expected) {
  const bytes = readFileSync(join(here, name));
  const limit = Number(name.match(/-([123])k\.txt$/)![1]) * 1000;
  const recorded = manifest.capsules[name];
  const sha256 = createHash("sha256").update(bytes).digest("hex");
  if (bytes.length >= limit || bytes.some(byte => byte > 127) ||
      bytes.length !== recorded.bytes || limit !== recorded.exclusiveLimit ||
      sha256 !== recorded.sha256)
    throw Error(`${name}: byte budget, ASCII or manifest mismatch`);
  console.log(`${name}: ${bytes.length} < ${limit} bytes; hash matches`);
}
console.log("Byte/identity checks only; semantic equivalence is not established here.");
