// Sealed source check/emission for world/Workshop. No ambient filesystem imports,
// hub access, main.ts telemetry, source execution, kernel build or grant creation.
import {readFileSync, writeFileSync, mkdirSync} from "node:fs";
import {createHash} from "node:crypto";
import {resolve, join} from "node:path";
import {pathToFileURL} from "node:url";
import {elaborateSealed, type Module} from "./sealed.ts";

const repo = resolve(process.argv[2] ?? ".");
const upstream = process.argv[3];
const output = process.argv[4];
if (!upstream || !output) throw new Error("usage: check-workshop.ts REPO PINNED_BEND2 OWN_OUTPUT");
const sha256 = (bytes: Uint8Array) => createHash("sha256").update(bytes).digest("hex");
for (const [file, expected] of [
  ["bend.ts", "7deae3693eb896f33c73867081b99d2c6f3ed3b57e77e55eb5f6260840dd0e63"],
  ["safe.ts", "54cb3a534ab7cc9ee313bf6383b3948ccdcac022469b3020e00745bbfe6f7e04"]
]) {
  if (sha256(readFileSync(join(upstream, file))) !== expected) throw new Error(`changed upstream ${file}`);
}
const Bend = await import(pathToFileURL(resolve(upstream, "bend.ts")).href);
const Safe = await import(pathToFileURL(resolve(upstream, "safe.ts")).href);
const ownedOutput = resolve(output);
mkdirSync(ownedOutput, {recursive: true});
const source = (name: string) => readFileSync(join(repo, "world", "Workshop", `${name}.bend`));
const prelude = source("Prelude");
const review = source("CatalogReview");
const capacity = source("OrderedCapacity");
const workshop = source("ReusableWorkshop");
const surface = source("WorldSurface");
const baseImport = {alias: "", path: "Base", module: 0, sha256: sha256(prelude)};
const results: unknown[] = [];

for (const [name, entry] of [
  ["OrderedCapacity", "allocate"], ["CatalogReview", "prepare"],
  ["ReusableWorkshop", "presentation"], ["Demonstration", "demonstration"],
  ["WorkshopFaces", "domain_face"], ["MemberExtension", "focused_review"],
  ["ContractedReview", "contracted_review"]
]) {
  const modules: Module[] = [{namespace: "", bytes: prelude, sha256: sha256(prelude), imports: []}];
  const imports = [baseImport];
  if (["ReusableWorkshop", "MemberExtension", "ContractedReview"].includes(name)) {
    modules.push({namespace: "CatalogReview", bytes: review, sha256: sha256(review), imports: [baseImport]});
    imports.push({alias: "Review", path: "./CatalogReview.bend", module: 1, sha256: sha256(review)});
  }
  if (["MemberExtension", "ContractedReview"].includes(name)) {
    modules.push({namespace: "ReusableWorkshop", bytes: workshop, sha256: sha256(workshop),
      imports: [baseImport, {alias: "Review", path: "./CatalogReview.bend", module: 1, sha256: sha256(review)}]});
    imports.push({alias: "Workshop", path: "./ReusableWorkshop.bend", module: 2, sha256: sha256(workshop)});
  }
  if (name === "Demonstration") {
    modules.push({namespace: "OrderedCapacity", bytes: capacity, sha256: sha256(capacity), imports: [baseImport]});
    imports.push({alias: "Capacity", path: "./OrderedCapacity.bend", module: 1, sha256: sha256(capacity)});
  }
  if (name === "WorkshopFaces") {
    modules.push({namespace: "WorldSurface", bytes: surface, sha256: sha256(surface), imports: [baseImport]});
    imports.push({alias: "World", path: "./WorldSurface.bend", module: 1, sha256: sha256(surface)});
  }
  const bytes = source(name);
  const entryModule = modules.length;
  modules.push({namespace: name, bytes, sha256: sha256(bytes), imports});
  try {
    const result = elaborateSealed(Bend, Safe, {modules, entryModule, entryDefinition: entry}, ownedOutput);
    results.push({module: name, entry, ...result.transcript,
      bookPath: result.bookPath, transcriptPath: result.transcriptPath});
    console.log(`SOURCE CHECK + BENDTT EMISSION PASS ${name}`);
  } catch (error) {
    console.error((error as {$?: string}).$ === "Err" ? Bend.err_show(error) : String(error));
    process.exit(1);
  }
}
writeFileSync(join(ownedOutput, "sealed-results.json"), JSON.stringify(results, null, 2) + "\n");
