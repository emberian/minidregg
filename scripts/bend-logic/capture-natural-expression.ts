// Scoped source parser/elaborator only; no safe_check/upstream kernel build.
import {readFileSync, writeFileSync} from "node:fs";
import {createHash} from "node:crypto";
const root = process.argv[2];
const tools = process.env.BEND_SOURCE_TOOLING_ROOT;
if (!root || !tools) throw new Error("source root and pinned BEND_SOURCE_TOOLING_ROOT required");
const Bend = await import(`${tools}/bend.ts`);
const Safe = await import(`${tools}/safe.ts`);
const {elaborateSealed} = await import(`${tools}/sealed.ts`);
const digest = (bytes: Uint8Array) => createHash("sha256").update(bytes).digest("hex");
const base = readFileSync(`${tools}/base.bend`);
const source = readFileSync(`${root}/tests/bend-source-representation/NaturalExpressionSource.bend`);
const result = elaborateSealed(Bend, Safe, {modules:[
  {namespace:"",bytes:base,sha256:digest(base),imports:[]},
  {namespace:"",bytes:source,sha256:digest(source),imports:[
    {alias:"",path:"Base",module:0,sha256:digest(base)}]}],
  entryModule:1,entryDefinition:"SourceNat.doubleSum"}, root);
writeFileSync(`${root}/tests/bend-source-representation/NaturalExpressionSource.bendtt`, result.bookBytes);
writeFileSync(`${root}/natural-expression-frontend.json`, JSON.stringify(result.transcript,null,2)+"\n");
console.log("NATURAL EXPRESSION CAPTURE PASS", digest(result.bookBytes));
