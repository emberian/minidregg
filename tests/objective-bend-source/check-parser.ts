// Parser cohort, through the Lean parser (Compiler/ObjectiveBendParse, via the front end's
// batch command): structural assertions on real ASTs, malformed-let refusals, and every
// in-repo .obend parses.
// usage: bun tests/objective-bend-source/check-parser.ts   (env LEAN, LEAN_PATH: see front.ts)
import {readFileSync,readdirSync,writeFileSync,mkdtempSync} from "node:fs";
import {join} from "node:path";
import {tmpdir} from "node:os";
import {batch} from "./front.ts";
const here=import.meta.dirname;
const names=["EvenOdd","TwiceReview","GenericExtension","Heterogeneous","WholeSuper","LazySpecification","LazyUnusedArgument","LazyUnusedField","LazySharedField"];
const every=readdirSync(here).filter(f=>f.endsWith(".obend")).sort();
const letSource="edition ObjectiveBend 1\ndef f(x: Nat) -> Nat:\n  let y = x + 1n\n  let z: Nat = y * y\n  match z:\n    case 0n: 0n\n    case 1n+p:\n      let w = p - 1n\n      w / 2n\ndef g(x: Nat) -> Nat:\n  let a = 1n in a + x\n";
const badLets:[string,string][]=[["def f() -> Nat:\n  let y = 1n\n    y\n","a let body indented deeper"],["def f() -> Nat:\n  let y = 1n\n","a let with no body"],["def f() -> Nat:\n  let = 1n\n  1n\n","a let with no name"]];
const jobs=[...every.map(f=>({name:f,parse:readFileSync(join(here,f),"utf8")})),{name:"lets",parse:letSource},
 ...badLets.map(([src,why])=>({name:"bad:"+why,parse:"edition ObjectiveBend 1\n"+src}))];
const work=mkdtempSync(join(tmpdir(),"obend-parser-"));writeFileSync(join(work,"jobs.json"),JSON.stringify(jobs));
const results=batch(join(work,"jobs.json"),join(work,"results.json"));
const ast=(name:string)=>{const r=results.find((x:any)=>x.name===name);if(!r?.ok)throw Error("did not parse: "+name+" "+JSON.stringify(r?.diagnostic));return r.ast;};
for(const name of names){if(!ast(name+".obend").declarations.length)throw Error("empty AST "+name);console.log(name+": actual source parse");}
const unused=ast("LazyUnusedArgument.obend").declarations.find((d:any)=>d.kind==="function"&&d.signature.name==="result");
if(unused?.kind!=="function"||unused.body.kind!=="expression"||unused.body.expression.kind!=="call")throw new Error("lazy argument call lost");
const recursive=unused.body.expression.args[1];if(recursive?.kind!=="fix"||recursive.specification.kind!=="extension-value")throw new Error("captured extension replaced by metadata or forced away");
if(recursive.specification.body.kind!=="var"||recursive.specification.body.name!=="self")throw new Error("actual recursive body lost");
const heterogeneous=ast("Heterogeneous.obend").declarations.find((d:any)=>d.kind==="extension"&&d.name==="AddY");
if(heterogeneous?.kind!=="extension"||heterogeneous.parameters[0].type===heterogeneous.parameters[1].type||heterogeneous.targetType===heterogeneous.parameters[0].type)throw new Error("open V/C/W annotations collapsed");
console.log("OBJECTIVE SOURCE AST COHORT PASS: 9 source programs; nested captured extension and independent types retained");
const quoted=ast("QuotedFields.obend");
const row=quoted.declarations.find((d:any)=>d.kind==="record") as any;
const selected=quoted.declarations.find((d:any)=>d.kind==="function") as any;
if(JSON.stringify(row.fields.map((f:any)=>f.name))!==JSON.stringify(["0","1"])||selected.body.expression.name!=="1")throw Error("quoted field identity differs");
console.log("QUOTED FIELDS PASS: canonical ordinal keys, escaped string names, actual member selection");
const lets=ast("lets");
const letF=lets.declarations[0].body,letG=lets.declarations[1].body;
if(letF.kind!=="let"||letF.name!=="y"||letF.type!=="_"||letF.value.op!=="+"||letF.body.kind!=="let"||letF.body.type!=="Nat"||letF.body.body.kind!=="match")throw Error("statement let chain lost");
if(letF.body.body.branches[1].body.kind!=="let"||letF.body.body.branches[1].body.body.expression.op!=="/")throw Error("let inside a match arm lost");
if(letG.kind!=="expression"||letG.expression.kind!=="let"||letG.expression.body.op!=="+")throw Error("expression let lost");
for(const [,why] of badLets)if(results.find((x:any)=>x.name==="bad:"+why)?.ok!==false)throw Error("malformed let accepted: "+why);
console.log("LET PARSE PASS: statement chain, let in a match arm, expression form, malformed lets refused");
for(const f of every)ast(f);
console.log("EVERY OBEND PARSES: "+every.length+" files");
