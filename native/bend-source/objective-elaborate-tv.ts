// Translation validation: the Lean elaborator (Compiler/ObjectiveBendElaborate.lean)
// against this TypeScript elaborator, on every in-repo .obend. For every
// declaration (definition mode) and every preview-cohort invocation
// (application mode, with its arguments), both must refuse, or both must emit
// the same Core4 term and the same typing proposal (type table, annotations,
// bounds, shareable variables), compared as canonical JSON.
// usage: bun objective-elaborate-tv.ts NEW_WORK_DIR LEAN_COMMAND...
//   e.g. bun objective-elaborate-tv.ts /tmp/tv lake env lean --run Host/ObjectiveBendElaborateRun.lean
import {readFileSync,readdirSync,writeFileSync,mkdirSync,existsSync} from "node:fs";
import {join,resolve} from "node:path";
import {execFileSync} from "node:child_process";
import {parseObjective} from "./objective-parser.ts";
import {elaborate,literalAnnotations} from "./objective-elaborate.ts";
const [workRaw,...leanCommand]=process.argv.slice(2);
if(!workRaw||!leanCommand.length)throw Error("usage: objective-elaborate-tv NEW_WORK_DIR LEAN_COMMAND...");
const work=resolve(workRaw);if(existsSync(work))throw Error("work directory must be new");mkdirSync(work,{recursive:true});
const canonical=(v:any):string=>JSON.stringify(v&&typeof v==="object"?Array.isArray(v)?v.map(x=>JSON.parse(canonical(x))):Object.fromEntries(Object.keys(v).sort().map(k=>[k,JSON.parse(canonical(v[k]))])):v);
const testDir=resolve(import.meta.dirname,"../../tests/objective-bend-source");
const moduleSet=(file:string)=>{
 const ast=parseObjective(readFileSync(join(testDir,file),"utf8"));
 const mods:any[]=ast.imports.map((i:any)=>{const base=i.path.slice(2).replace(".obend","");return {name:base,imports:[],ast:parseObjective(readFileSync(join(testDir,base+".obend"),"utf8"))};});
 mods.push({name:file.replace(".obend",""),imports:ast.imports.map((i:any,j:number)=>({alias:i.alias,moduleName:mods[j].name,module:String(j)})),ast});
 return mods;
};
const jobs:any[]=[];
for(const file of readdirSync(testDir).filter(f=>f.endsWith(".obend")).sort()){
 const mods=moduleSet(file);const last=mods[mods.length-1];
 for(const d of last.ast.declarations)if(d.kind!=="record"&&d.kind!=="sum")
  jobs.push({name:file+"#"+(d.name??d.signature.name),modules:mods,entryModule:mods.length-1,entryDefinition:d.name??d.signature.name,arguments:[],mode:"definition"});
}
// A cohort item names its own modules (sources may live outside this directory, e.g. world/market) and import indices.
const cohortModules=(item:any)=>item.modules.map((m:any)=>({name:m.name,ast:parseObjective(readFileSync(join(testDir,m.source),"utf8")),
 imports:(m.imports??[]).map((i:any)=>({alias:i.alias,moduleName:item.modules[Number(i.module)].name,module:String(i.module)}))}));
for(const item of JSON.parse(readFileSync(join(testDir,"preview-cohort.json"),"utf8"))){
 const mods=cohortModules(item);
 const args=item.argumentEncoding==="typed-values-v1"?{schema:"dregg.objective-bend.argument-values.v1",values:item.arguments}:item.arguments;
 jobs.push({name:"cohort:"+item.name,modules:mods,entryModule:mods.length-1,entryDefinition:item.entry,arguments:args,mode:"application"});
}
// Inline probes: refusals both elaborators must agree on, and lowering paths
// the in-repo programs do not reach.
const R="record R:\n  v(n: Nat) -> Nat\n";
const A="sum P:\n  go: {}\nsum R:\n  ok: {}\n";
const A2="sum L:\n  nil: {}\n  cons: {head: Nat, tail: L}\n";
const sp=(name:string,head:string,body="    super.v(n) + 1n")=>head.replace("NAME",name)+"\n  def v(n: Nat) -> Nat:\n"+body+"\n";
const probes:[string,string][]=[
 ["refuse-unbound","def f() -> Nat:\n  missing\n"],
 ["accept-order-operators","def f(a: Nat, b: Nat) -> Bool:\n  a < b || a <= b || a > b || a >= b\n"],
 ["accept-subtract-divide","def f(a: Nat, b: Nat) -> Nat:\n  a - b + a / b\n"],
 ["accept-order-in-spec-law",R+"spec O for R:\n  def v(n: Nat) -> Nat:\n    n - 1n\n  law positive(n: Nat): self.v(n) < n\n"],
 ["accept-let-statement","def f(x: Nat) -> Nat:\n  let y = x + 1n\n  let z: Nat = y * y\n  match z:\n    case 0n: 0n\n    case 1n+p:\n      let w = p - 1n\n      w / 2n\n"],
 ["accept-let-expression","def f(x: Nat) -> Nat:\n  let a = (let b = x + 1n in b * b) in a + a\n"],
 ["accept-let-shadow","def f(x: Nat) -> Nat:\n  let x = x + 10n\n  let x = x * 2n\n  x\n"],
 ["accept-let-function","def f(a: Nat) -> Nat:\n  let twice = fn(n: Nat) -> Nat: n + n\n  twice(twice(a))\n"],
 ["accept-let-unresolved-type","def g(p: Nat) -> Nat:\n  let y = metadata(p)\n  1n\n"],
 ["accept-let-sum-recursive",A2+"def f(xs: L) -> Nat:\n  let n = 3n\n  match xs:\n    case nil(_): n\n    case cons(c): let m = c.head in m + f(c.tail)\n"],
 ["accept-let-activity-tail",A+"def f(n: Nat) -> Activity<P, R, Nat>:\n  let m = n + 1n\n  match perform(P.go({})):\n    case ok(_): let k = m * 2n in k\n"],
 ["accept-let-activity-pure-tail",A+"def f(n: Nat) -> Activity<P, R, Nat>:\n  match perform(P.go({})):\n    case ok(_):\n      let k = n + 1n\n      k\n"],
 ["refuse-let-activity-value",A+"def f(n: Nat) -> Activity<P, R, Nat>:\n  let x = perform(P.go({}))\n  1n\n"],
 ["accept-let-unknown-annotation-type","def f(x: Nat) -> Nat:\n  let y: Nope = x\n  y\n"],
 ["refuse-untyped-eq","def f(a, b) -> Bool:\n  a == b\n"],
 ["refuse-nat-wildcard","def f(n: Nat) -> Nat:\n  match n:\n    case _: 1n\n"],
 ["refuse-nonexhaustive","sum S:\n  a: Nat\n  b: Nat\ndef f(s: S) -> Nat:\n  match s:\n    case a(x): x\n"],
 ["refuse-unknown-case","sum S:\n  a: Nat\ndef f() -> S:\n  S.z(1n)\n"],
 ["refuse-c4-inconsistent",R+sp("O","spec NAME for R:","    n")+sp("H","spec NAME extends O for R:")+sp("V","spec NAME extends O for R:")+sp("HV","spec NAME extends H, V for R:")+sp("VH","spec NAME extends V, H for R:")+sp("X","spec NAME extends HV, VH for R:")],
 ["refuse-suffix",R+sp("S","suffix spec NAME for R:","    n")+sp("T","suffix spec NAME for R:","    n")+sp("X","spec NAME extends S, T for R:")],
 ["refuse-cycle",R+sp("A","spec NAME extends B for R:")+sp("B","spec NAME extends A for R:")],
 ["refuse-before",R+sp("O","spec NAME for R:","    n")+"spec B extends O for R:\n  before v(n: Nat) -> Nat:\n    n\n"],
 ["refuse-mixed-qualifier",R+sp("O","spec NAME for R:","    n")+"spec P extends O for R:\n  combine + v(n: Nat) -> Nat:\n    n\n"],
 ["refuse-duplicate-param","def f(x: Nat, x: Nat) -> Nat:\n  x\n"],
 ["accept-bool-eq","def f(a: Bool, b: Bool) -> Bool:\n  a == b\ndef g(a: Bool, b: Bool) -> Bool:\n  a != b || a\n"],
 ["accept-string-neq","def f(a: String) -> Bool:\n  a != \"x\"\n"],
 ["accept-affine-closure","def f(affine x: Nat) -> Nat -> Nat:\n  fn(y: Nat) -> Nat: x + y\n"],
 ["accept-specification-type",R+sp("O","spec NAME for R:","    n")+"def s() -> Specification<R>:\n  O\n"],
 ["accept-single-layer",R+sp("O","spec NAME for R:","    n")+"spec E extends O for R:\n  requires v(n: Nat) -> Nat\n"],
 // Activities (EVENTS-DESIGN): named refusals of an Activity in a shared position.
 ["refuse-activity-argument",A+"def g(x: Nat) -> Nat:\n  x\ndef f(n: Nat) -> Activity<P, R, Nat>:\n  g(perform(P.go({})))\n"],
 ["refuse-activity-field",A+"def f(n: Nat) -> Activity<P, R, Nat>:\n  match perform(P.go({})):\n    case ok(_): {x: perform(P.go({}))}.x\n"],
 ["refuse-perform-outside-activity",A+"def f(n: Nat) -> R:\n  perform(P.go({}))\n"],
 ["refuse-nullary-activity",A+"def f() -> Activity<P, R, Nat>:\n  match perform(P.go({})):\n    case ok(_): 1n\n"],
 ["accept-activity-pure-and-effect-arms",A+"def f(n: Nat) -> Activity<P, R, Nat>:\n  match perform(P.go({})):\n    case ok(_): if n == 0n then 1n else f(0n)\n"],
 ["accept-times-and",R+"record W:\n  w() -> Nat\n  ok() -> Bool\nspec A for W:\n  combine * w() -> Nat:\n    2n\n  combine and ok() -> Bool:\n    true\nspec B extends A for W:\n  combine * w() -> Nat:\n    3n\n  combine and ok() -> Bool:\n    false\n"],
];
for(const [name,body] of probes){
 const ast=parseObjective("edition ObjectiveBend 1\n"+body);
 const decls=ast.declarations.filter((d:any)=>d.kind!=="record"&&d.kind!=="sum");const last:any=decls[decls.length-1];
 jobs.push({name:"probe:"+name,modules:[{name:"Probe",imports:[],ast}],entryModule:0,entryDefinition:last.name??last.signature.name,arguments:[],mode:"definition"});
}
const ts=jobs.map(job=>{
 try{
  const out=elaborate(job.modules.map((m:any)=>({...m,sha256:"tv",astSha256:"tv"})),job.entryModule,job.entryDefinition,job.arguments,job.mode);
  const typed:any=literalAnnotations(out);
  return {ok:true,term:out.term,typed:typed.status==="unsupported"?{unsupported:typed.message}:{types:typed.types,annotations:typed.annotations,bounds:typed.bounds,shareableVariables:typed.shareableVariables}};
 }catch(e:any){return {ok:false,error:e?.message??String(e)};}
});
const jobsPath=join(work,"jobs.json"),leanOut=join(work,"lean-results.json");
writeFileSync(jobsPath,JSON.stringify(jobs.map(j=>({...j,modules:j.modules.map((m:any)=>({name:m.name,imports:m.imports,ast:m.ast}))})))+"\n");
execFileSync(leanCommand[0],[...leanCommand.slice(1),jobsPath,leanOut],{stdio:["ignore","inherit","inherit"],env:{...process.env,LEAN_NUM_THREADS:"2"}});
const lean=JSON.parse(readFileSync(leanOut,"utf8"));
if(lean.length!==jobs.length)throw Error("Lean returned "+lean.length+" results for "+jobs.length+" jobs");
const report:any[]=[];let agreeAccepted=0,agreeRefused=0,typedAgree=0,typedBothUnsupported=0;
for(const [i,job] of jobs.entries()){
 const a=ts[i],b=lean[i];const row:any={name:job.name,ts:a.ok?"accepted":"refused",lean:b.ok?"accepted":"refused"};
 if(a.ok!==b.ok){row.verdict="DISAGREE: acceptance";row.tsError=a.error;row.leanError=b.error;}
 else if(!a.ok){row.verdict="agree: both refuse";agreeRefused++;row.tsError=a.error;row.leanError=b.error;}
 else if(canonical(a.term)!==canonical(b.output.term))row.verdict="DISAGREE: core term";
 else{
  const ua="unsupported" in a.typed,ub="unsupported" in b.output.typed;
  if(ua&&ub){row.verdict="agree: same term; both typing proposals unsupported";typedBothUnsupported++;agreeAccepted++;}
  else if(ua!==ub){row.verdict="DISAGREE: typing proposal support";row.tsTyped=a.typed.unsupported;row.leanTyped=b.output.typed.unsupported;}
  else if(canonical(a.typed)!==canonical(b.output.typed))row.verdict="DISAGREE: typing proposal";
  else{row.verdict="agree: same term and typing proposal";typedAgree++;agreeAccepted++;}
  row.termBytes=canonical(a.term).length;row.leanCoreTermErasure=b.output.coreTermErasure;
 }
 report.push(row);
}
// Falsifiers: a one-label change to a Lean term and a one-field change to a
// Lean annotation must each be caught by the same comparison.
const firstAgree=report.findIndex(r=>r.verdict==="agree: same term and typing proposal");
if(firstAgree<0)throw Error("no agreeing job to falsify against");
const mutateLabel=(t:any):boolean=>{if(!t||typeof t!=="object")return false;if(t.tag==="label"){t.value+="\u0000mutated";return true;}return Object.values(t).some(mutateLabel);};
const termCopy=JSON.parse(JSON.stringify(lean[firstAgree].output.term));
if(!mutateLabel(termCopy)||canonical(termCopy)===canonical(lean[firstAgree].output.term))throw Error("term mutation did not happen");
if(canonical(ts[firstAgree].term)===canonical(termCopy))throw Error("FALSIFIER: mutated Lean term still compares equal");
const typedCopy=JSON.parse(JSON.stringify(lean[firstAgree].output.typed));
typedCopy.annotations[0].reuse=typedCopy.annotations[0].reuse==="once"?"reusable":"once";
if(canonical(ts[firstAgree].typed)===canonical(typedCopy))throw Error("FALSIFIER: mutated Lean annotation still compares equal");
writeFileSync(join(work,"report.json"),JSON.stringify(report,null,2)+"\n");
const disagreements=report.filter(r=>r.verdict.startsWith("DISAGREE"));
for(const r of disagreements)console.error(JSON.stringify(r));
const probeRows=report.filter(r=>r.name.startsWith("probe:"));
for(const r of probeRows){const expect=r.name.startsWith("probe:refuse")?"refused":"accepted";
 if(r.ts!==expect)console.error(JSON.stringify({probe:r.name,expected:expect,got:r.ts,error:r.tsError}));}
const badProbes=probeRows.filter(r=>r.ts!==(r.name.startsWith("probe:refuse")?"refused":"accepted")).length;
console.log(JSON.stringify({schema:"dregg.objective-bend.elaboration-translation-validation.v1",status:disagreements.length?"failed":"passed",
 jobs:jobs.length,falsifiers:"term label and annotation reuse mutations detected",agreeAccepted,typedAgree,typedBothUnsupported,agreeRefused,disagreements:disagreements.length,probes:probeRows.length,probesMisclassified:badProbes,report:join(work,"report.json")}));
if(disagreements.length||badProbes)process.exitCode=1;
