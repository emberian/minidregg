// LTUO characterization probes (OB-LTUO LT0; docs/objective-bend/MODULAR-TYPING.md).
// Each row of probe-cohort.json pins the CURRENT outcome of one probe through the one
// Lean front end (capture, then preview: parse, elaborate, check, run) and names the
// TARGET outcome the LT row that owns it must reach. The gate is the current outcome:
//   - actual == current, target != current  -> pending (the row's LT work is not done)
//   - actual == current == target           -> met
//   - actual != current                     -> RED. If actual == target the LT work
//     landed: promote the row (current := target). Otherwise the front end moved
//     somewhere nobody asked for.
// So a target can never turn green silently, and nothing here is allowed to drift.
// usage: bun check-probes.ts COHORT_JSON NEW_OUTPUT_ROOT LEAN_BINARY LEAN_PATH
import {readFileSync,mkdirSync,writeFileSync,existsSync} from "node:fs";
import {join,resolve,dirname} from "node:path";
import {createHash} from "node:crypto";
import {capture,preview} from "../front.ts";
const [cohortPath,outputRootRaw,lean,leanPath]=process.argv.slice(2);
if(!cohortPath||!outputRootRaw||!lean||!leanPath)throw Error("usage: check-probes COHORT_JSON NEW_OUTPUT_ROOT LEAN_BINARY LEAN_PATH");
const env={lean,leanPath};
const outputRoot=resolve(outputRootRaw);if(existsSync(outputRoot))throw Error("output root must be new");
mkdirSync(outputRoot,{recursive:true});
const cohortDir=dirname(resolve(cohortPath));
const sha=(p:string)=>createHash("sha256").update(readFileSync(p)).digest("hex");
type Outcome={status:string,value?:string,refusal?:string};
const actualOf=(item:any):{outcome:Outcome,message:string}=>{
 const dir=join(outputRoot,item.name);mkdirSync(dir);
 const packagePath=join(dir,"package-input.json");
 writeFileSync(packagePath,JSON.stringify({schema:"dregg.objective-bend.package-input.v1",edition:"objective-bend-1",
  modules:item.modules.map((m:any)=>({name:m.name,sourcePath:join(cohortDir,m.source),imports:m.imports??[]})),
  entryModule:String(item.modules.length-1),entryDefinition:item.entry},null,2)+"\n",{flag:"wx"});
 try{capture(packagePath,join(dir,"capture"),env);}
 catch(e:any){const message=String(e?.message??e);return {outcome:{status:"refused",refusal:message},message};}
 const capturePath=join(dir,"capture","objective.json");
 const requestPath=join(dir,"request.json");
 writeFileSync(requestPath,JSON.stringify({schema:"dregg.objective-bend.preview-input.v2",capturePath,captureSha256:sha(capturePath),
  argumentEncoding:"legacy-values-v1",arguments:item.arguments??[],projections:[],responses:[],
  limits:{ticks:"100000",heap:"100000",stack:"10000",typeFuel:"4096"}},null,2)+"\n",{flag:"wx"});
 const out:any=preview(requestPath,join(dir,"preview"),env);
 const message=String(out.diagnostic?.message??"");
 if(out.status==="finished")return {outcome:{status:"finished",value:String(out.preview?.result?.value)},message};
 return {outcome:{status:out.status,refusal:message},message};
};
// A pinned refusal is a prefix of the actual diagnostic (the diagnostic may carry more).
const matches=(actual:Outcome,pinned:Outcome)=>actual.status===pinned.status&&
 (pinned.value===undefined||actual.value===pinned.value)&&
 (pinned.refusal===undefined||(actual.refusal??"").startsWith(pinned.refusal));
const cohort=JSON.parse(readFileSync(cohortPath,"utf8"));
const red:string[]=[];const rows:any[]=[];
for(const item of cohort){
 if(!item.current||!item.target||!item.owner)throw Error("probe row needs current, target and owner: "+item.name);
 const {outcome,message}=actualOf(item);
 const isCurrent=matches(outcome,item.current);
 const targetMet=matches(outcome,item.target);
 const promoted=JSON.stringify(item.current)===JSON.stringify(item.target);
 let verdict:string;
 if(!isCurrent)verdict=targetMet?"RED: meets its target; promote current := target":"RED: outcome moved, matches neither current nor target";
 else verdict=promoted?"met":"pending "+item.owner;
 if(!isCurrent)red.push(item.name+": "+verdict+" actual="+JSON.stringify(outcome));
 rows.push({name:item.name,owner:item.owner,verdict,actual:outcome,diagnostic:message});
}
writeFileSync(join(outputRoot,"results.json"),JSON.stringify(rows,null,2)+"\n");
for(const r of rows)console.log(r.name.padEnd(28)+" "+r.verdict.padEnd(14)+" "+r.actual.status+(r.actual.value!==undefined?"="+r.actual.value:"")+(r.diagnostic?"  ["+r.diagnostic.slice(0,160)+"]":""));
if(red.length){console.error(JSON.stringify({schema:"dregg.objective-bend.ltuo-probes.v1",status:"failed",red}));process.exit(1);}
const pending=rows.filter(r=>r.verdict.startsWith("pending"));
console.log("LTUO PROBES CURRENT: "+rows.length+" rows pinned, "+(rows.length-pending.length)+" at target, "+pending.length+" pending ("+[...new Set(pending.map(r=>r.owner))].join(" ")+")");
