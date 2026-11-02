// Actual source preview contract/refusers over the in-repo cohort
// (preview-cohort.json). Each item is captured, elaborated, checked and run by the Lean
// front end (Host/ObjectiveBendFrontEnd: capture, then preview).
// usage: bun check-preview.ts COHORT_JSON NEW_OUTPUT_ROOT LEAN_BINARY LEAN_PATH
import {readFileSync,mkdirSync,writeFileSync,existsSync} from "node:fs";
import {join,resolve,dirname} from "node:path";
import {createHash} from "node:crypto";
import {readPreview,runCommands} from "./front.ts";
const [cohortPath,outputRootRaw,leanBinary,leanPath]=process.argv.slice(2);
if(!cohortPath||!outputRootRaw||!leanBinary||!leanPath)throw Error("usage: check-preview COHORT_JSON NEW_OUTPUT_ROOT LEAN_BINARY LEAN_PATH");
const env={lean:leanBinary,leanPath};
const outputRoot=resolve(outputRootRaw);if(existsSync(outputRoot))throw Error("output root must be new");
const cohortDir=dirname(resolve(cohortPath));
const sha=(path:string)=>createHash("sha256").update(readFileSync(path)).digest("hex");
const failures:string[]=[];
const require=(ok:boolean,message:string)=>{if(!ok)failures.push(message);return ok;};
const canonical=(v:any):string=>JSON.stringify(v&&typeof v==="object"?Array.isArray(v)?v.map(x=>JSON.parse(canonical(x))):Object.fromEntries(Object.keys(v).sort().map(k=>[k,JSON.parse(canonical(v[k]))])):v);
// Typed data with record fields ordered by name (materialization keeps source order).
const norm=(d:any):any=>d?.tag==="record"?{...d,fields:d.fields.map((f:any)=>({name:f.name,value:norm(f.value)})).sort((a:any,b:any)=>a.name<b.name?-1:1)}:d?.tag==="variant"?{...d,payload:norm(d.payload)}:d;
// The activity kernel's protocol (Kernel/ObjectiveActivity: decodePlan, responseData, effectProtocol), for
// rows marked `"protocol":"kernel"`: every yielded Plan is one the kernel performs (`await {write, on,
// patience}`, `transfer {to, amount, write}`, `commit {write}`), and every response is the kernel's
// `resumed {outcome, view}` with an outcome the kernel can deliver for the Plan it answers: an effect is
// decided at its yield (`settled` | `refused`), an await by its slot, height or deadline.
const fieldOf=(d:any,name:string)=>d?.tag==="record"?d.fields.find((f:any)=>f.name===name)?.value:undefined;
const natural=(d:any)=>d?.tag==="natural"&&/^[0-9]+$/.test(String(d.value));
// A transfer is decided `settled` or `refused` at its yield; a commit is always `settled` (its write
// goes through the object's law exactly as an await's: a law refusal refuses the whole turn, so no
// response follows it).
const awaitOutcomes=["reply","refused","unknown","timedOut","broken","upgraded"],transferOutcomes=["settled","refused"],commitOutcomes=["settled"];
const planKind=(p:any):string|null=>{
 if(p?.tag!=="variant"||p.payload?.tag!=="record")return null;
 const f=(n:string)=>fieldOf(p.payload,n);
 if(p.label==="await"){const on=f("on");
  const source=on?.tag==="variant"&&((on.label==="reply"&&natural(fieldOf(on.payload,"decider")))||(on.label==="height"&&natural(fieldOf(on.payload,"at"))));
  return f("write")?.tag==="record"&&source&&natural(f("patience"))&&BigInt(f("patience").value)>0n?"await":null;}
 if(p.label==="transfer")return f("write")?.tag==="record"&&natural(f("to"))&&natural(f("amount"))&&BigInt(f("amount").value)>0n?"transfer":null;
 if(p.label==="commit")return f("write")?.tag==="record"?"commit":null;
 return null;};
const kernelProtocol=(item:any,turns:any[])=>{
 const responses=item.responses??[];
 turns.forEach((turn:any,i:number)=>{
  const kind=planKind(turn.plan);
  if(!require(kind!==null,"not a kernel Plan: "+item.name+" turn "+i+" "+JSON.stringify(turn.plan)))return;
  const r=responses[i];if(r===undefined)return;
  const outcome=fieldOf(r?.payload,"outcome"),view=fieldOf(r?.payload,"view");
  require(r?.tag==="variant"&&r.label==="resumed"&&outcome?.tag==="variant"&&natural(fieldOf(view,"version"))&&fieldOf(view,"state")!==undefined,
   "not a kernel response resumed {outcome, view}: "+item.name+" response "+i);
  require((kind==="transfer"?transferOutcomes:kind==="commit"?commitOutcomes:awaitOutcomes).includes(outcome?.label),
   "outcome the kernel cannot deliver for a "+kind+": "+item.name+" response "+i+" "+outcome?.label);});};
mkdirSync(outputRoot,{recursive:true});
const cohort=JSON.parse(readFileSync(cohortPath,"utf8"));
const requests:string[]=[];const results:any[]=[];
const captureCmds:string[][]=[];
for(const item of cohort){
 const dir=join(outputRoot,item.name);mkdirSync(dir);
 const packageInput={schema:"dregg.objective-bend.package-input.v1",edition:"objective-bend-1",
  modules:item.modules.map((m:any)=>({name:m.name,sourcePath:join(cohortDir,m.source),imports:m.imports??[]})),
  entryModule:String(item.modules.length-1),entryDefinition:item.entry};
 const packagePath=join(dir,"package-input.json");writeFileSync(packagePath,JSON.stringify(packageInput,null,2)+"\n",{flag:"wx"});
 captureCmds.push(["capture",packagePath,join(dir,"capture")]);
}
const captureCmdsPath=join(outputRoot,"capture-commands.json");
writeFileSync(captureCmdsPath,JSON.stringify(captureCmds)+"\n",{flag:"wx"});
runCommands(captureCmdsPath,env);
const previewCmds:string[][]=[];
for(const item of cohort){
 const dir=join(outputRoot,item.name);
 const capturePath=join(dir,"capture","objective.json");
 const request={schema:"dregg.objective-bend.preview-input.v2",capturePath,captureSha256:sha(capturePath),
  argumentEncoding:item.argumentEncoding??"legacy-values-v1",arguments:item.arguments,projections:item.projections??[],responses:item.responses??[],
  limits:{ticks:"100000",heap:"100000",stack:"10000",typeFuel:"4096"}};
 const requestPath=join(dir,"request.json");writeFileSync(requestPath,JSON.stringify(request,null,2)+"\n",{flag:"wx"});requests.push(requestPath);
 previewCmds.push(["preview",requestPath,join(dir,"preview")]);
}
const firstFinished=cohort.findIndex((c:any)=>c.expectedStatus!=="refused");
const original=JSON.parse(readFileSync(requests[firstFinished],"utf8"));
const refuserSpecs=[
 ["WrongCapture",{captureSha256:"0".repeat(64)},"refused"],
 ["TypingBudget",{limits:{...original.limits,typeFuel:"1"}},"refused"],
 ["Ticks",{limits:{...original.limits,ticks:"1"}},"suspended"],
 ["Capacity",{limits:{...original.limits,heap:"1"}},"suspended"]
] as const;
for(const [name,change] of refuserSpecs){
 const request=join(outputRoot,name+"-request.json");writeFileSync(request,JSON.stringify({...original,...change})+"\n",{flag:"wx"});
 previewCmds.push(["preview",request,join(outputRoot,name)]);
}
const previewCmdsPath=join(outputRoot,"preview-commands.json");
writeFileSync(previewCmdsPath,JSON.stringify(previewCmds)+"\n",{flag:"wx"});
runCommands(previewCmdsPath,env);
for(const item of cohort){
 const dir=join(outputRoot,item.name);
 const out:any=readPreview(join(dir,"preview"));
 const turns=out.preview?.turns??[];
 results.push({name:item.name,status:out.status,type:out.preview?.type?.tag??null,result:out.preview?.result??null,turns:turns.length,diagnostic:out.diagnostic?.message??null});
 if(item.expectedStatus==="refused"){require(out.status==="refused","source typing refusal differs: "+item.name+" "+out.status);
  // The preview names the kind of rule that refused (Host/ObjectiveBendPreview.refusalReason).
  if(item.expectedRefusal!==undefined)require(String(out.diagnostic?.message??"").startsWith(item.expectedRefusal),"refusal reason differs: "+item.name+" "+out.diagnostic?.message);
  continue;}
 // Activities: every yield is quiescent and its checkpoint round-trips (executed, not proved here).
 for(const turn of turns)require(turn.quiescent===true&&turn.checkpointRoundTrips===true,"yield not a quiescent round-tripping checkpoint: "+item.name);
 if(item.protocol==="kernel")kernelProtocol(item,turns);
 if(item.expectedTurns!==undefined)require(turns.length===item.expectedTurns,"turn count differs: "+item.name+" "+turns.length);
 if(item.expectedLastPlan!==undefined)require(turns.length>0&&canonical(norm(turns[turns.length-1].plan))===canonical(norm(item.expectedLastPlan)),"yielded plan differs: "+item.name+" "+JSON.stringify(turns.at(-1)?.plan));
 if(item.expectedStatus==="yielded"){require(out.status==="yielded"&&out.preview.result===null,"activity did not stop at a yield: "+item.name+" "+out.status);continue;}
 // Budget exhaustion is a verdict, not an error: the preview stopped at its tick budget and shows no result.
 if(item.expectedStatus==="suspended"){require(out.status==="suspended"&&out.preview.result===null&&out.preview.resultData===null,"program did not suspend at its budget: "+item.name+" "+out.status);continue;}
 if(!require(out.status==="finished","preview did not finish: "+item.name+" "+out.status+" "+JSON.stringify(out.diagnostic??out.preview?.diagnostic)))continue;
 // An activity's checked type is Activity<Plan, Response, Result>; its finished value has type Result.
 const resultType=out.preview.type.tag==="computation"?out.preview.type.result:out.preview.type;
 require(resultType.tag===(item.expectedType??"natural"),"actual typed source result type differs: "+item.name+" "+resultType.tag);
 // `result` is the weak-head view; `resultData` is the deep view (every field and payload forced). expectedData pins a structured result.
 if(item.expectedData!==undefined){
  require(out.preview.resultDataStatus==="materialized"&&canonical(norm(out.preview.resultData))===canonical(norm(item.expectedData)),"deep result differs: "+item.name+" "+out.preview.resultDataStatus+" "+JSON.stringify(out.preview.resultData));
  require(out.preview.result.tag===out.preview.resultData?.tag,"weak-head and deep result disagree on the constructor: "+item.name);
 }
 else if(item.expectedDataStatus!==undefined)require(out.preview.resultDataStatus===item.expectedDataStatus&&out.preview.resultData===null&&out.preview.result.tag==="record","deep view status differs: "+item.name+" "+out.preview.resultDataStatus+" "+JSON.stringify(out.preview.resultData));
 else require(item.expectedRecord?out.preview.result.tag==="record":out.preview.result.value===item.expected,"actual typed source result differs: "+item.name+" "+JSON.stringify(out.preview.result));
 // A scalar result is its own deep view.
 if(out.preview.result.value!==undefined)require(canonical(out.preview.resultData)===canonical(out.preview.result),"deep view of a scalar differs from its weak-head view: "+item.name+" "+JSON.stringify(out.preview.resultData));
 require(out.preview.sameDecodedTerm===true&&out.preview.uses.length===0,"checked/executed join differs: "+item.name);
}
for(const [name,_,expect] of refuserSpecs){
 const result:any=readPreview(join(outputRoot,name));
 require(result.status===expect,"preview refusal/exhaustion differs: "+name+" "+result.status);
 if(name==="TypingBudget")require(String(result.diagnostic?.message??"").startsWith("checker budget refused"),"a budget refusal is not named as one: "+result.diagnostic?.message);
 require(expect!=="suspended"||result.preview?.result===null,"exhaustion falsely returned a source result");
}
writeFileSync(join(outputRoot,"results.json"),JSON.stringify(results,null,2)+"\n");
if(failures.length){console.error(JSON.stringify({schema:"dregg.objective-bend.preview-cohort-check.v1",status:"failed",failures}));process.exit(1);}
console.log(JSON.stringify({schema:"dregg.objective-bend.preview-cohort-check.v1",status:"passed",sourceResults:results.map(r=>r.name+":"+r.status+(r.result?.value!==undefined?"="+r.result.value:"")),refusers:["capture identity","typing budget"],suspensions:["ticks","capacity"]}));
