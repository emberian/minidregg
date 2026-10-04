// Actual source preview contract/refusers over the in-repo cohort
// (preview-cohort.json). Each item is captured by the real frontend, elaborated
// by the real elaborator and checked + run by Host/ObjectiveBendPreview.
// usage: bun check-preview.ts COHORT_JSON NEW_OUTPUT_ROOT LEAN_BINARY OLEAN_ROOT [BUN_BINARY]
import {readFileSync,mkdirSync,writeFileSync,existsSync} from "node:fs";
import {join,resolve,dirname} from "node:path";
import {createHash} from "node:crypto";
import {preview} from "../../native/bend-source/objective-preview.ts";
import {captureObjective} from "../../native/bend-source/objective-frontend.ts";
const [cohortPath,outputRootRaw,leanPath,oleanRoot,bunPath=process.execPath]=process.argv.slice(2);
if(!cohortPath||!outputRootRaw||!leanPath||!oleanRoot)throw Error("usage: check-preview COHORT_JSON NEW_OUTPUT_ROOT LEAN_BINARY OLEAN_ROOT [BUN_BINARY]");
const outputRoot=resolve(outputRootRaw);if(existsSync(outputRoot))throw Error("output root must be new");
const repo=resolve(import.meta.dirname,"../..");const cohortDir=dirname(resolve(cohortPath));
const sha=(path:string)=>createHash("sha256").update(readFileSync(path)).digest("hex");
const failures:string[]=[];
const require=(ok:boolean,message:string)=>{if(!ok)failures.push(message);return ok;};
const canonical=(v:any):string=>JSON.stringify(v&&typeof v==="object"?Array.isArray(v)?v.map(x=>JSON.parse(canonical(x))):Object.fromEntries(Object.keys(v).sort().map(k=>[k,JSON.parse(canonical(v[k]))])):v);
// Typed data with record fields ordered by name (materialization keeps source order).
const norm=(d:any):any=>d?.tag==="record"?{...d,fields:d.fields.map((f:any)=>({name:f.name,value:norm(f.value)})).sort((a:any,b:any)=>a.name<b.name?-1:1)}:d?.tag==="variant"?{...d,payload:norm(d.payload)}:d;
mkdirSync(outputRoot,{recursive:true});
const tool=(rel:string)=>join(repo,rel);
const tooling={schema:"dregg.objective-bend.preview-tooling.v2",bunPath,leanPath,oleanRoot,
 elaboratorPath:tool("native/bend-source/objective-elaborate.ts"),parserPath:tool("native/bend-source/objective-parser.ts"),
 previewHostPath:tool("Host/ObjectiveBendPreview.lean"),
 pins:[["elaborator","native/bend-source/objective-elaborate.ts"],["parser","native/bend-source/objective-parser.ts"],["preview-host","Host/ObjectiveBendPreview.lean"]]
  .map(([role,rel])=>({role,path:tool(rel),sha256:sha(tool(rel))}))};
const toolingPath=join(outputRoot,"tooling.json");writeFileSync(toolingPath,JSON.stringify(tooling,null,2)+"\n",{flag:"wx"});
const cohort=JSON.parse(readFileSync(cohortPath,"utf8"));
const requests:string[]=[];const results:any[]=[];
for(const item of cohort){
 const dir=join(outputRoot,item.name);mkdirSync(dir);
 const packageInput={schema:"dregg.objective-bend.package-input.v1",edition:"objective-bend-1",
  modules:item.modules.map((m:any)=>({name:m.name,sourcePath:join(cohortDir,m.source),imports:m.imports??[]})),
  entryModule:String(item.modules.length-1),entryDefinition:item.entry};
 const packagePath=join(dir,"package-input.json");writeFileSync(packagePath,JSON.stringify(packageInput,null,2)+"\n",{flag:"wx"});
 captureObjective(packagePath,join(dir,"capture"));
 const capturePath=join(dir,"capture","objective.json");
 const request={schema:"dregg.objective-bend.preview-input.v2",capturePath,captureSha256:sha(capturePath),
  argumentEncoding:item.argumentEncoding??"legacy-values-v1",arguments:item.arguments,projections:item.projections??[],responses:item.responses??[],
  limits:{ticks:"100000",heap:"100000",stack:"10000",typeFuel:"4096"}};
 const requestPath=join(dir,"request.json");writeFileSync(requestPath,JSON.stringify(request,null,2)+"\n",{flag:"wx"});requests.push(requestPath);
 let out:any;try{out=preview(requestPath,join(dir,"preview"),toolingPath);}catch(error){out=error;}
 const turns=out.preview?.turns??[];
 results.push({name:item.name,status:out.status,type:out.preview?.type?.tag??null,result:out.preview?.result??null,turns:turns.length,diagnostic:out.diagnostic?.message??null});
 if(item.expectedStatus==="refused"){require(out.status==="refused","source typing refusal differs: "+item.name+" "+out.status);continue;}
 // Activities: every yield is quiescent and its checkpoint round-trips (executed, not proved here).
 for(const turn of turns)require(turn.quiescent===true&&turn.checkpointRoundTrips===true,"yield not a quiescent round-tripping checkpoint: "+item.name);
 if(item.expectedTurns!==undefined)require(turns.length===item.expectedTurns,"turn count differs: "+item.name+" "+turns.length);
 if(item.expectedLastPlan!==undefined)require(turns.length>0&&canonical(norm(turns[turns.length-1].plan))===canonical(norm(item.expectedLastPlan)),"yielded plan differs: "+item.name+" "+JSON.stringify(turns.at(-1)?.plan));
 if(item.expectedStatus==="yielded"){require(out.status==="yielded"&&out.preview.result===null,"activity did not stop at a yield: "+item.name+" "+out.status);continue;}
 if(!require(out.status==="finished","preview did not finish: "+item.name+" "+out.status+" "+JSON.stringify(out.diagnostic??out.preview?.diagnostic)))continue;
 // An activity's checked type is Activity<Plan, Response, Result>; its finished value has type Result.
 const resultType=out.preview.type.tag==="computation"?out.preview.type.result:out.preview.type;
 require(resultType.tag===(item.expectedType??"natural"),"actual typed source result type differs: "+item.name+" "+resultType.tag);
 require(item.expectedRecord?out.preview.result.tag==="record":out.preview.result.value===item.expected,"actual typed source result differs: "+item.name+" "+JSON.stringify(out.preview.result));
 require(out.preview.sameDecodedTerm===true&&out.preview.uses.length===0,"checked/executed join differs: "+item.name);
}
const firstFinished=cohort.findIndex((c:any)=>c.expectedStatus!=="refused");
const original=JSON.parse(readFileSync(requests[firstFinished],"utf8"));
for(const [name,change,expect] of [
 ["WrongCapture",{captureSha256:"0".repeat(64)},"refused"],
 ["TypingBudget",{limits:{...original.limits,typeFuel:"1"}},"refused"],
 ["Ticks",{limits:{...original.limits,ticks:"1"}},"suspended"],
 ["Capacity",{limits:{...original.limits,heap:"1"}},"suspended"]
] as const){
 const request=join(outputRoot,name+"-request.json");writeFileSync(request,JSON.stringify({...original,...change})+"\n",{flag:"wx"});
 let result:any;try{result=preview(request,join(outputRoot,name),toolingPath);}catch(error){result=error;}
 require(result.status===expect,"preview refusal/exhaustion differs: "+name+" "+result.status);
 require(expect!=="suspended"||result.preview.result===null,"exhaustion falsely returned a source result");
}
writeFileSync(join(outputRoot,"results.json"),JSON.stringify(results,null,2)+"\n");
if(failures.length){console.error(JSON.stringify({schema:"dregg.objective-bend.preview-cohort-check.v1",status:"failed",failures}));process.exit(1);}
console.log(JSON.stringify({schema:"dregg.objective-bend.preview-cohort-check.v1",status:"passed",sourceResults:results.map(r=>r.name+":"+r.status+(r.result?.value!==undefined?"="+r.result.value:"")),refusers:["capture identity","typing budget"],suspensions:["ticks","capacity"]}));
