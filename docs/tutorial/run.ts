// Run one .obend file through the front end and the preview.
//
//   bun docs/tutorial/run.ts FILE.obend ENTRY [ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]
//
// ENTRY is the name of a `def` in FILE. ARGS_JSON is an array of arguments
// (Nats as decimal strings, as in "[\"7\"]"). RESPONSES_JSON is an array of
// responses for an activity: a label such as "written" stands for that label
// with an empty record payload; a full typed-data object is passed through.
// --ticks N sets the tick budget (default 100000). --json prints the preview
// result unchanged instead of the short form.
//
// Environment: LEAN (default `lean`) and OLEAN_ROOT (default
// <repo>/.lake/build/lib/lean, which must hold the compiled Theory modules that
// Host/ObjectiveBendPreview.lean imports).
import {readFileSync,writeFileSync,mkdirSync,mkdtempSync} from "node:fs";
import {join,resolve,basename} from "node:path";
import {tmpdir} from "node:os";
import {createHash} from "node:crypto";
import {captureObjective} from "../../native/bend-source/objective-frontend.ts";
import {preview} from "../../native/bend-source/objective-preview.ts";

const repo=resolve(import.meta.dirname,"../..");
const argv=process.argv.slice(2);
const flag=(name:string)=>{const i=argv.indexOf(name);if(i<0)return undefined;const v=name==="--json"?"1":argv[i+1];argv.splice(i,name==="--json"?1:2);return v;};
const raw=flag("--json")!==undefined;const ticks=flag("--ticks")??"100000";
const [file,entry,argsJson0,responsesJson0]=argv;
const argsJson=argsJson0||"[]",responsesJson=responsesJson0||"[]";
if(!file||!entry){console.error("usage: bun docs/tutorial/run.ts FILE.obend ENTRY [ARGS_JSON] [RESPONSES_JSON] [--ticks N] [--json]");process.exit(64);}
const sha=(p:string)=>createHash("sha256").update(readFileSync(p)).digest("hex");
const work=mkdtempSync(join(tmpdir(),"obend-tutorial-"));
const tool=(rel:string)=>join(repo,rel);
const tooling={schema:"dregg.objective-bend.preview-tooling.v2",bunPath:process.execPath,leanPath:process.env.LEAN??"lean",
 oleanRoot:process.env.OLEAN_ROOT??join(repo,".lake/build/lib/lean"),
 elaboratorPath:tool("native/bend-source/objective-elaborate.ts"),parserPath:tool("native/bend-source/objective-parser.ts"),
 previewHostPath:tool("Host/ObjectiveBendPreview.lean"),
 pins:[["elaborator","native/bend-source/objective-elaborate.ts"],["parser","native/bend-source/objective-parser.ts"],["preview-host","Host/ObjectiveBendPreview.lean"]]
  .map(([role,rel])=>({role,path:tool(rel),sha256:sha(tool(rel))}))};
const toolingPath=join(work,"tooling.json");writeFileSync(toolingPath,JSON.stringify(tooling));
const packagePath=join(work,"package.json");
writeFileSync(packagePath,JSON.stringify({schema:"dregg.objective-bend.package-input.v1",edition:"objective-bend-1",
 modules:[{name:basename(file).replace(/\.obend$/,"").replace(/[^A-Za-z0-9_]/g,"_").replace(/^[0-9]+/,m=>"M"+m),sourcePath:resolve(file),imports:[]}],
 entryModule:"0",entryDefinition:entry}));
let result:any;
try{
 captureObjective(packagePath,join(work,"capture"));
 const capturePath=join(work,"capture","objective.json");
 const responses=JSON.parse(responsesJson).map((r:any)=>typeof r==="string"?{tag:"variant",label:r,payload:{tag:"record",fields:[]}}:r);
 const request={schema:"dregg.objective-bend.preview-input.v2",capturePath,captureSha256:sha(capturePath),argumentEncoding:"legacy-values-v1",
  arguments:JSON.parse(argsJson),projections:[],responses,limits:{ticks,heap:"100000",stack:"10000",typeFuel:"4096"}};
 const requestPath=join(work,"request.json");writeFileSync(requestPath,JSON.stringify(request));
 result=preview(requestPath,join(work,"preview"),toolingPath);
}catch(error:any){result=error;if(error?.schema==="dregg.bend.compiler-diagnostic.v1")result={status:"refused",diagnostic:error};else if(!error?.diagnostic&&!error?.preview){console.error(String(error?.stack??error));process.exit(1);}}

// ---- short form ----
const ty=(t:any):string=>{
 switch(t?.tag){
  case "natural":return "Nat";case "boolean":return "Bool";case "label":return "String";case "emptyRow":return "{}";case "variable":return "variable "+t.index;
  case "field":{const parts:string[]=[];let r=t;while(r?.tag==="field"){parts.push(r.name+": "+ty(r.member));r=r.tail;}return "{"+parts.join(", ")+"}";}
  case "variant":return "sum "+ty(t.row);
  case "computation":return "Activity<"+ty(t.plan)+", "+ty(t.response)+", "+ty(t.result)+">";
  default:return JSON.stringify(t);}};
const data=(d:any):string=>{
 switch(d?.tag){
  case "natural":return d.value;case "boolean":return String(d.value);case "label":return JSON.stringify(d.value);
  case "record":return "{"+d.fields.map((f:any)=>typeof f==="string"?f:f.name+": "+data(f.value)).join(", ")+"}";
  case "variant":return d.label+"("+(d.payload?data(d.payload):"...")+")";
  default:return JSON.stringify(d);}};
if(raw){console.log(JSON.stringify(result.preview??result,null,2));process.exit(result.status==="refused"?2:0);}
const p=result.preview;
if(result.status==="refused"&&!p){
 const d=result.diagnostic??{};console.log("status: refused\nstage: "+(d.childDiagnostic?.stage??d.stage??"?")+"\nmessage: "+(d.message??JSON.stringify(d)));process.exit(2);}
console.log("status: "+result.status);
console.log("type: "+ty(p.type));
for(const [i,t] of (p.turns??[]).entries())
 console.log("turn "+(i+1)+": yield "+data(t.plan)+(t.response?"  <- "+data(t.response):"  (waiting)"));
if(p.result!==null&&p.result!==undefined)console.log("result: "+data(p.result));
if(p.diagnostic)console.log("diagnostic: "+p.diagnostic);
