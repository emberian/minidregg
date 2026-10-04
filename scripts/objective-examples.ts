// Objective Bend reference examples: regenerate or verify the typed packets.
//
// Each example `reference/<Name>.lean` embeds `reference/<Name>.typed.json`, the
// typed core packet the CURRENT front end (parser -> capture -> elaborator ->
// annotation proposal) produces for the cohort row `<Name>` in
// tests/objective-bend-source/preview-cohort.json. The cohort row is the single
// description of the entry point and its arguments; nothing is restated here.
//
// usage: bun scripts/objective-examples.ts check|refresh WORK_DIR BUN LEAN OLEAN_ROOT NAME...
//   check   fails (exit 1) unless the freshly produced packet is byte-identical to the
//           committed one, and writes WORK_DIR/<Name>.expected.json: the cohort row's
//           status, type and result as the driver's `main` must print them.
//   refresh overwrites the committed packet.
import {readFileSync,writeFileSync,mkdirSync,existsSync} from "node:fs";
import {join,resolve,dirname} from "node:path";
import {createHash} from "node:crypto";
import {preview} from "../native/bend-source/objective-preview.ts";
import {captureObjective} from "../native/bend-source/objective-frontend.ts";
const [mode,workRaw,bunPath,leanPath,oleanRoot,...names]=process.argv.slice(2);
if(!["check","refresh"].includes(mode)||!workRaw||!bunPath||!leanPath||!oleanRoot||names.length===0)
 throw Error("usage: objective-examples check|refresh WORK_DIR BUN LEAN OLEAN_ROOT NAME...");
const repo=resolve(import.meta.dirname,"..");
const cohortPath=join(repo,"tests/objective-bend-source/preview-cohort.json"),cohortDir=dirname(cohortPath);
const referenceDir=join(repo,"examples/objective-bend-world/reference");
const work=resolve(workRaw);if(existsSync(work))throw Error("work directory must be new: "+work);mkdirSync(work,{recursive:true});
const sha=(path:string)=>createHash("sha256").update(readFileSync(path)).digest("hex");
const tool=(rel:string)=>join(repo,rel);
const tooling={schema:"dregg.objective-bend.preview-tooling.v2",bunPath,leanPath,oleanRoot,
 elaboratorPath:tool("native/bend-source/objective-elaborate.ts"),parserPath:tool("native/bend-source/objective-parser.ts"),
 previewHostPath:tool("Host/ObjectiveBendPreview.lean"),
 pins:[["elaborator","native/bend-source/objective-elaborate.ts"],["parser","native/bend-source/objective-parser.ts"],["preview-host","Host/ObjectiveBendPreview.lean"]]
  .map(([role,rel])=>({role,path:tool(rel),sha256:sha(tool(rel))}))};
const toolingPath=join(work,"tooling.json");writeFileSync(toolingPath,JSON.stringify(tooling,null,2)+"\n");
const cohort=JSON.parse(readFileSync(cohortPath,"utf8"));
let failed=false;
for(const name of names){
 const row=cohort.find((c:any)=>c.name===name);
 if(!row||row.expectedStatus!==undefined||row.expectedRecord||row.responses)throw Error("not a finished, scalar, response-free cohort row: "+name);
 const dir=join(work,name);mkdirSync(dir);
 const packageInput={schema:"dregg.objective-bend.package-input.v1",edition:"objective-bend-1",
  modules:row.modules.map((m:any)=>({name:m.name,sourcePath:join(cohortDir,m.source),imports:m.imports??[]})),
  entryModule:String(row.modules.length-1),entryDefinition:row.entry};
 const packagePath=join(dir,"package-input.json");writeFileSync(packagePath,JSON.stringify(packageInput,null,2)+"\n");
 captureObjective(packagePath,join(dir,"capture"));
 const capturePath=join(dir,"capture","objective.json");
 const request={schema:"dregg.objective-bend.preview-input.v2",capturePath,captureSha256:sha(capturePath),
  argumentEncoding:row.argumentEncoding??"legacy-values-v1",arguments:row.arguments,projections:row.projections??[],responses:[],
  limits:{ticks:"100000",heap:"100000",stack:"10000",typeFuel:"4096"}};
 const requestPath=join(dir,"request.json");writeFileSync(requestPath,JSON.stringify(request,null,2)+"\n");
 const out=preview(requestPath,join(dir,"preview"),toolingPath);
 if(out.status!=="finished"){console.error("example did not finish: "+name+" "+out.status);failed=true;continue;}
 const fresh=readFileSync(join(dir,"preview","source.typed.json"),"utf8");
 const committedPath=join(referenceDir,name+".typed.json");
 if(mode==="refresh")writeFileSync(committedPath,fresh);
 else if(!existsSync(committedPath)||readFileSync(committedPath,"utf8")!==fresh){console.error("STALE typed packet: "+name+" (run scripts/check-objective-examples.sh --refresh)");failed=true;}
 // What the driver's main must print: the cohort row's expectation, not the preview's own output.
 const resultType=out.preview.type.tag;
 const expectedResult=row.expectedType==="boolean"?{tag:"boolean",value:row.expected}:row.expectedType==="label"?{tag:"label",value:row.expected}:{tag:"natural",value:row.expected};
 writeFileSync(join(work,name+".expected.json"),JSON.stringify({name,status:"finished",type:row.expectedType??"natural",result:expectedResult,uses:[],typing:"accepted by actual annotated checker"})+"\n");
 if(resultType!==(row.expectedType??"natural")){console.error("cohort type differs from preview type: "+name+" "+resultType);failed=true;}
}
process.exit(failed?1:0);
