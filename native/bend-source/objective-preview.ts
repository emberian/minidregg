// One generic source preview pipeline. The actual checker and demand machine
// share a decoded Term; this adapter binds source/core/tooling/resource bytes.
import {readFileSync,writeFileSync,mkdirSync,readdirSync} from "node:fs";
import {dirname,join,resolve} from "node:path";
import {createHash} from "node:crypto";
import {execFileSync} from "node:child_process";
const sha=(bytes:Uint8Array)=>createHash("sha256").update(bytes).digest("hex");
const encode=(value:any)=>JSON.stringify(value,null,2)+"\n";
const json=(path:string)=>JSON.parse(readFileSync(path,"utf8"));
const canonical=(value:any):string=>JSON.stringify(value&&typeof value==="object"?Array.isArray(value)?value.map(v=>JSON.parse(canonical(v))):Object.fromEntries(Object.keys(value).sort().map(k=>[k,JSON.parse(canonical(value[k]))])):value);
const count=(value:unknown,key:string,cap:number)=>{if(typeof value!=="string"||! /^[1-9][0-9]*$/.test(value)||BigInt(value)>BigInt(cap))throw new Error("invalid preview capacity: "+key);return value;};
function child(command:string,args:string[],env:Record<string,string>={}){
 try{return execFileSync(command,args,{encoding:"utf8",timeout:150000,maxBuffer:4194304,env:{...process.env,...env},killSignal:"SIGKILL"});}
 catch(error:any){let diagnostic:any;for(const text of [String(error.stderr??""),String(error.stdout??"")])try{diagnostic=JSON.parse(text.trim().split("\n").at(-1)!);break;}catch{}
  throw {schema:"dregg.bend.compiler-diagnostic.v1",stage:"objective-preview-child",message:diagnostic?.message??String(error),childDiagnostic:diagnostic??null,exitStatus:error.status??null};}
}
export function preview(requestPath:string,outputDirectory:string,toolingPath:string){
 let stage="preview-request";let binding:any={};
 try{
  const requestBytes=readFileSync(requestPath),request=JSON.parse(new TextDecoder("utf-8",{fatal:true}).decode(requestBytes));
  binding.previewRequestSha256=sha(requestBytes);
  if(request.schema!=="dregg.objective-bend.preview-input.v2"||typeof request.capturePath!=="string"||typeof request.captureSha256!=="string")throw new Error("preview input schema/capture pin required");
  const captureBytes=readFileSync(request.capturePath);if(sha(captureBytes)!==request.captureSha256)throw new Error("captured package identity differs");
  const capture=JSON.parse(new TextDecoder("utf-8",{fatal:true}).decode(captureBytes));
  if(capture.schema!=="dregg.objective-bend.captured-package.v1"||capture.edition!=="objective-bend-1")throw new Error("captured Objective edition required");
  binding={...binding,captureSha256:sha(captureBytes),sourceRequestSha256:capture.requestSha256,edition:capture.edition,sourceEntry:capture.sourceEntry,
   modules:capture.modules.map((m:any)=>({name:m.name,sourceSha256:m.sha256,astSha256:m.astSha256,imports:m.imports}))};
  if(!Array.isArray(request.arguments)||!Array.isArray(request.projections))throw new Error("arguments/projections arrays required");
  const argumentEncoding=request.argumentEncoding??"legacy-values-v1";
  if(!["legacy-values-v1","typed-values-v1"].includes(argumentEncoding))throw new Error("unknown preview argument encoding");
  const argumentsWire=argumentEncoding==="typed-values-v1"?{schema:"dregg.objective-bend.argument-values.v1",values:request.arguments}:request.arguments;
  binding.argumentEncoding=argumentEncoding;
  const limits={ticks:count(request.limits?.ticks,"ticks",100000),heap:count(request.limits?.heap,"heap",100000),stack:count(request.limits?.stack,"stack",100000)};
  const typeFuel=count(request.limits?.typeFuel,"typeFuel",16384);
  stage="preview-tooling";const toolingBytes=readFileSync(toolingPath),tooling=JSON.parse(toolingBytes.toString());
  if(tooling.schema!=="dregg.objective-bend.preview-tooling.v2"||!Array.isArray(tooling.pins))throw new Error("pinned tooling configuration required");
  for(const pin of tooling.pins)if(sha(readFileSync(pin.path))!==pin.sha256)throw new Error("changed preview tooling: "+pin.role);
  if(sha(readFileSync(tooling.parserPath))!==capture.parserSourceSha256)throw new Error("capture parser edition differs from configured parser");
  binding.toolingManifestSha256=sha(toolingBytes);binding.tooling=tooling.pins;binding.limits={...limits,typeFuel};
  mkdirSync(outputDirectory,{recursive:true});if(readdirSync(outputDirectory).length)throw new Error("preview output directory must be empty");
  const retainedCapture=resolve(join(outputDirectory,"capture.json"));writeFileSync(retainedCapture,captureBytes,{flag:"wx"});
  const runner=resolve(join(outputDirectory,"source"));stage="objective-core-elaboration";
  const lowering=child(tooling.bunPath,[tooling.elaboratorPath,retainedCapture,runner,JSON.stringify(argumentsWire),JSON.stringify(request.projections),JSON.stringify(limits)]);
  writeFileSync(join(outputDirectory,"lowering.json"),lowering,{flag:"wx"});
  const corePath=runner+".core.json",typedPath=runner+".typed.json";const coreBytes=readFileSync(corePath),typedBytes=readFileSync(typedPath),core=JSON.parse(coreBytes.toString()),typed=JSON.parse(typedBytes.toString());
  binding.coreSha256=sha(coreBytes);binding.sourceEntry=core.sourceEntry;
  if(core.schema!=="dregg.objective-bend.core.v2"||core.edition!=="objective-bend-1")throw new Error("Objective runtime wire edition2 required");
  if(typed.schema!=="dregg.objective-bend.typed-core.v2")throw {schema:"dregg.bend.compiler-diagnostic.v1",stage:"objective-source-type-proposal",message:typed.message??"source annotation proposal unsupported",span:typed.span??null};
  if(canonical(typed.term)!==canonical(core.term))throw new Error("checker packet term differs from actual elaborated core");
  typed.fuel=typeFuel;const submitted=join(outputDirectory,"typed-input.json"),limitsPath=join(outputDirectory,"limits.json");
  writeFileSync(submitted,encode(typed),{flag:"wx"});writeFileSync(limitsPath,encode(limits),{flag:"wx"});binding.typedPacketSha256=sha(readFileSync(submitted));
  stage="objective-typed-preview";const actual=child(tooling.leanPath,["-j","2","--run",tooling.previewHostPath,submitted,limitsPath],{LEAN_PATH:tooling.oleanRoot,LEAN_NUM_THREADS:"2"});
  const result=JSON.parse(actual.trim());if(result.schema!=="dregg.objective-bend.typed-preview.v2"||result.sameDecodedTerm!==true||result.typing!=="accepted by actual annotated checker")throw new Error("typed preview receiver shape differs");
  const output={schema:"dregg.objective-bend.preview-result.v2",status:result.status,binding,preview:result,authority:"none; source preview only"};
  writeFileSync(join(outputDirectory,"preview.json"),encode(output),{flag:"wx"});return output;
 }catch(error:any){const diagnostic={schema:"dregg.objective-bend.preview-result.v2",status:"refused",binding,diagnostic:error&&typeof error==="object"&&"stage" in error?error:{schema:"dregg.bend.compiler-diagnostic.v1",stage,message:String(error)},authority:"none; source preview only"};
  try{mkdirSync(outputDirectory,{recursive:true});if(!readdirSync(outputDirectory).includes("diagnostic.json"))writeFileSync(join(outputDirectory,"diagnostic.json"),encode(diagnostic),{flag:"wx"});}catch{}throw diagnostic;}
}
if(import.meta.main){const [requestPath,outputDirectory,toolingPath]=process.argv.slice(2);if(!requestPath||!outputDirectory||!toolingPath)throw new Error("usage: objective-preview PREVIEW_REQUEST OWNED_EMPTY_OUTPUT_DIR PINNED_TOOLING_CONFIG");
 try{console.log(JSON.stringify(preview(requestPath,outputDirectory,toolingPath)));}catch(error){console.error(JSON.stringify(error));process.exitCode=2;}}
