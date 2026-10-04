// Objective Bend edition 1 package capture. Source/AST producer only: the
// independent Objective elaborator owns resolution, effects and operational meaning.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {join,resolve} from "node:path";
import {createHash} from "node:crypto";
import {parseObjective} from "./objective-parser.ts";

const digest=(bytes:Uint8Array)=>createHash("sha256").update(bytes).digest("hex");
const index=(value:unknown,label:string)=>{
 if(typeof value!=="string"||!/^(0|[1-9][0-9]*)$/.test(value))throw new Error(label+": canonical decimal index required");
 const n=Number(value);if(!Number.isSafeInteger(n))throw new Error(label+": index capacity");return n;
};
const named=(value:unknown,label:string):string=>{
 if(typeof value!=="string"||! /^[A-Za-z_]\w*$/.test(value))throw new Error(label+": identifier required");return value;
};
const distinct=(names:string[],label:string)=>{if(new Set(names).size!==names.length)throw new Error("duplicate "+label);};
const declarationName=(d:any)=>d.kind==="function"?d.signature.name:d.name;

export function captureObjective(specPath:string,outputDirectory:string,options:{adoptCapturedEdition?:boolean}={}){
 const requestBytes=readFileSync(specPath);const request=JSON.parse(new TextDecoder("utf-8",{fatal:true}).decode(requestBytes));
 const adopted=options.adoptCapturedEdition===true&&request.schema==="dregg.bend.package-input.v1";
 if(!adopted&&(request.schema!=="dregg.objective-bend.package-input.v1"||request.edition!=="objective-bend-1"))throw new Error("Objective package schema/edition required");
 if(!Array.isArray(request.modules)||request.modules.length<1||request.modules.length>256)throw new Error("module capacity");
 distinct(request.modules.map((m:any)=>named(m.name,"module name")),"module name");
 const entryModule=index(request.entryModule,"entry module"),entryDefinition=named(request.entryDefinition,"entry definition");
 if(entryModule>=request.modules.length)throw new Error("entry module absent");
 // All source and imports are validated before writing a success transcript.
 // Every byte is read once; no import follows a source path outside this manifest.
 const modules:any[]=[];let total=0;
 for(let i=0;i<request.modules.length;i++){
  const m=request.modules[i];if(typeof m.sourcePath!=="string"||!Array.isArray(m.imports))throw new Error("invalid module record");
  const bytes=readFileSync(m.sourcePath);total+=bytes.length;if(total>4194304)throw new Error("source byte capacity");
  const sha256=digest(bytes);if(m.sha256!==undefined&&m.sha256!==sha256)throw new Error("changed module bytes: "+m.name);
  let ast:ReturnType<typeof parseObjective>;
  try{ast=parseObjective(new TextDecoder("utf-8",{fatal:true}).decode(bytes));}
  catch(error){throw error&&typeof error==="object"&&"stage" in error?{...error,module:m.name}:{schema:"dregg.bend.compiler-diagnostic.v1",stage:"objective-source-parse",module:m.name,message:String(error)};}
  distinct(ast.declarations.map(declarationName),"declaration in "+m.name);
  if(ast.imports.length!==m.imports.length)throw new Error("import count differs: "+m.name);
  distinct(ast.imports.map(edge=>edge.alias),"import alias in "+m.name);
  const imports=ast.imports.map((edge,j)=>{
   const lock=m.imports[j],target=index(lock.module,"import module");
   if(target>=i)throw new Error("imports must reference an earlier sealed module");
   if(lock.alias!==edge.alias||(!adopted||lock.path!==undefined)&&lock.path!==edge.path)throw new Error("source import path/alias differs: "+m.name);
   if(!/^\.\/[A-Za-z_]\w*\.obend$/.test(edge.path))throw new Error("Objective edition 1 imports require sealed ./NAME.obend paths (Gen-1 ./NAME.bend is retired)");
   if(edge.path!=="./"+modules[target].name+".obend")throw new Error("source import target differs: "+m.name);
   if(lock.sha256!==undefined&&lock.sha256!==modules[target].sha256)throw new Error("changed imported bytes: "+m.name);
   return {...edge,module:String(target),moduleName:modules[target].name,sha256:modules[target].sha256};
  });
  modules.push({name:m.name,sha256,bytes,ast,imports});
 }
 if(!modules[entryModule].ast.declarations.some((d:any)=>declarationName(d)===entryDefinition))throw new Error("entry declaration absent");
 mkdirSync(outputDirectory,{recursive:true});const sourceRoot=join(outputDirectory,"source"),astRoot=join(outputDirectory,"ast");
 mkdirSync(sourceRoot,{recursive:true});mkdirSync(astRoot,{recursive:true});
 const records=modules.map((m,i)=>{
  const sourcePath=resolve(join(sourceRoot,i+".obend")),astPath=resolve(join(astRoot,i+".json"));
  writeFileSync(sourcePath,m.bytes,{flag:"wx"});
  const astBytes=new TextEncoder().encode(JSON.stringify(m.ast,null,2)+"\n");writeFileSync(astPath,astBytes,{flag:"wx"});
  return {name:m.name,sourcePath,sha256:m.sha256,astPath,astSha256:digest(astBytes),imports:m.imports};
 });
 // Canonical Mini Package computes its own cSHAKE identities from these exact
 // snapshots. SHA hashes below are byte fingerprints, never Package identities.
 const packageInput={schema:"dregg.bend.package-input.v1",modules:records.map(m=>({name:m.name,sourcePath:m.sourcePath,imports:m.imports.map(e=>({alias:e.alias,module:e.module}))})),entryModule:String(entryModule),entryDefinition};
 const packageInputPath=resolve(join(outputDirectory,"package-input.json"));
 writeFileSync(packageInputPath,JSON.stringify(packageInput,null,2)+"\n",{flag:"wx"});
 const result={parserSourceSha256:digest(readFileSync(join(import.meta.dirname,"objective-parser.ts"))),producerSourceSha256:digest(readFileSync(import.meta.path)),schema:"dregg.objective-bend.captured-package.v1",edition:"objective-bend-1",parserSchema:"dregg.objective-bend.module.v1",requestSha256:digest(requestBytes),requestSchema:request.schema,editionSelection:adopted?"explicit-caller-adoption":"declared-request",modules:records,entryModule:String(entryModule),entryDefinition,
  sourceEntry:records[entryModule].name+"."+entryDefinition,packageInputPath,
  sourceStatus:"exact locked source and parsed AST",semanticStatus:"requires Objective elaboration and execution receipt",theoremScope:"no typing or totality theorem asserted"};
 writeFileSync(join(outputDirectory,"objective.json"),JSON.stringify(result,null,2)+"\n",{flag:"wx"});return result;
}
if(import.meta.main){
 const [specPath,outputDirectory,editionOption]=process.argv.slice(2);
 if(!specPath||!outputDirectory)throw new Error("usage: objective-frontend PACKAGE_SPEC OWNED_OUTPUT_DIRECTORY");
 try{console.log(JSON.stringify(captureObjective(specPath,outputDirectory,{adoptCapturedEdition:editionOption==="--objective-edition-1"})));}
 catch(error){const diagnostic=error&&typeof error==="object"&&"stage" in error?error:{schema:"dregg.bend.compiler-diagnostic.v1",stage:"objective-package-capture",message:String(error)};
 mkdirSync(outputDirectory,{recursive:true});writeFileSync(join(outputDirectory,"diagnostic.json"),JSON.stringify(diagnostic,null,2)+"\n");console.error(JSON.stringify(diagnostic));process.exitCode=2;}
}
