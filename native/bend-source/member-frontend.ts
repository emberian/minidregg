// Actual member-package frontend. Reads only explicitly listed source files;
// pinned parser/emitter and exact Mini package producer remain separate stages.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {join,resolve} from "node:path";
import {createHash} from "node:crypto";
import {elaborateSealed,sourceImport} from "./member-sealed.ts";

const PIN="947db722640c86247849343657bf2f7ef01cb7f1";
const HASHES:Record<string,string>={
 "bend.ts":"7deae3693eb896f33c73867081b99d2c6f3ed3b57e77e55eb5f6260840dd0e63",
 "safe.ts":"54cb3a534ab7cc9ee313bf6383b3948ccdcac022469b3020e00745bbfe6f7e04",
 "base.bend":"c742fae9c49b14f0cc9128429a2c6109364c8a933a142f2c90b9f2e5fd976661"
};
const hash=(bytes:Uint8Array)=>createHash("sha256").update(bytes).digest("hex");
const natural=(value:unknown,name:string):number=>{
 if(typeof value!=="string"||!/^(0|[1-9][0-9]*)$/.test(value))throw new Error(name+": expected canonical decimal natural");
 const n=Number(value);if(!Number.isSafeInteger(n))throw new Error(name+": exceeds parser index bound");return n;
};
const sourceImports=(bytes:Uint8Array)=>{
 const lines=new TextDecoder("utf-8",{fatal:true}).decode(bytes).split("\n");
 const result:{path:string;alias:string}[]=[];
 for(const line of lines){
  const text=line.trim();if(!text||text.startsWith("#"))continue;
  if(!/^import(\s|$)/.test(text))break;
  result.push(sourceImport(text));
 }
 return result;
};

export async function capture(specPath:string,outputDirectory:string,toolingRoot:string){
 let renderError=(error:unknown)=>String(error);
 const binding:{requestSha256?:string,moduleSources:{index:number,name:string,sha256:string}[],emittedBookSha256?:string}={moduleSources:[]};
 try{
 for(const [name,expected] of Object.entries(HASHES)){
  if(hash(readFileSync(join(toolingRoot,name)))!==expected)throw new Error("changed pinned tooling: "+name);
 }
 const requestBytes=readFileSync(specPath);binding.requestSha256=hash(requestBytes);
 const spec=JSON.parse(new TextDecoder("utf-8",{fatal:true}).decode(requestBytes));
 if(spec.schema!=="dregg.bend.package-input.v1")throw new Error("unknown package input schema");
 if(!Array.isArray(spec.modules)||spec.modules.length<1||spec.modules.length>256)throw new Error("module capacity");
 const entryModule=natural(spec.entryModule,"entryModule");
 if(entryModule>=spec.modules.length)throw new Error("entry module absent");
 if(typeof spec.entryDefinition!=="string")throw new Error("entry definition absent");
 mkdirSync(outputDirectory,{recursive:true});
 const snapshots=join(outputDirectory,"source");mkdirSync(snapshots,{recursive:true});
 const modules:any[]=[];const prepared:any[]=[];let total=0;
 for(let index=0;index<spec.modules.length;index++){
  const m=spec.modules[index];if(typeof m.name!=="string"||typeof m.sourcePath!=="string"||!Array.isArray(m.imports))throw new Error("invalid module record");
  const bytes=readFileSync(m.sourcePath);binding.moduleSources.push({index,name:m.name,sha256:hash(bytes)});total+=bytes.length;if(total>4194304)throw new Error("source byte capacity");
  const parsed=sourceImports(bytes);
  if(parsed.length!==m.imports.length)throw new Error("source import manifest count differs");
  const imports=parsed.map((edge,j)=>{
   const declared=m.imports[j];const target=natural(declared.module,"import module");
   if(target>=index||declared.alias!==edge.alias)throw new Error("changed, missing, cyclic or aliased import");
   if(edge.path==="Base"&&spec.modules[target].name!=="Base")throw new Error("Base import names another module");
   return {...edge,module:target,sha256:modules[target].sha256};
  });
  const snapshot=join(snapshots,index+".bend");writeFileSync(snapshot,bytes,{flag:"wx"});
  modules.push({namespace:m.name==="Base"?"":m.name,bytes,sha256:hash(bytes),imports});
  prepared.push({name:m.name,sourcePath:resolve(snapshot),imports:m.imports});
 }
 const Bend=await import(join(toolingRoot,"bend.ts"));
 renderError=(error:unknown)=>error&&typeof error==="object"&&"$" in error&&error.$==="Err"?Bend.err_show(error):String(error);
 const Safe=await import(join(toolingRoot,"safe.ts"));
 const result=elaborateSealed(Bend,Safe,{modules,entryModule,entryDefinition:spec.entryDefinition},outputDirectory);
 binding.emittedBookSha256=hash(result.bookBytes);
 const corePath=join(outputDirectory,"book.bendtt");writeFileSync(corePath,result.bookBytes,{flag:"wx"});
 const namespace=modules[entryModule].namespace;
 const sourceEntry=namespace===""?spec.entryDefinition:namespace+":"+spec.entryDefinition;
 const coreEntry=Bend.name_key(sourceEntry).replace(/[^A-Za-z0-9_.]|^[.0-9]/g,(c:string)=>"_"+c.codePointAt(0)!.toString(16)+"_");
 const packageInput={schema:"dregg.bend.package-input.v1",modules:prepared,entryModule:spec.entryModule,entryDefinition:spec.entryDefinition};
 const packageInputPath=join(outputDirectory,"package-input.json");writeFileSync(packageInputPath,JSON.stringify(packageInput,null,2)+"\n",{flag:"wx"});
 const transcript={...result.transcript,...binding,schema:"dregg.bend.member-frontend.v1",upstream:PIN,coreEntry,corePath:resolve(corePath),packageInputPath:resolve(packageInputPath),
  sourcePackageStatus:"exact snapshots awaiting Mini canonical package producer",coreStatus:"actual upstream parser/safe_emit; awaiting Mini Book.check",
  surfaceCorrespondence:"recorded actual elaboration, no universal TypeScript compiler theorem"};
 writeFileSync(join(outputDirectory,"frontend.json"),JSON.stringify(transcript,null,2)+"\n",{flag:"wx"});
 return transcript;
 }catch(error){throw {schema:"dregg.bend.compiler-diagnostic.v1",stage:"member-frontend",message:renderError(error),binding};}
}

if(import.meta.main){
 const [specPath,outputDirectory,toolingRoot]=process.argv.slice(2);
 if(!specPath||!outputDirectory||!toolingRoot)throw new Error("usage: member-frontend PACKAGE_SPEC OUTPUT_DIR PINNED_TOOLING_ROOT");
 try{console.log(JSON.stringify(await capture(specPath,outputDirectory,toolingRoot)));}
 catch(error){mkdirSync(outputDirectory,{recursive:true});const diagnostic=error&&typeof error==="object"&&"stage" in error?error:{schema:"dregg.bend.compiler-diagnostic.v1",stage:"member-frontend",message:String(error)};
 writeFileSync(join(outputDirectory,"diagnostic.json"),JSON.stringify(diagnostic,null,2)+"\n");console.error(JSON.stringify(diagnostic));process.exitCode=2;}
}
