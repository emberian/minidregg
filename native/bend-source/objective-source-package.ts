// Objective edition 1 capture -> canonical package input (schema
// dregg.objective-bend.source-package-input.v2) for the native Host's
// `objective-publication` operation, which builds the Mini package identity.
//
// The three tool pins are the SHA-256 of the exact tool sources in this
// directory: the parser and frontend that produced the capture (checked
// against the capture's own record), and the elaborator that lowers the
// selected declaration to the typed core the artifact publishes. The receiver
// compares each pin with the operator policy; it does not establish that the
// tools are correct (trusted frontend boundary).
import {readFileSync,writeFileSync} from "node:fs";
import {join} from "node:path";
import {createHash} from "node:crypto";
import {parseObjective} from "./objective-parser.ts";

const sha=(b:Uint8Array)=>createHash("sha256").update(b).digest("hex");
const hex=(b:Uint8Array)=>Buffer.from(b).toString("hex");
const here=(name:string)=>readFileSync(join(import.meta.dirname,name));

export function toolPins(){
 return {parserSha256:sha(here("objective-parser.ts")),frontendSha256:sha(here("objective-frontend.ts")),
  elaboratorSha256:sha(here("objective-elaborate.ts"))};
}

export function packageInput(capturePath:string){
 const raw=readFileSync(capturePath);if(raw.length>4194304)throw Error("capture byte capacity");
 const c=JSON.parse(new TextDecoder("utf-8",{fatal:true}).decode(raw));
 const pins=toolPins();
 if(c.schema!=="dregg.objective-bend.captured-package.v1"||c.edition!=="objective-bend-1")throw Error("Objective capture schema/edition");
 if(c.parserSourceSha256!==pins.parserSha256||c.producerSourceSha256!==pins.frontendSha256)
  throw Error("capture was produced by another parser/frontend than this directory's");
 if(!Array.isArray(c.modules)||c.modules.length<1||c.modules.length>64)throw Error("module capacity");
 let sourceTotal=0,astTotal=0;
 const modules=c.modules.map((m:any,index:number)=>{
  const source=readFileSync(m.sourcePath),astBytes=readFileSync(m.astPath);
  sourceTotal+=source.length;astTotal+=astBytes.length;
  if(sourceTotal>4194304||astTotal>8388608)throw Error("source/AST byte capacity");
  if(sha(source)!==m.sha256||sha(astBytes)!==m.astSha256)throw Error("captured source/AST identity: "+m.name);
  const ast=JSON.parse(astBytes.toString("utf8"));
  if(JSON.stringify(parseObjective(new TextDecoder("utf-8",{fatal:true}).decode(source)))!==JSON.stringify(ast))
   throw Error("source parser replay mismatch: "+m.name);
  const imports=m.imports.map((e:any)=>{
   if(!/^(0|[1-9][0-9]*)$/.test(e.module)||Number(e.module)>=index)throw Error("sealed import index");
   const target=c.modules[Number(e.module)];
   if(target.name!==e.moduleName||target.sha256!==e.sha256)throw Error("sealed imported module identity");
   return {alias:e.alias,path:e.path,target:e.module};
  });
  return {name:m.name,sourceHex:hex(source),astHex:hex(astBytes),imports};
 });
 if(typeof c.entryModule!=="string"||!/^(0|[1-9][0-9]*)$/.test(c.entryModule)||Number(c.entryModule)>=modules.length)
  throw Error("selected module");
 return {schema:"dregg.objective-bend.source-package-input.v2",edition:c.edition,...pins,modules,
  entryModule:c.entryModule,entryDefinition:c.entryDefinition};
}

if(import.meta.main){
 const [capturePath,output]=process.argv.slice(2);
 try{
  if(capturePath==="--pins"){console.log(JSON.stringify(toolPins()));process.exit(0);}
  if(!capturePath||!output)throw Error("usage: objective-source-package CAPTURE_JSON NEW_PACKAGE_INPUT_JSON | --pins");
  const data=packageInput(capturePath);
  writeFileSync(output,JSON.stringify(data)+"\n",{flag:"wx"});
  console.log(JSON.stringify({schema:data.schema,parserSha256:data.parserSha256,frontendSha256:data.frontendSha256,
   elaboratorSha256:data.elaboratorSha256,sourceEntry:data.modules[Number(data.entryModule)].name+"."+data.entryDefinition}));
 }catch(e){console.error(JSON.stringify({stage:"objective-source-package",message:String(e)}));process.exitCode=2;}
}
