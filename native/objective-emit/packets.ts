// Produce the core/typed packets the differential harness runs, through the
// SAME producer path as the Studio preview: the real frontend capture
// (objective-frontend.ts) and the real elaborator CLI (objective-elaborate.ts),
// with the preview's argument wire. No term is authored here.
// usage: bun packets.ts OUTPUT_ROOT COHORT_JSON...
import {readFileSync,writeFileSync,mkdirSync,existsSync} from "node:fs";
import {join,resolve,dirname} from "node:path";
import {execFileSync} from "node:child_process";
import {captureObjective} from "../bend-source/objective-frontend.ts";
const [outRaw,...cohorts]=process.argv.slice(2);
if(!outRaw||!cohorts.length)throw Error("usage: bun packets.ts OUTPUT_ROOT COHORT_JSON...");
const outRoot=resolve(outRaw);if(existsSync(outRoot))throw Error("output root must be new");mkdirSync(outRoot,{recursive:true});
const elaborator=resolve(import.meta.dirname,"../bend-source/objective-elaborate.ts");
const limits={heap:"1000000",stack:"1000000",ticks:"1000000"};
const index:any[]=[];
for(const cohortPath of cohorts){
 const cohortDir=dirname(resolve(cohortPath));
 for(const item of JSON.parse(readFileSync(cohortPath,"utf8"))){
  const dir=join(outRoot,item.name);mkdirSync(dir);
  const packageInput={schema:"dregg.objective-bend.package-input.v1",edition:"objective-bend-1",
   modules:item.modules.map((m:any)=>({name:m.name,sourcePath:resolve(cohortDir,m.source),imports:m.imports??[]})),
   entryModule:String(item.modules.length-1),entryDefinition:item.entry};
  writeFileSync(join(dir,"package-input.json"),JSON.stringify(packageInput,null,2)+"\n");
  // An activity's responses, on the preview's wire, in delivery order.
  writeFileSync(join(dir,"responses.json"),JSON.stringify(item.responses??[],null,2)+"\n");
  let status="ok",message="";
  try{
   captureObjective(join(dir,"package-input.json"),join(dir,"capture"));
   const encoding=item.argumentEncoding??"legacy-values-v1";
   const wire=encoding==="typed-values-v1"?{schema:"dregg.objective-bend.argument-values.v1",values:item.arguments}:item.arguments;
   execFileSync(process.execPath,[elaborator,join(dir,"capture","objective.json"),join(dir,"source"),JSON.stringify(wire),JSON.stringify(item.projections??[]),JSON.stringify(limits)],{encoding:"utf8",stdio:["ignore","pipe","pipe"]});
  }catch(error:any){status="refused";message=String(error.stderr??error.message??error).trim().slice(0,400);}
  index.push({name:item.name,cohort:cohortPath,status,message,core:existsSync(join(dir,"source.core.json"))?join(dir,"source.core.json"):null,
   typed:existsSync(join(dir,"source.typed.json"))?join(dir,"source.typed.json"):null,
   responses:join(dir,"responses.json")});
 }
}
writeFileSync(join(outRoot,"index.json"),JSON.stringify(index,null,2)+"\n");
console.log(JSON.stringify(index.map(i=>[i.name,i.status])));
