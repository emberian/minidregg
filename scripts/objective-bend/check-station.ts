// Sealed source checking only. Native receiving is a separate obligation.
import { readFileSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { dirname, resolve, join } from "node:path";
import { fileURLToPath } from "node:url";
const repository = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
const runtime = process.env.BEND_SEALED_RUNTIME;
const evidence = process.env.STATION_EVIDENCE_ROOT;
if (!runtime || !evidence) throw new Error("BEND_SEALED_RUNTIME and STATION_EVIDENCE_ROOT are required");
const Bend = await import(join(runtime, "bend.ts"));
const Safe = await import(join(runtime, "safe.ts"));
const { elaborateSealed } = await import(join(runtime, "sealed.ts"));
const sourceRoot = resolve(process.env.STATION_SOURCE_ROOT ?? join(repository,"examples/objective-bend-station"));
const worldSource = resolve(process.env.WORLD_PLAN_SCALAR_SOURCE ?? join(repository,"examples/objective-bend-world/WorldPlanScalar.bend"));
const sha = (bytes: Uint8Array) => createHash("sha256").update(bytes).digest("hex");
const base = {name:"Base",namespace:"",path:`${sourceRoot}/Prelude.bend`,imports:[]};
const station = {name:"SharedConsequences",namespace:"SharedConsequences",path:`${sourceRoot}/SharedConsequences.bend`,imports:[['','Base','Base']]};
const world = {name:"WorldPlanScalar",namespace:"WorldPlanScalar",path:worldSource,imports:[['','Base','Base']]};
const author = {name:"EngineeringStation",namespace:"EngineeringStation",path:`${sourceRoot}/EngineeringStation.bend`,imports:[['','Base','Base'],['Station','./SharedConsequences.bend','SharedConsequences']]};
const bridge = {name:"NativePlans",namespace:"NativePlans",path:`${sourceRoot}/NativePlans.bend`,imports:[['','Base','Base'],['Station','./SharedConsequences.bend','SharedConsequences'],['World','./WorldPlanScalar.bend','WorldPlanScalar']]};
const example = {name:"Receiving",namespace:"Receiving",path:`${sourceRoot}/Receiving.bend`,imports:[['','Base','Base'],['Station','./SharedConsequences.bend','SharedConsequences']]};
const result: unknown[] = [];
for (const [file,entry,dependencies,imports] of [
 ['SharedConsequences','take',[base],station.imports],
 ['Receiving','take_key',[base,station],example.imports],
 ['EngineeringStation','move',[base,station],author.imports],
 ['NativePlans','result_plan',[base,station,world],bridge.imports],
 ['NativeMethods','take',[base,station,world,author,bridge],[['','Base','Base'],['Station','./SharedConsequences.bend','SharedConsequences'],['Author','./EngineeringStation.bend','EngineeringStation'],['Bridge','./NativePlans.bend','NativePlans'],['World','./WorldPlanScalar.bend','WorldPlanScalar']]],
 ['NativeReceiving','take_key_plan',[base,station,world,bridge,example],[['','Base','Base'],['Example','./Receiving.bend','Receiving'],['Bridge','./NativePlans.bend','NativePlans'],['World','./WorldPlanScalar.bend','WorldPlanScalar']]],
] as const) {
 const descriptors=[...dependencies,{name:file,namespace:file,path:`${sourceRoot}/${file}.bend`,imports}];
 const bytes=descriptors.map(d=>readFileSync(d.path));
 const modules=descriptors.map((d,i)=>({namespace:d.namespace,bytes:bytes[i],sha256:sha(bytes[i]),imports:d.imports.map(([alias,path,name])=>{
  const module=descriptors.findIndex(x=>x.name===name);
  if(module<0 || module>=i) throw new Error(`non-earlier import ${name} in ${d.name}`);
  return {alias,path,module,sha256:sha(bytes[module])};
 })}));
 try {
  const checked=elaborateSealed(Bend,Safe,{modules,entryModule:modules.length-1,entryDefinition:entry},evidence);
  result.push({file,entry,...checked.transcript,bookPath:checked.bookPath,transcriptPath:checked.transcriptPath});
  console.log(`SOURCE CHECK + BENDTT EMISSION PASS ${file}`);
 } catch(error) {
  console.error((error as {$?:string}).$==="Err" ? Bend.err_show(error) : String(error));
  process.exit(1);
 }
}
writeFileSync(join(evidence,"sealed-results.json"),JSON.stringify(result,null,2)+"\n");
