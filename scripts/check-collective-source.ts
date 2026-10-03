// Check sealed authored domain sources with the repository's qualified Bend tools.
// Usage: bun scripts/check-collective-source.ts TOOLING_DIR OUTPUT_DIR [SOURCE_DIR]
// TOOLING_DIR supplies bend.ts, safe.ts and sealed.ts. No network loader is used.
// This emits Books; run CheckCollective.lean separately for actual kernel checking.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {createHash} from "node:crypto";
import {resolve} from "node:path";
const [toolingArg,outArg,sourceArg]=process.argv.slice(2);
if (!toolingArg || !outArg) throw Error("tooling and output directories required");
const tooling=resolve(toolingArg), output=resolve(outArg);
const source=resolve(sourceArg ?? resolve(import.meta.dir,"../world/Workshop"));
const Bend=await import(tooling+"/bend.ts");
const Safe=await import(tooling+"/safe.ts");
const {elaborateSealed}=await import(tooling+"/sealed.ts");
mkdirSync(output,{recursive:true});
type Dep=[string,string,string];
const base:Dep=["","Base","Prelude"];
const math:Dep=["Math","./MarketMath.bend","MarketMath"];
const seller:Dep=["Seller","./SingleSellerAllocation.bend","SingleSellerAllocation"];
const dependencies:Record<string,Dep[]>={
 Prelude:[], CatalogReview:[base], MarketMath:[base],
 CollectiveAdoption:[base,["Review","./CatalogReview.bend","CatalogReview"],math],
 SingleSellerAllocation:[base,math], UniformProRata:[base,math],
 SingleSellerSettlement:[base,math,seller],
 SingleSellerTransfers:[base,math,seller,["Settlement","./SingleSellerSettlement.bend","SingleSellerSettlement"]],
 CanonicalBookSettlement:[base,math,seller],
 CanonicalUniformSettlement:[base,math,["Uniform","./UniformProRata.bend","UniformProRata"],
   ["Book","./CanonicalBookSettlement.bend","CanonicalBookSettlement"]],
 CollectiveDemonstration:[base,seller,["Book","./CanonicalBookSettlement.bend","CanonicalBookSettlement"]],
 SharedBookSettlement:[base,math,seller,["Book","./CanonicalBookSettlement.bend","CanonicalBookSettlement"]],
 SharedSettlementDemonstration:[base,seller,["Book","./CanonicalBookSettlement.bend","CanonicalBookSettlement"],["Shared","./SharedBookSettlement.bend","SharedBookSettlement"]],
 ResidentServiceCommons:[base,math,["Book","./CanonicalBookSettlement.bend","CanonicalBookSettlement"]],
 WorldSurface:[base],
 ServiceCommonsFaces:[base,["World","./WorldSurface.bend","WorldSurface"],["Service","./ResidentServiceCommons.bend","ResidentServiceCommons"]]
};
const entries:Record<string,string>={
 MarketMath:"divide",CollectiveAdoption:"prepare_install",SingleSellerAllocation:"allocate",
 UniformProRata:"allocate",SingleSellerSettlement:"settle",SingleSellerTransfers:"settle",
 CanonicalBookSettlement:"settle",CanonicalUniformSettlement:"settle",CollectiveDemonstration:"input",SharedBookSettlement:"settle",SharedSettlementDemonstration:"input",ResidentServiceCommons:"reserve",ServiceCommonsFaces:"domain_face"
};
const results=[];
for(const [name,entryDefinition] of Object.entries(entries)){
 const modules:any[]=[];
 const indices=new Map<string,number>();
 const visit=(name:string):number=>{
   const known=indices.get(name);if(known!==undefined)return known;
   const imports=dependencies[name].map(([alias,path,child])=>{
     const module=visit(child);return {alias,path,module,sha256:modules[module].sha256};
   });
   const bytes=readFileSync(resolve(source,name+".bend"));
   const sha256=createHash("sha256").update(bytes).digest("hex");
   const index=modules.length;modules.push({namespace:name==="Prelude"?"":name,bytes,sha256,imports});
   indices.set(name,index);return index;
 };
 try{
   const entryModule=visit(name);
   const result=elaborateSealed(Bend,Safe,{modules,entryModule,entryDefinition},output);
   results.push({module:name,entry:entryDefinition,...result.transcript,bookPath:result.bookPath,
     transcriptPath:result.transcriptPath});
   console.log("SOURCE CHECK + BENDTT EMISSION PASS "+name);
 }catch(error){
   console.error((error as {$?:string}).$==="Err" ? Bend.err_show(error) : String(error));
   process.exit(1);
 }
}
writeFileSync(resolve(output,"collective-source-results.json"),JSON.stringify(results,null,2)+"\n");

