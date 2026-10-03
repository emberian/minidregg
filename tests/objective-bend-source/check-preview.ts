// Actual source preview contract/refusers; producer remains generic.
import {readFileSync,mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
import {preview} from "../../native/bend-source/objective-preview.ts";
const [cohortPath,toolingPath,outputRoot]=process.argv.slice(2);
const cohort=JSON.parse(readFileSync(cohortPath,"utf8"));
const require=(ok:boolean,message:string)=>{if(!ok)throw Error(message);};
mkdirSync(outputRoot,{recursive:true});
for(const item of cohort){
 let out:any;try{out=preview(item.requestPath,join(outputRoot,item.name),toolingPath);}catch(error){out=error;}
 if(item.expectedStatus==="refused"){require(out.status==="refused","source typing refusal differs: "+item.name);continue;}
 require(out.status==="finished"&&out.preview.type.tag===(item.expectedType??"natural"),"actual typed source result type differs: "+item.name);
 require(item.expectedRecord?out.preview.result.tag==="record":out.preview.result.value===item.expected,"actual typed source result differs: "+item.name);
 require(out.preview.sameDecodedTerm===true&&out.preview.uses.length===0,"checked/executed join differs");
}
const original=JSON.parse(readFileSync(cohort[0].requestPath,"utf8"));
for(const [name,change,expect] of [
 ["WrongCapture",{captureSha256:"0".repeat(64)},"refused"],
 ["TypingBudget",{limits:{...original.limits,typeFuel:"1"}},"refused"],
 ["Ticks",{limits:{...original.limits,ticks:"1"}},"suspended"],
 ["Capacity",{limits:{...original.limits,heap:"1"}},"suspended"]
] as const){
 const request=join(outputRoot,name+"-request.json");writeFileSync(request,JSON.stringify({...original,...change})+"\n",{flag:"wx"});
 let result:any;try{result=preview(request,join(outputRoot,name),toolingPath);}catch(error){result=error;}
 require(result.status===expect,"preview refusal/exhaustion differs: "+name);
 require(expect!=="suspended"||result.preview.result===null,"exhaustion falsely returned a source result");
}
console.log(JSON.stringify({schema:"dregg.objective-bend.preview-cohort-check.v1",status:"passed",sourceResults:cohort.map((c:any)=>c.name),refusers:["capture identity","typing budget"],suspensions:["ticks","capacity"]}));
