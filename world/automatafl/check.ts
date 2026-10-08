// bun world/automatafl/check.ts prepare NEW_DIR [AUTOMATAFL_ROOT]
// bun world/automatafl/check.ts compare DIR
// Between them run Run.lean on jobs.json -> bend.jsonl (see README).
import {readFileSync,writeFileSync,mkdirSync,existsSync,copyFileSync} from "node:fs";
import {resolve,join} from "node:path";
import {spawnSync} from "node:child_process";
import {createHash} from "node:crypto";
const [mode,dir0,auto0]=process.argv.slice(2);
if(!dir0||!["prepare","compare"].includes(mode))throw Error("usage: check.ts prepare NEW_DIR [AUTOMATAFL_ROOT] | compare DIR");
const dir=resolve(dir0),here=import.meta.dirname;
if(readFileSync(join(here,"../../docs/objective-bend/EMERGENT-SMALLTALK.txt")).length>=3000)throw Error("language/object capsule exceeds its <3000-byte budget");
const read=(p:string)=>JSON.parse(readFileSync(p,"utf8"));
const write=(p:string,v:any)=>writeFileSync(p,JSON.stringify(v,null,2)+"\n");
const pack=(xs:number[],base=4)=>xs.reduceRight((a,n)=>a*BigInt(base)+BigInt(n),0n).toString();
const unpack=(n:string,size:number,base=4)=>{let x=BigInt(n);const xs=Array.from({length:size},()=>{const v=Number(x%BigInt(base));x/=BigInt(base);return v;});if(x!==0n)throw Error("result has digits outside the board");return xs;};
const sha=(p:string)=>createHash("sha256").update(readFileSync(p)).digest("hex");
const run=(cmd:string,args:string[],opts:any={})=>{const r=spawnSync(cmd,args,{encoding:"utf8",maxBuffer:1<<27,...opts});if(r.status!==0)throw Error(`${cmd}: ${r.error??r.stderr??r.stdout}`);return r.stdout;};
if(mode==="prepare"){
 if(existsSync(dir))throw Error("output directory must be new");mkdirSync(dir,{recursive:true});
 const auto=resolve(auto0??join(here,"../../../automatafl"));
 const cases:any[]=[];
 function add(id:string,pieces:[number,number][],moves:number[][]=[],a=12,marks:number[]=[],w=5,h=5){
  const cells=Array(w*h).fill(0);for(const [at,p]of pieces)cells[at]=p;cells[a]=3;
  cases.push({id,w,h,a,cells,marks,moves,kind:moves.length?"round":"automaton"});
 }
 add("empty",[]);add("attractor",[[14,1]]);add("repulsor",[[14,2]]);
 add("column-tie",[[14,1],[22,1]]);add("blocked-attractor",[[13,1]]);
 add("opposing-pair",[[10,2],[14,1],[22,1]]);
 add("pair-repulsor-tiebreak",[[10,2],[14,1],[22,1],[7,2]]);
 add("repulsion-before-attraction",[[14,2],[22,1]]);
 add("balanced-repulsors",[[10,2],[14,2]]);
 add("edge-cannot-flee",[[2,2]],[],0+10);
 add("independent",[[0,1],[4,2]],[[0,5],[4,9]]);
 add("identical",[[0,1]],[[0,5],[0,5]]);
 add("fork",[[0,1]],[[0,5],[0,1]]);
 add("vacuum-fork",[],[[0,5],[0,1]]);
 add("collision",[[0,1],[4,2]],[[0,2],[4,2]]);
 add("vacuum-convergence",[[0,1]],[[0,2],[4,2]]);
 add("vacuum-chain",[[0,1]],[[0,5],[5,10]]);
 add("occupied-chain",[[0,1],[5,2]],[[0,5],[5,10]]);
 add("two-cycle-one-piece",[[0,1]],[[0,5],[5,0]]);
 add("two-cycle-two-pieces",[[0,1],[5,2]],[[0,5],[5,0]]);
 add("two-cycle-empty",[],[[0,5],[5,0]]);
 add("stationary-path-blocker",[[0,1],[1,2]],[[0,4],[20,21]]);
 add("stationary-destination",[[0,1],[5,2]],[[0,5],[20,21]]);
 add("failed-source-still-blocks",[[0,1],[2,2],[7,1]],[[0,4],[2,22]]);
 add("moving-source-unblocks",[[0,1],[2,2]],[[0,4],[2,7]]);
 add("conflict-mark-refused",[[0,1]],[[0,5],[20,21]],12,[0]);
 add("diagonal-refused",[[0,1]],[[0,6],[20,21]]);
 add("automaton-refused",[],[[12,17],[20,21]]);
 add("zero-move-refused",[],[[0,0],[20,21]]);
 add("win-top",[[3,2]],[[20,21],[24,23]],1);
 add("win-bottom",[[21,2]],[[0,1],[4,3]],23);
 // Exhaust all nearest-particle types at distances 1/2 on each axis (3^4 * 2).
 for(let code=0;code<81;code++)for(const distance of [1,2]){
  let k=code;const pieces:[number,number][]=[];
  for(const delta of [1,-1,5,-5]){const p=k%3;k=Math.floor(k/3);if(p)pieces.push([12+delta*distance,p]);}
  add(`rays-${code}-${distance}`,pieces);
 }
 // Reproducible unrelated board/move samples; each also checked with player order swapped.
 let seed=0xA170FA1;const rng=(n:number)=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n;};
 for(let i=0;i<80;i++){
  const pieces:[number,number][]=[];for(let at=0;at<25;at++)if(at!==12&&rng(5)===0)pieces.push([at,1+rng(2)]);
  const legal:number[][]=[];for(let s=0;s<25;s++)for(let t=0;t<25;t++)if(s!==t&&s!==12&&t!==12&&(s%5===t%5||Math.floor(s/5)===Math.floor(t/5)))legal.push([s,t]);
  const moves=[legal[rng(legal.length)],legal[rng(legal.length)]];
  add(`random-${i}`,pieces,moves);add(`random-${i}-swapped`,pieces,[moves[1],moves[0]]);
 }
 write(join(dir,"cases.json"),cases);
 write(join(dir,"jobs.json"),cases.map(c=>({id:c.id,entry:c.kind==="automaton"?"automaton":"play",arguments:
  [String(c.w),String(c.h),pack(c.cells),String(c.a),...(c.kind==="automaton"?[]:[pack(c.cells.map((_:any,i:number)=>c.marks.includes(i)?1:0),2),...c.moves.flat().map(String)])]})));
 const crate=join(dir,"oracle");mkdirSync(join(crate,"src"),{recursive:true});copyFileSync(join(here,"oracle.rs"),join(crate,"src/main.rs"));
 writeFileSync(join(crate,"Cargo.toml"),`[package]\nname="automatafl-crosscheck"\nversion="0.0.0"\nedition="2024"\n[workspace]\n[dependencies]\nautomatafl-logic={path=${JSON.stringify(join(auto,"logic"))}}\nserde_json="1"\nndarray="0.16"\n`);
 // Keep all target/package state in this run; never build into either shared tree.
 run("cargo",["build","--quiet","--manifest-path",join(crate,"Cargo.toml"),"-j","2"],{env:{...process.env,CARGO_TARGET_DIR:join(dir,"target")}});
 const output=run(join(dir,"target/debug/automatafl-crosscheck"),[],{input:cases.map(c=>JSON.stringify(c)).join("\n")+"\n"});writeFileSync(join(dir,"rust.jsonl"),output);
 const files=["logic/src/lib.rs","logic/src/game.rs","logic/src/board.rs","logic/src/automaton.rs","logic/src/types.rs","logic/README.md"];
 write(join(dir,"sources.json"),{automataflHead:run("git",["-C",auto,"rev-parse","HEAD"]).trim(),automatafl:Object.fromEntries(files.map(p=>[p,sha(join(auto,p))])),bend:sha(join(here,"Automatafl.obend")),driver:sha(join(here,"Run.lean")),oracle:sha(join(here,"oracle.rs"))});
 console.log(JSON.stringify({prepared:cases.length,dir}));
}else{
 const cases=read(join(dir,"cases.json"));
 const lines=(name:string)=>new Map(readFileSync(join(dir,name),"utf8").trim().split("\n").map(l=>{const r=JSON.parse(l);return[r.id,r];}));
 const rust=lines("rust.jsonl"),bend=lines("bend.jsonl");
 const scalar=(d:any):any=>d.tag==="record"?Object.fromEntries(d.fields.map((f:any)=>[f.name,scalar(f.value)])):d.value;
 const diffs:any[]=[],failures:any[]=[],outputs=new Map();let agrees=0;
 for(const c of cases){
  const br:any=bend.get(c.id),rr:any=rust.get(c.id);
  if(br?.error||br?.result?.status!=="finished"||br?.result?.resultDataStatus!=="materialized"||!br?.result?.sameDecodedTerm||!rr||rr.result?.panic){failures.push({id:c.id,bend:br,rust:rr});continue;}
  const data=scalar(br.result.resultData);let b:any,r:any=rr.result;
  if(c.kind==="automaton")b={a:Number(data)};
  else if(Number(data.status)===2)b={rejected:true};
  else b={cells:unpack(data.board,c.w*c.h),a:Number(data.automaton),marks:unpack(data.marks,c.w*c.h,2).flatMap((v,i)=>v?[i]:[]),status:Number(data.status),winner:Number(data.winner)};
  outputs.set(c.id,b);
  r=r.rejected?{rejected:true}:c.kind==="automaton"?{a:r.a}:{cells:r.cells,a:r.a,marks:r.marks,status:r.status,winner:r.winner};
  if(JSON.stringify(b)===JSON.stringify(r))agrees++;else diffs.push({id:c.id,input:c,bend:b,rust:rr.result});
  if(c.kind==="round"&&!b.rejected){
   const count=(xs:number[],p:number)=>xs.filter(n=>n===p).length;
   if([1,2,3].some(p=>count(b.cells,p)!==count(c.cells,p)))failures.push({id:c.id,invariant:"particle conservation"});
   if(b.cells[b.a]!==3)failures.push({id:c.id,invariant:"automaton location"});
   if(b.status===1&&JSON.stringify(b.cells)!==JSON.stringify(c.cells))failures.push({id:c.id,invariant:"conflict preserves board"});
  }
 }
 for(let i=0;i<80;i++)if(JSON.stringify(outputs.get(`random-${i}`))!==JSON.stringify(outputs.get(`random-${i}-swapped`)))failures.push({id:`random-${i}`,invariant:"player-order independence"});
 const report={status:failures.length?"failed":diffs.length?"discrepancies":"agreement",cases:cases.length,agrees,discrepancies:diffs.length,failures,differences:diffs};
 write(join(dir,"report.json"),report);console.log(JSON.stringify({...report,differences:diffs.map(d=>d.id)}));
 if(failures.length)process.exit(1);
}
