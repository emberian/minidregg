// The one way a harness reaches the Objective Bend front end: the Lean program
// Host/ObjectiveBendFrontEndMain.lean (`lean --run`, against built oleans). There is no
// other parser or elaborator.
//
// env: LEAN       lean binary (default `lean`)
//      LEAN_PATH  module search path holding the built oleans (default: OLEAN_ROOT, then
//                 <repo>/.lake/build/lib/lean)
import {spawnSync} from "node:child_process";
import {readFileSync,existsSync} from "node:fs";
import {join,resolve} from "node:path";
export const repo=resolve(import.meta.dirname,"../..");
export const frontEnv=()=>({lean:process.env.LEAN??"lean",
 leanPath:process.env.LEAN_PATH??process.env.OLEAN_ROOT??join(repo,".lake/build/lib/lean")});
export function front(args:string[],env=frontEnv()){
 const r=spawnSync(env.lean,["--run",join(repo,"Host/ObjectiveBendFrontEndMain.lean"),...args],
  {encoding:"utf8",maxBuffer:1<<28,timeout:900000,env:{...process.env,LEAN_PATH:env.leanPath,LEAN_NUM_THREADS:"2"}});
 if(r.error)throw r.error;
 return {status:r.status??-1,stdout:r.stdout??"",stderr:r.stderr??""};
}
const lastLine=(text:string)=>text.trim().split("\n").at(-1)??"";
// capture: the capture record, or throws the diagnostic.
export function capture(specPath:string,dir:string,env=frontEnv()){
 const r=front(["capture",specPath,dir],env);
 if(r.status!==0)throw JSON.parse(lastLine(r.stderr)||'{"message":"capture failed"}');
 return JSON.parse(lastLine(r.stdout));
}
// preview: the preview result (finished/suspended/...) or the refusal record, as written.
export function preview(requestPath:string,dir:string,env=frontEnv()){
 const r=front(["preview",requestPath,dir],env);
 for(const name of ["preview.json","diagnostic.json"])if(existsSync(join(dir,name)))return JSON.parse(readFileSync(join(dir,name),"utf8"));
 return {status:"refused",diagnostic:{stage:"objective-front",message:(r.stderr||r.stdout).trim().slice(0,400)}};
}
// batch: run in-memory jobs in one process.
export function batch(jobsPath:string,outPath:string,env=frontEnv()){
 const r=front(["batch",jobsPath,outPath],env);
 if(r.status!==0)throw Error("front-end batch failed: "+r.stderr.slice(0,400));
 return JSON.parse(readFileSync(outPath,"utf8"));
}
