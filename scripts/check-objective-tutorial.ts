// Re-run every command block of docs/OBJECTIVE-BEND-TUTORIAL.md and compare.
//
// The tutorial says each printed result is the output of `bun docs/tutorial/run.ts`. This
// is the check: for each ```sh fence, every line `$ COMMAND` is run (sh -c, from the
// repository root) and its stdout must equal the lines that follow it up to the next
// `$ ` line or the closing fence. A final line `(exit status N)` is the expected exit
// status (default 0) and is not part of the output. The runner needs a built Lean tree:
// LEAN (default `lean`) and OLEAN_ROOT, as docs/tutorial/run.ts reads them.
//
// usage: bun scripts/check-objective-tutorial.ts [DOC.md]
// env:   TUTORIAL_LIST=1  print the parsed commands and exit (no Lean needed)
import {readFileSync} from "node:fs";
import {spawnSync} from "node:child_process";
import {resolve} from "node:path";

const repo=resolve(import.meta.dirname,"..");
const doc=resolve(process.argv[2]??resolve(repo,"docs/OBJECTIVE-BEND-TUTORIAL.md"));
type Case={line:number;command:string;expected:string;status:number};
const cases:Case[]=[];
const lines=readFileSync(doc,"utf8").split("\n");
for(let i=0;i<lines.length;i++){
 if(lines[i]!=="```sh")continue;
 let j=i+1;const block:string[]=[];
 while(j<lines.length&&lines[j]!=="```")block.push(lines[j++]);
 let k=0;
 while(k<block.length){
  if(!block[k].startsWith("$ ")){k++;continue;}
  const at=i+1+k+1;const command=block[k].slice(2);const out:string[]=[];k++;
  while(k<block.length&&!block[k].startsWith("$ "))out.push(block[k++]);
  while(out.length&&out[out.length-1]==="")out.pop(); // a blank line before the next `$ ` is not output
  let status=0;const last=out[out.length-1]?.match(/^\(exit status (\d+)\)$/);
  if(last){status=Number(last[1]);out.pop();}
  while(out.length&&out[out.length-1]==="")out.pop();
  cases.push({line:at,command,expected:out.join("\n"),status});
 }
 i=j;
}
if(!cases.length){console.error("no commands found in "+doc);process.exit(1);}
if(process.env.TUTORIAL_LIST){for(const c of cases)console.log(c.line+": "+c.command+"  -> exit "+c.status+", "+c.expected.split("\n").length+" lines");process.exit(0);}
let bad=0;
for(const c of cases){
 const r=spawnSync("sh",["-c",c.command],{cwd:repo,encoding:"utf8",maxBuffer:1<<24});
 const got=(r.stdout??"").replace(/\n+$/,"");
 if(r.status!==c.status||got!==c.expected){
  bad++;console.error("MISMATCH line "+c.line+": "+c.command+"\n  expected exit "+c.status+", got "+r.status+"\n  expected:\n"+c.expected.replace(/^/gm,"    ")+"\n  got:\n"+got.replace(/^/gm,"    ")+(r.stderr?"\n  stderr: "+r.stderr.slice(0,400):""));
 }
}
if(bad){console.error("TUTORIAL FAIL: "+bad+" of "+cases.length+" commands differ");process.exit(1);}
console.log("TUTORIAL PASS: "+cases.length+" commands reproduce the tutorial's printed output");
