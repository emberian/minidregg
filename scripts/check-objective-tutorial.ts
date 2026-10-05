// Re-run every command block of an Objective Bend document and compare.
//
// The document says each printed result is the output of `bun docs/tutorial/run.ts`. This
// is the check: for each ```sh fence, every line `$ COMMAND` is run (sh -c, from the
// repository root) and its stdout must equal the lines that follow it up to the next
// `$ ` line or the closing fence. A final line `(exit status N)` is the expected exit
// status (default 0) and is not part of the output. A fence opened as ```obend PATH is a
// source listing: its lines must equal the file PATH (repository-relative) byte for byte,
// so a listing cannot drift from the program the commands run. A fence may be indented
// (inside a list item); its indent is removed from every line of the block. The runner
// needs a built Lean tree: LEAN (default `lean`) and OLEAN_ROOT or LEAN_PATH, as
// docs/tutorial/run.ts reads them.
//
// usage: bun scripts/check-objective-tutorial.ts [DOC.md]   (default: the tutorial)
// env:   TUTORIAL_LIST=1  print the parsed commands and listings and exit (no Lean needed)
import {readFileSync,existsSync} from "node:fs";
import {spawnSync} from "node:child_process";
import {resolve} from "node:path";

const repo=resolve(import.meta.dirname,"..");
const doc=resolve(process.argv[2]??resolve(repo,"docs/OBJECTIVE-BEND-TUTORIAL.md"));
type Case={line:number;command:string;expected:string;status:number};
type Listing={line:number;path:string;text:string};
const cases:Case[]=[];const listings:Listing[]=[];
const lines=readFileSync(doc,"utf8").split("\n");
for(let i=0;i<lines.length;i++){
 const open=lines[i].match(/^( *)```(sh|obend (\S+))$/);
 if(!open)continue;
 const indent=open[1];
 let j=i+1;const block:string[]=[];
 while(j<lines.length&&lines[j]!==indent+"```"){
  const l=lines[j++];
  if(l!==""&&!l.startsWith(indent)){console.error(doc+":"+j+": a line of the block at line "+(i+1)+" is not indented by its fence's "+indent.length+" spaces");process.exit(1);}
  block.push(l.slice(indent.length));
 }
 if(j>=lines.length){console.error(doc+":"+(i+1)+": unclosed fence");process.exit(1);}
 if(open[3]!==undefined){listings.push({line:i+1,path:open[3],text:block.join("\n")});i=j;continue;}
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
if(process.env.TUTORIAL_LIST){
 for(const l of listings)console.log(l.line+": listing "+l.path);
 for(const c of cases)console.log(c.line+": "+c.command+"  -> exit "+c.status+", "+c.expected.split("\n").length+" lines");
 process.exit(0);}
let bad=0;
for(const l of listings){
 const file=resolve(repo,l.path);
 const actual=existsSync(file)?readFileSync(file,"utf8").replace(/\n$/,""):undefined;
 if(actual!==l.text){bad++;console.error("LISTING MISMATCH line "+l.line+": "+l.path+(actual===undefined?" does not exist":" differs from the block"));}
}
for(const c of cases){
 const r=spawnSync("sh",["-c",c.command],{cwd:repo,encoding:"utf8",maxBuffer:1<<24});
 const got=(r.stdout??"").replace(/\n+$/,"");
 if(r.status!==c.status||got!==c.expected){
  bad++;console.error("MISMATCH line "+c.line+": "+c.command+"\n  expected exit "+c.status+", got "+r.status+"\n  expected:\n"+c.expected.replace(/^/gm,"    ")+"\n  got:\n"+got.replace(/^/gm,"    ")+(r.stderr?"\n  stderr: "+r.stderr.slice(0,400):""));
 }
}
if(bad){console.error("TUTORIAL FAIL: "+bad+" of "+(cases.length+listings.length)+" commands and listings differ");process.exit(1);}
console.log("TUTORIAL PASS: "+cases.length+" commands reproduce the document's printed output; "+listings.length+" listings equal their files");
