import {readFileSync} from "node:fs";
import {join} from "node:path";
import {parseObjective} from "../../native/bend-source/objective-parser.ts";
const names=["EvenOdd","TwiceReview","GenericExtension","Heterogeneous","WholeSuper","LazySpecification","LazyUnusedArgument","LazyUnusedField","LazySharedField"];
const asts=new Map<string,ReturnType<typeof parseObjective>>();
for(const name of names){const ast=parseObjective(readFileSync(join(import.meta.dirname,name+".obend"),"utf8"));if(!ast.declarations.length)throw new Error("empty AST "+name);asts.set(name,ast);console.log(name+": actual source parse");}
const unused=asts.get("LazyUnusedArgument")!.declarations.find(d=>d.kind==="function"&&d.signature.name==="result");
if(unused?.kind!=="function"||unused.body.kind!=="expression"||unused.body.expression.kind!=="call")throw new Error("lazy argument call lost");
const recursive=unused.body.expression.args[1];if(recursive?.kind!=="fix"||recursive.specification.kind!=="extension-value")throw new Error("captured extension replaced by metadata or forced away");
if(recursive.specification.body.kind!=="var"||recursive.specification.body.name!=="self")throw new Error("actual recursive body lost");
const heterogeneous=asts.get("Heterogeneous")!.declarations.find(d=>d.kind==="extension"&&d.name==="AddY");
if(heterogeneous?.kind!=="extension"||heterogeneous.parameters[0].type===heterogeneous.parameters[1].type||heterogeneous.targetType===heterogeneous.parameters[0].type)throw new Error("open V/C/W annotations collapsed");
console.log("OBJECTIVE SOURCE AST COHORT PASS: 9 source programs; nested captured extension and independent types retained");

const quoted=parseObjective(readFileSync(new URL("./QuotedFields.obend",import.meta.url),"utf8"));
const row=quoted.declarations.find((d:any)=>d.kind==="record") as any;
const selected=quoted.declarations.find((d:any)=>d.kind==="function") as any;
if(JSON.stringify(row.fields.map((f:any)=>f.name))!==JSON.stringify(["0","1"])||selected.body.expression.name!=="1")throw Error("quoted field identity differs");
console.log("QUOTED FIELDS PASS: canonical ordinal keys, escaped string names, actual member selection");
