// Objective Bend edition 1 source AST. This parser preserves the new language,
// including open recursion and fixpoints, as written.
export type Span={start:number,end:number,line:number};
export type Expr={span:Span}&(
 {kind:"var",name:string}|{kind:"nat",value:string}|{kind:"bool",value:boolean}|
 {kind:"string",value:string}|{kind:"unit"}|{kind:"record",fields:{name:string,value:Expr}[]}|{kind:"extend",inherited:Expr,fields:{name:string,value:Expr}[]}|{kind:"member",target:Expr,name:string}|
 {kind:"call",callee:Expr,args:Expr[]}|{kind:"compose",specifications:Expr[]}|
 {kind:"fix",specification:Expr,inherited:Expr}|{kind:"extension-value",parameters:Parameter[],targetType:string,body:Expr}|{kind:"lambda",parameters:Parameter[],resultType:string,body:Expr}|
 {kind:"binary",op:string,left:Expr,right:Expr}|{kind:"if",condition:Expr,whenTrue:Expr,whenFalse:Expr}|
 {kind:"let",name:string,type:string,value:Expr,body:Expr});
// Quantities: `+x` copy (unrestricted), `-x` dead (erased), `affine x`, `linear x`;
// an unmarked parameter is the default (unrestricted, shareable) quantity.
export type Quantity="default"|"copy"|"dead"|"affine"|"linear";
export type Parameter={name:string,type:string,quantity:Quantity};
// Method qualifiers (ltuo 9.2.3): primary `def`, `around`, the pure simple
// combinations `combine + | * | and`, and `before`/`after` (parsed so the
// elaborator can refuse them with a reason: they need an effect constructor).
export type Qualifier="primary"|"around"|"before"|"after"|"+"|"*"|"and";
export type Signature={name:string,parameters:Parameter[],resultType:string,span:Span};
export type Body={kind:"expression",expression:Expr,span:Span}|
 {kind:"match",scrutinee:Expr,branches:{pattern:{kind:"zero"|"succ"|"wildcard"|"bool"|"constructor",binder?:string,value?:boolean,label?:string},body:Body,span:Span}[],span:Span}|
 {kind:"let",name:string,type:string,value:Expr,body:Body,span:Span};
export type Declaration=
 {kind:"spec",name:string,suffix:boolean,parents:string[],targetType:string,requirements:Signature[],methods:(Signature&{qualifier:Qualifier,body:Body})[],laws:{name:string,parameters:Parameter[],body:Expr,span:Span}[],span:Span}|
 {kind:"extension",name:string,parameters:Parameter[],targetType:string,body:Body,span:Span}|
 {kind:"function",signature:Signature,body:Body,span:Span}|
 {kind:"record",name:string,methods:Signature[],fields:{name:string,type:string,span:Span}[],span:Span}|
 {kind:"sum",name:string,cases:{label:string,type:string,span:Span}[],span:Span};
type Line={text:string,indent:number,number:number,start:number,end:number};
const byteLength=(s:string)=>new TextEncoder().encode(s).length;
const span=(line:Line):Span=>({start:line.start,end:line.end,line:line.number});
const fail=(line:Line,message:string):never=>{throw {schema:"dregg.bend.compiler-diagnostic.v1",stage:"objective-source-parse",message,span:span(line)};};
const splitParameters=(raw:string):Parameter[]=>{
 if(!raw.trim())return [];
 const pieces:string[]=[];let start=0,depth=0;
 for(let i=0;i<raw.length;i++){if("(<[".includes(raw[i]))depth++;if(")>]".includes(raw[i]))depth--;if(raw[i]===","&&depth===0){pieces.push(raw.slice(start,i));start=i+1;}}
 pieces.push(raw.slice(start));
 return pieces.map(piece=>{
  const m=/^\s*(?:(affine|linear)\s+)?([+-]?)([A-Za-z_]\w*)\s*(?::\s*(.+?))?\s*$/.exec(piece);
  if(!m)throw new Error("invalid parameter");
  if(m[1]&&m[2])throw new Error("parameter "+m[3]+" has two quantity markers");
  if(m[1]&&(m[3]==="affine"||m[3]==="linear"))throw new Error("quantity keyword is not a parameter name");
  const quantity:Quantity=m[1]?m[1] as Quantity:m[2]==="+"?"copy":m[2]==="-"?"dead":"default";
  return {name:m[3],type:m[4]??"_",quantity};});
};
const signature=(raw:string,line:Line):Signature=>{
 const m=/^([A-Za-z_]\w*)\s*\((.*)\)(?:\s*->\s*(.+?))?\s*$/.exec(raw);
 if(!m)fail(line,"expected method signature");
 try{return {name:m[1],parameters:splitParameters(m[2]),resultType:m[3]??"_",span:span(line)};}catch(e){fail(line,String(e));}
};
const fieldName=(text:string):string=>{
 if(/^[A-Za-z_]\w*$/.test(text))return text;
 if(text.startsWith('"')){const value=JSON.parse(text);if(typeof value==="string")return value;}
 throw new Error("expected identifier or quoted string field name");
};

export function expression(text:string,sourceSpan:Span):Expr{
 const tokens:{text:string,start:number,end:number}[]=[];let at=0;
 while(at<text.length){
  if(/\s/.test(text[at])){at++;continue;}
  const rest=text.slice(at);const token=/^(?:[A-Za-z_]\w*|[0-9]+n?|"(?:[^"\\]|\\.)*"|->|==|!=|<=|>=|&&|\|\||[{}:=().,+*/<>-])/.exec(rest);
  if(!token)throw new Error("unsupported expression at column "+at);
  tokens.push({text:token[0],start:at,end:at+token[0].length});at+=token[0].length;
 }
 let cursor=0;
 const precedence:Record<string,number>={"||":1,"&&":2,"==":3,"!=":3,"<":4,">":4,"<=":4,">=":4,"+":5,"-":5,"*":6,"/":6};
 const location=(start:number,end:number):Span=>({start:sourceSpan.start+byteLength(text.slice(0,start)),end:sourceSpan.start+byteLength(text.slice(0,end)),line:sourceSpan.line});
 const take=(wanted?:string)=>{const t=tokens[cursor++];if(!t||wanted&&t.text!==wanted)throw new Error("expected "+(wanted??"expression"));return t;};
 const parse=(minimum=0):Expr=>{
  const first=take();let result:Expr;
  if(first.text==="let"){
   // `let x = value in body` / `let x: T = value in body`: call-by-need sharing of `value` (one lazy cell), scope = body.
   const name=take();if(!/^[A-Za-z_]\w*$/.test(name.text)||name.text==="in")throw new Error("expected a name after let");
   let type="_";
   if(tokens[cursor]?.text===":"){const colon=take(":");let end=colon;while(tokens[cursor]?.text!=="="){if(cursor>=tokens.length)throw new Error("expected = in let");end=take();}
    type=text.slice(colon.end,tokens[cursor].start).trim();if(!type)throw new Error("missing let type");}
   take("=");const value=parse();take("in");const letBody=parse();
   return {kind:"let",name:name.text,type,value,body:letBody,span:{...location(first.start,first.end),end:letBody.span.end}};
  }
  if(first.text==="if"){
   const condition=parse();take("then");const whenTrue=parse();take("else");const whenFalse=parse();
   result={kind:"if",condition,whenTrue,whenFalse,span:{...location(first.start,first.end),end:whenFalse.span.end}};
   return result;
  }
  if((first.text==="fn"||first.text==="extension")&&tokens[cursor]?.text==="("){
   const open=take("(");let depth=1;let close=open;
   while(depth){close=take();if(close.text==="(")depth++;if(close.text===")")depth--;}
   const parameters=splitParameters(text.slice(open.end,close.start));take("->");
   const typeStart=tokens[cursor]?.start;if(typeStart===undefined)throw new Error("missing closure result type");
   while(tokens[cursor]?.text!==":"){if(cursor>=tokens.length)throw new Error("missing closure body");cursor++;}
   const colon=take(":");const resultType=text.slice(typeStart,colon.start).trim();if(!resultType)throw new Error("missing closure result type");
   const closureBody=parse();const range={...location(first.start,first.end),end:closureBody.span.end};
   result=first.text==="fn"?{kind:"lambda",parameters,resultType,body:closureBody,span:range}:
    {kind:"extension-value",parameters,targetType:resultType,body:closureBody,span:range};
  }else if(first.text==="{"){
   const fields:{name:string,value:Expr}[]=[];
   if(tokens[cursor]?.text!=="}")while(true){const key=take();const name=fieldName(key.text);take(":");fields.push({name,value:parse()});if(tokens[cursor]?.text!==",")break;take(",");}
   const end=take("}");result={kind:"record",fields,span:location(first.start,end.end)};
  }else if(first.text==="("){
   if(tokens[cursor]?.text===")"){const end=take(")");result={kind:"unit",span:location(first.start,end.end)};}
   else{result=parse();take(")");}
  }else if(first.text==="true"||first.text==="false")result={kind:"bool",value:first.text==="true",span:location(first.start,first.end)};
  else if(/^[0-9]+n?$/.test(first.text))result={kind:"nat",value:first.text.replace(/n$/," ").trim().replace(/^0+(?=[0-9])/ ,""),span:location(first.start,first.end)};
  else if(first.text.startsWith('"'))result={kind:"string",value:JSON.parse(first.text),span:location(first.start,first.end)};
  else if(/^[A-Za-z_]\w*$/.test(first.text))result={kind:"var",name:first.text,span:location(first.start,first.end)};
  else throw new Error("expected expression atom");
  while(cursor<tokens.length){
   const next=tokens[cursor].text;
   if(next==="."){take(".");const field=take();const name=fieldName(field.text);
    result={kind:"member",target:result,name,span:{...result.span,end:location(field.start,field.end).end}};continue;}
   if(next==="("){take("(");const args:Expr[]=[];if(tokens[cursor]?.text!==")"){while(true){args.push(parse());if(tokens[cursor]?.text!==",")break;take(",");}}
    const close=take(")");const range={...result.span,end:location(close.start,close.end).end};
    if(result.kind==="var"&&result.name==="compose")result={kind:"compose",specifications:args,span:range};
    else if(result.kind==="var"&&result.name==="fix"){if(args.length!==2)throw new Error("fix expects specification and inherited target");result={kind:"fix",specification:args[0],inherited:args[1],span:range};}
    else if(result.kind==="var"&&result.name==="extend"){if(args.length!==2||args[1].kind!=="record")throw new Error("extend expects inherited target and record fields");result={kind:"extend",inherited:args[0],fields:args[1].fields,span:range};}
    else result={kind:"call",callee:result,args,span:range};continue;}
   const priority=precedence[next];if(priority===undefined||priority<minimum)break;
   take();const right=parse(priority+1);result={kind:"binary",op:next,left:result,right,span:{...result.span,end:right.span.end}};
  }
  return result;
 };
 const result=parse();if(cursor!==tokens.length)throw new Error("unexpected trailing expression token");return result;
}
export function parseObjective(source:string){
 const lines:Line[]=[];let byteOffset=0;
 for(const [i,raw] of source.split("\n").entries()){
  if(raw.includes("\t"))throw new Error("tabs are not indentation in Objective Bend edition1");
  const indent=raw.length-raw.trimStart().length;const text=raw.trim();
  if(text&&!text.startsWith("#"))lines.push({text,indent,number:i+1,start:byteOffset+byteLength(raw.slice(0,indent)),end:byteOffset+byteLength(raw)});
  byteOffset+=byteLength(raw)+1;
 }
 let cursor=0;const imports:{path:string,alias:string,span:Span}[]=[];const declarations:Declaration[]=[];
 const expr=(text:string,line:Line)=>{try{return expression(text,{...span(line),start:line.start+byteLength(line.text.slice(0,line.text.lastIndexOf(text)))});}catch(e){fail(line,String(e));}};
 const body=(indent:number):Body=>{
  const line=lines[cursor];if(!line||line.indent<=indent)throw new Error("missing indented method body");
  cursor++;
  if(line.text.startsWith("match ")&&line.text.endsWith(":")){
   const scrutinee=expr(line.text.slice(6,-1),line);const branches:Extract<Body,{kind:"match"}>["branches"]=[];
   while(cursor<lines.length&&lines[cursor].indent>line.indent){
    const branch=lines[cursor++];const m=/^case\s+(0n?|1n?\+([A-Za-z_]\w*)|_|true|false|([A-Za-z_]\w*)\(\s*([A-Za-z_]\w*)?\s*\))\s*:\s*(.*)$/.exec(branch.text);
    if(!m)fail(branch,"expected zero/successor/true/false/label(binder)/wildcard case");
    const pattern:Extract<Body,{kind:"match"}>["branches"][number]["pattern"]=m[1]==="_"?{kind:"wildcard"}:m[1]==="true"||m[1]==="false"?{kind:"bool",value:m[1]==="true"}:
     m[3]?{kind:"constructor",label:m[3],binder:m[4]??"_"}:m[2]?{kind:"succ",binder:m[2]}:{kind:"zero"};
    const branchBody:Body=m[5]?{kind:"expression",expression:expr(m[5],branch),span:span(branch)}:body(branch.indent);
    branches.push({pattern,body:branchBody,span:span(branch)});
   }
   if(!branches.length)fail(line,"empty match");return {kind:"match",scrutinee,branches,span:span(line)};
  }
  // `let x = value` / `let x: T = value`, then the rest of the body at the same indent. A whole-line
  // `let x = a in b` is an expression and falls through.
  const letLine=/^let\s+([A-Za-z_]\w*)\s*(?::\s*(.+?))?\s*=\s*(.+)$/.exec(line.text);
  if(letLine&&letLine[1]!=="in"){
   let value:Expr|null=null;try{value=expression(letLine[3],{...span(line),start:line.start+byteLength(line.text.slice(0,line.text.lastIndexOf(letLine[3])))});}catch{}
   if(value){
    if(cursor>=lines.length||lines[cursor].indent!==line.indent)fail(line,"a let must be followed by its body at the same indent");
    return {kind:"let",name:letLine[1],type:letLine[2]??"_",value,body:body(line.indent-1),span:span(line)};
   }
  }
  const text=line.text.startsWith("return ")?line.text.slice(7):line.text;
  return {kind:"expression",expression:expr(text,line),span:span(line)};
 };
 while(cursor<lines.length){
  const line=lines[cursor++];if(line.indent!==0)fail(line,"unexpected indentation");
  if(line.text==="edition ObjectiveBend 1")continue;
  const namedImport=/^import\s+([A-Za-z_]\w*)\s+from\s+"(\.\/[^"\\]+\.obend)"$/.exec(line.text);
  if(namedImport){imports.push({path:namedImport[2],alias:namedImport[1],span:span(line)});continue;}
  const imported=/^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?$/.exec(line.text);
  if(/^import\s/.test(line.text)&&/\.bend"?(\s|$)/.test(line.text))fail(line,"Gen-1 ./NAME.bend imports are retired; Objective Bend imports ./NAME.obend");
  if(imported){imports.push({path:imported[1],alias:imported[2]??"",span:span(line)});continue;}
  const spec=/^(suffix\s+)?spec\s+([A-Za-z_]\w*)(?:\s+extends\s+(.+?))?\s+for\s+(.+):$/.exec(line.text);
  if(spec){
   const requirements:Signature[]=[],methods:(Signature&{qualifier:Qualifier,body:Body})[]=[],laws:Extract<Declaration,{kind:"spec"}>["laws"]=[];
   const parents=spec[3]===undefined?[]:spec[3].split(",").map(p=>p.trim());
   for(const parent of parents)if(!/^[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)?$/.test(parent))fail(line,"spec parent must be a declaration name or Alias.Name");
   if(new Set(parents).size!==parents.length)fail(line,"duplicate spec parent");
   while(cursor<lines.length&&lines[cursor].indent>0){
    const clause=lines[cursor++];
    if(clause.text.startsWith("requires ")){requirements.push(signature(clause.text.slice(9),clause));continue;}
    const qualified=/^(def|around|before|after|combine\s+(\+|\*|and))\s+(.*):$/.exec(clause.text);
    if(qualified){const qualifier:Qualifier=qualified[2]?qualified[2] as Qualifier:qualified[1]==="def"?"primary":qualified[1] as Qualifier;
     const method=signature(qualified[3],clause);methods.push({...method,qualifier,body:body(clause.indent)});continue;}
    const law=/^law\s+([A-Za-z_]\w*)(?:\((.*)\))?\s*:\s*(.+)$/.exec(clause.text);
    if(law){laws.push({name:law[1],parameters:splitParameters(law[2]??""),body:expr(law[3],clause),span:span(clause)});continue;}
    fail(clause,"expected requires, actual method body, or law");
   }
   declarations.push({kind:"spec",name:spec[2],suffix:spec[1]!==undefined,parents,targetType:spec[4],requirements,methods,laws,span:span(line)});continue;
  }
  const extension=/^extension\s+([A-Za-z_]\w*)\((.*)\)\s*->\s*(.+):$/.exec(line.text);
  if(extension){declarations.push({kind:"extension",name:extension[1],parameters:splitParameters(extension[2]),targetType:extension[3],body:body(line.indent),span:span(line)});continue;}
  const sum=/^sum\s+([A-Za-z_]\w*):$/.exec(line.text);
  if(sum){const cases:{label:string,type:string,span:Span}[]=[];
   while(cursor<lines.length&&lines[cursor].indent>0){const c=lines[cursor++];const m=/^([A-Za-z_]\w*)\s*:\s*(.+)$/.exec(c.text);
    if(!m)fail(c,"expected sum case label: Type");cases.push({label:m[1],type:m[2],span:span(c)});}
   if(!cases.length)fail(line,"empty sum");if(new Set(cases.map(c=>c.label)).size!==cases.length)fail(line,"duplicate sum label");
   declarations.push({kind:"sum",name:sum[1],cases,span:span(line)});continue;}
  const record=/^record\s+([A-Za-z_]\w*):$/.exec(line.text);
  if(record){const methods:Signature[]=[],fields:{name:string,type:string,span:Span}[]=[];while(cursor<lines.length&&lines[cursor].indent>0){const method=lines[cursor++];const field=/^([A-Za-z_]\w*|"(?:[^"\\]|\\.)*"):\s*(.+)$/.exec(method.text);if(field)fields.push({name:fieldName(field[1]),type:field[2],span:span(method)});else methods.push(signature(method.text,method));}
   declarations.push({kind:"record",name:record[1],methods,fields,span:span(line)});continue;}
  if(line.text.startsWith("def ")&&line.text.endsWith(":")){declarations.push({kind:"function",signature:signature(line.text.slice(4,-1),line),body:body(line.indent),span:span(line)});continue;}
  fail(line,"unsupported Objective Bend declaration");
 }
 return {schema:"dregg.objective-bend.module.v1",edition:"objective-bend-1",imports,declarations,
  theoremScope:"new source AST; elaboration and reference semantics are Objective Core4"};
}
