import {parseObjective} from './objective-parser.ts';
import {elaborate,literalAnnotations} from './objective-elaborate.ts';
const moduleFor=(source:string)=>({name:'Probe',sha256:'test-only',astSha256:'test-only',imports:[],ast:parseObjective(source)});
const run=(body:string,type:string)=>elaborate([moduleFor(`edition ObjectiveBend 1\ndef value() -> ${type}:\n  ${body}\n`)],0,'value',[]);
const bool=literalAnnotations(run('true','Bool'));
if(bool.schema!=='dregg.objective-bend.typed-core.v2'||bool.bounds[0].type.member.tag!=='boolean')throw Error('Bool source annotation lost');
const label=literalAnnotations(run('"ordinary text"','String'));
if(label.schema!=='dregg.objective-bend.typed-core.v2'||label.bounds[0].type.member.tag!=='label')throw Error('String source annotation lost');
for(const formerlyReserved of ['true','false']){
 const strings=literalAnnotations(run(JSON.stringify(formerlyReserved),'String'));
 if(strings.schema!=='dregg.objective-bend.typed-core.v2'||strings.bounds[0].type.member.tag!=='label')throw Error('String content reclassified as Boolean');
}
const unknown=literalAnnotations(run('7n','Unknown'));
if(unknown.status!=='unsupported')throw Error('unsupported authored type silently replaced');
const inferred=elaborate([moduleFor('edition ObjectiveBend 1\ndef value(x: Nat):\n  return x + 1n\n')],0,'value',['7']);
const proposal=literalAnnotations(inferred);
if(proposal.schema!=='dregg.objective-bend.typed-core.v2'||proposal.bounds[0].type.member.codomain.tag!=='natural')throw Error('ordinary result hole did not infer actual primitive body');
console.log('OBJECTIVE ELABORATION DIAGNOSTICS PASS: Bool/String distinction, formerly reserved String acceptance, unknown type refusal');

const identityModule=moduleFor('edition ObjectiveBend 1\ndef identity(x: String) -> String:\n  return x\n');
const typed=(values:any[])=>({schema:'dregg.objective-bend.argument-values.v1',values});
const identity=(value:any)=>elaborate([identityModule],0,'identity',typed([value]));
if(identity({tag:'label',value:'7'}).term.arg.tag!=='label')throw Error('typed String coerced to Nat');
if(identity({tag:'natural',value:'7'}).term.arg.tag!=='nat')throw Error('typed Nat reclassified');
if(identity({tag:'boolean',value:true}).term.arg.tag!=='boolean')throw Error('typed Boolean reclassified');
const nested=identity({tag:'record',fields:[{name:'root',value:{tag:'label',value:'00ab'}}]});
if(nested.term.arg.fields[0].value.tag!=='label')throw Error('nested String lost');
for(const bad of [{tag:'natural',value:'07'},{tag:'natural',value:'-1'},{tag:'label',value:'7',extra:true},{tag:'boolean',value:'true'},{tag:'record',fields:[{name:'x',value:{tag:'natural',value:'0'}},{name:'x',value:{tag:'natural',value:'1'}}]}]){
 let refused=false;try{identity(bad)}catch{refused=true}if(!refused)throw Error('malformed tagged value accepted');
}
let extraRefused=false;try{elaborate([identityModule],0,'identity',{...typed([]),extra:true})}catch{extraRefused=true}
if(!extraRefused)throw Error('ignored argument envelope field');
console.log('TAGGED ARGUMENT VALUES PASS: exact Nat/Boolean/String/record and malformed-value refusals');
