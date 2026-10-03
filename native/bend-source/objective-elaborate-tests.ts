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
