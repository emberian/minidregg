# Structural authoring only. Lean remains the sole policy/admission evaluator.
def nat: type == "string" and test("^(0|[1-9][0-9]*)$");
def inc:
  if . == "" then "1"
  elif endswith("9") then (.[0:-1] | inc) + "0"
  else .[0:-1] + ((.[-1:] | tonumber) + 1 | tostring) end;
def eq($s; $v): {type:"eq",slot:$s,value:$v};
def neg($p): {type:"not",predicate:$p};
def allp($ps): {type:"all",predicates:$ps};
def anyp($ps): {type:"any",predicates:$ps};
def operation: "authority/operation/pay-claim";
def authorized: "pay/claim/authorized";
def selfenrol: "authority/operation/pay-self-enrol";
def extend($base):
  anyp([allp([eq(operation;"1"),eq(authorized;"1")]),
        allp([neg(eq(operation;"1")),$base])]);
def widen:
  . as $whole |
  if (type != "object" or keys != ["predicates","type"] or
      .type != "all" or (.predicates | type) != "array" or
      (.predicates | length) < 1)
  then error("unknown factory ticker wrapper") else . end |
  .predicates[0:-1] as $tickers |
  if all($tickers[];
    . as $t | .predicate.value as $n |
    ($n | nat) and $t == neg(eq("request/subject";$n)))
  then . else error("unknown ticker confinement") end |
  .predicates[-1] as $observer |
  $observer.predicates[0].predicates[0].value as $subject |
  $observer.predicates[1].predicates[2] as $base |
  if ($subject | nat) and $observer ==
    anyp([allp([eq("request/subject";$subject),eq(selfenrol;"1")]),
          allp([neg(eq("request/subject";$subject)),neg(eq(selfenrol;"1")),$base])])
  then . else error("unknown observer confinement; review required") end |
  if any($base | .. | strings; . == operation or . == authorized)
  then error("claim slots already present; refuse duplicate or unknown claim policy")
  else . end |
  $whole | .predicates[-1].predicates[1].predicates[2] = extend($base);

$policy[0] as $p | $challenge[0] as $c | $reference[0] as $r | $workspace[0] as $w |
if $p.type != "policy" or
   ([$p.policyId,$p.version,$p.address,$p.domain,$p.semantics,$c.authorityRoot,
     $r.target,$r.observeCapability,$r.controlCapability,$w.subject] | all(.[]; nat) | not) or
   ($p.previous != null and ($p.previous | nat | not))
then error("malformed retained policy, authority root, or workspace reference") else . end |
($p.predicate | widen) as $predicate |
{subject:$w.subject,nonce:$nonce,
 purpose:{type:"prepare",draft:{
   type:"install-source",subject:$w.subject,control:$r.controlCapability,
   declaration:{expectedPreRoot:$c.authorityRoot,
     expected:{version:$p.version,address:$p.address},nonce:$declarationNonce,
     source:{policyId:$p.policyId,version:($p.version|inc),domain:$p.domain,
       semantics:$p.semantics,previous:$p.address,predicate:$predicate}}}},
 grants:[{kind:$r.kind,target:$r.target,capability:$r.observeCapability}]}
