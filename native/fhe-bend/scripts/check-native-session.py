#!/usr/bin/env python3
"""Actual signed isolated native FHE journey; requires matching built Host/client.
Zero monetary tariff/balance; no mock receipts, seeded history or live deployment.
All runtime keys, ciphertexts and journals stay in a fresh private evidence tree.
"""
import argparse, hashlib, json, os, shlex, subprocess
from pathlib import Path

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,obj): Path(p).write_text(json.dumps(obj,separators=(",",":"))+"\n")
def run(argv,log):
    with Path(log).open("wb") as out:
        subprocess.run([str(x) for x in argv],stdout=out,stderr=subprocess.STDOUT,check=True)
def read(p): return json.loads(Path(p).read_text())
def decimal(s):
    if not isinstance(s,str) or not s.isdecimal() or str(int(s))!=s: raise ValueError("noncanonical native decimal")
    return s

def main():
    ap=argparse.ArgumentParser()
    for name in ["host","mini","store","signature","source-artifact","source-inspection",
                 "compiler-artifact","compiler-pin","evaluator","owner","new-evidence"]:
        ap.add_argument("--"+name,required=True)
    a=ap.parse_args()
    root=Path(a.new_evidence).resolve()
    if root.exists(): raise ValueError("evidence tree already exists")
    root.mkdir(mode=0o700)
    for name in ["host","mini","store","signature","evaluator","owner"]:
        value=Path(getattr(a,name)).resolve()
        if not value.is_file() or not os.access(value,os.X_OK): raise ValueError("missing actual executable: "+name)
        setattr(a,name,str(value))
    artifact=Path(a.source_artifact).resolve()
    compiler=Path(a.compiler_artifact).resolve()
    if sha(compiler)!=a.compiler_pin: raise ValueError("compiler bytes differ from actual checked pin")
    inspection=read(a.source_inspection)
    if inspection.get("schema")!="dregg.fhe-bend.source-publication-inspection.v1":
        raise ValueError("source-owned canonical inspection required")
    source_atom=decimal(inspection["artifactId"]); source_schema=decimal(inspection["sourceSchema"])
    key=root/"owner-authority.key"; pub=root/"owner-authority.pub"
    run([a.mini,"keygen","--secret",key,"--public",pub,"--no-prerotation"],root/"keygen.log")
    key.chmod(0o600)
    operator={"domain":98501,"federation":9,"factoryId":10,"resourceBookId":11,
      "authorityCellId":12,"issuer":5,"ownerBudget":10000000,"lifetime":10000,
      "tariffBase":0,"tariffPerBirth":0,"tariffPerGrant":0,"tariffPerInitialPayloadByte":0,
      "collector":99,"asset":0,"genesisHeight":10,"expectedSeed":0,
      "storageBinary":a.store,"storageRoot":str(root/"store"),"signatureBinary":a.signature}
    op=root/"operator.json"; write(op,operator)
    run([a.host,op,"profile"],root/"profile.json")
    semantics=decimal(read(root/"profile.json")["semantics"])
    allpred={"type":"all","predicates":[]}
    genesis={k:str(operator[k]) for k in ["domain","factoryId","resourceBookId","authorityCellId",
      "federation","tariffBase","tariffPerBirth","tariffPerGrant","tariffPerInitialPayloadByte","collector","asset","genesisHeight"]}
    genesis.update({"expectedSemantics":semantics,"issuerEpoch":"2","factoryPredicate":allpred,
      "enrollments":[{"key":{"keyId":"7007","keyEpoch":"2","algorithm":"1","subject":"7",
        "publicKey":pub.read_bytes().hex(),"activeFrom":"0","activeUntil":"1000000","nextKeyDigest":None},
        "accountId":"7","spendCapabilityId":"41","controlCapabilityId":"51",
        "factoryObserveCapabilityId":"54","initialBalance":"0","accountPredicate":allpred}],
      "factoryControllerSubject":"7","factoryControllerCapability":"53","clockTickers":[],"tailBound":"256",
      "meterAllowance":{k:"50000000" for k in ["incidences","turnBytes","memoryTouches","witnessBytes",
        "proofWork","storageBytes","networkBytes","sideEffectCount","feeDebit","leaseByteBlocks"]}})
    gen=root/"genesis.json";write(gen,genesis)
    run([a.mini,"bootstrap","--host",a.host,"--config",op,"--source",gen,"--dir",root/"deployment"],root/"bootstrap.log")
    config=root/"deployment/pinned-config.json"
    resources=[{"kind":"object","storage":"content","target":str(target),"owner":"7",
      "ownerCapability":str(cap),"controlCapability":str(cap+1),"predicate":allpred}
      for target,cap in [(600,61),(601,63),(602,65)]]
    birth={"subject":"7","nonce":"22000","birth":{"genesis":genesis,
      "template":{"issuer":"5","ownerBudget":"10000000","lifetime":"10000"},
      "creator":"7","nonce":"22000","resources":resources,"sourceCapabilities":["41"],
      "funding":[],"feePayer":"7"},"grants":[{"kind":"object","target":"10","capability":"54"},
        {"kind":"account","target":"7","capability":"41"}]}
    bp=root/"birth.json";write(bp,birth)
    run([a.mini,"submit","--host",a.host,"--config",config,"--intent",bp,"--intent-kind","birth-intent",
         "--key",key,"--dir",root/"birth"],root/"birth.log")
    if read(root/"birth/outcome.json").get("type")!="confirmed": raise ValueError("real birth not confirmed")
    def query(target,cap,label,nonce):
        qp=root/(label+".json")
        write(qp,{"subject":"7","nonce":str(nonce),"purpose":{"type":"query","kind":"object",
          "target":str(target),"view":"resource"},"grants":[{"kind":"object","target":str(target),"capability":str(cap)}]})
        run([a.mini,"query","--host",a.host,"--config",config,"--intent",qp,"--key",key,
          "--view","resource","--dir",root/label],root/(label+".log"))
        return decimal(read(root/label/"view.json")["cell"]["root"])
    source_before=query(600,61,"source-before",30001)
    publish={"subject":"7","nonce":"30002","purpose":{"type":"prepare","draft":{"type":"invoke",
      "command":{"subject":"7","nonce":"30003","targets":[{"kind":"object","target":"600",
        "capability":"61","observeCapability":None,"schemaVersion":"1","expectedTargetRoot":source_before,
        "payload":{"type":"content","actions":[{"type":"createAtom","atom":source_atom,
          "kind":{"type":"inlineObject","schema":source_schema},"payload":artifact.read_bytes().hex()}]}}]}}},
      "grants":[{"kind":"object","target":"600","capability":"61"}]}
    pp=root/"publish-source.json";write(pp,publish)
    run([a.mini,"submit","--host",a.host,"--config",config,"--intent",pp,"--key",key,
      "--dir",root/"source-publication"],root/"publish-source.log")
    if read(root/"source-publication/outcome.json").get("type")!="confirmed":
        raise ValueError("real source publication not confirmed")
    source_root=query(600,61,"source-current",30004)
    key_root=query(601,63,"key-before",30005)
    result_root=query(602,65,"result-before",30006)
    for name in ["custody","snapshots"]: (root/name).mkdir(mode=0o700)
    # This wrapper only routes to the actual qualified Host's source-owned
    # native session commands. The host and client have separate session pins.
    wrapper=root/"native-driver.sh"
    wrapper.write_text("#!/bin/sh\nset -eu\nexec "+shlex.quote(a.host)+" "+shlex.quote(str(config))+" bend-session \"$@\"\n")
    wrapper.chmod(0o700)
    transformer=Path(a.evaluator).parent.parent.parent/"transformer-id.txt"
    # Actual physical binary normally lives target/release; explicit sibling
    # provenance file is generated by its source-pinned scoped build.
    if not transformer.exists(): raise ValueError("physical transformer pin file unavailable")
    transformer_pin=transformer.read_text().strip()
    if len(transformer_pin)!=64: raise ValueError("physical transformer pin shape")
    session={"schema":"dregg.fhe-bend.native-session.v1","subject":"7","nonce":"40000",
      "sourceResource":"600","sourceCapability":"61","sourceRoot":source_root,"sourceAtom":source_atom,
      "keyResource":"601","keyCapability":"63","keyRoot":key_root,"keyAtom":"0",
      "resultResource":"602","resultCapability":"65","resultRoot":result_root,"releaseCapability":"65",
      "audience":"7","generation":"0","purpose":"owner-local-test-result","returnName":"encrypted-result",
      "predecessor":"0","capacity":["10000000"]*10,"compilerSHA256":a.compiler_pin,
      "physicalBinary":a.evaluator,"physicalBinarySHA256":sha(a.evaluator),
      "physicalTransformerSHA256":transformer_pin,"custodyClient":a.mini,"custodyClientSHA256":sha(a.mini),
      "nativeHost":a.host,"nativeHostSHA256":sha(a.host),"nativeConfigPath":str(config),
      "authoritySeedPath":str(key),"privateRoot":str(root/"custody"),
      "physicalSnapshotRoot":str(root/"snapshots"),"cursorPath":str(root/"cursor.bin")}
    sp=root/"session.json";write(sp,session)
    run([a.owner,compiler,a.compiler_pin,a.evaluator,root/"owner-run","--governed",artifact,wrapper,
      sha(wrapper),sp],root/"native-owner-journey.log")
    repeated=(root/"owner-run/next-completion.json").is_file()
    candidate=root/("owner-run/next-completion.json" if repeated else "owner-run/completion.json")
    request=root/("owner-run/next-request.json" if repeated else "owner-run/request.json")
    released=root/("owner-run/release-1/released-completion.json" if repeated else "owner-run/release-0/released-completion.json")
    if candidate.read_bytes()!=released.read_bytes(): raise ValueError("released completion differs")
    if not (root/"cursor.bin").is_file(): raise ValueError("canonical storage/release cursor absent")
    # Real original-attempt recovery must return identical retained bytes.
    keyhandle=root/"owner-run/key-registration/key-record.json"; retry=root/"retried-completion.json"
    run([wrapper,"commit-release",artifact,compiler,keyhandle,request,
      candidate,sp,retry],root/"original-receipt-retry.log")
    if retry.read_bytes()!=candidate.read_bytes(): raise ValueError("retry returned other bytes")
    # These calls use the actual driver/current native image. They must emit no
    # new context or release bytes; a process failure alone is not sufficient.
    def refuse(arguments,label,output):
        with (root/(label+".log")).open("wb") as log:
            result=subprocess.run([str(x) for x in arguments],stdout=log,stderr=subprocess.STDOUT)
        if result.returncode==0 or output.exists():
            raise ValueError("native refusal emitted an output: "+label)
    for field,bad in [("sourceCapability","999999"),("keyCapability","999999"),
                      ("sourceRoot","0"),("compilerSHA256","0"*64)]:
        altered=dict(session); altered[field]=bad
        badconfig=root/("refuse-"+field+".json"); write(badconfig,altered)
        output=root/("refuse-"+field+"-context.json")
        refuse([wrapper,"prepare-context",artifact,compiler,keyhandle,badconfig,output],
               "refuse-"+field,output)
    wrong=read(candidate); wrong["request_sha256"]="0"*64
    wrongfile=root/"wrong-completion.json"; write(wrongfile,wrong)
    output=root/"wrong-released-completion.json"
    refuse([wrapper,"commit-release",artifact,compiler,keyhandle,request,wrongfile,sp,output],
           "refuse-completion-request-binding",output)
    print("FHE NATIVE JOURNEY PASS: actual signed source/key/read/storage/current release; exact recipient bytes; original receipt retry; current source/key/root/compiler/candidate refusals; opaque custody only")
if __name__=="__main__": main()
