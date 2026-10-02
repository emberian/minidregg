#!/usr/bin/env python3
"""Join an independently received export to its source room job.

This coordination artifact carries receipt coordinates, never document text or
credentials. Native document grants remain the runtime admission boundary.
"""
import argparse
import fcntl
import importlib.util
import json
import os
from pathlib import Path


def construct(request, journey_input, result, status):
    def require(ok, message):
        if not ok:
            raise RuntimeError(message)
    require(request["protocol"] == "mini-resident-room-capture-request-v1", "room request protocol differs")
    require(result["protocol"] == "mini-app-document-journey-result-v1" and result["status"] == "saved", "independent document receiving is incomplete")
    require(status["type"] == "mini-app-document-result-v1" and status["status"] == "saved", "document publication remains undecided")
    require(status["id"] == result["operation"] == journey_input["operation"], "retained operation differs")
    require(status["subject"] == result["subject"] and status["target"] == result["target"] == request["documentTarget"], "published document identity differs")
    require(journey_input["reader"]["workspace"] == request["founderWorkspace"]
        and journey_input["reader"]["document"] == request["documentAlias"], "founder source reference was not the independent native reader")
    publication = status["outcome"]
    require(publication["type"] == "confirmed" and publication["confirmation"] in ("installed", "replayed"), "native publication confirmation required")
    for field in ("transactionId", "eventId", "worldRoot", "acceptedCount"):
        require(isinstance(publication[field], str) and publication[field].isascii() and publication[field].isdecimal(), "native receipt coordinate differs")
    require(all(field in result["receipt"] and field in status["receipt"] and result["receipt"][field] == status["receipt"][field] for field in ("bodyBytes","bodySha256","operation","transaction")), "received export custody differs")
    return {"protocol": "mini-captured-document-room-context-v1",
        **{field: request[field] for field in ("worldConfig", "socket", "founderSubject", "founderWorkspace", "founderHome", "roomAlias", "roomTarget", "documentAlias")},
        "documentTarget": status["target"], "connectorSubject": status["subject"],
        "connectorWorkspace": journey_input["workspace"], "operation": status["id"],
        "publicationReceipt": {field:publication[field] for field in ("type","confirmation","transactionId","eventId","worldRoot","acceptedCount")}, "publicationAttempt": status["attempt"],
        "exportCustody": {field:result["receipt"][field] for field in ("bodyBytes","bodySha256","operation","transaction")}, "callSha256": result["callSha256"],
        "evidence": result["evidence"]}


def main():
    os.umask(0o077)
    parser=argparse.ArgumentParser(description=__doc__)
    for arg in ("request", "journey", "result", "status", "output", "custody-helper"):
        parser.add_argument("--"+arg, required=True)
    args=parser.parse_args()
    spec=importlib.util.spec_from_file_location("capture_context_custody", Path(args.custody_helper))
    custody=importlib.util.module_from_spec(spec); spec.loader.exec_module(custody)
    def load(path):
        path=Path(path);custody.private_file(path);return custody.load(path)
    request=load(args.request);journey=load(args.journey);result=load(args.result)
    if Path(args.result)!=Path(result["evidence"])/"result.json" or Path(args.status)!=Path(result["evidence"])/"exact-lookup.json" or Path(args.journey)!=Path(journey["root"])/"input.json":
        raise RuntimeError("receiving evidence paths differ")
    envelope=load(args.status);status=envelope["result"]
    # The journey source-binding checks already established this reader belongs
    # to this Store. Recheck its immutable config/socket and subject here.
    reader=load(Path(request["founderWorkspace"])/"workspace.json")
    if reader["config"]!=request["worldConfig"] or reader["socket"]!=request["socket"] or reader["subject"]!=request["founderSubject"]:
        raise RuntimeError("room request belongs to another native reader")
    provisioned=load(journey["provisioned"])
    if custody.sha(Path(journey["provisioned"]))!=journey["provisionedSha256"]:
        raise RuntimeError("connector provision pin differs")
    connector=load(Path(provisioned["workspace"])/"workspace.json")
    if connector["config"]!=reader["config"] or connector["socket"]!=reader["socket"] or connector["subject"]!=status["subject"] or provisioned["subject"]!=status["subject"]:
        raise RuntimeError("connector/source room identity differs")
    if custody.sha(Path(status["attempt"])/"call.bin")!=result["callSha256"]:
        raise RuntimeError("exact publication call differs")
    journey["workspace"]=provisioned["workspace"]
    context=construct(request,journey,result,status)
    output=Path(args.output);custody.private_directory(output.parent)
    context["receivingInputs"]={field:{"path":str(Path(getattr(args,field))),"sha256":custody.sha(Path(getattr(args,field)))} for field in ("request","journey","result","status")}
    lock=os.open(output.parent/("."+output.name+".lock"),os.O_WRONLY|os.O_CREAT|os.O_NOFOLLOW,0o600)
    try:
        custody.private_file(output.parent/("."+output.name+".lock"))
        fcntl.flock(lock,fcntl.LOCK_EX)
        custody.save(output,context)
    finally:
        os.close(lock)
    print(json.dumps(context))

if __name__=="__main__":
    main()
