// Capture-bound request authoring; does not admit source/native authority.
import {readFileSync,writeFileSync} from "node:fs";
import {resolve} from "node:path";
import {createHash} from "node:crypto";
const [capturePath,requestPath,argsJson="[]",projectionJson="[]",limitsJson,argumentEncoding="legacy-values-v1"]=process.argv.slice(2);
if(!capturePath||!requestPath)throw Error("usage: objective-preview-request CAPTURE_JSON NEW_REQUEST_JSON ARGS_JSON PROJECTIONS_JSON [LIMITS_JSON] [legacy-values-v1|typed-values-v1]");
const bytes=readFileSync(capturePath),capture=JSON.parse(new TextDecoder("utf-8",{fatal:true}).decode(bytes));
if(capture.schema!=="dregg.objective-bend.captured-package.v1"||capture.edition!=="objective-bend-1")throw Error("Objective capture required");
const arguments_=JSON.parse(argsJson),projections=JSON.parse(projectionJson);
if(!Array.isArray(arguments_)||!Array.isArray(projections))throw Error("arguments and projections arrays required");
const request={schema:"dregg.objective-bend.preview-input.v2",capturePath:resolve(capturePath),argumentEncoding,captureSha256:createHash("sha256").update(bytes).digest("hex"),arguments:arguments_,projections,
 limits:limitsJson?JSON.parse(limitsJson):{ticks:"4096",heap:"8192",stack:"1024",typeFuel:"4096"}};
writeFileSync(requestPath,JSON.stringify(request,null,2)+"\n",{flag:"wx"});
console.log(JSON.stringify({schema:request.schema,requestPath:resolve(requestPath),captureSha256:request.captureSha256,sourceEntry:capture.sourceEntry}));
