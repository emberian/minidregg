// Scoped pinned parser/safe_emit capture; no safe_check/upstream kernel build.
import {readFileSync, writeFileSync} from "node:fs";
import {createHash} from "node:crypto";
const root = process.argv[2];
const tools = process.env.BEND_SOURCE_TOOLING_ROOT;
if (!root || !tools) throw new Error("source root and pinned tooling root required");
const Bend = await import(`${tools}/bend.ts`);
const Safe = await import(`${tools}/safe.ts`);
const digest = (bytes: Uint8Array) => createHash("sha256").update(bytes).digest("hex");
const base = readFileSync(`${tools}/base.bend`);
const source = readFileSync(`${root}/tests/bend-source-representation/NaturalExpressionSource.bend`);
const sourceText=source.toString("utf8");
if (!sourceText.startsWith("import Base\n")) throw new Error("unexpected source import");
const book=Bend.book_nil();
Bend.parse_book(book,"",base.toString("utf8"),"",{});
// The upstream emitter traverses only user roots; base definitions are pulled
// through their actual reference dependencies, exactly as normal Base imports.
for (const def of Object.values(book.tlds)) def.b=true;
Bend.parse_book(book,"",sourceText.replace(/^import Base\n/,"\n"),"",{});
Bend.book_valid(book);
const destination=`${root}/tests/bend-source-representation/NaturalExpressionSource.bendtt`;
const outOfScope=Safe.safe_emit(book,destination);
if(outOfScope.length) throw new Error(outOfScope.join(""));
const bookBytes=readFileSync(destination);
writeFileSync(`${root}/natural-expression-frontend.json`,JSON.stringify({
 schema:"dregg.bend.captured-safe-emit.v1",upstream:"947db722640c86247849343657bf2f7ef01cb7f1",
 baseSha256:digest(base),sourceSha256:digest(source),entry:"SourceNat.doubleSum",
 emittedBookSha256:digest(bookBytes),outOfScope
},null,2)+"\n");
console.log("NATURAL EXPRESSION CAPTURE PASS",digest(bookBytes));
