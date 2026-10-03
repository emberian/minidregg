// Upstream parser/checker adapter for a sealed package. Never calls book_load:
// that loader performs filesystem/hub/name resolution and implicit Base loads.
// The only parser is the injected, exact-pinned upstream Bend.parse_book.
import { createHash } from "node:crypto";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

export const UPSTREAM = "947db722640c86247849343657bf2f7ef01cb7f1";
const LIMIT = 4 * 1024 * 1024;
const sha256 = (bytes: Uint8Array) => createHash("sha256").update(bytes).digest("hex");
const fail = (condition: unknown, detail: string): void => {
  if (!condition) throw new Error(detail);
};

export type Module = {
  namespace: string;
  bytes: Uint8Array;
  sha256: string;
  imports: { alias: string; path: string; module: number; sha256: string }[];
};
export type Package = { modules: Module[]; entryModule: number; entryDefinition: string };
type Definition = { $: string; u?: boolean; i?: string[]; v?: unknown; b?: boolean };
export type Book = { tlds: Record<string, Definition>; order: string[]; hols: number };
export type Parser<B extends Book> = {
  book_nil(): B;
  parse_book(book: B, dir: string, source: string, namespace: string,
    aliases: Record<string, string>): void;
  book_valid(book: B): void;
};
export type Transcript = {
  schema: "dregg.bend.sealed-parser-transcript.v1";
  upstream: typeof UPSTREAM;
  sourceDigestAlgorithm: "sha256";
  modules: { namespace: string; source: string;
    imports: { alias: string; path: string; module: number; source: string }[] }[];
  entryModule: number;
  entryDefinition: string;
  definitions: string[];
};

// A sealed header resolves exactly the manifest edge; no source path is loaded.
export function sourceImport(text: string): {path:string;alias:string} {
  const named = /^import\s+([A-Za-z_]\w*)\s+from\s+"(\.\/[^"\\]+\.bend)"\s*(?:#.*)?$/.exec(text);
  if (named) return {alias:named[1],path:named[2]};
  const ordinary = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/.exec(text);
  if (!ordinary) throw new Error("malformed source import");
  return {path:ordinary[1],alias:ordinary[2]??""};
}

// Match the pinned loader's leading import grammar. Replacing characters with
// spaces retains every source offset for diagnostics without granting a loader
// access to paths. Manifest edges must equal the actually parsed imports.
function header(module: Module, index: number, modules: Module[]): {
  body: string; aliases: Record<string, string>; imports: Transcript["modules"][number]["imports"]
} {
  const source = new TextDecoder("utf-8", { fatal: true }).decode(module.bytes);
  fail(new TextEncoder().encode(source).length === module.bytes.length, "source encoding changed");
  const lines = source.split("\n");
  const aliases: Record<string, string> = Object.create(null);
  const imports: Transcript["modules"][number]["imports"] = [];
  for (let line = 0; line < lines.length; line++) {
    const trimmed = lines[line].trim();
    if (trimmed === "" || trimmed.startsWith("#")) continue;
    if (!/^import(\s|$)/.test(trimmed)) break;
    const {path,alias} = sourceImport(trimmed);
    fail(alias !== "" || path === "Base", "only Base has an empty alias");
    fail(path === "Base" || /^\.\/(?:[A-Za-z_][\w-]*\/)*[A-Za-z_][\w-]*\.bend$/.test(path),
      "only sealed local import paths are supported; resolve external names before publication");
    fail(!(alias in aliases), "duplicate import alias");
    const edge = module.imports[imports.length];
    fail(edge && edge.path === path && edge.alias === alias, "source and sealed import manifest differ");
    fail(Number.isSafeInteger(edge.module) && edge.module >= 0 && edge.module < index,
      "missing or cyclic sealed import");
    const imported = modules[edge.module];
    fail(imported.sha256 === edge.sha256 && sha256(imported.bytes) === edge.sha256,
      "changed imported source");
    fail(path !== "Base" || imported.namespace === "", "Base must be the sealed empty namespace");
    // Base contributes globally scoped names. An empty alias would collide
    // with every ordinary declaration in upstream parse_fresh.
    if (alias !== "") aliases[alias] = imported.namespace;
    imports.push({ alias, path, module: edge.module, source: edge.sha256 });
    lines[line] = " ".repeat(lines[line].length);
  }
  fail(imports.length === module.imports.length, "unused or undeclared manifest import");
  return { body: lines.join("\n"), aliases, imports };
}

export function checkSealed<B extends Book>(parser: Parser<B>, source: Package): {
  book: B; transcript: Transcript;
} {
  fail(source.modules.length > 0 && source.modules.length <= 256, "module capacity");
  fail(Number.isSafeInteger(source.entryModule) && source.entryModule >= 0 &&
    source.entryModule < source.modules.length, "missing entry module");
  fail(/^[A-Za-z_][\w.]*$/.test(source.entryDefinition), "invalid entry definition");
  fail(new Set(source.modules.map(m => m.namespace)).size === source.modules.length,
    "ambiguous module namespace");
  let total = 0;
  const book = parser.book_nil();
  const modules: Transcript["modules"] = [];
  for (let index = 0; index < source.modules.length; index++) {
    const module = source.modules[index];
    total += module.bytes.length;
    fail(total <= LIMIT, "source byte capacity");
    fail(module.namespace === "" || /^[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*$/.test(module.namespace),
      "invalid sealed namespace");
    fail(/^[0-9a-f]{64}$/.test(module.sha256) && sha256(module.bytes) === module.sha256,
      "changed source module");
    const parsed = header(module, index, source.modules);
    const previous = new Set(Object.keys(book.tlds));
    parser.parse_book(book, "", parsed.body, module.namespace, parsed.aliases);
    if (module.namespace === "") {
      for (const [name, definition] of Object.entries(book.tlds)) {
        if (!previous.has(name)) definition.b = true;
      }
    }
    modules.push({ namespace: module.namespace, source: module.sha256, imports: parsed.imports });
  }
  for (const [name, definition] of Object.entries(book.tlds)) {
    // Unreachable standard-library declarations are not source roots. The
    // emitter still refuses a reached foreign/unsafe/out-of-scope definition.
    if (definition.b === true) continue;
    fail(definition.u !== true, `unsafe definition refused: ${name}`);
    fail(!definition.i?.length, `foreign effect implementation refused: ${name}`);
    fail(definition.$ !== "Def" || definition.v != null, `opaque unbound law refused: ${name}`);
  }
  parser.book_valid(book);
  fail(book.hols === 0, "unfilled source holes");
  const namespace = source.modules[source.entryModule].namespace;
  const entry = namespace === "" ? source.entryDefinition : namespace + ":" + source.entryDefinition;
  fail(book.tlds[entry]?.$ === "Def", "entry is not a filled source definition");
  return {
    book,
    transcript: { schema: "dregg.bend.sealed-parser-transcript.v1", upstream: UPSTREAM,
      sourceDigestAlgorithm: "sha256", modules, entryModule: source.entryModule,
      entryDefinition: source.entryDefinition, definitions: book.order.slice() }
  };
}

export type Elaborator<B extends Book> = { safe_emit(book: B, destination: string): string[] };

// This emits with the pinned upstream elaborator but never invokes safe_check:
// safe_check may build/install its 4.34 kernel. Mini's source kernel separately
// parses/checks the exact emitted Book bytes before computational admission.
export function elaborateSealed<B extends Book>(parser: Parser<B>, safe: Elaborator<B>,
    source: Package, ownedDirectory: string): {
  transcript: Transcript & { emittedBookSha256: string; outOfScope: string[] };
  bookBytes: Uint8Array; bookPath: string; transcriptPath: string;
} {
  const checked = checkSealed(parser, source);
  const output = mkdtempSync(join(ownedDirectory, "sealed-bend-"));
  const bookPath = join(output, "book.bendtt");
  const outOfScope = safe.safe_emit(checked.book, bookPath);
  const bookBytes = readFileSync(bookPath);
  fail(bookBytes.length <= LIMIT, "elaborated Book capacity");
  const transcript = { ...checked.transcript, emittedBookSha256: sha256(bookBytes), outOfScope };
  const transcriptPath = join(output, "transcript.json");
  writeFileSync(transcriptPath, JSON.stringify(transcript) + "\n", { flag: "wx" });
  fail(outOfScope.length === 0, "source contains definitions outside BendTT elaboration scope");
  return { transcript, bookBytes, bookPath, transcriptPath };
}

// This transcript records parser dependencies, not a theorem of source-to-core
// equivalence. Publication must retain exact emitted canonical Book/entry bytes
// and actual Book.check evidence before computational admission.
