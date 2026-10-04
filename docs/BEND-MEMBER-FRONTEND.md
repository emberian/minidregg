# Member frontend producer

> **Status (2026-10-04).** This is the upstream-Bend front end for the retiring
> BendTT path (`member-frontend.ts` emits `book.bendtt` for `BendCoreAdmission`).
> It is not an Objective Bend front end; that is `objective-frontend.ts`, described
> in [source capture](OBJECTIVE-BEND-FRONTEND.md). The Gen-1 linker preview this
> page once fed was deleted on 2026-10-04.

Run `bun native/bend-source/member-frontend.ts PACKAGE_SPEC OUTPUT_DIRECTORY PINNED_TOOLING_ROOT`.
The package spec is the existing `dregg.bend.package-input.v1`: ordered modules with name,
sourcePath, and imports (alias and earlier decimal-string module index); decimal-string
entryModule and entryDefinition. Only explicitly listed files are read. Each source is
snapshotted once; aliases and leading import syntax must exactly match the manifest.
Base has the empty upstream namespace; ordinary module names become namespaces.

The pinned Bend parser and safe emitter handle their supported pure source language:
dependent/quantity types, datatypes, ordinary functions, case trees, and source recursion.
Foreign, unsafe, bodyless user definitions, holes, unresolved imports, or out-of-scope
elaboration produce structured diagnostics. Standard-library declarations are dependencies
rather than user roots; reached opaque/foreign assumptions still need actual Mini core
admission. This frontend is broader than the numeric input/literal/add circuit grammar.
There is no implicit loader, hub, source execution, telemetry, or upstream kernel build.

Success writes emitted book.bendtt, frontend.json, exact source snapshots, and
package-input.json referencing those snapshots. The transcript reports actual emitted
SHA256, coreEntry, pinned tooling, module/import/source SHA identities, and stage status.
SHA256 is a transcript/deployment hash. It is never relabeled as Mini cSHAKE identity.

Run the existing Host.BendPackage producer on package-input.json to obtain canonical
Mini Package bytes. Then run Host.BendMemberFrontendCheck with PACKAGE_BYTES EMITTED_BOOK
CORE_ENTRY OUTPUT_DIRECTORY. It canonicalizes and admits the exact Book through
BendCoreAdmission, checks the selected entry, and writes canonical.bendtt plus checked.json.
Diagnostics use dregg.bend.compiler-diagnostic.v1, stage, and message. Native Plan/effect/current-authority admission remains
a separate receiver. Captured elaboration is not a universal TypeScript correctness theorem.
