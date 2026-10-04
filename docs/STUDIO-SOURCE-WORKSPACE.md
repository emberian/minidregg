# Source workspace

The source studio composes ordinary module documents into an ordered package
manifest. A member creates source module documents with the normal document
creation flow, selects their held reference names, chooses the entry module and
definition, and records imports of earlier modules. Imports are composition
choices; they grant no access to a module.

Each source editor uses the existing document editor's signed base, durable
submission identity, exact outcome recovery and retained stale draft. Source
and history links use ordinary current-authorized document inspection. A fresh
current source read gates opening a module through the studio, including when a
retained editor is selected. Previously opened drafts remain separate from the
currently saved module text.

Composition updates compare the selected workspace revision. Submitted manifest
text is retained before parsing or revision comparison, so malformed and stale
composition drafts survive reload without replacing the selected package.
Capturing saved source rereads every module under the member's current access,
requires identical native read coordinates, and retains exact source roots and
source bytes for the canonical package producer. The generated producer input
uses the existing `dregg.bend.package-input.v1` schema. This local source custody
is not a canonical source identity, publication receipt or execution authority.

The first source implementation is WIP and has not been compiled or received in
a browser. Governed publication, prototype instantiation and instance evolution
are unavailable until their real producer and native intent APIs are connected.
Objective Bend preview is a separate route (`studio_preview.rs` to the pinned Host's
`objective-front` command; see [Objective Bend](OBJECTIVE-BEND.md#execution-paths)). No compiler success or installed program is
inferred from a document save or package metadata.

Module, import and entry controls apply exact revision-bound composition operations.
Every submitted operation is retained before validation or revision comparison.
Earlier composition revisions are inspectable and can be forked into a separate
workspace. Forks retain ordinary document references; they do not copy private
source or confer access. Existing source editor drafts remain retained.

Prototype declarations in `native/resource-client/src/workspace/studio.rs` still
carry the Gen-1 `dregg.objective-bend.partial-input.v1` shape (directParents,
ancestorOrder, required finalSelf/priorSuper selectors, provided entries). Its
producer, `Host/ObjectiveBendPartialAuthor`, was deleted with Gen-1 on 2026-10-04,
so these declarations feed nothing. In Objective Bend Core4 ancestry and
requirements are written in `.obend` source (`compose`, `requires`), not in a
side declaration; this editor code must be rewritten against the Objective front
end or deleted.
