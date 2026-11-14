/-
# Theory.KeyedModel -- the logical content of a keyed byte store, as a specification model

An authenticated keyed store (a trie under one root) is specified against what it holds: an
association list from keys to byte strings, read by the first entry of a key. This is the
spec-level form of a stored value (`List UInt8`). Executed code holds rows and digests; the
model appears only in definitions that say what a history's store must hold and in the
statements that tie the rows to it.
-/
module

@[expose] public section

namespace Minidregg.Theory.KeyedModel

/-- The logical content of a store keyed by `K`: key and value bytes, an entry per key held. -/
abbrev Model (K : Type) := List (K × List UInt8)

end Minidregg.Theory.KeyedModel
