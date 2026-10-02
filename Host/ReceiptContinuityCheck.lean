import Host.ReceiptContinuity

namespace Minidregg.Host.ReceiptContinuityCheck

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.ReceiptContinuity
open Minidregg.Host.ReceiptContinuity
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.WorldRoot

private def witness (height : Nat) (chain : Digest) : RootWitness :=
  let roots := DurableReceiverIO.RootCache.ofEntries
    [(.system, DurableCheckpointCodec.systemLeaf height chain), (.cell 7, ⟨91⟩)]
  ⟨⟨height, roots.root⟩, chain, cachedSiblings roots.tree (deployed.ix .system)⟩

private def check (name : String) (okay : Bool) : IO Unit := do
  unless okay do throw (IO.userError s!"receipt continuity: {name}")

private def accepted (query : Query) (extension : Extension) : Bool :=
  (verify query extension).isOk

private def run : IO Unit := do
  let identity : Identity := ⟨⟨1⟩, ⟨2⟩, ⟨3⟩⟩
  let start := witness 0 ⟨13⟩
  let suffix : List Digest := [⟨17⟩, ⟨18⟩]
  let ending := witness 2 (chainAfterDigests start.chain suffix)
  let query : Query := ⟨identity, some start.point, ending.point⟩
  let extension : Extension := ⟨identity, start.point, ending.point, start.chain, ending.chain,
    start.siblings, ending.siblings, suffix, true⟩
  check "actual system openings and suffix accepted" (accepted query extension)
  check "suffix replacement refused" (!accepted query { extension with suffix := [⟨19⟩, ⟨18⟩] })
  check "suffix reorder refused" (!accepted query { extension with suffix := suffix.reverse })
  check "truncated suffix refused" (!accepted query { extension with suffix := [⟨17⟩] })
  check "missing old opening refused" (!accepted query { extension with fromSiblings := [] })
  check "missing new opening refused" (!accepted query { extension with toSiblings := [] })
  check "forged old chain refused" (!accepted query { extension with startChain := ⟨14⟩ })
  check "forged new chain refused" (!accepted query { extension with endChain := ⟨14⟩ })
  check "wrong response root refused" (!accepted query
    { extension with endPoint := { ending.point with worldRoot := ⟨0⟩ } })
  check "wrong identity refused" (!accepted query
    { extension with identity := { identity with expectedSeed := ⟨4⟩ } })
  check "false completion flag refused" (!accepted query { extension with complete := false })
  check "lower head refused" (!accepted { query with anchor := some ending.point, target := start.point } extension)
  check "same height different root refused" (!accepted
    ⟨identity, some ending.point, { ending.point with worldRoot := ⟨0⟩ }⟩ extension)
  let bootstrap : Query := ⟨identity, none, ending.point⟩
  let first : Extension := ⟨identity, ending.point, ending.point, ending.chain, ending.chain,
    ending.siblings, ending.siblings, [], true⟩
  check "explicit endpoint bootstrap accepted" (accepted bootstrap first)
  check "bootstrap cannot smuggle unrelated prefix" (!accepted bootstrap extension)
  check "extra path sibling refused" (!accepted query
    { extension with toSiblings := ⟨0⟩ :: ending.siblings })
  IO.println "receipt-continuity: 16 source-verifier checks passed"

#eval run

end Minidregg.Host.ReceiptContinuityCheck
