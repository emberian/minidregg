/-
KN2-STORE-OPEN LAYER-2 planted forges. These ELABORATE (the types cannot stop them); the
receiver-token audit (Host/ReceiverTokenAudit, list in scripts/kn2/token-audit-list.txt) must
flag every one of them by name.
-/
import Compiler.DurableHistoryReader

open Minidregg.Compiler
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)

-- FORGE-A: a genesis head minted outside the open (for a Store that is not empty, every
-- nullifier and transaction id would read as verifiably absent).
def forgeGenesis (store : StoreIdentity) : Head store := Head.genesis store ⟨0⟩

-- FORGE-B: a Store identity minted outside the open, under a key of the forger's choosing.
def forgeIdentity (key : DurableCheckpointCodec.MacKey) : StoreIdentity := StoreIdentity.ofOpen key ⟨0⟩

-- FORGE-C: the identity built by tactic (the `by constructor` route around a private constructor).
def forgeByConstructor (key : DurableCheckpointCodec.MacKey) : StoreIdentity := by
  constructor
  · exact key
  · exact ⟨0⟩
