/- A named finite continuity witness for legacy→selected→empty→selected. -/
module

public import Kernel.FnConsumerFrontierCore

-- Bodies this file reduces through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.FnConsumerFrontierScenario

open Minidregg.Kernel.FnConsumerFrontierCore

set_option autoImplicit false

private def key : Key :=
  ⟨[1], ⟨[1], [2], [3], [4], [5], 1, 0, 1⟩, [6], ⟨7⟩, 0, ⟨8⟩⟩

private def receipt1 : Minidregg.Compiler.NativeHostCodec.Receipt :=
  ⟨⟨11⟩, ⟨12⟩, 1, ⟨13⟩⟩
private def receipt2 : Minidregg.Compiler.NativeHostCodec.Receipt :=
  ⟨⟨21⟩, ⟨22⟩, 2, ⟨23⟩⟩
private def receipt3 : Minidregg.Compiler.NativeHostCodec.Receipt :=
  ⟨⟨31⟩, ⟨32⟩, 3, ⟨33⟩⟩
private def receipt4 : Minidregg.Compiler.NativeHostCodec.Receipt :=
  ⟨⟨41⟩, ⟨42⟩, 4, ⟨43⟩⟩

private def legacy : Transition :=
  ⟨key, .legacyEmpty, 0, 2, none, none, receipt1⟩
private def selected1 : Transition :=
  ⟨key, .selectedV2, 2, 4, some 3, some receipt1, receipt2⟩
private def empty : Transition :=
  ⟨key, .emptyV2, 4, 5, none, some receipt2, receipt3⟩
private def selected2 : Transition :=
  ⟨key, .selectedV2, 5, 7, some 6, some receipt3, receipt4⟩

theorem finite_continuity :
    (do
      let a ← step [] legacy
      let b ← step a selected1
      let c ← step b empty
      let d ← step c selected2
      pure (lookup d key).position) = .ok 7 := by
  decide

theorem duplicate_transition_refused :
    (do
      let a ← step [] legacy
      let b ← step a selected1
      step b selected1) =
        .error "fn consumer progress predecessor or scan window differs" := by
  decide

end Minidregg.Kernel.FnConsumerFrontierScenario
