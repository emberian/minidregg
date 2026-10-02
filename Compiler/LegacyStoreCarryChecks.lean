/- Receiving poles for the actual Store2 paid payload boundary. The shared
PayCellUpgrade proofs cover typed rows; these checks also exercise the frozen
source frame and the final target decoder path. -/
import Compiler.LegacyStoreCarry

namespace Minidregg.Compiler.LegacyStoreCarryChecks
open Minidregg.Kernel
open LegacyStoreCarry
set_option autoImplicit false

private def sourceBytes : List UInt8 :=
  encodeV2 PayCellLegacyV4.wire PayCellLegacyV4.enrolledFixture

private def refuses (bytes : List UInt8) : Bool :=
  match decodePay bytes with
  | .error _ => true
  | .ok _ => false

private def enrolledCarry : Bool :=
  match decodePay sourceBytes with
  | .error _ => false
  | .ok store =>
      PayCell.enrolmentAt store PayEnrolMemo.fixtureMemo.miniKey ==
          some ⟨PayEnrolMemo.fixtureMemo.sshBlob, 108, some 1, 500168, 900⟩ &&
        PayCell.sshIndexAt store PayEnrolMemo.fixtureMemo.sshBlob ==
          some PayEnrolMemo.fixtureMemo.miniKey &&
        PayCell.tariffOf store == PayCellLegacyV4.tariffOf PayCellLegacyV4.enrolledFixture &&
        (PayCell.computeActivationOf store).isNone &&
        (PayCell.computeUsageAt store 108).isNone &&
        (PayCell.chainTipOf store).isNone &&
        (PayCell.claimAt store [1, 2, 3]).isNone &&
        (PayCell.claimConsumptionAt store [1, 2, 3]).isNone

#guard enrolledCarry
-- A newer outer frame does not silently widen the source language.
#guard refuses (StoreCodec.encode PayCellLegacyV4.wire PayCellLegacyV4.enrolledFixture)
-- Neither current target bytes nor a current payload in an old frame is old v4.
#guard refuses (StoreCodec.encode PayCell.wire
  (PayCellUpgrade.lift PayCellLegacyV4.enrolledFixture))
#guard refuses (encodeV2 PayCell.wire
  (PayCellUpgrade.lift PayCellLegacyV4.enrolledFixture))
#guard refuses (sourceBytes ++ [0])
#guard refuses (sourceBytes.dropLast)

end Minidregg.Compiler.LegacyStoreCarryChecks
