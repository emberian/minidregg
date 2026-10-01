/-
`scripts/probe-channel-epoch.lean` — byte fixtures for the CH-EPOCH journey hook, computed by the
kernel's own definitions (`Kernel.DomainEpoch`), never re-implemented.

  lake env lean --run scripts/probe-channel-epoch.lean record DOMAIN EPOCH CLASS N ROOTS MASK SALTBYTE
    prints three lines: the append topic (hex), the record payload (hex), the opening (hex).
    MASK is a string of 0/1, one per position; the record's absentCommit is commitAbsent of
    (MASK, 32 × SALTBYTE). ROOTS tick roots are cSHAKE256 digests of their index.
  lake env lean --run scripts/probe-channel-epoch.lean open PAYLOADHEX OPENINGHEX
    prints `opened <mask length>` or `refused <reason>` (openRecord: the mask length is checked on the
    opening against the record's class and n).
-/
import Kernel.DomainEpoch

open Minidregg.Kernel.DomainEpoch

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def toHex (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def nib (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def ofHex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
      let x ← nib a; let y ← nib b; let r ← ofHex rest
      pure ((x * 16 + y).toUInt8 :: r)
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | ["record", d, e, cls, n, k, mask, salt] =>
    let some d := d.toNat? | throw (IO.userError "domain")
    let some e := e.toNat? | throw (IO.userError "epoch")
    let some cls := cls.toNat? | throw (IO.userError "class")
    let some n := n.toNat? | throw (IO.userError "n")
    let some k := k.toNat? | throw (IO.userError "roots")
    let some salt := salt.toNat? | throw (IO.userError "salt")
    let o : AbsentOpening := ⟨mask.toList.map (· == '1'), ⟨List.replicate 32 salt.toUInt8, by simp⟩⟩
    let r : EpochRecord :=
      { domain := Minidregg.Theory.Channel.U16.ofNat d, epoch := e.toUInt64, classId := cls.toUInt8,
        n := n.toUInt32,
        tickRoots := (List.range k).map fun i => hashWith tickTag [i.toUInt8],
        absentCommit := commitAbsent o }
    let a := recordAppend r
    IO.println (toHex a.topic)
    IO.println (toHex a.payload)
    IO.println (toHex o.encode)
    return 0
  | ["open", payload, opening] =>
    let some p := ofHex payload.toList | throw (IO.userError "payload hex")
    let some ob := ofHex opening.toList | throw (IO.userError "opening hex")
    match EpochRecord.decode p with
    | none => IO.println "refused malformedRecord"; return 1
    | some r =>
      match openRecord r ob with
      | .ok o => IO.println s!"opened {o.mask.length}"; return 0
      | .error reason => IO.println s!"refused {((toString (repr reason)).splitOn ".").getLast!}"; return 1
  | _ => throw (IO.userError "usage: record D E CLASS N ROOTS MASK SALT | open PAYLOADHEX OPENINGHEX")
