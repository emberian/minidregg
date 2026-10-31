/-
# Compiler.Tower256Backend -- the profile-bound half of the shared Tower256 backend

`backend : Backend (binaryTower 8)` pairs the shared cSHAKE/Merkle/transcript domains of
`Compiler.Tower256ConcreteBackend` with `BinaryTower256Profile.profile`, the Fan--Paar
GF(2^256) field profile.  It is split from the codec half because the profile's carrier
is `GaloisField 2 (2 ^ 8)`: naming it imports Mathlib's finite-field, splitting-field and
adjoin-root theory.  The host's wire codecs, pins and digest domains need none of that, so
they stay in `Compiler.Tower256ConcreteBackend`, and only the proof controllers built on
the field-typed backend import this module.  The declarations keep the
`Minidregg.Compiler.Tower256ConcreteBackend` namespace: their full names are unchanged.
-/

module

public import Compiler.Tower256ConcreteBackend
public import Compiler.BinaryTower256Profile
meta import Compiler.Tower256ConcreteBackend
meta import Compiler.BinaryTower256Profile

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
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

namespace Minidregg.Compiler.Tower256ConcreteBackend

open Minidregg.Compiler.Tower256CshakeMerkleController

set_option autoImplicit false

noncomputable def backend : Backend BinaryTower256Profile.Tower256 where
  tower := BinaryTower256Profile.profile
  cshake := cshake
  merkle := merkleDomains
  transcript := transcriptDomains

theorem towerExact : backend.tower = BinaryTower256Profile.profile := rfl

theorem cshakeExact : backend.cshake =
    Sp800185Cshake256.controller cshakeAlgorithmId digestCodecPin := rfl

theorem cshakeAlgorithmExact : backend.cshake.algorithmId = cshakeAlgorithmId := rfl

theorem digestCodecPinExact :
    backend.cshake.digestCodecPin = digestCodecPin := rfl

theorem merkleSuiteExact : backend.merkle.suiteId = merkleSuiteId := rfl

theorem merkleCodecPinExact :
    backend.merkle.proofCodecPin = merklePathCodecPin := rfl

theorem merkleCodecExact : backend.merkle.proofCodec = merklePathCodec := rfl

theorem merkleDomainsExact :
    backend.merkle.leafCustomization = leafCustomization ∧
    backend.merkle.nodeCustomization = nodeCustomization := ⟨rfl, rfl⟩

theorem transcriptCodecsExact :
    backend.transcript.frameCodec = globalFrameCodec ∧
    backend.transcript.labelCodec = globalDrawLabelCodec := ⟨rfl, rfl⟩

theorem transcriptDomainsExact :
    backend.transcript.absorbDomain = absorbDomain ∧
    backend.transcript.squeezeDomain = squeezeDomain ∧
    backend.transcript.drawFrameTag = drawFrameTag := ⟨rfl, rfl, rfl⟩

theorem cshakeOutputExact (customization input : List UInt8) :
    backend.cshake.digestCodec.encode
        (backend.cshake.xofDigest customization input) =
      (Sp800185Cshake256.hash customization input).bytes :=
  Sp800185Cshake256.controller_digest_encode_exact
    cshakeAlgorithmId digestCodecPin customization input

/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.towerExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms towerExact
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.cshakeExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cshakeExact
/-- info: 'Minidregg.Compiler.Tower256ConcreteBackend.cshakeOutputExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cshakeOutputExact

end Minidregg.Compiler.Tower256ConcreteBackend
