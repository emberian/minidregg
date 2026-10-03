import Compiler.BendInvocation
import Compiler.BendProofBytes

/- Two CLOSED public-semantic disclosure profiles. These are pure projection
and opening relations, not authority tokens or proof admission. The kernel
must retain actual source/current-law/input/observer admission before selecting
one. Hidden-code profiles are deliberately absent. -/
namespace Minidregg.Compiler.BendProofProjection
open Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Tower256ConcreteBackend
set_option autoImplicit false

inductive Policy where
  | privateEffects
  | publicEffects
  deriving DecidableEq, Repr

def Policy.name : Policy → String
  | .privateEffects => "public-semantic/private-input-result-v1"
  | .publicEffects => "public-semantic/public-effects-private-returns-v1"

def Policy.id (policy : Policy) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.DISCLOSURE-PROFILE/v1".toUTF8.toList
    policy.name.toUTF8.toList).digest

def policyStream : StreamCodec Policy :=
  StreamCodec.xmap StreamCodec.bool
    (fun p => match p with | .privateEffects => false | .publicEffects => true)
    (fun b => if b then .publicEffects else .privateEffects)
    (by intro p; cases p <;> rfl)

/-- Public context fixed independently by admitted invocation and disclosure
law. Generation, epoch and audience identify a release context; they never
replace the current recipient's separate release authorization. -/
structure Context where
  policy : Policy
  definition : BendInvocation.ProgramIdentity
  invocation : Digest
  profile : Digest
  generation : Nat
  keyEpoch : Digest
  audience : Digest
  tariff : Digest
  capacity : List Nat
  deriving DecidableEq, Repr

def contextStream : StreamCodec Context :=
  StreamCodec.xmap (StreamCodec.product policyStream
    (StreamCodec.product BendInvocation.programStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.list StreamCodec.nat)))))))))
    (fun c => (c.policy, c.definition, c.invocation, c.profile, c.generation,
      c.keyEpoch, c.audience, c.tariff, c.capacity))
    (fun c => ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1,
      c.2.2.2.2.2.1, c.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.1,
      c.2.2.2.2.2.2.2.2⟩)
    (by intro c; cases c; rfl)

structure Coins where
  input : List UInt8
  effects : List UInt8
  returns : List UInt8
  statement : List UInt8
  deriving DecidableEq, Repr

/-- Length is structural only. Fresh unpredictable independent coins require
the actual entropy producer; this predicate cannot certify randomness. -/
def Coins.shape (coins : Coins) : Prop :=
  coins.input.length = 32 ∧ coins.effects.length = 32 ∧
  coins.returns.length = 32 ∧ coins.statement.length = 32

/-- Randomized domain-separated commitment candidate. Binding/hiding and
arithmetization of this exact hash remain explicit backend obligations. Never
replace this with an unsalted hash of low-entropy data. -/
def commit (domain : String) (context : Context) (coins payload : List UInt8) : Digest :=
  (Sp800185Cshake256.hash domain.toUTF8.toList
    ((StreamCodec.product contextStream
      (StreamCodec.product bytesStream bytesStream)).encode (context, coins, payload))).digest

structure Public where
  context : Context
  inputCommitment : Digest
  effectsCommitment : Digest
  returnsCommitment : Digest
  statementCommitment : Digest
  /-- Empty in privateEffects; exact ordered actual effects in publicEffects.
  The latter requires current native disclosure authorization for those effects. -/
  revealedEffects : List BendWorldPlan.Effect
  deriving DecidableEq, Repr

def publicStream : StreamCodec Public :=
  StreamCodec.xmap (StreamCodec.product contextStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.list BendWorldPlan.effectStream))))))
    (fun p => (p.context, p.inputCommitment, p.effectsCommitment,
      p.returnsCommitment, p.statementCommitment, p.revealedEffects))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)
    (by intro p; cases p; rfl)

def frame : List UInt8 := "DREGG/BEND/PUBLIC-PROJECTION/v1".toUTF8.toList
def encode (statement : Public) : List UInt8 := frame ++ publicStream.encode statement
def decode (bytes : List UInt8) : Option Public :=
  NockProgramCodec.framedDecode frame publicStream bytes

def publicFields (statement : Public) : List BabyBear := BendProofBytes.fields (encode statement)

def expectedContext (policy : Policy) (artifact : BendWorldProgramCodec.Artifact)
    (result : BendInvocation.Result) : Context :=
  ⟨policy, result.definition, result.execution.invocation,
    BendWorldProgramCodec.profileId artifact.profile, result.result.generation,
    result.result.keyEpoch, result.result.audience,
    result.execution.tariff, result.execution.capacity⟩

/-- Pure producer. `inputBytes` must be the exact admitted canonical input
encoding, supplied by Kernel.BendInvocationInput; accepting arbitrary bytes
here does not mint its checked provenance. No private trace count is exposed. -/
def project (policy : Policy) (artifact : BendWorldProgramCodec.Artifact)
    (result : BendInvocation.Result) (inputBytes : List UInt8) (coins : Coins) : Public :=
  let context := expectedContext policy artifact result
  { context
    inputCommitment := commit "DREGG.BEND.INPUT-COMMIT/v1" context coins.input inputBytes
    effectsCommitment := commit "DREGG.BEND.EFFECT-COMMIT/v1" context coins.effects
      ((StreamCodec.list BendWorldPlan.effectStream).encode result.effects)
    returnsCommitment := commit "DREGG.BEND.RETURN-COMMIT/v1" context coins.returns
      (BendWorldPlan.encodeReturn result.result)
    statementCommitment := commit "DREGG.BEND.STATEMENT-COMMIT/v1" context coins.statement
      (BendInvocation.encode result)
    revealedEffects := match policy with | .privateEffects => [] | .publicEffects => result.effects }

/-- Exact PRIVATE opening relation. It does not imply native current-law,
input provenance, source execution, PCS soundness or computational hiding.
The real proof circuit must constrain these equalities and those joins. -/
def Opens (policy : Policy) (artifact : BendWorldProgramCodec.Artifact)
    (result : BendInvocation.Result) (admittedInputBytes : List UInt8)
    (coins : Coins) (statement : Public) : Prop :=
  BendInvocation.matchesArtifact result artifact = true ∧
  artifact.profile.disclosure = policy.id ∧ coins.shape ∧
  statement = project policy artifact result admittedInputBytes coins

theorem private_effects_absent (artifact : BendWorldProgramCodec.Artifact)
    (result : BendInvocation.Result) (input : List UInt8) (coins : Coins) :
    (project .privateEffects artifact result input coins).revealedEffects = [] := rfl

theorem public_effects_exact (artifact : BendWorldProgramCodec.Artifact)
    (result : BendInvocation.Result) (input : List UInt8) (coins : Coins) :
    (project .publicEffects artifact result input coins).revealedEffects = result.effects := rfl

theorem roundtrip (statement : Public) : decode (encode statement) = some statement :=
  NockProgramCodec.framedDecode_encode frame publicStream statement

theorem canonical {bytes : List UInt8} {statement : Public}
    (parsed : decode bytes = some statement) : encode statement = bytes :=
  NockProgramCodec.framedDecode_canonical parsed

theorem publicFields_injective : Function.Injective publicFields := by
  intro left right same
  have bytes := BendProofBytes.fields_injective same
  have parsed := congrArg decode bytes
  simpa only [roundtrip, Option.some.injEq] using parsed

#assert_axioms private_effects_absent
#assert_axioms public_effects_exact
#assert_axioms roundtrip
#assert_axioms canonical
#assert_axioms publicFields_injective
end Minidregg.Compiler.BendProofProjection
