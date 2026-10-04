/-
# `Kernel.GenericSimplexReconfig` — reconfiguration of Generic Simplex, statement first

Generic Simplex (`Kernel.GenericSimplex`) runs a FIXED committee, `n = 3f+1`
(`docs/GENERIC-SIMPLEX-NATIVE.md`: "Changing membership … [is] separate work"). This module states
the reconfiguration discipline Bread's 2026-08-08 reading docs extracted from the literature,
against the engine's real types: `GenericSimplexCodec.Context` (scope, `epoch`, instance,
`Config`, public keys), `Certificate`, `commitmentBytes`, and `Kernel.GenericSimplex.Block`
(exact ancestry: a block's length is its height). Nothing here changes the engine; W1.7 owns
`Kernel/GenericSimplex*.lean`, and this file must be re-pointed at its intake when that lands.

Sources (READ): breadstuffs `docs/reference/FEDERATION-DESIGN-GAPS-2026-08-08.md` §0 ("a
configuration number, an install point determined by a certificate rather than by local time, and a
rule that a new member does not count until it has the state"), `DYNAMIC-COMMITTEE-LITERATURE`
(Dyno/DZ §III–VI and Lemma C.9, Rondo §IV, LPR §15.3, Pastro §5), `FLUID-MEMBERSHIP`,
`READING-BLOCKLACE`; Mini `docs/GENERIC-SIMPLEX-NATIVE.md` ("Reconfiguration must preserve existing
liabilities; a fresh file or epoch number is not proof that old certificates cannot complete").

The four rules, each with definitions, statements, the inhabitant of its premises, and the
test schedule that would refute it:

1. **Configuration number** = `Context.epoch`. `commitmentBytes_binds_config` (PROVED): the
   signed COMMIT preimage binds context (hence epoch), view and block. `EpochChain` (STATED): each
   install increments the number by exactly one.
2. **Certificate-determined install point** = the height of the FIRST reconfiguration command in a
   block certified by a full COMMIT certificate of the old configuration.
   `installPoint_certificate_determined` (PROVED from the stated premise `CommitAgreement`): two
   certified blocks of one configuration that both carry a command agree on the install point.
3. **A new member counts only once it holds the state.** `countReady` counts a new-configuration
   signer only with readiness evidence extending the install block; `unready_signer_not_counted`
   (PROVED). `ReadinessSafety` (STATED, DZ Lemma C.9). `growth_needs_readiness` (PROVED): under
   Mini's `n = 3f+1` shape, EVERY committee growth exceeds the no-state-transfer churn bound, so
   the readiness rule is mandatory, not an optimization.
4. **Old-certificate liability.** `acceptsAt` accepts a certificate only under the configuration in
   force at its height. `stale_certificate_refused` and `liability_retained_below_install`
   (PROVED, one-install history): an old-configuration certificate above the install point is
   refused; one at or below it stays valid. `naive_acceptor_admits_fork` (PROVED): the
   "quorum from any historical committee" acceptor admits two conflicting certificates at the same
   height. `OldKeysErased` (STATED, Pastro §5) is the residual a height-bound verifier cannot close
   for a slow reader that does not yet hold the install certificate.
-/
import Compiler.GenericSimplexCodec
import Theory.AxiomPin

namespace Minidregg.Kernel.GenericSimplexReconfig

open Minidregg.Kernel.GenericSimplex
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

/-! ## 1. Configuration number -/

/-- The configuration number of a committee context. -/
def configNumber (c : Context) : Nat := c.epoch

theorem streamEncode_injective {α : Type} (codec : StreamCodec α) :
    Function.Injective codec.encode := by
  intro a b same
  have decoded := congrArg codec.toLawful.decode same
  have left := codec.toLawful.decode_encode a
  have right := codec.toLawful.decode_encode b
  change codec.toLawful.decode (codec.encode a) = some a at left
  change codec.toLawful.decode (codec.encode b) = some b at right
  rw [left, right] at decoded
  exact Option.some.inj decoded

/-- **The signed COMMIT statement names its configuration.** Equal signed preimages have equal
context (hence equal configuration number), view and block: a COMMIT signature can never be
counted under a configuration other than the one it was made in. (FDG:195 "A vote must name the
configuration it is a vote in"; Mini already puts it inside the signed preimage.) -/
theorem commitmentBytes_binds_config {c c' : Context} {v v' : Nat} {b b' : Block}
    (h : commitmentBytes c v b = commitmentBytes c' v' b') :
    c = c' ∧ v = v' ∧ b = b' := by
  unfold commitmentBytes at h
  have h2 := List.append_cancel_left h
  have h3 := streamEncode_injective
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat blockStream)) h2
  simp only [Prod.mk.injEq] at h3
  exact ⟨h3.1, h3.2.1, h3.2.2⟩

theorem commitmentBytes_binds_configNumber {c c' : Context} {v v' : Nat} {b b' : Block}
    (h : commitmentBytes c v b = commitmentBytes c' v' b') : configNumber c = configNumber c' := by
  rw [(commitmentBytes_binds_config h).1]

/-! ## 2. The certificate-determined install point -/

/-- Domain tag of a reconfiguration command payload ("MINI-RECONFIG", version 1). -/
def reconfigTag : Bytes := [77, 73, 78, 73, 45, 82, 69, 67, 79, 78, 70, 73, 71, 1]

/-- The reconfiguration command installing `next`. -/
def reconfigPayload (next : Context) : Bytes := reconfigTag ++ contextStream.encode next

/-- Is this payload a reconfiguration command? -/
def isReconfig (payload : Bytes) : Bool := payload.take reconfigTag.length == reconfigTag

theorem reconfigPayload_isReconfig (next : Context) : isReconfig (reconfigPayload next) = true := by
  simp [isReconfig, reconfigPayload]

/-- The install point a block determines: the height (1-based) of its first reconfiguration
command, if any. -/
def installPoint? (b : Block) : Option Nat := (b.findIdx? isReconfig).map (· + 1)

/-- The install point is stable under extension: once a certified prefix carries a command, every
extension reports the same install point. -/
theorem installPoint_extend {b₁ b₂ : Block} (hp : b₁ <+: b₂) {h : Nat}
    (hb : installPoint? b₁ = some h) : installPoint? b₂ = some h := by
  obtain ⟨t, rfl⟩ := hp
  unfold installPoint? at *
  rw [List.findIdx?_append]
  cases hf : b₁.findIdx? isReconfig with
  | none => simp [hf] at hb
  | some i => simpa [hf] using hb

/-- **Premise (Simplex agreement, per configuration).** Any two blocks certified by accepted COMMIT
certificates of one configuration are prefix-comparable. This is the engine's safety property; it
is a premise here. Inhabitant: any single certified block (`commitAgreement_singleton`). -/
def CommitAgreement (certified : Block → Prop) : Prop :=
  ∀ b₁ b₂, certified b₁ → certified b₂ → b₁ <+: b₂ ∨ b₂ <+: b₁

theorem commitAgreement_singleton (b : Block) : CommitAgreement (fun x => x = b) := by
  intro b₁ b₂ h₁ h₂; subst h₁; subst h₂; exact Or.inl (List.prefix_refl _)

/-- **The install point is determined by certificates, not local time.** Under agreement, two
certified blocks that both carry a reconfiguration command report the SAME install point. Refuting
schedule (LPR fn. 51): two candidate boundary blocks each gathering a partial certificate — the
premise `CommitAgreement` then fails, which is exactly what the four-node harness must never
exhibit for full certificates. -/
theorem installPoint_certificate_determined {certified : Block → Prop}
    (hagree : CommitAgreement certified) {b₁ b₂ : Block} (h₁ : certified b₁) (h₂ : certified b₂)
    {i₁ i₂ : Nat} (hi₁ : installPoint? b₁ = some i₁) (hi₂ : installPoint? b₂ = some i₂) :
    i₁ = i₂ := by
  rcases hagree b₁ b₂ h₁ h₂ with hp | hp
  · rw [installPoint_extend hp hi₁] at hi₂; exact Option.some.inj hi₂
  · rw [installPoint_extend hp hi₂] at hi₁; exact (Option.some.inj hi₁).symm

/-- One installation: a full COMMIT certificate of the old configuration whose block carries, at
its install point, the command for the next configuration. -/
structure Install where
  certificate : Certificate
  next : Context
  height : Nat

/-- Structural validity of one installation from configuration `old`. The signature check is the
IO layer's (`GenericSimplexIO.verifyCertificate`); this states what that check does not. -/
def Install.Valid (old : Context) (i : Install) : Prop :=
  i.certificate.context = old ∧
    installPoint? i.certificate.block = some i.height ∧
    i.certificate.block[i.height - 1]? = some (reconfigPayload i.next) ∧
    configNumber i.next = configNumber old + 1

/-- **Stated: the configuration number increments by exactly one along the install chain.** -/
def EpochChain : Context → List Install → Prop
  | _, [] => True
  | old, i :: rest => i.Valid old ∧ EpochChain i.next rest

/-- The configuration in force at a height: blocks at or below an install point are certified by
the old configuration; blocks above it by the new one. -/
def configAt : Context → List Install → Nat → Context
  | g, [], _ => g
  | g, i :: rest, h => if h ≤ i.height then g else configAt i.next rest h

/-! ## 4. Old-certificate liability (proved for one installation) -/

/-- **The height-bound verifier rule.** Accept a certificate only under the configuration in force
at its certified height. -/
def acceptsAt (g : Context) (hist : List Install) (cert : Certificate) : Bool :=
  decide (cert.context = configAt g hist cert.block.length)

/-- **An old-configuration certificate above the install point is refused.** Refuting schedule
(GSN:36-37 + Pastro §5): after the install at `h*`, `f+1` retired config-`k` members (keys not
erased) complete a config-`k` COMMIT for a block of height `h*+1`; a verifier holding the install
certificate must refuse it. -/
theorem stale_certificate_refused (g : Context) (i : Install) (hv : i.Valid g)
    (cert : Certificate) (hold : cert.context = g) (habove : i.height < cert.block.length) :
    acceptsAt g [i] cert = false := by
  unfold acceptsAt configAt
  rw [if_neg (by omega)]
  simp only [configAt, hold]
  have hne : g ≠ i.next := by
    intro heq
    have := hv.2.2.2
    rw [← heq] at this
    unfold configNumber at this
    omega
  simpa using hne

/-- **Liabilities are retained.** An old-configuration certificate at or below the install point is
still accepted: reconfiguration does not erase what the old committee already certified. -/
theorem liability_retained_below_install (g : Context) (i : Install) (cert : Certificate)
    (hold : cert.context = g) (hbelow : cert.block.length ≤ i.height) :
    acceptsAt g [i] cert = true := by
  unfold acceptsAt configAt
  rw [if_pos hbelow]
  simp [hold]

/-- The new configuration is accepted above the install point. -/
theorem new_configuration_accepted_above (g : Context) (i : Install) (cert : Certificate)
    (hnew : cert.context = i.next) (habove : i.height < cert.block.length) :
    acceptsAt g [i] cert = true := by
  unfold acceptsAt configAt
  rw [if_neg (by omega)]
  simp [configAt, hnew]

/-- The acceptor this rule replaces: a quorum from ANY historical committee (FDG:238 "to be
deleted, not kept alongside"). -/
def acceptsAnyHistorical (g : Context) (hist : List Install) (cert : Certificate) : Bool :=
  decide (cert.context = g) || hist.any (fun i => decide (cert.context = i.next))

/-- A concrete one-install history for the fork witness. -/
def forkOld : Context :=
  { scope := [1], epoch := 0, instanceBytes := [2],
    config := { parties := 4, faults := 1, timeout := 1 }, publicKeys := [] }
def forkNew : Context :=
  { scope := [1], epoch := 1, instanceBytes := [2],
    config := { parties := 4, faults := 1, timeout := 1 }, publicKeys := [] }
def forkInstallCert : Certificate :=
  { context := forkOld, view := 1, block := [reconfigPayload forkNew], signers := [] }
def forkInstall : Install :=
  { certificate := forkInstallCert, next := forkNew, height := 1 }
def forkOldCert : Certificate :=
  { context := forkOld, view := 2, block := [reconfigPayload forkNew, [5]], signers := [] }
def forkNewCert : Certificate :=
  { context := forkNew, view := 2, block := [reconfigPayload forkNew, [6]], signers := [] }

theorem forkInstall_valid : forkInstall.Valid forkOld := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · simp [forkInstall, forkInstallCert, installPoint?, reconfigPayload_isReconfig]
  · rfl

/-- **The historical acceptor admits a fork; the height-bound rule does not.** Two certificates at
the same height 2 with conflicting tips, one from the retired configuration, one from the new: the
naive acceptor takes both, `acceptsAt` refuses the stale one. -/
theorem naive_acceptor_admits_fork :
    acceptsAnyHistorical forkOld [forkInstall] forkOldCert = true ∧
      acceptsAnyHistorical forkOld [forkInstall] forkNewCert = true ∧
      forkOldCert.block.length = forkNewCert.block.length ∧
      forkOldCert.block ≠ forkNewCert.block ∧
      acceptsAt forkOld [forkInstall] forkOldCert = false ∧
      acceptsAt forkOld [forkInstall] forkNewCert = true := by
  refine ⟨by simp [acceptsAnyHistorical, forkOldCert], by simp [acceptsAnyHistorical, forkNewCert,
    forkInstall], rfl, by simp [forkOldCert, forkNewCert], ?_, ?_⟩
  · exact stale_certificate_refused forkOld forkInstall forkInstall_valid forkOldCert rfl
      (by simp [forkOldCert, forkInstall])
  · exact new_configuration_accepted_above forkOld forkInstall forkNewCert rfl
      (by simp [forkNewCert, forkInstall])

/-- **Stated (Pastro §5): old keys are erased at install.** Before configuration `k+1` installs, a
quorum of configuration `k` has destroyed the signing keys of `k`, so no new config-`k` signature
can form above the install point. `stale_certificate_refused` protects every verifier that holds
the install certificate; this premise is what protects a slow reader that does not. Inhabitant:
the empty set of post-install old-key signatures. Refuting schedule: the fork above, delivered to a
replica that has not yet received `forkInstall`. -/
def OldKeysErased (old : Context) (installHeight : Nat) (signedAfter : List Certificate) : Prop :=
  ∀ c ∈ signedAfter, c.context = old → c.block.length ≤ installHeight

theorem oldKeysErased_inhabited (old : Context) (h : Nat) : OldKeysErased old h [] := by
  intro c hc; simp at hc

/-! ## 3. A new member counts only once it holds the state -/

/-- Readiness evidence: the committed prefix each member attests to hold (its signature over that
attestation is the IO layer's). -/
abbrev Readiness := Nat → Option Block

/-- Does this member's evidence extend the install block? -/
def readyFor (i : Install) (ready : Readiness) (member : Nat) : Bool :=
  match ready member with
  | some b => i.certificate.block.isPrefixOf b
  | none => false

/-- New-configuration signers that count: only ready ones, each once. -/
def countReady (i : Install) (ready : Readiness) (signers : List Nat) : Nat :=
  ((signers.filter (readyFor i ready)).eraseDups).length

/-- **A signer without state does not count.** Appending a vote from a member whose readiness
evidence does not extend the install block leaves the count unchanged. Refuting schedule (DZ
Lemma C.9): a joiner that has not completed state transfer signs `m′` conflicting with a committed
`m`; if its signature raised the count, the quorum-intersection argument loses a member. -/
theorem unready_signer_not_counted (i : Install) (ready : Readiness) (signers : List Nat)
    (m : Nat) (hm : readyFor i ready m = false) :
    countReady i ready (signers ++ [m]) = countReady i ready signers := by
  unfold countReady
  rw [List.filter_append]
  simp [hm]

/-- The readiness premise is inhabited: every member holds the install block itself. -/
theorem readyFor_install_block (i : Install) (m : Nat) :
    readyFor i (fun _ => some i.certificate.block) m = true := by
  simp [readyFor, List.isPrefixOf_iff_prefix]

/-- **Stated (DZ Lemma C.9): with readiness enforced, every block the new configuration commits
extends the install block.** `certifiedNew b signers` = `b` gathered the listed new-configuration
signers. Test schedule: in the four-node harness with one install, every committed block above the
install point must have the install block as prefix; refuted by any committed config-`k+1` block
that does not. -/
def ReadinessSafety (i : Install) (ready : Readiness)
    (certifiedNew : Block → List Nat → Prop) : Prop :=
  ∀ b signers, certifiedNew b signers →
    i.next.config.quorum ≤ countReady i ready signers → i.certificate.block <+: b

/-- The no-state-transfer churn bound (DZ §III.D, derived in DYNAMIC-COMMITTEE-LITERATURE:217-241):
an old quorum and a new quorum, from an old committee of `n` growing to `n'`, share at least
`(n−f) + (n'−f') − (n'−n) − n` old members; safety without readiness needs that to exceed `f'`. -/
def ChurnSafe (n f n' f' : Nat) : Prop :=
  (f' : Int) < ((n : Int) - f) + ((n' : Int) - f') - ((n' : Int) - n) - n

/-- The doc's counterexample, in Mini's quorum rule: `4 → 7` is unsafe without readiness. -/
theorem four_to_seven_unsafe : ¬ ChurnSafe 4 1 7 2 := by
  unfold ChurnSafe; omega

/-- **Under Mini's `n = 3f+1` shape every growth needs the readiness rule.** The smallest growth,
`3f+1 → 3(f+1)+1`, already fails the no-state-transfer bound for every `f`: the overlap is `f`
against a new fault bound `f+1`. -/
theorem growth_needs_readiness (f : Nat) : ¬ ChurnSafe (3 * f + 1) f (3 * (f + 1) + 1) (f + 1) := by
  unfold ChurnSafe; push_cast; omega

/-- …and a same-size committee with no joiners is trivially safe (the fixed-committee engine). -/
theorem fixed_committee_churn_safe (f : Nat) : ChurnSafe (3 * f + 1) f (3 * f + 1) f := by
  unfold ChurnSafe; push_cast; omega

#assert_axioms streamEncode_injective
#assert_axioms commitmentBytes_binds_config
#assert_axioms commitmentBytes_binds_configNumber
#assert_axioms reconfigPayload_isReconfig
#assert_axioms installPoint_extend
#assert_axioms commitAgreement_singleton
#assert_axioms installPoint_certificate_determined
#assert_axioms stale_certificate_refused
#assert_axioms liability_retained_below_install
#assert_axioms new_configuration_accepted_above
#assert_axioms forkInstall_valid
#assert_axioms naive_acceptor_admits_fork
#assert_axioms oldKeysErased_inhabited
#assert_axioms unready_signer_not_counted
#assert_axioms readyFor_install_block
#assert_axioms four_to_seven_unsafe
#assert_axioms growth_needs_readiness
#assert_axioms fixed_committee_churn_safe

end Minidregg.Kernel.GenericSimplexReconfig
