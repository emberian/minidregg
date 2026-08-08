/-
# `Compiler/FiatShamirAir.lean` — [RECURSE-verifier]: the Fiat–Shamir challenge binding —
the recursive verifier's challenges are hashes, not choices

**Substrate, said out loud: this is Lean-AUTHORED AIR.** Every constraint below is AirHash's
`hashTerm` — a `Term (AirSig F Idx)` built from the DSL surface, read through the one fold —
composed as a `ConstraintSystem`; its meaning comes from `hashTerm_correct` (itself rung 1's
initiality). NO check is hand-authored outside the DSL: no Rust, no bespoke `air_accepts`,
no parallel executor. The gadget is BUILT FROM AirHash — `hashTerm`/`hashExec` consumed,
never re-derived.

## What is arithmetized

The landed verifier gadgets (`sumcheckVerifierGadget`, `friQueryVerifierAir`) take their
challenges (`chal i`, `beta k`) as FREE input wires — deliberately, with the binding named
as remaining `[RECURSE-verifier]` mass. A verifier whose challenges are free is not a
verifier: a prover who picks the challenges AFTER the messages forges transcripts at will
(§5 exhibits exactly that attack passing the free-challenge pair). This file closes that
door — Fiat–Shamir IN-CIRCUIT:

* `fsChainVal` — the absorb–squeeze chain, executor side: squeeze 0 is the hash of the
  first transcript block; squeeze `k+1` is the hash of (squeeze `k` ∥ block `k+1`'s fresh
  slots) — replacement chaining, the running state occupying rate slot 0. Squeeze `k`
  therefore reads EVERY prior block: it is a hash of the whole transcript prefix.
* `fsBindingGadget` — one `hashTerm` per squeeze step, asserting
  `challenge k ≐ hash(prev challenge ∥ fresh transcript wires)`; the state input is the
  PREVIOUS CHALLENGE WIRE by wire-sharing — the same composition mechanism that chains FRI
  rounds (`FriQueryVerifierAir` §5) — so the chain is carried by the wires themselves.
* `fsBinding_correct` — the keystone iff: the system accepts IFF every challenge wire
  carries EXACTLY the chain hash of its transcript prefix (`FsBound`, statement-first).
  The equivalence between the ROUND-LOCAL equations (each `hashTerm`'s meaning) and the
  GLOBAL chain statement is the file's one induction.
* `boundVerifier` — `fsBindingGadget ++ sumcheckVerifierGadget ++ friQueryVerifierGadget`
  as ONE system; `boundVerifier_correct`: accepts iff (challenges FS-bound) ∧ (sumcheck
  verifier accepts) ∧ (FRI query verifier accepts). With the challenge wires SHARED
  (`chal i`/`beta k` ARE squeeze wires — `boundVerifier_challenges_bound`, and the §5 demo
  instantiates it), the challenges are NOT free: the composed AIR is a SELF-CONTAINED
  non-interactive verifier. A satisfying assignment IS a transcript whose challenges were
  derived, not chosen.

## The Loom correspondence (prose, boundary-honest)

`Compiler` may not import `Loom` (`Theory`-boundary law), so the correspondence is stated
at matching shape: `FsBound` is the in-circuit form of Loom's Fiat–Shamir challenge
derivation — the challenge at round `k` is a deterministic hash of the transcript prefix,
the object `[LC-fs-adaptive]`'s grinding bound quantifies over (the adversary retries the
HASH, it cannot pick the challenge). `[RECURSE-fs-bridge]` — the machine-checked
identification (`FsBound` ⟺ Loom's FS transcript relation, through the sponge
representation), statable only Assurance-side — is the named residual, exactly like
`[RECURSE-sumcheck-bridge]`/`[RECURSE-fri-bridge]`.

## Honest scope — floors and residuals, none smuggled

* `[FS-oracle]` FLOOR: that hash-bound challenges yield a SOUND non-interactive proof
  (soundness error ≈ interactive error × query count) is a cryptographic assumption about
  the instantiated permutation (random-oracle-style; `[COMMIT-CR]`'s sibling). Every
  theorem here is about what the constraints FORCE, not about hardness.
* `[RECURSE-fs-sponge]` RESIDUAL: deployed sponge mode — rate/capacity split (the demo
  chains with capacity 0 through the squeezed element), padding, domain separation, and
  the deployed Poseidon2 parameters (`[AIR-poseidon-params]` inherited). The STRUCTURE
  (chained absorb, one block per squeeze; multi-slot absorption = several chain steps
  between squeezes, exercised in §5's demo where 2 of 5 squeezes are internal state) is
  closed here; the deployed layout is instantiation.
* `[RECURSE-merkle-bind]` RESIDUAL — the remaining composition piece: binding the OPENED
  wires (`lo k`/`hi k`/`next k`, sumcheck's `finalW`) and the absorbed commitment roots to
  Merkle openings via AirMembership's `membershipGadget` (same `++` and wire-sharing, the
  vocabulary already landed), plus `twoX k` to the query index's domain point. Until then
  those wires' CONSISTENCY is constrained but their PROVENANCE is not.

## The recursion point

`boundVerifier` is a `ConstraintSystem`, so the verified emit path applies verbatim —
`emit_accepts_iff_fin` is consumed on the composed demo in §6. **"The FS-bound verifier
accepted" is itself an emitted, Loom-provable statement**: a Loom proof of THAT statement
is a proof that a non-interactive proof verified — the recursive apex, now with no free
challenge wires. With `[RECURSE-merkle-bind]` closed the emitted system is the whole
self-contained light-client verifier.

## Statement-first (ATLAS fields)

* `FsBound` — the binding as a `Prop`, stated BEFORE the gadget. Satisfiable: honest
  transcripts with genuinely-derived challenges accept (§5, decided, ZMod 7 and the
  composed ZMod 13 demo). Teeth: a FORGED challenge — chosen to make the free-challenge
  verifiers pass — is REJECTED by the binding alone, with machine-checked attribution to
  the exact violated `hashTerm`; over ZMod 7 the challenge wires are FULLY DETERMINED
  (quantified iff over all 49 assignments). Premise-inhabitation: `fsBinding_complete`
  builds the accepting assignment for EVERY transcript.
-/
import Compiler.FriQueryVerifierAir

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u} {w s n rounds : ℕ}

/-! ## §1. The semantic spec, statement-first — the absorb–squeeze chain as an executor. -/

/-- **The Fiat–Shamir chain, executor side.** `blk k` is round `k`'s transcript block
(values); squeeze 0 hashes block 0 directly, squeeze `k+1` hashes block `k+1` with the
PREVIOUS squeeze overlaid on slot 0 (replacement chaining — the running state occupies the
first slot, so slot 0 of blocks ≥ 1 is superseded). Squeeze `k` reads every block `≤ k`:
it is a hash of the whole transcript prefix. -/
def fsChainVal [NeZero w] (spec : PermSpec F w) (blk : ℕ → Fin w → F) : ℕ → F
  | 0 => hashExec spec (blk 0)
  | k + 1 => hashExec spec fun i =>
      if (i : ℕ) = 0 then fsChainVal spec blk k else blk (k + 1) i

/-- The transcript wire VALUES under an assignment, junk-extended past the horizon (the
chain at `k < n` never reads a block `≥ n` — `chalOf`'s junk pattern). -/
def transcriptVals (asg : Idx → F) (transcript : Fin n → Fin w → Idx) : ℕ → Fin w → F :=
  fun m i => if h : m < n then asg (transcript ⟨m, h⟩ i) else 0

/-- **The Fiat–Shamir binding, statement-first.** Every challenge equals the chain hash of
its transcript prefix — the challenges are DERIVED, not chosen. This is the in-circuit form
of Loom's FS challenge derivation; the machine-checked identification is
`[RECURSE-fs-bridge]`. -/
def FsBound [NeZero w] (spec : PermSpec F w) (blk : ℕ → Fin w → F)
    (chalv : Fin n → F) : Prop :=
  ∀ k : Fin n, chalv k = fsChainVal spec blk k.val

/-! ## §2. The gadget — one `hashTerm` per squeeze, the chain carried by wire-sharing. -/

/-- Round `k`'s absorb block, as WIRES: slot 0 of rounds ≥ 1 is the PREVIOUS CHALLENGE
WIRE (wire-sharing carries the chain state; the corresponding transcript slot is
superseded — `fsChainVal` mirrors this exactly); everything else is round `k`'s transcript
wires. -/
def fsNote (transcript : Fin n → Fin w → Idx) (challenge : Fin n → Idx)
    (k : Fin n) (i : Fin w) : Idx :=
  if 0 < (k : ℕ) ∧ (i : ℕ) = 0 then
    challenge ⟨(k : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
  else transcript k i

/-- **The Fiat–Shamir binding gadget**: per squeeze step one `hashTerm` (AirHash's, reused
verbatim) asserting `challenge k ≐ hash(fsNote k)` — the challenge wires are FORCED to the
absorb–squeeze chain of the transcript wires. A `ConstraintSystem`, so the emit path
applies verbatim (§6). -/
def fsBindingGadget [NeZero w] (spec : PermSpec F w)
    (transcript : Fin n → Fin w → Idx) (challenge : Fin n → Idx) :
    ConstraintSystem F Idx :=
  (List.finRange n).map fun k =>
    hashTerm spec (challenge k) (fsNote transcript challenge k)

/-! ## §3. The keystone iff — round-local hash equations ⟺ the global chain. -/

private theorem fsNote_zero_vals (asg : Idx → F) (transcript : Fin n → Fin w → Idx)
    (challenge : Fin n → Idx) (hm : 0 < n) :
    (fun i => asg (fsNote transcript challenge ⟨0, hm⟩ i))
      = transcriptVals asg transcript 0 := by
  funext i
  simp [fsNote, transcriptVals, hm]

private theorem fsNote_succ_vals (asg : Idx → F) (transcript : Fin n → Fin w → Idx)
    (challenge : Fin n → Idx) {p : ℕ} (hm : p + 1 < n) (hp : p < n) :
    (fun i => asg (fsNote transcript challenge ⟨p + 1, hm⟩ i))
      = fun i : Fin w => if (i : ℕ) = 0 then asg (challenge ⟨p, hp⟩)
          else transcriptVals asg transcript (p + 1) i := by
  funext i
  by_cases hi : (i : ℕ) = 0 <;> simp [fsNote, transcriptVals, hi, hm]

/-- **`fsBinding_correct` — the keystone iff.** The system accepts `asg` IFF every
challenge wire carries EXACTLY the Fiat–Shamir chain hash of its transcript prefix
(`FsBound`). Sound AND complete: nothing but the chain equations is imposed, and they are
fully imposed. The round-local ⟺ global-chain equivalence is one induction over the
squeeze index; each round's meaning is `hashTerm_correct`, reused. -/
theorem fsBinding_correct [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (transcript : Fin n → Fin w → Idx) (challenge : Fin n → Idx) :
    systemAccepts asg (fsBindingGadget spec transcript challenge) ↔
      FsBound spec (transcriptVals asg transcript) fun k => asg (challenge k) := by
  refine Iff.trans (systemAccepts_map_finRange asg _) (Iff.trans
    (forall_congr' fun k => hashTerm_correct asg spec (challenge k)
      (fsNote transcript challenge k)) ?_)
  constructor
  · intro hr
    suffices hs : ∀ m (hm : m < n),
        asg (challenge ⟨m, hm⟩) = fsChainVal spec (transcriptVals asg transcript) m from
      fun k => hs k.val k.isLt
    intro m
    induction m with
    | zero =>
      intro hm
      rw [hr ⟨0, hm⟩, fsNote_zero_vals asg transcript challenge hm]
      rfl
    | succ p ih =>
      intro hm
      have hp : p < n := Nat.lt_of_succ_lt hm
      rw [hr ⟨p + 1, hm⟩, fsNote_succ_vals asg transcript challenge hm hp, ih hp]
      rfl
  · intro hb
    have hbm : ∀ m (hm : m < n),
        asg (challenge ⟨m, hm⟩) = fsChainVal spec (transcriptVals asg transcript) m :=
      fun m hm => hb ⟨m, hm⟩
    intro k
    obtain ⟨_ | p, hm⟩ := k
    · rw [fsNote_zero_vals asg transcript challenge hm]
      exact hbm 0 hm
    · have hp : p < n := Nat.lt_of_succ_lt hm
      rw [fsNote_succ_vals asg transcript challenge hm hp, hbm p hp]
      exact hbm (p + 1) hm

/-- The EXECUTOR reading of the keystone — `accepts_iff_semHolds` (initiality) doing the
transfer, no new trust. -/
theorem fsBinding_semHolds_correct [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (transcript : Fin n → Fin w → Idx) (challenge : Fin n → Idx) :
    systemSemHolds asg (fsBindingGadget spec transcript challenge) ↔
      FsBound spec (transcriptVals asg transcript) fun k => asg (challenge k) := by
  rw [← systemAccepts_iff_systemSemHolds, fsBinding_correct]

/-- **Teeth, general form**: an assignment with ANY challenge wire off its chain hash is
REJECTED — the free-challenge attack fails at every round, for every spec. -/
theorem fsBinding_teeth [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (transcript : Fin n → Fin w → Idx) (challenge : Fin n → Idx) (k : Fin n)
    (h : asg (challenge k) ≠ fsChainVal spec (transcriptVals asg transcript) k.val) :
    ¬ systemAccepts asg (fsBindingGadget spec transcript challenge) :=
  fun hacc => h ((fsBinding_correct asg spec transcript challenge).mp hacc k)

/-- **Premise-inhabitation / completeness**: EVERY transcript has its accepting
assignment — the block values on the transcript wires, the computed chain hashes on the
challenge wires. The iff has teeth in both directions. -/
theorem fsBinding_complete [NeZero w] (spec : PermSpec F w)
    (blkv : Fin n → Fin w → F) :
    ∃ asg : (ULift.{u} (Fin n × Fin w) ⊕ ULift.{u} (Fin n)) → F,
      (∀ k i, asg (.inl (ULift.up (k, i))) = blkv k i) ∧
        systemAccepts asg (fsBindingGadget spec
          (fun k i => .inl (ULift.up (k, i))) (fun k => .inr (ULift.up k))) := by
  refine ⟨fun x => match x with
    | .inl p => blkv p.down.1 p.down.2
    | .inr k => fsChainVal spec
        (fun m i => if h : m < n then blkv ⟨m, h⟩ i else 0) k.down.val,
    fun _ _ => rfl, ?_⟩
  rw [fsBinding_correct]
  intro k
  rfl

/-! ## §4. The BOUND verifier — the challenges are not free. -/

/-- **The FS-bound recursive verifier**: challenge binding ++ sumcheck verifier ++
FRI-query verifier as ONE system. The binding is load-bearing exactly when the verifier
challenge wires are SHARED with the squeeze wires (`chal i = challenge (e i)`,
`beta k = challenge (eb k)` — a wiring instantiation, like the FRI `next`-chaining); then
acceptance forces every challenge to its transcript hash
(`boundVerifier_challenges_bound`). -/
def boundVerifier [NeZero w] (spec : PermSpec F w)
    (transcript : Fin s → Fin w → Idx) (challenge : Fin s → Idx)
    (claimW scFinalW : Idx) (g0 g1 chal : Fin n → Idx)
    (half : F) (friFinalW : Idx) (lo hi next beta tw twoX : Fin rounds → Idx) :
    ConstraintSystem F Idx :=
  fsBindingGadget spec transcript challenge
    ++ (sumcheckVerifierGadget claimW scFinalW g0 g1 chal
      ++ friQueryVerifierGadget half friFinalW lo hi next beta tw twoX)

/-- **`boundVerifier_correct` — the composed keystone.** The bound verifier accepts IFF
the challenges are the FS chain hashes of the transcript AND the sumcheck verifier accepts
AND the FRI query verifier accepts — `systemAccepts_append` + the three landed keystones,
zero new constraint work. -/
theorem boundVerifier_correct [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (transcript : Fin s → Fin w → Idx) (challenge : Fin s → Idx)
    (claimW scFinalW : Idx) (g0 g1 chal : Fin n → Idx)
    (half : F) (friFinalW : Idx) (lo hi next beta tw twoX : Fin rounds → Idx) :
    systemAccepts asg (boundVerifier spec transcript challenge claimW scFinalW
        g0 g1 chal half friFinalW lo hi next beta tw twoX) ↔
      (FsBound spec (transcriptVals asg transcript) (fun k => asg (challenge k))
        ∧ SumcheckVerifierAccepts (asg claimW) (asg scFinalW)
            (fun i => asg (g0 i)) (fun i => asg (g1 i)) (fun i => asg (chal i))
        ∧ FriQueryAccepts half (asg friFinalW)
            (fun k => asg (lo k)) (fun k => asg (hi k)) (fun k => asg (next k))
            (fun k => asg (beta k)) (fun k => asg (tw k)) (fun k => asg (twoX k))) := by
  unfold boundVerifier
  rw [systemAccepts_append, fsBinding_correct, recursiveVerifierPair_correct]

/-- **The challenges are NOT free.** In the shared instantiation (each verifier challenge
wire IS a squeeze wire), acceptance FORCES every sumcheck challenge and every FRI fold
challenge to the chain hash of its transcript prefix — the in-circuit Fiat–Shamir
discipline, as a theorem about every accepting assignment. -/
theorem boundVerifier_challenges_bound [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (transcript : Fin s → Fin w → Idx) (challenge : Fin s → Idx)
    (claimW scFinalW : Idx) (g0 g1 chal : Fin n → Idx)
    (half : F) (friFinalW : Idx) (lo hi next beta tw twoX : Fin rounds → Idx)
    (e : Fin n → Fin s) (he : ∀ i, chal i = challenge (e i))
    (eb : Fin rounds → Fin s) (heb : ∀ k, beta k = challenge (eb k))
    (hacc : systemAccepts asg (boundVerifier spec transcript challenge claimW scFinalW
      g0 g1 chal half friFinalW lo hi next beta tw twoX)) :
    (∀ i, asg (chal i) = fsChainVal spec (transcriptVals asg transcript) (e i).val)
      ∧ ∀ k, asg (beta k) = fsChainVal spec (transcriptVals asg transcript) (eb k).val := by
  have hb := ((boundVerifier_correct asg spec transcript challenge claimW scFinalW
    g0 g1 chal half friFinalW lo hi next beta tw twoX).mp hacc).1
  exact ⟨fun i => by rw [he i]; exact hb (e i),
    fun k => by rw [heb k]; exact hb (eb k)⟩

/-! ## §5. Keystone witnesses — BUILT over `ZMod 7` and `ZMod 13`, all `decide`d against
the REAL fold via `AirRange`'s `Decidable` instances. -/

namespace FiatShamirExample

/-! ### The binding alone, `ZMod 7` — the challenge wires are fully determined.

`spec7`: `α = 5` (`gcd(5, 6) = 1`, a genuine S-box over `ZMod 7`), one full + one partial
round — demo values exercising the structure, not deployed parameters
(`[AIR-poseidon-params]`). Layout on `Fin 5`: transcript wires `m₀ m₁ m₂` at 0–2,
challenge wires at 3–4. Blocks: round 0 absorbs `(m₀, m₁)`; round 1 chains
`(chal₀ ∥ m₂)` — the slot-0 entry of `transcript7`'s row 1 is superseded by the chain, so
we pass the challenge wire itself there, making the supersession visible in the layout.
Honest chain: `chal₀ = H(3, 5) = 2`, `chal₁ = H(2, 6) = 1`. -/

/-- Demo linear layer over `ZMod 7` (invertible: det `= 1`). -/
def demoM7 : Fin 2 → Fin 2 → ZMod 7 := ![![1, 1], ![1, 2]]

/-- Demo 2-round spec over `ZMod 7`: full (rc `(1,2)`), partial (rc `(3,4)`). -/
def spec7 : PermSpec (ZMod 7) 2 where
  α := 5
  rounds := [⟨![1, 2], true, demoM7⟩, ⟨![3, 4], false, demoM7⟩]

def transcript7 : Fin 2 → Fin 2 → Fin 5 := ![![0, 1], ![3, 2]]
def chal7 : Fin 2 → Fin 5 := ![3, 4]

/-- The 2-squeeze binding gadget over `ZMod 7`. -/
def fsGadget7 : ConstraintSystem (ZMod 7) (Fin 5) :=
  fsBindingGadget spec7 transcript7 chal7

/-- *The chain computes*: `H(3, 5) = 2`. -/
example : hashExec spec7 ![3, 5] = 2 := by decide

/-- *The chain function computes end-to-end*: squeeze 1 on the honest wires is
`H(H(3,5), 6) = H(2, 6) = 1` — the prefix (both blocks) genuinely read. -/
example : fsChainVal spec7
    (transcriptVals (![3, 5, 6, 2, 1] : Fin 5 → ZMod 7) transcript7) 1 = 1 := by decide

/-- *Satisfiable, computed*: the honest transcript with its DERIVED challenges `(2, 1)`
is ACCEPTED. -/
example : systemAccepts ![3, 5, 6, 2, 1] fsGadget7 := by decide

/-- *The challenge wires are FULLY DETERMINED, quantified over all 49 assignments*: with
the transcript fixed, acceptance holds IFF both challenge wires carry exactly the chain
hashes — no freedom whatsoever remains on the challenge wires. -/
example : ∀ c d : ZMod 7,
    systemAccepts ![3, 5, 6, c, d] fsGadget7 ↔ (c = 2 ∧ d = 1) := by decide

/-- *Teeth (the transcript is committed)*: tampering an EARLY transcript wire
(`m₀ : 3 → 4`) under the stale challenges is REJECTED — `chal₀ = 2 ≠ H(4, 5) = 6`; the
binding pins the challenges to THIS transcript, not merely to some transcript. -/
example : ¬ systemAccepts ![4, 5, 6, 2, 1] fsGadget7 := by decide

/-- *Teeth (a forged root challenge with a CONSISTENT continuation)*: `chal₀` forged
`2 → 3` and `chal₁` re-derived honestly FROM the forgery (`H(3, 6) = 0`) — REJECTED
anyway: the chain's root is anchored in the transcript hash, not in the previous wire
alone. -/
example : ¬ systemAccepts ![3, 5, 6, 3, 0] fsGadget7 := by decide

/-- *…attribution, machine-checked*: on that forged vector the round-1 `hashTerm` ACCEPTS
(the continuation was consistent)… -/
example : accepts (![3, 5, 6, 3, 0] : Fin 5 → ZMod 7)
    (hashTerm spec7 (chal7 1) (fsNote transcript7 chal7 1)) := by decide

/-- *…so the rejection is EXACTLY the round-0 binding* — `3 ≠ H(3, 5)`. -/
example : ¬ accepts (![3, 5, 6, 3, 0] : Fin 5 → ZMod 7)
    (hashTerm spec7 (chal7 0) (fsNote transcript7 chal7 0)) := by decide

/-! ### The BOUND verifier, `ZMod 13` — the free-challenge attack rejected.

AirHash's `demoSpec` (w = 2, α = 5, 3 rounds) as the FS permutation; the sumcheck
verifier's honest MLE-of-AND transcript (`SumcheckVerifierAir` §5) with its challenges now
DERIVED, and the FRI-query verifier (1 round, the fold of `p(X) = 3X + 2` at `x = 2`,
`half = 7`) with its fold challenge β derived too. FIVE chain steps absorb the WHOLE
sumcheck transcript — claim, `g₀(0)`, `g₀(1)`, `g₁(0)`, `g₁(1)`, and the claimed oracle
value — two squeezes being internal state (multi-slot absorption as chained steps), three
feeding the verifiers:

  `c₀ = H(claim, g₀(0))`, `r₀ = H(c₀, g₀(1))`, `c₂ = H(r₀, g₁(0))`,
  `r₁ = H(c₂, g₁(1))`, `β = H(r₁, final)`.

Layout on `Fin 17`: the sumcheck layout at 0–7 (claim 0, final 1, `gᵢ(0)` 2+i, `gᵢ(1)`
4+i, `rᵢ` 6+i), the FRI layout at 8–14 (final 8, lo 9, hi 10, next 11, β 12, tw 13,
twoX 14), the two state squeezes at 15 (`c₀`) and 16 (`c₂`). Squeeze wires
`![15, 6, 16, 7, 12]` — wires 6, 7 ARE the sumcheck challenge wires and wire 12 IS the FRI
β wire: sharing, not copying. Honest chain over `ZMod 13`: `c₀ = H(1,0) = 6`,
`r₀ = H(6,1) = 10`, `c₂ = H(10,0) = 10`, `r₁ = H(10,10) = 7`, final `= r₀·r₁ = 5`,
`β = H(7,5) = 6`; the honest FRI fold at `β = 6`: `lo = 8`, `hi = 9`,
`next = 2 + 3·6 = 7`, `tw = 10`, `twoX = 4`. The FRI opened wires and the oracle value are
still free-floating pending `[RECURSE-merkle-bind]`. -/

set_option maxRecDepth 8192

/-- The five squeeze wires: state `c₀`, sumcheck `r₀`, state `c₂`, sumcheck `r₁`, FRI β. -/
def wChalFS : Fin 5 → Fin 17 := ![15, 6, 16, 7, 12]

/-- The five absorb blocks (slot 0 of rows ≥ 1 superseded by the chain; we pass the
previous squeeze wire there, making the supersession visible). -/
def transcript13 : Fin 5 → Fin 2 → Fin 17 := ![![0, 2], ![15, 4], ![6, 3], ![16, 5], ![7, 1]]

def scG0 : Fin 2 → Fin 17 := ![2, 3]
def scG1 : Fin 2 → Fin 17 := ![4, 5]
def scChal : Fin 2 → Fin 17 := ![6, 7]

/-- **The composed, FS-bound recursive verifier** over `ZMod 13` at the shared layout. -/
def boundDemo : ConstraintSystem (ZMod 13) (Fin 17) :=
  boundVerifier demoSpec transcript13 wChalFS 0 1 scG0 scG1 scChal
    7 8 ![9] ![10] ![11] ![12] ![13] ![14]

/-- The HONEST assignment: the real MLE-of-AND sumcheck run and the real FRI fold, every
challenge the DERIVED chain hash. -/
def honest : Fin 17 → ZMod 13 := ![1, 5, 0, 0, 1, 10, 10, 7, 7, 8, 9, 7, 6, 10, 4, 6, 10]

/-- The FORGED assignment — the free-challenge attack: `r₀` forged `10 → 11`, every
DOWNSTREAM wire re-derived consistently from the forgery (`g₁(1) = 11`,
`c₂' = H(11,0) = 8`, `r₁' = H(8,11) = 7`, final `= 11·7 = 12`, `β' = H(7,12) = 2`,
`next' = 2 + 3·2 = 8`) so that BOTH verifiers and the whole downstream chain accept. Only
the root binding `r₀ = H(c₀, g₀(1))` is violated. -/
def forged : Fin 17 → ZMod 13 := ![1, 12, 0, 0, 1, 11, 11, 7, 8, 8, 9, 8, 2, 10, 4, 6, 8]

/-- *The chain computes*: squeeze 1 (= `r₀`) on the honest wires is `10`. -/
example : fsChainVal demoSpec (transcriptVals honest transcript13) 1 = 10 := by decide

/-- *The chain computes end-to-end*: squeeze 4 (= β) reads the whole five-block prefix —
`H(H(H(H(H(1,0),1),0),10),5) = 6`. -/
example : fsChainVal demoSpec (transcriptVals honest transcript13) 4 = 6 := by decide

/-- *Satisfiable, computed*: the honest transcript with DERIVED challenges is ACCEPTED by
the whole bound verifier — binding + sumcheck + FRI in one system. -/
example : systemAccepts honest boundDemo := by decide

/-- *The attack the binding exists to kill, computed*: the forged transcript — challenges
chosen, not derived — is ACCEPTED by the free-challenge verifier pair (sumcheck + FRI
exactly as landed): a prover who picks `r₀` freely forges at will. -/
example : systemAccepts forged
    (sumcheckVerifierGadget (0 : Fin 17) 1 scG0 scG1 scChal
      ++ friQueryVerifierGadget 7 8 ![9] ![10] ![11] ![12] ![13] ![14]) := by decide

/-- *…and the binding alone kills it*: the same forged assignment is REJECTED by
`fsBindingGadget` — the FS binding is load-bearing, not decorative. -/
example : ¬ systemAccepts forged (fsBindingGadget demoSpec transcript13 wChalFS) := by
  decide

/-- *So the BOUND verifier rejects the attack.* -/
example : ¬ systemAccepts forged boundDemo := by decide

/-- *Attribution, machine-checked*: on the forged assignment every squeeze EXCEPT the
forged one accepts (the attacker re-derived the continuation honestly)… -/
example : ∀ k : Fin 5, k ≠ 1 →
    accepts forged (hashTerm demoSpec (wChalFS k) (fsNote transcript13 wChalFS k)) := by
  decide

/-- *…so the rejection is EXACTLY the forged squeeze* — `11 ≠ H(c₀, g₀(1)) = 10`. -/
example : ¬ accepts forged
    (hashTerm demoSpec (wChalFS 1) (fsNote transcript13 wChalFS 1)) := by decide

/-- *Teeth + premise-inhabitation, quantified*: with everything else honest, the shared
challenge wire `r₀` is FORCED — acceptance holds iff `c = 10`, over every field element. -/
example : ∀ c : ZMod 13,
    systemAccepts ![1, 5, 0, 0, 1, 10, c, 7, 7, 8, 9, 7, 6, 10, 4, 6, 10] boundDemo
      ↔ c = 10 := by decide

/-- *The general binding, consumed on the demo*: EVERY accepting assignment of
`boundDemo` has its sumcheck challenges and its FRI β equal to the chain hashes —
`boundVerifier_challenges_bound` at the shared wiring (`scChal = wChalFS ∘ ![1, 3]`,
β `= wChalFS 4`), no enumeration. -/
example (asg : Fin 17 → ZMod 13) (h : systemAccepts asg boundDemo) :
    (∀ i : Fin 2, asg (scChal i)
        = fsChainVal demoSpec (transcriptVals asg transcript13)
            ((![1, 3] : Fin 2 → Fin 5) i).val)
      ∧ ∀ k : Fin 1, asg ((![12] : Fin 1 → Fin 17) k)
          = fsChainVal demoSpec (transcriptVals asg transcript13)
              ((![4] : Fin 1 → Fin 5) k).val :=
  boundVerifier_challenges_bound asg demoSpec transcript13 wChalFS 0 1 scG0 scG1 scChal
    7 8 ![9] ![10] ![11] ![12] ![13] ![14] ![1, 3] (by decide) ![4] (by decide) h

/-! ## §6. The recursion point, BUILT — the BOUND verifier EMITS.

Because `boundVerifier` is a `ConstraintSystem`, the verified emit path applies with zero
new work: the emitted `ConstraintDescriptor`'s satisfiability IS the bound verifier's
acceptance. So **"the FS-bound verifier accepted this transcript" is itself an emitted,
Loom-provable statement** — and unlike the §4 pair of the landed files, its challenge
wires are NOT free: a satisfying witness must carry the derived challenges. A Loom proof
of the emitted statement is a proof that a NON-INTERACTIVE proof verified — the recursive
apex with Fiat–Shamir inside the circuit. Remaining: `[RECURSE-merkle-bind]` (openings and
absorbed roots via AirMembership), then the emitted system is the whole self-contained
light-client verifier. -/

/-- **The bound verifier emitted**: descriptor satisfiability at the demo layout ⟺ the
FS-bound verifier accepts — `emit_accepts_iff_fin` consumed on the composed gadget, no new
proof. -/
example (asg : Fin 17 → ZMod 13) :
    (∃ wv : ℕ → ZMod 13, (∀ i : Fin 17, wv i.val = asg i) ∧
        descriptorHolds (emit Fin.val 17 17 boundDemo) wv)
      ↔ systemAccepts asg boundDemo :=
  emit_accepts_iff_fin 17 17 asg boundDemo

end FiatShamirExample

/-! ### Honest residuals — the rungs above this one (named, none stubbed)

`[RECURSE-merkle-bind]` — the remaining composition piece: `lo`/`hi`/`next`, the oracle
value, and the absorbed commitment roots bound to AirMembership's `membershipGadget` (the
same `++` + wire-sharing; vocabulary landed), and `twoX` to the query index's domain
point. `[RECURSE-fs-sponge]` — deployed sponge mode (rate/capacity, padding, domain
separation) atop `[AIR-poseidon-params]`. `[RECURSE-fs-bridge]` — the Loom identification
of `FsBound` with the FS transcript relation (`[LC-fs-adaptive]`'s object),
Assurance-side, like `[RECURSE-sumcheck-bridge]`/`[RECURSE-fri-bridge]`. `[FS-oracle]` —
FS soundness of the instantiated permutation is a cryptographic FLOOR (`[COMMIT-CR]`'s
sibling), never a theorem here: the constraints force the challenges to BE the hashes;
that hash-forced challenges are as good as random ones is the assumption the label
carries. -/

end Minidregg.Compiler
