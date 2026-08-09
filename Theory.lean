/-
# Theory — the candidate-independent core (ATLAS §7).

Everything here must be the metatheory of *any* system built this way: abstract
parameters only, no imports outside Mathlib + Theory itself (enforced by
`scripts/check-import-boundary.sh`).
-/
import Theory.Knowledge  -- the verify/find seam: Verifiable/Discharged/Searchable, Claim/Holds/Knower
import Theory.PrivacyProfile  -- observer-indexed privacy axes, typed same-opening/release joins, and compositional noninterference
import Theory.DisclosureDeclaration  -- first-order observer releases require both request-indexed authorization and a checked same-opening witness before VerifiedRelease exists
import Theory.PrivateComputationDeclaration  -- typed ZK/MPC/FHE requests complete only with authorization, named representation bridges, same-opening, evidence, and an explicit disclosure effect
import Theory.IndexedProgram  -- indexed free programs with response-dependent typestate, executable handlers, fold fusion, and cross-carrier logical-relation folds
import Theory.GuardedAdvice  -- eager hole shape, typed late advice, total verification, and durable replay refusal
import Theory.ReactiveReceipt  -- authoritative receipt deltas, dependency-local reactive projections, atomic rejection, and witness-cursor snapshots
import Theory.ReactiveController  -- Lean-owned guarded-hole/reactive control derives Pending/Reject/CommitIntent from data-only host observations; physical CAS remains external
import Theory.TypedAuthorization  -- complete-request-indexed authority evidence, explicit bearer/subject holders, exact epochs/revocation, and monotone capability attenuation
import Theory.AuthorizationDeclaration  -- first-order authorization plans compiled to indexed programs; accepted plans construct the request-indexed Authorized proposition
import Theory.EffectDeclaration  -- target-indexed effects derive exact footprints and full-width resource deltas; only authorized, balanced declarations yield an AuthorizedEffect token
import Theory.Bignum  -- canonical fixed-width little-endian limbs + proved Nat/Int codec (wide digest/challenge substrate)
import Theory.CrossModulus  -- one canonical integer with exact quotient/remainder views in two coprime moduli; CRT/range/canonicality seams for RNS/FHE bridges
import Theory.CompressedLinearEquation  -- exact signed integer equations normalized to canonical unsigned limb/carry balances for compressed RNS/FHE checks
import Theory.BinaryTower  -- [OB-8-tower] the GF(2) binary-tower field substrate (Binius path)
import Theory.BinaryTowerFanPaar  -- [BTOWER-fanpaar] the Fan–Paar generator recursion + fast tower multiplication
import Theory.BinaryTowerTrace  -- [BTOWER-fanpaar-basis] CLOSED (Wiedemann trace induction) — FanPaarRecursion holds
import Theory.AdditiveNTT  -- [BTOWER-additive-fri] additive domains + subspace-vanishing (GF(2)-linear) + novelpolynomial basis + the additive FRI fold
import Theory.AdditiveNTTTransform  -- [ANTT-transform] CLOSED: the additive NTT is a linear bijection; Loom/AdditiveProximity now realizes a macroscopic one-round [ANTT-proximity] band, while an executable butterfly/tower backend remains separate runtime work
