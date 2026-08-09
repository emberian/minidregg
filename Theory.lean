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
import Theory.CellState  -- typed logical cells, canonical materialization, and validated footprint patches make root coherence, frame, rejection atomicity, and no-ghost state structural
import Theory.ReactiveCellTransition  -- declaration-derived reactive control plus validated typed patches; physical CAS/nullifier insertion is an explicit handler premise
import Theory.CanonicalTransition  -- one canonical materialized post and proof-relevant typed delta unify ordinary and reactive prepared turns without a parallel store or caller-supplied roots
import Theory.ResourceCost  -- Lean-owned multi-lane bounds/exact debits, checked word overflow, canonical-turn metering, atomic refusal, and additive composition
import Theory.CanonicalReactiveView  -- observer-indexed typed lenses advance directly from canonical deltas; accepted guarded holes retain eager nullifiers without a parallel uniform post
import Theory.TypedAuthorization  -- complete-request-indexed authority evidence, explicit bearer/subject holders, exact epochs/revocation, and monotone capability attenuation
import Theory.AuthorizationDeclaration  -- first-order authorization plans compiled to indexed programs; accepted plans construct the request-indexed Authorized proposition
import Theory.CredentialAuthorityFamily  -- signature/proof/capability/token carriers share exact request digests, holder/scope/current-policy semantics, and proof-relevant strict attenuation without mode bypasses
import Theory.EffectDeclaration  -- target-indexed effects derive exact footprints and full-width resource deltas; only authorized, balanced declarations yield an AuthorizedEffect token
import Theory.DeclaredTurn  -- data-only authorization/effect execution with exact-post semantic certification and definitional rejection atomicity
import Theory.TurnTransition  -- ordinary and resumed reactive turns share canonical roots, exact footprints/deltas, frame laws, and atomic refusal
import Theory.AcceptedCellEffect  -- request-indexed semantic effect families admit ZK/MPC/FHE results as canonical cell transitions; sealed is the default and release is explicit
import Theory.CredentialAuthorityState  -- capability lineage, current epochs/policies, revocations, and operation nullifiers occupy one canonical typed sparse CellState; AuthState roots/reads project from that exact cell
import Theory.CredentialAuthorityEffects  -- issuance, strict attenuation, revocation, and epoch rotation are sealed AcceptedCellEffect families with exact atomic patches and same-canonical-pre authorization
import Theory.Hyperdocument  -- versioned domain-separated hyperdocument identity, authenticated principals, typed sparse namespaces, and exact canonical CellState mapping
import Theory.Bignum  -- canonical fixed-width little-endian limbs + proved Nat/Int codec (wide digest/challenge substrate)
import Theory.CrossModulus  -- one canonical integer with exact quotient/remainder views in two coprime moduli; CRT/range/canonicality seams for RNS/FHE bridges
import Theory.CompressedLinearEquation  -- exact signed integer equations normalized to canonical unsigned limb/carry balances for compressed RNS/FHE checks
import Theory.BinaryTower  -- [OB-8-tower] the GF(2) binary-tower field substrate (Binius path)
import Theory.BinaryTowerCodec  -- exact recursive Fan--Paar coordinates and fixed-width 32-byte round-trip; native code remains opaque
import Theory.BinaryTowerFanPaar  -- [BTOWER-fanpaar] the Fan–Paar generator recursion + fast tower multiplication
import Theory.BinaryTowerTrace  -- [BTOWER-fanpaar-basis] CLOSED (Wiedemann trace induction) — FanPaarRecursion holds
import Theory.AdditiveNTT  -- [BTOWER-additive-fri] additive domains + subspace-vanishing (GF(2)-linear) + novelpolynomial basis + the additive FRI fold
import Theory.AdditiveNTTTransform  -- [ANTT-transform] CLOSED: the additive NTT is a linear bijection; Loom/AdditiveProximity now realizes a macroscopic one-round [ANTT-proximity] band, while an executable butterfly/tower backend remains separate runtime work
