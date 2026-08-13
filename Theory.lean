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
import Theory.CellStateWitness  -- ANTI-VACUITY: a closed schema/codec/materializer/cell whose patch actually reaches `ValidatedPatch` through `validate`, plus stale-root and both footprint-mismatch rejections computed
import Theory.TypedAuthorizationWitness  -- ANTI-VACUITY: a built portal/state/request that reaches `Authorized`, with the policy gate and the epoch equation shown load-bearing as refutations (evidence exists; authority does not follow)
import Theory.AcceptedCellEffectWitness  -- ANTI-VACUITY, the summit: a closed `AcceptedCellEffect` standing on the two witnesses above, forced sealed, with both request-binding equations exhibited as refutations
import Theory.CanonicalTransitionWitness  -- ANTI-VACUITY: a `PreparedTurn` whose derived post-root actually MOVES (`⟨0⟩` to `⟨1⟩`) — a singleton state space would have inhabited the type while testing nothing
import Theory.ReactiveCellTransition  -- declaration-derived reactive control plus validated typed patches; physical CAS/nullifier insertion is an explicit handler premise
import Theory.CanonicalTransition  -- one canonical materialized post and proof-relevant typed delta unify ordinary and reactive prepared turns without a parallel store or caller-supplied roots
import Theory.ResourceCost  -- Lean-owned multi-lane bounds/exact debits, checked word overflow, canonical-turn metering, atomic refusal, and additive composition
import Theory.CanonicalResourceKernel  -- typed sparse asset/account nucleus: transfer, issuer-backed mint/burn, fees, and prepaid leases share one patch-derived conservation law
import Theory.CellSlot  -- stable heterogeneous absent/present slots, canonical payload decoding, and monotone identifiers make creation and retirement first-class transitions
import Theory.CanonicalReactiveView  -- observer-indexed typed lenses advance directly from canonical deltas; accepted guarded holes retain eager nullifiers without a parallel uniform post
import Theory.TypedAuthorization  -- complete-request-indexed authority evidence, explicit bearer/subject holders, exact epochs/revocation, and monotone capability attenuation
import Theory.AuthorizationDeclaration  -- first-order authorization plans compiled to indexed programs; accepted plans construct the request-indexed Authorized proposition
import Theory.CredentialAuthorityFamily  -- signature/proof/capability/token carriers share exact request digests, holder/scope/current-policy semantics, and proof-relevant strict attenuation without mode bypasses
import Theory.EffectDeclaration  -- target-indexed effects derive exact footprints and full-width resource deltas; only authorized, balanced declarations yield an AuthorizedEffect token
import Theory.DeclaredActionLowering  -- a closed create/write/move action language lowers into exact accepted semantic effects without reviving the legacy runtime
import Theory.DeclaredTurn  -- data-only authorization/effect execution with exact-post semantic certification and definitional rejection atomicity
import Theory.TurnTransition  -- ordinary and resumed reactive turns share canonical roots, exact footprints/deltas, frame laws, and atomic refusal
import Theory.AcceptedCellEffect  -- request-indexed semantic effect families admit ZK/MPC/FHE results as canonical cell transitions; sealed is the default and release is explicit
import Theory.AcceptedCellEffectRequestBinding  -- family-selected lawful argument projections close the common request's args digest without duplicating authorization or overbinding envelopes
import Theory.CredentialAuthorityState  -- capability lineage, current epochs/policies, revocations, and operation nullifiers occupy one canonical typed sparse CellState; AuthState roots/reads project from that exact cell
import Theory.CanonicalAuthorityProjection  -- the finite revocation universe is derived from the authority cell's own sparse support, so omitted caller keys cannot erase a live revocation
import Theory.MaterializerCardinality  -- REGRESSION TOOTH: the deleted total-function carrier was uncountable; the landed sparse carrier is characterized by ordinary countability
import Theory.DeployedTotalCarrierAudit  -- closes the deleted total-carrier impossibility teeth for authority and Hyperdocument, completing all four migrated deployed schemas
import Theory.StoreFiniteSupport  -- total semantic stores reachable from zero have an exact sparse realization, while arbitrary infinite-support functions still do not acquire canonical bytes
import Theory.SparseLogicalState  -- the canonical dependent finite-map carrier, with primitive absence and explicit total `readD` views above it
import Theory.DeployedMaterializerWitness  -- effect, authority, and Hyperdocument schemas now have concrete materializers and cells; existence codecs are not deployment wire claims
import Theory.CredentialAuthorityEffects  -- issuance, strict attenuation, revocation, and epoch rotation are sealed AcceptedCellEffect families with exact atomic patches and same-canonical-pre authorization
import Theory.Hyperdocument  -- versioned domain-separated hyperdocument identity, authenticated principals, typed sparse namespaces, and exact canonical CellState mapping
import Theory.StableRanges  -- insertion-stable atom/range anchors, explicit deletion policies, and exact adapters into durable Hyperdocument marks/annotations
import Theory.HyperdocumentOperationIntent  -- acyclic pre-commit OperationId binds canonical action bytes but excludes post/request/effect/final-version identities
import Theory.HyperdocumentOperations  -- first-order create/edit/link/transclude/mark/annotate declarations derive exact accepted content patches, requests, and concrete post records
import Theory.HyperdocumentInterface  -- versioned capability-scoped interface negotiation for content/history reads and mutations; query never grants ambient object authority
import Theory.CausalVersionDag  -- content-addressed causal events admit exact resolved parents and concurrent siblings; current-tip-only is an explicit optional policy
import Theory.HyperdocumentCausalFamily -- ordinary accepted content effects instantiate the causal semantic family; includes one real deployed-schema genesis/history witness
import Theory.CausalVersionAncestry  -- admitted parent edges induce proof-relevant ancestry, acyclicity, and conservative common-base certificates without a fake unique LCA
import Theory.Bignum  -- canonical fixed-width little-endian limbs + proved Nat/Int codec (wide digest/challenge substrate)
import Theory.CrossModulus  -- one canonical integer with exact quotient/remainder views in two coprime moduli; CRT/range/canonicality seams for RNS/FHE bridges
import Theory.CompressedLinearEquation  -- exact signed integer equations normalized to canonical unsigned limb/carry balances for compressed RNS/FHE checks
import Theory.BinaryTower  -- [OB-8-tower] the GF(2) binary-tower field substrate (Binius path)
import Theory.BinaryTowerCodec  -- exact recursive Fan--Paar coordinates and fixed-width 32-byte round-trip; native code remains opaque
import Theory.BinaryTowerFanPaarCodec  -- concrete recursive Fan--Paar coordinate codec and canonical fixed-width byte realization; still no native representation theorem
import Theory.BinaryTowerFanPaar  -- [BTOWER-fanpaar] the Fan–Paar generator recursion + fast tower multiplication
import Theory.BinaryTowerTrace  -- [BTOWER-fanpaar-basis] CLOSED (Wiedemann trace induction) — FanPaarRecursion holds
import Theory.AdditiveNTT  -- [BTOWER-additive-fri] additive domains + subspace-vanishing (GF(2)-linear) + novelpolynomial basis + the additive FRI fold
import Theory.AdditiveNTTTransform  -- [ANTT-transform] CLOSED: the additive NTT is a linear bijection; Selvage/AdditiveProximity now realizes a macroscopic one-round [ANTT-proximity] band, while an executable butterfly/tower backend remains separate runtime work
import Theory.IntegerFingerprint  -- the Zaratan/Limber integer relation `a*b = c + u*m` and its random-prime fingerprint: counting core proved, prime-counting denominator left as a named hypothesis
import Theory.CyclotomicInertia  -- [SIS-inertia] ord_{3^k}(KoalaBear) = phi(3^k) at EVERY k, so Phi_81 is IRREDUCIBLE over F_KB and `F_KB[X]/(Phi_81)` is a FIELD of degree 54 -- maximal inertia, the best possible splitting for a lattice/module-SIS commitment. Both teeth: same conductor 81 is REDUCIBLE over BabyBear (2 factors) and M31 (6); same field F_KB SPLITS `X^(2^k)+1` completely for every k+1 <= 24, which is why the negacyclic lattice-PCS family is arithmetically dead on KoalaBear. ARITHMETIC POSSIBILITY ONLY -- the security bill is unpriced.
import Theory.ZkmlTensorOps  -- the zkML tensor-op vocabulary: an IxSignature over the intersection op set (scalar un/bin/cmp/select/fma, matmul-as-ordered-fold, ordered reduce, pure map, index read, shape-only reshaping), with a TOTAL denotation at an abstract ScalarOps carrier; NO op carries tensor data ([N3-converse]: constants are context entries, a commitment surface, never a payload). run = fold denAlg, so there is one program and N readings; run_transport (fold_rel, ONE induction, none at the use site) relates any two ScalarHom-related readings on EVERY trace; arith_transport does the same along a RingHom on the fragment TOp.arithmetic, whose complement -- div, pow, cmp, map, gather, dtype-changing cast -- IS the derived arithmetization bill; census_macs_eq_macAlg is the same collapse by fold_fusion for the cost reading. Teeth: a wrong cost algebra (matmul at m*n vs m*k*n), a wrong scalar reading (sub read as add), and the div gap exhibited on a pair of readings that agree on the arithmetic fragment. All witnesses kernel-decided; axiom footprints guarded.
