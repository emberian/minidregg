# D-0004 — Loom as heterogeneous proof-assurance fabric

- Status: accepted, falsifiable
- Date: 2026-08-09

## Decision

Keep Loom as the proof-theoretic composition and assurance layer for the proof-native semantic
computer. Loom is not a universal execution field, VM, PCS, or requirement to invent every proof
component locally. Specialized Boolean/GF(2), ordinary-field, residue-ring FHE, MPC, lookup/RAM,
zero-knowledge, and history constructions remain native dialects.

Loom owns the typed joints between them: roots-before-challenges transcript causality, exact
security/error regimes, checked common-opening representation relations, native-failure
non-authority, clause evidence, and proof-carrying history attribution. The first deployment target
is one Tower256/additive authenticated-column controller shared by indexed lookup and the terminal
history checkpoint, followed by a cross-carrier BFV receipt.

## Why a composition layer is necessary

No current construction simultaneously supplies:

- efficient Boolean/word proving;
- odd-characteristic arithmetic and residue-ring FHE;
- authenticated MPC and controlled release;
- small/large lookup and mutable memory;
- malicious-composable zero knowledge;
- append-native straight-line-knowledge-sound history; and
- typed cross-carrier representation equality.

Different-characteristic carriers have no arithmetic cast that can honestly serve as the common
meaning. The common object is a canonical semantic value and exact checked opening relation, not a
field element. Imported constructions such as WARP, Flock, LogUp*, VEIL, ERA, or SwitchFold can
provide dialect components; they do not define the semantic machine or their composition.

## Hard invariants and non-claims

- Lean solely owns protocol control, semantics, and acceptance.
- Native CPU/GPU/FHE/MPC work is opaque and fallible. It may block availability; it cannot return
  an accepted token.
- GF(2), odd-characteristic fields, residue rings, and shares remain distinct.
- A bridge is a checked common-opening relation, never a cross-characteristic cast.
- Unique/Johnson/post-Johnson, PCS, commitment-CR, ROM, sampling, ZK, and extraction errors remain
  separate until a common game composes them.
- A manifest/controller/pin is not implementation or cryptographic evidence.
- Loom is not yet a deployed succinct or zero-knowledge proof system. Concrete PCS, CR, ROM,
  sampled-decider, hiding, and benchmark seams remain.

## Alternatives rejected

- **One universal field/AIR:** misrepresents ring/share semantics and sacrifices native efficiency.
- **One bespoke protocol interface per dialect:** repeats the same commitment/transcript/history
  seams and makes splice resistance depend on every adapter remembering them.
- **One imported frontier system as the whole architecture:** no candidate covers the required
  heterogeneous semantic, authorization, external-effect, and history interfaces.
- **Native verifier/protocol mirrors:** creates a second semantic authority outside Lean.

## Required evidence

- `Compiler.AuthenticatedColumnPlan`: concrete accepted transcript with typed roots, openings,
  representation edges, opaque native errors, and a Lean terminal checker.
- `Assurance.SemanticHistoryWARPAdditiveJoin`: pre-challenge semantic link roots and exact
  post-challenge folds joined to the additive checkpoint.
- One instantiated Tower256 codec/commitment/cSHAKE/Merkle/PCS controller shared by lookup and
  history.
- One BFV/RNS native-ring clause joined to exact bounded-integer consequences through checked
  representations.
- End-to-end prover/verifier/proof-size/memory measurements on application workloads.

## Kill or replace criteria

Revisit or remove Loom if:

1. one formalizable transparent/PQ construction supplies the required heterogeneous commitments,
   straight-line unbounded accumulation, malicious-composable ZK, and ring/MPC adapters with less
   machinery;
2. the shared controller still requires dialect-specific protocol mirrors;
3. it fails to remove at least two bespoke commitment/transcript joins;
4. application benchmarks show no useful performance or assurance frontier versus a homogeneous
   stack;
5. the security ledger cannot be reduced to one reviewable deployed game; or
6. formal maintenance prevents the semantic kernel and applications from progressing.

## Related decision and audit

- `D-0001`: authenticated columns and dual-root history.
- `D-0002`: canonical cell effects and hyperedge turns.
- Top-level live-source audit:
  `/Users/ember/dev/BREADSTUFFS_MINIDREGG_SUBSUMPTION_AUDIT_2026-08-09.md`.
