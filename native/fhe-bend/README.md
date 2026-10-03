# Public Bend on private BFV inputs

This physical package consumes the checked `Host/BendLogicEmit.lean` artifact.
It does not author Bend semantics, solve relational AIR for missing wires, mint
input-validity proofs, or create transition/release authority. Its separate
public evaluator and public checker accept the same exact source artifact hash,
parameter encoding, key epoch, ciphertext bytes and invocation context.

The initial profile is public unary literal enum cases with owner-generated
canonical Boolean ciphertexts. Parameters are degree4096, t1032193 and the exact
three preserved coefficient moduli. The actual owned fhe0.1.1 fork is included
with its source/license, rather than pulling the Bread GPU/PQ/proof tower.
`constructiveIntegerOutput` is emitted by the existing Lean expression/flatten
compiler at Rat, and its integral constants are cross-checked against the same
expression emitted at BabyBear. Negative scalar multiplication uses ciphertext
negation, preserving signed lifting instead of multiplying by the unrelated
BabyBear residue or the uncentered BFV t-minus-one coefficient.

`fhe-bend evaluate ARTIFACT REQUEST COMPLETION CHECKED_ARTIFACT_SHA256` writes
only a completion candidate. `fhe-bend check` independently reexecutes and
compares every completion field and exact canonical ciphertext bytes. Shape and
encoding checks are public parsing restrictions, not proofs that a malicious
ciphertext encrypts a bit or was honestly sampled.

`fhe-bend-owner ARTIFACT HASH FHE_BEND_BINARY NEW_RUN_DIR` is a physical
conformance harness. Its secret key/plaintexts remain resident in the parent;
children receive only public artifact/input/key material. It privately checks
all packed slots of the one emitted source plan and rejection cases. A changed
key-epoch claim refusal does not prove ciphertext membership in that key; input
sampling/bitness/key linkage remains the honest owner-generator assumption. It does not establish Mini governance or
threshold custody. Its context is labeled conformance-only. No secret key is
written, and no arbitrary decrypt CLI exists. This test's plaintext assertions
must never be used as public authority over ordinary submitted ciphertexts.

Semantic scope: exact source compiler theorems and BFV correctness remain
separate. The plaintext modulus t=1032193 is prime; Air's Field theorems must not be
instantiated over arbitrary composite Z_t. Actual sampler/ring/noise/Rust
correspondence is a named proof frontier, not certified by successful tests.
Depth0 is leveled and excludes ciphertext multiplication. Current parameter
selection is inherited from the pinned library, not a new end-to-end lattice
security/noise/lifetime theorem. Public plan/layout/packing/size/steps are leaked;
circuit/program secrecy and sanitization are not claimed.

Mini's native receiving join must consume exact candidate bytes and bind actual
program/semantic IDs, input commitment, predecessor, current authority and
canonical tariff, then prepare/commit an encrypted result. A separate authorized
release must bind that committed output, current policy and recipient before any
production owner decoder accepts it. The conformance runner cannot supply this
join. Retain the existing reserve-before-private-release budget discipline.

The same package now has a second explicitly bounded plan profile for the
compiler's actual dynamic core-enum mux schema: selector/trueArm/falseArm input
wires1/2/3 and y+b*(x-y), private relational layout, signed Rat projection. Its
source/API compiles and has passed actual physical conformance on the
qualified emitted artifact, including all eight Boolean environments and a
second encrypted predecessor computation. Future source adapters must likewise
wait for their own qualified emitted artifact. It uses the preserved library's fallible
Multiplicator with canonical level0 relin material, exactly one ciphertext
product and one relinearization. Relin polynomial format is NttShoup and has
its own public parser checks. Matching key/short-noise relation remains a premise.

Request adds optional relinearization_key (absent in literal mode) and ordered
input_depths. The key epoch binds params/publickey/relin material. Cost now names
relinearizations and CUMULATIVE multiplicative depth. One plan multiplication
level does not reset ciphertext lifetime on each invocation. The mux profile
admits owner/provenance-declared input depth at most1 and output lifetime at
most2; a third unrefreshed invocation refuses. Syntax cannot prove these declared
depths or a cryptographic noise envelope; production needs authenticated lineage,
actual scheme correspondence and lifetime failure admission. Tests cannot supply
that theorem. Fresh/reused input validity remains an honest-generator premise.

Owner source includes a bounded repeated-state conformance case using the prior
ciphertext as falseArm under the SAME source/keys, a freshly encrypted private
selector, exact predecessor binding, a deterministic byte-identical retry, and
refusal after the lifetime bound. No coordinator decrypts state; only the owning
conformance parent decodes its privately known outputs. This is not durable Mini
installation/release, fee idempotence or persistent key recovery.

Resident-owner join source (pending native qualification): optional --governed SOURCE_ARTIFACT DRIVER DRIVER_SHA256 NATIVE_SESSION_CONFIG invokes the deployment-pinned current-authority driver before each decode. SOURCE_ARTIFACT is native BendWorldProgramCodec bytes, distinct from constructive compiler JSON. Driver prepares actual source/context IDs before execution; ten declared capacity lanes remain opaque provenance and do not replace actual ordinary storage charge. commit-release verifies current canonical publication, permissions, durable storage and release journal, then returns exact full retained Completion bytes. Failure/uncertainty/different bytes aborts before decrypt. There is no mock receipt or driver. Native context, key registration and repeated nonce/generation progression remain world-owned qualification obligations. Trusted deployment executable paths are outside attacker-controlled input; hostile local OS/executable replacement is outside this adapter trust model.

The confirmed native driver sequence is:
1. register-key SOURCE_ARTIFACT OWNER_PUBLIC_MANIFEST SESSION_CONFIG KEY_RECORD
2. prepare-context SOURCE_ARTIFACT COMPILER_ARTIFACT KEY_RECORD SESSION_CONFIG CONTEXT
3. commit-release SOURCE_ARTIFACT COMPILER_ARTIFACT KEY_RECORD REQUEST COMPLETION SESSION_CONFIG RELEASED_COMPLETION
KeyRecord is the source-owned canonical registration receipt/reference; Rust
passes the exact retained bytes and never invents that codec. Registration
attributes public material to an authorized native owner and current law. It
does not prove key relation, ciphertext input domain or short noise. The actual
native driver remains a separate qualification obligation.


Generic natural-expression extension (source authored, not compiled or executed):
The public-natural-expression.v1 compiler producer uses exact captured source
Book/entry and a reusable input/literal/add expression grammar, with the same
signed constructive DAG and independent natural-expression owner oracle.
Inputs are scalar SIMD natural values, caps exclusive; outputMax is inclusive.
The consumer permits at most 16 inputs and 64 ordered addition gates, no
ciphertext multiplication or nontrivial plaintext multiplication, no relinearization
key, and fresh input depth zero. Natural intermediate maxima must be below t.
Source charge policy/reservation remain compiler/native semantic fields; physical
Cost counts do not stand for source evaluation charges.

ConditionalLinearEnvelope is an explicit conditional abstract phase bound,
not ciphertext input validity, a noise certificate, or a Rust refinement theorem.
Fresh public-key encryption CBD variance10 support gives coefficient error
bound 2*4096*20*20+20 = 3,276,820; actual floor(q*m/t) lifting adds at most one
defect per ciphertext/ciphertext or ciphertext/plaintext addition. Every wire
derives its own bound and final 2*t*(B+1)<q margin. Scalar slot range and inverse
NTT polynomial coefficient range differ. Actual NTT/RNS/rounding correspondence
and same-opening/range evidence for externally supplied ciphertexts remain
separate proof obligations. Declared depth zero cannot prove fresh encryption,
and this profile cannot reset inherited ciphertext provenance. Public parameters
are additionally checked for variance10. No generic emitted artifact is fabricated.

Fable review6 reconciliation (2026-10-03): prior run-literal-03, run-mux-02
and run-prelude-01 exercised real BFV across4096 slots, deterministic independent
ciphertext replay, same-key encrypted predecessor depth2 and hostile/refusal
cases. These are executed owner conformance tests, not Rust #[test] functions.
They did not call measure_noise. Latest owner source now checks vendor
measure_noise at fresh ciphertexts and depth1/depth2 outputs only in offline
honest-owner conformance; measured values remain local and never authorize
native input/release. This new diagnostic is authored but not executed yet.
The vendor metric depends on its own decrypt/lift and is variable-time;
source-oracle checks remain separate, and neither is a general crypto proof.

n4096/Q109/variance10 is an exact pinned parameter identity. Upstream's
default_parameters_128 name/docstring does not establish an independently
estimated classical or quantum security level. No estimator output is currently
qualified for this preserved vendor/profile. Security/PQ estimation remains
unqualified. A depth integer is only structural lineage, never inherited noise.
The add-only natural profile is fresh-input-only with conditional coefficient
bound3,276,820 and recurrence Badd=Bleft+Bright+1; doubleSum bound13,107,283.
Persistent ctct inputs do not acquire that bound from an opaque native receipt.
