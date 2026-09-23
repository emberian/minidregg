# Portable fn authorship to Mini E1 evidence

`minidregg-host ORIGIN-PIN.json portable-verify-fn FN-PIN.json CLAIM.json
CARRIER.eml SOURCE.bin PACKAGE.bin RESULT.json` is an offline, read-only
boundary. `FN-PIN.json` independently selects the fn native image, ML-DSA-65
PEM path, principal (32 octets), Ed25519 public key (32 octets), and complete
ML-DSA-65 public key (1952 octets, lowercase hex). `CLAIM.json` supplies the
48-octet fn source identity, Message-ID and group text to compare; those
claims do not authorize themselves. The fn image's `hybrid-verify-source`
verb decodes the exact carrier in ACL2, checks both native signature suites,
and returns a versioned, bounded line with the verified principal, ACL2-
derived source identity, full keyset and exact authored source. Mini caps the
carrier at 32,768 bytes, checks the verifier exit and exact six-token line
with no trailing junk, and compares all identity fields to the independent
pin and claim. A different PEM file cannot silently select a different ML
key: the full verified raw key is compared after the native check.

`Kernel/FnPortableSource.lean` then decodes Mini's **application-specific**
one-part E1 source. It requires the fixed MIME headers and order, CRLF,
76-character base64 folding and canonical padding. It derives the exact
`DREGG/FN/NATIVE-PREFIX/v1` package from the authenticated source, then
`FnEvidence.verify` re-admits that package against the separately selected
Mini origin pin. The caller cannot hand Mini another package for the same
signed source. Outputs are written only after all checks pass. The source
and package files are exact bytes; the result describes portable fn
authorship and historical Mini origin admission separately.

The result deliberately says `storeAdmission: unestablished`. A valid
portable signature does not show that an fn Store retained the article, which
groups accepted it, what historical T10 verdict was recorded, or whether an
E2 consumer cursor advanced. This command does not author or submit a Mini
operation intent. The P1 local consumer's synthetic `fnVerdictRef` is not
upgraded by this command. Joining exact Store kind-4 event, enrolled snapshot,
Store history/incarnation/sequence and the future E2 fetch/ack interface is
a separate P2 step. Mini's native signature helper and fn's native image/
primitive observations remain trusted physical boundaries; these checks are
not proofs of key custody, hash collision resistance or filesystem power-
loss behavior.
