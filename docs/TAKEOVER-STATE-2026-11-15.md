# November 15 upstream takeover integration

Three independent changes are integrated from the same upstream base, `5d607d21d`.

- PR #31: `ab2023bc9` adds terminal delivery decline while allowing later destination completion to supersede it. Storage identity includes the entire binding and uses canonical JSON independent of downstream map-order features. Changed consumers handle the new variant.
- PR #30 test fix: `95c41f8a0` isolates the process-wide audit file-size limit in a guarded child test process. The broader service-bearer proposal is not included in this integration; its standalone successor is [keygate](https://github.com/emberian/keygate).
- PR #29: `00fecf315` generalizes safety thresholds and executable refinement to admitted committees beyond `n = 3f + 1`. Solo `(1,0)` remains admitted; multi-node zero-fault profiles are refused. [GENERALIZE.md](../GENERALIZE.md) states the exact scope: standard executable quorum, abstract smaller-quorum safety, and remaining liveness/reconfiguration obligations.

## Verification

The integrated source is byte-identical to each reviewed lane in its changed paths. The Simplex lane's 20-file Lean check and theorem axiom checks therefore apply unchanged. This integration changes no additional Lean source.

A Linux check of the combined Rust source passed:

- 17 SDK custody tests with `native` enabled.
- 2 binding-identity tests with both `native` and `serde_json/preserve_order` enabled.
- The exact broker audit-limit regression in a child process.

Earlier lane verification also checked the SDK consumers and parent limit/signal isolation. No deployment or live multi-node acceptance is claimed by these checks.

## Remaining integration

The full service-bearer PR remains outside Mini. The standalone [keygate](https://github.com/emberian/keygate) broker is undergoing hardening before adoption. Generalized Simplex liveness and arbitrary membership replacement are separate proof obligations, not results of this landing.
