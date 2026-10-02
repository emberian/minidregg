# Compatible SPK profile upgrades

`spk-host grain rebind-profile OLD_PROFILE ADMISSION` runs as the Store operator
while all retained application generations have completed STOP and their resident
units have no active process. It reads the root-owned `compatible-admission.json`
produced by the compatible-upgrade operator. The admission is trusted local
operator evidence of the compatibility audit, not a cryptographic history proof.
No old Host binary is executed against the upgraded Store.

The command authenticates the complete original profile hash, the old image and
config hashes, the preserved physical host identity, and the exact target images.
The only changes are the Mini Host and SPK runtime path/hash pairs, the Mini config
path/hash, and an explicit legacy genesis-config identity anchor. The config's
contents may change only `storageBinary` and `signatureBinary`, each to its exact
manifest-pinned image. Domain, semantics, seed, management custody, completion
custody, bubblewrap and Store directory remain fixed. The operator socket also
remains fixed unless the root admission explicitly adopts paired management/public
endpoints; only its managementSocket may replace miniOperatorSocket. The public
endpoint is never used for private authoring. This supports upgrade while the public
relay remains stopped, without accepting a caller-provided endpoint override.

The successor is written once at
`STATE_ROOT/upgrades/TRANSACTION_BASENAME/grain-host.json`. The original profile,
previous generation configs and enrollment attempts remain intact. An immutable
selection record is retained beside each successor, and `STATE_ROOT/active-profile.json`
is atomically replaced with the selected profile path/hash and admission path/hash.
A Store-private flock serializes selection with grain lifecycle commands. A stale
explicit profile refuses once a successor is selected. `grain supervise-instance`
follows the authenticated selection instead of reopening the original profile.

The legacy v2 Store directory convention uses the first sixteen hexadecimal digits
of its original config hash. Successors preserve that hash in `genesisConfigSha256`;
the canonical original profile cannot introduce this field. Successor loading checks
the complete root-admitted lineage back to that original profile. This compatibility
field does not replace any deployment identity supplied by newer source protocols.
Historical admissions are validated without requiring their old live helper paths
to remain installed; the current successor's runtime pins are still checked.

`spk-host grain session-intents PROFILE APP` reads retained route metadata and
validated fixed dispatch custody. Its JSON includes identities, capability references,
public signer pins and seed **paths**, never key bytes or bearer tokens. Enrollment
role is `null`: the original route did not retain it, so current source inspection
must recover the role when preparing a new enrollment. Re-enrollment and live route
registration are separate typed operations; changing a profile does neither.

The shared `native/compatible-upgrade-custody` crate validates admissions for both
SPK profiles and participant enrollment recovery. It checks root ownership, every
non-writable ancestor, canonical paths, file hashes, exact config change allowance,
and arbitrary-size JSON integers without floating-point rounding.

The operator must keep service entry points quiescent across publication and rebind.
The command's lock covers cooperating grain commands, not a privileged actor
starting systemd units directly. Rust tests and compilation establish the receiving
contract; full upgrade/START/re-enrollment/browser use still requires a joined
candidate journey.
