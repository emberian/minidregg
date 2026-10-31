# Rulings (present state; root writes, ember overrules by editing)

## Direction
- No rehearsal cut for now: make the system excellent. Hermes repaired; efficiency everywhere; reds fixed properly.
- Be wide: the largest costs first. Today's worst (see COSTS.md): app create to first page ~26 s (BEGIN plan 3-6 s,
  route 4.5 s, enrolment 4.1 s, START 2.3 s); `story new` 10-15 s; birth submit ~600 ms and growing with height;
  certify ~6 s per tail; restart plus first read ~5 s; cold first read 3.9 s; consent catch-up 20-30 ms per record;
  Host signed read ~5 ms; Hermes ask latency (unmeasured).
- Integrate the system with itself: more wiring, remove arbitrary restrictions, flesh out mechanisms.

## Decided
- Trunk is `main`; `green` marks the last fully green commit (83e926874 at the switch). Integrator agent retired;
  the builder script replaces it.
- No fsync anywhere; the network boundary does not imply permanence; reads keep nothing per read.
- Snapshots, never genesis replays; we trust the storage device.
- Shared consent resident (split tenancy) approved.
- Read-path GETs approved with (c) prepaid per-payer reservations and (d) per-route declared eligibility; owned by
  host-execution, statement first (astra's review: root scratchpad done/astra-get-contract.md).
- FORMAT (a): trie roots for unblinded growing kinds (eventHistory, authority); blinded kinds wait for the ZK
  selective opening (epoch b). Book entries become their own store addresses.
- KeptCell: the Materialized Aux cache (option b).
- Hashes: cSHAKE256 (SP 800-185, Keccak) for roots, cell digests and kernels; KMAC256 for keyed uses. BLAKE3 only where an
  outside format fixes it (SDK profile key derivation, fn's wire grammar, Bread's Turn::hash). No algebraic hash
  (Poseidon2) for roots: every write would pay it natively, and an opening must verify against the root, so the root's
  hash fixes the circuit. The ZK opening is a boolean proof system (MPC-in-the-head) over Keccak, where its only
  nonlinearity (chi) is cheap; to make openings faster, change the proof system, not the root hash.
- Cold first read and restart are the full Store open, O(height) (~4.3 ms per record). They go away only with KN2
  stage 2b: host-execution retypes the Host session and NativeHostReplay's admission over the light `Opening`;
  read-path then ports ClientConsentCore/ConsentAnchor. No constant-factor trims inside the full open.
- Residents never idle out; members share one base, a per-member session of a few MB is the target (up to 100
  members, more someday).
- Post-quantum ssh key exchange stays. GLM only via ~/.zai-key on the Z.AI coding-plan endpoint; OpenRouter (capped
  at $50) serves only non-GLM models.
- Confine even our own code: composed gate container to least privilege (Stage A, then user-namespaced with the
  custodian), every root unit reviewed. Demo Discord alert off until the next rehearsal.
- The builder lands its own fixture rerecord on main: by path, only the two fixture *Data.lean files, as a
  fast-forward of origin/main, never forced, never over a commit to those files since the recorded tip (10-31).
- Held: egress gateway; Oracle7 integration (its branches stay, unmerged). No new build box; persvati is available
  (stay within ~80 GB).
