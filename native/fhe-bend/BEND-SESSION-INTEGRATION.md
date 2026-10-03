# Current native BFV receiving construction
Source-only WIP, not an executable governed acceptance result.

Kernel/BendKeyRegistration is coupled source-read/key-write ordinary native
admission over exact canonical Registered public material. Its storage receipt
attributes bytes to current author/law only, never crypto validity or threshold.

Host/BendSessionDriver owns actual current prepare, registered-key lookup,
external pinned ciphertext replay, source/key/result commit recheck, ordinary
opaque storage and current independent exact-byte release. CheckedPhysical has
a private constructor and binds retained bytes to native context + registered
key. The full compiler artifact and checker binary pins come from the operator,
not the physical request. Source-selected typed admission/charge/disclosure
remain world producer obligations. Internal source-only prepared tokens are
not accepted from arbitrary decoded wire statements.

native/resource-client/src/bend_session.rs is the additive custody bridge.
It reuses existing private plan_headers/sign_headers/read_secret/encode_signatures
via a child module, never recreates cSHAKE, and signs only source-owned whole
plans re-prepared by Host on its current image. The authority Ed25519 seed stays
in client process, and BFV sk stays in the physical owner process.

Required named captain changes (do not edit shared files concurrently):
* native/resource-client/src/main.rs: mod bend_session; dispatch
  bend-session-sign to bend_session::run(arguments after verb).
* Host/Main.lean: import Host.BendSessionDriver. Reuse Settings/loadSettings;
  no second global main/config implementation. Add bend-session-signing-check
  KIND PLAN_BYTES OUTPUT_JSON routed to signingInspection config KIND with the
  exact bounded input bytes and IO.ofExcept; write its returned inspection.
* Host/BendSessionDriverJson now authors strict native-session/key-handle ingress
  and all three concrete register-key/prepare-context/commit-release file commands.
  Canonical key handle retains resource/root/Registered bytes/actual storage
  receipt. Context output comes from real prepareContext. Add existing Host.Main
  dispatch after loading its Settings/config to call runFiles config configPath;
  match .error by nonzero exit and write no success/release substitute.
  Full executable driver wrapper should supply the pinned native config path to
  existing Host and forward exact command/file arguments unchanged.
* Shared NativeHostReplay+profile must register BendReturnRelease event before
  any release append. This new next-cohort event must not enter old Host journal.

Current gap: full CLI/current-session config/key-handle codecs are now authored
but uncompiled, and there is no executed current-governed result journey.
Session core + signer bridge remain uncompiled WIP.
This first native session binds one authored nonce/generation/root. The physical
owner repeated mux adapter passes the same config and therefore cannot advance
native state after the first commit; a separate current-admitted result cursor/
next invocation protocol must qualify before repeated governed use. Depth/noise/
typed lineage cannot be inferred from the opaque receipt. Host/BendReceiving and release authoring source/olean
qualification are separate owned dependencies. No JSON success flag is a receipt.


Host/BendSessionCursor source-only continuation now verifies exact original
storage command/event/receipt, exact release ingress/event/receipt, matching
opaque result key/artifact/audience, and current signed native predecessor read.
A private admitted cursor derives next nonce from accepted predecessor identity
and increments actual predecessor generation. It does not upgrade honest input
domain/noise assumptions. Canonical persisted cursor codec and driver retention/
uncertain reconciliation integration remain to be authored; no repeated native
run is qualified. Compiler.BendArtifactBinding producer is now owned by compiler
lane: actual Book/entry/body/expression/DAG/profile and planId must be derived
from source, not a chosen external artifact SHA. Driver binding consumption
awaits that concrete API and source profile domain agreement.
