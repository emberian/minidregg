# Hosted current-birth provider fixture

`current_birth_provider.rs` is deterministic test support for the actual Hermes
worker. It requests the advertised Mini application tool, waits for a matching
tool response, then requests a session in a second prompt. It does not decide
Mini admission or replace the worker.

Build explicitly with `cargo build --locked --release --example
current_birth_provider` from this crate, respecting the repository's isolated
build guidance. Run the resulting executable with `--port PORT --state-dir
ABS_PRIVATE_DIR`. The directory must already exist with owner-only access and
must have no `stage` file. The listener binds only to `127.0.0.1`.

Every streamed response reports synthetic usage of one input and one output
token. Those values support the deterministic metering fixture; they are not
provider billing measurements. Stage is persisted before sending a response;
a lost response stops automatic replay of that stage. A completed stage sequence
only proves that stimulus and tool-response messages were exchanged. Acceptance
must separately verify native application/session receipts, signed resource
reads, budget settlement, and retained recovery. This is not real-model evidence.
