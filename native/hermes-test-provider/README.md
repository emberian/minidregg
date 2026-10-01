# Hermes/Mini local protocol fixture

This standalone executable is a deterministic, loopback-only OpenAI chat-completions endpoint for an **actual upstream Hermes ACP** integration probe. It is not an AI model, a provider adapter for production, or a custody implementation. It makes no outbound requests and accepts no credentials. Mini still authenticates and settles every MCP operation through its normal controller and signed native path.

Run `cargo build --release`, then `target/release/mini-hermes-test-provider 127.0.0.1:PORT LOG_PATH`. Point an isolated Hermes `HERMES_HOME/config.yaml` at `http://127.0.0.1:PORT/v1` with `provider: custom`, `api_mode: chat_completions`, `default: mini-hermes-protocol-fixture`, and a dummy local API key. Do not carry a real provider key into the sandbox.

For the opt-in provider metering probe, append `--metered-usage`: streamed
responses then include one terminal usage chunk (1 prompt token, 2 completion
tokens) before `[DONE]`. `--metered-missing-usage` leaves usage out, and
`--metered-http-422` returns a local 422 error on each completion request.
`--route-probe` answers every completion with a fixed text reply and logs
`route-probe bytes=N auth=none|sha256:HEX`: the SHA-256 of the exact
`Authorization` header value it received (`Bearer TOKEN`), never the value, so
provider-routing evidence can say which credential a request carried.
These modes exercise the controller's held-allowance behavior; the default
fixture remains unchanged. The reported counts are synthetic, not an invoice.

The fixture requires Hermes to advertise `mcp__mini_grain__mini_read_resource` and `mcp__mini_grain__mini_publish`. Its first response for each prompt calls `mini_read_resource` for the allowlisted `publication` resource. It extracts the decimal `view.page.root` from that actual MCP result and uses it as `expectedTargetRoot`. On a fresh object it creates scalar field 0 with value 1; on a retained session whose signed read shows field 0, it creates field 2 with value 2. It considers only tool results after the current user prompt, so prior session history cannot fake completion. It ends only after a signed tool resource receipt. Unexpected models, missing tools, unreadable roots, reported tool errors, and missing receipts are rejected. The append-only log records protocol stages and byte counts, not prompts or tool-result bodies.

Use a fresh Mini deployment and controller state for each end-to-end run. The model-driven behavior here is only a repeatable protocol stimulus; acceptance evidence must also include the native signed read and publication outcome.

For the separate ContentResource workroom fixture, add `--content-workroom` after the log path and provision the allowlisted `workroom` read plus publication object 8001. Each prompt starts with a signed read: an empty page creates text atom 7401; the original atom is edited using the complete `before` record from that signed page; the revised atom yields a read-only final response. Run these as distinct prompts with retained ACP session identity, and check each Mini native receipt and readback. This mode is a protocol fixture, not an instruction-following model.
