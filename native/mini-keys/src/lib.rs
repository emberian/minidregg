//! `mini-keys`: the key broker.
//!
//! Under split tenancy (dregg-infra `/etc/mini/tenancy` = `split`) exactly one
//! account, `mini-keys`, can read the credential seal key, the sealed provider
//! keys and the Discord mirror's bot token and webhook URL. Everything that
//! needs one of them asks this broker over a Unix socket, and the broker either
//! performs the operation itself (seal a member's key, call the provider with
//! the bearer, post to the webhook, read the channel with the bot token) or
//! refuses by name. No secret is ever returned to a caller.
//!
//! A caller is named by the kernel, not by anything it says: the broker reads
//! the peer's uid and gid from the connected socket (`SO_PEERCRED` on Linux,
//! `getpeereid` on the BSDs and macOS) and maps them to roles through the
//! root-owned broker config. A role grants a fixed set of operations:
//!
//! | role       | who (split tenancy)                 | operations |
//! |------------|-------------------------------------|------------|
//! | `member`   | session accounts (group mini-sessions) | `member-action` (the signed key-service exchange) |
//! | `provider` | the Hermes controller (`mini-core`) | `provider-authorize`, `provider-forward`, `provider-verify-grant`, `provider-selected-choice` |
//! | `discord`  | the Discord mirror's session account | `discord-post`, `discord-read` |
//! | `operator` | root                                | `pool` |
//!
//! Every request is one line in the broker's audit log (who, role, operation,
//! outcome, named refusal; digests, never secrets).
//!
//! The crate's default feature `server` is the broker; clients depend on it
//! with `default-features = false` and get [`wire`], [`peer`] and [`client`].

pub mod client;
pub mod peer;
pub mod wire;

#[cfg(feature = "server")]
pub mod server;
