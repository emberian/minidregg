//! # mini-sdk — the Mini client SDK
//!
//! ```text
//! Profile ─► Intent (one typed cut) ─► explain() ─► Confirmation (nonce-bound)
//!          ─► sign (only consent-host headers, only with the Confirmation) ─► sealed call
//!          ─► submit ─► Receipt | Refused | Uncertain ─► lookup (the SAME call, never a new nonce)
//! ```
//!
//! Two nouns: [`custody::Receipt`] (exactly the Host's `NativeHostCodec.Receipt` presentation)
//! and [`custody::Attempt`] (one retained exact call and its classified outcome).
//!
//! # Trust model: CLIENT-LOCAL
//!
//! - **Runs on** the member's device. Key material never leaves it.
//! - **Trusts** the device, the member's independently selected local semantic Host image and
//!   consent executable (chosen by local custody, never by the operator), and this crate's
//!   framing and signing.
//! - **Does not trust** the operator socket (its challenge and plan are offers that the Lean
//!   consent process re-derives before any key signs), served presentations (only the local
//!   Host's decoding is rendered), or other members (mediated by capabilities).
//! - **Does not** execute, prove, or decide admission. The Host executes, and re-executes on
//!   every replay; that deterministic re-execution is Mini's evidence. The plan check is the
//!   Lean `NativeClientConsent`/`NativeSpecializedConsent`, reached through
//!   [`consent`] (feature `native`); this crate never re-implements it.
//!
//! # Offline core and `native`
//!
//! With default features the crate is the OFFLINE CORE and builds on `wasm32-unknown-unknown`:
//! no Lean link, no processes, no filesystem, no sockets. Feature `native` adds the
//! consent-process client, the local Host codec client, the operator-socket client, the
//! filesystem custody store, and the end-to-end [`flow`].
#![forbid(unsafe_op_in_unsafe_fn)]

pub mod confirm;
pub mod contracts;
pub mod custody;
pub mod explain;
pub mod hex;
pub mod profile;
pub mod sign;

#[cfg(feature = "native")]
pub mod consent;
#[cfg(feature = "native")]
pub mod flow;
#[cfg(feature = "native")]
pub mod frame;
#[cfg(feature = "native")]
pub mod host;
#[cfg(feature = "native")]
pub mod operator;
#[cfg(feature = "native")]
pub mod store;

#[cfg(feature = "wasm")]
pub mod wasm;

pub use confirm::{Confirmation, Presented};
pub use contracts::{Cut, Intent, InvocationId};
pub use custody::{Attempt, Outcome, Phase, Receipt};
pub use explain::{explain, Explanation};
pub use profile::Profile;

/// SDK error: a message naming the refused step. Every refusal is a value, never a panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}
impl From<&str> for Error {
    fn from(s: &str) -> Self {
        Error(s.to_owned())
    }
}
impl From<String> for Error {
    fn from(s: String) -> Self {
        Error(s)
    }
}
pub type Result<T> = std::result::Result<T, Error>;

/// SHA-256 of `bytes`.
pub fn sha256(bytes: &[u8]) -> [u8; 32] {
    use sha2::Digest;
    sha2::Sha256::digest(bytes).into()
}
