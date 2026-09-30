//! The PAY watcher (PAY.md §3): a stateless process that turns finalized Solana transfers into
//! `Observation` records (PAY.md §2.4) for the kernel's observation ingress.
//!
//! One run: read the finalized tip, then for every book index ask every configured endpoint
//! for the token accounts the book address owns for the asset's mint, their signature
//! histories (paged back to a retained receipt or the page bound), and each transaction's
//! `jsonParsed` balances. A transfer is emitted only when EVERY endpoint returns the same
//! record for it. There is no cursor and no ledger: the only memory is the retained-receipt
//! directory the caller supplies, and the kernel's nullifier refusal is what makes a
//! resubmission harmless.
//!
//! The decoding is a port of Bread's `RpcTransferFetcher` (`discord-bot/src/pay.rs`) and the
//! re-checks of `SignatureWatcher::poll` (`dregg-pay/src/watcher.rs`), with the token program
//! a per-asset value and every attribution mismatch a named refusal rather than a silent skip.

pub mod config;
pub mod decode;
pub mod model;
pub mod transport;
pub mod watch;

pub use config::{Asset, BookEntry, Config};
pub use model::{Clock, Event, EventKind, Observation, Reason, Refusal};
pub use transport::{CurlTransport, FixtureTransport, Transport};
pub use watch::{load_receipts, run, Report};
