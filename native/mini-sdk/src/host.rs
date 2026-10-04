//! The member's local semantic Host as a pure codec (ops 7–11): it authors and decodes the
//! canonical bytes; this crate never does. Selected by local custody (`MINI_LOCAL_HOST`).
use std::path::Path;

use serde_json::Value;

use crate::frame::{kind, pair, Process};
use crate::Result;

pub struct LocalHost(Process);

impl LocalHost {
    pub fn start(executable: &Path, settings: &Path) -> Result<Self> {
        Process::start(executable, settings).map(LocalHost)
    }
    /// Op 7: canonical bytes of the authoring JSON `source` of `kind` (e.g. `intent`).
    pub fn author(&mut self, kind_name: &str, source: &[u8]) -> Result<Vec<u8>> {
        self.0.call(7, &kind(kind_name, source)?)
    }
    /// Op 8: the Host's own presentation of canonical bytes of `kind`.
    pub fn inspect(&mut self, kind_name: &str, bytes: &[u8]) -> Result<Value> {
        let out = self.0.call(8, &kind(kind_name, bytes)?)?;
        serde_json::from_slice(&out).map_err(|e| format!("Host presentation is not JSON: {e}").into())
    }
    /// Op 9: the canonical signature list from its JSON spelling.
    pub fn signatures(&mut self, json: &str) -> Result<Vec<u8>> {
        self.0.call(9, json.as_bytes())
    }
    /// Op 10: a signed observation from a challenge and its signatures.
    pub fn observe_assemble(&mut self, challenge: &[u8], signatures: &[u8]) -> Result<Vec<u8>> {
        self.0.call(10, &pair(challenge, signatures)?)
    }
    /// Op 11: the exact call from a plan and its signatures.
    pub fn assemble(&mut self, plan: &[u8], signatures: &[u8]) -> Result<Vec<u8>> {
        self.0.call(11, &pair(plan, signatures)?)
    }
}
