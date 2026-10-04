//! Attempt custody: ONE state machine for "an exact call, and what became of it".
//!
//! SHARED-CONTRACTS separation #11: the [`InvocationId`] is the semantic request; an attempt
//! number, its command nonce and its intent nonce are distinct, related identities. A lost
//! reply is answered by exact lookup of the SAME call bytes; only a definite non-admission
//! (a Host refusal, or a call never transmitted) permits a successor attempt with fresh nonces.
//! (Scout D: bugs D2/D5/D7 were divergences between copies of this machine.)
//!
//! ```text
//! Drafted ─prepared─► Prepared ─sealed(call)─► Sealed ─transmit─► Confirmed | Refused | Uncertain
//! Sealed | Uncertain ─lookup(same call)─► Confirmed | Refused | Uncertain
//! Drafted | Prepared | NeverSent | Refused ─successor(fresh nonces)─► Drafted(attempt + 1)
//! ```
//!
//! [`Delivery`] is the same discipline for an EXTERNAL destination (a webhook post): a started
//! delivery that did not complete is `Unknown` and is resolved only by destination evidence,
//! never by re-sending. Destination custody is not Mini custody.
use serde_json::{json, Value};

use crate::contracts::{Dec, InvocationId};
use crate::{sha256, Error, Result};

/// Exactly the Host's `inspect outcome` presentation of `NativeHostCodec.Receipt`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Receipt {
    /// `installed`, `replayed` or `recoveredAfterUncertainResponse`.
    pub confirmation: String,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub world_root: String,
}

/// Confirmations that mean the exact call is admitted.
pub const CONFIRMATIONS: &[&str] = &["installed", "replayed", "recoveredAfterUncertainResponse"];

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Confirmed(Receipt),
    /// The Host decided not to admit this call (the decoded refusal is retained).
    Refused(Value),
    /// The Host answered, but not with a decision this machine reads as final.
    Undecided(Value),
}

/// Read one Host outcome presentation.
pub fn outcome_of(v: &Value) -> Outcome {
    let s = |k: &str| v.get(k).and_then(Value::as_str).map(str::to_owned);
    match v.get("type").and_then(Value::as_str) {
        Some("confirmed") => match (s("confirmation"), s("transactionId"), s("eventId"), s("acceptedCount"), s("worldRoot")) {
            (Some(c), Some(t), Some(e), Some(a), Some(w)) if CONFIRMATIONS.contains(&c.as_str()) => Outcome::Confirmed(
                Receipt { confirmation: c, transaction_id: t, event_id: e, accepted_count: a, world_root: w }),
            _ => Outcome::Undecided(v.clone()),
        },
        Some("refused") => Outcome::Refused(v.clone()),
        _ => Outcome::Undecided(v.clone()),
    }
}

/// Classify a retained outcome history (oldest first): any confirmation wins; otherwise only
/// the NEWEST outcome being a refusal is terminal; otherwise undecided. (The rule of
/// `workspace.rs::retained_attempt_outcome`.)
pub fn classify(history: &[Value]) -> Option<Outcome> {
    for v in history.iter().rev() {
        if let Outcome::Confirmed(r) = outcome_of(v) {
            return Some(Outcome::Confirmed(r));
        }
    }
    history.last().map(outcome_of)
}

/// What came back from one transmission of a sealed call.
#[derive(Debug, Clone, PartialEq)]
pub enum Transmission {
    /// The Host answered with this outcome presentation.
    Answered(Value),
    /// Certainly never forwarded to the Host (connect failed, or the socket's 254 refusal).
    Unsent(String),
    /// Written, but no decided reply: the call may or may not be admitted.
    Uncertain(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Phase {
    Drafted,
    Prepared,
    /// The exact call is retained (fsynced) before any transmission.
    Sealed { call_sha256: [u8; 32] },
    Uncertain { call_sha256: [u8; 32], detail: String },
    Confirmed { call_sha256: [u8; 32], receipt: Receipt },
    Refused { call_sha256: [u8; 32], refusal: Value },
    NeverSent { call_sha256: [u8; 32], detail: String },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Attempt {
    pub invocation: InvocationId,
    pub number: u32,
    pub intent_nonce: Dec,
    pub command_nonce: Dec,
    pub phase: Phase,
}

impl Attempt {
    pub fn first(invocation: InvocationId, intent_nonce: Dec, command_nonce: Dec) -> Self {
        Attempt { invocation, number: 1, intent_nonce, command_nonce, phase: Phase::Drafted }
    }

    pub fn prepared(&mut self) -> Result<()> {
        match self.phase {
            Phase::Drafted => {
                self.phase = Phase::Prepared;
                Ok(())
            }
            _ => Err(self.refuse("prepare")),
        }
    }

    /// The exact call bytes are durably retained; from now on only these bytes may travel.
    pub fn sealed(&mut self, call: &[u8]) -> Result<()> {
        match self.phase {
            Phase::Prepared => {
                self.phase = Phase::Sealed { call_sha256: sha256(call) };
                Ok(())
            }
            _ => Err(self.refuse("seal")),
        }
    }

    /// The SHA-256 of the one call this attempt may (re)transmit or look up.
    pub fn call(&self) -> Option<[u8; 32]> {
        match &self.phase {
            Phase::Sealed { call_sha256 } | Phase::Uncertain { call_sha256, .. } => Some(*call_sha256),
            _ => None,
        }
    }

    /// Record a transmission (`submit`) or an exact lookup of `call`. Refuses any other bytes.
    pub fn record(&mut self, call: &[u8], t: Transmission) -> Result<&Phase> {
        let sha = self.call().ok_or_else(|| self.refuse("transmit or look up"))?;
        if sha256(call) != sha {
            return Err(Error("these are not the attempt's retained call bytes; never transmit another call under this attempt".into()));
        }
        let was_uncertain = matches!(self.phase, Phase::Uncertain { .. });
        self.phase = match t {
            Transmission::Answered(v) => match outcome_of(&v) {
                Outcome::Confirmed(receipt) => Phase::Confirmed { call_sha256: sha, receipt },
                Outcome::Refused(refusal) => Phase::Refused { call_sha256: sha, refusal },
                Outcome::Undecided(v) => Phase::Uncertain { call_sha256: sha, detail: v.to_string() },
            },
            // A call that may have travelled before stays uncertain even if THIS send did not.
            Transmission::Unsent(detail) if was_uncertain => Phase::Uncertain { call_sha256: sha, detail },
            Transmission::Unsent(detail) => Phase::NeverSent { call_sha256: sha, detail },
            Transmission::Uncertain(detail) => Phase::Uncertain { call_sha256: sha, detail },
        };
        Ok(&self.phase)
    }

    /// A new attempt of the same invocation, with fresh nonces; only after a definite
    /// non-admission or before any call was sealed.
    pub fn successor(&self, intent_nonce: Dec, command_nonce: Dec) -> Result<Attempt> {
        match self.phase {
            Phase::Drafted | Phase::Prepared | Phase::NeverSent { .. } | Phase::Refused { .. } => {}
            Phase::Sealed { .. } | Phase::Uncertain { .. } => {
                return Err("the retained call may be admitted: look it up (same bytes) instead of a new attempt".into())
            }
            Phase::Confirmed { .. } => return Err("the invocation is confirmed; there is no successor".into()),
        }
        if command_nonce == self.command_nonce || intent_nonce == self.intent_nonce {
            return Err("a successor attempt needs fresh nonces".into());
        }
        let number = self.number.checked_add(1).ok_or("attempt numbers exhausted")?;
        Ok(Attempt { invocation: self.invocation, number, intent_nonce, command_nonce, phase: Phase::Drafted })
    }

    fn refuse(&self, step: &str) -> Error {
        Error(format!("attempt {} of {} cannot {step} from {:?}", self.number, self.invocation.hex(), self.phase))
    }
}

/// External delivery custody (one record per destination effect).
#[derive(Debug, Clone, PartialEq)]
pub enum DeliveryState {
    /// No record: nothing was started.
    Fresh,
    /// Started and not completed: the destination may or may not have it.
    Unknown,
    Completed(Value),
}

/// A delivery record's JSON: `{"binding", "phase": "started"|"completed", "evidence"?}`.
#[derive(Debug, Clone, PartialEq)]
pub struct Delivery {
    pub binding: Value,
    pub record: Option<Value>,
}

impl Delivery {
    /// Read a record for `binding`; a record bound to anything else refuses.
    pub fn open(binding: Value, record: Option<Value>) -> Result<Self> {
        if let Some(r) = &record {
            if r.get("binding") != Some(&binding) {
                return Err("delivery record is bound to another source or destination".into());
            }
            if !matches!(r.get("phase").and_then(Value::as_str), Some("started" | "completed")) {
                return Err("delivery record has no readable phase".into());
            }
        }
        Ok(Delivery { binding, record })
    }

    pub fn state(&self) -> DeliveryState {
        match &self.record {
            None => DeliveryState::Fresh,
            Some(r) if r["phase"] == "completed" => DeliveryState::Completed(r["evidence"].clone()),
            Some(_) => DeliveryState::Unknown,
        }
    }

    /// The record to retain BEFORE the external send. Only from `Fresh`.
    pub fn start(&self, at: u64) -> Result<Value> {
        match self.state() {
            DeliveryState::Fresh => Ok(json!({"binding":self.binding,"phase":"started","at":at})),
            DeliveryState::Unknown => Err("delivery UNKNOWN: inspect the destination and resolve before continuing; never re-sent automatically".into()),
            DeliveryState::Completed(_) => Err("delivery already completed".into()),
        }
    }

    /// The record after destination evidence (a 2xx, or an operator's destination lookup).
    pub fn complete(&self, evidence: Value, at: u64) -> Result<Value> {
        match self.state() {
            DeliveryState::Unknown => Ok(json!({"binding":self.binding,"phase":"completed","evidence":evidence,"at":at})),
            DeliveryState::Fresh => Err("cannot complete a delivery that was never started".into()),
            DeliveryState::Completed(_) => Err("delivery already completed".into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn d(s: &str) -> Dec {
        Dec::new(s).unwrap()
    }
    fn confirmed(c: &str) -> Value {
        json!({"type":"confirmed","confirmation":c,"transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"})
    }
    fn sealed() -> Attempt {
        let mut a = Attempt::first(InvocationId([1; 32]), d("10"), d("20"));
        a.prepared().unwrap();
        a.sealed(b"call").unwrap();
        a
    }

    #[test]
    fn recovered_after_uncertain_is_confirmed_by_exact_lookup_never_a_new_nonce() {
        let mut a = sealed();
        assert!(matches!(a.record(b"call", Transmission::Uncertain("reply lost".into())).unwrap(), Phase::Uncertain { .. }));
        // D7: a lost reply never licenses a fresh nonce.
        assert!(a.successor(d("11"), d("21")).unwrap_err().0.contains("look it up"));
        // Another call under this attempt refuses.
        assert!(a.record(b"other", Transmission::Answered(confirmed("installed"))).is_err());
        let p = a.record(b"call", Transmission::Answered(confirmed("recoveredAfterUncertainResponse"))).unwrap();
        assert!(matches!(p, Phase::Confirmed { receipt, .. } if receipt.confirmation == "recoveredAfterUncertainResponse"));
        assert!(a.successor(d("11"), d("21")).is_err());
    }

    #[test]
    fn refused_permits_one_successor_with_fresh_nonces_only() {
        let mut a = sealed();
        a.record(b"call", Transmission::Answered(json!({"type":"refused","reason":"staleRoot"}))).unwrap();
        assert!(a.successor(d("10"), d("21")).is_err());
        assert!(a.successor(d("11"), d("20")).is_err());
        let b = a.successor(d("11"), d("21")).unwrap();
        assert_eq!((b.number, b.invocation, b.phase.clone()), (2, a.invocation, Phase::Drafted));
    }

    #[test]
    fn unsent_is_never_sent_but_unsent_after_uncertain_stays_uncertain() {
        let mut a = sealed();
        a.record(b"call", Transmission::Unsent("connect refused".into())).unwrap();
        assert!(matches!(a.phase, Phase::NeverSent { .. }));
        assert!(a.successor(d("11"), d("21")).is_ok());
        let mut b = sealed();
        b.record(b"call", Transmission::Uncertain("write".into())).unwrap();
        b.record(b"call", Transmission::Unsent("connect refused".into())).unwrap();
        assert!(matches!(b.phase, Phase::Uncertain { .. }));
    }

    #[test]
    fn unknown_confirmation_words_and_malformed_receipts_are_undecided() {
        assert!(matches!(outcome_of(&confirmed("probably")), Outcome::Undecided(_)));
        assert!(matches!(outcome_of(&json!({"type":"confirmed","confirmation":"installed"})), Outcome::Undecided(_)));
        let mut a = sealed();
        a.record(b"call", Transmission::Answered(confirmed("probably"))).unwrap();
        assert!(matches!(a.phase, Phase::Uncertain { .. }));
    }

    #[test]
    fn classification_confirmation_wins_then_newest_refusal() {
        let refused = json!({"type":"refused"});
        let pending = json!({"type":"pending"});
        assert!(matches!(classify(&[confirmed("installed"), refused.clone()]), Some(Outcome::Confirmed(_))));
        assert!(matches!(classify(&[pending.clone(), refused.clone()]), Some(Outcome::Refused(_))));
        assert!(matches!(classify(&[refused, pending]), Some(Outcome::Undecided(_))));
        assert_eq!(classify(&[]), None);
    }

    #[test]
    fn delivery_unknown_is_resolved_only_by_evidence_never_by_resending() {
        let binding = json!({"source":"42:7","destination":"webhook"});
        let fresh = Delivery::open(binding.clone(), None).unwrap();
        let started = fresh.start(1).unwrap();
        let unknown = Delivery::open(binding.clone(), Some(started)).unwrap();
        assert_eq!(unknown.state(), DeliveryState::Unknown);
        assert!(unknown.start(2).unwrap_err().0.contains("UNKNOWN"));
        let done = unknown.complete(json!({"http":204}), 3).unwrap();
        let done = Delivery::open(binding, Some(done)).unwrap();
        assert_eq!(done.state(), DeliveryState::Completed(json!({"http":204})));
        assert!(done.start(4).is_err());
        assert!(Delivery::open(json!({"other":1}), done.record).is_err());
    }
}
