//! Attempt custody: ONE state machine for "an exact call, and what became of it".
//!
//! SHARED-CONTRACTS separation #11: the [`InvocationId`] is the semantic request; an attempt
//! number, its command nonce and its intent nonce are distinct, related identities. A lost
//! reply is answered by exact lookup of the SAME call bytes. A successor attempt with fresh
//! nonces is permitted only where the call certainly never reached the Host (never sealed, or
//! never forwarded). (Scout D: bugs D2/D5/D7 were divergences between copies of this machine.)
//!
//! A Host `refused` answer is terminal for the attempt but does NOT license a successor: Lean
//! declares no no-effect class on `Outcome` yet, and a retained history shows a confirmation can
//! follow a refusal of the same call (see [`standing`]). Until the Host answers a proven no-append
//! outcome with its positive no-record frame (the Lean lane's `NO_RECORD`; review questions Q1,
//! Q2, Q9 in `docs/review/2026-10-26-native-crates/resource-client.md` §8.1–8.2), a refused attempt
//! is reported and stops; a new operation is the member's own new decision.
//!
//! A `confirmed` answer with `disposition: "charged"` (an Objective call admitted with only its
//! price posted, `Host/Json.lean` `.charged`) is terminal and is NOT a success: [`Outcome::Charged`].
//!
//! ```text
//! Drafted ─prepared─► Prepared ─sealed(call)─► Sealed ─transmit─► Confirmed | Charged | Refused | Uncertain
//! Sealed | Uncertain ─lookup(same call)─► Confirmed | Charged | Refused | Uncertain
//! Drafted | Prepared | NeverSent ─successor(fresh nonces)─► Drafted(attempt + 1)
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
    /// The call is admitted and only its price was posted; nothing else was written. `cause` is
    /// the Host's own `cause` field. Terminal (never resent), and not a success.
    Charged { receipt: Receipt, cause: Value },
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
            (Some(c), Some(t), Some(e), Some(a), Some(w)) if CONFIRMATIONS.contains(&c.as_str()) => {
                let receipt = Receipt { confirmation: c, transaction_id: t, event_id: e, accepted_count: a, world_root: w };
                match v.get("disposition") {
                    None => Outcome::Confirmed(receipt),
                    Some(d) if d == "charged" => Outcome::Charged { receipt, cause: v.get("cause").cloned().unwrap_or(Value::Null) },
                    // A disposition this machine does not know is not a success it can claim.
                    Some(_) => Outcome::Undecided(v.clone()),
                }
            }
            _ => Outcome::Undecided(v.clone()),
        },
        Some("refused") => Outcome::Refused(v.clone()),
        _ => Outcome::Undecided(v.clone()),
    }
}

/// What a RETAINED history says about an exact call, by the Host's own words and nothing else
/// (reading evidence off disk, not building a typed receipt): any element that is `confirmed` with
/// a known confirmation word is the confirmation point and is returned verbatim (as `Charged` when
/// its disposition is `charged`); otherwise the NEWEST element being a refusal is terminal;
/// otherwise the call is pending (look it up). This is the rule of
/// `workspace.rs::retained_attempt_outcome`; [`classify`] refines it for the typed flow by also
/// requiring the five receipt fields.
#[derive(Debug, Clone, PartialEq)]
pub enum Standing {
    Confirmed(Value),
    /// Admitted with only its price posted: terminal, not a success.
    Charged(Value),
    Refused,
    Pending,
}

pub fn standing(history: &[Value]) -> Standing {
    let confirmed = |v: &Value| {
        v.get("type").and_then(Value::as_str) == Some("confirmed")
            && v.get("confirmation").and_then(Value::as_str).is_some_and(|c| CONFIRMATIONS.contains(&c))
    };
    if let Some(v) = history.iter().rev().find(|v| confirmed(v)) {
        return match v.get("disposition") {
            None => Standing::Confirmed(v.clone()),
            Some(d) if d == "charged" => Standing::Charged(v.clone()),
            Some(_) => Standing::Pending,
        };
    }
    match history.last() {
        Some(v) if v.get("type").and_then(Value::as_str) == Some("refused") => Standing::Refused,
        _ => Standing::Pending,
    }
}

/// Classify a retained outcome history (oldest first): any confirmation wins; otherwise only
/// the NEWEST outcome being a refusal is terminal; otherwise undecided. (The rule of
/// `workspace.rs::retained_attempt_outcome`.)
pub fn classify(history: &[Value]) -> Option<Outcome> {
    for v in history.iter().rev() {
        if let o @ (Outcome::Confirmed(_) | Outcome::Charged { .. }) = outcome_of(v) {
            return Some(o);
        }
    }
    history.last().map(outcome_of)
}

/// What came back from one transmission of a sealed call.
#[derive(Debug, Clone, PartialEq)]
pub enum Transmission {
    /// The Host answered with this outcome presentation (the operation's own reply, or a
    /// `NO_RECORD` frame: decided).
    Answered(Value),
    /// The Host answered under its `HOST_OUTCOME` envelope (255): undecided whatever it decodes
    /// to (the exact call may be admitted); the attempt stays uncertain and is looked up.
    Envelope(Value),
    /// Certainly never forwarded to the Host (connect failed, or the socket's 254 refusal).
    Unsent(String),
    /// Written, but no decided reply: the call may or may not be admitted.
    Uncertain(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Phase {
    Drafted,
    Prepared,
    /// The exact call is retained before any transmission.
    Sealed { call_sha256: [u8; 32] },
    Uncertain { call_sha256: [u8; 32], detail: String },
    Confirmed { call_sha256: [u8; 32], receipt: Receipt },
    Charged { call_sha256: [u8; 32], receipt: Receipt, cause: Value },
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
                Outcome::Charged { receipt, cause } => Phase::Charged { call_sha256: sha, receipt, cause },
                Outcome::Refused(refusal) => Phase::Refused { call_sha256: sha, refusal },
                Outcome::Undecided(v) => Phase::Uncertain { call_sha256: sha, detail: v.to_string() },
            },
            // A call that may have travelled before stays uncertain even if THIS send did not.
            Transmission::Envelope(v) => Phase::Uncertain { call_sha256: sha, detail: v.to_string() },
            Transmission::Unsent(detail) if was_uncertain => Phase::Uncertain { call_sha256: sha, detail },
            Transmission::Unsent(detail) => Phase::NeverSent { call_sha256: sha, detail },
            Transmission::Uncertain(detail) => Phase::Uncertain { call_sha256: sha, detail },
        };
        Ok(&self.phase)
    }

    /// A new attempt of the same invocation, with fresh nonces; only where the call certainly
    /// never reached the Host: before any call was sealed, or never forwarded.
    pub fn successor(&self, intent_nonce: Dec, command_nonce: Dec) -> Result<Attempt> {
        match self.phase {
            Phase::Drafted | Phase::Prepared | Phase::NeverSent { .. } => {}
            Phase::Sealed { .. } | Phase::Uncertain { .. } => {
                return Err("the retained call may be admitted: look it up (same bytes) instead of a new attempt".into())
            }
            Phase::Refused { .. } => return Err("the Host refused this call, and no Lean-declared no-effect class says \
                the refusal left nothing behind: report it; a new operation is the member's own decision".into()),
            Phase::Confirmed { .. } => return Err("the invocation is confirmed; there is no successor".into()),
            Phase::Charged { .. } => return Err("the call was admitted and charged; a new attempt is a new paid operation".into()),
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
    /// The destination answered a send and did not take it (an HTTP refusal such as 429):
    /// nothing was delivered, so a new send may start. `attempts` sends were refused so far;
    /// `not_before` is the caller's backoff, retained with the refusal.
    Refused { attempts: u64, not_before: u64 },
    Completed(Value),
}

/// A delivery record's JSON: `{"binding", "phase": "started"|"refused"|"completed", "request", "at",
/// "evidence"?, "attempts"?, "notBefore"?}`.
/// `binding` is what the effect IS (known before it starts, so a later open can check it);
/// `request` is the identity of this one send (a nonce, a message id) that the destination can be
/// asked about, known only once the send is decided, so it lives beside the binding, not in it.
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
            if !matches!(r.get("phase").and_then(Value::as_str), Some("started" | "refused" | "completed")) {
                return Err("delivery record has no readable phase".into());
            }
        }
        Ok(Delivery { binding, record })
    }

    pub fn state(&self) -> DeliveryState {
        match &self.record {
            None => DeliveryState::Fresh,
            Some(r) if r["phase"] == "completed" => DeliveryState::Completed(r["evidence"].clone()),
            Some(r) if r["phase"] == "refused" => DeliveryState::Refused {
                attempts: r["attempts"].as_u64().unwrap_or(1),
                not_before: r["notBefore"].as_u64().unwrap_or(0),
            },
            Some(_) => DeliveryState::Unknown,
        }
    }

    /// The record to retain BEFORE the external send, naming the send (`request`). From `Fresh`,
    /// or from `Refused` once its backoff has passed (the refusal count is carried forward).
    pub fn start(&self, request: Value, at: u64) -> Result<Value> {
        match self.state() {
            DeliveryState::Fresh => Ok(json!({"binding":self.binding,"phase":"started","request":request,"at":at})),
            DeliveryState::Refused { attempts, not_before } if at >= not_before => Ok(json!({"binding":self.binding,
                "phase":"started","request":request,"at":at,"attempts":attempts})),
            DeliveryState::Refused { not_before, .. } => Err(format!("delivery refused by the destination; backing off until {not_before}").into()),
            DeliveryState::Unknown => Err("delivery UNKNOWN: inspect the destination and resolve before continuing; never re-sent automatically".into()),
            DeliveryState::Completed(_) => Err("delivery already completed".into()),
        }
    }

    /// The record after destination evidence (a 2xx, or an operator's destination lookup).
    pub fn complete(&self, evidence: Value, at: u64) -> Result<Value> {
        match self.state() {
            DeliveryState::Unknown => Ok(json!({"binding":self.binding,"phase":"completed",
                "request":self.record.as_ref().map_or(Value::Null, |r| r["request"].clone()),"evidence":evidence,"at":at})),
            DeliveryState::Fresh | DeliveryState::Refused { .. } => Err("cannot complete a delivery that was never started".into()),
            DeliveryState::Completed(_) => Err("delivery already completed".into()),
        }
    }

    /// The record after the destination ANSWERED the started send with a refusal (it did not
    /// take it): back to a state a new send may start from, no earlier than `not_before`. Only
    /// from `Unknown`; a send whose answer was lost stays `Unknown`.
    pub fn refused(&self, evidence: Value, at: u64, not_before: u64) -> Result<Value> {
        match self.state() {
            DeliveryState::Unknown => {
                let record = self.record.as_ref().expect("an unknown delivery has a record");
                Ok(json!({"binding":self.binding,"phase":"refused","request":record["request"].clone(),
                    "evidence":evidence,"at":at,"notBefore":not_before,
                    "attempts":record["attempts"].as_u64().unwrap_or(0) + 1}))
            }
            _ => Err("only a started delivery can be refused by its destination".into()),
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
    fn a_refusal_is_terminal_and_licenses_no_successor() {
        let mut a = sealed();
        a.record(b"call", Transmission::Answered(json!({"type":"refused","reason":"staleRoot"}))).unwrap();
        assert!(matches!(a.phase, Phase::Refused { .. }));
        assert!(a.successor(d("11"), d("21")).unwrap_err().0.contains("no-effect"));
        // Only a call that never reached the Host has a successor, and only with fresh nonces.
        let mut b = sealed();
        b.record(b"call", Transmission::Unsent("connect refused".into())).unwrap();
        assert!(b.successor(d("10"), d("21")).is_err());
        assert!(b.successor(d("11"), d("20")).is_err());
        let c = b.successor(d("11"), d("21")).unwrap();
        assert_eq!((c.number, c.invocation, c.phase.clone()), (2, b.invocation, Phase::Drafted));
    }

    #[test]
    fn an_envelope_answer_is_undecided_whatever_it_decodes_to() {
        let mut a = sealed();
        a.record(b"call", Transmission::Envelope(json!({"type":"refused","reason":"staleRoot"}))).unwrap();
        assert!(matches!(a.phase, Phase::Uncertain { .. }));
        assert!(a.successor(d("11"), d("21")).unwrap_err().0.contains("look it up"));
        // The exact lookup decides it.
        assert!(matches!(a.record(b"call", Transmission::Answered(confirmed("replayed"))).unwrap(), Phase::Confirmed { .. }));
    }

    #[test]
    fn a_charged_failure_is_terminal_and_never_a_confirmation() {
        let mut charged = confirmed("installed");
        charged["disposition"] = json!("charged");
        charged["cause"] = json!("exhausted");
        assert!(matches!(outcome_of(&charged), Outcome::Charged { ref cause, .. } if cause == "exhausted"));
        let mut a = sealed();
        a.record(b"call", Transmission::Answered(charged.clone())).unwrap();
        assert!(matches!(a.phase, Phase::Charged { .. }));
        assert!(a.successor(d("11"), d("21")).is_err());
        assert!(a.record(b"call", Transmission::Answered(confirmed("installed"))).is_err(), "terminal");
        assert_eq!(standing(&[charged.clone()]), Standing::Charged(charged.clone()));
        assert!(matches!(classify(&[charged.clone()]), Some(Outcome::Charged { .. })));
        // An unknown disposition is no success either.
        let mut odd = confirmed("installed");
        odd["disposition"] = json!("partial");
        assert!(matches!(outcome_of(&odd), Outcome::Undecided(_)));
        assert_eq!(standing(&[odd]), Standing::Pending);
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
    fn standing_is_the_words_alone_while_classify_also_wants_the_receipt() {
        let word_only = json!({"type":"confirmed","confirmation":"installed"});
        let refused = json!({"type":"refused","reason":"staleRoot"});
        let uncertain = json!({"type":"uncertain"});
        // A known word is a confirmation point for the retained reading, wherever it sits ...
        assert_eq!(standing(&[word_only.clone(), uncertain.clone()]), Standing::Confirmed(word_only.clone()));
        assert_eq!(standing(&[refused.clone(), word_only.clone(), refused.clone()]), Standing::Confirmed(word_only.clone()));
        // ... but not for the typed flow: a confirmation without its receipt fields is undecided.
        assert!(matches!(classify(&[word_only.clone()]), Some(Outcome::Undecided(_))));
        // Otherwise only the NEWEST refusal is terminal; an unknown word or an empty history is pending.
        assert_eq!(standing(&[uncertain.clone(), refused.clone()]), Standing::Refused);
        assert_eq!(standing(&[refused, uncertain]), Standing::Pending);
        assert_eq!(standing(&[json!({"type":"confirmed","confirmation":"absent"})]), Standing::Pending);
        assert_eq!(standing(&[]), Standing::Pending);
    }

    #[test]
    fn delivery_unknown_is_resolved_only_by_evidence_never_by_resending() {
        let binding = json!({"source":"42:7","destination":"webhook"});
        let fresh = Delivery::open(binding.clone(), None).unwrap();
        let started = fresh.start(json!({"nonce":"ab"}), 1).unwrap();
        let unknown = Delivery::open(binding.clone(), Some(started)).unwrap();
        assert_eq!(unknown.state(), DeliveryState::Unknown);
        assert!(unknown.start(json!({"nonce":"cd"}), 2).unwrap_err().0.contains("UNKNOWN"));
        let done = unknown.complete(json!({"http":204}), 3).unwrap();
        assert_eq!(done["request"], json!({"nonce":"ab"}), "completion keeps the identity of the send it resolves");
        let done = Delivery::open(binding, Some(done)).unwrap();
        assert_eq!(done.state(), DeliveryState::Completed(json!({"http":204})));
        assert!(done.start(json!(null), 4).is_err());
        assert!(Delivery::open(json!({"other":1}), done.record).is_err());
    }

    #[test]
    fn a_destination_refusal_returns_to_a_startable_state_after_its_backoff() {
        let binding = json!({"source":"42:8","destination":"webhook"});
        let started = Delivery::open(binding.clone(), None).unwrap().start(json!({"n":1}), 10).unwrap();
        let refused = Delivery::open(binding.clone(), Some(started)).unwrap().refused(json!({"http":429}), 11, 70).unwrap();
        let refused = Delivery::open(binding.clone(), Some(refused)).unwrap();
        assert_eq!(refused.state(), DeliveryState::Refused { attempts: 1, not_before: 70 });
        assert!(refused.start(json!({"n":2}), 69).is_err(), "not before the backoff");
        assert!(refused.complete(json!({}), 69).is_err());
        let again = Delivery::open(binding.clone(), Some(refused.start(json!({"n":2}), 70).unwrap())).unwrap();
        assert_eq!(again.state(), DeliveryState::Unknown);
        let twice = Delivery::open(binding.clone(), Some(again.refused(json!({"http":429}), 71, 200).unwrap())).unwrap();
        assert_eq!(twice.state(), DeliveryState::Refused { attempts: 2, not_before: 200 });
        assert!(Delivery::open(binding, None).unwrap().refused(json!({}), 1, 2).is_err());
    }
}
