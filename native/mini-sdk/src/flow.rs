//! The authorized flow end to end, over the member's local Host, local consent process and
//! the operator socket. The steps are `resource-client`'s `submit_once`, with custody as one
//! [`Attempt`] and signing gated by [`Confirmation`]:
//!
//! 1. author `intent.bin` (local Host op 7) from the lowered intent;
//! 2. consent op 220, then sign the intent; operator `challenge` (op 4);
//! 3. consent op 221 → observation headers; sign; Host ops 9, 10 → signed observation;
//! 4. operator `prepare` (op 1) → `plan.bin`; Host `inspect plan`; consent op 222 → headers;
//! 5. [`Presented`] (with `explain()`) → the member confirms →
//! 6. sign the headers; Host ops 9, 11 → the exact call; retain it (fsync) — [`Attempt::sealed`];
//! 7. operator `submit` (op 2) → outcome; a lost reply → `lookup` (op 3) of the SAME call.
use serde_json::Value;

use crate::confirm::{Confirmation, Presented};
use crate::consent::Consent;
use crate::contracts::{Intent, Lowering};
use crate::custody::{Attempt, Phase, Transmission};
use crate::host::LocalHost;
use crate::operator::{op, Failure, Operator, Reply};
use crate::sign::{sign_intent, sign_observation_headers, sign_transaction, signatures_json};
use crate::signer::Signer;
use crate::store::AttemptDir;
use crate::{Error, Result};

pub struct Client {
    pub host: LocalHost,
    pub consent: Consent,
    pub operator: Operator,
    pub key: Box<dyn Signer>,
}

/// A prepared attempt awaiting the member's confirmation.
pub struct Prepared {
    pub attempt: Attempt,
    pub presented: Presented,
    pub intent_json: Value,
    pub plan_json: Value,
}

fn operator_answer(r: std::result::Result<Reply, Failure>, host: &mut LocalHost, what: &str) -> Result<Vec<u8>> {
    match r {
        Ok(Reply::Answer(b)) => Ok(b),
        Ok(Reply::Refused(b)) => {
            let decoded = host.inspect("outcome", &b).map(|v| v.to_string()).unwrap_or_else(|_| "undecoded".into());
            Err(Error(format!("host refused {what}: {decoded}")))
        }
        Err(Failure::Unsent(d)) | Err(Failure::Uncertain(d)) => Err(Error(format!("{what}: {d}"))),
    }
}

impl Client {
    /// Steps 1–5 for `attempt` (fresh from [`Attempt::first`] or [`Attempt::successor`]).
    pub fn prepare(&mut self, intent: &Intent, mut attempt: Attempt, domain: &crate::contracts::Dec) -> Result<Prepared> {
        if intent.invocation_id()? != attempt.invocation {
            return Err("attempt belongs to another invocation".into());
        }
        let intent_json = intent.lower(&Lowering { domain: domain.clone(), intent_nonce: attempt.intent_nonce.clone(),
            command_nonce: attempt.command_nonce.clone() })?;
        let source = crate::contracts::canonical_json(&intent_json)?;
        let intent_bin = self.host.author("intent", source.as_bytes())?;
        let verifying = self.key.public_key();
        let consented = self.consent.intent(&intent_bin, &verifying)?;
        let intent_sig = sign_intent(self.key.as_ref(), &consented)?;
        let challenge = operator_answer(self.operator.call(op::CHALLENGE, &crate::frame::pair(&intent_bin, &intent_sig)?),
            &mut self.host, "challenge")?;
        let observation_headers = self.consent.observation(&intent_bin, &verifying, &intent_sig, &challenge)?;
        let sigs = self.host.signatures(&signatures_json(&sign_observation_headers(self.key.as_ref(), &observation_headers)?))?;
        let observed = self.host.observe_assemble(&challenge, &sigs)?;
        let plan_bin = operator_answer(self.operator.call(op::PREPARE, &observed), &mut self.host, "prepare")?;
        let plan_json = self.host.inspect("plan", &plan_bin)?;
        let headers = self.consent.plan(&intent_bin, &verifying, &plan_bin)?;
        attempt.prepared()?;
        let presented = Presented::new(attempt.invocation, attempt.number, &intent_json, intent_bin, &plan_json, plan_bin, headers)?;
        Ok(Prepared { attempt, presented, intent_json, plan_json })
    }

    /// Step 6: sign under the member's confirmation and retain the exact call in `dir`.
    pub fn seal(&mut self, prepared: &mut Prepared, confirmation: &Confirmation, dir: &AttemptDir) -> Result<Vec<u8>> {
        let sigs = sign_transaction(self.key.as_ref(), &prepared.presented, confirmation)?;
        let encoded = self.host.signatures(&signatures_json(&sigs))?;
        let call = self.host.assemble(&prepared.presented.plan_bin, &encoded)?;
        dir.seal_call(&call)?;
        prepared.attempt.sealed(&call)?;
        Ok(call)
    }

    /// Step 7: transmit (`submit`) or look up (`lookup`) the attempt's exact call.
    pub fn transmit(&mut self, attempt: &mut Attempt, call: &[u8], lookup: bool) -> Result<Phase> {
        let operation = if lookup { op::LOOKUP } else { op::SUBMIT };
        let t = match self.operator.call(operation, call) {
            Ok(Reply::Answer(b)) | Ok(Reply::Refused(b)) => match self.host.inspect("outcome", &b) {
                Ok(v) => Transmission::Answered(v),
                Err(e) => Transmission::Uncertain(format!("outcome undecoded by the local Host: {e}")),
            },
            Err(Failure::Unsent(d)) => Transmission::Unsent(d),
            Err(Failure::Uncertain(d)) => Transmission::Uncertain(d),
        };
        attempt.record(call, t).cloned()
    }
}
