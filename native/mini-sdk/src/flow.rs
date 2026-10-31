//! The signing path, end to end, over one attempt directory. This is the path `mini` signs every
//! ordinary intent with (moved here from `resource-client`'s `authorize_observation` and
//! `submit_once`), so the CLI and any other client share one order of steps, one set of signed
//! bytes and one custody layout:
//!
//! 1. [`Flow::observe`]: the intent is authored (local codec op 7) or copied as `intent.bin`; the
//!    consent provider confirms the key is the intent subject's current one (220) before the
//!    intent signature `intent-signature.bin` is released; the operator answers `challenge.bin`
//!    (op 4), the local codec presents it (`challenge.json`); consent names the challenge headers
//!    the intent permits (221); they are signed (`observation-signatures.{json,bin}`, op 9) and
//!    assembled (op 10) into `signed-observation.bin`.
//! 2. [`Flow::prepare`]: the operator plans (op 1) into `plan.bin`.
//! 3. [`Flow::present`]: the local codec presents a plan (op 8, `plan.json`).
//! 4. [`Flow::seal`]: consent names the plan headers the intent permits (222, or thin 232); the
//!    caller's release sees exactly what would be signed; the headers are signed
//!    (`transaction-signatures.{json,bin}`), assembled (op 11) into `call.bin`, and the attempt's
//!    nothing else is written before it can be transmitted.
//! 5. [`Flow::transmit`]: the exact retained call is submitted (op 2) or looked up (op 3), and the
//!    local codec presents the answer. A lost reply is answered by looking up the SAME call
//!    ([`crate::custody`]), never by a new one.
//!
//! A signed read is step 1 and then [`Flow::query`] (op 5, `view.bin`, presented as `view.json`).
//!
//! The steps are separate so a caller may interpose between them (the CLI's provider continuity
//! guard sits between 2 and 4). Each step reads and writes only files of its
//! [`crate::attempt::Attempt`]: on disk as each is made for a write, so the directory is the
//! custody record; in memory for a read, written to the directory only when something needs a
//! path (a one-shot Host, a refusal's record). The member's local side ([`Local`]: codec and consent) and
//! the operator side ([`Operator`]) are traits: the CLI implements them over its process-wide
//! codec child and consent provider and its pinned transport; [`Member`] implements them over
//! this crate's own [`crate::local::Codec`], [`crate::consent::Consent`] and
//! [`crate::operator::Operator`].
//!
//! **Release.** [`Flow::seal`] signs only after `release` accepts the [`Sealing`]. A UI builds a
//! [`crate::confirm::Presented`] from it and checks the member's [`crate::confirm::Confirmation`];
//! a command-line client whose member typed the command passes a release that accepts. Either
//! way the headers are exactly those the local Lean consent provider returned for this intent and
//! plan: nothing else is ever signed.
use std::path::PathBuf;

use serde_json::Value;

use crate::attempt::Attempt;
use crate::signer::Signer;
use crate::{Error, Result};

/// Where the intent comes from: a file of the attempt.
pub enum Source<'a> {
    /// Authoring source of this kind (e.g. `intent`) in the attempt file `name`, authored by the
    /// local codec into `intent.bin`.
    Authored { kind: &'a str, name: &'a str },
    /// Canonical intent bytes in the attempt file `name`, kept as `intent.bin`.
    Binary(&'a str),
}

/// The member's local processes: the storeless codec (frames 7–11) and the consent provider.
/// Each codec verb takes its inputs' bytes and answers the output's bytes.
pub trait Local {
    fn author(&mut self, kind: &str, input: &[u8]) -> Result<Vec<u8>>;
    /// The presentation, as the codec's JSON bytes.
    fn inspect(&mut self, kind: &str, input: &[u8]) -> Result<Vec<u8>>;
    fn signatures(&mut self, json: &[u8]) -> Result<Vec<u8>>;
    fn observe_assemble(&mut self, challenge: &[u8], signatures: &[u8]) -> Result<Vec<u8>>;
    fn assemble(&mut self, plan: &[u8], signatures: &[u8]) -> Result<Vec<u8>>;
    /// Consent 220: `key` is the intent subject's current key.
    fn consent_intent(&mut self, intent: &[u8], key: &[u8]) -> Result<()>;
    /// Consent 221: the challenge headers this intent permits `key` to sign.
    fn consent_observation(&mut self, intent: &[u8], signature: &[u8], challenge: &[u8], key: &[u8]) -> Result<Vec<Vec<u8>>>;
    /// Consent 222: the plan headers this intent permits `key` to sign.
    fn consent_plan(&mut self, intent: &[u8], plan: &[u8], key: &[u8]) -> Result<Vec<Vec<u8>>>;
}

/// An operator request of the flow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Request {
    /// Op 4: `(intent, intent signature)` → challenge.
    Challenge,
    /// Op 1: signed observation → plan.
    Prepare,
    /// Op 2: exact call → outcome.
    Submit,
    /// Op 3: exact call → outcome, read-only.
    Lookup,
    /// Op 5: signed observation → the observed view.
    Query,
}

impl Request {
    /// The Host verb (the one-shot command word and the session command name).
    pub fn verb(self) -> &'static str {
        match self {
            Request::Challenge => "challenge",
            Request::Prepare => "prepare",
            Request::Submit => "submit",
            Request::Lookup => "lookup",
            Request::Query => "query",
        }
    }
    pub fn operation(self) -> u8 {
        use crate::host_operations as op;
        match self {
            Request::Challenge => op::OBSERVATION_CHALLENGE,
            Request::Prepare => op::AUTHORIZED_PREPARE,
            Request::Submit => op::SUBMIT,
            Request::Lookup => op::LOOKUP,
            Request::Query => op::AUTHORIZED_QUERY,
        }
    }
}

/// How the Host framed the answer `Operator::request` wrote.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Answered {
    /// The operation's own reply.
    Answer,
    /// `NO_RECORD` (253): decided before any append; a fresh attempt is safe.
    NoRecord,
    /// `HOST_OUTCOME` (255): undecided whatever it decodes to; look the exact call up.
    Outcome,
}

/// The serving Host: `request` takes the attempt files `inputs` and creates the answer as the
/// attempt file `output`, and says how it was framed. It is given the attempt, not bytes, because
/// a one-shot Host reads and writes files and a refusal is retained beside its request. An
/// uncertain or never-forwarded transmission is an error; what it means for the attempt is the
/// caller's custody (a submit or lookup error leaves the retained call to be looked up). An
/// implementation may also report a marker frame as an error it has already classified (the
/// CLI's transport does).
pub trait Operator {
    fn request(&mut self, request: Request, attempt: &mut Attempt, inputs: &[&str], output: &str) -> Result<Answered>;
}

/// What [`Flow::seal`] would sign, shown to the caller's release before any key signs.
pub struct Sealing<'a> {
    pub intent: &'a [u8],
    pub plan: &'a [u8],
    /// The ordered headers the consent provider returned for exactly this intent and plan.
    pub headers: &'a [Vec<u8>],
}

/// One attempt and the parties that act on it.
pub struct Flow<'a, H: Local + Operator + ?Sized> {
    pub attempt: &'a mut Attempt,
    pub host: &'a mut H,
    pub signer: &'a dyn Signer,
}

fn json_bytes(value: &Value) -> Result<Vec<u8>> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| Error(format!("cannot render JSON: {e}")))?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn parse(name: &str, bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(bytes).map_err(|e| Error(format!("invalid host JSON {name}: {e}")))
}

/// The JSON list the Host's `signatures` codec (op 9) reads: each header signed, hex, in order.
pub fn signature_list(signer: &dyn Signer, headers: &[Vec<u8>]) -> Result<Value> {
    headers.iter().map(|h| Ok(Value::String(crate::hex::encode(&signer.sign(h)?)))).collect::<Result<Vec<_>>>().map(Value::Array)
}


impl<'a, H: Local + Operator + ?Sized> Flow<'a, H> {
    /// The local codec's presentation of the attempt file `input`, kept as `output`.
    pub fn inspect(&mut self, kind: &str, input: &str, output: &str) -> Result<Value> {
        let bytes = self.host.inspect(kind, &self.attempt.read(input)?)?;
        self.attempt.create(output, &bytes)?;
        parse(output, &bytes)
    }

    /// Step 1: an authorized observation of `source`, kept as `signed-observation.bin`; returns
    /// that name.
    pub fn observe(&mut self, source: Source<'_>) -> Result<&'static str> {
        let intent = match source {
            Source::Binary(name) => self.attempt.read(name)?.into_owned(),
            Source::Authored { kind, name } => {
                if self.attempt.exists("intent.bin") {
                    return Err(Error(format!("refusing to replace {}", self.attempt.dir().join("intent.bin").display())));
                }
                let input = self.attempt.read(name)?.into_owned();
                self.host.author(kind, &input)?
            }
        };
        self.attempt.create("intent.bin", &intent)?;
        // The local consent provider binds the retained intent and current subject to custody
        // before even the observation's first signature is released.
        let key = self.signer.public_key();
        self.host.consent_intent(&intent, &key)?;
        let signature = self.signer.sign(&intent)?;
        self.attempt.create("intent-signature.bin", &signature)?;
        self.host.request(Request::Challenge, self.attempt, &["intent.bin", "intent-signature.bin"], "challenge.bin")?;
        let challenge = self.attempt.read("challenge.bin")?.into_owned();
        let presented = self.host.inspect("challenge", &challenge)?;
        self.attempt.create("challenge.json", &presented)?;
        let headers = self.host.consent_observation(&intent, &signature, &challenge, &key)?;
        let list = json_bytes(&signature_list(self.signer, &headers)?)?;
        self.attempt.create("observation-signatures.json", &list)?;
        let signatures = self.host.signatures(&list)?;
        self.attempt.create("observation-signatures.bin", &signatures)?;
        let signed = self.host.observe_assemble(&challenge, &signatures)?;
        self.attempt.create("signed-observation.bin", &signed)?;
        Ok("signed-observation.bin")
    }

    /// A signed read: the Host's view of the attempt file `observation`, kept as `view.bin`, and
    /// its presentation by `inspection`, kept as `view.json`.
    pub fn query(&mut self, observation: &str, inspection: &str) -> Result<Value> {
        self.host.request(Request::Query, self.attempt, &[observation], "view.bin")?;
        self.inspect(inspection, "view.bin", "view.json")
    }

    /// Step 2: the operator's plan for `observation`, kept as `plan.bin`; returns its name.
    pub fn prepare(&mut self, observation: &str) -> Result<&'static str> {
        self.host.request(Request::Prepare, self.attempt, &[observation], "plan.bin")?;
        Ok("plan.bin")
    }

    /// Step 3: the local codec's presentation of a plan, kept as `plan_json`.
    pub fn present(&mut self, plan_bin: &str, plan_json: &str) -> Result<Value> {
        self.inspect("plan", plan_bin, plan_json)
    }

    /// Step 4: sign the consented headers of `plan_bin` after `release` accepts them, assemble the
    /// exact call into `call.bin`; returns its name.
    pub fn seal(&mut self, plan_bin: &str, release: &mut dyn FnMut(&Sealing<'_>) -> Result<()>) -> Result<&'static str> {
        let signatures = self.sign(plan_bin, release)?;
        let plan = self.attempt.read(plan_bin)?.into_owned();
        let signatures = self.attempt.read(signatures)?.into_owned();
        let call = self.host.assemble(&plan, &signatures)?;
        self.attempt.create("call.bin", &call)?;
        Ok("call.bin")
    }

    /// The signing half of [`Flow::seal`]: the consented headers of `plan_bin`, released and
    /// signed into `transaction-signatures.{json,bin}`; returns the `.bin` name. A caller that
    /// does not assemble a call (a dry run, op 130) stops here.
    pub fn sign(&mut self, plan_bin: &str, release: &mut dyn FnMut(&Sealing<'_>) -> Result<()>) -> Result<&'static str> {
        let intent = self.attempt.read("intent.bin")?.into_owned();
        let plan = self.attempt.read(plan_bin)?.into_owned();
        let headers = self.host.consent_plan(&intent, &plan, &self.signer.public_key())?;
        if headers.is_empty() {
            return Err("consent returned no headers; nothing to sign".into());
        }
        release(&Sealing { intent: &intent, plan: &plan, headers: &headers })?;
        let list = json_bytes(&signature_list(self.signer, &headers)?)?;
        self.attempt.create("transaction-signatures.json", &list)?;
        let signatures = self.host.signatures(&list)?;
        self.attempt.create("transaction-signatures.bin", &signatures)?;
        Ok("transaction-signatures.bin")
    }

    /// Step 5: submit or look up the retained `call.bin`; the answer is kept as `outcome_bin` and
    /// the local codec's presentation of it as `outcome_json`. Returns the presentation and how
    /// the Host framed it; [`Flow::transmission`] turns both into the attempt's
    /// [`crate::custody::Transmission`] (a 255 envelope is undecided whatever it decodes to).
    pub fn transmit(&mut self, request: Request, outcome_bin: &str, outcome_json: &str) -> Result<(Value, Answered)> {
        if !matches!(request, Request::Submit | Request::Lookup) {
            return Err("only an exact call is transmitted".into());
        }
        let answered = self.host.request(request, self.attempt, &["call.bin"], outcome_bin)?;
        Ok((self.inspect("outcome", outcome_bin, outcome_json)?, answered))
    }

    /// The custody reading of a transmitted answer.
    pub fn transmission(outcome: Value, answered: Answered) -> crate::custody::Transmission {
        match answered {
            Answered::Outcome => crate::custody::Transmission::Envelope(outcome),
            Answered::Answer | Answered::NoRecord => crate::custody::Transmission::Answered(outcome),
        }
    }
}

/// [`Local`] and [`Operator`] over this crate's own processes: one codec child, one consent
/// provider, and the operator socket. For a client that is not `mini`.
pub struct Member {
    pub codec: crate::local::Codec,
    pub consent: crate::consent::Consent,
    /// The member's own semantic Host image (the codec executable) and its settings.
    pub image: PathBuf,
    pub settings: PathBuf,
    pub operator: crate::operator::Operator,
}


impl Member {
    fn codec(&mut self, answer: std::result::Result<Vec<u8>, crate::local::CodecError>) -> Result<Vec<u8>> {
        match answer {
            Ok(body) => Ok(body),
            Err(crate::local::CodecError::Refused { decoded, .. }) => Err(Error(format!("local codec refused: {}",
                decoded.map_or_else(|| "undecoded".to_owned(), |v| v.to_string())))),
            Err(crate::local::CodecError::Failed(e)) => Err(Error(e)),
        }
    }
}

impl Local for Member {
    fn author(&mut self, kind: &str, input: &[u8]) -> Result<Vec<u8>> {
        let answer = self.codec.author(&self.image, &self.settings, kind, input);
        self.codec(answer)
    }
    fn inspect(&mut self, kind: &str, input: &[u8]) -> Result<Vec<u8>> {
        let answer = self.codec.inspect(&self.image, &self.settings, kind, input);
        self.codec(answer)
    }
    fn signatures(&mut self, json: &[u8]) -> Result<Vec<u8>> {
        let answer = self.codec.signatures(&self.image, &self.settings, json);
        self.codec(answer)
    }
    fn observe_assemble(&mut self, challenge: &[u8], signatures: &[u8]) -> Result<Vec<u8>> {
        let answer = self.codec.observe_assemble(&self.image, &self.settings, challenge, signatures);
        self.codec(answer)
    }
    fn assemble(&mut self, plan: &[u8], signatures: &[u8]) -> Result<Vec<u8>> {
        let answer = self.codec.assemble(&self.image, &self.settings, plan, signatures);
        self.codec(answer)
    }
    fn consent_intent(&mut self, intent: &[u8], key: &[u8]) -> Result<()> {
        self.consent.intent(intent, key, false)?;
        Ok(())
    }
    fn consent_observation(&mut self, intent: &[u8], signature: &[u8], challenge: &[u8], key: &[u8]) -> Result<Vec<Vec<u8>>> {
        Ok(self.consent.observation(intent, key, signature, challenge, false)?)
    }
    fn consent_plan(&mut self, intent: &[u8], plan: &[u8], key: &[u8]) -> Result<Vec<Vec<u8>>> {
        Ok(self.consent.plan(intent, key, plan)?)
    }
}

impl Operator for Member {
    fn request(&mut self, request: Request, attempt: &mut Attempt, inputs: &[&str], output: &str) -> Result<Answered> {
        let payload = match (request, inputs) {
            (Request::Challenge, [intent, signature]) => crate::local::pair(&attempt.read(intent)?, &attempt.read(signature)?)?,
            (Request::Prepare | Request::Submit | Request::Lookup | Request::Query, [input]) => attempt.read(input)?.into_owned(),
            _ => return Err(Error(format!("{} takes other inputs", request.verb()))),
        };
        match self.operator.call(request.operation(), &payload) {
            Ok(crate::operator::Reply::Answer(body)) => attempt.create(output, &body).map(|_| Answered::Answer),
            // A marker frame is an outcome too: retained for the local codec to decode; its class
            // is the marker's (`Reply::NoRecord` decided, `Reply::Outcome` undecided).
            Ok(crate::operator::Reply::NoRecord(body)) if matches!(request, Request::Submit | Request::Lookup) => {
                attempt.create(output, &body).map(|_| Answered::NoRecord)
            }
            Ok(crate::operator::Reply::Outcome(body)) if matches!(request, Request::Submit | Request::Lookup) => {
                attempt.create(output, &body).map(|_| Answered::Outcome)
            }
            Ok(crate::operator::Reply::NoRecord(body)) => Err(Error(format!("host answered {} with no record; encoded outcome: {}",
                request.verb(), crate::hex::encode(&body)))),
            Ok(crate::operator::Reply::Outcome(body)) => Err(Error(format!("host answered {} undecided; encoded outcome: {}",
                request.verb(), crate::hex::encode(&body)))),
            Err(crate::operator::Failure::Unsent(d)) => Err(Error(format!("{}: never forwarded: {d}", request.verb()))),
            Err(crate::operator::Failure::Uncertain(d)) => Err(Error(format!("{}: uncertain: {d}", request.verb()))),
        }
    }
}
