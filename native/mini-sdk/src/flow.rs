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
//! The steps are separate so a caller may interpose between them (the CLI's provider continuity
//! guard sits between 2 and 4). Each step reads and writes only files of the attempt, so the
//! directory is the custody record. The member's local side ([`Local`]: codec and consent) and
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
use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::durable::{self, Perm};
use crate::signer::Signer;
use crate::{Error, Result};

/// Where the intent comes from.
pub enum Source<'a> {
    /// Authoring source of this kind (e.g. `intent`), authored by the local codec into `intent.bin`.
    Authored { kind: &'a str, path: &'a Path },
    /// Canonical intent bytes, copied as `intent.bin`.
    Binary(&'a Path),
}

/// The member's local processes, by file: the storeless codec (frames 7–11) and the consent
/// provider. Each codec verb reads its inputs and writes its answer to `output`, a new file.
pub trait Local {
    fn author(&mut self, kind: &str, input: &Path, output: &Path) -> Result<()>;
    /// Writes the presentation to `output` and returns it.
    fn inspect(&mut self, kind: &str, input: &Path, output: &Path) -> Result<Value>;
    fn signatures(&mut self, json: &Path, output: &Path) -> Result<()>;
    fn observe_assemble(&mut self, challenge: &Path, signatures: &Path, output: &Path) -> Result<()>;
    fn assemble(&mut self, plan: &Path, signatures: &Path, output: &Path) -> Result<()>;
    /// Consent 220: `key` is the intent subject's current key. Returns the retained intent bytes
    /// the provider confirmed unchanged.
    fn consent_intent(&mut self, intent: &Path, key: &[u8]) -> Result<Vec<u8>>;
    /// Consent 221: the challenge headers this intent permits `key` to sign.
    fn consent_observation(&mut self, intent: &Path, signature: &Path, challenge: &Path, key: &[u8]) -> Result<Vec<Vec<u8>>>;
    /// Consent 222: the plan headers this intent permits `key` to sign.
    fn consent_plan(&mut self, intent: &Path, plan: &Path, key: &[u8]) -> Result<Vec<Vec<u8>>>;
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
}

impl Request {
    /// The Host verb (the one-shot command word and the session command name).
    pub fn verb(self) -> &'static str {
        match self {
            Request::Challenge => "challenge",
            Request::Prepare => "prepare",
            Request::Submit => "submit",
            Request::Lookup => "lookup",
        }
    }
    pub fn operation(self) -> u8 {
        use crate::host_operations as op;
        match self {
            Request::Challenge => op::OBSERVATION_CHALLENGE,
            Request::Prepare => op::AUTHORIZED_PREPARE,
            Request::Submit => op::SUBMIT,
            Request::Lookup => op::LOOKUP,
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

/// The serving Host, by file: `request` reads `inputs` and writes the answer to `output`, a new
/// file, and says how it was framed. An uncertain or never-forwarded transmission is an error;
/// what it means for the attempt is the caller's custody (a submit or lookup error leaves the
/// retained call to be looked up). An implementation may also report a marker frame as an error
/// it has already classified (the CLI's transport does).
pub trait Operator {
    fn request(&mut self, request: Request, inputs: &[&Path], output: &Path) -> Result<Answered>;
}

/// What [`Flow::seal`] would sign, shown to the caller's release before any key signs.
pub struct Sealing<'a> {
    pub intent_bin: &'a Path,
    pub plan_bin: &'a Path,
    /// The ordered headers the consent provider returned for exactly this intent and plan.
    pub headers: &'a [Vec<u8>],
}

/// One attempt directory and the parties that act on it.
pub struct Flow<'a, H: Local + Operator + ?Sized> {
    pub dir: &'a Path,
    pub host: &'a mut H,
    pub signer: &'a dyn Signer,
}

fn create(path: &Path, bytes: &[u8]) -> Result<()> {
    durable::create_new(path, bytes, Perm::Umask).map_err(|e| Error(format!("cannot create {}: {e}", path.display())))
}

fn create_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| Error(format!("cannot render {}: {e}", path.display())))?;
    bytes.push(b'\n');
    create(path, &bytes)
}

/// The JSON list the Host's `signatures` codec (op 9) reads: each header signed, hex, in order.
pub fn signature_list(signer: &dyn Signer, headers: &[Vec<u8>]) -> Result<Value> {
    headers.iter().map(|h| Ok(Value::String(crate::hex::encode(&signer.sign(h)?)))).collect::<Result<Vec<_>>>().map(Value::Array)
}


impl<'a, H: Local + Operator + ?Sized> Flow<'a, H> {
    fn path(&self, name: &str) -> PathBuf {
        self.dir.join(name)
    }

    /// Step 1: an authorized observation of `source`; returns `signed-observation.bin`.
    pub fn observe(&mut self, source: Source<'_>) -> Result<PathBuf> {
        let intent_bin = self.path("intent.bin");
        let intent_signature = self.path("intent-signature.bin");
        let challenge_bin = self.path("challenge.bin");
        let challenge_json = self.path("challenge.json");
        let signatures_json = self.path("observation-signatures.json");
        let signatures_bin = self.path("observation-signatures.bin");
        let signed = self.path("signed-observation.bin");
        match source {
            Source::Binary(path) => {
                let mut input = std::fs::File::open(path).map_err(|e| Error(format!("cannot open {}: {e}", path.display())))?;
                let length = input.metadata().ok().and_then(|m| usize::try_from(m.len()).ok());
                durable::create_new_from(&intent_bin, &mut input, length, Perm::Umask, &mut |_| Ok(()))
                    .map_err(|e| Error(format!("cannot copy {} to {}: {e}", path.display(), intent_bin.display())))?;
            }
            Source::Authored { kind, path } => {
                if intent_bin.exists() {
                    return Err(Error(format!("refusing to replace {}", intent_bin.display())));
                }
                self.host.author(kind, path, &intent_bin)?;
            }
        }
        // The local consent provider binds the retained intent and current subject to custody
        // before even the observation's first signature is released.
        let key = self.signer.public_key();
        let intent = self.host.consent_intent(&intent_bin, &key)?;
        create(&intent_signature, &self.signer.sign(&intent)?)?;
        self.host.request(Request::Challenge, &[&intent_bin, &intent_signature], &challenge_bin)?;
        self.host.inspect("challenge", &challenge_bin, &challenge_json)?;
        let headers = self.host.consent_observation(&intent_bin, &intent_signature, &challenge_bin, &key)?;
        create_json(&signatures_json, &signature_list(self.signer, &headers)?)?;
        self.host.signatures(&signatures_json, &signatures_bin)?;
        self.host.observe_assemble(&challenge_bin, &signatures_bin, &signed)?;
        Ok(signed)
    }

    /// Step 2: the operator's plan for `observation`, written to `plan.bin`; returns its path.
    pub fn prepare(&mut self, observation: &Path) -> Result<PathBuf> {
        let plan_bin = self.path("plan.bin");
        self.host.request(Request::Prepare, &[observation], &plan_bin)?;
        Ok(plan_bin)
    }

    /// Step 3: the local codec's presentation of a plan, written to `plan_json`.
    pub fn present(&mut self, plan_bin: &Path, plan_json: &Path) -> Result<Value> {
        self.host.inspect("plan", plan_bin, plan_json)
    }

    /// Step 4: sign the consented headers of `plan_bin` after `release` accepts them, assemble the
    /// exact call into `call.bin`; returns its path.
    pub fn seal(&mut self, plan_bin: &Path, release: &mut dyn FnMut(&Sealing<'_>) -> Result<()>) -> Result<PathBuf> {
        let signatures_bin = self.sign(plan_bin, release)?;
        let call = self.path("call.bin");
        self.host.assemble(plan_bin, &signatures_bin, &call)?;
        Ok(call)
    }

    /// The signing half of [`Flow::seal`]: the consented headers of `plan_bin`, released and
    /// signed into `transaction-signatures.{json,bin}`; returns the `.bin`. A caller that does not
    /// assemble a call (a dry run, op 130) stops here.
    pub fn sign(&mut self, plan_bin: &Path, release: &mut dyn FnMut(&Sealing<'_>) -> Result<()>) -> Result<PathBuf> {
        let intent_bin = self.path("intent.bin");
        let signatures_json = self.path("transaction-signatures.json");
        let signatures_bin = self.path("transaction-signatures.bin");
        let headers = self.host.consent_plan(&intent_bin, plan_bin, &self.signer.public_key())?;
        if headers.is_empty() {
            return Err("consent returned no headers; nothing to sign".into());
        }
        release(&Sealing { intent_bin: &intent_bin, plan_bin, headers: &headers })?;
        create_json(&signatures_json, &signature_list(self.signer, &headers)?)?;
        self.host.signatures(&signatures_json, &signatures_bin)?;
        Ok(signatures_bin)
    }

    /// Step 5: submit or look up the retained `call.bin`; the answer goes to `outcome_bin` and the
    /// local codec's presentation of it to `outcome_json`. Returns the presentation and how the
    /// Host framed it; [`Flow::transmission`] turns both into the attempt's
    /// [`crate::custody::Transmission`] (a 255 envelope is undecided whatever it decodes to).
    pub fn transmit(&mut self, request: Request, outcome_bin: &Path, outcome_json: &Path) -> Result<(Value, Answered)> {
        if !matches!(request, Request::Submit | Request::Lookup) {
            return Err("only an exact call is transmitted".into());
        }
        let call = self.path("call.bin");
        let answered = self.host.request(request, &[&call], outcome_bin)?;
        Ok((self.host.inspect("outcome", outcome_bin, outcome_json)?, answered))
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

fn read(path: &Path) -> Result<Vec<u8>> {
    crate::fsread::read_regular(path, 0, crate::local::CAP).map_err(|e| Error(e.to_string()))
}

impl Member {
    fn codec(&mut self, answer: std::result::Result<Vec<u8>, crate::local::CodecError>, output: &Path) -> Result<Vec<u8>> {
        match answer {
            Ok(body) => {
                create(output, &body)?;
                Ok(body)
            }
            Err(crate::local::CodecError::Refused { decoded, .. }) => Err(Error(format!("local codec refused: {}",
                decoded.map_or_else(|| "undecoded".to_owned(), |v| v.to_string())))),
            Err(crate::local::CodecError::Failed(e)) => Err(Error(e)),
        }
    }
}

impl Local for Member {
    fn author(&mut self, kind: &str, input: &Path, output: &Path) -> Result<()> {
        let answer = self.codec.author(&self.image, &self.settings, kind, &read(input)?);
        self.codec(answer, output).map(|_| ())
    }
    fn inspect(&mut self, kind: &str, input: &Path, output: &Path) -> Result<Value> {
        let answer = self.codec.inspect(&self.image, &self.settings, kind, &read(input)?);
        let body = self.codec(answer, output)?;
        serde_json::from_slice(&body).map_err(|e| Error(format!("invalid host JSON {}: {e}", output.display())))
    }
    fn signatures(&mut self, json: &Path, output: &Path) -> Result<()> {
        let answer = self.codec.signatures(&self.image, &self.settings, &read(json)?);
        self.codec(answer, output).map(|_| ())
    }
    fn observe_assemble(&mut self, challenge: &Path, signatures: &Path, output: &Path) -> Result<()> {
        let answer = self.codec.observe_assemble(&self.image, &self.settings, &read(challenge)?, &read(signatures)?);
        self.codec(answer, output).map(|_| ())
    }
    fn assemble(&mut self, plan: &Path, signatures: &Path, output: &Path) -> Result<()> {
        let answer = self.codec.assemble(&self.image, &self.settings, &read(plan)?, &read(signatures)?);
        self.codec(answer, output).map(|_| ())
    }
    fn consent_intent(&mut self, intent: &Path, key: &[u8]) -> Result<Vec<u8>> {
        let bytes = read(intent)?;
        self.consent.intent(&bytes, key, false)?;
        Ok(bytes)
    }
    fn consent_observation(&mut self, intent: &Path, signature: &Path, challenge: &Path, key: &[u8]) -> Result<Vec<Vec<u8>>> {
        Ok(self.consent.observation(&read(intent)?, key, &read(signature)?, &read(challenge)?, false)?)
    }
    fn consent_plan(&mut self, intent: &Path, plan: &Path, key: &[u8]) -> Result<Vec<Vec<u8>>> {
        Ok(self.consent.plan(&read(intent)?, key, &read(plan)?)?)
    }
}

impl Operator for Member {
    fn request(&mut self, request: Request, inputs: &[&Path], output: &Path) -> Result<Answered> {
        let payload = match (request, inputs) {
            (Request::Challenge, [intent, signature]) => crate::local::pair(&read(intent)?, &read(signature)?)?,
            (Request::Prepare | Request::Submit | Request::Lookup, [input]) => read(input)?,
            _ => return Err(Error(format!("{} takes other inputs", request.verb()))),
        };
        match self.operator.call(request.operation(), &payload) {
            Ok(crate::operator::Reply::Answer(body)) => create(output, &body).map(|_| Answered::Answer),
            // A marker frame is an outcome too: retained for the local codec to decode; its class
            // is the marker's (`Reply::NoRecord` decided, `Reply::Outcome` undecided).
            Ok(crate::operator::Reply::NoRecord(body)) if matches!(request, Request::Submit | Request::Lookup) => {
                create(output, &body).map(|_| Answered::NoRecord)
            }
            Ok(crate::operator::Reply::Outcome(body)) if matches!(request, Request::Submit | Request::Lookup) => {
                create(output, &body).map(|_| Answered::Outcome)
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
