//! STOP after a lost op22 (BEGIN) or op26 (CLAIM) reply.
//!
//! A Running journal that still holds a STOP attempt used to refuse every
//! later `resident-stop` ("requires audit"), leaving the app Running with no
//! tool path. These are the receipt-only lookups START already has, applied
//! to STOP: op23 on the exact retained BEGIN ingress, op27 on the exact
//! retained CLAIM ingress. A lookup never submits, assembles or signs.
//!
//! - BEGIN `confirmed replayed`: the BEGIN is Lean's; STOP resumes from
//!   CLAIM assembly with the retained plan and Lean's original receipt.
//! - BEGIN or CLAIM `absent` after the Host ANSWERED that submit (its
//!   `op22`/`op26-frame.bin` is retained): Lean holds no record of that exact
//!   call; the attempt is set aside, whole, under the journal, and STOP
//!   authors afresh.
//! - `absent` after a LOST reply: undecided (ruling 2026-10-26; no positive
//!   no-append frame yet). STOP refuses by name and records the lookup; a
//!   later run looks up again.
//! - CLAIM `confirmed replayed`: Lean recorded the STOP claim but its
//!   committed permit (the only thing that may arm the physical fence) was
//!   lost and a lookup cannot re-issue it. STOP refuses by name and records
//!   the receipt.
//!
//! Every decision writes `stop-submit-reconciliation-<nonce>.json`.

use crate::io_context::IoContext;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::lifecycle_receipt_lookup::{lookup_view, outcome_receipt, retained};
use crate::lifecycle_v3_native::{hex, text};
use crate::lifecycle_v3_stop_begin_native::AcceptedStopBegin;
use crate::lifecycle_v3_stop_claim_native::ExactReceipt;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::{self, Read};
use std::path::{Path, PathBuf};

const MAX_FRAME: u64 = 12_102_760;
const MAX_MARKER: u64 = 65_536;
const BEGIN_ACTIVE: &str = "lifecycle-stop-begin-v3-active.json";
const CLAIM_ACTIVE: &str = "lifecycle-stop-claim-v3-active.json";
const ASSEMBLY_ACTIVE: &str = "lifecycle-stop-claim-assembly-active.json";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn present(path: &Path) -> io::Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

/// The STOP attempt directories of one journal, as `StopConfig` names them.
pub(crate) struct StopAttempts<'a> {
    pub journal_dir: &'a Path,
    pub begin: &'a Path,
    pub claim_author: &'a Path,
    pub claim: &'a Path,
}

enum Lookup {
    Replayed(ExactReceipt, String),
    Absent(String),
}

fn decided(view: &Value, name: String) -> io::Result<Lookup> {
    match view.get("type").and_then(Value::as_str) {
        Some("absent") => Ok(Lookup::Absent(name)),
        Some("confirmed") => {
            let [transaction, event, count, root] = outcome_receipt(view, "replayed")?;
            Ok(Lookup::Replayed(
                ExactReceipt::new(&transaction, &event, &count, &root)?,
                name,
            ))
        }
        _ => Err(invalid("STOP lookup was not answered by a receipt or absence")),
    }
}

fn record(journal_dir: &Path, value: Value) -> io::Result<()> {
    let mut random = [0u8; 16];
    File::open("/dev/urandom").ctx("open", &"/dev/urandom")?.read_exact(&mut random)?;
    write_new(
        journal_dir,
        &format!("stop-submit-reconciliation-{}.json", hex(&random)),
        &serde_json::to_vec(&value)?,
    )?;
    Ok(())
}

fn receipt_json(receipt: &ExactReceipt) -> Value {
    json!({"transactionId":receipt.transaction_id(),"eventId":receipt.event_id(),
        "acceptedCount":receipt.accepted_count(),"worldRoot":receipt.world_root()})
}

/// Move `paths` (those present) into a fresh `<label>-<nonce>` directory
/// under the journal. Nothing is deleted.
fn set_aside(journal_dir: &Path, label: &str, paths: &[&Path]) -> io::Result<PathBuf> {
    let mut random = [0u8; 16];
    File::open("/dev/urandom").ctx("open", &"/dev/urandom")?.read_exact(&mut random)?;
    let aside = journal_dir.join(format!("{label}-{}", hex(&random)));
    std::os::unix::fs::DirBuilderExt::mode(&mut fs::DirBuilder::new(), 0o700).create(&aside)?;
    for path in paths {
        if present(path)? {
            let name = path
                .file_name()
                .ok_or_else(|| invalid("STOP set-aside name absent"))?;
            fs::rename(path, aside.join(name)).ctx("rename", &path)?;
        }
    }
    Ok(aside)
}

/// The exact CLAIM ingress the one op26 carried, checked against its marker
/// and the journal's active marker.
fn retained_claim_ingress(attempts: &StopAttempts<'_>) -> io::Result<Vec<u8>> {
    private_dir(attempts.claim)?;
    let marker_bytes = retained(&attempts.claim.join("op26-requested.json"), MAX_MARKER)?;
    if retained(&attempts.journal_dir.join(CLAIM_ACTIVE), MAX_MARKER)? != marker_bytes {
        return Err(invalid("STOP claim active marker differs from its attempt"));
    }
    let marker: Value = serde_json::from_slice(&marker_bytes)?;
    let ingress = retained(&attempts.claim.join("claim-ingress-v3.bin"), MAX_FRAME)?;
    if text(&marker, "protocol")? != "mini-spk-stop-claim-op26-requested-v1"
        || text(&marker, "claimIngressSha256")? != hex(&Sha256::digest(&ingress))
    {
        return Err(invalid("STOP claim submit marker differs from retained ingress"));
    }
    Ok(ingress)
}

/// The exact BEGIN ingress the one op22 carried.
fn retained_begin_ingress(attempts: &StopAttempts<'_>) -> io::Result<Vec<u8>> {
    crate::lifecycle_receipt_lookup::retained_submitted_ingress(
        attempts.begin,
        BEGIN_ACTIVE,
        "op66-requested.json",
        "op22-requested.json",
        "mini-spk-stop-begin-op22-requested-v1",
        "begin-v3.bin",
    )
}

/// Reconcile the STOP submits a Running journal still holds. `Ok(Some)` is a
/// Lean-accepted BEGIN to resume from; `Ok(None)` means nothing remains and
/// STOP authors afresh (absent attempts were set aside). A CLAIM Lean
/// recorded without our committed permit is refused by name.
pub(crate) fn reconcile_running(
    operator: &PrivateOperator,
    attempts: &StopAttempts<'_>,
) -> io::Result<Option<AcceptedStopBegin>> {
    let journal_dir = attempts.journal_dir;
    if present(&attempts.claim.join("op26-requested.json"))? {
        if present(&attempts.claim.join("committed-v3.bin"))? {
            // The committed permit was retained: that is the physical
            // fence's audit (resume_fenced_exact), not a lost reply.
            return Err(invalid(
                "STOP claim committed on a Running journal requires the fence audit",
            ));
        }
        let ingress = retained_claim_ingress(attempts)?;
        let answered = present(&attempts.claim.join("op26-frame.bin"))?;
        let (view, name, _) = lookup_view(operator, attempts.claim, 27, &ingress)?;
        match decided(&view, name)? {
            Lookup::Replayed(receipt, name) => {
                record(journal_dir, json!({"protocol":"mini-spk-stop-submit-reconciliation-v1",
                    "phase":"claim","lookup":"op27","decision":"recorded-without-permit",
                    "evidence":format!("{name}/outcome.json"),"receipt":receipt_json(&receipt),
                    "noResubmit":true}))?;
                return Err(invalid(
                    "STOP CLAIM recorded by Mini (op27 lookup) but its committed permit was lost; no fence was armed and source recovery is required",
                ));
            }
            Lookup::Absent(name) if !answered => {
                record(journal_dir, json!({"protocol":"mini-spk-stop-submit-reconciliation-v1",
                    "phase":"claim","lookup":"op27","decision":"undecided-absent-after-lost-reply",
                    "evidence":format!("{name}/outcome.json"),"noResubmit":true}))?;
                return Err(invalid(
                    "STOP CLAIM reply was lost and Mini's op27 lookup finds no record; undecided until a positive no-append answer exists, so the attempt is kept and STOP retries the lookup later",
                ));
            }
            Lookup::Absent(name) => {
                let aside = set_aside(
                    journal_dir,
                    "stop-claim-absent",
                    &[
                        attempts.claim,
                        attempts.claim_author,
                        &journal_dir.join(CLAIM_ACTIVE),
                        &journal_dir.join(ASSEMBLY_ACTIVE),
                    ],
                )?;
                record(journal_dir, json!({"protocol":"mini-spk-stop-submit-reconciliation-v1",
                    "phase":"claim","lookup":"op27","decision":"absent-set-aside",
                    "evidence":format!("{name}/outcome.json"),
                    "setAside":aside.file_name().and_then(|n| n.to_str())}))?;
            }
        }
    } else if present(attempts.claim)? || present(&journal_dir.join(CLAIM_ACTIVE))? {
        return Err(invalid("STOP claim attempt without its submit marker requires audit"));
    } else if present(attempts.claim_author)? {
        // Assembly (op68/op69) writes no Store record and no op26 was sent.
        let aside = set_aside(
            journal_dir,
            "stop-claim-unsubmitted",
            &[attempts.claim_author, &journal_dir.join(ASSEMBLY_ACTIVE)],
        )?;
        record(journal_dir, json!({"protocol":"mini-spk-stop-submit-reconciliation-v1",
            "phase":"claim-assembly","decision":"unsubmitted-set-aside",
            "setAside":aside.file_name().and_then(|n| n.to_str())}))?;
    }
    if !present(&attempts.begin.join("op22-requested.json"))? {
        return Ok(None);
    }
    let ingress = retained_begin_ingress(attempts)?;
    let answered = present(&attempts.begin.join("op22-frame.bin"))?;
    let (view, name, _) = lookup_view(operator, attempts.begin, 23, &ingress)?;
    match decided(&view, name)? {
        Lookup::Replayed(receipt, name) => {
            record(journal_dir, json!({"protocol":"mini-spk-stop-submit-reconciliation-v1",
                "phase":"begin","lookup":"op23","decision":"resume-from-claim",
                "evidence":format!("{name}/outcome.json"),"receipt":receipt_json(&receipt),
                "noResubmit":true}))?;
            Ok(Some(AcceptedStopBegin::recovered(attempts.begin, receipt)?))
        }
        Lookup::Absent(name) if !answered => {
            record(journal_dir, json!({"protocol":"mini-spk-stop-submit-reconciliation-v1",
                "phase":"begin","lookup":"op23","decision":"undecided-absent-after-lost-reply",
                "evidence":format!("{name}/outcome.json"),"noResubmit":true}))?;
            Err(invalid(
                "STOP BEGIN reply was lost and Mini's op23 lookup finds no record; undecided until a positive no-append answer exists, so the attempt is kept and STOP retries the lookup later",
            ))
        }
        Lookup::Absent(name) => {
            let aside = set_aside(
                journal_dir,
                "stop-begin-absent",
                &[attempts.begin, &journal_dir.join(BEGIN_ACTIVE)],
            )?;
            record(journal_dir, json!({"protocol":"mini-spk-stop-submit-reconciliation-v1",
                "phase":"begin","lookup":"op23","decision":"absent-set-aside",
                "evidence":format!("{name}/outcome.json"),
                "setAside":aside.file_name().and_then(|n| n.to_str())}))?;
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grain_export::tests::FakeHost;
    use std::os::unix::fs::DirBuilderExt;

    fn begin_attempt(journal: &Path, ingress: &[u8]) -> PathBuf {
        let begin = journal.join("stop-begin");
        fs::DirBuilder::new().mode(0o700).create(&begin).unwrap();
        let requested = br#"{"protocol":"mini-spk-stop-begin-op66-requested-v1","clientOperationId":"5"}"#;
        write_new(&begin, "op66-requested.json", requested).unwrap();
        write_new(journal, BEGIN_ACTIVE, requested).unwrap();
        write_new(&begin, "begin-v3.bin", ingress).unwrap();
        let marker = json!({"protocol":"mini-spk-stop-begin-op22-requested-v1",
            "ingressSha256":hex(&Sha256::digest(ingress))});
        write_new(&begin, "op22-requested.json", &serde_json::to_vec(&marker).unwrap()).unwrap();
        let plan = b"plan";
        write_new(&begin, "stop-plan-v2.bin", plan).unwrap();
        let view = json!({"canonicalPlanHex":hex(plan),"basePlan":{"authorizationOperationId":"6",
            "processGeneration":"7","volumeIdHex":"ab"}});
        write_new(&begin, "stop-plan-v2.json", &serde_json::to_vec(&view).unwrap()).unwrap();
        begin
    }

    /// Lean has the BEGIN: STOP resumes with Lean's receipt and the retained
    /// plan. An answered submit Lean lacks: set aside, nothing deleted. A lost
    /// reply Lean lacks: undecided, refused, attempt kept.
    #[test]
    fn lost_stop_begin_resumes_on_receipt_and_sets_aside_on_absence() {
        // The lost-reply absent case is undecided: refused, attempt kept.
        {
            let fake = FakeHost::new("stop-begin-lost-absent");
            let ingress = b"DREGG/APPLICATION/LIFECYCLE-BEGIN-INGRESS/v3 exact".to_vec();
            let begin = begin_attempt(&fake.root, &ingress);
            let served = fake.serve(vec!["absent"]);
            let attempts = StopAttempts {
                journal_dir: &fake.root,
                begin: &begin,
                claim_author: &fake.root.join("stop-claim-author"),
                claim: &fake.root.join("stop-claim"),
            };
            assert!(reconcile_running(&fake.operator, &attempts).is_err());
            assert_eq!(served.join().unwrap(), vec![(23, ingress.clone())]);
            assert!(begin.join("begin-v3.bin").exists());
            assert!(fake.root.join(BEGIN_ACTIVE).exists());
        }
        for (word, resumed) in [("replayed", true), ("absent", false)] {
            let fake = FakeHost::new("stop-begin-lookup");
            let ingress = b"DREGG/APPLICATION/LIFECYCLE-BEGIN-INGRESS/v3 exact".to_vec();
            let begin = begin_attempt(&fake.root, &ingress);
            // The Host answered the submit (not installed): its frame is kept.
            write_new(&begin, "op22-frame.bin", b"answered").unwrap();
            let served = fake.serve(vec![word]);
            let attempts = StopAttempts {
                journal_dir: &fake.root,
                begin: &begin,
                claim_author: &fake.root.join("stop-claim-author"),
                claim: &fake.root.join("stop-claim"),
            };
            let outcome = reconcile_running(&fake.operator, &attempts).unwrap();
            assert_eq!(served.join().unwrap(), vec![(23, ingress.clone())]);
            assert_eq!(outcome.is_some(), resumed);
            if let Some(accepted) = outcome {
                assert_eq!(accepted.client_operation_id(), "5");
                assert_eq!(accepted.receipt().accepted_count(), "73");
                assert_eq!(accepted.ingress(), ingress.as_slice());
            } else {
                assert!(!begin.exists());
                assert!(!fake.root.join(BEGIN_ACTIVE).exists());
                assert!(fs::read_dir(&fake.root).unwrap().any(|entry| entry
                    .unwrap()
                    .file_name()
                    .to_string_lossy()
                    .starts_with("stop-begin-absent-")));
            }
        }
    }
}
