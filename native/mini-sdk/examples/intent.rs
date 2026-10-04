//! A worked example: build one typed intent, print its canonical bytes and its digest, sign it
//! under both key schemes, verify, and show a tampered signature refuse. It needs no Host, no
//! consent process and no network: everything here is the OFFLINE CORE.
//!
//!     cargo run --offline --example intent
//!
//! The output is pinned by `tests/examples.rs`, the same text the TypeScript example
//! (`native/mini-sdk-ts/examples/intent.ts`) prints, and the intent bytes are cross-checked
//! against the vector Lean emitted for the same intent (`golden/lean-intents.json`, row
//! `example-invoke`).
//!
//! What is NOT shown, because it needs a Host: in the real flow the key signs only header bytes
//! the member's local consent process returned, and only under a `Confirmation` of what
//! `explain()` rendered (`flow::Client`, feature `native`). Here the key signs the intent bytes
//! directly, to show the signer interface.
use mini_sdk::contracts::{Cut, Dec, Intent, InvokeTarget, ObjectRef, RevisionRef};
use mini_sdk::signer::{verify, Scheme};
use mini_sdk::{hex, sha256, Profile};
use serde_json::json;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn main() -> Result<()> {
    // One request by one actor: write the text "hello" into a document. The salt makes this ONE
    // request: a retry of it reuses the salt, a second deliberate identical request would not.
    let intent = Intent {
        actor: Dec::new("12504530369102912422")?,
        request_salt: std::array::from_fn(|i| i as u8),
        cut: Cut::Invoke {
            targets: vec![InvokeTarget {
                revision: RevisionRef {
                    object: ObjectRef { id: Dec::new("11713997809205700508")?, domain: Dec::new("8501")?, kind: "object".into() },
                    root: Dec::new("94531388991341573437548127621893842788707596369540381335288917555563780111749")?,
                },
                capability: Dec::new("9591460230184716503")?,
                observe_capability: Dec::new("9591460230184716503")?,
                schema_version: Dec::new("9")?,
                payload: json!({"type":"content","actions":[{"type":"createAtom","atom":"1","kind":{"type":"text"},"payload":"68656c6c6f"}]}),
            }],
            family: None,
        },
    };

    // The bytes are the Lean codec's (`Kernel/Contracts/Intents.lean`); the name is their digest.
    let bytes = intent.canonical_bytes()?;
    println!("cut            {}", intent.cut.name());
    println!("actor          {}", intent.actor.as_str());
    println!("intent bytes   {} bytes", bytes.len());
    println!("  {}", hex::encode(&bytes));
    println!("preimage       {} bytes (DREGG/CONTRACT/INTENT-ID/v1 || intent bytes)", intent.id_preimage()?.len());
    println!("invocation id  {}", intent.invocation_id()?.hex());

    // A profile is a 64-byte master seed; each key scheme derives its key from it.
    let seed: [u8; 64] = std::array::from_fn(|i| i as u8);
    let profile = Profile::from_seed("example", seed)?;
    for (name, scheme) in [("ed25519", Scheme::Ed25519), ("hybrid", Scheme::HybridEd25519MlDsa65)] {
        let signer = profile.mini_signer(0, scheme);
        let (public, signature) = (signer.public_key(), signer.sign(&bytes)?);
        println!("{name}");
        println!("  public key   {} bytes, sha256 {}", public.len(), hex::encode(&sha256(&public)));
        println!("  signature    {} bytes, sha256 {}", signature.len(), hex::encode(&sha256(&signature)));
        verify(scheme, &public, &bytes, &signature)?;
        println!("  verified     ok");
        let mut tampered = signature.clone();
        let last = tampered.len() - 1;
        tampered[last] ^= 1;
        match verify(scheme, &public, &bytes, &tampered) {
            Ok(()) => return Err("a tampered signature verified".into()),
            Err(e) => println!("  tampered     refused: {e}"),
        }
    }
    Ok(())
}
