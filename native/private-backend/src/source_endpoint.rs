//! Exact native JointBackendPartyCodec REQUEST/OUTCOME adapter.
//! These are untrusted claims. Canonical decoding and semantic byte matching
//! confer no current enrollment, source Applied, funding, WAL readback or Qualified.
use crate::{
    authenticated_ingress::{self, Envelope, ProgressClaim},
    codec::{bad, bytes, Generation, Nat, Reader},
};
use std::io::Result;
const REQUEST: &[u8] = b"DREGG.JOINT.PRIVATE.REQUEST\x01";
const OUTCOME: &[u8] = b"DREGG.JOINT.PRIVATE.OUTCOME\x01";
pub const MAX_REQUEST: usize = 262144;
pub const MAX_OUTCOME: usize = 262070;
/// Public traffic shape P262144 minus the complete mode's actual overhead.
pub const MAX_COMPLETE_NATIVE_REQUEST: usize = 262078;
pub const MAX_COMPLETE_NATIVE_REPLY: usize = 262070;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RequestClaim {
    pub candidate_bytes: Vec<u8>,
    pub participant: Nat,
    pub full_generation_bytes: Vec<u8>,
    pub manifest_root: Nat,
    pub raw_carrier: Vec<u8>,
}
impl RequestClaim {
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut b = REQUEST.to_vec();
        bytes(&self.candidate_bytes, &mut b);
        self.participant.put(&mut b);
        bytes(&self.full_generation_bytes, &mut b);
        self.manifest_root.put(&mut b);
        bytes(&self.raw_carrier, &mut b);
        if b.len() > MAX_REQUEST {
            return Err(bad("native private request codec capacity"));
        }
        Ok(b)
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        if b.len() > MAX_REQUEST || !b.starts_with(REQUEST) {
            return Err(bad("native private request frame/capacity"));
        }
        let mut r = Reader::new(&b[REQUEST.len()..])?;
        let v = Self {
            candidate_bytes: r.bytes()?,
            participant: r.nat()?,
            full_generation_bytes: r.bytes()?,
            manifest_root: r.nat()?,
            raw_carrier: r.bytes()?,
        };
        r.finish()?;
        if v.encode()? != b {
            return Err(bad("native private request canonical"));
        }
        Ok(v)
    }
    /// Mechanical equality only: native receiver still selects actual source
    /// manifest/current grant and verifies its native request-header credential.
    pub fn protocol_binding(&self) -> Result<Envelope> {
        let wire = authenticated_ingress::public_ingress_gate(&self.raw_carrier)?;
        let envelope = Envelope::decode(&wire)?;
        let mut r = Reader::new(&self.full_generation_bytes)?;
        let generation = Generation::get(&mut r)?;
        r.finish()?;
        let mut canonical = vec![];
        generation.put(&mut canonical);
        if canonical != self.full_generation_bytes
            || generation != envelope.party.context.generation
        {
            return Err(bad("native outer/inner exact generation"));
        }
        Ok(envelope)
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgressOutcomeClaim {
    pub request_bytes: Vec<u8>,
    pub descriptor_bytes: Vec<u8>,
    pub source_record_bytes: Vec<u8>,
    pub source_receipt_bytes: Vec<u8>,
    pub backend_progress_bytes: Vec<u8>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OutcomeClaim {
    Refused(Nat),
    Unknown {
        request_bytes: Vec<u8>,
        source_receipt_bytes: Vec<u8>,
    },
    Progress(ProgressOutcomeClaim),
}
impl OutcomeClaim {
    pub fn encode(&self) -> Result<Vec<u8>> {
        let mut b = OUTCOME.to_vec();
        match self {
            Self::Refused(n) => {
                b.push(0);
                n.put(&mut b);
            }
            Self::Unknown {
                request_bytes,
                source_receipt_bytes,
            } => {
                b.push(1);
                bytes(request_bytes, &mut b);
                bytes(source_receipt_bytes, &mut b);
            }
            Self::Progress(p) => {
                b.push(2);
                for v in [
                    &p.request_bytes,
                    &p.descriptor_bytes,
                    &p.source_record_bytes,
                    &p.source_receipt_bytes,
                    &p.backend_progress_bytes,
                ] {
                    bytes(v, &mut b);
                }
            }
        }
        if b.len() > MAX_OUTCOME {
            return Err(bad("native private outcome capacity"));
        }
        Ok(b)
    }
    pub fn decode(b: &[u8]) -> Result<Self> {
        if b.len() > MAX_OUTCOME || !b.starts_with(OUTCOME) {
            return Err(bad("native outcome frame/capacity"));
        }
        let payload = b
            .get(OUTCOME.len() + 1..)
            .ok_or_else(|| bad("native outcome tag"))?;
        let mut r = Reader::new(payload)?;
        let v = match b[OUTCOME.len()] {
            0 => Self::Refused(r.nat()?),
            1 => Self::Unknown {
                request_bytes: r.bytes()?,
                source_receipt_bytes: r.bytes()?,
            },
            2 => Self::Progress(ProgressOutcomeClaim {
                request_bytes: r.bytes()?,
                descriptor_bytes: r.bytes()?,
                source_record_bytes: r.bytes()?,
                source_receipt_bytes: r.bytes()?,
                backend_progress_bytes: r.bytes()?,
            }),
            _ => return Err(bad("native outcome variant")),
        };
        r.finish()?;
        if v.encode()? != b {
            return Err(bad("native outcome canonical"));
        }
        Ok(v)
    }
    /// A transport-facing claim comparator, not a constructor of actual
    /// source authority or actual readback. Return no terminal YES/result.
    pub fn matches_request(&self, expected: &RequestClaim) -> Result<Option<ProgressClaim>> {
        let exact = expected.encode()?;
        match self {
            Self::Refused(_) => Ok(None),
            Self::Unknown { request_bytes, .. } => {
                if *request_bytes != exact {
                    return Err(bad("unknown response cross request"));
                }
                Ok(None)
            }
            Self::Progress(p) => {
                if p.request_bytes != exact {
                    return Err(bad("progress response cross request"));
                }
                let envelope = expected.protocol_binding()?;
                let progress = ProgressClaim::decode(&p.backend_progress_bytes)?;
                if progress.signing_bytes != envelope.signing_bytes() {
                    return Err(bad("progress response wrong party/protocol/epoch/sequence"));
                }
                // Retain full protected descriptor/source-record/receipt bytes;
                // absence cannot be promoted to an authority-bearing response.
                if p.descriptor_bytes.is_empty()
                    || p.source_record_bytes.is_empty()
                    || p.source_receipt_bytes.is_empty()
                {
                    return Err(bad("progress missing original source bindings"));
                }
                Ok(Some(progress))
            }
        }
    }
}
/// Call on the FINAL complete native carrier, including config/purpose/op
/// wrapping. Raw REQUEST codec limits cannot establish physical packet fit.
pub fn admit_complete_transport_frame(request: &[u8], reply: &[u8]) -> Result<()> {
    if request.len() > MAX_COMPLETE_NATIVE_REQUEST || reply.len() > MAX_COMPLETE_NATIVE_REPLY {
        return Err(bad(
            "complete private native frame exceeds fixed public packet",
        ));
    }
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::authenticated_ingress::{CommitteeParty, Context, Protocol};
    fn request() -> RequestClaim {
        let generation = Generation {
            invocation: Nat::from_be(&[255; 32]),
            command: vec![3, 4],
            attempt: Nat::new(7),
            generation: Nat::new(11),
            configuration: Nat::from_be(&[254; 32]),
        };
        let packet = Envelope {
            party: CommitteeParty {
                context: Context {
                    protocol: Protocol::AcssId,
                    generation: generation.clone(),
                    authority_epoch: Nat::new(14),
                    session: vec![6],
                    recipient: 3,
                    recipient_role: b"holder".to_vec(),
                },
                party: 1,
                subject: vec![2],
                key_epoch: Nat::new(19),
                key_binding: vec![4],
                credential_purpose: b"private-message".to_vec(),
            },
            sequence: 123,
            message: vec![3, 7],
            credential: vec![8, 9],
        };
        let mut g = vec![];
        generation.put(&mut g);
        RequestClaim {
            candidate_bytes: vec![2],
            participant: Nat::from_be(&[255; 32]),
            full_generation_bytes: g,
            manifest_root: Nat::from_be(&[253; 32]),
            raw_carrier: authenticated_ingress::carrier(&packet.encode().unwrap()).unwrap(),
        }
    }
    fn outcome(r: &RequestClaim) -> OutcomeClaim {
        let p = r.protocol_binding().unwrap();
        OutcomeClaim::Progress(ProgressOutcomeClaim {
            request_bytes: r.encode().unwrap(),
            descriptor_bytes: vec![4],
            source_record_bytes: vec![5],
            source_receipt_bytes: vec![6],
            backend_progress_bytes: ProgressClaim {
                signing_bytes: p.signing_bytes(),
                outbox_digest: [7; 32],
                outbox_bytes: 19,
            }
            .encode()
            .unwrap(),
        })
    }
    #[test]
    fn canonical_native_claim_codec_preserves_full_nats_and_rejects_suffixes() {
        let r = request();
        assert_eq!(RequestClaim::decode(&r.encode().unwrap()).unwrap(), r);
        for o in [
            OutcomeClaim::Refused(Nat::from_be(&[255; 32])),
            OutcomeClaim::Unknown {
                request_bytes: r.encode().unwrap(),
                source_receipt_bytes: vec![9],
            },
            outcome(&r),
        ] {
            assert_eq!(OutcomeClaim::decode(&o.encode().unwrap()).unwrap(), o);
            let mut bytes = o.encode().unwrap();
            bytes.push(0);
            assert!(OutcomeClaim::decode(&bytes).is_err());
        }
        let mut bytes = r.encode().unwrap();
        bytes.push(0);
        assert!(RequestClaim::decode(&bytes).is_err());
    }
    #[test]
    fn crossed_party_epoch_sequence_and_outer_generation_progress_refuse() {
        let r = request();
        assert!(outcome(&r).matches_request(&r).unwrap().is_some());
        let mut packet = r.protocol_binding().unwrap();
        for tag in 0..4 {
            let mut other = packet.clone();
            match tag {
                0 => other.party.party = 2,
                1 => other.party.context.authority_epoch = Nat::new(15),
                2 => other.sequence += 1,
                _ => other.party.context.protocol = Protocol::PrivateSend,
            }
            let mut fake = outcome(&r);
            let OutcomeClaim::Progress(p) = &mut fake else {
                unreachable!()
            };
            p.backend_progress_bytes = ProgressClaim {
                signing_bytes: other.signing_bytes(),
                outbox_digest: [7; 32],
                outbox_bytes: 19,
            }
            .encode()
            .unwrap();
            assert!(fake.matches_request(&r).is_err());
        }
        packet.party.context.generation.attempt = Nat::new(8);
        let mut wrong = r.clone();
        wrong.raw_carrier = authenticated_ingress::carrier(&packet.encode().unwrap()).unwrap();
        assert!(wrong.protocol_binding().is_err());
        let mut wrong = r.clone();
        wrong.candidate_bytes.push(1);
        assert!(outcome(&r).matches_request(&wrong).is_err());
    }
    #[test]
    fn actual_complete_frame_capacity_includes_all_native_wrapping() {
        assert!(admit_complete_transport_frame(
            &vec![0; MAX_COMPLETE_NATIVE_REQUEST],
            &vec![0; MAX_COMPLETE_NATIVE_REPLY]
        )
        .is_ok());
        assert!(
            admit_complete_transport_frame(&vec![0; MAX_COMPLETE_NATIVE_REQUEST + 1], &[]).is_err()
        );
        assert!(
            admit_complete_transport_frame(&[], &vec![0; MAX_COMPLETE_NATIVE_REPLY + 1]).is_err()
        );
    }
}
