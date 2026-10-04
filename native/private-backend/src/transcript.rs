//! Test-only wiretap: the complete ordered stream of messages ONE party receives,
//! across every protocol layer of a run (input ACSS, King preprocessing ACSS/Sh2t,
//! King, layered MPC, recipient output). An honest-but-curious party's view is
//! exactly this stream plus its own randomness.
use crate::{acss_id, field_network, private_output, sh2t_id, triple_king};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Wire {
    Acss(acss_id::Message),
    Sh2t(sh2t_id::Message),
    King(triple_king::Message),
    Layer(field_network::Message),
    Output(private_output::Message),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Frame {
    pub(crate) phase: String,
    pub(crate) sender: u16,
    pub(crate) wire: Wire,
}
pub(crate) struct Tap {
    curious: Option<u16>,
    pub(crate) frames: Vec<Frame>,
}
impl Tap {
    pub(crate) fn none() -> Self {
        Self {
            curious: None,
            frames: vec![],
        }
    }
    pub(crate) fn on(curious: u16) -> Self {
        Self {
            curious: Some(curious),
            frames: vec![],
        }
    }
    /// Record a delivery if it is addressed to the curious party.
    pub(crate) fn see(&mut self, phase: &str, to: u16, sender: u16, wire: impl FnOnce() -> Wire) {
        if self.curious == Some(to) {
            self.frames.push(Frame {
                phase: phase.to_string(),
                sender,
                wire: wire(),
            });
        }
    }
}
