//! `spk-host grain route`: bind one participant entrance to an installed
//! application from the participant's retained, Mini-accepted session,
//! ticket and enrollment evidence.

use crate::grain::HostView;
use serde_json::Value;
use std::io;
use std::path::Path;

pub(crate) fn route(_host: &HostView<'_>, _app: &str, _request: &Path) -> io::Result<Value> {
    Err(io::Error::other("grain route: not yet implemented"))
}
