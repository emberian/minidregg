//! Private Sandstorm two-party RPC endpoint for a checked Mini app session.
//!
//! This crate does not establish request authority. A trusted Mini controller
//! must check resource, generation, subject, grant and exact operation before
//! giving it an approved session. There is no public listener here.

mod bridge_config;
mod permission_schema;
mod protocol;
mod web;
pub use bridge_config::{decode_bridge_config, BridgeConfig};
pub use permission_schema::{permission_schema_source, permission_schema_source_bytes};
pub use protocol::{
    InlineResponse, LocalizedText, PermissionDefinition, RoleDefinition, SessionParameters,
    SupervisorConnection, ViewInfo,
};
pub use web::{
    dispatch_web, open_web_socket, send_to_app, Body, Cookie, CookieExpiry, ETag,
    ETagPrecondition, Header, Method, RequestContext, SetCookie, WebRequest, WebResponse,
    WebResult, WebSocketOpen, WebSocketSession, MAX_WEBSOCKET_MESSAGE,
};

#[allow(clippy::all)]
pub mod util_capnp {
    include!(concat!(env!("OUT_DIR"), "/util_capnp.rs"));
}
#[allow(clippy::all)]
pub mod identity_capnp {
    include!(concat!(env!("OUT_DIR"), "/identity_capnp.rs"));
}
#[allow(clippy::all)]
pub mod powerbox_capnp {
    include!(concat!(env!("OUT_DIR"), "/powerbox_capnp.rs"));
}
#[allow(clippy::all)]
pub mod activity_capnp {
    include!(concat!(env!("OUT_DIR"), "/activity_capnp.rs"));
}
#[allow(clippy::all)]
pub mod grain_capnp {
    include!(concat!(env!("OUT_DIR"), "/grain_capnp.rs"));
}
#[allow(clippy::all)]
pub mod supervisor_capnp {
    include!(concat!(env!("OUT_DIR"), "/supervisor_capnp.rs"));
}
#[allow(clippy::all)]
pub mod ip_capnp {
    include!(concat!(env!("OUT_DIR"), "/ip_capnp.rs"));
}
#[allow(clippy::all)]
pub mod web_session_capnp {
    include!(concat!(env!("OUT_DIR"), "/web_session_capnp.rs"));
}
#[allow(clippy::all)]
pub mod api_session_capnp {
    include!(concat!(env!("OUT_DIR"), "/api_session_capnp.rs"));
}
#[allow(clippy::all)]
pub mod package_rust_capnp {
    include!(concat!(env!("OUT_DIR"), "/package_rust_capnp.rs"));
}
#[allow(clippy::all)]
pub mod persistent_capnp {
    include!(concat!(env!("OUT_DIR"), "/capnp/persistent_capnp.rs"));
}

pub mod schema {
    pub use crate::{
        activity_capnp, api_session_capnp, grain_capnp, identity_capnp, ip_capnp,
        package_rust_capnp, powerbox_capnp, supervisor_capnp, util_capnp, web_session_capnp,
    };
}
