//! Bounded, typed WebSession calls. These values are protocol inputs, not Mini authority.
use crate::{util_capnp, web_session_capnp as web};
use std::{cell::RefCell, rc::Rc, time::Duration};

const MAX_PATH: usize = 8192;
const MAX_BODY: usize = 8 * 1024 * 1024;
const MAX_FIELDS: usize = 128;
const MAX_FIELD: usize = 8192;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Method {
    Get,
    Head,
    Post,
    Put,
    Patch,
    Delete,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub name: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cookie {
    pub name: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CookieExpiry {
    None,
    Absolute(i64),
    Relative(u64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetCookie {
    pub name: String,
    pub value: String,
    pub path: String,
    pub http_only: bool,
    pub expiry: CookieExpiry,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ETag {
    pub value: String,
    pub weak: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum ETagPrecondition {
    #[default]
    None,
    Exists,
    DoesNotExist,
    MatchesOneOf(Vec<ETag>),
    MatchesNoneOf(Vec<ETag>),
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct RequestContext {
    pub cookies: Vec<Cookie>,
    pub accept: Vec<(String, u16)>, // q-value in thousandths
    pub accept_encoding: Vec<(String, u16)>,
    pub additional_headers: Vec<Header>,
    pub etag_precondition: ETagPrecondition,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Body {
    pub mime_type: String,
    pub encoding: String,
    pub bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WebRequest {
    pub method: Method,
    /// Relative Sandstorm path, including the exact query suffix. The schema has no query field.
    pub path_and_query: String,
    pub context: RequestContext,
    pub body: Option<Body>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WebResult {
    Content {
        status: u16,
        mime_type: String,
        encoding: String,
        language: String,
        etag: Option<ETag>,
        body: Vec<u8>,
        download_name: Option<String>,
    },
    NoContent {
        reset_form: bool,
        etag: Option<ETag>,
    },
    PreconditionFailed {
        matching_etag: Option<ETag>,
    },
    Redirect {
        permanent: bool,
        switch_to_get: bool,
        location: String,
    },
    ClientError {
        status: u16,
        html: String,
        non_html: Option<(String, Vec<u8>)>,
    },
    ServerError {
        html: String,
        non_html: Option<(String, Vec<u8>)>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WebResponse {
    pub result: WebResult,
    pub headers: Vec<Header>,
    pub set_cookies: Vec<SetCookie>,
}

fn error(message: &str) -> capnp::Error {
    capnp::Error::failed(message.into())
}
fn bounded(text: &str, max: usize) -> capnp::Result<()> {
    if text.len() > max || text.contains(['\r', '\n', '\0']) {
        Err(error("invalid or oversized WebSession text"))
    } else {
        Ok(())
    }
}
fn allowed_header(name: &str, response: bool) -> bool {
    if name.starts_with("x-sandstorm-app-") {
        return true;
    }
    if response {
        return name == "x-oc-mtime";
    }
    matches!(
        name,
        "oc-total-length"
            | "oc-chunk-size"
            | "x-oc-mtime"
            | "oc-fileid"
            | "oc-chunked"
            | "oc-checksum"
            | "oc-chunk-offset"
            | "oc-lazyops"
            | "x-requested-with"
            | "x-csrftoken"
            | "x-csrf-token"
    ) || name.starts_with("x-hgarg-")
        || name.starts_with("x-phabricator-")
}
fn validate(request: &WebRequest, max_response: usize) -> capnp::Result<()> {
    let path = &request.path_and_query;
    if path.starts_with('/') || path.contains('#') {
        return Err(error("Sandstorm path must be relative without fragment"));
    }
    bounded(path, MAX_PATH)?;
    if max_response > MAX_BODY {
        return Err(error("response bound exceeds transport maximum"));
    }
    match request.method {
        Method::Post | Method::Put | Method::Patch if request.body.is_none() => {
            return Err(error("method requires typed body"))
        }
        Method::Get | Method::Head | Method::Delete if request.body.is_some() => {
            return Err(error("method does not carry a body"))
        }
        _ => {}
    }
    if let Some(body) = &request.body {
        bounded(&body.mime_type, 256)?;
        bounded(&body.encoding, 128)?;
        if body.bytes.len() > MAX_BODY {
            return Err(error("request body exceeds transport bound"));
        }
    }
    let c = &request.context;
    if c.cookies.len() > MAX_FIELDS
        || c.accept.len() > MAX_FIELDS
        || c.accept_encoding.len() > MAX_FIELDS
        || c.additional_headers.len() > MAX_FIELDS
    {
        return Err(error("too many WebSession fields"));
    }
    for cookie in &c.cookies {
        bounded(&cookie.name, MAX_FIELD)?;
        bounded(&cookie.value, MAX_FIELD)?;
        if cookie.name.contains(['=', ';', ',']) || cookie.value.contains([';', ',']) {
            return Err(error("invalid cookie"));
        }
    }
    for (value, q) in c.accept.iter().chain(c.accept_encoding.iter()) {
        bounded(value, MAX_FIELD)?;
        if *q > 1000 {
            return Err(error("invalid quality value"));
        }
    }
    for h in &c.additional_headers {
        bounded(&h.name, 128)?;
        bounded(&h.value, MAX_FIELD)?;
        if h.name != h.name.to_ascii_lowercase() || !allowed_header(&h.name, false) {
            return Err(error("header outside Sandstorm whitelist"));
        }
    }
    let tags = match &c.etag_precondition {
        ETagPrecondition::MatchesOneOf(tags) | ETagPrecondition::MatchesNoneOf(tags) => {
            tags.as_slice()
        }
        _ => &[],
    };
    if tags.len() > MAX_FIELDS {
        return Err(error("too many ETags"));
    }
    for tag in tags {
        bounded(&tag.value, MAX_FIELD)?;
    }
    Ok(())
}

#[derive(Default)]
struct StreamState {
    bytes: Vec<u8>,
    done: bool,
    failed: bool,
    expected: Option<u64>,
}
struct ResponseStream {
    state: Rc<RefCell<StreamState>>,
    max: usize,
    wake: Rc<tokio::sync::Notify>,
}
impl util_capnp::byte_stream::Server for ResponseStream {
    async fn write(
        self: capnp::capability::Rc<Self>,
        params: util_capnp::byte_stream::WriteParams,
    ) -> capnp::Result<()> {
        let data = params.get()?.get_data()?;
        let mut state = self.state.borrow_mut();
        if state.done || data.len() > self.max.saturating_sub(state.bytes.len()) {
            state.failed = true;
            self.wake.notify_waiters();
            return Err(error("response stream exceeds bound or wrote after done"));
        }
        state.bytes.extend_from_slice(data);
        self.wake.notify_waiters();
        Ok(())
    }
    async fn expect_size(
        self: capnp::capability::Rc<Self>,
        params: util_capnp::byte_stream::ExpectSizeParams,
        _: util_capnp::byte_stream::ExpectSizeResults,
    ) -> capnp::Result<()> {
        let size = params.get()?.get_size();
        if size > self.max as u64 {
            self.state.borrow_mut().failed = true;
            self.wake.notify_waiters();
            return Err(error("response stream declared oversized body"));
        }
        self.state.borrow_mut().expected = Some(size);
        Ok(())
    }
    async fn done(
        self: capnp::capability::Rc<Self>,
        _: util_capnp::byte_stream::DoneParams,
        _: util_capnp::byte_stream::DoneResults,
    ) -> capnp::Result<()> {
        let mut state = self.state.borrow_mut();
        if state.done {
            return Err(error("response stream duplicate done"));
        }
        state.done = true;
        if state
            .expected
            .is_some_and(|n| n != state.bytes.len() as u64)
        {
            state.failed = true;
        }
        self.wake.notify_waiters();
        Ok(())
    }
}

fn fill_context(
    mut ctx: web::web_session::context::Builder<'_>,
    c: &RequestContext,
    stream: util_capnp::byte_stream::Client,
) {
    ctx.set_response_stream(stream);
    let mut cookies = ctx.reborrow().init_cookies(c.cookies.len() as u32);
    for (i, cookie) in c.cookies.iter().enumerate() {
        let mut kv = cookies.reborrow().get(i as u32);
        kv.set_key(&cookie.name);
        kv.set_value(&cookie.value);
    }
    let mut accept = ctx.reborrow().init_accept(c.accept.len() as u32);
    for (i, (name, q)) in c.accept.iter().enumerate() {
        let mut value = accept.reborrow().get(i as u32);
        value.set_mime_type(name);
        value.set_q_value(*q as f32 / 1000.0);
    }
    let mut enc = ctx
        .reborrow()
        .init_accept_encoding(c.accept_encoding.len() as u32);
    for (i, (name, q)) in c.accept_encoding.iter().enumerate() {
        let mut value = enc.reborrow().get(i as u32);
        value.set_content_coding(name);
        value.set_q_value(*q as f32 / 1000.0);
    }
    let mut headers = ctx
        .reborrow()
        .init_additional_headers(c.additional_headers.len() as u32);
    for (i, h) in c.additional_headers.iter().enumerate() {
        let mut value = headers.reborrow().get(i as u32);
        value.set_name(&h.name);
        value.set_value(&h.value);
    }
    let mut pre = ctx.init_e_tag_precondition();
    match &c.etag_precondition {
        ETagPrecondition::None => pre.set_none(()),
        ETagPrecondition::Exists => pre.set_exists(()),
        ETagPrecondition::DoesNotExist => pre.set_doesnt_exist(()),
        ETagPrecondition::MatchesOneOf(values) => {
            let mut tags = pre.init_matches_one_of(values.len() as u32);
            for (i, t) in values.iter().enumerate() {
                let mut tag = tags.reborrow().get(i as u32);
                tag.set_value(&t.value);
                tag.set_weak(t.weak);
            }
        }
        ETagPrecondition::MatchesNoneOf(values) => {
            let mut tags = pre.init_matches_none_of(values.len() as u32);
            for (i, t) in values.iter().enumerate() {
                let mut tag = tags.reborrow().get(i as u32);
                tag.set_value(&t.value);
                tag.set_weak(t.weak);
            }
        }
    }
}

fn text(value: capnp::Result<capnp::text::Reader<'_>>) -> capnp::Result<String> {
    Ok(value?.to_str()?.to_owned())
}
fn optional_tag(
    value: capnp::Result<web::web_session::e_tag::Reader<'_>>,
) -> capnp::Result<Option<ETag>> {
    let value = value?;
    if value.get_value()?.is_empty() {
        Ok(None)
    } else {
        Ok(Some(ETag {
            value: text(value.get_value())?,
            weak: value.get_weak(),
        }))
    }
}
fn parse_response(
    reply: web::web_session::response::Reader<'_>,
    stream: &Rc<RefCell<StreamState>>,
    max: usize,
) -> capnp::Result<(WebResponse, Option<util_capnp::handle::Client>)> {
    use web::web_session::response::{self, content};
    let mut headers = Vec::new();
    let raw_headers = reply.get_additional_headers()?;
    if raw_headers.len() as usize > MAX_FIELDS {
        return Err(error("too many response headers"));
    }
    for h in raw_headers.iter() {
        let name = text(h.get_name())?;
        let value = text(h.get_value())?;
        bounded(&name, 128)?;
        bounded(&value, MAX_FIELD)?;
        if name != name.to_ascii_lowercase() || !allowed_header(&name, true) {
            return Err(error("app returned unrepresentable header"));
        }
        headers.push(Header { name, value });
    }
    let mut set_cookies = Vec::new();
    let raw_cookies = reply.get_set_cookies()?;
    if raw_cookies.len() as usize > MAX_FIELDS {
        return Err(error("too many set-cookies"));
    }
    for c in raw_cookies.iter() {
        use web::web_session::cookie::expires;
        let name = text(c.get_name())?;
        let value = text(c.get_value())?;
        let path = text(c.get_path())?;
        bounded(&name, MAX_FIELD)?;
        bounded(&value, MAX_FIELD)?;
        bounded(&path, MAX_PATH)?;
        let expiry = match c.get_expires().which().map_err(|e| error(&e.to_string()))? {
            expires::Which::None(()) => CookieExpiry::None,
            expires::Which::Absolute(t) => CookieExpiry::Absolute(t),
            expires::Which::Relative(t) => CookieExpiry::Relative(t),
        };
        set_cookies.push(SetCookie {
            name,
            value,
            path,
            http_only: c.get_http_only(),
            expiry,
        });
    }
    let mut stream_handle = None;
    let result = match reply.which().map_err(|e| error(&e.to_string()))? {
        response::Which::Content(v) => {
            let status = match v.get_status_code().map_err(|e| error(&e.to_string()))? {
                response::SuccessCode::Ok => 200,
                response::SuccessCode::Created => 201,
                response::SuccessCode::Accepted => 202,
                response::SuccessCode::NoContent => 204,
                response::SuccessCode::PartialContent => 206,
                response::SuccessCode::MultiStatus => 207,
                response::SuccessCode::NotModified => 304,
            };
            let body = match v.get_body().which().map_err(|e| error(&e.to_string()))? {
                content::body::Which::Bytes(bytes) => {
                    let bytes = bytes?.to_vec();
                    if bytes.len() > max {
                        return Err(error("response body exceeds bound"));
                    }
                    bytes
                }
                content::body::Which::Stream(handle) => {
                    stream_handle = Some(handle?);
                    Vec::new()
                }
            };
            let download_name = match v
                .get_disposition()
                .which()
                .map_err(|e| error(&e.to_string()))?
            {
                content::disposition::Which::Normal(()) => None,
                content::disposition::Which::Download(name) => Some(text(name)?),
            };
            WebResult::Content {
                status,
                mime_type: text(v.get_mime_type())?,
                encoding: text(v.get_encoding())?,
                language: text(v.get_language())?,
                etag: optional_tag(v.get_e_tag())?,
                body,
                download_name,
            }
        }
        response::Which::NoContent(v) => WebResult::NoContent {
            reset_form: v.get_should_reset_form(),
            etag: optional_tag(v.get_e_tag())?,
        },
        response::Which::PreconditionFailed(v) => WebResult::PreconditionFailed {
            matching_etag: optional_tag(v.get_matching_e_tag())?,
        },
        response::Which::Redirect(v) => WebResult::Redirect {
            permanent: v.get_is_permanent(),
            switch_to_get: v.get_switch_to_get(),
            location: text(v.get_location())?,
        },
        response::Which::ClientError(v) => {
            let status = match v.get_status_code().map_err(|e| error(&e.to_string()))? {
                response::ClientErrorCode::BadRequest => 400,
                response::ClientErrorCode::Forbidden => 403,
                response::ClientErrorCode::NotFound => 404,
                response::ClientErrorCode::MethodNotAllowed => 405,
                response::ClientErrorCode::NotAcceptable => 406,
                response::ClientErrorCode::Conflict => 409,
                response::ClientErrorCode::Gone => 410,
                response::ClientErrorCode::PreconditionFailed => 412,
                response::ClientErrorCode::RequestEntityTooLarge => 413,
                response::ClientErrorCode::RequestUriTooLong => 414,
                response::ClientErrorCode::UnsupportedMediaType => 415,
                response::ClientErrorCode::ImATeapot => 418,
                response::ClientErrorCode::UnprocessableEntity => 422,
            };
            WebResult::ClientError {
                status,
                html: text(v.get_description_html())?,
                non_html: error_body(v.get_non_html_body(), max)?,
            }
        }
        response::Which::ServerError(v) => WebResult::ServerError {
            html: text(v.get_description_html())?,
            non_html: error_body(v.get_non_html_body(), max)?,
        },
    };
    if stream_handle.is_none() && (!stream.borrow().bytes.is_empty() || stream.borrow().done) {
        return Err(error("unexpected response stream writes"));
    }
    Ok((
        WebResponse {
            result,
            headers,
            set_cookies,
        },
        stream_handle,
    ))
}
fn error_body(
    value: capnp::Result<web::web_session::response::error_body::Reader<'_>>,
    max: usize,
) -> capnp::Result<Option<(String, Vec<u8>)>> {
    let value = value?;
    let bytes = value.get_data()?.to_vec();
    if bytes.len() > max {
        return Err(error("error body exceeds bound"));
    }
    if bytes.is_empty() {
        Ok(None)
    } else {
        Ok(Some((text(value.get_mime_type())?, bytes)))
    }
}

/// Dispatches one already-authorized operation over the actual Sandstorm WebSession RPC.
/// Timeout is a transport bound; after it fires, delivery may be uncertain.
pub async fn dispatch_web(
    session: &web::web_session::Client,
    request: &WebRequest,
    max_response: usize,
    timeout: Duration,
) -> capnp::Result<WebResponse> {
    validate(request, max_response)?;
    let state = Rc::new(RefCell::new(StreamState::default()));
    let wake = Rc::new(tokio::sync::Notify::new());
    let stream: util_capnp::byte_stream::Client = capnp_rpc::new_client(ResponseStream {
        state: state.clone(),
        max: max_response,
        wake: wake.clone(),
    });
    let path = &request.path_and_query;
    let future = async {
        let (mut response, stream_handle) = match request.method {
            Method::Get | Method::Head => {
                let mut call = session.get_request();
                let mut p = call.get();
                p.set_path(path);
                p.set_ignore_body(request.method == Method::Head);
                fill_context(p.init_context(), &request.context, stream.clone());
                parse_response(call.send().promise.await?.get()?, &state, max_response)?
            }
            Method::Delete => {
                let mut call = session.delete_request();
                let mut p = call.get();
                p.set_path(path);
                fill_context(p.init_context(), &request.context, stream.clone());
                parse_response(call.send().promise.await?.get()?, &state, max_response)?
            }
            Method::Post => {
                let mut call = session.post_request();
                let mut p = call.get();
                p.set_path(path);
                let body = request.body.as_ref().expect("validated");
                let mut content = p.reborrow().init_content();
                content.set_mime_type(&body.mime_type);
                content.set_encoding(&body.encoding);
                content.set_content(&body.bytes);
                fill_context(p.init_context(), &request.context, stream.clone());
                parse_response(call.send().promise.await?.get()?, &state, max_response)?
            }
            Method::Patch => {
                let mut call = session.patch_request();
                let mut p = call.get();
                p.set_path(path);
                let body = request.body.as_ref().expect("validated");
                let mut content = p.reborrow().init_content();
                content.set_mime_type(&body.mime_type);
                content.set_encoding(&body.encoding);
                content.set_content(&body.bytes);
                fill_context(p.init_context(), &request.context, stream.clone());
                parse_response(call.send().promise.await?.get()?, &state, max_response)?
            }
            Method::Put => {
                let mut call = session.put_request();
                let mut p = call.get();
                p.set_path(path);
                let body = request.body.as_ref().expect("validated");
                let mut content = p.reborrow().init_content();
                content.set_mime_type(&body.mime_type);
                content.set_encoding(&body.encoding);
                content.set_content(&body.bytes);
                fill_context(p.init_context(), &request.context, stream);
                parse_response(call.send().promise.await?.get()?, &state, max_response)?
            }
        };
        if stream_handle.is_some() {
            loop {
                let notified = wake.notified();
                let done = {
                    let s = state.borrow();
                    if s.failed {
                        return Err(error("response stream failed"));
                    }
                    s.done
                };
                if done {
                    break;
                }
                notified.await;
            }
            if let WebResult::Content { body, .. } = &mut response.result {
                *body = state.borrow().bytes.clone();
            }
        }
        drop(stream_handle);
        Ok(response)
    };
    tokio::time::timeout(timeout, future)
        .await
        .map_err(|_| error("WebSession RPC deadline exceeded; delivery uncertain"))?
}

/// One already-admitted `openWebSocket` (`web-session.capnp` @2). The Mini
/// write is the open; what follows are opaque WebSocket protocol bytes inside
/// the admitted session, in both directions, never parsed here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WebSocketOpen {
    /// Relative Sandstorm path, including the exact query suffix.
    pub path_and_query: String,
    pub context: RequestContext,
    /// The client's requested subprotocols, `Sec-WebSocket-Protocol`, in order.
    pub protocols: Vec<String>,
}

/// An opened socket. `to_app` carries client→app bytes (`serverStream`);
/// `from_app` yields app→client bytes and ends when the app drops the
/// `clientStream` it was given. Dropping `to_app` is the close toward the app.
pub struct WebSocketSession {
    pub protocols: Vec<String>,
    pub to_app: web::web_session::web_socket_stream::Client,
    pub from_app: tokio::sync::mpsc::Receiver<Vec<u8>>,
}

/// Bytes the app may have in flight toward one client before its
/// `sendBytes` waits (Cap'n Proto streaming carries the backpressure).
const FROM_APP_QUEUE: usize = 16;
/// The largest single `sendBytes` message accepted from the app.
pub const MAX_WEBSOCKET_MESSAGE: usize = 1024 * 1024;
const MAX_PROTOCOLS: usize = 32;

struct ClientStream {
    to_client: tokio::sync::mpsc::Sender<Vec<u8>>,
}
impl web::web_session::web_socket_stream::Server for ClientStream {
    async fn send_bytes(
        self: capnp::capability::Rc<Self>,
        params: web::web_session::web_socket_stream::SendBytesParams,
    ) -> capnp::Result<()> {
        let message = params.get()?.get_message()?;
        if message.len() > MAX_WEBSOCKET_MESSAGE {
            return Err(error("app WebSocket message exceeds transport bound"));
        }
        self.to_client
            .send(message.to_vec())
            .await
            .map_err(|_| error("WebSocket client side closed"))
    }
}

/// A WebSocket open has no HTTP response body; the context's response stream
/// refuses every write.
struct NoResponseStream;
impl util_capnp::byte_stream::Server for NoResponseStream {}

fn protocol_token(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 256
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"!#$%&'*+-.^_`|~".contains(&byte))
}

/// Calls `openWebSocket` on an already-admitted WebSession. The app's chosen
/// subprotocols must be among those the client requested.
pub async fn open_web_socket(
    session: &web::web_session::Client,
    open: &WebSocketOpen,
    timeout: Duration,
) -> capnp::Result<WebSocketSession> {
    let path = &open.path_and_query;
    if path.starts_with('/') || path.contains('#') {
        return Err(error("Sandstorm path must be relative without fragment"));
    }
    bounded(path, MAX_PATH)?;
    if open.protocols.len() > MAX_PROTOCOLS || !open.protocols.iter().all(|p| protocol_token(p)) {
        return Err(error("WebSocket subprotocol list outside protocol bound"));
    }
    validate(
        &WebRequest {
            method: Method::Get,
            path_and_query: open.path_and_query.clone(),
            context: open.context.clone(),
            body: None,
        },
        0,
    )?;
    let (to_client, from_app) = tokio::sync::mpsc::channel(FROM_APP_QUEUE);
    let client_stream: web::web_session::web_socket_stream::Client =
        capnp_rpc::new_client(ClientStream { to_client });
    let no_body: util_capnp::byte_stream::Client = capnp_rpc::new_client(NoResponseStream);
    let future = async {
        let mut call = session.open_web_socket_request();
        let mut p = call.get();
        p.set_path(path);
        fill_context(p.reborrow().init_context(), &open.context, no_body);
        let mut protocols = p.reborrow().init_protocol(open.protocols.len() as u32);
        for (index, protocol) in open.protocols.iter().enumerate() {
            protocols.set(index as u32, protocol.as_str());
        }
        p.set_client_stream(client_stream);
        let reply = call.send().promise.await?;
        let reply = reply.get()?;
        let chosen = reply.get_protocol()?;
        if chosen.len() as usize > MAX_PROTOCOLS {
            return Err(error("app chose too many WebSocket subprotocols"));
        }
        let mut accepted = Vec::new();
        for protocol in chosen.iter() {
            let protocol = protocol?.to_str()?.to_owned();
            if !open.protocols.contains(&protocol) {
                return Err(error("app chose a WebSocket subprotocol the client did not offer"));
            }
            accepted.push(protocol);
        }
        Ok(WebSocketSession {
            protocols: accepted,
            to_app: reply.get_server_stream()?,
            from_app,
        })
    };
    tokio::time::timeout(timeout, future)
        .await
        .map_err(|_| error("WebSocket open RPC deadline exceeded; open uncertain"))?
}

/// Client→app bytes, one `sendBytes` (Cap'n Proto streaming: the returned
/// future resolves under the connection's flow-control window).
pub async fn send_to_app(
    to_app: &web::web_session::web_socket_stream::Client,
    bytes: &[u8],
) -> capnp::Result<()> {
    let mut call = to_app.send_bytes_request();
    call.get().set_message(bytes);
    call.send().await
}
