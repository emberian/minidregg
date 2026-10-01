//! Physical mapping of an already matched Mini request to packaged WebSession
//! values. Only the source checked principal and effective ordered bits enter
//! Sandstorm session identity/permissions; HTTP labels and headers grant none.
#![allow(dead_code)] // No HTTP delivery until native op34/claim join is complete.

use crate::dispatch_inspection::{
    HttpProjection, MatchedInspection, Route, STREAMED_OPEN_METHOD,
};
use crate::rpc_adapter::{SessionBinding, SessionKind};
use minidregg_spk_rpc::{
    Body, Cookie, ETag, ETagPrecondition, Header, Method, RequestContext, SessionParameters,
    WebRequest, WebSocketOpen,
};
use std::io;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn quality_list(value: &str) -> io::Result<Vec<(String, u16)>> {
    let mut result = Vec::new();
    for part in value.split(',') {
        let part = part.trim();
        let (name, quality) = if let Some((name, suffix)) = part.split_once(';') {
            let decimal = suffix
                .trim()
                .strip_prefix("q=")
                .ok_or_else(|| invalid("unsupported HTTP quality parameter"))?;
            let (whole, fractional) = decimal.split_once('.').unwrap_or((decimal, ""));
            if !matches!(whole, "0" | "1")
                || fractional.len() > 3
                || !fractional.bytes().all(|b| b.is_ascii_digit())
            {
                return Err(invalid("invalid HTTP quality"));
            }
            let fraction = format!("{fractional:0<3}")
                .parse::<u16>()
                .map_err(|_| invalid("invalid HTTP quality"))?;
            let q = whole.parse::<u16>().unwrap() * 1000 + fraction;
            if q > 1000 {
                return Err(invalid("HTTP quality exceeds one"));
            }
            (name.trim(), q)
        } else {
            (part, 1000)
        };
        if name.is_empty() || name.len() > 8192 || name.contains(['\r', '\n', '\0']) {
            return Err(invalid("invalid HTTP weighted value"));
        }
        result.push((name.to_owned(), quality));
        if result.len() > 128 {
            return Err(invalid("too many HTTP weighted values"));
        }
    }
    Ok(result)
}

fn cookies(value: &str) -> io::Result<Vec<Cookie>> {
    let mut result = Vec::new();
    for part in value.split(';') {
        let (name, value) = part
            .trim()
            .split_once('=')
            .ok_or_else(|| invalid("malformed app cookie"))?;
        if name.is_empty()
            || name.len() > 8192
            || value.len() > 8192
            || name.contains(['=', ';', ','])
            || value.contains([';', ','])
        {
            return Err(invalid("app cookie outside protocol bound"));
        }
        result.push(Cookie {
            name: name.to_owned(),
            value: value.to_owned(),
        });
        if result.len() > 128 {
            return Err(invalid("too many app cookies"));
        }
    }
    Ok(result)
}

fn etags(value: &str, matches: bool) -> io::Result<ETagPrecondition> {
    if value == "*" {
        return Ok(if matches {
            ETagPrecondition::Exists
        } else {
            ETagPrecondition::DoesNotExist
        });
    }
    let mut tags = Vec::new();
    for part in value.split(',') {
        let part = part.trim();
        let (weak, quoted) = if let Some(rest) = part.strip_prefix("W/") {
            (true, rest)
        } else {
            (false, part)
        };
        let tag = quoted
            .strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .ok_or_else(|| invalid("unsupported HTTP ETag syntax"))?;
        if tag.len() > 8192 || tag.bytes().any(|b| b < 0x20 || b == 0x7f || b == b'"') {
            return Err(invalid("invalid HTTP ETag"));
        }
        tags.push(ETag {
            value: tag.to_owned(),
            weak,
        });
        if tags.len() > 128 {
            return Err(invalid("too many HTTP ETags"));
        }
    }
    Ok(if matches {
        ETagPrecondition::MatchesOneOf(tags)
    } else {
        ETagPrecondition::MatchesNoneOf(tags)
    })
}

pub(crate) struct PhysicalWebInput {
    pub binding: SessionBinding,
    pub request: WebRequest,
}

/// An admitted streamed dispatch: the WebSocket open's session and call.
pub(crate) struct PhysicalOpenInput {
    pub binding: SessionBinding,
    pub open: WebSocketOpen,
}

/// The one physical call a committed request reaches.
enum Call {
    Exchange(Method),
    Open,
}

/// The streamed open of the same matched request. Only a record whose method
/// is the streamed-open token projects here; every other header rule is the
/// exchange's, plus the signed subprotocol list.
pub(crate) fn physical_open_input(
    matched: &MatchedInspection,
    http: &HttpProjection<'_>,
    display_name: &str,
    preferred_handle: &str,
    base_path: &str,
) -> io::Result<PhysicalOpenInput> {
    let (binding, call, context, body, protocols) =
        project(matched, http, display_name, preferred_handle, base_path)?;
    match (call, body) {
        (Call::Open, None) => Ok(PhysicalOpenInput {
            binding,
            open: WebSocketOpen {
                path_and_query: matched.app_path_and_query.clone(),
                context,
                protocols,
            },
        }),
        _ => Err(invalid("Mini record is not a streamed open")),
    }
}

/// `matched` must come from the private op34+source-inspection comparison.
/// The display label/handle are operator-configured UI text, never auth data.
/// Every accepted ordinary HTTP header is represented or the call refuses;
/// there is no silent drop of a Mini-signed header.
/// `base_path` is the browser route's origin, `https://HOST` with no
/// trailing slash: Sandstorm's `WebSession.Params.basePath`, from which
/// sandstorm-http-bridge builds `X-Sandstorm-Base-Path` and absolute URLs.
/// The bridge refuses anything without a scheme ("Base URL does not have a
/// protocol scheme"), so the old "/" failed every web session at its first
/// request (SPK-APPS 2026-10-01: EtherCalc, WordPress, Gogs, Hacker Slides,
/// Roundcube, Simple Todos all 503). An API session carries no base path.
pub(crate) fn physical_web_input(
    matched: &MatchedInspection,
    http: &HttpProjection<'_>,
    display_name: &str,
    preferred_handle: &str,
    base_path: &str,
) -> io::Result<PhysicalWebInput> {
    let (binding, call, context, body, _) =
        project(matched, http, display_name, preferred_handle, base_path)?;
    let Call::Exchange(method) = call else {
        return Err(invalid("a streamed open is not a WebSession exchange"));
    };
    Ok(PhysicalWebInput {
        binding,
        request: WebRequest {
            method,
            path_and_query: matched.app_path_and_query.clone(),
            context,
            body,
        },
    })
}

#[allow(clippy::type_complexity)]
fn project(
    matched: &MatchedInspection,
    http: &HttpProjection<'_>,
    display_name: &str,
    preferred_handle: &str,
    base_path: &str,
) -> io::Result<(SessionBinding, Call, RequestContext, Option<Body>, Vec<String>)> {
    let call = match matched.method.as_str() {
        "GET" => Call::Exchange(Method::Get),
        "HEAD" => Call::Exchange(Method::Head),
        "POST" => Call::Exchange(Method::Post),
        "PUT" => Call::Exchange(Method::Put),
        "PATCH" => Call::Exchange(Method::Patch),
        "DELETE" => Call::Exchange(Method::Delete),
        STREAMED_OPEN_METHOD => Call::Open,
        _ => return Err(invalid("Mini method unavailable to WebSession")),
    };
    let mut protocols = None;
    if display_name.len() > 1024
        || preferred_handle.len() > 256
        || display_name.contains(['\r', '\n', '\0'])
        || preferred_handle.contains(['\r', '\n', '\0'])
    {
        return Err(invalid("operator display label outside protocol bound"));
    }
    let mut context = RequestContext::default();
    let mut content_type = None;
    let mut user_agent = None;
    for (name, value) in http.ordered_headers {
        match name.as_str() {
            "accept" => context.accept.extend(quality_list(value)?),
            "accept-encoding" => context.accept_encoding.extend(quality_list(value)?),
            "cookie" => context.cookies.extend(cookies(value)?),
            "content-type" => {
                if value.len() > 256 {
                    return Err(invalid("content-type exceeds WebSession bound"));
                }
                if content_type.replace(value.as_str()).is_some() {
                    return Err(invalid("duplicate content-type"));
                }
            }
            "user-agent" => {
                if value.len() > 4096 {
                    return Err(invalid("user-agent exceeds WebSession bound"));
                }
                if user_agent.replace(value.as_str()).is_some() {
                    return Err(invalid("duplicate user-agent"));
                }
            }
            "if-match" | "if-none-match" => {
                if context.etag_precondition != ETagPrecondition::None {
                    return Err(invalid("conflicting HTTP ETag preconditions"));
                }
                context.etag_precondition = etags(value, name == "if-match")?;
            }
            "x-requested-with" | "x-csrftoken" | "x-csrf-token" | "oc-total-length"
            | "oc-chunk-size" | "x-oc-mtime" | "oc-fileid" | "oc-chunked" | "oc-checksum"
            | "oc-chunk-offset" | "oc-lazyops" => {
                context.additional_headers.push(Header {
                    name: name.clone(),
                    value: value.clone(),
                });
            }
            "sec-websocket-protocol" if matches!(call, Call::Open) => {
                if protocols
                    .replace(crate::web_socket::protocols(Some(value))?)
                    .is_some()
                {
                    return Err(invalid("duplicate WebSocket subprotocol list"));
                }
            }
            _ => {
                return Err(invalid(
                    "Mini signed header has no physical WebSession mapping",
                ))
            }
        }
    }
    if context.accept.len() > 128
        || context.accept_encoding.len() > 128
        || context.cookies.len() > 128
        || context.additional_headers.len() > 128
    {
        return Err(invalid("WebSession context category exceeds bound"));
    }
    let body = if matches!(
        call,
        Call::Exchange(Method::Post | Method::Put | Method::Patch)
    ) {
        let mime_type = content_type.unwrap_or("");
        Some(Body {
            mime_type: mime_type.to_owned(),
            encoding: String::new(),
            bytes: http.body.to_vec(),
        })
    } else {
        if content_type.is_some() || !http.body.is_empty() {
            return Err(invalid("body/header on bodyless WebSession method"));
        }
        None
    };
    let (kind, base_path) = match http.route {
        Route::Browser => {
            let host = base_path
                .strip_prefix("https://")
                .ok_or_else(|| invalid("browser session base path is not an https origin"))?;
            if host.is_empty()
                || host.len() > 253
                || !host
                    .bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'.' || b == b'-')
            {
                return Err(invalid("browser session base path is not an https origin"));
            }
            (SessionKind::Web, base_path.to_owned())
        }
        Route::Api { .. } => (SessionKind::Api, String::new()),
    };
    Ok((
        SessionBinding {
            app: matched.app,
            process_generation: matched.app_generation,
            session_resource: matched
                .session_resource
                .parse()
                .map_err(|_| invalid("Mini session resource exceeds physical host range"))?,
            subject: matched
                .subject
                .parse()
                .map_err(|_| invalid("Mini subject exceeds physical host range"))?,
            projection_fingerprint: matched.session_fingerprint,
            kind,
            params: SessionParameters {
                identity_id: matched.principal,
                display_name: display_name.to_owned(),
                preferred_handle: preferred_handle.to_owned(),
                permissions: matched.effective_bits.clone(),
                tab_id: Vec::new(),
                base_path,
                user_agent: user_agent.unwrap_or("Mini SPK Host").to_owned(),
                acceptable_languages: Vec::new(),
            },
        },
        call,
        context,
        body,
        protocols.unwrap_or_default(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn matched() -> MatchedInspection {
        MatchedInspection {
            app: 6100,
            app_generation: 1,
            session_resource: "6209".into(),
            session_generation: "0".into(),
            subject: "9".into(),
            operation_id: "7".into(),
            physical_request_digest: "123".into(),
            dispatch_transaction: "456".into(),
            dispatch_event: "789".into(),
            session_fingerprint: [42; 32],
            principal: [0xaa; 32],
            before_world_root: "111".into(),
            after_world_root: "222".into(),
            accepted_count: "12".into(),
            effective_bits: vec![true, false],
            app_path_and_query: "repo.git/git-receive-pack".into(),
            method: "POST".into(),
        }
    }

    #[test]
    fn signed_git_push_body_and_identity_reach_typed_api_session() {
        let body = b"0010want deadbeef\n";
        let headers = vec![
            (
                "content-type".into(),
                "application/x-git-receive-pack-request".into(),
            ),
            (
                "accept".into(),
                "application/x-git-receive-pack-result".into(),
            ),
        ];
        let http = HttpProjection {
            method: "POST",
            path_and_query: "git-receive-pack",
            ordered_headers: &headers,
            body,
            route: Route::Api {
                signed_path: "/repo.git/",
            },
        };
        let projected = physical_web_input(&matched(), &http, "Friend", "friend", "https://friend.example.test").unwrap();
        assert_eq!(projected.binding.params.identity_id, [0xaa; 32]);
        assert_eq!(projected.binding.params.permissions, [true, false]);
        assert_eq!(projected.binding.kind, SessionKind::Api);
        assert_eq!(
            projected.request.path_and_query,
            "repo.git/git-receive-pack"
        );
        assert_eq!(projected.request.body.unwrap().bytes, body);
    }

    #[test]
    fn root_signed_api_poll_reaches_typed_session_with_exact_query() {
        let mut source = matched();
        source.method = "GET".into();
        source.app_path_and_query = "team/json?poll=1".into();
        let http = HttpProjection {
            method: "GET",
            path_and_query: "team/json?poll=1",
            ordered_headers: &[],
            body: b"",
            route: Route::Api { signed_path: "/" },
        };
        let projected = physical_web_input(&source, &http, "Friend", "friend", "https://friend.example.test").unwrap();
        assert_eq!(projected.binding.kind, SessionKind::Api);
        assert_eq!(projected.binding.params.identity_id, [0xaa; 32]);
        assert_eq!(projected.request.path_and_query, "team/json?poll=1");
        assert!(projected.request.body.is_none());

        source.method = "POST".into();
        source.app_path_and_query.clear();
        let headers = vec![("content-type".into(), "application/json".into())];
        let body = br#"{"topic":"team","message":"ready"}"#;
        let post = HttpProjection {
            method: "POST",
            path_and_query: "",
            ordered_headers: &headers,
            body,
            route: Route::Api { signed_path: "/" },
        };
        let projected = physical_web_input(&source, &post, "Friend", "friend", "https://friend.example.test").unwrap();
        assert_eq!(projected.request.path_and_query, "");
        let posted = projected.request.body.unwrap();
        assert_eq!(posted.mime_type, "application/json");
        assert_eq!(posted.bytes, body);
    }

    #[test]
    fn ordinary_browser_headers_map_or_refuse_without_silent_drop() {
        let mut source = matched();
        source.method = "GET".into();
        source.app_path_and_query = "gitweb.cgi?a=summary".into();
        let headers = vec![
            (
                "accept".into(),
                "text/html,application/xhtml+xml;q=0.9".into(),
            ),
            ("cookie".into(), "theme=light; view=compact".into()),
            ("if-none-match".into(), "W/\"rev1\"".into()),
        ];
        let http = HttpProjection {
            method: "GET",
            path_and_query: "gitweb.cgi?a=summary",
            ordered_headers: &headers,
            body: b"",
            route: Route::Browser,
        };
        let projected = physical_web_input(&source, &http, "Friend", "friend", "https://friend.example.test").unwrap();
        assert_eq!(projected.binding.kind, SessionKind::Web);
        assert_eq!(projected.binding.params.base_path, "https://friend.example.test");
        assert!(physical_web_input(&source, &http, "Friend", "friend", "/").is_err());
        assert_eq!(projected.binding.kind, SessionKind::Web);
        assert_eq!(projected.request.context.cookies.len(), 2);
        assert_eq!(
            projected.request.context.accept[1],
            ("application/xhtml+xml".into(), 900)
        );
        let mut unsupported = headers.clone();
        unsupported.push(("x-unknown".into(), "value".into()));
        let http = HttpProjection {
            ordered_headers: &unsupported,
            ..http
        };
        assert!(physical_web_input(&source, &http, "Friend", "friend", "https://friend.example.test").is_err());
    }

    #[test]
    fn empty_post_without_content_type_is_a_typed_body() {
        let headers = Vec::new();
        let http = HttpProjection {
            method: "POST",
            path_and_query: "git-receive-pack",
            ordered_headers: &headers,
            body: b"",
            route: Route::Api {
                signed_path: "/repo.git/",
            },
        };
        let input = physical_web_input(&matched(), &http, "Friend", "friend", "https://friend.example.test").unwrap();
        let body = input.request.body.unwrap();
        assert!(body.bytes.is_empty());
        assert!(body.mime_type.is_empty());
    }

    #[test]
    fn app_cookie_and_session_parameter_wire_bounds_refuse_before_rpc() {
        let headers = vec![("cookie".into(), "session=one,two".into())];
        let http = HttpProjection {
            method: "GET",
            path_and_query: "gitweb.cgi",
            ordered_headers: &headers,
            body: b"",
            route: Route::Browser,
        };
        assert!(physical_web_input(&matched(), &http, "Friend", "friend", "https://friend.example.test").is_err());
        let empty = HttpProjection {
            ordered_headers: &[],
            ..http
        };
        assert!(physical_web_input(&matched(), &empty, &"a".repeat(1025), "friend", "https://friend.example.test").is_err());
        assert!(physical_web_input(&matched(), &empty, "Friend", &"a".repeat(257), "https://friend.example.test").is_err());
        // A browser session needs an https origin as its base path (the bridge
        // refuses a scheme-less one); a path or a foreign scheme is refused here.
        assert!(physical_web_input(&matched(), &empty, "Friend", "friend", "/").is_err());
        assert!(physical_web_input(&matched(), &empty, "Friend", "friend", "http://x.test").is_err());
    }

    /// A streamed record projects only as an open, with its signed
    /// subprotocols; an exchange record never projects as an open, and the
    /// subprotocol header never reaches an exchange.
    #[test]
    fn streamed_record_projects_only_as_an_open() {
        let headers = vec![("sec-websocket-protocol".to_owned(), "chat, superchat".to_owned())];
        let http = HttpProjection {
            method: STREAMED_OPEN_METHOD,
            path_and_query: "websocket",
            ordered_headers: &headers,
            body: b"",
            route: Route::Browser,
        };
        let mut open = matched();
        open.method = STREAMED_OPEN_METHOD.into();
        open.app_path_and_query = "websocket".into();
        let projected =
            physical_open_input(&open, &http, "Friend", "friend", "https://friend.example.test").unwrap();
        assert_eq!(projected.open.protocols, ["chat", "superchat"]);
        assert_eq!(projected.open.path_and_query, "websocket");
        assert_eq!(projected.binding.kind, SessionKind::Web);
        assert!(physical_web_input(&open, &http, "Friend", "friend", "https://friend.example.test").is_err());
        let mut get = matched();
        get.method = "GET".into();
        let get_http = HttpProjection { method: "GET", ..http };
        assert!(physical_open_input(&get, &get_http, "Friend", "friend", "https://friend.example.test").is_err());
        assert!(physical_web_input(&get, &get_http, "Friend", "friend", "https://friend.example.test").is_err());
    }
}