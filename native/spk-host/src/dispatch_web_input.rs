//! Physical mapping of an already matched Mini request to packaged WebSession
//! values. Only the source checked principal and effective ordered bits enter
//! Sandstorm session identity/permissions; HTTP labels and headers grant none.

use crate::dispatch_inspection::{
    HttpProjection, MatchedInspection, Route, STREAMED_OPEN_METHOD,
};
use crate::rpc_adapter::{SessionBinding, SessionKind};
use minidregg_spk_rpc::{
    Body, Cookie, DavArgs, Depth, ETag, ETagPrecondition, Header, Method, RequestContext,
    SessionParameters, WebRequest, WebSocketOpen,
};
use std::io;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn qvalue(decimal: &str) -> io::Result<u16> {
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
    Ok(q)
}

/// RFC 9110 weighted list: `range *( ";" parameter ) [ ";" "q=" qvalue ]`.
/// Media-range parameters such as `v=b3` (Chromium's signed-exchange offer)
/// are part of the value and stay in the WebSession name, so the bridge
/// reconstructs exactly the signed range; only the weight becomes the number.
/// A parameter after the weight is outside the grammar and refuses.
fn quality_list(value: &str) -> io::Result<Vec<(String, u16)>> {
    let mut result = Vec::new();
    for part in value.split(',') {
        let mut pieces = part.split(';');
        let range = pieces.next().unwrap_or("").trim();
        let mut name = range.to_owned();
        let mut quality = None;
        for parameter in pieces {
            let parameter = parameter.trim();
            if quality.is_some() {
                return Err(invalid("HTTP parameter after quality weight"));
            }
            let (key, argument) = parameter
                .split_once('=')
                .ok_or_else(|| invalid("malformed HTTP media parameter"))?;
            if key.is_empty()
                || argument.is_empty()
                || key.trim() != key
                || argument.trim() != argument
            {
                return Err(invalid("malformed HTTP media parameter"));
            }
            if key.eq_ignore_ascii_case("q") {
                quality = Some(qvalue(argument)?);
            } else {
                name.push(';');
                name.push_str(parameter);
            }
        }
        if range.is_empty() || name.len() > 8192 || name.contains(['\r', '\n', '\0']) {
            return Err(invalid("invalid HTTP weighted value"));
        }
        result.push((name, quality.unwrap_or(1000)));
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
        if name == "__Host-mini_spk_session" {
            return Err(invalid("custody session cookie is not an app cookie"));
        }
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
    let (binding, call, context, body, protocols, _) =
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
    let (binding, call, context, body, _, dav) =
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
            dav,
        },
    })
}

fn call_for(method: &str) -> io::Result<Call> {
    Ok(match method {
        crate::hosted_conversation::METHOD => Call::Exchange(Method::HostedConversation),
        "GET" => Call::Exchange(Method::Get),
        "HEAD" => Call::Exchange(Method::Head),
        "POST" => Call::Exchange(Method::Post),
        "PUT" => Call::Exchange(Method::Put),
        "PATCH" => Call::Exchange(Method::Patch),
        "DELETE" => Call::Exchange(Method::Delete),
        "PROPFIND" => Call::Exchange(Method::Propfind),
        "PROPPATCH" => Call::Exchange(Method::Proppatch),
        "MKCOL" => Call::Exchange(Method::Mkcol),
        "COPY" => Call::Exchange(Method::Copy),
        "MOVE" => Call::Exchange(Method::Move),
        "LOCK" => Call::Exchange(Method::Lock),
        "UNLOCK" => Call::Exchange(Method::Unlock),
        "REPORT" => Call::Exchange(Method::Report),
        "OPTIONS" => Call::Exchange(Method::Options),
        STREAMED_OPEN_METHOD => Call::Open,
        _ => return Err(invalid("Mini method unavailable to WebSession")),
    })
}

/// The WebSession projection of everything the entrance request alone
/// determines. It is a pure function of the request, so running it before
/// any Mini authoring refuses an unprojectable request while no Store record,
/// operation number or generation-wide marker exists. The committed record
/// is projected again by `project` from the same bytes afterwards.
pub(crate) fn preflight_web_input(
    http: &HttpProjection<'_>,
    display_name: &str,
    preferred_handle: &str,
    base_path: &str,
    upgrade: bool,
) -> io::Result<()> {
    let call = call_for(http.method)?;
    if matches!(call, Call::Open) != upgrade {
        return Err(invalid("entrance upgrade differs from WebSession call"));
    }
    project_http(&call, http, display_name, preferred_handle, base_path).map(|_| ())
}

struct HttpParts {
    context: RequestContext,
    body: Option<Body>,
    protocols: Option<Vec<String>>,
    dav: DavArgs,
    kind: SessionKind,
    base_path: String,
    user_agent: Option<String>,
}

#[allow(clippy::type_complexity)]
fn project(
    matched: &MatchedInspection,
    http: &HttpProjection<'_>,
    display_name: &str,
    preferred_handle: &str,
    base_path: &str,
) -> io::Result<(SessionBinding, Call, RequestContext, Option<Body>, Vec<String>, DavArgs)> {
    let call = call_for(matched.method.as_str())?;
    let HttpParts {
        context,
        body,
        protocols,
        dav,
        kind,
        base_path,
        user_agent,
    } = project_http(&call, http, display_name, preferred_handle, base_path)?;
    let session_resource = matched.session_resource.parse::<u64>()
        .map_err(|_| invalid("Mini session resource exceeds physical host range"))?;
    let subject = matched.subject.parse::<u64>()
        .map_err(|_| invalid("Mini subject exceeds physical host range"))?;
    if matched.subject != subject.to_string()
        || matched.session_resource != session_resource.to_string() {
        return Err(invalid("Mini session identity coordinates must be canonical unsigned integers"));
    }
    // Sandstorm tabId correlates a source session across process restarts. It
    // is not a browser label or request header and carries no new authority.
    let mut tab_id = b"mini-session-v1\0".to_vec();
    for id in [matched.app, subject, session_resource] {
        tab_id.extend_from_slice(&id.to_be_bytes());
    }
    Ok((
        SessionBinding {
            app: matched.app,
            process_generation: matched.app_generation,
            session_resource,
            session_generation: matched.session_generation.clone(),
            subject,
            projection_fingerprint: matched.session_fingerprint,
            ticket_resource: None,
            kind,
            params: SessionParameters {
                identity_id: matched.principal,
                display_name: display_name.to_owned(),
                preferred_handle: preferred_handle.to_owned(),
                permissions: matched.effective_bits.clone(),
                tab_id,
                base_path,
                user_agent: user_agent.unwrap_or_else(|| "Mini SPK Host".to_owned()),
                acceptable_languages: Vec::new(),
            },
        },
        call,
        context,
        body,
        protocols.unwrap_or_default(),
        dav,
    ))
}

fn project_http(
    call: &Call,
    http: &HttpProjection<'_>,
    display_name: &str,
    preferred_handle: &str,
    base_path: &str,
) -> io::Result<HttpParts> {
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
    let mut content_encoding = None;
    let mut user_agent = None;
    let mut dav = DavArgs::default();
    let dav_call = matches!(call, Call::Exchange(m) if crate::host_operations::dav_method(dav_name(*m)));
    let mut dav_seen = std::collections::HashSet::new();
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
            "content-encoding" => {
                if value.len() > 128 || !value.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
                    return Err(invalid("content-encoding is not one coding token"));
                }
                if content_encoding.replace(value.as_str()).is_some() {
                    return Err(invalid("duplicate content-encoding"));
                }
            }
            dav_header if crate::host_operations::dav_header_name(dav_header) => {
                if !dav_call || !matches!(call, Call::Exchange(m) if crate::host_operations::dav_header_allowed(dav_name(*m), dav_header, value)) {
                    return Err(invalid("DAV parameter header on a non-DAV call"));
                }
                if !dav_seen.insert(dav_header) {
                    return Err(invalid("duplicate DAV parameter header"));
                }
                dav_parameter(&mut dav, dav_header, value, http.route, base_path)?;
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
            "referer" if !crate::host_operations::referer_value_ok(value) => {
                return Err(invalid("signed referer is not a same-origin path (refererValueOk)"));
            }
            // The rest of Lean's ordinaryHeaderOk (generated): carried as additional headers. The
            // names with their own projection are matched above this arm.
            other if crate::host_operations::ordinary_header_ok(other, value) => {
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
    let body = match call {
        Call::Exchange(Method::Post | Method::Put | Method::Patch | Method::Proppatch | Method::HostedConversation) => Some(Body {
            mime_type: content_type.unwrap_or("").to_owned(),
            encoding: content_encoding.unwrap_or("").to_owned(),
            bytes: http.body.to_vec(),
        }),
        // A DAV call's content is optional: present exactly when the request carried a body.
        Call::Exchange(Method::Propfind | Method::Lock | Method::Mkcol | Method::Report)
            if !http.body.is_empty() =>
        {
            Some(Body {
                mime_type: content_type.unwrap_or("").to_owned(),
                encoding: content_encoding.unwrap_or("").to_owned(),
                bytes: http.body.to_vec(),
            })
        }
        Call::Exchange(Method::Propfind | Method::Lock | Method::Mkcol | Method::Report) => None,
        _ => {
            if content_type.is_some() || content_encoding.is_some() || !http.body.is_empty() {
                return Err(invalid("body/header on bodyless WebSession method"));
            }
            None
        }
    };
    match call {
        Call::Exchange(Method::Copy | Method::Move) if dav.destination.is_none() => {
            return Err(invalid("COPY/MOVE without a destination"))
        }
        Call::Exchange(Method::Unlock) if dav.lock_token.is_none() => {
            return Err(invalid("UNLOCK without a lock token"))
        }
        _ => {}
    }
    let (kind, base_path) = match http.route {
        Route::Browser => {
            let host = base_path
                .strip_prefix("https://")
                .ok_or_else(|| invalid("browser session base path is not an https origin"))?;
            // This is the same origin that the custodian already validated.
            // Keep its host[:port] grammar rather than a divergent DNS-only copy.
            if !crate::http_entrance::valid_expected_host(host) {
                return Err(invalid("browser session base path is not an https origin"));
            }
            (SessionKind::Web, base_path.to_owned())
        }
        Route::Api { .. } => (SessionKind::Api, String::new()),
    };
    Ok(HttpParts {
        context,
        body,
        protocols,
        dav,
        kind,
        base_path,
        user_agent: user_agent.map(str::to_owned),
    })
}

/// The method token Lean's `davMethod` names for a WebSession DAV call.
fn dav_name(method: Method) -> &'static str {
    match method {
        Method::Propfind => "PROPFIND",
        Method::Proppatch => "PROPPATCH",
        Method::Mkcol => "MKCOL",
        Method::Copy => "COPY",
        Method::Move => "MOVE",
        Method::Lock => "LOCK",
        Method::Unlock => "UNLOCK",
        Method::Report => "REPORT",
        Method::Options => "OPTIONS",
        _ => "",
    }
}

/// One signed DAV parameter header into its typed WebSession parameter, as Sandstorm's own
/// front end maps them: `depth` 0/1/infinity, `overwrite: F` is `noOverwrite`, `lock-token`
/// verbatim, and `destination` (an absolute URL on this grain's origin, or an absolute path)
/// into the relative Sandstorm path.
fn dav_parameter(
    dav: &mut DavArgs,
    name: &str,
    value: &str,
    route: Route<'_>,
    base_path: &str,
) -> io::Result<()> {
    match name {
        "depth" => {
            dav.depth = Some(match value.to_ascii_lowercase().as_str() {
                "0" => Depth::Zero,
                "1" => Depth::One,
                "infinity" => Depth::Infinity,
                _ => return Err(invalid("DAV depth is not 0, 1 or infinity")),
            })
        }
        "overwrite" => {
            dav.no_overwrite = match value {
                "F" | "f" => true,
                "T" | "t" => false,
                _ => return Err(invalid("DAV overwrite is not T or F")),
            }
        }
        "lock-token" => dav.lock_token = Some(value.to_owned()),
        "destination" => {
            // Browser Destination has HTTP origin semantics; API Destination is an
            // exact relative path under the already verified signed package prefix.
            let routed;
            let path = match route {
                Route::Api { signed_path } => {
                    routed = minidregg_signed_api_path::route(signed_path, value)
                        .map_err(invalid)?;
                    routed.as_str()
                }
                Route::Browser => {
                    if let Some(rest) = value.strip_prefix("https://") {
                        let (authority, path) = rest.split_once('/').unwrap_or((rest, ""));
                        if format!("https://{authority}") != base_path {
                            return Err(invalid("DAV destination is on another origin"));
                        }
                        path
                    } else {
                        value.strip_prefix('/').ok_or_else(|| invalid("DAV browser destination is not absolute"))?
                    }
                }
            };
            if path.len() > 8192 || path.contains(['#', '\r', '\n', '\0']) {
                return Err(invalid("DAV destination outside protocol bound"));
            }
            dav.destination = Some(path.to_owned());
        }
        _ => return Err(invalid("unknown DAV parameter header")),
    }
    Ok(())
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
    fn source_session_tab_is_stable_across_restart_and_separates_sessions() {
        let mut source=matched();
        let http=HttpProjection {method:"POST",path_and_query:"repo.git/git-receive-pack",
            ordered_headers:&[],body:b"",route:Route::Api {signed_path:"/repo.git/"}};
        let project_tab=|m:&MatchedInspection| physical_web_input(m,&http,"label","handle","/")
            .map(|p|p.binding.params.tab_id);
        let original=project_tab(&source).unwrap();
        assert_eq!(original,[b"mini-session-v1\0".as_slice(),&6100_u64.to_be_bytes(),&9_u64.to_be_bytes(),&6209_u64.to_be_bytes()].concat());
        source.app_generation+=1;source.session_fingerprint=[7;32];
        assert_eq!(project_tab(&source).unwrap(),original);
        source.session_resource="6210".into();assert_ne!(project_tab(&source).unwrap(),original);
        source.app=0;source.subject="0".into();source.session_resource="0".into();
        assert_eq!(project_tab(&source).unwrap(),[b"mini-session-v1\0".as_slice(), &[0_u8;24]].concat());
        for bad in ["","01","+9","18446744073709551616"] {
            source.session_resource=bad.into();assert!(project_tab(&source).is_err());
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
    fn dav_api_destination_is_exactly_under_signed_prefix() {
        let mut args = DavArgs::default();
        dav_parameter(&mut args, "destination", "notes/new.txt",
            Route::Api { signed_path: "/dav/" }, "").unwrap();
        assert_eq!(args.destination.as_deref(), Some("dav/notes/new.txt"));
        for destination in ["/elsewhere", "https://elsewhere/a", "../escape", "a/%2e%2e/b"] {
            assert!(dav_parameter(&mut DavArgs::default(), "destination", destination,
                Route::Api { signed_path: "/dav/" }, "").is_err());
        }
        assert!(!crate::host_operations::dav_header_allowed("MOVE", "depth", "1"));
        assert!(!crate::host_operations::dav_header_allowed("PROPFIND", "overwrite", "T"));
    }

    #[test]
    fn dav_headers_project_into_typed_parameters_and_refuse_off_dav() {
        let base = "https://friend.example.test";
        let project = |method: &'static str, path: &'static str, headers: &[(String, String)], body: &'static [u8]| {
            let mut source = matched();
            source.method = method.into();
            source.app_path_and_query = path.into();
            let http = HttpProjection { method, path_and_query: path, ordered_headers: headers, body, route: Route::Browser };
            physical_web_input(&source, &http, "Friend", "friend", base)
        };
        let h = |pairs: &[(&str, &str)]| pairs.iter().map(|(n, v)| (n.to_string(), v.to_string())).collect::<Vec<_>>();
        let propfind = project("PROPFIND", "dav/notes", &h(&[("depth", "0"), ("content-type", "application/xml")]), b"<propfind/>").unwrap();
        assert_eq!(propfind.request.method, Method::Propfind);
        assert_eq!(propfind.request.dav.depth, Some(Depth::Zero));
        assert_eq!(propfind.request.body.unwrap().bytes, b"<propfind/>");
        let mv = project("MOVE", "dav/a", &h(&[("destination", "https://friend.example.test/dav/b%20c"), ("overwrite", "F")]), b"").unwrap();
        assert_eq!(mv.request.dav.destination.as_deref(), Some("dav/b%20c"));
        assert!(mv.request.dav.no_overwrite);
        assert!(mv.request.body.is_none());
        let by_path = project("COPY", "dav/a", &h(&[("destination", "/dav/c"), ("depth", "0")]), b"").unwrap();
        assert_eq!(by_path.request.dav.destination.as_deref(), Some("dav/c"));
        assert_eq!(by_path.request.dav.depth, Some(Depth::Zero));
        let unlock = project("UNLOCK", "dav/a", &h(&[("lock-token", "<opaquelocktoken:1>")]), b"").unwrap();
        assert_eq!(unlock.request.dav.lock_token.as_deref(), Some("<opaquelocktoken:1>"));
        let mkcol = project("MKCOL", "dav/new", &[], b"").unwrap();
        assert!(mkcol.request.body.is_none());
        let encoded = project("POST", "repo.git/git-upload-pack", &h(&[("content-type", "application/x-git-upload-pack-request"), ("content-encoding", "gzip")]), b"\x1f\x8b").unwrap();
        assert_eq!(encoded.request.body.unwrap().encoding, "gzip");
        // Refusals by name, before any call.
        assert!(project("MOVE", "dav/a", &h(&[("destination", "https://elsewhere.example/dav/b")]), b"").is_err());
        assert!(project("MOVE", "dav/a", &[], b"").is_err());
        assert!(project("UNLOCK", "dav/a", &[], b"").is_err());
        assert!(project("GET", "dav/a", &h(&[("depth", "1")]), b"").is_err());
        assert!(project("PROPFIND", "dav/a", &h(&[("depth", "2")]), b"").is_err());
        assert!(project("COPY", "dav/a", &h(&[("destination", "/dav/b"), ("overwrite", "maybe")]), b"").is_err());
        assert!(project("PROPFIND", "dav/a", &h(&[("depth", "1"), ("depth", "0")]), b"").is_err());
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

    #[test]
    fn browser_origin_uses_custodian_host_and_port_grammar() {
        let http = HttpProjection {
            method: "GET", path_and_query: "sheet", ordered_headers: &[],
            body: b"", route: Route::Browser,
        };
        for origin in ["https://localhost:18443", "https://grain.example.test", "https://grain.example.test:443"] {
            let input = physical_web_input(&matched(), &http, "Friend", "friend", origin).unwrap();
            assert_eq!(input.binding.params.base_path, origin);
        }
        for origin in ["https://localhost:0", "https://localhost:018443", "https://localhost:65536",
            "https://localhost:18443/path", "https://user@localhost:18443", "https://LOCALHOST:18443",
            "https://localhost:18443#fragment", "https://localhost:18443?query", "https://bad..host"] {
            assert!(physical_web_input(&matched(), &http, "Friend", "friend", origin).is_err(), "{origin}");
        }
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
    /// Chromium's navigation Accept carries `v=b3` before its weight. The
    /// range keeps its parameter (the bridge rebuilds exactly the signed
    /// range) and only the weight becomes the WebSession number.
    #[test]
    fn chromium_navigation_accept_keeps_media_parameters() {
        let chromium = "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7";
        let parsed = quality_list(chromium).unwrap();
        assert_eq!(parsed.len(), 8);
        assert_eq!(parsed[2], ("application/xml".into(), 900));
        assert_eq!(parsed[6], ("*/*".into(), 800));
        assert_eq!(parsed[7], ("application/signed-exchange;v=b3".into(), 700));
        assert_eq!(quality_list("text/plain;Q=0.5").unwrap(), [("text/plain".into(), 500)]);
        assert_eq!(
            quality_list("text/html;level=1").unwrap(),
            [("text/html;level=1".into(), 1000)]
        );
        for refused in [
            "text/html;q=0.5;level=1",
            "text/html;q=0.5;q=0.4",
            "text/html;q=2",
            "text/html;q=0.1234",
            "text/html;level",
            "text/html;=1",
            ";q=0.5",
            "text/html,,text/plain",
        ] {
            assert!(quality_list(refused).is_err(), "{refused}");
        }
        let headers = vec![("accept".to_owned(), chromium.to_owned())];
        let http = HttpProjection {
            method: "GET",
            path_and_query: "",
            ordered_headers: &headers,
            body: b"",
            route: Route::Browser,
        };
        let mut source = matched();
        source.method = "GET".into();
        let projected =
            physical_web_input(&source, &http, "Friend", "friend", "https://friend.example.test")
                .unwrap();
        assert_eq!(projected.request.context.accept.len(), 8);
    }

    /// The pre-commit preflight is the same projection as the committed one:
    /// whatever it admits projects after commit, and whatever it refuses is
    /// refused before any Mini authoring or generation-wide marker exists.
    #[test]
    fn preflight_refuses_unprojectable_request_before_any_mini_call() {
        let origin = "https://friend.example.test";
        let good = vec![
            ("accept".to_owned(), "text/html;q=0.9".to_owned()),
            ("user-agent".to_owned(), "Browser/1".to_owned()),
        ];
        let http = HttpProjection {
            method: "GET",
            path_and_query: "sheet",
            ordered_headers: &good,
            body: b"",
            route: Route::Browser,
        };
        preflight_web_input(&http, "Friend", "friend", origin, false).unwrap();
        let mut source = matched();
        source.method = "GET".into();
        physical_web_input(&source, &http, "Friend", "friend", origin).unwrap();
        assert!(preflight_web_input(&http, "Friend", "friend", origin, true).is_err());
        let unmapped = vec![("x-mini-export-capture".to_owned(), "a".repeat(32))];
        let refused = HttpProjection {
            ordered_headers: &unmapped,
            ..http
        };
        assert!(preflight_web_input(&refused, "Friend", "friend", origin, false).is_err());
        let bad_accept = vec![("accept".to_owned(), "text/html;q=0.5;level=1".to_owned())];
        let refused = HttpProjection {
            ordered_headers: &bad_accept,
            ..http
        };
        assert!(preflight_web_input(&refused, "Friend", "friend", origin, false).is_err());
        let refused = HttpProjection {
            body: b"x",
            ..http
        };
        assert!(preflight_web_input(&refused, "Friend", "friend", origin, false).is_err());
        assert!(preflight_web_input(&http, "Friend", "friend", "/", false).is_err());
        let protocols = vec![("sec-websocket-protocol".to_owned(), "chat".to_owned())];
        let open = HttpProjection {
            method: STREAMED_OPEN_METHOD,
            ordered_headers: &protocols,
            ..http
        };
        preflight_web_input(&open, "Friend", "friend", origin, true).unwrap();
        assert!(preflight_web_input(&open, "Friend", "friend", origin, false).is_err());
    }
}

/// Lower the fixed HTTP half of an admitted compound hosted descriptor through
/// the same ordinary header/body projection as every other WebSession request.
pub(crate) fn hosted_http(value: &serde_json::Value, binding: &SessionBinding,
    api_prefix: Option<&str>) -> io::Result<WebRequest> {
    let text = |key: &str| value[key].as_str().ok_or_else(|| invalid("hosted HTTP text field absent"));
    let method=text("method")?;
    let call=call_for(method)?;
    let Call::Exchange(method) = call else { return Err(invalid("nested hosted HTTP must be an exchange")); };
    if method == Method::HostedConversation { return Err(invalid("nested conversation refused")); }
    let headers=value["headers"].as_array().ok_or_else(||invalid("hosted HTTP headers absent"))?.iter().map(|header| {
        Ok((header["name"].as_str().ok_or_else(||invalid("hosted header name absent"))?.to_owned(),
            header["value"].as_str().ok_or_else(||invalid("hosted header value absent"))?.to_owned()))
    }).collect::<io::Result<Vec<_>>>()?;
    let body=crate::canonical::unhex(text("bodyHex")?).ok_or_else(||invalid("hosted HTTP body hex refused"))?;
    let query=text("query")?;
    let path=if query.is_empty() { text("path")?.to_owned() } else { format!("{}?{query}",text("path")?) };
    let route=match binding.kind {
        SessionKind::Web => Route::Browser,
        SessionKind::Api => Route::Api { signed_path:api_prefix.ok_or_else(||invalid("hosted API prefix custody absent"))? },
    };
    let http=HttpProjection { method:text("method")?,path_and_query:&path,ordered_headers:&headers,body:&body,route };
    let (app_path,query)=crate::dispatch_inspection::app_route_path(&http)?;
    let parts=project_http(&call,&http,&binding.params.display_name,&binding.params.preferred_handle,&binding.params.base_path)?;
    Ok(WebRequest { method,path_and_query:if query.is_empty() {app_path} else {format!("{app_path}?{query}")},context:parts.context,body:parts.body,dav:parts.dav })
}
