//! Bounded HTTP/1.1 projection of a completed WebSession response.
//!
//! This is a physical codec, not dispatch admission. The private entrance must
//! obtain a fresh Mini committed permit before calling the RPC driver or this
//! serializer. An uncertain RPC result is never converted into a retry.
#![allow(dead_code)] // Staged behind Mini's committed dispatch permit route.

use minidregg_spk_rpc::{CookieExpiry, ETag, WebResponse, WebResult};
use std::io;

const MAX_BODY: usize = 8 * 1024 * 1024;
const MAX_HEADERS: usize = 128;
const MAX_FIELD: usize = 8192;
const MAX_HEAD: usize = 64 * 1024;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn field(value: &str) -> io::Result<&str> {
    if value.len() > MAX_FIELD
        || value.bytes().any(|byte| {
            byte == 0
                || byte == b'\r'
                || byte == b'\n'
                || (byte < 0x20 && byte != b'\t')
                || byte == 0x7f
        })
    {
        Err(invalid("WebSession response header field refused"))
    } else {
        Ok(value)
    }
}

fn token(value: &str) -> io::Result<&str> {
    if value.is_empty()
        || value.len() > 128
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"!#$%&'*+-.^_`|~".contains(&byte))
    {
        Err(invalid("WebSession response token refused"))
    } else {
        Ok(value)
    }
}

fn etag(value: &ETag) -> io::Result<String> {
    if value.value.len() > MAX_FIELD
        || value
            .value
            .bytes()
            .any(|byte| byte < 0x20 || byte == 0x7f || byte == b'"')
    {
        return Err(invalid("WebSession response ETag refused"));
    }
    Ok(format!(
        "{}\"{}\"",
        if value.weak { "W/" } else { "" },
        value.value
    ))
}

fn add(headers: &mut String, name: &str, value: &str) -> io::Result<()> {
    token(name)?;
    field(value)?;
    headers.push_str(name);
    headers.push_str(": ");
    headers.push_str(value);
    headers.push_str("\r\n");
    if headers.len() > MAX_HEAD - 256 {
        return Err(invalid("WebSession response headers exceed proxy bound"));
    }
    Ok(())
}

fn content_disposition(value: &str) -> io::Result<String> {
    if value.len() > 1024 {
        return Err(invalid("WebSession download name refused: longer than 1024 bytes"));
    }
    if value.chars().any(char::is_control) {
        return Err(invalid("WebSession download name refused: control character"));
    }
    let mut encoded = String::new();
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric() || b"!#$&+-.^_`|~".contains(&byte) {
            encoded.push(byte as char);
        } else {
            encoded.push_str(&format!("%{byte:02X}"));
        }
    }
    Ok(format!(
        "attachment; filename=\"download\"; filename*=UTF-8''{encoded}"
    ))
}

fn relative_location(value: &str) -> io::Result<&str> {
    field(value)?;
    if value.is_empty()
        || value != value.trim()
        || value.starts_with("//")
        || value.contains('\\')
        || value
            .split(['/', '?', '#'])
            .next()
            .is_some_and(|first| first.contains(':'))
    {
        Err(invalid("WebSession redirect outside relative app path"))
    } else {
        Ok(value)
    }
}

fn cookie_value(value: &str) -> io::Result<&str> {
    if value.len() > MAX_FIELD
        || !value.bytes().all(|byte| {
            byte == 0x21
                || (0x23..=0x2b).contains(&byte)
                || (0x2d..=0x3a).contains(&byte)
                || (0x3c..=0x5b).contains(&byte)
                || (0x5d..=0x7e).contains(&byte)
        })
    {
        Err(invalid("WebSession cookie value refused"))
    } else {
        Ok(value)
    }
}

fn cookie_path(value: &str) -> io::Result<&str> {
    if value.is_empty() {
        return Ok("/");
    }
    if !value.starts_with('/')
        || value.len() > MAX_FIELD
        || value
            .bytes()
            .any(|byte| byte < 0x20 || byte == 0x7f || byte == b';')
    {
        Err(invalid("WebSession cookie path refused"))
    } else {
        Ok(value)
    }
}

fn cookie_expires(epoch_seconds: i64) -> io::Result<String> {
    let seconds: libc::time_t = epoch_seconds;
    let mut utc = unsafe { std::mem::zeroed::<libc::tm>() };
    if unsafe { libc::gmtime_r(&seconds, &mut utc) }.is_null()
        || !(0..7).contains(&utc.tm_wday)
        || !(0..12).contains(&utc.tm_mon)
        || !(0..24).contains(&utc.tm_hour)
        || !(0..60).contains(&utc.tm_min)
        || !(0..61).contains(&utc.tm_sec)
        || !(1..=31).contains(&utc.tm_mday)
        || !(0..=8099).contains(&utc.tm_year)
    {
        return Err(invalid("WebSession cookie expiry outside HTTP date range"));
    }
    const DAYS: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
    const MONTHS: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    Ok(format!(
        "{}, {:02} {} {:04} {:02}:{:02}:{:02} GMT",
        DAYS[utc.tm_wday as usize],
        utc.tm_mday,
        MONTHS[utc.tm_mon as usize],
        utc.tm_year + 1900,
        utc.tm_hour,
        utc.tm_min,
        utc.tm_sec
    ))
}

/// Serializes one already completed app response; the caller owns authority,
/// deadline, exact request matching, and the no-retry decision.
pub(crate) fn serialize(response: &WebResponse, head_request: bool) -> io::Result<Vec<u8>> {
    if response.headers.len() + response.set_cookies.len() > MAX_HEADERS {
        return Err(invalid("too many WebSession response headers"));
    }
    let mut headers = String::new();
    let (status, reason, body): (u16, &str, &[u8]) = match &response.result {
        WebResult::Content {
            status,
            mime_type,
            encoding,
            language,
            etag: tag,
            body,
            download_name,
        } => {
            if !matches!(*status, 200 | 201 | 202 | 204 | 206 | 207 | 304) {
                return Err(invalid("unsupported WebSession content status"));
            }
            if matches!(*status, 204 | 304) && !body.is_empty() {
                return Err(invalid("body on bodyless WebSession status"));
            }
            if !matches!(*status, 204 | 304) {
                add(&mut headers, "Content-Type", field(mime_type)?)?;
                if !encoding.is_empty() {
                    add(&mut headers, "Content-Encoding", field(encoding)?)?;
                }
                if !language.is_empty() {
                    add(&mut headers, "Content-Language", field(language)?)?;
                }
            }
            if let Some(tag) = tag {
                add(&mut headers, "ETag", &etag(tag)?)?;
            }
            if !matches!(*status, 204 | 304) {
                // An empty download name is what sandstorm-http-bridge sends
                // for a bare `Content-Disposition: attachment`; Sandstorm's
                // shell treats it as no disposition (a falsy name), and so
                // does this proxy. Measured: Davros's WebDAV GET of a file
                // answered 503 on the refusal (SPK-APPS 2026-10-01).
                if let Some(name) = download_name.as_deref().filter(|name| !name.is_empty()) {
                    add(
                        &mut headers,
                        "Content-Disposition",
                        &content_disposition(name)?,
                    )?;
                }
            }
            let reason = match *status {
                200 => "OK",
                201 => "Created",
                202 => "Accepted",
                204 => "No Content",
                206 => "Partial Content",
                207 => "Multi-Status",
                304 => "Not Modified",
                _ => unreachable!(),
            };
            (*status, reason, body.as_slice())
        }
        WebResult::NoContent {
            reset_form,
            etag: tag,
        } => {
            if let Some(tag) = tag {
                add(&mut headers, "ETag", &etag(tag)?)?;
            }
            (if *reset_form { 205 } else { 204 }, "No Content", &[])
        }
        WebResult::PreconditionFailed { matching_etag } => {
            if let Some(tag) = matching_etag {
                add(&mut headers, "ETag", &etag(tag)?)?;
            }
            (412, "Precondition Failed", &[])
        }
        WebResult::Redirect {
            permanent,
            switch_to_get,
            location,
        } => {
            add(&mut headers, "Location", relative_location(location)?)?;
            let status = match (*permanent, *switch_to_get) {
                (false, false) => 307,
                (true, false) => 308,
                (false, true) => 303,
                (true, true) => 301,
            };
            (status, "Redirect", &[])
        }
        WebResult::ClientError {
            status,
            html,
            non_html,
        } => {
            if !(400..=499).contains(status) {
                return Err(invalid("WebSession client error status refused"));
            }
            if let Some((mime, data)) = non_html {
                add(&mut headers, "Content-Type", field(mime)?)?;
                (*status, "Client Error", data.as_slice())
            } else {
                add(&mut headers, "Content-Type", "text/html; charset=utf-8")?;
                (*status, "Client Error", html.as_bytes())
            }
        }
        WebResult::ServerError { html, non_html } => {
            if let Some((mime, data)) = non_html {
                add(&mut headers, "Content-Type", field(mime)?)?;
                (500, "Internal Server Error", data.as_slice())
            } else {
                add(&mut headers, "Content-Type", "text/html; charset=utf-8")?;
                (500, "Internal Server Error", html.as_bytes())
            }
        }
    };
    if body.len() > MAX_BODY {
        return Err(invalid("WebSession response body exceeds bound"));
    }
    for extra in &response.headers {
        // Security context and HTTP framing belong to the host, never the app.
        if extra.name != "x-oc-mtime" {
            return Err(invalid("WebSession response header refused"));
        }
        add(&mut headers, &extra.name, &extra.value)?;
    }
    for cookie in &response.set_cookies {
        token(&cookie.name)?;
        if cookie.name.eq_ignore_ascii_case("__Host-mini_spk_session") {
            return Err(invalid("app cookie reserved for host transport"));
        }
        let value = cookie_value(&cookie.value)?;
        let path = cookie_path(&cookie.path)?;
        if cookie.name.starts_with("__Host-") && path != "/" {
            return Err(invalid("app __Host- cookie requires root path"));
        }
        let mut rendered = format!(
            "{}={value}; Path={path}; Secure; SameSite=Strict",
            cookie.name
        );
        if cookie.http_only {
            rendered.push_str("; HttpOnly");
        }
        match cookie.expiry {
            CookieExpiry::None => {}
            CookieExpiry::Relative(seconds) => rendered.push_str(&format!("; Max-Age={seconds}")),
            CookieExpiry::Absolute(seconds) => {
                rendered.push_str(&format!("; Expires={}", cookie_expires(seconds)?))
            }
        }
        add(&mut headers, "Set-Cookie", &rendered)?;
    }
    let length = if matches!(status, 204 | 304) {
        String::new()
    } else {
        format!("Content-Length: {}\r\n", body.len())
    };
    let mut out = format!("HTTP/1.1 {status} {reason}\r\n{headers}{length}Cache-Control: no-store\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\n").into_bytes();
    if out.len() > MAX_HEAD {
        return Err(invalid("WebSession HTTP header exceeds proxy bound"));
    }
    if !head_request {
        out.extend_from_slice(body);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use minidregg_spk_rpc::{Header, WebResult};

    #[test]
    fn git_smart_http_preserves_binary_body_and_head_suppresses_it() {
        let reply = WebResponse {
            result: WebResult::Content {
                status: 200,
                mime_type: "application/x-git-upload-pack-result".into(),
                encoding: "".into(),
                language: "".into(),
                etag: None,
                body: b"\0git\xff".to_vec(),
                download_name: None,
            },
            headers: vec![],
            set_cookies: vec![],
        };
        let get = serialize(&reply, false).unwrap();
        assert!(get.ends_with(b"\0git\xff"));
        assert!(String::from_utf8_lossy(&get).contains("Content-Length: 5\r\n"));
        let head = serialize(&reply, true).unwrap();
        assert!(!head.ends_with(b"\0git\xff"));
        assert!(String::from_utf8_lossy(&head).contains("Content-Length: 5\r\n"));
    }

    #[test]
    fn app_cannot_replace_transport_cookie_or_forge_security_header() {
        let mut reply = WebResponse {
            result: WebResult::NoContent {
                reset_form: false,
                etag: None,
            },
            headers: vec![],
            set_cookies: vec![],
        };
        reply.headers.push(Header {
            name: "x-sandstorm-app-permissions".into(),
            value: "write".into(),
        });
        assert!(serialize(&reply, false).is_err());
        reply.headers.clear();
        reply.set_cookies.push(minidregg_spk_rpc::SetCookie {
            name: "__Host-mini_spk_session".into(),
            value: "replacement".into(),
            path: "/".into(),
            http_only: true,
            expiry: CookieExpiry::None,
        });
        assert!(serialize(&reply, false).is_err());
    }

    #[test]
    fn redirect_refuses_cross_origin_and_header_injection() {
        let mut reply = WebResponse {
            result: WebResult::Redirect {
                permanent: false,
                switch_to_get: true,
                location: "repo.git/".into(),
            },
            headers: vec![],
            set_cookies: vec![],
        };
        assert!(serialize(&reply, false)
            .unwrap()
            .starts_with(b"HTTP/1.1 303"));
        reply.result = WebResult::Redirect {
            permanent: false,
            switch_to_get: true,
            location: "https://elsewhere".into(),
        };
        assert!(serialize(&reply, false).is_err());
        reply.result = WebResult::Redirect {
            permanent: false,
            switch_to_get: true,
            location: "x\r\nSet-Cookie: stolen=1".into(),
        };
        assert!(serialize(&reply, false).is_err());
        reply.result = WebResult::Redirect {
            permanent: false,
            switch_to_get: true,
            location: "\\\\evil.example/".into(),
        };
        assert!(serialize(&reply, false).is_err());
    }

    #[test]
    fn no_content_has_no_length_and_ordinary_download_name_is_encoded() {
        let mut reply = WebResponse {
            result: WebResult::NoContent {
                reset_form: false,
                etag: None,
            },
            headers: vec![],
            set_cookies: vec![],
        };
        let empty = String::from_utf8(serialize(&reply, false).unwrap()).unwrap();
        assert!(empty.starts_with("HTTP/1.1 204"));
        assert!(!empty.contains("Content-Length:"));
        reply.result = WebResult::Content {
            status: 200,
            mime_type: "application/octet-stream".into(),
            encoding: "".into(),
            language: "".into(),
            etag: None,
            body: vec![],
            download_name: Some("report 你好.txt".into()),
        };
        let download = String::from_utf8(serialize(&reply, false).unwrap()).unwrap();
        assert!(download.contains("filename*=UTF-8''report%20%E4%BD%A0%E5%A5%BD.txt"));
        // A bare `attachment` arrives as an empty name: no disposition, as
        // Sandstorm's shell does; a control character is still refused.
        if let WebResult::Content { download_name, .. } = &mut reply.result {
            *download_name = Some(String::new());
        }
        let bare = String::from_utf8(serialize(&reply, false).unwrap()).unwrap();
        assert!(bare.starts_with("HTTP/1.1 200") && !bare.contains("Content-Disposition"));
        if let WebResult::Content { download_name, .. } = &mut reply.result {
            *download_name = Some("a\r\nSet-Cookie: x=y".into());
        }
        assert!(serialize(&reply, false).is_err());
    }

    #[test]
    fn app_cookie_absolute_expiry_path_and_octet_rules() {
        let mut reply = WebResponse {
            result: WebResult::NoContent {
                reset_form: false,
                etag: None,
            },
            headers: vec![],
            set_cookies: vec![minidregg_spk_rpc::SetCookie {
                name: "app_pref".into(),
                value: "abc_123".into(),
                path: "/repo".into(),
                http_only: true,
                expiry: CookieExpiry::Absolute(1_700_000_000),
            }],
        };
        let encoded = String::from_utf8(serialize(&reply, false).unwrap()).unwrap();
        assert!(encoded.contains(
            "Path=/repo; Secure; SameSite=Strict; HttpOnly; Expires=Tue, 14 Nov 2023 22:13:20 GMT"
        ));
        reply.set_cookies[0].value = "space in cookie".into();
        assert!(serialize(&reply, false).is_err());
        reply.set_cookies[0].value = "abc".into();
        reply.set_cookies[0].name = "__Host-mini_spk_session".into();
        assert!(serialize(&reply, false).is_err());
        reply.set_cookies[0].name = "__Host-app".into();
        assert!(serialize(&reply, false).is_err());
        reply.set_cookies[0].path = "/".into();
        assert!(serialize(&reply, false).is_ok());
    }

    #[test]
    fn aggregate_response_headers_fit_private_tls_proxy() {
        let reply = WebResponse {
            result: WebResult::NoContent {
                reset_form: false,
                etag: None,
            },
            headers: (0..16)
                .map(|_| Header {
                    name: "x-oc-mtime".into(),
                    value: "x".repeat(8192),
                })
                .collect(),
            set_cookies: vec![],
        };
        assert!(serialize(&reply, false).is_err());
    }

    #[test]
    fn not_modified_omits_body_and_length() {
        let mut reply = WebResponse {
            result: WebResult::Content {
                status: 304,
                mime_type: String::new(),
                encoding: String::new(),
                language: String::new(),
                etag: None,
                body: Vec::new(),
                download_name: None,
            },
            headers: vec![],
            set_cookies: vec![],
        };
        let wire = String::from_utf8(serialize(&reply, false).unwrap()).unwrap();
        assert!(wire.starts_with("HTTP/1.1 304 Not Modified"));
        assert!(!wire.contains("Content-Length:"));
        if let WebResult::Content { body, .. } = &mut reply.result {
            body.push(1);
        }
        assert!(serialize(&reply, false).is_err());
    }
}
