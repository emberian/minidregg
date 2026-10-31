//! Exact routing under an SPK's signature-verified legacy HTTP API prefix.
//! The caller must separately compare the prefix to Mini's admitted package
//! descriptor. This module neither supplies authority nor decodes URL escapes.

const MAX_PREFIX: usize = 256;
const MAX_RELATIVE_PATH: usize = 8192;

fn safe_segment(segment: &str) -> bool {
    !segment.is_empty()
        && segment != "."
        && segment != ".."
        && segment
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.' | b'~'))
}

/// Accept only a literal, canonical signed prefix: it starts with `/`, and every
/// segment after it is a safe segment, the last one optionally followed by `/`. `/` is
/// the root API profile; a missing prefix means that the SPK has no HTTP API.
///
/// Sandstorm's own bridge forms an API request line as `rootPath + path`, the signed
/// `apiPath` followed by the relative path, with nothing between them
/// (sandstorm-http-bridge.c++, `lines.add(kj::str(method, " ", rootPath, path, ...))`).
/// So a prefix such as `/pub` is legal there, and the request for `x` reaches the app as
/// `/pubx`. Admitting it here gives the same meaning. `route` still emits the literal
/// signed prefix followed by a canonical relative path, which has no leading slash, no dot
/// segment and no escape. The routed path therefore always begins with the bytes the
/// package signed and cannot leave them.
pub fn checked_prefix(prefix: &str) -> Result<(), &'static str> {
    if prefix.is_empty() || prefix.len() > MAX_PREFIX || !prefix.starts_with('/') {
        return Err("signed API prefix is not canonical");
    }
    let body = &prefix[1..];
    let body = body.strip_suffix('/').unwrap_or(body);
    if prefix != "/" && !body.split('/').all(safe_segment) {
        return Err("signed API prefix contains an unsafe segment");
    }
    Ok(())
}

/// Mini keeps the original descriptor codec for a package without an API or
/// for the first GitWeb profile. A different signed prefix uses descriptor v2.
pub fn descriptor_inspection_type(prefix: Option<&str>) -> Result<&'static str, &'static str> {
    match prefix {
        None | Some("/repo.git/") => Ok("application-spk-package-identity-v1"),
        Some(path) => {
            checked_prefix(path)?;
            Ok("application-spk-package-identity-v2")
        }
    }
}

pub fn launch_inspection_type(prefix: Option<&str>) -> Result<&'static str, &'static str> {
    match descriptor_inspection_type(prefix)? {
        "application-spk-package-identity-v1" => Ok("application-spk-launch-descriptor-v2"),
        _ => Ok("application-spk-launch-descriptor-v3"),
    }
}

/// The external API path is relative to the signed prefix. Return the exact
/// app-relative path; never decode, collapse, or repair caller bytes.
pub fn route(prefix: &str, relative: &str) -> Result<String, &'static str> {
    checked_prefix(prefix)?;
    if relative.len() > MAX_RELATIVE_PATH
        || relative.starts_with('/')
        || relative.ends_with('/') && !relative.is_empty()
        || !relative.is_empty() && !relative.split('/').all(safe_segment)
    {
        return Err("relative API path is not canonical");
    }
    let mut result = String::with_capacity(prefix.len() - 1 + relative.len());
    result.push_str(&prefix[1..]);
    result.push_str(relative);
    if result.len() > MAX_RELATIVE_PATH {
        return Err("routed API path exceeds native bound");
    }
    Ok(result)
}

/// The route of a hosted CONVERSATION request: `route`, except that the relative path may end in one
/// `/`. The path is the app's own URL for its websocket endpoint and is carried byte-exact: socket.io
/// (engine.io's `addTrailingSlash`) only upgrades `/socketio/...`, so `socketio/` and `socketio` are
/// different endpoints. Nothing else loosens: no leading slash, no empty segment, so `a//` is refused.
pub fn conversation_route(prefix: &str, relative: &str) -> Result<String, &'static str> {
    match relative.strip_suffix('/') {
        Some(base) if !base.is_empty() => {
            let mut routed = route(prefix, base)?;
            routed.push('/');
            if routed.len() > MAX_RELATIVE_PATH {
                return Err("routed API path exceeds native bound");
            }
            Ok(routed)
        }
        Some(_) => Err("relative API path is not canonical"),
        None => route(prefix, relative),
    }
}

/// A member's WebSession route carries no signed prefix: the model path is the exact
/// canonical relative browser path (no leading slash, no query or fragment, no repair or
/// decoding), the Host's `app_route_path` rule for a browser target. Bounded like `route`.
pub fn browser_route(relative: &str) -> Result<String, &'static str> {
    if relative.len() > MAX_RELATIVE_PATH
        || relative.starts_with('/')
        || relative.contains(['?', '#'])
    {
        return Err("relative browser path is not canonical");
    }
    Ok(relative.to_owned())
}

/// Check that an app-relative path is exactly under the same signed prefix.
pub fn is_under(prefix: &str, app_relative: &str) -> bool {
    checked_prefix(prefix).is_ok()
        && app_relative
            .strip_prefix(&prefix[1..])
            .is_some_and(|relative| route(prefix, relative).as_deref() == Ok(app_relative))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn git_and_root_profiles_preserve_exact_paths() {
        assert_eq!(
            route("/repo.git/", "info/refs"),
            Ok("repo.git/info/refs".into())
        );
        assert_eq!(route("/repo.git/", ""), Ok("repo.git/".into()));
        assert_eq!(route("/", "topic/json"), Ok("topic/json".into()));
        assert_eq!(route("/", ""), Ok("".into()));
        assert!(is_under("/repo.git/", "repo.git/info/refs"));
        assert!(is_under("/", "topic/json"));
        assert_eq!(
            descriptor_inspection_type(None),
            Ok("application-spk-package-identity-v1")
        );
        assert_eq!(
            descriptor_inspection_type(Some("/repo.git/")),
            Ok("application-spk-package-identity-v1")
        );
        assert_eq!(
            descriptor_inspection_type(Some("/")),
            Ok("application-spk-package-identity-v2")
        );
        assert_eq!(
            launch_inspection_type(Some("/repo.git/")),
            Ok("application-spk-launch-descriptor-v2")
        );
        assert_eq!(
            launch_inspection_type(Some("/")),
            Ok("application-spk-launch-descriptor-v3")
        );
    }

    #[test]
    fn refuse_ambiguous_prefix_and_path_without_normalizing() {
        for prefix in [
            "",
            "api/",
            "//",
            "/api//",
            "/./",
            "/../",
            "/api/%2e/",
            "/api\\/",
        ] {
            assert!(checked_prefix(prefix).is_err(), "{prefix}");
        }
        for path in [
            "/absolute",
            "//host",
            "a//b",
            ".",
            "..",
            "a/../b",
            "a/%2e%2e/b",
            "a%2fb",
            "a?b",
            "a#b",
            "a\\b",
            "a/",
            "a:b",
        ] {
            assert!(route("/", path).is_err(), "{path}");
        }
        assert!(!is_under("/repo.git/", "repo.git2/info"));
        assert!(!is_under("/repo.git/", "repo.git/../other"));
        assert!(route("/repo.git/", &"a".repeat(MAX_RELATIVE_PATH)).is_err());
    }
}

#[cfg(test)]
mod exact_prefix_tests {
    use super::*;

    #[test]
    fn near_miss_prefixes_are_not_under_the_signed_prefix() {
        // The slash terminator makes /api and /apix different prefixes.
        assert!(is_under("/api/", "api/v1"));
        assert!(!is_under("/api/", "apix/v1"));
        assert!(!is_under("/api/", "api"));
        assert!(!is_under("/api/", "API/v1"));
        assert!(!is_under("/api/", "other/api/v1"));
        assert!(!is_under("/api/", "api//v1"));
        assert!(!is_under("/api/", "api/v1/"));
        // A prefix without its terminating slash is Sandstorm's plain concatenation: the
        // relative path follows the signed bytes directly, and nothing escapes them.
        assert!(checked_prefix("/api").is_ok());
        assert_eq!(route("/api", "v1"), Ok("apiv1".into()));
        assert_eq!(route("/pub", ""), Ok("pub".into()));
        assert!(is_under("/pub", "pubx"));
        assert!(!is_under("/api", "api/v1"));
        assert!(route("/pub", "../secret").is_err());
        assert!(route("/pub", "/etc").is_err());
        assert!(!is_under("/pub", "pu"));
        for hostile in ["/pub/../x", "/pub//", "/./", "/a/./b", "/pub%2f", "/p\\", "pub", "/pub?x", "/pub#x"] {
            assert!(checked_prefix(hostile).is_err(), "{hostile}");
        }
        // Nested prefixes route exactly and do not leak into siblings.
        assert_eq!(route("/api/v2/", "x"), Ok("api/v2/x".into()));
        assert!(!is_under("/api/v2/", "api/v1/x"));
        assert!(!is_under("/api/v2/", "api/v22/x"));
    }

    #[test]
    fn percent_escapes_and_trailing_slashes_are_refused_not_decoded() {
        assert!(route("/api/", "a%2Fb").is_err());
        assert!(route("/api/", "%2e%2e").is_err());
        assert!(route("/api/", "a%00").is_err());
        assert!(route("/api/", "dir/").is_err());
        assert_eq!(route("/api/", ""), Ok("api/".into()));
        assert!(checked_prefix("/api%2f/").is_err());
        assert!(!is_under("/api/", "api/%2e%2e/secret"));
        assert!(!is_under("/api/", "api/a%2fb"));
    }

    #[test]
    fn a_conversation_path_may_end_in_one_slash_and_nothing_else_loosens() {
        assert_eq!(conversation_route("/", "socketio/"), Ok("socketio/".into()));
        assert_eq!(conversation_route("/", "socket.io/"), Ok("socket.io/".into()));
        assert_eq!(conversation_route("/", "api/kernels/"), Ok("api/kernels/".into()));
        assert_eq!(conversation_route("/", "websocket"), Ok("websocket".into()));
        assert_eq!(conversation_route("/", ""), Ok("".into()));
        assert_eq!(conversation_route("/repo.git/", "info/"), Ok("repo.git/info/".into()));
        for bad in ["/", "//", "a//", "/a/", "a//b/", "./", "../", "a/./", "a b/"] {
            assert!(conversation_route("/", bad).is_err(), "{bad}");
        }
        // The ordinary route is unchanged: a trailing slash stays refused there.
        assert!(route("/", "socketio/").is_err());
    }
}
