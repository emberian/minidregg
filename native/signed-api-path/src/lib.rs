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

/// Accept only a literal, canonical, slash-terminated signed prefix. `/` is
/// the root API profile; a missing prefix means that the SPK has no HTTP API.
pub fn checked_prefix(prefix: &str) -> Result<(), &'static str> {
    if prefix.is_empty()
        || prefix.len() > MAX_PREFIX
        || !prefix.starts_with('/')
        || !prefix.ends_with('/')
    {
        return Err("signed API prefix is not canonical");
    }
    if prefix != "/" && !prefix[1..prefix.len() - 1].split('/').all(safe_segment) {
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
