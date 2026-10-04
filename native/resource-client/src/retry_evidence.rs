//! Retained physical-delivery evidence for one unchanged semantic call.
//! File numbering is custody bookkeeping, not an admission/retry budget. A
//! sparse or metadata-only prior attempt remains reserved; all readers use the
//! same numeric grammar and never mistake transport metadata for an outcome.
use std::fs;
use std::path::{Path, PathBuf};

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind { Binary, Outcome, Transport }

fn parse(name: &str) -> Option<(u64, Kind)> {
    let (stem, kind) = if let Some(stem) = name.strip_suffix(".transport.json") {
        (stem, Kind::Transport)
    } else if let Some(stem) = name.strip_suffix(".json") {
        (stem, Kind::Outcome)
    } else if let Some(stem) = name.strip_suffix(".bin") {
        (stem, Kind::Binary)
    } else { return None };
    let digits = stem.strip_prefix("retry-")?;
    // Existing clients used zero-padded names of several widths. Preserve that
    // evidence; new names use a minimum width of four, without a four-digit cap.
    if !mini_sdk::decimal::is_digits(digits) { return None }
    Some((digits.parse().ok()?, kind))
}

/// Allocate after the greatest reserved attempt in one streaming directory
/// pass. No repeated probes of nonexistent filenames, no gap reuse after a
/// partial write, and no artificial exhaustion at four decimal digits.
/// Exclusive writers still protect the returned paths against concurrent use.
pub(crate) fn next_paths(directory: &Path) -> Result<(PathBuf, PathBuf)> {
    let mut greatest = 0u64;
    for entry in fs::read_dir(directory).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        if let Some((index, _)) = entry.file_name().to_str().and_then(parse) {
            greatest = greatest.max(index);
        }
    }
    let index = greatest.checked_add(1).ok_or("retry evidence sequence exceeds u64")?;
    Ok((directory.join(format!("retry-{index:04}.bin")),
        directory.join(format!("retry-{index:04}.json"))))
}

/// Retained decoded outcomes in numeric attempt order. Transport bookkeeping
/// is never an outcome; a fifth digit does not reorder time lexicographically.
pub(crate) fn outcomes(directory: &Path) -> Result<Vec<PathBuf>> {
    let mut rows = Vec::new();
    for entry in fs::read_dir(directory).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        if let Some((index, Kind::Outcome)) = entry.file_name().to_str().and_then(parse) {
            rows.push((index, entry.path()));
        }
    }
    rows.sort_by(|left, right| left.0.cmp(&right.0).then_with(|| left.1.cmp(&right.1)));
    Ok(rows.into_iter().map(|(_, path)| path).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!("mini-retry-evidence-{}-{}",
                std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
            fs::create_dir(&path).unwrap(); Self(path)
        }
        fn put(&self, name: &str) { fs::write(self.0.join(name), name.as_bytes()).unwrap(); }
    }
    impl Drop for Scratch { fn drop(&mut self) { fs::remove_dir_all(&self.0).unwrap(); } }

    #[test]
    fn metadata_and_partial_writes_reserve_their_attempt_without_becoming_outcomes() {
        let root = Scratch::new();
        for name in ["retry-0001.bin", "retry-0002.json", "retry-10000.transport.json"] { root.put(name) }
        assert_eq!(next_paths(&root.0).unwrap(),
            (root.0.join("retry-10001.bin"), root.0.join("retry-10001.json")));
        assert_eq!(outcomes(&root.0).unwrap(), vec![root.0.join("retry-0002.json")]);
        assert_eq!(fs::read(root.0.join("retry-10000.transport.json")).unwrap(), b"retry-10000.transport.json");
    }

    #[test]
    fn later_outcomes_remain_later_beyond_four_digits_and_legacy_padding_is_preserved() {
        let root = Scratch::new();
        for name in ["retry-10000.json", "retry-9999.json", "retry-003.json",
            "retry-10000.transport.json", "retry-garbage.json", "retry--1.json"] { root.put(name) }
        assert_eq!(outcomes(&root.0).unwrap(), ["retry-003.json", "retry-9999.json", "retry-10000.json"]
            .map(|name| root.0.join(name)).to_vec());
        assert_eq!(next_paths(&root.0).unwrap().0, root.0.join("retry-10001.bin"));
    }

    #[test]
    fn sparse_history_does_not_reuse_old_attempt_numbers() {
        let root = Scratch::new(); root.put("retry-0042.bin");
        assert_eq!(next_paths(&root.0).unwrap().1, root.0.join("retry-0043.json"));
    }

    #[test]
    fn representational_exhaustion_refuses_without_wrapping_to_prior_evidence() {
        let root = Scratch::new(); root.put("retry-18446744073709551615.bin");
        assert!(next_paths(&root.0).unwrap_err().contains("exceeds u64"));
    }
}
