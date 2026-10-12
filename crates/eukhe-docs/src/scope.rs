//! Authored search targets: `;`-separated roots resolved against the caller's
//! working directory, glob splitting, and workspace-relative display paths.
//!
//! Ported from omp `crates/envd/src/tool_search.rs` and
//! `crates/tools/src/read/selector.rs`.

use std::{
    io,
    path::{Component, Path, PathBuf},
};

/// Trims whitespace and one pair of surrounding double quotes.
pub(crate) fn normalize_path_input(input: &str) -> &str {
    let trimmed = input.trim();
    if trimmed.len() > 1 && trimmed.starts_with('"') && trimmed.ends_with('"') {
        &trimmed[1..trimmed.len() - 1]
    } else {
        trimmed
    }
}

/// Whether a path segment holds glob syntax.
pub(crate) fn has_glob_chars(segment: &str) -> bool {
    segment
        .bytes()
        .any(|byte| matches!(byte, b'*' | b'?' | b'[' | b'{'))
}

/// Joins a relative input onto `root`; absolute inputs stay as they are.
pub(crate) fn resolve_input_path(root: &Path, input: &str) -> PathBuf {
    let path = Path::new(input);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    }
}

/// Whether a metadata failure means the target does not exist.
pub(crate) fn is_missing(error: &io::Error) -> bool {
    matches!(
        error.kind(),
        io::ErrorKind::NotFound | io::ErrorKind::NotADirectory | io::ErrorKind::InvalidInput
    )
}

/// `path` relative to `root` with `/` separators; a path outside `root` stays
/// absolute.
pub(crate) fn workspace_relative(root: &Path, path: &Path) -> io::Result<String> {
    let Ok(relative) = path.strip_prefix(root) else {
        return Ok(path.to_string_lossy().replace('\\', "/"));
    };
    let mut normalized = String::new();
    for component in relative.components() {
        match component {
            Component::CurDir => {}
            Component::Normal(component) => {
                if !normalized.is_empty() {
                    normalized.push('/');
                }
                normalized.push_str(&component.to_string_lossy());
            }
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::PermissionDenied,
                    "path is outside the workspace",
                ));
            }
        }
    }
    Ok(normalized)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quoted_inputs_lose_one_quote_pair() {
        assert_eq!(
            [
                normalize_path_input(r#" "a b" "#),
                normalize_path_input("\""),
                normalize_path_input(" src ")
            ],
            ["a b", "\"", "src"]
        );
    }

    #[test]
    fn display_paths_are_relative_inside_the_root_and_absolute_outside() {
        let root = Path::new("/work");
        assert_eq!(
            [
                workspace_relative(root, Path::new("/work/src/a.rs")).unwrap(),
                workspace_relative(root, Path::new("/elsewhere/b.rs")).unwrap(),
            ],
            ["src/a.rs", "/elsewhere/b.rs"]
        );
    }
}
