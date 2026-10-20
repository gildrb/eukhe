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

/// Splits `input` on top-level `;`, leaving `;` inside `{...}` and after `\`
/// in place.
pub(crate) fn split_top_level_semicolons(input: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut brace_depth = 0_u32;
    let mut start = 0;
    let mut escaped = false;
    for (index, character) in input.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        match character {
            '\\' => escaped = true,
            '{' => brace_depth = brace_depth.saturating_add(1),
            '}' => brace_depth = brace_depth.saturating_sub(1),
            ';' if brace_depth == 0 => {
                parts.push(&input[start..index]);
                start = index + character.len_utf8();
            }
            _ => {}
        }
    }
    parts.push(&input[start..]);
    parts
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

/// Whether `name` is a temporary file of a document write: grep and glob
/// hide these names.
pub(crate) fn is_eukhe_temp(name: &std::ffi::OsStr) -> bool {
    name.as_encoded_bytes()
        .starts_with(crate::write::TEMP_PREFIX.as_bytes())
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
    fn top_level_semicolons_split_outside_braces_and_escapes() {
        assert_eq!(
            split_top_level_semicolons("src/{one;two}.rs; tests/**/*.rs"),
            ["src/{one;two}.rs", " tests/**/*.rs"]
        );
        assert_eq!(split_top_level_semicolons(r"src/a\;b.rs"), [r"src/a\;b.rs"]);
    }

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
