//! Path arguments of the file tools. Port of `tools/path-utils.ts`.

use eukhe_chord::context::Context;
use unicode_normalization::UnicodeNormalization;

use crate::env::{ExecutionEnv, FileError};

const NARROW_NO_BREAK_SPACE: char = '\u{202F}';

/// `/[\u00A0\u2000-\u200A\u202F\u205F\u3000]/`.
fn is_unicode_space(c: char) -> bool {
    matches!(
        c,
        '\u{00A0}' | '\u{2000}'..='\u{200A}' | '\u{202F}' | '\u{205F}' | '\u{3000}'
    )
}

fn normalize_tool_path(path: &str) -> String {
    let normalized: String = path
        .chars()
        .map(|c| if is_unicode_space(c) { ' ' } else { c })
        .collect();
    match normalized.strip_prefix('@') {
        Some(rest) => rest.to_owned(),
        None => normalized,
    }
}

pub(crate) async fn resolve_tool_path(
    env: &dyn ExecutionEnv,
    path: &str,
    cx: &Context,
) -> Result<String, FileError> {
    env.absolute_path(&normalize_tool_path(path), cx).await
}

/// The first of the path's macOS variants that exists (screenshot names with
/// U+202F before AM/PM, NFD names, U+2019 apostrophes), else the path.
pub(crate) async fn resolve_read_tool_path(
    env: &dyn ExecutionEnv,
    path: &str,
    cx: &Context,
) -> Result<String, FileError> {
    let resolved = resolve_tool_path(env, path, cx).await?;
    let nfd: String = resolved.nfd().collect();
    let variants = [
        resolved.clone(),
        narrow_space_before_meridiem(&resolved),
        nfd.clone(),
        resolved.replace('\'', "\u{2019}"),
        nfd.replace('\'', "\u{2019}"),
    ];

    // `new Set(variants)`: the first occurrence of each, in order.
    for (index, variant) in variants.iter().enumerate() {
        if variants[..index].contains(variant) {
            continue;
        }
        if env.exists(variant, cx).await? {
            return Ok(variant.clone());
        }
    }
    Ok(resolved)
}

/// `path.replace(/ (AM|PM)\./gi, "\u202F$1.")`. The pattern is ASCII, so
/// matching bytes never splits a character.
fn narrow_space_before_meridiem(path: &str) -> String {
    let bytes = path.as_bytes();
    let mut result = String::with_capacity(path.len());
    let mut copied = 0;
    let mut index = 0;
    while index + 4 <= bytes.len() {
        let matches = bytes[index] == b' '
            && matches!(bytes[index + 1], b'A' | b'a' | b'P' | b'p')
            && matches!(bytes[index + 2], b'M' | b'm')
            && bytes[index + 3] == b'.';
        if matches {
            result.push_str(&path[copied..index]);
            result.push(NARROW_NO_BREAK_SPACE);
            result.push_str(&path[index + 1..index + 4]);
            index += 4;
            copied = index;
        } else {
            index += 1;
        }
    }
    result.push_str(&path[copied..]);
    result
}

#[cfg(test)]
mod tests {
    use eukhe_chord::context::BACKGROUND_CONTEXT;

    use super::*;
    use crate::env::{NativeExecutionEnv, NativeExecutionEnvOptions};

    #[test]
    fn replaces_meridiem_spaces_case_insensitively() {
        assert_eq!(
            narrow_space_before_meridiem("Shot 1.02.03 PM.png am. x Am.y"),
            "Shot 1.02.03\u{202F}PM.png\u{202F}am. x\u{202F}Am.y"
        );
        assert_eq!(
            narrow_space_before_meridiem(" AM. PM."),
            "\u{202F}AM.\u{202F}PM."
        );
        assert_eq!(narrow_space_before_meridiem(" AM"), " AM");
    }

    #[tokio::test]
    async fn resolves_unicode_spaces_and_at_prefixes() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().to_str().unwrap().to_owned();
        let env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
            cwd: cwd.clone(),
            ..Default::default()
        });
        let resolved = resolve_tool_path(&env, "@a\u{00A0}b\u{3000}c.txt", &BACKGROUND_CONTEXT)
            .await
            .unwrap();
        assert_eq!(resolved, format!("{cwd}/a b c.txt"));
    }

    #[tokio::test]
    async fn resolves_read_paths_to_existing_macos_variants() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path().to_str().unwrap().to_owned();
        let env = NativeExecutionEnv::new(NativeExecutionEnvOptions {
            cwd: cwd.clone(),
            ..Default::default()
        });
        let screenshot = "Screenshot 2024-01-01 at 10.00.00\u{202F}AM.png";
        std::fs::write(dir.path().join(screenshot), b"").unwrap();
        let curly = "Capture d\u{2019}e\u{0301}cran.png";
        std::fs::write(dir.path().join(curly), b"").unwrap();

        let cx = &BACKGROUND_CONTEXT;
        assert_eq!(
            resolve_read_tool_path(&env, "Screenshot 2024-01-01 at 10.00.00 AM.png", cx)
                .await
                .unwrap(),
            format!("{cwd}/{screenshot}")
        );
        assert_eq!(
            resolve_read_tool_path(&env, "Capture d'\u{00E9}cran.png", cx)
                .await
                .unwrap(),
            format!("{cwd}/{curly}")
        );
        assert_eq!(
            resolve_read_tool_path(&env, "missing.txt", cx)
                .await
                .unwrap(),
            format!("{cwd}/missing.txt")
        );
    }
}
