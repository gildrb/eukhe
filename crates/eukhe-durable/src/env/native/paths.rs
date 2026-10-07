//! Node's POSIX `path` functions, `os.homedir()`, `os.tmpdir()`, and
//! `url.fileURLToPath()`, as `env/node.ts` uses them.

use percent_encoding::percent_decode_str;

/// The segments of `path` after removing `.`, empty segments, and resolving
/// `..`; with `allow_above_root`, leading `..` segments are kept. Node's
/// `normalizeString`.
fn normalize_segments(path: &str, allow_above_root: bool) -> String {
    let mut segments: Vec<&str> = Vec::new();
    for segment in path.split('/') {
        match segment {
            "" | "." => {}
            ".." => {
                if segments.last().is_some_and(|last| *last != "..") {
                    segments.pop();
                } else if allow_above_root {
                    segments.push("..");
                }
            }
            name => segments.push(name),
        }
    }
    segments.join("/")
}

/// `process.cwd()`, or `/` when it cannot be read.
fn process_cwd() -> String {
    std::env::current_dir().map_or_else(
        |_| "/".to_owned(),
        |path| path.to_string_lossy().into_owned(),
    )
}

/// Node's `path.posix.resolve(...paths)`.
pub(crate) fn resolve(paths: &[&str]) -> String {
    let mut resolved = String::new();
    let mut absolute = false;
    for path in paths.iter().rev() {
        if path.is_empty() {
            continue;
        }
        resolved = format!("{path}/{resolved}");
        absolute = path.starts_with('/');
        if absolute {
            break;
        }
    }
    if !absolute {
        let cwd = process_cwd();
        absolute = cwd.starts_with('/');
        resolved = format!("{cwd}/{resolved}");
    }
    let normalized = normalize_segments(&resolved, !absolute);
    if absolute {
        format!("/{normalized}")
    } else if normalized.is_empty() {
        ".".to_owned()
    } else {
        normalized
    }
}

/// Node's `path.posix.normalize(path)`.
pub(crate) fn normalize(path: &str) -> String {
    if path.is_empty() {
        return ".".to_owned();
    }
    let absolute = path.starts_with('/');
    let trailing_separator = path.ends_with('/');
    let mut normalized = normalize_segments(path, !absolute);
    if normalized.is_empty() {
        if absolute {
            return "/".to_owned();
        }
        return if trailing_separator { "./" } else { "." }.to_owned();
    }
    if trailing_separator {
        normalized.push('/');
    }
    if absolute {
        format!("/{normalized}")
    } else {
        normalized
    }
}

/// Node's `path.posix.join(...paths)`.
pub(crate) fn join(paths: &[&str]) -> String {
    let joined = paths
        .iter()
        .filter(|path| !path.is_empty())
        .copied()
        .collect::<Vec<_>>()
        .join("/");
    if joined.is_empty() {
        return ".".to_owned();
    }
    normalize(&joined)
}

/// Node's `path.posix.isAbsolute(path)`.
pub(crate) fn is_absolute(path: &str) -> bool {
    path.starts_with('/')
}

/// Node's `path.posix.basename(path)`.
pub(crate) fn basename(path: &str) -> &str {
    let trimmed = path.trim_end_matches('/');
    if trimmed.is_empty() {
        return "";
    }
    trimmed.rsplit('/').next().unwrap_or(trimmed)
}

/// `os.homedir()`: `$HOME`, else the password database entry.
pub(crate) fn home_dir() -> String {
    // Node throws when neither exists; a process without a home directory
    // cannot resolve `~`, so it resolves to the root instead.
    std::env::home_dir().map_or_else(
        || "/".to_owned(),
        |path| path.to_string_lossy().into_owned(),
    )
}

/// `os.tmpdir()` on POSIX: `$TMPDIR`, `$TMP`, `$TEMP`, or `/tmp`, without a
/// trailing slash.
pub(crate) fn tmp_dir() -> String {
    let mut path = ["TMPDIR", "TMP", "TEMP"]
        .into_iter()
        .find_map(|name| std::env::var(name).ok().filter(|value| !value.is_empty()))
        .unwrap_or_else(|| "/tmp".to_owned());
    if path.len() > 1 && path.ends_with('/') {
        path.pop();
    }
    path
}

/// `url.fileURLToPath(url)` on POSIX, or `None` where Node throws: not a
/// `file:` URL, a host, an encoded `/`, or percent-escapes that are not UTF-8.
pub(crate) fn file_url_to_path(input: &str) -> Option<String> {
    let url = url::Url::parse(input).ok()?;
    if url.scheme() != "file" {
        return None;
    }
    if url.host_str().is_some_and(|host| !host.is_empty()) {
        return None;
    }
    let pathname = url.path();
    let bytes = pathname.as_bytes();
    for (index, byte) in bytes.iter().enumerate() {
        if *byte == b'%'
            && bytes.get(index + 1) == Some(&b'2')
            && bytes.get(index + 2).is_some_and(|next| next | 0x20 == b'f')
        {
            return None;
        }
    }
    percent_decode_str(pathname)
        .decode_utf8()
        .ok()
        .map(std::borrow::Cow::into_owned)
}

/// `resolvePath` of `env/node.ts`: `~`, `~/…`, and `file://` URLs, then
/// `path.resolve` against `cwd`.
pub(crate) fn resolve_path(cwd: &str, path: &str) -> String {
    let normalized = if path == "~" {
        home_dir()
    } else if let Some(rest) = path.strip_prefix("~/") {
        join(&[&home_dir(), rest])
    } else if path.starts_with("file://") {
        // Keep malformed URLs as ordinary paths so filesystem methods preserve
        // their non-failing contract.
        file_url_to_path(path).unwrap_or_else(|| path.to_owned())
    } else {
        path.to_owned()
    };
    if is_absolute(&normalized) {
        resolve(&[&normalized])
    } else {
        resolve(&[cwd, &normalized])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn posix_path_functions_match_node() {
        assert_eq!(resolve(&["/a/b", "../c/./d/"]), "/a/c/d");
        assert_eq!(resolve(&["/a", "/b", "c"]), "/b/c");
        assert_eq!(resolve(&["/", ".."]), "/");
        assert_eq!(join(&["a/", "b/"]), "a/b/");
        assert_eq!(join(&["/a", "..", "..", "b"]), "/b");
        assert_eq!(join(&["a", "../../b"]), "../b");
        assert_eq!(join(&["", ""]), ".");
        assert_eq!(join(&["/x/y", ".."]), "/x");
        assert_eq!(normalize("./"), "./");
        assert_eq!(basename("/a/b.txt"), "b.txt");
        assert_eq!(basename("/a/b/"), "b");
        assert_eq!(basename("/"), "");
        assert_eq!(
            file_url_to_path("file:///tmp/file%20with%20spaces.txt").as_deref(),
            Some("/tmp/file with spaces.txt")
        );
        assert_eq!(
            file_url_to_path("file://localhost/tmp/x").as_deref(),
            Some("/tmp/x")
        );
        assert_eq!(file_url_to_path("file://host/tmp/x"), None);
        assert_eq!(file_url_to_path("file:///tmp/a%2Fb"), None);
    }
}
