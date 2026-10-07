//! POSIX path helpers of `node-watch.ts`: Node's `path.posix` `dirname` and
//! `relative` as the watcher uses them, `ancestorsOf`, `isWithin`, and JS's
//! default sort order.

use std::cmp::Ordering;

/// The separator of the POSIX paths the watcher works on (TS `sep`).
pub(super) const SEP: &str = "/";

/// Node's `path.posix.dirname`.
pub(super) fn dirname(path: &str) -> &str {
    if path.is_empty() {
        return ".";
    }
    let bytes = path.as_bytes();
    let has_root = bytes[0] == b'/';
    let mut end = None;
    let mut matched_slash = true;
    for index in (1..bytes.len()).rev() {
        if bytes[index] == b'/' {
            if !matched_slash {
                end = Some(index);
                break;
            }
        } else {
            matched_slash = false;
        }
    }
    match end {
        None if has_root => "/",
        None => ".",
        Some(1) if has_root => "//",
        Some(end) => &path[..end],
    }
}

/// Ancestors of `path`, nearest first, up to the root.
pub(super) fn ancestors_of(path: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut current = dirname(path);
    loop {
        result.push(current.to_owned());
        let parent = dirname(current);
        if parent == current {
            return result;
        }
        current = parent;
    }
}

/// Whether `path` is `ancestor` or below it.
pub(super) fn is_within(path: &str, ancestor: &str) -> bool {
    if path == ancestor {
        return true;
    }
    if ancestor.ends_with(SEP) {
        path.starts_with(ancestor)
    } else {
        path.len() > ancestor.len()
            && path.starts_with(ancestor)
            && path[ancestor.len()..].starts_with(SEP)
    }
}

/// `${directory.endsWith(sep) ? directory : directory + sep}${name}`.
pub(super) fn join(directory: &str, name: &str) -> String {
    if directory.ends_with(SEP) {
        format!("{directory}{name}")
    } else {
        format!("{directory}{SEP}{name}")
    }
}

/// `relative(ancestor, path).split(sep)` for a `path` strictly below the
/// resolved `ancestor`: the components after it. Node's `relative` resolves
/// both paths first, which for the paths the watcher builds (a resolved target
/// joined with entry names) only drops empty components.
pub(super) fn components_below<'a>(ancestor: &str, path: &'a str) -> Vec<&'a str> {
    path[ancestor.len()..]
        .split(SEP)
        .filter(|component| !component.is_empty())
        .collect()
}

/// libuv's `uv__basename_r`: what follows the last `/`, or the whole path.
pub(super) fn basename(path: &str) -> &str {
    path.rfind('/').map_or(path, |index| &path[index + 1..])
}

/// JS's default `Array.prototype.sort` order: UTF-16 code units.
pub(super) fn compare_utf16(left: &str, right: &str) -> Ordering {
    left.encode_utf16().cmp(right.encode_utf16())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dirname_matches_node_posix() {
        assert_eq!(dirname("/a/b"), "/a");
        assert_eq!(dirname("/a/b/"), "/a");
        assert_eq!(dirname("/a"), "/");
        assert_eq!(dirname("/"), "/");
        assert_eq!(dirname("//a"), "//");
        assert_eq!(dirname("a"), ".");
        assert_eq!(dirname(""), ".");
    }

    #[test]
    fn ancestors_run_to_the_root() {
        assert_eq!(ancestors_of("/a/b/c"), ["/a/b", "/a", "/"]);
        assert_eq!(ancestors_of("/"), ["/"]);
    }

    #[test]
    fn within_needs_a_separator() {
        assert!(is_within("/a/b", "/a"));
        assert!(is_within("/a", "/a"));
        assert!(!is_within("/ab", "/a"));
        assert!(is_within("/a", "/"));
        assert_eq!(components_below("/a", "/a/b/c"), ["b", "c"]);
        assert_eq!(components_below("/", "/a/b"), ["a", "b"]);
    }

    #[test]
    fn sorts_by_utf16_code_units() {
        // U+1F600 sorts after U+FF5E in UTF-8 byte order but before it in UTF-16.
        assert_eq!(compare_utf16("\u{1F600}", "\u{FF5E}"), Ordering::Less);
    }
}
