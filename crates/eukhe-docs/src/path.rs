//! Path resolution against the caller's working directory and the
//! snapshot key every store entry uses.

use std::path::{Component, Path, PathBuf};

/// Resolve an authored path: `~` expands to `home`, relative paths join `cwd`.
#[must_use]
pub fn resolve(cwd: &Path, home: Option<&Path>, authored: &str) -> PathBuf {
    let expanded = match (authored.strip_prefix('~'), home) {
        (Some(""), Some(home)) => home.to_path_buf(),
        (Some(rest), Some(home)) if rest.starts_with('/') => home.join(&rest[1..]),
        (Some(_) | None, Some(_) | None) => PathBuf::from(authored),
    };
    if expanded.is_absolute() {
        expanded
    } else {
        cwd.join(expanded)
    }
}

/// Snapshot key: the realpath, else the parent realpath plus the file name,
/// else the input.
#[must_use]
pub fn canonical_key(absolute: &Path) -> PathBuf {
    std::fs::canonicalize(absolute)
        .or_else(|_| {
            let parent = absolute.parent().ok_or(std::io::ErrorKind::NotFound)?;
            let name = absolute.file_name().ok_or(std::io::ErrorKind::NotFound)?;
            std::fs::canonicalize(parent).map(|parent| parent.join(name))
        })
        .unwrap_or_else(|_| absolute.to_path_buf())
}

/// Drop `.` components and resolve `..` against the preceding component,
/// without touching the filesystem.
#[must_use]
pub fn lexical_normalize(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => {
                normalized.push(component.as_os_str());
            }
        }
    }
    normalized
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolves_home_relative_and_absolute() {
        let cwd = Path::new("/work");
        let home = Some(Path::new("/home/u"));
        assert_eq!(
            [
                resolve(cwd, home, "~/a.rs"),
                resolve(cwd, home, "src/a.rs"),
                resolve(cwd, home, "/etc/x"),
                resolve(cwd, None, "~/a.rs"),
            ],
            [
                PathBuf::from("/home/u/a.rs"),
                PathBuf::from("/work/src/a.rs"),
                PathBuf::from("/etc/x"),
                PathBuf::from("/work/~/a.rs"),
            ]
        );
    }
}
