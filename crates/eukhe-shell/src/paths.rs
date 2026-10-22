//! The judgment of a path under the session's [`PathPolicy`] (docs/tools.md
//! S7, `LAWS.bend` section `path_policy`): `judge` in `bend/path_policy.bend`,
//! one pure call per path the shell or a document tool touches. The
//! caller resolves the path ([`resolve`], IO) and judges the [`RealPath`]
//! it acts on; a second resolution would lose a loop.
//!
//! - The class: Secret under a secret entry; else Protected when a rule
//!   covers it (a Tree rule's path or anything under it, a Dir rule's
//!   directory or an entry directly in it, a Named rule's name as a
//!   component below the path's deepest workspace root) or it is an
//!   ancestor of a rule's entry or of a secret; else Inside under a
//!   workspace root unless its links looped; else Outside.
//! - It holds a secret: it is under a secret entry, or an ancestor of one.

use std::path::{Path, PathBuf};

use eukhe_types::path_policy::{resolve, PathClass, PathPolicy, PathRule, RealPath};

/// The judgment of one resolved path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Judged {
    pub class: PathClass,
    /// It is a secret or a directory that holds one: a recursive read of
    /// it reads a secret.
    pub holds_secret: bool,
}

/// The judgment of `resolved` under `policy`, on its real path as it is.
#[must_use]
pub fn judge(policy: &PathPolicy, resolved: &RealPath) -> Judged {
    let real = resolved.path();
    let secret = policy.secret();
    let holds_secret = secret
        .iter()
        .any(|entry| entry.starts_with(real) || real.starts_with(entry));
    if secret.iter().any(|entry| real.starts_with(entry)) {
        return Judged {
            class: PathClass::Secret,
            holds_secret,
        };
    }
    let root = policy
        .roots()
        .iter()
        .filter(|root| real.starts_with(root))
        .max_by_key(|root| root.components().count());
    let below = root.map_or(real, |root| real.strip_prefix(root).unwrap_or(real));
    let ancestor = |entry: &Path| entry != real && entry.starts_with(real);
    let protected = policy
        .protected()
        .iter()
        .any(|rule| covers(rule, real, below))
        || policy
            .protected()
            .iter()
            .filter_map(PathRule::entry)
            .chain(secret.iter().map(PathBuf::as_path))
            .any(ancestor);
    let class = match (protected, root, resolved.looped()) {
        (true, _, _) => PathClass::Protected,
        (false, Some(_), false) => PathClass::Inside,
        (false, Some(_), true) | (false, None, _) => PathClass::Outside,
    };
    Judged {
        class,
        holds_secret,
    }
}

/// `rule` covers `real`; `below` is the part of `real` under its
/// workspace root (all of it when under no root).
fn covers(rule: &PathRule, real: &Path, below: &Path) -> bool {
    match rule {
        PathRule::Tree(path) => real.starts_with(path),
        PathRule::Dir(path) => real == path || real.parent() == Some(path.as_path()),
        PathRule::Named(name) => below
            .components()
            .any(|component| component.as_os_str() == name.as_os_str()),
    }
}

/// The judgment of `absolute`, on its real path ([`resolve`]).
#[must_use]
pub fn judge_path(policy: &PathPolicy, absolute: &Path) -> Judged {
    judge(policy, &resolve(absolute))
}

#[cfg(test)]
mod tests;
