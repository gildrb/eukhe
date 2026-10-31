//! The path policy (`laws/path_policy.bend` (G1)): the data that
//! judges a path an agent tool reads or writes. The document tools and
//! the shell use this one policy, so the two cannot judge a path
//! differently; the judgment itself is `eukhe_shell::paths::judge`
//! (`judge` in `bend/path_policy.bend`).
//!
//! A path is judged on its real path: [`resolve`] follows every symlink
//! on the part of the path that exists (a dangling link too: a write
//! through it creates its target), and `..` after a resolved part goes up
//! from the real directory. A symlink is thus judged by its target. A
//! tool that resolved a path itself judges the [`RealPath`] it acts on; a
//! second resolution of the real path would lose a loop.
//!
//! The classes, strongest first:
//!
//! - [`PathClass::Secret`]: under a secret entry (an ssh key dir, a
//!   credential store). A read or a write gates like any access: the
//!   user's auto set decides.
//! - [`PathClass::Protected`]: eukhe's own config and credentials (a
//!   [`PathRule`] covers it), or an ancestor of a protected or secret entry
//!   (a write there can move or remove the entry). A write asks the user.
//! - [`PathClass::Inside`]: under a workspace root. A write may run
//!   without a question when the user's auto set allows writes.
//! - [`PathClass::Outside`]: anything else. A write asks the user.
//!
//! A path whose links loop (more than [`MAX_LINKS`] links) is never
//! [`PathClass::Inside`]: the part not resolved cannot be judged.

use std::ffi::OsString;
use std::path::{Component, Path, PathBuf};

use serde::{Deserialize, Serialize};

/// The most symlinks one resolution follows (Linux `MAXSYMLINKS`); past
/// it the path loops.
pub const MAX_LINKS: usize = 40;

/// The class of one path under a [`PathPolicy`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PathClass {
    /// Under a workspace root, and covered by no stronger class.
    Inside,
    /// Under no workspace root, and covered by no stronger class.
    Outside,
    /// eukhe's own config or credentials, or an ancestor of them.
    Protected,
    /// A secret: ssh keys, credential stores.
    Secret,
}

impl PathClass {
    /// The class's wire name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Inside => "inside",
            Self::Outside => "outside",
            Self::Protected => "protected",
            Self::Secret => "secret",
        }
    }
}

/// One rule of the protected set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathRule {
    /// The path and everything under it.
    Tree(PathBuf),
    /// The directory itself and every entry directly in it (not deeper).
    Dir(PathBuf),
    /// Every path with a component of this name below its workspace root
    /// (any component, when the path is under no root).
    Named(OsString),
}

impl PathRule {
    /// The rule over real paths.
    fn real(self) -> Self {
        match self {
            Self::Tree(path) => Self::Tree(real_path(&path)),
            Self::Dir(path) => Self::Dir(real_path(&path)),
            Self::Named(name) => Self::Named(name),
        }
    }

    /// The concrete path the rule names; `None` for a name rule.
    #[must_use]
    pub fn entry(&self) -> Option<&Path> {
        match self {
            Self::Tree(path) | Self::Dir(path) => Some(path),
            Self::Named(_) => None,
        }
    }
}

/// The workspace roots, the protected rules and the secret entries of one
/// session, each over real paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathPolicy {
    roots: Vec<PathBuf>,
    protected: Vec<PathRule>,
    secret: Vec<PathBuf>,
}

/// One step of a resolution.
enum Part {
    Root,
    Up,
    Name(OsString),
}

/// Push the parts of `path` on `stack`, so the first part pops first.
fn push_parts(stack: &mut Vec<Part>, path: &Path) {
    let parts: Vec<Part> = path
        .components()
        .filter_map(|component| match component {
            Component::Prefix(_) | Component::RootDir => Some(Part::Root),
            Component::CurDir => None,
            Component::ParentDir => Some(Part::Up),
            Component::Normal(name) => Some(Part::Name(name.to_os_string())),
        })
        .collect();
    stack.extend(parts.into_iter().rev());
}

/// A path with every symlink on its existing part followed ([`resolve`]),
/// and whether its links looped. The document tools act on [`Self::path`]
/// and their gate judges this value, so the gate judges the place the
/// access happens, and a loop is not lost between the two.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RealPath {
    path: PathBuf,
    looped: bool,
}

impl RealPath {
    /// The real path; a path whose links looped keeps the link where the
    /// count ran out.
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// More than [`MAX_LINKS`] links: the part after them is not resolved.
    #[must_use]
    pub fn looped(&self) -> bool {
        self.looped
    }

    /// The real path, owned.
    #[must_use]
    pub fn into_path(self) -> PathBuf {
        self.path
    }
}

/// Resolve `absolute`: every symlink on the part that exists is followed
/// (a dangling one too), `.` is dropped, and `..` goes up from the real
/// directory (`..` of `/` is `/`). The part that does not exist is kept as
/// written. Past [`MAX_LINKS`] links the path loops: the link where the
/// count ran out is kept as a name.
#[must_use]
pub fn resolve(absolute: &Path) -> RealPath {
    let mut stack = Vec::new();
    push_parts(&mut stack, absolute);
    let mut path = PathBuf::new();
    let mut links = 0;
    let mut looped = false;
    while let Some(part) = stack.pop() {
        match part {
            Part::Root => path = PathBuf::from("/"),
            Part::Up => {
                // `path` holds no link, so its parent is the real `..`;
                // `..` of `/` is `/`.
                path.pop();
            }
            Part::Name(name) => {
                let next = path.join(name);
                let target = std::fs::symlink_metadata(&next)
                    .ok()
                    .filter(|metadata| metadata.file_type().is_symlink())
                    .and_then(|_| std::fs::read_link(&next).ok());
                match target {
                    Some(target) if links < MAX_LINKS => {
                        links += 1;
                        // An absolute target starts with the root part.
                        push_parts(&mut stack, &target);
                    }
                    Some(_) => {
                        looped = true;
                        path = next;
                    }
                    None => path = next,
                }
            }
        }
    }
    RealPath { path, looped }
}

/// The real path of `absolute` ([`resolve`]).
#[must_use]
pub fn real_path(absolute: &Path) -> PathBuf {
    resolve(absolute).path
}

impl PathPolicy {
    /// A policy over `roots` (the workspace roots), `protected` and
    /// `secret` (each entry covers itself and everything under it). Every
    /// concrete path is made real now.
    #[must_use]
    pub fn new(roots: Vec<PathBuf>, protected: Vec<PathRule>, secret: Vec<PathBuf>) -> Self {
        Self {
            roots: roots.into_iter().map(|root| real_path(&root)).collect(),
            protected: protected.into_iter().map(PathRule::real).collect(),
            secret: secret.into_iter().map(|entry| real_path(&entry)).collect(),
        }
    }

    /// The workspace roots, real.
    #[must_use]
    pub fn roots(&self) -> &[PathBuf] {
        &self.roots
    }

    /// The protected rules, over real paths.
    #[must_use]
    pub fn protected(&self) -> &[PathRule] {
        &self.protected
    }

    /// The secret entries, real.
    #[must_use]
    pub fn secret(&self) -> &[PathBuf] {
        &self.secret
    }
    /// Whether `resolved` is a strict ancestor of a secret (a secret
    /// below it, none at it): only a read that descends into it (a
    /// search) reads that secret, so a shallow listing does not. The
    /// wider `holds_secret` of the same path (the Bend model's `judge`)
    /// is this plus the secret itself and everything inside it.
    #[must_use]
    pub fn ancestor_of_secret_of_resolved(&self, resolved: &RealPath) -> bool {
        let real = resolved.path();
        self.secret
            .iter()
            .any(|entry| entry != real && entry.starts_with(real))
    }
}

#[cfg(test)]
mod tests;
