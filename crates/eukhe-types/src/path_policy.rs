//! The path policy (docs/tools.md S7, LAWS.bend (G1)): the class of a
//! path that an agent tool reads or writes. The document tools and the
//! shell use this one policy, so the two cannot judge a path differently.
//!
//! A path is judged on its real path: [`resolve`] follows every symlink
//! on the part of the path that exists (a dangling link too: a write
//! through it creates its target), and `..` after a resolved part goes up
//! from the real directory. A symlink is thus judged by its target. A
//! tool that resolved a path itself judges the [`RealPath`] it acts on
//! ([`PathPolicy::class_of_resolved`]); a second resolution of the real
//! path would lose a loop.
//!
//! The classes, strongest first:
//!
//! - [`PathClass::Secret`]: under a secret entry (an ssh key dir, a
//!   credential store). A read asks the user; a write asks the user.
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
    fn entry(&self) -> Option<&Path> {
        match self {
            Self::Tree(path) | Self::Dir(path) => Some(path),
            Self::Named(_) => None,
        }
    }

    /// `real` is covered; `below` is the part of `real` under its
    /// workspace root (all of it when under no root).
    fn covers(&self, real: &Path, below: &Path) -> bool {
        match self {
            Self::Tree(path) => real.starts_with(path),
            Self::Dir(path) => real == path || real.parent() == Some(path.as_path()),
            Self::Named(name) => below
                .components()
                .any(|component| component.as_os_str() == name.as_os_str()),
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

    /// The class of `absolute`, judged on its real path.
    #[must_use]
    pub fn class(&self, absolute: &Path) -> PathClass {
        self.class_of_resolved(&resolve(absolute))
    }

    /// The class of a resolved path, judged on its real path as it is (no
    /// second resolution): the place where an access to it happens. A path
    /// whose links looped is never [`PathClass::Inside`].
    #[must_use]
    pub fn class_of_resolved(&self, resolved: &RealPath) -> PathClass {
        let real = resolved.path();
        if self.secret.iter().any(|entry| real.starts_with(entry)) {
            return PathClass::Secret;
        }
        let root = self
            .roots
            .iter()
            .filter(|root| real.starts_with(root))
            .max_by_key(|root| root.components().count());
        let below = root.map_or(real, |root| real.strip_prefix(root).unwrap_or(real));
        let ancestor = |entry: &Path| entry != real && entry.starts_with(real);
        let protected = self.protected.iter().any(|rule| rule.covers(real, below))
            || self
                .protected
                .iter()
                .filter_map(PathRule::entry)
                .chain(self.secret.iter().map(PathBuf::as_path))
                .any(ancestor);
        match (protected, root, resolved.looped()) {
            (true, _, _) => PathClass::Protected,
            (false, Some(_), false) => PathClass::Inside,
            (false, Some(_), true) | (false, None, _) => PathClass::Outside,
        }
    }

    /// `absolute` is a secret, or a directory that holds one: a recursive
    /// read of it reads a secret.
    #[must_use]
    pub fn holds_secret(&self, absolute: &Path) -> bool {
        self.holds_secret_of_resolved(&resolve(absolute))
    }

    /// [`Self::holds_secret`] of a resolved path, as it is (no second
    /// resolution).
    #[must_use]
    pub fn holds_secret_of_resolved(&self, resolved: &RealPath) -> bool {
        let real = resolved.path();
        self.secret
            .iter()
            .any(|entry| entry.starts_with(real) || real.starts_with(entry))
    }
}

#[cfg(test)]
mod tests;
