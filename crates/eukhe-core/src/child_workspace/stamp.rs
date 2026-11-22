//! A workspace's stamp: the stat of each path it lists (the tracked and
//! the untracked, not ignored files, as a child's copy lists them; eukhe's
//! `.eukhe` directory left out), read without a byte of content. The
//! stamps before and after a check or a job name the paths written in
//! between: a result judged one tree state only when none was.
//!
//! Cost: one `git ls-files` and one `lstat` per path (no hashing); a
//! workspace without git, and a child's copy (whose own repository its
//! first git makes), is walked, and past [`MAX_WORKSPACE_FILES`] paths it
//! gets no stamp.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use super::files::{self, Listing};
use super::{ChildWorkspace, MAX_WORKSPACE_FILES};

/// The paths a [`WorkspaceDrift`] names; the others are only counted.
const NAMED_PATHS: usize = 8;

/// eukhe's own state directory in a project: its writes are no change of
/// the tree a check judges.
const EUKHE_DIR: &str = ".eukhe";

/// One path's stat: a write, a replacement and a mode change each change
/// it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Stat {
    inode: u64,
    len: u64,
    mode: u32,
    modified: (i64, i64),
    changed: (i64, i64),
}

impl Stat {
    fn of(meta: &fs::Metadata) -> Self {
        Self {
            inode: meta.ino(),
            len: meta.size(),
            mode: meta.mode(),
            modified: (meta.mtime(), meta.mtime_nsec()),
            changed: (meta.ctime(), meta.ctime_nsec()),
        }
    }
}

/// What a workspace held at one moment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TreeStamp {
    /// Each listed path's stat; `None`: listed (a tracked file) but gone.
    Taken(BTreeMap<PathBuf, Option<Stat>>),
    /// No stamp, and why.
    Missing(String),
}

impl TreeStamp {
    /// Stamp the workspace at `dir`.
    #[tracing::instrument(level = "debug")]
    pub(crate) async fn take(dir: &Path) -> Self {
        // A child's copy is walked, never listed by git: the repository
        // the child's first git makes there (`.git`, which the walk skips)
        // changes no stamp of it.
        let git = match ChildWorkspace::copy_at(dir) {
            Some(_) => None,
            None => files::git_paths(dir).await,
        };
        let listed = if let Some(paths) = git {
            Ok(paths)
        } else {
            let dir = dir.to_path_buf();
            tokio::task::spawn_blocking(move || bounded_walk(&dir))
                .await
                .unwrap_or_else(|error| Err(format!("the walk's task failed: {error}")))
        };
        let paths = match listed {
            Ok(paths) => paths,
            Err(reason) => return Self::Missing(reason),
        };
        let dir = dir.to_path_buf();
        tokio::task::spawn_blocking(move || stats(&dir, paths))
            .await
            .unwrap_or_else(|error| Self::Missing(format!("the stat task failed: {error}")))
    }

    /// The drift from `self` to the later stamp `after`.
    #[must_use]
    pub(crate) fn drift(&self, after: &Self) -> WorkspaceDrift {
        match (self, after) {
            (Self::Taken(before), Self::Taken(after)) => {
                let changed: BTreeSet<&PathBuf> = before
                    .keys()
                    .chain(after.keys())
                    .filter(|path| {
                        before.get(*path).copied().flatten() != after.get(*path).copied().flatten()
                    })
                    .collect();
                if changed.is_empty() {
                    WorkspaceDrift::Held
                } else {
                    WorkspaceDrift::Changed {
                        count: changed.len() as u64,
                        paths: changed
                            .iter()
                            .take(NAMED_PATHS)
                            .map(|path| path.to_string_lossy().into_owned())
                            .collect(),
                    }
                }
            }
            (Self::Missing(reason), _) | (Self::Taken(_), Self::Missing(reason)) => {
                WorkspaceDrift::Unknown {
                    reason: reason.clone(),
                }
            }
        }
    }
}

/// The not ignored paths under `dir`, or why there are none: past
/// [`MAX_WORKSPACE_FILES`] the walk stops.
fn bounded_walk(dir: &Path) -> Result<BTreeSet<PathBuf>, String> {
    let paths = files::walked(dir, Listing::NotIgnored, Vec::new())
        .take(MAX_WORKSPACE_FILES + 1)
        .collect::<io::Result<BTreeSet<PathBuf>>>()
        .map_err(|error| format!("{} cannot be listed: {error}", dir.display()))?;
    if paths.len() > MAX_WORKSPACE_FILES {
        return Err(format!(
            "{} holds more than {MAX_WORKSPACE_FILES} files",
            dir.display()
        ));
    }
    Ok(paths)
}

/// The stamp of `paths` under `dir`, `.eukhe` left out.
fn stats(dir: &Path, paths: BTreeSet<PathBuf>) -> TreeStamp {
    let mut stamp = BTreeMap::new();
    for path in paths {
        if path.starts_with(EUKHE_DIR) {
            continue;
        }
        let stat = match fs::symlink_metadata(dir.join(&path)) {
            Ok(meta) => Some(Stat::of(&meta)),
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                ) =>
            {
                None
            }
            Err(error) => {
                return TreeStamp::Missing(format!("{} cannot be read: {error}", path.display()))
            }
        };
        stamp.insert(path, stat);
    }
    TreeStamp::Taken(stamp)
}

/// Whether a workspace's files changed while a check or a job ran.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", tag = "kind")]
pub enum WorkspaceDrift {
    /// No listed path changed: the result judged the tree as it stands.
    Held,
    /// `count` paths changed (by the run itself or by another writer);
    /// `paths` names the first of them.
    Changed { count: u64, paths: Vec<String> },
    /// No stamp at the start or the end.
    Unknown { reason: String },
}

impl WorkspaceDrift {
    /// The drift of a record written before drifts were stamped.
    #[must_use]
    pub fn unrecorded() -> Self {
        Self::Unknown {
            reason: "not recorded".to_owned(),
        }
    }

    /// The drift of a run named `what` ("the check", "the job") as the
    /// model reads it; `None` when the workspace held.
    #[must_use]
    pub fn text(&self, what: &str) -> Option<String> {
        match self {
            Self::Held => None,
            Self::Changed { count, paths } => {
                let more = if *count > paths.len() as u64 {
                    ", …"
                } else {
                    ""
                };
                let noun = if *count == 1 { "path" } else { "paths" };
                Some(format!(
                    "The workspace changed while {what} ran ({count} {noun}: {}{more}): its result judged no single tree state.",
                    paths.join(", ")
                ))
            }
            Self::Unknown { reason } => Some(format!(
                "Whether the workspace changed while {what} ran is unknown: {reason}."
            )),
        }
    }
}
