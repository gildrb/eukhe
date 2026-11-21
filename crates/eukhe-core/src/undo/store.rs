//! The git IO of the snapshots: one shadow git dir per session
//! (`<work root>/snapshots/<session id>.git`) whose work tree is the
//! workspace. A snapshot is a tree, kept by ref
//! (`refs/eukhe/turns/<turn>`, the session's first under
//! `refs/eukhe/base/<turn>`), with the paths it held back as a blob
//! (`refs/eukhe/held/<turn>`) and the root run it starts as a plain file
//! `runs/<turn>`. A turn whose snapshot failed is a plain
//! file `lost/<turn>` holding why (no git needed to write it), and a store
//! that could not even be read at a turn start has `lost/unread`: the turn
//! still counts, so `/undo` never takes back two turns at once. The
//! workspace's `.gitignore` files and `.git/info/exclude` apply; `.git`
//! and `.eukhe` are never taken.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Stdio;

use eukhe_bend::rules::undo::Snapshots;
use tokio::io::AsyncWriteExt;

use super::UndoError;
use crate::workspace_snapshot::git::git_command;

/// A file above this size is held back: not snapshotted, never touched.
pub(crate) const FILE_CAP_BYTES: u64 = 16 * 1024 * 1024;

/// A workspace with more files than this is not snapshotted.
pub(crate) const MAX_FILES: usize = 200_000;

const TURNS: &str = "refs/eukhe/turns/";
const BASE: &str = "refs/eukhe/base/";
const HELD: &str = "refs/eukhe/held/";

/// The directory, in the shadow git dir, of the turns whose snapshot
/// failed.
const LOST: &str = "lost";

/// The file, in [`LOST`], of a store that a turn start could not read.
const UNREAD: &str = "unread";

/// The directory, in the shadow git dir, of the root run each turn
/// starts (its number, in decimal).
const RUNS: &str = "runs";

/// What the store holds: the snapshots, and why each turn that has none
/// lacks it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Loaded {
    pub state: Snapshots,
    pub lost: BTreeMap<u64, String>,
}

/// The excludes every snapshot adds to the workspace's own.
const OWN_EXCLUDES: &str = ".git\n.eukhe\n";

/// A tree of the workspace and the paths it held back (over the size cap,
/// nested repositories as `dir/`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Taken {
    pub tree: String,
    pub held: BTreeSet<String>,
}

/// One path's entry in a tree: its mode and object.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Blob {
    pub mode: String,
    pub oid: String,
}

/// A path that differs between two trees.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Change {
    pub path: String,
    pub before: Option<Blob>,
    pub now: Option<Blob>,
}

/// The shadow git dir of one session and its workspace.
#[derive(Debug, Clone)]
pub(crate) struct Store {
    git_dir: PathBuf,
    workspace: PathBuf,
    /// The exclude lines of this store: [`OWN_EXCLUDES`], then each of
    /// eukhe's own directories that lies in the workspace.
    excludes: String,
}

impl Store {
    /// The store in `git_dir` of `workspace`, never taking `state` (eukhe's
    /// own directories: the agent dir, the work root) where they lie in it.
    pub(crate) fn new(git_dir: PathBuf, workspace: PathBuf, state: &[PathBuf]) -> Self {
        let excludes = std::iter::once(OWN_EXCLUDES.to_owned())
            .chain(
                state
                    .iter()
                    .filter_map(|dir| dir.strip_prefix(&workspace).ok())
                    .filter(|rel| !rel.as_os_str().is_empty())
                    .map(|rel| format!("/{}/\n", rel.display())),
            )
            .collect();
        Self {
            git_dir,
            workspace,
            excludes,
        }
    }

    pub(crate) fn workspace(&self) -> &Path {
        &self.workspace
    }

    /// `git args` on the shadow git dir and the workspace, every path
    /// taken literally.
    async fn git(&self, args: &[&str], input: Option<Vec<u8>>) -> Result<Vec<u8>, UndoError> {
        self.git_with(&["--literal-pathspecs"], args, input).await
    }

    /// `git flags args` on the shadow git dir and the workspace.
    async fn git_with(
        &self,
        flags: &[&str],
        args: &[&str],
        input: Option<Vec<u8>>,
    ) -> Result<Vec<u8>, UndoError> {
        let git_dir = format!("--git-dir={}", self.git_dir.display());
        let work_tree = format!("--work-tree={}", self.workspace.display());
        let mut all = vec![git_dir.as_str(), work_tree.as_str()];
        all.extend_from_slice(flags);
        all.extend_from_slice(args);
        run(git_command(&all, &self.workspace), args, input).await
    }

    /// Create the shadow git dir (private) when it is missing.
    async fn ensure(&self) -> Result<(), UndoError> {
        if self.git_dir.join("HEAD").is_file() {
            return Ok(());
        }
        if let Some(parent) = self.git_dir.parent() {
            crate::platform::perms::create_dir_all_private(parent)?;
        }
        let dir = self.git_dir.display().to_string();
        let parent = self
            .git_dir
            .parent()
            .map_or_else(|| self.workspace.clone(), Path::to_path_buf);
        run(
            git_command(&["init", "-q", "--bare", &dir], &parent),
            &["init"],
            None,
        )
        .await?;
        self.git(&["config", "gc.auto", "0"], None).await?;
        self.git(&["config", "core.autocrlf", "false"], None)
            .await?;
        Ok(())
    }

    /// The shadow repository's excludes: its own, then the workspace's
    /// `.git/info/exclude`.
    fn write_excludes(&self) -> Result<(), UndoError> {
        let workspace_excludes =
            std::fs::read_to_string(self.workspace.join(".git/info/exclude")).unwrap_or_default();
        let info = self.git_dir.join("info");
        std::fs::create_dir_all(&info)?;
        std::fs::write(
            info.join("exclude"),
            format!("{}{workspace_excludes}", self.excludes),
        )?;
        Ok(())
    }

    /// Snapshot the workspace as it is now: its tree and what it held back.
    pub(crate) async fn take(&self) -> Result<Taken, UndoError> {
        self.ensure().await?;
        self.write_excludes()?;
        let listed = self
            .git(
                &[
                    "ls-files",
                    "-z",
                    "--cached",
                    "--others",
                    "--exclude-standard",
                ],
                None,
            )
            .await?;
        let ignored = self
            .git(
                &[
                    "ls-files",
                    "-z",
                    "--cached",
                    "--ignored",
                    "--exclude-standard",
                ],
                None,
            )
            .await?;
        let ignored: BTreeSet<String> = nul_split(&ignored).collect();
        let candidates: BTreeSet<String> = nul_split(&listed).collect();
        if candidates.len() > MAX_FILES {
            return Err(UndoError::TooLarge {
                files: candidates.len(),
            });
        }
        let sorted = sort_candidates(&self.workspace, candidates, &ignored);
        if !sorted.drop.is_empty() {
            self.git(
                &["update-index", "-z", "--force-remove", "--stdin"],
                Some(nul_join(&sorted.drop)),
            )
            .await?;
        }
        if !sorted.keep.is_empty() {
            self.git(
                &["update-index", "-z", "--add", "--remove", "--stdin"],
                Some(nul_join(&sorted.keep)),
            )
            .await?;
        }
        let tree = text(&self.git(&["write-tree"], None).await?);
        Ok(Taken {
            tree,
            held: sorted.held,
        })
    }

    /// Keep `taken` as the snapshot of `turn`.
    pub(crate) async fn keep(&self, turn: u64, taken: &Taken) -> Result<(), UndoError> {
        let held = text(
            &self
                .git(
                    &["hash-object", "-w", "--stdin"],
                    Some(nul_join(&taken.held)),
                )
                .await?,
        );
        self.update_ref(&format!("{HELD}{turn}"), &held).await?;
        self.update_ref(&format!("{TURNS}{turn}"), &taken.tree)
            .await
    }

    /// Keep the snapshot of `turn` as the session's first.
    pub(crate) async fn keep_base(&self, turn: u64, tree: &str) -> Result<(), UndoError> {
        self.update_ref(&format!("{BASE}{turn}"), tree).await
    }

    async fn update_ref(&self, name: &str, oid: &str) -> Result<(), UndoError> {
        self.git(&["update-ref", name, oid], None).await.map(drop)
    }

    /// The snapshots the refs and the lost turns hold: the live turns,
    /// newest first, and the session's first turn. An empty state before
    /// the first turn.
    ///
    /// # Errors
    ///
    /// [`UndoError::Unread`] once a turn start could not read the store;
    /// git or file IO failed.
    pub(crate) async fn load(&self) -> Result<Loaded, UndoError> {
        let lost = self.lost()?;
        let (mut live, mut base) = (Vec::new(), Vec::new());
        if self.git_dir.join("HEAD").is_file() {
            let refs = self
                .git(
                    &["for-each-ref", "--format=%(refname)", "refs/eukhe/"],
                    None,
                )
                .await?;
            let names = String::from_utf8_lossy(&refs).into_owned();
            let turn_of = |prefix: &str| {
                names
                    .lines()
                    .filter_map(|line| line.strip_prefix(prefix))
                    .filter_map(|n| n.parse::<u64>().ok())
                    .collect::<Vec<u64>>()
            };
            live = turn_of(TURNS);
            base = turn_of(BASE);
        }
        // A lost turn is never undone (its /undo is refused), so it is
        // live; the first turn may be one.
        let extra: Vec<u64> = lost
            .keys()
            .copied()
            .filter(|turn| !live.contains(turn))
            .collect();
        live.extend(extra);
        live.sort_unstable_by(|a, b| b.cmp(a));
        Ok(Loaded {
            state: Snapshots {
                live,
                base: base.into_iter().chain(lost.keys().copied()).min(),
            },
            lost,
        })
    }

    /// The turns whose snapshot failed, and why.
    fn lost(&self) -> Result<BTreeMap<u64, String>, UndoError> {
        let dir = self.git_dir.join(LOST);
        let entries = match std::fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                return Ok(BTreeMap::new())
            }
            Err(error) => return Err(error.into()),
        };
        let mut lost = BTreeMap::new();
        for entry in entries {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().into_owned();
            let reason = std::fs::read_to_string(entry.path())?;
            if name == UNREAD {
                return Err(UndoError::Unread { reason });
            }
            if let Ok(turn) = name.parse::<u64>() {
                lost.insert(turn, reason);
            }
        }
        Ok(lost)
    }

    /// Record that the snapshot of `turn` failed with `reason` (`None`: the
    /// store could not be read, so the turn's number is unknown).
    ///
    /// # Errors
    ///
    /// The record cannot be written.
    pub(crate) fn lose(&self, turn: Option<u64>, reason: &str) -> Result<(), UndoError> {
        let dir = self.git_dir.join(LOST);
        crate::platform::perms::create_dir_all_private(&dir)?;
        let name = turn.map_or_else(|| UNREAD.to_owned(), |turn| turn.to_string());
        std::fs::write(dir.join(name), reason)?;
        Ok(())
    }

    /// Record that `turn` starts the root session's run `run`.
    ///
    /// # Errors
    ///
    /// The record cannot be written.
    pub(crate) fn keep_run(&self, turn: u64, run: u64) -> Result<(), UndoError> {
        let dir = self.git_dir.join(RUNS);
        crate::platform::perms::create_dir_all_private(&dir)?;
        std::fs::write(dir.join(turn.to_string()), run.to_string())?;
        Ok(())
    }

    /// The root run `turn` starts; `None` when the store has no record of
    /// it (a snapshot kept before runs were recorded).
    ///
    /// # Errors
    ///
    /// The record cannot be read, or holds no number.
    pub(crate) fn run_of(&self, turn: u64) -> Result<Option<u64>, UndoError> {
        match std::fs::read_to_string(self.git_dir.join(RUNS).join(turn.to_string())) {
            Ok(run) => run.trim().parse::<u64>().map(Some).map_err(|_| {
                UndoError::Io(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("the run record of prompt {turn} holds {run:?}"),
                ))
            }),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error.into()),
        }
    }

    /// Delete the refs and run records of the turns `old` has and `new`
    /// does not.
    pub(crate) async fn forget(&self, old: &Snapshots, new: &Snapshots) -> Result<(), UndoError> {
        for turn in old.live.iter().filter(|turn| !new.live.contains(turn)) {
            self.git(&["update-ref", "-d", &format!("{TURNS}{turn}")], None)
                .await?;
            if new.base != Some(*turn) {
                self.git(&["update-ref", "-d", &format!("{HELD}{turn}")], None)
                    .await?;
            }
            match std::fs::remove_file(self.git_dir.join(RUNS).join(turn.to_string())) {
                Err(error) if error.kind() != std::io::ErrorKind::NotFound => {
                    return Err(error.into())
                }
                Ok(()) | Err(_) => {}
            }
        }
        Ok(())
    }

    /// The tree and held paths of the snapshot of `turn`: a live one, else
    /// the session's first.
    pub(crate) async fn snapshot(&self, turn: u64) -> Result<Taken, UndoError> {
        let tree = match self.resolve(&format!("{TURNS}{turn}")).await {
            Ok(tree) => tree,
            Err(_) => self.resolve(&format!("{BASE}{turn}")).await?,
        };
        let held_oid = self.resolve(&format!("{HELD}{turn}")).await?;
        let held = self.git(&["cat-file", "blob", &held_oid], None).await?;
        Ok(Taken {
            tree,
            held: nul_split(&held).collect(),
        })
    }

    async fn resolve(&self, name: &str) -> Result<String, UndoError> {
        Ok(text(
            &self
                .git(&["rev-parse", "--verify", "--quiet", name], None)
                .await?,
        ))
    }

    /// The paths that differ between the trees `before` and `now`.
    pub(crate) async fn changes(&self, before: &str, now: &str) -> Result<Vec<Change>, UndoError> {
        let out = self
            .git(
                &["diff-tree", "-r", "-z", "--no-renames", before, now],
                None,
            )
            .await?;
        parse_diff_tree(&out)
    }

    /// Which of `paths` the workspace's ignore rules ignore now.
    pub(crate) async fn ignored(&self, paths: &[String]) -> Result<BTreeSet<String>, UndoError> {
        if paths.is_empty() {
            return Ok(BTreeSet::new());
        }
        // check-ignore takes its paths as they are and refuses pathspec
        // magic, so no --literal-pathspecs.
        let out = self
            .git_with(
                &[],
                &["check-ignore", "-z", "--no-index", "--stdin"],
                Some(nul_join(paths)),
            )
            .await;
        match out {
            Ok(out) => Ok(nul_split(&out).collect()),
            // check-ignore exits 1 when it ignores none of them.
            Err(UndoError::Git {
                status: Some(1), ..
            }) => Ok(BTreeSet::new()),
            Err(error) => Err(error),
        }
    }

    /// The unified diff from `before` to `now` over `paths`.
    pub(crate) async fn unified(
        &self,
        before: &str,
        now: &str,
        paths: &[String],
    ) -> Result<String, UndoError> {
        if paths.is_empty() {
            return Ok(String::new());
        }
        let mut args = vec![
            "diff-tree",
            "-p",
            "-r",
            "--no-renames",
            "--no-ext-diff",
            "--no-color",
            before,
            now,
            "--",
        ];
        args.extend(paths.iter().map(String::as_str));
        Ok(String::from_utf8_lossy(&self.git(&args, None).await?).into_owned())
    }

    /// The content of the object `oid`.
    pub(crate) async fn blob(&self, oid: &str) -> Result<Vec<u8>, UndoError> {
        self.git(&["cat-file", "blob", oid], None).await
    }
}

/// The candidates of a snapshot, sorted: the paths it takes, the paths it
/// drops from the index (gone, ignored, held back) and the held ones.
struct Sorted {
    keep: Vec<String>,
    drop: Vec<String>,
    held: BTreeSet<String>,
}

fn sort_candidates(
    workspace: &Path,
    candidates: BTreeSet<String>,
    ignored: &BTreeSet<String>,
) -> Sorted {
    let mut sorted = Sorted {
        keep: Vec::new(),
        drop: Vec::new(),
        held: BTreeSet::new(),
    };
    for path in candidates {
        if path.ends_with('/') {
            // A nested repository: git lists its directory.
            sorted.held.insert(path);
            continue;
        }
        if ignored.contains(&path) {
            sorted.drop.push(path);
            continue;
        }
        match std::fs::symlink_metadata(workspace.join(&path)) {
            Ok(meta) if meta.is_file() && meta.len() > FILE_CAP_BYTES => {
                sorted.drop.push(path.clone());
                sorted.held.insert(path);
            }
            Ok(meta) if meta.is_file() || meta.file_type().is_symlink() => sorted.keep.push(path),
            Ok(_) | Err(_) => sorted.drop.push(path),
        }
    }
    sorted
}

/// Parse `git diff-tree -r -z` records:
/// `:<old mode> <new mode> <old oid> <new oid> <status>\0<path>\0`.
fn parse_diff_tree(out: &[u8]) -> Result<Vec<Change>, UndoError> {
    let mut fields = out.split(|b| *b == 0).filter(|f| !f.is_empty());
    let mut changes = Vec::new();
    while let Some(head) = fields.next() {
        let head = String::from_utf8_lossy(head);
        let path = fields
            .next()
            .map(|p| String::from_utf8_lossy(p).into_owned())
            .ok_or_else(|| UndoError::git("diff-tree record without a path"))?;
        let parts: Vec<&str> = head.trim_start_matches(':').split(' ').collect();
        let [old_mode, new_mode, old_oid, new_oid, _status] = parts.as_slice() else {
            return Err(UndoError::git("unreadable diff-tree record"));
        };
        let blob = |mode: &str, oid: &str| {
            (mode != "000000").then(|| Blob {
                mode: mode.to_owned(),
                oid: oid.to_owned(),
            })
        };
        changes.push(Change {
            path,
            before: blob(old_mode, old_oid),
            now: blob(new_mode, new_oid),
        });
    }
    Ok(changes)
}

fn nul_split(bytes: &[u8]) -> impl Iterator<Item = String> + '_ {
    bytes
        .split(|b| *b == 0)
        .filter(|p| !p.is_empty())
        .map(|p| String::from_utf8_lossy(p).into_owned())
}

fn nul_join<'a>(paths: impl IntoIterator<Item = &'a String>) -> Vec<u8> {
    paths.into_iter().fold(Vec::new(), |mut out, path| {
        out.extend_from_slice(path.as_bytes());
        out.push(0);
        out
    })
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).trim().to_owned()
}

/// Number each distinct blob of `changes` (in order of first use), for the
/// compiled core, which compares blobs by number.
pub(crate) fn blob_numbers(changes: &[Change]) -> BTreeMap<Blob, u64> {
    changes
        .iter()
        .flat_map(|change| change.before.iter().chain(change.now.iter()))
        .fold(BTreeMap::new(), |mut numbers, blob| {
            let next = u64::try_from(numbers.len()).unwrap_or(u64::MAX);
            numbers.entry(blob.clone()).or_insert(next);
            numbers
        })
}

async fn run(
    mut command: tokio::process::Command,
    args: &[&str],
    input: Option<Vec<u8>>,
) -> Result<Vec<u8>, UndoError> {
    command
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true);
    let mut child = command.spawn()?;
    // The input is written beside the reads: a child that answers while it
    // reads (check-ignore) would block on a full pipe otherwise.
    let stdin = child.stdin.take();
    let feed = tokio::spawn(async move {
        if let (Some(mut stdin), Some(input)) = (stdin, input) {
            stdin.write_all(&input).await?;
        }
        Ok::<(), std::io::Error>(())
    });
    let output = child.wait_with_output().await?;
    feed.await
        .map_err(|error| UndoError::git(&format!("git input writer failed: {error}")))??;
    if !output.status.success() {
        return Err(UndoError::Git {
            detail: format!(
                "git {}: {}",
                args.first().copied().unwrap_or_default(),
                String::from_utf8_lossy(&output.stderr).trim()
            ),
            status: output.status.code(),
        });
    }
    Ok(output.stdout)
}
