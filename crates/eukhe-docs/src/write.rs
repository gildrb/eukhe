//! Locked, atomic writes. Every write lands on the target's real path
//! (symlinks followed) and runs only after the host's [`AccessGate`]
//! let it. A writer then takes an OS lock on
//! `<lock dir>/<xxh64 of the real path>.lock` (shared by every session
//! and process of one eukhe home), and replaces the file through a
//! same-directory temporary file: write, fsync, re-read the target, rename,
//! fsync the directory. Another program may change the target with no path
//! lock: the re-read just before the rename sees it, and the change is
//! rebased onto those bytes or refused, never written over them. A
//! replaced file keeps its mode; a created file gets the default mode (no
//! execute bit).
//!
//! A temporary file is named `.eukhe-tmp-<xxh64 of the target name>-<pid>-<n>`
//! (a fixed length, so a long target name still fits) and its writer holds
//! an OS lock on it while it lives. Each write of a target first removes the
//! target's temporary files whose lock it can take: a crash left them.
//!
//! Every choice (the check of an edit, what a publish did, the step after
//! a publish's re-read, the write tool's base, the temporary files' prefix
//! and which a sweep removes) runs as the compiled Bend core
//! ([`crate::commit`], [`eukhe_bend::rules::doc_publish`]); this module
//! locks, reads, compares, publishes and removes.

use std::fs::{File, OpenOptions, Permissions};
use std::io::Write as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use eukhe_bend::rules::doc_publish::{self, Seen, Step};
use eukhe_types::path_policy::{real_path, resolve};
use twox_hash::XxHash64;

use crate::error::EditError;
use crate::gate::{Access, AccessGate, AccessRefusal};
use crate::hashline::{Basis, EditWriter, Published, WriteOp, WriteRequest as EditWriteRequest};
use crate::store::EditStore;
use crate::text::{self, encoding_name, LineEnding, Projection, BOM};

/// An exclusive lock on one canonical path; released on drop.
#[derive(Debug)]
pub(crate) struct PathLock {
    _file: File,
}

/// Block until this process holds the lock of `canonical`.
pub(crate) fn lock(lock_dir: &Path, canonical: &Path) -> std::io::Result<PathLock> {
    std::fs::create_dir_all(lock_dir)?;
    let key = XxHash64::oneshot(0, canonical.as_os_str().as_encoded_bytes());
    let file = OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(lock_dir.join(format!("{key:016x}.lock")))?;
    file.lock()?;
    Ok(PathLock { _file: file })
}

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

/// The digest of `target`'s file name, which names its temporary files.
fn name_digest(target: &Path) -> String {
    let name = target
        .file_name()
        .map_or(&[][..], |name| name.as_encoded_bytes());
    format!("{:016x}", XxHash64::oneshot(0, name))
}

/// The name prefix of the temporary files of `target` (the core's
/// [`crate::commit::prefix`]).
#[cfg(test)]
pub(crate) fn temp_prefix(target: &Path) -> String {
    crate::commit::prefix(&name_digest(target))
}

/// Remove the temporary files of the target whose file name has the digest
/// `digest` that no live writer holds, as the core's sweep chooses. The
/// caller holds the path lock of the target. Rust lists only the entries
/// whose names start with `prefix` (the core's prefix: a lock is probed
/// only by opening the file) and probes their locks; the core chooses
/// which of them go.
fn sweep_temps(directory: &Path, digest: &str, prefix: &str) {
    // The sweep only cleans up: a directory it cannot list, or a file it
    // cannot open or remove, stays for a later sweep.
    let Ok(entries) = std::fs::read_dir(directory) else {
        return;
    };
    let mut probed = Vec::new();
    for entry in entries.flatten() {
        let name = entry.file_name();
        if !name.as_encoded_bytes().starts_with(prefix.as_bytes()) {
            continue;
        }
        let path = entry.path();
        let Ok(file) = File::open(&path) else {
            continue;
        };
        // A lock taken here is kept until the removal (the handle lives).
        let held = file.try_lock().is_err();
        probed.push((name.to_string_lossy().into_owned(), held, path, file));
    }
    let facts: Vec<(String, bool)> = probed
        .iter()
        .map(|(name, held, _, _)| (name.clone(), *held))
        .collect();
    for at in crate::commit::gone(digest, &facts) {
        let _left_for_a_later_sweep = std::fs::remove_file(&probed[at].2);
    }
}

/// A point of a publish where a test can make it fail.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Stage {
    /// The temporary file is written and synced; the target is not changed.
    BeforeRename,
    /// The target holds the new bytes; the directory is not synced.
    AfterRename,
    /// A move wrote its destination; the source is not removed.
    RemoveSource,
}

/// Failures a publish meets at each [`Stage`]. Production uses
/// [`NoFaults`]; a test returns an error at a chosen stage to see what the
/// writer then reports. An implementation returns `Ok(())` to let the
/// stage run and an error to fail it, and has no other effect.
pub(crate) trait Faults: Sync {
    /// The failure of `stage` of the publish of `target`, if any.
    fn inject(&self, target: &Path, stage: Stage) -> std::io::Result<()>;
}

/// The production [`Faults`]: no stage fails.
pub(crate) struct NoFaults;

impl Faults for NoFaults {
    fn inject(&self, _target: &Path, _stage: Stage) -> std::io::Result<()> {
        Ok(())
    }
}

/// One change a write is about to make to a file: its real path goes
/// from `base` to `next` (`None`: no file there).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Change<'a> {
    pub real: &'a Path,
    pub base: Option<&'a [u8]>,
    pub next: Option<&'a [u8]>,
}

/// The host's record of what a write is about to change, so that after a
/// crash it can tell whether the change landed: a file write as an
/// exactly-once effect (`eukhe_bend::rules::once`).
///
/// A write calls [`Witness::changing`] under its path locks, after its
/// checks and before any file can change: once with every change of the
/// call, then once more for each rebase, with the change it makes of that
/// file instead (`base`: the bytes another program wrote, `next`: the
/// rebased bytes). An implementation returns once its record is durable;
/// an error fails the write, and no file the call had not changed yet
/// changes.
pub trait Witness: Sync {
    /// Record `changes` before any of them happens.
    ///
    /// # Errors
    ///
    /// The record could not be made durable.
    fn changing(&self, changes: &[Change<'_>]) -> std::io::Result<()>;
}

/// The [`Witness`] of writes nobody tells apart after a crash (a kernel's
/// `fs.*` request, an LSP rename): it records nothing.
pub struct Unwitnessed;

impl Witness for Unwitnessed {
    fn changing(&self, _changes: &[Change<'_>]) -> std::io::Result<()> {
        Ok(())
    }
}

/// How a publish may treat a file at the target.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Publish<'a> {
    /// Replace it, only while it holds `base`: the bytes the new ones were
    /// made from. Over other bytes (another program wrote them, with no
    /// path lock) the change is rebased onto them and checked again, or
    /// refused ([`PublishError::Changed`]): the compiled core's step
    /// (`bend/doc_publish.bend`).
    Replace { base: &'a [u8] },
    /// Never replace it: a target that exists fails with
    /// [`std::io::ErrorKind::AlreadyExists`] and is not changed.
    Create,
}

/// A publish whose bytes are at the target.
#[derive(Debug)]
pub(crate) struct Placed {
    /// The text at the target when the change was rebased onto bytes
    /// another program wrote meanwhile; `None`: the given bytes.
    pub(crate) rebased: Option<String>,
    /// Why the directory sync failed: the new name may not survive a crash.
    pub(crate) unsynced: Option<std::io::Error>,
}

/// Why a publish left the target as it was.
#[derive(Debug, thiserror::Error)]
pub(crate) enum PublishError {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    /// Another program changed the target, and the change could not be
    /// carried onto its bytes (they are gone, the rebase was refused, or
    /// the rebases ran out).
    #[error("the file changed on disk while it was being written")]
    Changed,
}

/// What became of a temporary file once its publish looked at the target.
enum Staged<T> {
    /// It is at the target.
    Placed,
    /// It was removed; the target is as it was.
    Dropped(T),
}

/// Why a replace dropped its temporary file.
enum Retry {
    /// The target holds these bytes, not the base: rebase onto them.
    Rebase(Vec<u8>),
    /// Leave the target as it is.
    Refuse,
}

/// Put `bytes` at `target` atomically; `permissions` applies to the new
/// file from its creation (the replaced file's mode; `None`: the default
/// mode). A replace re-reads the target after the new bytes are synced,
/// just before the rename, and renames only over its base; over other
/// bytes it rebases the change onto them and tries again, as the core's
/// step chooses: a publish never replaces bytes it did not read. The
/// caller told `witness` of the change; each rebase tells it the change it
/// makes instead before that can land. An error means the target did not
/// change.
pub(crate) fn publish(
    target: &Path,
    bytes: &[u8],
    permissions: Option<Permissions>,
    mode: Publish<'_>,
    witness: &dyn Witness,
    faults: &dyn Faults,
) -> Result<Placed, PublishError> {
    let directory = target.parent().unwrap_or(Path::new("."));
    let digest = name_digest(target);
    let prefix = crate::commit::prefix(&digest);
    sweep_temps(directory, &digest, &prefix);
    let temps = Temps {
        directory,
        prefix: &prefix,
        target,
        permissions,
        faults,
    };
    let rebased = match mode {
        Publish::Create => {
            match temps.stage(bytes, |temp| {
                place_new(temp, target).map(|()| Staged::<std::convert::Infallible>::Placed)
            })? {
                Staged::Placed => None,
                Staged::Dropped(never) => match never {},
            }
        }
        Publish::Replace { base } => {
            // The bytes the staged text was rebased onto, and that text.
            let mut restaged: Option<(Vec<u8>, String)> = None;
            let mut rebases = 0;
            loop {
                let (base, staged) = match &restaged {
                    Some((head, text)) => (head.as_slice(), text.as_bytes()),
                    None => (base, bytes),
                };
                let staged_at = temps.stage(staged, |temp| {
                    let (seen, head) = match std::fs::read(target) {
                        Ok(head) if head == base => (Seen::Same, None),
                        Ok(head) => (Seen::Moved, Some(head)),
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                            (Seen::Gone, None)
                        }
                        Err(error) => return Err(error),
                    };
                    match (doc_publish::step(rebases, seen), head) {
                        (Step::Place, _) => std::fs::rename(temp, target).map(|()| Staged::Placed),
                        (Step::Rebase, Some(head)) => Ok(Staged::Dropped(Retry::Rebase(head))),
                        (Step::Rebase, None) => {
                            crate::commit::inconsistent("a rebase onto other bytes")
                        }
                        (Step::Refuse, _) => Ok(Staged::Dropped(Retry::Refuse)),
                    }
                })?;
                let head = match staged_at {
                    Staged::Placed => break restaged.map(|(_, text)| text),
                    Staged::Dropped(Retry::Rebase(head)) => head,
                    Staged::Dropped(Retry::Refuse) => return Err(PublishError::Changed),
                };
                // Only text rebases: bytes that are not UTF-8 refuse the file.
                let text = match (
                    std::str::from_utf8(base),
                    std::str::from_utf8(&head),
                    std::str::from_utf8(staged),
                ) {
                    (Ok(base), Ok(theirs), Ok(ours)) => {
                        crate::rebase::rebase_content(base, theirs, ours)
                            .map_err(|_conflict| PublishError::Changed)?
                    }
                    (Err(_), _, _) | (_, Err(_), _) | (_, _, Err(_)) => {
                        return Err(PublishError::Changed)
                    }
                };
                witness.changing(&[Change {
                    real: target,
                    base: Some(head.as_slice()),
                    next: Some(text.as_bytes()),
                }])?;
                restaged = Some((head, text));
                rebases += 1;
            }
        }
    };
    let unsynced = faults
        .inject(target, Stage::AfterRename)
        .and_then(|()| File::open(directory)?.sync_all())
        .err();
    Ok(Placed { rebased, unsynced })
}

/// The temporary files of one publish of `target`.
struct Temps<'a> {
    directory: &'a Path,
    prefix: &'a str,
    target: &'a Path,
    permissions: Option<Permissions>,
    faults: &'a dyn Faults,
}

impl Temps<'_> {
    /// Write and sync `bytes` to a new temporary file, then let `then`
    /// place it while its lock is held; a temporary file not placed is
    /// removed.
    fn stage<T>(
        &self,
        bytes: &[u8],
        then: impl FnOnce(&Path) -> std::io::Result<Staged<T>>,
    ) -> std::io::Result<Staged<T>> {
        let temp = self.directory.join(format!(
            "{}{}-{}",
            self.prefix,
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        let staged = write_synced(&temp, bytes, self.permissions.clone()).and_then(|_held| {
            self.faults.inject(self.target, Stage::BeforeRename)?;
            then(&temp)
        });
        match &staged {
            Ok(Staged::Placed) => {}
            // The temporary file may not exist; the write error is the one
            // to report.
            Ok(Staged::Dropped(_)) | Err(_) => {
                let _cleanup = std::fs::remove_file(&temp);
            }
        }
        staged
    }
}

/// Give `temp` the name `target` only when `target` does not exist: a hard
/// link fails on an existing name, so no check can go stale. A file system
/// without hard links gets a check under the path lock, then a rename.
fn place_new(temp: &Path, target: &Path) -> std::io::Result<()> {
    match std::fs::hard_link(temp, target) {
        Ok(()) => {
            // The target holds the bytes; a temporary name left here is
            // unlocked once its writer is done, and the next write of this
            // target sweeps it.
            let _swept_later = std::fs::remove_file(temp);
            Ok(())
        }
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => Err(error),
        Err(_) => match std::fs::symlink_metadata(target) {
            Ok(_) => Err(std::io::Error::from(std::io::ErrorKind::AlreadyExists)),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                std::fs::rename(temp, target)
            }
            Err(error) => Err(error),
        },
    }
}

/// Create `path` with `bytes` and sync it; the returned handle holds the
/// file's lock, which tells a sweep that its writer lives.
fn write_synced(
    path: &Path,
    bytes: &[u8],
    permissions: Option<Permissions>,
) -> std::io::Result<File> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    if let Some(permissions) = &permissions {
        // The mode applies at creation: no window where the bytes are
        // readable under a wider mode.
        options.mode(permissions.mode());
    }
    let mut file = options.open(path)?;
    file.lock()?;
    file.write_all(bytes)?;
    if let Some(permissions) = permissions {
        // The umask may have narrowed the creation mode.
        file.set_permissions(permissions)?;
    }
    file.sync_all()?;
    Ok(file)
}

/// Why a write failed.
#[derive(Debug, thiserror::Error)]
pub enum WriteError {
    #[error("Cannot write {display}: it is a directory.")]
    IsDirectory { display: String },
    #[error("Cannot write {display}: it changed on disk since it was read. Nothing was written; re-read it and retry.")]
    Changed { display: String },
    #[error("Cannot write {display}: this session has not read its current contents (a shell view such as cat does not count). Nothing was written; call read(\"{display}\"), then send this write again.")]
    Unseen { display: String },
    #[error("Did not write {display}: {reason}")]
    Refused {
        display: String,
        #[source]
        reason: WriteRefusal,
    },
    #[error("Cannot write {display}: {source}")]
    Io {
        display: String,
        #[source]
        source: std::io::Error,
    },
}

/// Why a write did not happen before it touched the file.
#[derive(Debug, thiserror::Error)]
pub enum WriteRefusal {
    /// The host's gate refused it.
    #[error(transparent)]
    Gate(#[from] AccessRefusal),
    /// The real path changed between the gate and the path lock (a link
    /// was made or moved meanwhile).
    #[error("its real path changed while the write waited (a symlink was made or moved). Nothing was written; retry.")]
    Moved,
}

/// Whether a write created or replaced its target.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WriteDisposition {
    Created,
    Overwrote,
}

/// A committed whole-file write.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WriteOutcome {
    pub path: String,
    pub absolute: PathBuf,
    pub disposition: WriteDisposition,
    /// Bytes persisted.
    pub bytes: usize,
    /// The new file tag; `None` when the file is too large to snapshot.
    pub tag: Option<String>,
    /// What the write changed that the content did not ask for, and a
    /// directory sync that failed after the bytes landed.
    pub warnings: Vec<String>,
    /// `[path#TAG]`, the confirmation line, and the warnings.
    pub rendered: String,
}

/// What a write expects to replace.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Base<'a> {
    /// No file, or bytes the session saw ([`EditStore::saw_bytes`]);
    /// anything else is [`WriteError::Unseen`].
    Seen,
    /// Exactly these bytes; anything else (or no file) is
    /// [`WriteError::Changed`].
    Bytes(&'a [u8]),
}

/// The file's permissions when its current bytes are `expected`; `None`
/// when they differ.
fn permissions_if_unchanged(
    canonical: &Path,
    expected: &[u8],
) -> std::io::Result<Option<Permissions>> {
    let current = std::fs::read(canonical)?;
    if current != expected {
        return Ok(None);
    }
    Ok(Some(std::fs::metadata(canonical)?.permissions()))
}

fn ending_name(ending: LineEnding) -> &'static str {
    match ending {
        LineEnding::Lf => "LF",
        LineEnding::CrLf => "CRLF",
    }
}

/// Create or overwrite `absolute` with `content` under its path lock, when
/// its current bytes are `base`, after `gate` let the write of its real
/// path and `witness` recorded the change.
///
/// A replaced file keeps its BOM, line endings, and mode, with a warning
/// when the content had other endings or the file was not UTF-8; a created
/// file gets `content` as given and the default mode (no execute bit).
/// The written text is recorded in `store` with every line seen.
#[allow(
    clippy::too_many_lines,
    clippy::too_many_arguments,
    reason = "one sequence under one path lock: check the base, encode, witness, publish, record"
)]
pub(crate) fn write_file(
    store: &EditStore,
    lock_dir: &Path,
    gate: &dyn AccessGate,
    witness: &dyn Witness,
    absolute: &Path,
    display: &str,
    content: &str,
    base: Base<'_>,
) -> Result<WriteOutcome, WriteError> {
    let io = |source| WriteError::Io {
        display: display.to_owned(),
        source,
    };
    let refused = |reason| WriteError::Refused {
        display: display.to_owned(),
        reason,
    };
    let resolved = resolve(absolute);
    gate.check(Access::Write, &resolved, display)
        .map_err(|refusal| refused(WriteRefusal::Gate(refusal)))?;
    let canonical = resolved.into_path();
    let _lock = lock(lock_dir, &canonical).map_err(io)?;
    if real_path(absolute) != canonical {
        return Err(refused(WriteRefusal::Moved));
    }
    let existing = match std::fs::metadata(&canonical) {
        Ok(metadata) if metadata.is_dir() => {
            return Err(WriteError::IsDirectory {
                display: display.to_owned(),
            })
        }
        Ok(metadata) => Some((
            std::fs::read(&canonical).map_err(io)?,
            metadata.permissions(),
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => return Err(io(error)),
    };
    let changed = || WriteError::Changed {
        display: display.to_owned(),
    };
    let unseen = || WriteError::Unseen {
        display: display.to_owned(),
    };
    let seen = store.seen_digests(&canonical);
    let digest = existing
        .as_ref()
        .map(|(bytes, _)| crate::store::digest(bytes));
    let disk = match (&existing, &digest) {
        (Some((bytes, _)), Some(digest)) => crate::commit::Disk::Present {
            digest,
            expected: matches!(base, Base::Bytes(expected) if bytes.as_slice() == expected),
        },
        (None, _) | (_, None) => crate::commit::Disk::Absent,
    };
    let on = match base {
        Base::Seen => crate::commit::Base::OnSeen(&seen),
        Base::Bytes(_) => crate::commit::Base::OnBytes,
    };
    match crate::commit::gate(&on, &disk) {
        crate::commit::Gate::Proceed => {}
        crate::commit::Gate::Unseen => return Err(unseen()),
        crate::commit::Gate::Stale => return Err(changed()),
    }
    let mut warnings = Vec::new();
    let (persisted, permissions, disposition, mode) = if let Some((bytes, permissions)) = &existing
    {
        let previous = String::from_utf8_lossy(bytes);
        if std::str::from_utf8(bytes).is_err() {
            warnings.push(format!(
                "{display} was {}; it is now UTF-8.",
                encoding_name(bytes)
            ));
        }
        let asked = Projection::of(content);
        let kept = text::kept(&Projection::of(&previous), &asked);
        if kept.warn {
            // A warning means the content's first ending is the other one.
            let had = match kept.sep {
                LineEnding::Lf => LineEnding::CrLf,
                LineEnding::CrLf => LineEnding::Lf,
            };
            warnings.push(format!(
                "{display} keeps its {} line endings; the content had {}.",
                ending_name(kept.sep),
                ending_name(had)
            ));
        }
        let mut persisted = String::with_capacity(content.len() + 3);
        if kept.bom {
            persisted.push_str(BOM);
        }
        for (at, line) in asked.lines.iter().enumerate() {
            if at > 0 {
                persisted.push_str(kept.sep.as_str());
            }
            persisted.push_str(line.text);
        }
        (
            persisted,
            Some(permissions.clone()),
            WriteDisposition::Overwrote,
            Publish::Replace { base: bytes },
        )
    } else {
        if let Some(parent) = canonical.parent() {
            std::fs::create_dir_all(parent).map_err(io)?;
        }
        (
            content.to_owned(),
            None,
            WriteDisposition::Created,
            Publish::Create,
        )
    };
    witness
        .changing(&[Change {
            real: &canonical,
            base: existing.as_ref().map(|(bytes, _)| bytes.as_slice()),
            next: Some(persisted.as_bytes()),
        }])
        .map_err(io)?;
    let placed = publish(
        &canonical,
        persisted.as_bytes(),
        permissions,
        mode,
        witness,
        &NoFaults,
    )
    .map_err(|error| match error {
        PublishError::Io(error) => match error.kind() {
            // Another program created the file after the check.
            std::io::ErrorKind::AlreadyExists => unseen(),
            _ => io(error),
        },
        PublishError::Changed => changed(),
    })?;
    let landed = crate::commit::outcome(crate::commit::Pub::Updated(crate::commit::Placed::Yes {
        synced: placed.unsynced.is_none(),
    }));
    if let (crate::commit::Outcome::Lands(crate::commit::Warn::Sync), Some(error)) =
        (landed, &placed.unsynced)
    {
        warnings.push(format!(
            "{display} was written, but its directory sync failed: {error}"
        ));
    }
    let (sent, persisted) = if let Some(text) = placed.rebased {
        warnings.push(rebased_warning(display));
        (Some(persisted), text)
    } else {
        store.saw_bytes(&canonical, persisted.as_bytes());
        (None, persisted)
    };
    let projection = Projection::of(&persisted);
    let text = projection.lf_text();
    let tag = (persisted.len() as u64 <= crate::store::MAX_SNAPSHOT_FILE_BYTES).then(|| {
        // Every line the write sent is seen; a line another program wrote
        // meanwhile (a rebased write) is not, and the write tool may not
        // replace those bytes.
        let seen: Vec<u32> = match &sent {
            None => {
                let line_count = crate::read::line_count(&projection);
                (1..=u32::try_from(line_count).unwrap_or(u32::MAX)).collect()
            }
            Some(sent) => crate::hashline::carry_seen(
                &Projection::of(sent).lf_text(),
                &text,
                |_| true,
                crate::hashline::Added::Unseen,
            ),
        };
        store.reset_noop(&canonical);
        store.record(&canonical, &text, Some(&seen))
    });
    let confirmation = format!("Successfully wrote {} bytes to {display}", persisted.len());
    let mut rendered = match &tag {
        Some(tag) => format!("[{display}#{tag}]\n{confirmation}"),
        None => confirmation,
    };
    if !warnings.is_empty() {
        rendered = format!("{rendered}\n\nWarnings:\n{}", warnings.join("\n"));
    }
    Ok(WriteOutcome {
        path: display.to_owned(),
        absolute: absolute.to_path_buf(),
        disposition,
        bytes: persisted.len(),
        tag,
        warnings,
        rendered,
    })
}

/// The [`EditWriter`] of a session: a call lets `gate` check each real
/// path it changes, takes the path locks of every file it touches, checks
/// each file's current bytes against the bytes the edit was applied to
/// (and that each move destination is free), tells `witness` every change,
/// and only then replaces the files atomically (mode kept), in order. Each
/// replace re-reads its file just before the rename ([`publish`]): bytes
/// another program wrote since the check are rebased onto, or the file is
/// not written.
pub(crate) struct LockedWriter<'a> {
    pub(crate) lock_dir: &'a Path,
    pub(crate) gate: &'a dyn AccessGate,
    pub(crate) witness: &'a dyn Witness,
    pub(crate) faults: &'a dyn Faults,
}

/// The real paths of one request that the gate let: its source and, for a
/// move, its destination.
struct Allowed {
    source: PathBuf,
    target: Option<PathBuf>,
}

impl LockedWriter<'_> {
    /// Let the gate check the write of `absolute` (shown as `display`);
    /// its real path.
    fn allow(&self, absolute: &Path, display: &str) -> Result<PathBuf, EditError> {
        let real = resolve(absolute);
        self.gate
            .check(Access::Write, &real, display)
            .map_err(|refusal| EditError::Refused {
                display: display.to_owned(),
                reason: WriteRefusal::Gate(refusal),
            })?;
        Ok(real.into_path())
    }

    /// Lock every path of `pairs` (each the written path, its real path at
    /// the gate, and its display), then fail if a real path changed
    /// meanwhile.
    fn lock_all(&self, pairs: &[(&Path, &Path, &str)]) -> Result<Vec<PathLock>, EditError> {
        let mut keys: Vec<(&Path, &str)> = pairs
            .iter()
            .map(|(_, real, display)| (*real, *display))
            .collect();
        // One global order keeps two writers of the same files from deadlocking.
        keys.sort_unstable_by_key(|(real, _)| *real);
        keys.dedup_by_key(|(real, _)| *real);
        let locks = keys
            .into_iter()
            .map(|(key, display)| {
                lock(self.lock_dir, key).map_err(|source| io_error(display, key, source))
            })
            .collect::<Result<Vec<_>, _>>()?;
        match pairs
            .iter()
            .find(|(absolute, real, _)| real_path(absolute) != *real)
        {
            Some((_, _, display)) => Err(EditError::Refused {
                display: (*display).to_owned(),
                reason: WriteRefusal::Moved,
            }),
            None => Ok(locks),
        }
    }

    /// Phase 2 of one request: publish it; its real paths are `allowed`,
    /// locked and checked, and `permissions` are the source file's. What
    /// the publish did is the core's choice ([`crate::commit::outcome`]).
    #[allow(
        clippy::too_many_lines,
        reason = "one publish in order: place, remove the source, the core's outcome"
    )]
    fn publish(
        &self,
        request: &EditWriteRequest<'_>,
        allowed: &Allowed,
        permissions: Permissions,
    ) -> Published {
        use crate::commit::{outcome, Outcome, Placed as Spot, Pub, Warn};
        let source = &allowed.source;
        let display = request.display;
        let spot = |placed: &Option<Placed>| match placed {
            Some(placed) => Spot::Yes {
                synced: placed.unsynced.is_none(),
            },
            None => Spot::No,
        };
        let mut failure = None;
        let mut remove_warning = None;
        let (facts, written, placed) = match request.op {
            WriteOp::Update {
                before_raw,
                content,
            } => {
                let placed = match publish(
                    source,
                    content.as_bytes(),
                    Some(permissions),
                    Publish::Replace {
                        base: before_raw.as_bytes(),
                    },
                    self.witness,
                    self.faults,
                ) {
                    Ok(placed) => Some(placed),
                    Err(PublishError::Io(error)) => {
                        failure = Some(io_error(display, source, error));
                        None
                    }
                    Err(PublishError::Changed) => {
                        failure = Some(EditError::apply(format!(
                            "Edit not applied to {display}: another program changed it while \
                             the edit was being written, and the edit could not be rebased \
                             onto its new bytes. {display} keeps them; re-read it and retry."
                        )));
                        None
                    }
                };
                (Pub::Updated(spot(&placed)), content, placed)
            }
            WriteOp::Delete { .. } => {
                let removed = match std::fs::remove_file(source) {
                    Ok(()) => true,
                    Err(error) => {
                        failure = Some(io_error(display, source, error));
                        false
                    }
                };
                (Pub::Deleted { removed }, "", None)
            }
            WriteOp::Move {
                destination,
                destination_display,
                content,
                ..
            } => {
                let target = allowed
                    .target
                    .clone()
                    .unwrap_or_else(|| real_path(destination));
                let parent = target
                    .parent()
                    .map(|parent| (parent, std::fs::create_dir_all(parent)));
                let placed = match parent {
                    Some((parent, Err(error))) => {
                        failure = Some(io_error(destination_display, parent, error));
                        None
                    }
                    Some((_, Ok(()))) | None => match publish(
                        &target,
                        content.as_bytes(),
                        Some(permissions),
                        Publish::Create,
                        self.witness,
                        self.faults,
                    ) {
                        Ok(placed) => Some(placed),
                        Err(PublishError::Io(error))
                            if error.kind() == std::io::ErrorKind::AlreadyExists =>
                        {
                            failure = Some(destination_taken(display, destination_display));
                            None
                        }
                        Err(PublishError::Io(error)) => {
                            failure = Some(io_error(destination_display, &target, error));
                            None
                        }
                        // A create never rebases: it never replaces a file.
                        Err(PublishError::Changed) => {
                            failure = Some(destination_taken(display, destination_display));
                            None
                        }
                    },
                };
                let removed = match &placed {
                    Some(_) => match self
                        .faults
                        .inject(source, Stage::RemoveSource)
                        .and_then(|()| std::fs::remove_file(source))
                    {
                        Ok(()) => true,
                        Err(error) => {
                            remove_warning = Some(format!(
                                "{display} was copied to {destination_display}, but it could not be \
                                 removed: {error}. Remove it with a REM edit."
                            ));
                            false
                        }
                    },
                    None => true,
                };
                (
                    Pub::Moved {
                        placed: spot(&placed),
                        removed,
                    },
                    content,
                    placed,
                )
            }
        };
        let (rebased, unsynced) = match placed {
            Some(Placed { rebased, unsynced }) => (rebased, unsynced),
            None => (None, None),
        };
        let sync_warning = unsynced
            .map(|error| format!("{display} was written, but its directory sync failed: {error}"));
        match (outcome(facts), failure) {
            (Outcome::Lands(warn), _) => {
                let (written, basis, mut warnings) = match rebased {
                    Some(text) => (text, Basis::Rebased, vec![rebased_warning(display)]),
                    None => (written.to_owned(), Basis::Staged, Vec::new()),
                };
                warnings.extend(match warn {
                    Warn::None => None,
                    Warn::Sync => sync_warning,
                    Warn::Remove => remove_warning,
                });
                Published::Landed {
                    written,
                    basis,
                    warnings,
                }
            }
            (Outcome::Fails, Some(error)) => Published::Failed(error),
            (Outcome::Fails, None) => crate::commit::inconsistent("a landed publish"),
        }
    }
}

fn io_error(display: &str, path: &Path, source: std::io::Error) -> EditError {
    EditError::Io {
        display: display.to_owned(),
        path: path.to_path_buf(),
        source,
    }
}

fn destination_taken(display: &str, destination: &str) -> EditError {
    EditError::apply(format!(
        "Edit rejected for {display}: the MV destination {destination} exists. Nothing was \
         written. Pick another name, or REM {destination} in an earlier edit."
    ))
}

/// The rejection of an edit whose file `display` changed since staging.
fn changed_on_disk(display: &str) -> EditError {
    EditError::apply(format!(
        "Edit rejected for {display}: the file changed on disk while the edit was being \
         applied. Nothing was written. Re-read the file and retry."
    ))
}

/// The warning of a change rebased, while it was written, onto the bytes
/// another program wrote to `display`.
fn rebased_warning(display: &str) -> String {
    format!(
        "{display} was changed by another program while this change was being written; the \
         change was rebased onto its new bytes, which it keeps. Re-read {display} before you \
         edit the lines that program wrote."
    )
}

impl LockedWriter<'_> {
    /// Tell the witness every change of the call before any lands: a move
    /// creates its destination and removes its source.
    fn witness_all(
        &self,
        requests: &[EditWriteRequest<'_>],
        allowed: &[Allowed],
    ) -> Result<(), EditError> {
        let destinations: Vec<Option<PathBuf>> = requests
            .iter()
            .zip(allowed)
            .map(|(request, paths)| match request.op {
                WriteOp::Move { destination, .. } => Some(
                    paths
                        .target
                        .clone()
                        .unwrap_or_else(|| real_path(destination)),
                ),
                WriteOp::Update { .. } | WriteOp::Delete { .. } => None,
            })
            .collect();
        let mut changes = Vec::with_capacity(requests.len() + destinations.len());
        for ((request, paths), destination) in requests.iter().zip(allowed).zip(&destinations) {
            let (before_raw, next) = match request.op {
                WriteOp::Update {
                    before_raw,
                    content,
                } => (before_raw, Some(content.as_bytes())),
                WriteOp::Delete { before_raw } | WriteOp::Move { before_raw, .. } => {
                    (before_raw, None)
                }
            };
            changes.push(Change {
                real: &paths.source,
                base: Some(before_raw.as_bytes()),
                next,
            });
            if let (WriteOp::Move { content, .. }, Some(destination)) = (request.op, destination) {
                changes.push(Change {
                    real: destination,
                    base: None,
                    next: Some(content.as_bytes()),
                });
            }
        }
        if let (Some(first), Some(paths)) = (requests.first(), allowed.first()) {
            self.witness
                .changing(&changes)
                .map_err(|error| io_error(first.display, &paths.source, error))?;
        }
        Ok(())
    }
}

impl EditWriter for LockedWriter<'_> {
    fn write_all(&self, requests: &[EditWriteRequest<'_>]) -> Result<Vec<Published>, EditError> {
        let mut allowed = Vec::with_capacity(requests.len());
        for request in requests {
            let source = self.allow(request.absolute, request.display)?;
            let target = match request.op {
                WriteOp::Move {
                    destination,
                    destination_display,
                    ..
                } => Some(self.allow(destination, destination_display)?),
                WriteOp::Update { .. } | WriteOp::Delete { .. } => None,
            };
            allowed.push(Allowed { source, target });
        }
        let mut pairs: Vec<(&Path, &Path, &str)> = Vec::with_capacity(requests.len());
        for (request, paths) in requests.iter().zip(&allowed) {
            pairs.push((request.absolute, &paths.source, request.display));
            match (request.op, &paths.target) {
                (
                    WriteOp::Move {
                        destination,
                        destination_display,
                        ..
                    },
                    Some(target),
                ) => pairs.push((destination, target, destination_display)),
                (WriteOp::Move { .. } | WriteOp::Update { .. } | WriteOp::Delete { .. }, _) => {}
            }
        }
        let _locks = self.lock_all(&pairs)?;
        let mut checked = Vec::with_capacity(requests.len());
        let mut mets = Vec::with_capacity(requests.len());
        for (request, paths) in requests.iter().zip(&allowed) {
            let source = &paths.source;
            let (before_raw, taken) = match request.op {
                WriteOp::Update { before_raw, .. } | WriteOp::Delete { before_raw } => {
                    (before_raw, false)
                }
                WriteOp::Move {
                    before_raw,
                    destination,
                    destination_display,
                    ..
                } => {
                    let target = paths
                        .target
                        .clone()
                        .unwrap_or_else(|| real_path(destination));
                    let taken = match std::fs::symlink_metadata(&target) {
                        Ok(_) => true,
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
                        Err(error) => return Err(io_error(destination_display, &target, error)),
                    };
                    (before_raw, taken)
                }
            };
            let permissions = permissions_if_unchanged(source, before_raw.as_bytes())
                .map_err(|error| io_error(request.display, source, error))?;
            mets.push(crate::commit::Met {
                changed: permissions.is_none(),
                taken,
            });
            checked.push(permissions);
        }
        if let Some((at, why)) = crate::commit::check(&mets) {
            let request = &requests[at];
            return Err(match (why, request.op) {
                (
                    crate::commit::Why::Taken,
                    WriteOp::Move {
                        destination_display,
                        ..
                    },
                ) => destination_taken(request.display, destination_display),
                (crate::commit::Why::Changed, _)
                | (crate::commit::Why::Taken, WriteOp::Update { .. } | WriteOp::Delete { .. }) => {
                    changed_on_disk(request.display)
                }
            });
        }
        self.witness_all(requests, &allowed)?;
        let mut published = Vec::with_capacity(requests.len());
        for ((request, paths), permissions) in requests.iter().zip(&allowed).zip(checked) {
            let permissions =
                permissions.unwrap_or_else(|| crate::commit::inconsistent("a checked file"));
            let result = self.publish(request, paths, permissions);
            let failed = match &result {
                Published::Landed { .. } => false,
                Published::Failed(_) => true,
            };
            published.push(result);
            if failed {
                break;
            }
        }
        Ok(published)
    }
}

#[cfg(test)]
mod tests;
