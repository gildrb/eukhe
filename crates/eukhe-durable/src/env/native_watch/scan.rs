//! Snapshots of watched paths: the `#scan` of `NodeFileWatcher`, its `Entry`
//! records, and `anyUnreliable`.

use std::collections::{HashMap, HashSet};
use std::fs::{self, Metadata};
use std::io;
use std::os::unix::fs::MetadataExt;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use sha2::{Digest, Sha256};

use super::paths::{ancestors_of, join};
use crate::env::node_error::{fs_error, uv_code};
use crate::env::{FileError, FileErrorCode};

/// In polling mode, recently modified small files are also compared by
/// content: a second write within the file system's timestamp granularity can
/// keep size and modification time.
const HASH_MAX_BYTES: u64 = 256 * 1024;
const HASH_RECENT_MS: f64 = 5000.0;

/// A watch target with its path resolved and its exclusions applied.
#[derive(Debug)]
pub(super) struct ResolvedTarget {
    pub(super) path: String,
    pub(super) recursive: bool,
    pub(super) hidden: bool,
    pub(super) names: HashSet<String>,
}

impl ResolvedTarget {
    /// TS `excluded(target, name)`.
    pub(super) fn excluded(&self, name: &str) -> bool {
        (self.hidden && name.starts_with('.')) || self.names.contains(name)
    }
}

/// What a path is, not following a final symbolic link unless recorded by
/// `stat`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum EntryKind {
    File,
    Directory,
    Symlink,
    Other,
}

/// What a snapshot remembers of one path. Directories and ancestors are
/// compared by identity only. Equality is TS `sameEntry`.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct Entry {
    pub(super) kind: EntryKind,
    pub(super) dev: u64,
    pub(super) ino: u64,
    pub(super) size: u64,
    /// Node's `stats.mtimeMs`: `sec * 1e3 + nsec / 1e6` as a double.
    pub(super) mtime_ms: f64,
    pub(super) hash: Option<String>,
}

pub(super) type Snapshot = HashMap<String, Entry>;

/// A scan: the snapshot, and targets that are symbolic links to files, whose
/// files need their own watchers (in insertion order).
pub(super) struct Scan {
    pub(super) snapshot: Snapshot,
    pub(super) linked_files: Vec<String>,
}

/// Why a scan failed: what TS `#scan` throws.
#[derive(Debug)]
pub(super) enum ScanError {
    /// TS `BudgetExceeded`, with its message.
    BudgetExceeded(String),
    /// A `node:fs` call failed: `scandir` of a target directory, or `stat` of
    /// a target.
    Fs {
        error: io::Error,
        syscall: &'static str,
        path: String,
    },
}

impl ScanError {
    /// What `open` fails with: `BudgetExceeded` becomes an `invalid`
    /// `FileError` without a path; Node errors go through node.ts
    /// `toFileError`.
    pub(super) fn into_open_error(self) -> FileError {
        match self {
            Self::BudgetExceeded(message) => FileError::new(FileErrorCode::Invalid, message, None),
            Self::Fs {
                error,
                syscall,
                path,
            } => fs_error(error, syscall, &path),
        }
    }

    /// What a failed flush delivers: TS `new FileError(isDenied(error) ?
    /// "permission_denied" : "invalid", message)`, without path or cause.
    pub(super) fn into_flush_error(self) -> FileError {
        match self {
            Self::BudgetExceeded(message) => FileError::new(FileErrorCode::Invalid, message, None),
            Self::Fs {
                error,
                syscall,
                path,
            } => {
                let code = if is_denied(&error) {
                    FileErrorCode::PermissionDenied
                } else {
                    FileErrorCode::Invalid
                };
                FileError::new(code, fs_error(error, syscall, &path).message, None)
            }
        }
    }
}

/// TS `isDenied`.
fn is_denied(error: &io::Error) -> bool {
    matches!(uv_code(error), "EACCES" | "EPERM")
}

fn kind_of(metadata: &Metadata) -> EntryKind {
    let file_type = metadata.file_type();
    if file_type.is_file() {
        EntryKind::File
    } else if file_type.is_dir() {
        EntryKind::Directory
    } else if file_type.is_symlink() {
        EntryKind::Symlink
    } else {
        EntryKind::Other
    }
}

#[expect(
    clippy::cast_precision_loss,
    reason = "Node computes mtimeMs as a double: sec * 1e3 + nsec / 1e6"
)]
fn mtime_ms(metadata: &Metadata) -> f64 {
    metadata.mtime() as f64 * 1000.0 + metadata.mtime_nsec() as f64 / 1e6
}

/// JS `Date.now()`: whole milliseconds since the epoch.
#[expect(
    clippy::cast_precision_loss,
    reason = "Date.now() is a double; milliseconds since the epoch stay far below 2^53"
)]
fn now_ms() -> f64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(elapsed) => elapsed.as_millis() as f64,
        Err(before) => -(before.duration().as_millis() as f64),
    }
}

/// TS `entryOf`.
fn entry_of(metadata: &Metadata, hash: Option<String>) -> Entry {
    let kind = kind_of(metadata);
    let directory = kind == EntryKind::Directory;
    Entry {
        kind,
        dev: metadata.dev(),
        ino: metadata.ino(),
        size: if directory { 0 } else { metadata.size() },
        mtime_ms: if directory { 0.0 } else { mtime_ms(metadata) },
        hash,
    }
}

/// `readdir(directory)`: entry names, sorted like libuv's `scandir` (byte
/// order). Names that are not UTF-8 are decoded lossily, as Node does.
fn read_names(directory: &str) -> io::Result<Vec<String>> {
    let mut names = fs::read_dir(directory)?
        .map(|entry| entry.map(|entry| entry.file_name().to_string_lossy().into_owned()))
        .collect::<io::Result<Vec<_>>>()?;
    names.sort_unstable();
    Ok(names)
}

/// TS `#scan`, run on a blocking thread. `polling` is the watcher's live mode,
/// read whenever a file is recorded.
pub(super) fn scan(
    targets: &[ResolvedTarget],
    polling: &AtomicBool,
    max_directories: usize,
) -> Result<Scan, ScanError> {
    let mut scanner = Scanner {
        polling,
        max_directories,
        snapshot: HashMap::new(),
        linked_files: Vec::new(),
        counted: HashSet::new(),
        traversed: HashSet::new(),
        listed: HashMap::new(),
    };
    for (index, target) in targets.iter().enumerate() {
        for ancestor in ancestors_of(&target.path) {
            if scanner.snapshot.contains_key(&ancestor) {
                continue;
            }
            // A missing or unreadable ancestor is not recorded (TS `.catch(() => undefined)`).
            if let Ok(metadata) = fs::symlink_metadata(&ancestor) {
                // Identity only: an ancestor's own timestamps change with every unrelated sibling.
                let entry = Entry {
                    size: 0,
                    mtime_ms: 0.0,
                    ..entry_of(&metadata, None)
                };
                scanner.snapshot.insert(ancestor, entry);
            }
        }
        // The target itself may be a symbolic link to what is watched; follow it. A missing
        // target is watched for its creation; one that cannot be reached for lack of
        // permission fails.
        let metadata = match fs::metadata(&target.path) {
            Ok(metadata) => metadata,
            Err(error) if is_denied(&error) => {
                return Err(ScanError::Fs {
                    error,
                    syscall: "stat",
                    path: target.path.clone(),
                });
            }
            Err(_) => continue,
        };
        scanner.record(&target.path, &metadata);
        if metadata.is_file()
            && fs::symlink_metadata(&target.path)
                .is_ok_and(|metadata| metadata.file_type().is_symlink())
            && !scanner.linked_files.contains(&target.path)
        {
            scanner.linked_files.push(target.path.clone());
        }
        if metadata.is_dir() {
            scanner.count_directory(&target.path)?;
            scanner.scan_directory(index, target)?;
        }
    }
    Ok(Scan {
        snapshot: scanner.snapshot,
        linked_files: scanner.linked_files,
    })
}

struct Scanner<'a> {
    polling: &'a AtomicBool,
    max_directories: usize,
    snapshot: Snapshot,
    linked_files: Vec<String>,
    /// Directories are counted once, but traversed once per target:
    /// overlapping targets differ in recursion and exclusions, and an entry
    /// recorded for one target must still be descended into for another.
    counted: HashSet<String>,
    traversed: HashSet<(usize, String)>,
    /// Kinds of listed entries, not following links: a target that links to a
    /// directory is recorded by `stat`, but symbolic links below a recursive
    /// target are not followed.
    listed: HashMap<String, EntryKind>,
}

impl Scanner<'_> {
    fn count_directory(&mut self, path: &str) -> Result<(), ScanError> {
        self.counted.insert(path.to_owned());
        if self.counted.len() > self.max_directories {
            return Err(ScanError::BudgetExceeded(format!(
                "Watched paths exceed {} directories",
                self.max_directories
            )));
        }
        Ok(())
    }

    fn record(&mut self, path: &str, metadata: &Metadata) {
        let mut hash = None;
        if self.polling.load(Ordering::SeqCst)
            && metadata.is_file()
            && metadata.size() <= HASH_MAX_BYTES
            && now_ms() - mtime_ms(metadata) < HASH_RECENT_MS
        {
            // An unreadable file is compared without its hash (TS `() => undefined`).
            hash = fs::read(path)
                .ok()
                .map(|content| format!("{:x}", Sha256::digest(content)));
        }
        self.snapshot
            .insert(path.to_owned(), entry_of(metadata, hash));
    }

    /// The names of `directory` for the `index`th target, or `None` when it
    /// was already traversed for that target or is skipped.
    fn list(
        &mut self,
        index: usize,
        target: &ResolvedTarget,
        directory: &str,
    ) -> Result<Option<Vec<String>>, ScanError> {
        if !self.traversed.insert((index, directory.to_owned())) {
            return Ok(None);
        }
        match read_names(directory) {
            Ok(names) => Ok(Some(names)),
            Err(error) => {
                // The watched directory itself must be readable; below it, unreadable
                // directories are skipped.
                if directory == target.path && is_denied(&error) {
                    return Err(ScanError::Fs {
                        error,
                        syscall: "scandir",
                        path: directory.to_owned(),
                    });
                }
                if matches!(uv_code(&error), "ENOENT" | "EACCES" | "EPERM" | "ENOTDIR") {
                    return Ok(None);
                }
                Err(ScanError::Fs {
                    error,
                    syscall: "scandir",
                    path: directory.to_owned(),
                })
            }
        }
    }

    /// TS `scanDirectory(index, target, target.path)`: the same depth-first
    /// order, with an explicit stack instead of recursion so deep trees cannot
    /// exhaust the thread's stack.
    fn scan_directory(&mut self, index: usize, target: &ResolvedTarget) -> Result<(), ScanError> {
        let mut stack: Vec<(String, std::vec::IntoIter<String>)> = Vec::new();
        if let Some(names) = self.list(index, target, &target.path)? {
            stack.push((target.path.clone(), names.into_iter()));
        }
        while let Some((directory, names)) = stack.last_mut() {
            let Some(name) = names.next() else {
                stack.pop();
                continue;
            };
            if target.excluded(&name) {
                continue;
            }
            let path = join(directory, &name);
            let kind = if let Some(kind) = self.listed.get(&path) {
                *kind
            } else {
                // An entry gone before its metadata is read is skipped.
                let Ok(metadata) = fs::symlink_metadata(&path) else {
                    continue;
                };
                let kind = kind_of(&metadata);
                self.listed.insert(path.clone(), kind);
                // A target's own entry (following links) wins over its listing by another target.
                if !self.snapshot.contains_key(&path) {
                    self.record(&path, &metadata);
                }
                kind
            };
            if target.recursive && kind == EntryKind::Directory {
                self.count_directory(&path)?;
                if let Some(names) = self.list(index, target, &path)? {
                    stack.push((path, names.into_iter()));
                }
            }
        }
        Ok(())
    }
}

/// Linux `statfs` magic numbers of file systems that accept watches but do not
/// report changes made elsewhere.
#[cfg(target_os = "linux")]
const UNRELIABLE_FILE_SYSTEMS: [nix::sys::statfs::FsType; 12] = {
    use nix::sys::statfs::FsType;
    [
        FsType(0x6969),      // NFS
        FsType(0x517b),      // SMB
        FsType(0xff53_4d42), // CIFS
        FsType(0xfe53_4d42), // SMB2
        FsType(0x6573_5546), // FUSE (sshfs, Android shared storage)
        FsType(0x0102_1997), // 9P (WSL2 Windows drives)
        FsType(0x0bd0_0bd0), // Lustre
        FsType(0x4750_4653), // GPFS
        FsType(0x00c3_6400), // Ceph
        FsType(0x5346_414f), // OpenAFS
        FsType(0x6b41_4653), // kAFS
        FsType(0x5dca_2df5), // sdcardfs
    ]
};

/// Whether any path, or its nearest existing ancestor, is on a file system
/// that does not report remote changes. Run on a blocking thread.
#[cfg(target_os = "linux")]
pub(super) fn any_unreliable(paths: &[String]) -> bool {
    for path in paths {
        for candidate in std::iter::once(path.clone()).chain(ancestors_of(path)) {
            // A path that cannot be examined defers to its parent (TS `.catch(() => undefined)`).
            let Ok(info) = nix::sys::statfs::statfs(candidate.as_str()) else {
                continue;
            };
            if UNRELIABLE_FILE_SYSTEMS.contains(&info.filesystem_type()) {
                return true;
            }
            break;
        }
    }
    false
}

/// `statfs` magic numbers are Linux's; elsewhere every file system counts as
/// reliable, as in TS.
#[cfg(target_os = "macos")]
pub(super) fn any_unreliable(_paths: &[String]) -> bool {
    false
}
