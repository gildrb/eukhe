//! The file operations of a child workspace: which paths it holds, the
//! content of one path, and copies that share extents where the
//! filesystem can.

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs;
use std::io::{self, Read};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::workspace_snapshot::git::git_command;

/// The suffix of the copy [`replace`] stages beside its target.
pub(super) const STAGED_SUFFIX: &str = ".eukhe-handback";

/// The content of one path: a file (the digest of its bytes and its
/// executable bit) or a symlink (its target). A directory is no content.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Content {
    File { digest: [u8; 32], executable: bool },
    Link(PathBuf),
}

/// The content of `path`; `None` when there is no file or symlink (also
/// when one of its directories is a file).
pub(super) fn content(path: &Path) -> io::Result<Option<Content>> {
    let meta = match fs::symlink_metadata(path) {
        Ok(meta) => meta,
        Err(error)
            if matches!(
                error.kind(),
                io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
            ) =>
        {
            return Ok(None)
        }
        Err(error) => return Err(error),
    };
    if meta.file_type().is_symlink() {
        return Ok(Some(Content::Link(fs::read_link(path)?)));
    }
    if !meta.is_file() {
        return Ok(None);
    }
    let mut file = fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 64 * 1024];
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        hasher.update(&buffer[..n]);
    }
    Ok(Some(Content::File {
        digest: hasher.finalize().into(),
        executable: meta.permissions().mode() & 0o111 != 0,
    }))
}

/// How [`copy_entry`] made a copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Copied {
    /// No data was copied: the file's extents are shared (a reflink), or
    /// the entry is a symlink.
    Cloned,
    /// The bytes were copied: the filesystem cannot share extents here.
    Plain,
    /// Nothing to copy: no file or symlink at the source.
    Skipped,
}

/// Copy the file or symlink `from` to the new path `to`, creating its
/// directories. A file is cloned (FICLONE on Linux, clonefile on macOS)
/// where the filesystem shares extents, else copied.
pub(super) fn copy_entry(from: &Path, to: &Path) -> io::Result<Copied> {
    let meta = match fs::symlink_metadata(from) {
        Ok(meta) => meta,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(Copied::Skipped),
        Err(error) => return Err(error),
    };
    if let Some(dir) = to.parent() {
        fs::create_dir_all(dir)?;
    }
    if meta.file_type().is_symlink() {
        std::os::unix::fs::symlink(fs::read_link(from)?, to)?;
        return Ok(Copied::Cloned);
    }
    if !meta.is_file() {
        return Ok(Copied::Skipped);
    }
    if clone_file(from, to, &meta).is_ok() {
        return Ok(Copied::Cloned);
    }
    fs::copy(from, to)?;
    Ok(Copied::Plain)
}

/// Clone `from` into the new file `to` (its data and its mode).
#[cfg(target_os = "linux")]
fn clone_file(from: &Path, to: &Path, meta: &fs::Metadata) -> io::Result<()> {
    let source = fs::File::open(from)?;
    let target = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(to)?;
    let cloned = rustix::fs::ioctl_ficlone(&target, &source)
        .map_err(io::Error::from)
        .and_then(|()| target.set_permissions(meta.permissions()));
    if cloned.is_err() {
        drop(target);
        fs::remove_file(to)?;
    }
    cloned
}

/// Clone `from` into the new file `to` (its data and its metadata).
#[cfg(target_os = "macos")]
fn clone_file(from: &Path, to: &Path, _meta: &fs::Metadata) -> io::Result<()> {
    let (Some(dir), Some(name)) = (to.parent(), to.file_name()) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("no directory and name in {}", to.display()),
        ));
    };
    let source = fs::File::open(from)?;
    let dir = fs::File::open(dir)?;
    rustix::fs::fclonefileat(&source, &dir, name, rustix::fs::CloneFlags::empty())
        .map_err(io::Error::from)
}

/// No extent clone on this platform: every copy is plain.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn clone_file(_from: &Path, _to: &Path, _meta: &fs::Metadata) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "no extent clone on this platform",
    ))
}

/// Put `from`'s content (or no file, when `from` has none) at `to` in one
/// step: a copy beside `to` renamed over it, or a removal. A crash leaves
/// `to` old or new, never half written; the copy's name is the same in
/// every run, so the run after a crash removes the copy it left.
pub(super) fn replace(from: &Path, to: &Path) -> io::Result<()> {
    let (Some(dir), Some(name)) = (to.parent(), to.file_name()) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("no directory and name in {}", to.display()),
        ));
    };
    let mut staged_name = OsStr::new(".").to_os_string();
    staged_name.push(name);
    staged_name.push(STAGED_SUFFIX);
    let staged = dir.join(staged_name);
    match fs::symlink_metadata(&staged) {
        Ok(_) => fs::remove_file(&staged)?,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    match copy_entry(from, &staged)? {
        Copied::Cloned | Copied::Plain => {
            if !fs::symlink_metadata(&staged)?.file_type().is_symlink() {
                fs::File::open(&staged)?.sync_all()?;
            }
            fs::rename(&staged, to)
        }
        Copied::Skipped => match fs::remove_file(to) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            removed => removed,
        },
    }
}

/// Which paths a walk lists.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Listing {
    /// Every file and symlink.
    All,
    /// The files and symlinks the `.gitignore` files in the tree do not
    /// ignore.
    NotIgnored,
}

/// The files and symlinks under `dir`, relative to it; `.git` is never
/// listed.
pub(super) fn walk(dir: &Path, listing: Listing) -> io::Result<BTreeSet<PathBuf>> {
    let mut builder = ignore::WalkBuilder::new(dir);
    builder.standard_filters(false).follow_links(false);
    match listing {
        Listing::All => {}
        Listing::NotIgnored => {
            builder.git_ignore(true).require_git(false);
        }
    }
    builder.filter_entry(|entry| entry.file_name() != ".git");
    let mut paths = BTreeSet::new();
    for entry in builder.build() {
        let entry = entry.map_err(io::Error::other)?;
        let Some(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_file() || kind.is_symlink() {
            if let Ok(relative) = entry.path().strip_prefix(dir) {
                paths.insert(relative.to_path_buf());
            }
        }
    }
    Ok(paths)
}

/// The paths of the parent workspace a child copies: the tracked and the
/// untracked, not ignored files of its git work tree under `dir`
/// (`git ls-files`), else (no git work tree) the files its `.gitignore`
/// files do not ignore.
#[tracing::instrument(level = "debug")]
pub(super) async fn parent_paths(dir: &Path) -> anyhow::Result<BTreeSet<PathBuf>> {
    let listed = git_command(
        &[
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ],
        dir,
    )
    .stdin(std::process::Stdio::null())
    .output()
    .await;
    match listed {
        Ok(output) if output.status.success() => Ok(output
            .stdout
            .split(|&b| b == 0)
            .filter(|path| !path.is_empty())
            .map(|path| PathBuf::from(OsStr::from_bytes(path)))
            .collect()),
        Ok(_) | Err(_) => {
            let dir = dir.to_path_buf();
            Ok(tokio::task::spawn_blocking(move || walk(&dir, Listing::NotIgnored)).await??)
        }
    }
}
