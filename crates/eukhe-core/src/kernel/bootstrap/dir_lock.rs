//! Cross-process bootstrap lock for the kernel venv, ported from
//! `utils/dir-lock.ts`: a `link(2)`-published lock file whose owner is a
//! live pid; stale locks are renamed aside, verified, then reclaimed.
//!
//! An attempt's candidate file (`<lock>.candidate-<pid>-<uuid>`) never
//! outlives the attempt: a guard removes it on every return path, and the
//! next acquire sweeps the candidates (and renamed-aside stale locks) of
//! processes that died inside an attempt. Which leftovers go and what an
//! attempt makes of the lock it finds are decided by the compiled Bend
//! core (`bend/ffi_kernel_local.bend` requests 1 and 2: `keep` and
//! `attempt` of `lock.of` in `bend/kernel_local.bend`; laws
//! `kernel_lock_sweep_removes_dead`, `kernel_lock_sweep_keeps_live`,
//! `kernel_lock_judge`); this file reads the dir, the lock and the pids,
//! and does what the core answers.

use std::io::Write;
use std::path::{Path, PathBuf};

use eukhe_bend::wire::{Reader, Writer, NAT_MAX};
use eukhe_bend::{Entry, Error};

use super::venv::{BOOTSTRAP_LOCK_NAME, BOOTSTRAP_LOCK_RETRY_MS};

/// The infix of an attempt's candidate file name.
const CANDIDATE_INFIX: &str = ".candidate-";
/// The infix of a stale lock renamed aside.
const STALE_INFIX: &str = ".stale-";

fn is_process_alive(pid: u32) -> bool {
    crate::platform::process::pid_exists(pid)
}

/// A `link(2)`-published lock file: born with owner content, EEXIST the only
/// collision signal; stale locks are renamed aside, verified, then reclaimed.
/// Ported from `utils/dir-lock.ts`.
pub(crate) enum DirLockAttempt {
    Acquired,
    Held,
    Reclaimed,
}

fn strict_pid(raw: Option<&str>) -> Option<u32> {
    let trimmed = raw?.trim();
    if trimmed.is_empty() || !trimmed.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let parsed: u32 = trimmed.parse().ok()?;
    (parsed > 0).then_some(parsed)
}

/// An attempt's candidate file: removed when the attempt ends, on every
/// path (a failed write, a lost link race, an error).
struct Candidate(PathBuf);

impl Drop for Candidate {
    fn drop(&mut self) {
        match std::fs::remove_file(&self.0) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                tracing::warn!(%error, path = %self.0.display(), "kernel lock candidate not removed");
            }
        }
    }
}

/// A file beside the lock, as the core's sweep reads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Leftover {
    /// An attempt's candidate, of an owner that lives (`true`) or not.
    Candidate(bool),
    /// A stale lock an attempt renamed aside, of an owner that lives or not.
    Aside(bool),
    /// Any other file: not a leftover, or one whose owner it does not name.
    Other,
}

/// The leftover `file_name` is beside the lock `lock_name`.
fn leftover(lock_name: &str, file_name: &str) -> Leftover {
    let Some(rest) = file_name.strip_prefix(lock_name) else {
        return Leftover::Other;
    };
    let (token, aside) = match (
        rest.strip_prefix(CANDIDATE_INFIX),
        rest.strip_prefix(STALE_INFIX),
    ) {
        (Some(token), _) => (token, false),
        (None, Some(token)) => (token, true),
        (None, None) => return Leftover::Other,
    };
    match strict_pid(token.split_once('-').map(|(pid, _)| pid)) {
        Some(owner) if aside => Leftover::Aside(is_process_alive(owner)),
        Some(owner) => Leftover::Candidate(is_process_alive(owner)),
        None => Leftover::Other,
    }
}

/// The core's sweep verdict on each of `files`, in order: `true` keeps it.
fn keeps(files: &[Leftover]) -> Result<Vec<bool>, Error> {
    let mut request = Writer::new();
    request.tag(1).count(files.len());
    for file in files {
        match *file {
            Leftover::Candidate(alive) => request.tag(0).bool(alive),
            Leftover::Aside(alive) => request.tag(1).bool(alive),
            Leftover::Other => request.tag(2).bool(true),
        };
    }
    let reply = eukhe_bend::call(Entry::KernelLocal, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut kept = Vec::with_capacity(count.min(files.len()));
    for _ in 0..count {
        kept.push(reader.bool()?);
    }
    reader.end()?;
    Ok(kept)
}

/// Remove the leftovers of attempts whose process is gone: an attempt's
/// candidate (`<lock>.candidate-<pid>-<uuid>`) or a stale lock it renamed
/// aside (`<lock>.stale-<pid>-<uuid>`), left by a process that died inside
/// the attempt. A live owner's leftover stays: its attempt still runs.
pub(crate) fn sweep_leftovers(lock_path: &Path) {
    let (Some(dir), Some(lock_name)) = (
        lock_path.parent(),
        lock_path.file_name().and_then(|name| name.to_str()),
    ) else {
        return;
    };
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(error) => {
            tracing::warn!(%error, dir = %dir.display(), "kernel lock leftovers not swept");
            return;
        }
    };
    let (paths, files): (Vec<PathBuf>, Vec<Leftover>) = entries
        .flatten()
        .map(|entry| {
            let file = entry
                .file_name()
                .to_str()
                .map_or(Leftover::Other, |name| leftover(lock_name, name));
            (entry.path(), file)
        })
        .unzip();
    let kept = eukhe_bend::expect_core(Entry::KernelLocal, keeps(&files));
    for (path, keep) in paths.iter().zip(kept) {
        if keep {
            continue;
        }
        match std::fs::remove_file(path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                tracing::warn!(%error, path = %path.display(), "kernel lock leftover not removed");
            }
        }
    }
}

/// What an attempt saw at the lock path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Seen {
    /// Its candidate was linked there: the lock is its own.
    Linked,
    /// The lock vanished before it was read.
    Vanished,
    /// The lock names an owner that lives (`true`) or not.
    Owner(bool),
    /// The lock names no owner; its age in ms (`None`: unknown).
    NoOwner(Option<u64>),
}

/// The core's verdict on an attempt that saw `seen`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    /// The lock is the attempt's.
    Got,
    /// The lock is held: wait and retry.
    Busy,
    /// The lock is stale: rename it aside and remove it.
    Free,
}

fn verdict(seen: Seen) -> Result<Verdict, Error> {
    let mut request = Writer::new();
    request.tag(2);
    match seen {
        Seen::Linked => request.tag(0),
        Seen::Vanished => request.tag(1),
        Seen::Owner(alive) => request.tag(2).bool(alive),
        Seen::NoOwner(None) => request.tag(3).none(),
        Seen::NoOwner(Some(age_ms)) => request.tag(3).some().nat(age_ms.min(NAT_MAX)),
    };
    let reply = eukhe_bend::call(Entry::KernelLocal, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = match reader.tag_of(3, "a lock attempt's end")? {
        0 => Verdict::Got,
        1 => Verdict::Busy,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Verdict::Free,
    };
    reader.end()?;
    Ok(verdict)
}

/// The age of the lock at `lock_path` in ms; `None` when its mtime cannot
/// be read or lies in the future.
fn lock_age_ms(lock_path: &Path) -> Option<u64> {
    let modified = std::fs::metadata(lock_path).ok()?.modified().ok()?;
    let age = std::time::SystemTime::now().duration_since(modified).ok()?;
    Some(u64::try_from(age.as_millis()).unwrap_or(u64::MAX))
}

/// What the lock at `lock_path` names, read after a failed link.
fn seen_at(lock_path: &Path) -> Seen {
    let owner = match std::fs::read_to_string(lock_path) {
        Ok(raw) => strict_pid(Some(&raw)),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Seen::Vanished,
        Err(error) if error.kind() == std::io::ErrorKind::IsADirectory => {
            // Legacy directory lock from the old protocol.
            match std::fs::read_to_string(lock_path.join("pid")) {
                Ok(raw) => strict_pid(Some(&raw)),
                Err(_) => None,
            }
        }
        Err(_) => None,
    };
    match owner {
        Some(pid) => Seen::Owner(is_process_alive(pid)),
        None => Seen::NoOwner(lock_age_ms(lock_path)),
    }
}

pub(crate) fn try_acquire_dir_lock(lock_path: &Path) -> anyhow::Result<DirLockAttempt> {
    std::fs::create_dir_all(lock_path.parent().unwrap_or(Path::new("/")))?;
    let token = format!("{}-{}", std::process::id(), uuid::Uuid::new_v4());
    let candidate = Candidate(lock_path.with_file_name(format!(
        "{}{CANDIDATE_INFIX}{token}",
        lock_path.file_name().unwrap_or_default().to_string_lossy(),
    )));
    {
        let mut options = std::fs::OpenOptions::new();
        options.create(true).write(true).truncate(true);
        crate::platform::perms::set_private_mode(&mut options);
        let mut file = options.open(&candidate.0)?;
        writeln!(file, "{}", std::process::id())?;
    }
    // The primary signal: link() publishing the candidate under the lock path.
    let seen = if std::fs::hard_link(&candidate.0, lock_path).is_ok() {
        Seen::Linked
    } else {
        seen_at(lock_path)
    };
    Ok(match verdict(seen)? {
        Verdict::Got => DirLockAttempt::Acquired,
        Verdict::Busy => DirLockAttempt::Held,
        Verdict::Free => {
            let aside_path = lock_path.with_file_name(format!(
                "{}{STALE_INFIX}{token}",
                lock_path.file_name().unwrap_or_default().to_string_lossy(),
            ));
            match std::fs::rename(lock_path, &aside_path) {
                Ok(()) => {
                    if std::fs::remove_file(&aside_path).is_ok() {
                        DirLockAttempt::Reclaimed
                    } else {
                        DirLockAttempt::Held
                    }
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    DirLockAttempt::Reclaimed
                }
                Err(_) => DirLockAttempt::Held,
            }
        }
    })
}

/// Serialize concurrent bootstraps across processes on the same venv.
pub(crate) async fn acquire_bootstrap_lock(venv: &Path) -> anyhow::Result<impl Drop> {
    let lock_dir = venv.with_file_name(format!(
        "{}{}",
        venv.file_name().unwrap_or_default().to_string_lossy(),
        BOOTSTRAP_LOCK_NAME
    ));
    std::fs::create_dir_all(lock_dir.parent().unwrap_or(Path::new("/")))?;
    sweep_leftovers(&lock_dir);
    loop {
        match try_acquire_dir_lock(&lock_dir)? {
            DirLockAttempt::Acquired => {
                struct Guard(PathBuf);
                impl Drop for Guard {
                    fn drop(&mut self) {
                        let _ = std::fs::remove_file(&self.0);
                    }
                }
                return Ok(Guard(lock_dir));
            }
            DirLockAttempt::Held | DirLockAttempt::Reclaimed => {
                tokio::time::sleep(std::time::Duration::from_millis(BOOTSTRAP_LOCK_RETRY_MS)).await;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The sweep's and the attempt's verdicts come from the compiled core:
    /// a dead attempt's candidate and stale lock go, a live one's and any
    /// other file stay; a lock naming no owner frees past 30 s, not at it.
    #[test]
    fn the_lock_verdicts_come_from_the_compiled_core() {
        let files = [
            Leftover::Candidate(false),
            Leftover::Candidate(true),
            Leftover::Aside(false),
            Leftover::Other,
        ];
        assert_eq!(
            (
                keeps(&files).expect("the sweep"),
                verdict(Seen::NoOwner(Some(30_001))).expect("an old lock"),
                verdict(Seen::NoOwner(Some(30_000))).expect("a young lock"),
            ),
            (vec![false, true, false, true], Verdict::Free, Verdict::Busy)
        );
    }
}
