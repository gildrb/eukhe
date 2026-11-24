//! Cancellation and the input lease (port of omp
//! `crates/natives/src/desktop/control.rs`).
//!
//! Shared state, and why: a session's [`CancelSource`] is shared by the
//! caller (who cancels) and the worker (who checks); the input lease is a
//! lock file the OS arbitrates between every session and process of one
//! user, so two agents never send input at once.

pub(crate) mod intervention;

use std::fs::{File, OpenOptions, TryLockError};
use std::io;
use std::os::unix::fs::{FileExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex, PoisonError, Weak};
use std::time::{Duration, Instant};

use crate::error::{Error, Holder, Interruption, Refusal, Unverified};

#[derive(Default)]
struct CancelState {
    generation: AtomicU64,
    lock: Mutex<()>,
    wake: Condvar,
    /// Takeover input the user's physical Escape stopped.
    escapes: AtomicU32,
}

impl CancelState {
    fn cancel(&self) {
        let _guard = self.lock.lock().unwrap_or_else(PoisonError::into_inner);
        self.generation.fetch_add(1, Ordering::AcqRel);
        self.wake.notify_all();
    }
}

/// Cancels a session's current and queued operations.
#[derive(Clone, Default)]
pub(crate) struct CancelSource(Arc<CancelState>);

impl CancelSource {
    /// A token for an operation queued now.
    pub(crate) fn token(&self) -> Token {
        Token {
            state: Arc::clone(&self.0),
            generation: self.0.generation.load(Ordering::Acquire),
            escapes: self.0.escapes.load(Ordering::Acquire),
        }
    }

    /// Stops the current operation and every one queued before this call.
    pub(crate) fn cancel(&self) {
        self.0.cancel();
    }

    /// How many times the user's physical Escape stopped this session.
    pub(crate) fn escapes(&self) -> u32 {
        self.0.escapes.load(Ordering::Acquire)
    }

    /// The handle an Escape monitor stops this session through.
    pub(crate) fn emergency_stop(&self) -> EmergencyStop {
        EmergencyStop(Arc::downgrade(&self.0))
    }
}

/// The physical Escape's way into a session; weak, so a monitor never keeps
/// a closed session alive.
pub(crate) struct EmergencyStop(Weak<CancelState>);

impl EmergencyStop {
    /// The user's physical Escape: counted before the cancel, so whoever
    /// sees the cancelled operation sees the stop that caused it.
    pub(crate) fn escape(&self) {
        if let Some(state) = self.0.upgrade() {
            state.escapes.fetch_add(1, Ordering::AcqRel);
            state.cancel();
        }
    }
}

/// One operation's view of its session's cancellation.
pub(crate) struct Token {
    state: Arc<CancelState>,
    generation: u64,
    escapes: u32,
}

/// Whether an operation has sent any input yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Sent {
    Nothing,
    Some,
}

impl Token {
    fn cancelled(&self) -> bool {
        self.state.generation.load(Ordering::Acquire) != self.generation
    }

    /// `Cancelled` once the operation was cancelled.
    pub(crate) fn check(&self) -> Result<(), Error> {
        if self.cancelled() {
            return Err(Error::Refused(Refusal::Cancelled));
        }
        Ok(())
    }

    /// [`Self::check`] before a press, saying whether input already went out.
    pub(crate) fn check_sent(&self, sent: Sent) -> Result<(), Error> {
        match (self.cancelled(), sent) {
            (false, _) => Ok(()),
            (true, Sent::Nothing) => Err(Error::Refused(Refusal::Cancelled)),
            (true, Sent::Some) => Err(Error::Unverified(Unverified::Interrupted(self.stopper()))),
        }
    }

    fn stopper(&self) -> Interruption {
        if self.state.escapes.load(Ordering::Acquire) > self.escapes {
            Interruption::Escape
        } else {
            Interruption::Cancelled
        }
    }

    /// Sleeps `duration`, ending early with `Cancelled` on a cancel.
    pub(crate) fn wait(&self, duration: Duration) -> Result<(), Error> {
        let deadline = Instant::now() + duration;
        let mut guard = self
            .state
            .lock
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        loop {
            self.check()?;
            let left = deadline.saturating_duration_since(Instant::now());
            if left.is_zero() {
                return Ok(());
            }
            guard = self
                .state
                .wake
                .wait_timeout(guard, left)
                .unwrap_or_else(PoisonError::into_inner)
                .0;
        }
    }
}

/// How long input waits for another session to release the lease.
const LEASE_WAIT: Duration = Duration::from_secs(5);
/// How often a waiting session tries the lease again.
const LEASE_POLL: Duration = Duration::from_millis(50);
/// Characters of a holder's name its record keeps.
const HOLDER_CHARS: usize = 64;

/// The input lease: an exclusive lock on one per-user file, held while a
/// session sends input. Dropping it closes the file, which unlocks it.
pub(crate) struct InputLease {
    _file: File,
}

impl InputLease {
    /// Takes the lease at `path`, recording `holder` for sessions that find
    /// it taken; waits up to [`LEASE_WAIT`] for another holder to let go.
    pub(crate) fn acquire(path: &Path, holder: &str, token: &Token) -> Result<Self, Error> {
        let file = open_lock(path)?;
        let limit = Instant::now() + LEASE_WAIT;
        loop {
            token.check()?;
            match file.try_lock() {
                Ok(()) => {
                    record(&file, holder)
                        .map_err(|error| platform("record the input lease", &error))?;
                    return Ok(Self { _file: file });
                }
                Err(TryLockError::WouldBlock) if Instant::now() < limit => {
                    token.wait(LEASE_POLL)?;
                }
                Err(TryLockError::WouldBlock) => {
                    return Err(Error::Refused(Refusal::InputBusy {
                        holder: holder_of(&file),
                    }));
                }
                Err(TryLockError::Error(error)) => {
                    return Err(platform("lock the input lease", &error));
                }
            }
        }
    }
}

fn platform(action: &str, error: &io::Error) -> Error {
    Error::Refused(Refusal::Platform {
        detail: format!("cannot {action}: {error}").into(),
    })
}

/// Opens the lock file, refusing anything but a private regular file: never
/// a symlink, a hard link, or a file other users can write.
fn open_lock(path: &Path) -> Result<File, Error> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)
        .map_err(|error| platform("open the input lease", &error))?;
    let metadata = file
        .metadata()
        .map_err(|error| platform("inspect the input lease", &error))?;
    if !metadata.is_file() || metadata.nlink() != 1 || metadata.mode() & 0o077 != 0 {
        return Err(Error::Refused(Refusal::Platform {
            detail: format!(
                "the input lease {} is not a private regular file",
                path.display()
            )
            .into(),
        }));
    }
    Ok(file)
}

/// Writes `pid\nholder` over the record a former holder left.
fn record(file: &File, holder: &str) -> io::Result<()> {
    let name: String = holder
        .chars()
        .filter(|c| !c.is_control())
        .take(HOLDER_CHARS)
        .collect();
    file.set_len(0)?;
    file.write_all_at(format!("{}\n{name}", std::process::id()).as_bytes(), 0)
}

/// The holder a locked file's record names; unnamed when it names none.
fn holder_of(file: &File) -> Holder {
    let mut buffer = [0u8; 10 + 1 + HOLDER_CHARS * 4];
    let Ok(length) = file.read_at(&mut buffer, 0) else {
        return Holder::Unnamed;
    };
    let text = String::from_utf8_lossy(&buffer[..length]);
    let Some((pid, name)) = text.split_once('\n') else {
        return Holder::Unnamed;
    };
    match pid.parse() {
        Ok(pid) if !name.is_empty() => Holder::Named {
            name: name.to_owned(),
            pid,
        },
        Ok(_) | Err(_) => Holder::Unnamed,
    }
}

/// The input lease path for this user: in `$XDG_RUNTIME_DIR` on Linux, in
/// the per-user temporary directory on macOS.
///
/// # Errors
///
/// `Platform` when Linux sets no `XDG_RUNTIME_DIR`.
pub fn default_input_lock() -> Result<PathBuf, Error> {
    const NAME: &str = "eukhe-desktop-input.lock";
    if cfg!(target_os = "macos") {
        return Ok(std::env::temp_dir().join(NAME));
    }
    std::env::var_os("XDG_RUNTIME_DIR")
        .map(|dir| PathBuf::from(dir).join(NAME))
        .ok_or_else(|| {
            Error::Refused(Refusal::Platform {
                detail:
                    "XDG_RUNTIME_DIR is not set, so there is no per-user place for the input lease"
                        .into(),
            })
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lock_path(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("eukhe-desktop-{name}-{}.lock", std::process::id()))
    }

    #[test]
    fn a_second_session_finds_the_lease_taken_and_named() {
        let path = lock_path("lease");
        let source = CancelSource::default();
        let first = InputLease::acquire(&path, "agent-a", &source.token());
        assert!(first.is_ok());
        let file = open_lock(&path).unwrap_or_else(|error| panic!("{error}"));
        assert!(matches!(file.try_lock(), Err(TryLockError::WouldBlock)));
        assert_eq!(
            holder_of(&file),
            Holder::Named {
                name: "agent-a".to_owned(),
                pid: std::process::id()
            }
        );
        drop(first);
        assert!(InputLease::acquire(&path, "agent-b", &source.token()).is_ok());
        assert!(std::fs::remove_file(&path).is_ok());
    }

    #[test]
    fn a_cancel_ends_waits_and_marks_sent_input_unverified() {
        let source = CancelSource::default();
        let token = source.token();
        source.cancel();
        assert_eq!(
            token.wait(Duration::from_secs(60)),
            Err(Error::Refused(Refusal::Cancelled))
        );
        assert_eq!(
            token.check_sent(Sent::Some),
            Err(Error::Unverified(Unverified::Interrupted(
                Interruption::Cancelled
            )))
        );
        source.emergency_stop().escape();
        assert_eq!(
            token.check_sent(Sent::Some),
            Err(Error::Unverified(Unverified::Interrupted(
                Interruption::Escape
            )))
        );
        assert_eq!(source.token().check(), Ok(()));
    }
}
