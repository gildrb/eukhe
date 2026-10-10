//! Session leases (port of core/session-lease.ts).
//!
//! One process may host one runtime per canonical session file. A lease is a
//! directory `<agent-dir>/session-leases/<sha256(path)>.lock` containing
//! `owner.json`; acquisition is an atomic rename of a candidate directory, and
//! stale owners (dead pid, or a recycled pid whose start identity changed) are
//! reclaimed. A separate guard lock serializes lease updates.

use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

pub const SESSION_LEASES_ENABLED_ENV: &str = "EUKHE_INTERNAL_SESSION_LEASES";
pub const SESSION_LEASE_OWNER_ID_ENV: &str = "EUKHE_INTERNAL_SESSION_LEASE_OWNER_ID";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct LeaseOwner {
    version: u32,
    token: String,
    pid: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    process_start_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    active_session_id: Option<String>,
    session_path: String,
    created_at: String,
}

/// Error matching the TS wire shape (`session_already_active`): `Display`
/// keeps the TS message byte-identical; the user-facing rendering lives in
/// [`crate::hold_refusal`] (the TS/Rust co-existence refusal).
#[derive(Debug, thiserror::Error)]
#[error("Session is already active in {owner}: {session_path}")]
pub struct SessionAlreadyActiveError {
    pub session_path: String,
    pub active_session_id: Option<String>,
    pub owner: String,
    /// The live holder's pid (the error is raised only against a live
    /// owner): what the refusal's holder classification resolves into a
    /// product flavor (this Rust build vs the TypeScript product).
    pub holder_pid: Option<u32>,
}

impl SessionAlreadyActiveError {
    /// The typed wire info for the refusal (`session_already_active`, the
    /// TS `serializeDaemonError` shape): the raw fields a client renders
    /// or acts on itself, carried beside the user-facing refusal text.
    #[must_use]
    pub fn error_info(&self) -> eukhe_types::daemon::DaemonErrorInfo {
        eukhe_types::daemon::DaemonErrorInfo::SessionAlreadyActive {
            session_path: self.session_path.clone(),
            active_session_id: self.active_session_id.clone(),
        }
    }

    fn for_owner(session_path: &str, owner: Option<&LeaseOwner>) -> Self {
        SessionAlreadyActiveError {
            session_path: session_path.to_string(),
            active_session_id: owner
                .and_then(|o| o.active_session_id.clone())
                .filter(|id| !id.is_empty()),
            // An owner without a session id is still identifiable by its
            // pid (the descriptive session-open error surfaces it).
            owner: owner
                .and_then(|o| o.active_session_id.clone())
                .filter(|id| !id.is_empty())
                .or_else(|| owner.map(|o| format!("another process (pid {})", o.pid)))
                .unwrap_or_else(|| "another process".to_string()),
            holder_pid: owner.map(|o| o.pid),
        }
    }
}

pub fn canonical_session_path(path: &Path) -> PathBuf {
    match path.canonicalize() {
        Ok(canonical) => canonical,
        Err(_) => match path.parent().map(std::path::Path::canonicalize) {
            Some(Ok(parent)) => parent.join(path.file_name().unwrap_or_default()),
            _ => path.to_path_buf(),
        },
    }
}

/// `proc:<starttime>` start identity (TS `getProcessStartId`); shared with
/// eukhe-core through `eukhe_types::platform`.
#[must_use]
pub fn get_process_start_id(pid: u32) -> Option<String> {
    eukhe_types::platform::process::process_start_id(pid)
}

/// True only for a process that is actually running: zombies do not count.
/// Errors when the platform cannot answer (the caller treats an unverifiable
/// owner as alive rather than reclaiming its lease).
///
/// # Errors
///
/// Returns an error when the platform cannot answer the liveness check.
pub fn is_process_alive(pid: u32) -> anyhow::Result<bool> {
    eukhe_types::platform::process::is_process_alive(pid)
}

fn lease_directory(agent_dir: &Path, session_path: &Path) -> PathBuf {
    let canonical = canonical_session_path(session_path);
    let key = Sha256::digest(canonical.to_string_lossy().as_bytes())
        .iter()
        .fold(String::new(), |mut key, b| {
            use std::fmt::Write;
            write!(key, "{b:02x}").expect("write to String");
            key
        });
    agent_dir.join("session-leases").join(format!("{key}.lock"))
}

fn leases_enabled() -> bool {
    matches!(
        std::env::var(SESSION_LEASES_ENABLED_ENV).as_deref(),
        Ok("1" | "true" | "yes")
    )
}

fn read_owner(directory: &Path) -> Result<Option<LeaseOwner>> {
    let owner_path = directory.join("owner.json");
    let content = match fs::read_to_string(&owner_path) {
        Ok(content) => content,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.into()),
    };
    let owner: LeaseOwner = serde_json::from_str(&content).map_err(|e| {
        anyhow!(
            "Corrupt session lease owner file: {} - {e}",
            owner_path.display()
        )
    })?;
    Ok(Some(owner))
}

fn owner_alive(owner: &LeaseOwner) -> bool {
    match is_process_alive(owner.pid) {
        Ok(true) => {}
        // A provably-dead owner is stale; an unverifiable one counts as
        // alive, like the TS lease (reclaiming a live owner is worse).
        Ok(false) => return false,
        Err(_) => return true,
    }
    match owner.process_start_id.as_deref() {
        None => true,
        Some(expected) => match get_process_start_id(owner.pid) {
            Some(current) => current == expected,
            // Unobservable identity counts as alive, like the TS lease.
            None => true,
        },
    }
}

fn lease_reclaimable(owner: Option<&LeaseOwner>) -> bool {
    owner.is_none_or(|owner| !owner_alive(owner))
}

/// Whether a failed candidate-onto-lease-directory rename means the lease
/// directory already exists (TS `isRenameTargetContention`): renaming onto
/// an existing directory raises EEXIST/ENOTEMPTY. EBUSY and permission
/// failures are never contention - they must propagate.
fn is_rename_target_contention(error: &std::io::Error) -> bool {
    matches!(
        error.kind(),
        std::io::ErrorKind::AlreadyExists | std::io::ErrorKind::DirectoryNotEmpty
    )
}

fn reclaim_stale(directory: &Path) -> bool {
    let stale = directory.with_extension(format!(
        "lock.stale-{}-{}",
        std::process::id(),
        uuid::Uuid::new_v4().simple()
    ));
    match fs::rename(directory, &stale) {
        Ok(()) => {
            let _ = fs::remove_dir_all(&stale);
            true
        }
        // The lease path is already free: nothing to reclaim.
        Err(error) => error.kind() == std::io::ErrorKind::NotFound,
    }
}

/// A guard older than this is stale and gets reclaimed (TS `stale: 5000`).
const STALE_GUARD_AFTER: Duration = Duration::from_secs(5);

/// Attempts before a fast guard acquisition surfaces its failure: the TS
/// `withLeaseGuard` budget of 100 retries at ~12ms.
const FAST_GUARD_ATTEMPTS: u32 = 100;

/// Wait past the stale window, covering the retry cadence between a
/// stale reclaim and the next acquisition attempt.
const THROUGH_STALE_SLACK: Duration = Duration::from_millis(500);

/// How long `release` drains an append already inside its write before the
/// lease directory is removed anyway: appends are file writes at most, so
/// this bounds a wedged device, not a normal turn.
const APPEND_DRAIN_AFTER: Duration = Duration::from_secs(10);

/// How long a guard acquisition waits for a foreign holder.
#[derive(Clone, Copy)]
enum GuardWait {
    /// The fast budget. The release path holds the guard only for its own
    /// sub-millisecond bookkeeping, so a guard that stays busy for longer
    /// belongs to a genuinely stuck peer and surfaces as a failure instead
    /// of stalling the caller.
    Fast,
    /// Outlast the stale window: a holder killed mid-mutation (kill -9)
    /// can never release its guard, so an acquisition on the create/open
    /// path must survive until the stale reclaim instead of failing
    /// while the reclaim is still seconds away.
    ThroughStale,
}

/// Serialize lease-directory mutations with a guard directory lock.
///
/// The guard is a bare `<lease>.guard` directory: TS (`proper-lockfile`)
/// reclaims a foreign guard by rmdir, so it must stay empty on every
/// platform. The holder removes it when the action ends; a holder that
/// dies mid-action leaves it behind, and only the `STALE_GUARD_AFTER`
/// mtime window reclaims it (a bare guard carries no holder identity to
/// consult). `GuardWait` picks whether an acquisition outlives that
/// window - a fresh guard of a dead holder blocks a session open forever
/// if the open gives up first.
fn with_lease_guard<T>(
    directory: &Path,
    wait: GuardWait,
    action: impl FnOnce() -> Result<T>,
) -> Result<T> {
    let guard = PathBuf::from(format!("{}.guard", directory.display()));
    let deadline = match wait {
        GuardWait::Fast => None,
        GuardWait::ThroughStale => {
            Some(std::time::Instant::now() + STALE_GUARD_AFTER + THROUGH_STALE_SLACK)
        }
    };
    let mut acquired = false;
    let mut attempt = 0u32;
    loop {
        match fs::create_dir(&guard) {
            Ok(()) => {
                acquired = true;
                break;
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                // Every contention consumes the budget, stale or not: a
                // reclaim that keeps failing (permissions, or a peer
                // re-creating the guard) must burn out like any other
                // busy guard instead of spinning past the deadline.
                attempt += 1;
                let exhausted = match deadline {
                    Some(deadline) => std::time::Instant::now() >= deadline,
                    None => attempt >= FAST_GUARD_ATTEMPTS,
                };
                if exhausted {
                    break;
                }
                // Stale guard: a holder that died without cleanup. The
                // bare guard carries no holder identity (TS reclaims a
                // foreign guard by rmdir, so it must stay empty), so the
                // lease's owner is the stand-in: steal only when the
                // owner is provably dead or the lease never finished
                // acquiring. A live owner may hold the guard mid-release;
                // the one contender a dead owner still allows - another
                // acquirer racing this one - is tolerated by acquire's own
                // contention retries. A successful reclaim retries
                // immediately; anything else falls through to the cadence
                // so it stays paced.
                if crate::paths::mtime_age(&guard).is_some_and(|age| age > STALE_GUARD_AFTER)
                    && match read_owner(directory) {
                        Ok(Some(owner)) => !owner_alive(&owner),
                        Ok(None) => true,
                        Err(_) => false,
                    }
                    && fs::remove_dir_all(&guard).is_ok()
                {
                    continue;
                }
                std::thread::sleep(Duration::from_millis(10 + u64::from(attempt % 5)));
            }
            Err(error) => return Err(error.into()),
        }
    }
    if !acquired {
        return Err(anyhow!(
            "Could not coordinate session lease: {}",
            directory.display()
        ));
    }
    let result = action();
    let _ = fs::remove_dir_all(&guard);
    result
}

/// A held session lease; release removes the directory when still owned.
#[derive(Debug)]
pub struct SessionLease {
    pub session_path: PathBuf,
    /// The path form the holder opened the file by: the process's window
    /// and scan caches key the file by it, so the release flushes both
    /// under it (`session_path` is the canonical identity; a symlinked
    /// sessions dir or macOS `/var` makes the two differ).
    opened_path: PathBuf,
    directory: PathBuf,
    token: String,
    released: std::sync::atomic::AtomicBool,
    /// Appends between `append`'s released-check and its write: `release`
    /// drains this before removing the lease directory, so no row lands
    /// behind a successor's acquire.
    append_in_flight: std::sync::atomic::AtomicUsize,
}

impl SessionLease {
    pub fn release(&self) {
        if self
            .released
            .swap(true, std::sync::atomic::Ordering::SeqCst)
        {
            return;
        }
        // Fence against a concurrent append: one already past its
        // released-check must land before the lease directory is removed,
        // or its row reaches the file after a successor acquires and the
        // window cache certifies a generation the new owner never saw.
        // New appends are refused from the swap above; this only drains
        // writes already in flight.
        let drain_deadline = Instant::now() + APPEND_DRAIN_AFTER;
        while self
            .append_in_flight
            .load(std::sync::atomic::Ordering::SeqCst)
            > 0
            && Instant::now() < drain_deadline
        {
            std::thread::yield_now();
        }
        let _ = eukhe_core::session::window::flush_cache(&self.opened_path);
        // The usage-scan sidecar persists beside the window snapshot, in
        // the same lease-keyed, best-effort shape: only the lease holder
        // writes, and a failed write costs the next open its warm resume,
        // nothing more.
        crate::session_store::persist_info_sidecar(&self.opened_path);
        let _ = with_lease_guard(&self.directory, GuardWait::Fast, || {
            if let Ok(Some(owner)) = read_owner(&self.directory) {
                if owner.token == self.token {
                    reclaim_stale(&self.directory);
                }
            }
            Ok(())
        });
    }
}

impl Drop for SessionLease {
    fn drop(&mut self) {
        self.release();
    }
}

impl SessionLease {
    pub(crate) fn acquire_target(&self, path: &Path) -> Result<std::sync::Arc<Self>> {
        let agent_dir = self
            .directory
            .parent()
            .and_then(Path::parent)
            .expect("lease directory has agent root");
        acquire_runtime_session_lease(path, agent_dir).map(std::sync::Arc::new)
    }

    /// Append one row under the held lease. The lease is exclusive from
    /// acquire to release, so the append takes no guard and re-reads no
    /// owner: the released-check plus the in-flight fence `release`
    /// drains is the whole ownership proof.
    pub(crate) fn append(&self, path: &Path, bytes: &[u8]) -> Result<()> {
        self.append_in_flight
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let result = (|| {
            anyhow::ensure!(
                !self.released.load(std::sync::atomic::Ordering::SeqCst)
                    && canonical_session_path(path) == self.session_path,
                "session lease does not own append target"
            );
            eukhe_core::session::window::append_cached(
                path,
                bytes,
                eukhe_core::session::window::AppendOwnership::SessionLeaseHeld,
            )?;
            Ok(())
        })();
        self.append_in_flight
            .fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
        result
    }
}

/// The live owner of a session file's runtime lease, when one exists: the
/// process identity another supervisor — or a surviving worker of any
/// daemon sharing this agent dir — would collide with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiveLeaseOwner {
    pub pid: u32,
    /// The owner's recorded active session id, when it carries one (the TS
    /// product and this port both stamp it): the holder identity the
    /// session-hold refusal names.
    pub active_session_id: Option<String>,
}

/// Whether a live process holds the session file's runtime lease: read the
/// shared `session-leases` ownership record (never acquiring, never
/// reclaiming) and keep only a provably-live owner. The lease table is the
/// one cross-daemon ownership record a shared agent dir offers, so the
/// automatic revival paths (boot adoption, the scheduled-work re-arm)
/// probe it before spawning a rival worker over a file another daemon's
/// worker already serves — one owning daemon. A dead owner, a missing
/// record, or an unreadable one answers `None` (a stale record is not
/// live ownership).
#[must_use]
pub fn live_lease_owner(agent_dir: &Path, session_path: &Path) -> Option<LiveLeaseOwner> {
    let directory = lease_directory(agent_dir, session_path);
    let owner = read_owner(&directory).ok()??;
    if !owner_alive(&owner) {
        return None;
    }
    Some(LiveLeaseOwner {
        pid: owner.pid,
        active_session_id: owner.active_session_id.filter(|id| !id.is_empty()),
    })
}

/// Acquire the lease for one session file. Returns `None` when leases are
/// disabled (default) or `session_path` is empty.
///
/// # Errors
///
/// Returns an error when the runtime acquire fails (another live owner
/// holds the lease, the lease guard stays busy past its wait budget, or
/// the lease directory or owner files cannot be created); the `Ok(None)`
/// answers never error.
pub fn acquire_session_lease(
    session_path: Option<&Path>,
    agent_dir: &Path,
) -> Result<Option<SessionLease>> {
    let Some(session_path) = session_path.filter(|p| !p.as_os_str().is_empty()) else {
        return Ok(None);
    };
    if !leases_enabled() {
        return Ok(None);
    }
    acquire_runtime_session_lease(session_path, agent_dir).map(Some)
}

/// Acquire mandatory runtime ownership before opening or writing a session.
/// The runtime acquire the daemon's workers use (ungated by the test
/// env flag): the CLI print-mode guard shares it so a resume either
/// atomically owns the file's runtime lease or answers the refusal -
/// no observe-then-open window for a second writer.
///
/// # Errors
///
/// Returns an error when another live owner already holds the lease
/// (`SessionAlreadyActiveError`), when the lease guard stays busy past
/// its wait budget, or when the lease directory or owner files cannot be
/// created.
pub fn acquire_runtime_session_lease(
    session_path: &Path,
    agent_dir: &Path,
) -> Result<SessionLease> {
    let canonical = canonical_session_path(session_path);
    let root = agent_dir.join("session-leases");
    fs::create_dir_all(&root)?;
    let directory = lease_directory(agent_dir, &canonical);

    // The open path outlasts the stale window: a guard left by a holder
    // killed mid-mutation can never be released by its dead owner, and
    // failing the relaunch while the stale reclaim is still seconds away
    // would leave a kill -9'd session unrevivable for the whole window.
    with_lease_guard(&directory, GuardWait::ThroughStale, || {
        for _ in 0..3 {
            let token = uuid::Uuid::new_v4().to_string();
            let candidate = directory.with_extension(format!(
                "lock.candidate-{}-{}",
                std::process::id(),
                uuid::Uuid::new_v4().simple()
            ));
            fs::create_dir_all(&candidate)?;
            let owner = LeaseOwner {
                version: 1,
                token: token.clone(),
                pid: std::process::id(),
                process_start_id: get_process_start_id(std::process::id()),
                active_session_id: std::env::var(SESSION_LEASE_OWNER_ID_ENV).ok(),
                session_path: canonical.to_string_lossy().to_string(),
                created_at: crate::util::now_iso(),
            };
            let owner_path = candidate.join("owner.json");
            fs::write(&owner_path, serde_json::to_string_pretty(&owner)? + "\n")?;
            match fs::rename(&candidate, &directory) {
                Ok(()) => {
                    return Ok(SessionLease {
                        session_path: canonical.clone(),
                        opened_path: session_path.to_path_buf(),
                        directory: directory.clone(),
                        token,
                        released: std::sync::atomic::AtomicBool::new(false),
                        append_in_flight: std::sync::atomic::AtomicUsize::new(0),
                    });
                }
                Err(error) => {
                    let _ = fs::remove_dir_all(&candidate);
                    if error.kind() == std::io::ErrorKind::NotFound {
                        continue;
                    }
                    if is_rename_target_contention(&error) {
                        let existing = read_owner(&directory)?;
                        if !lease_reclaimable(existing.as_ref()) {
                            return Err(SessionAlreadyActiveError::for_owner(
                                &canonical.to_string_lossy(),
                                existing.as_ref(),
                            )
                            .into());
                        }
                        reclaim_stale(&directory);
                        continue;
                    }
                    return Err(error.into());
                }
            }
        }
        let existing = read_owner(&directory)?;
        if !lease_reclaimable(existing.as_ref()) {
            return Err(SessionAlreadyActiveError::for_owner(
                &canonical.to_string_lossy(),
                existing.as_ref(),
            )
            .into());
        }
        Err(anyhow!(
            "Could not acquire session lease: {}",
            canonical.display()
        ))
    })
}

/// The boot sweep of `<agent-dir>/session-leases`: reclaim every lease
/// directory whose owner is provably dead (or missing), under the same
/// guard and liveness rule the acquire path uses, and remove leftover
/// `.lock.stale-*` directories of interrupted reclaims. A live owner and an
/// unreadable owner record keep their lease. Returns the removal count.
pub(crate) fn reclaim_dead_owner_leases(agent_dir: &Path) -> usize {
    let root = agent_dir.join("session-leases");
    let Ok(entries) = fs::read_dir(&root) else {
        return 0;
    };
    let mut removed = 0;
    for entry in entries.flatten() {
        let path = entry.path();
        if !entry.file_type().is_ok_and(|file_type| file_type.is_dir()) {
            continue;
        }
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if std::path::Path::new(name)
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case("lock"))
        {
            let reclaimed = with_lease_guard(&path, GuardWait::Fast, || {
                let existing = read_owner(&path)?;
                Ok(lease_reclaimable(existing.as_ref()) && reclaim_stale(&path))
            });
            if reclaimed.unwrap_or(false) {
                removed += 1;
            }
        } else if name.contains(".lock.stale-") && fs::remove_dir_all(&path).is_ok() {
            removed += 1;
        }
    }
    removed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn process_start_id_reflects_the_platform_ladder() {
        // Linux answers from /proc (`proc:`); macOS/BSD answer
        // `ps:<lstart>` - the same ladder TS `getProcessStartId` walks.
        let start = get_process_start_id(std::process::id());
        assert!(start.is_some());
        let id = start.unwrap();
        assert!(id.starts_with("proc:") || id.starts_with("ps:"));
        assert!(get_process_start_id(0).is_none());
    }

    #[test]
    fn runtime_lease_is_mandatory_and_shared_until_last_owner_drops() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("session.jsonl");
        std::fs::write(&path, "{}").unwrap();
        let lease = std::sync::Arc::new(acquire_runtime_session_lease(&path, dir.path()).unwrap());
        let shared = lease.clone();
        assert!(acquire_runtime_session_lease(&path, dir.path()).is_err());
        drop(lease);
        assert!(acquire_runtime_session_lease(&path, dir.path()).is_err());
        drop(shared);
        let next = acquire_runtime_session_lease(&path, dir.path()).unwrap();
        assert_eq!(next.session_path, canonical_session_path(&path));
    }

    #[test]
    fn lease_conflicts_and_releases() {
        let dir = std::env::temp_dir().join(format!("pa-lease-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir_all(&dir).unwrap();
        std::env::set_var(SESSION_LEASES_ENABLED_ENV, "1");
        let session = dir.join("s.jsonl");
        std::fs::write(&session, "{}").unwrap();
        let lease = acquire_session_lease(Some(&session), &dir)
            .unwrap()
            .unwrap();
        // Second holder conflicts.
        let err = acquire_session_lease(Some(&session), &dir).unwrap_err();
        assert!(err.to_string().contains("already active"));
        lease.release();
        // Released lease can be acquired again.
        let second = acquire_session_lease(Some(&session), &dir)
            .unwrap()
            .unwrap();
        second.release();
        std::env::remove_var(SESSION_LEASES_ENABLED_ENV);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn the_dead_owner_sweep_spares_live_and_unreadable_leases() {
        let dir = tempfile::tempdir().unwrap();
        let agent_dir = dir.path();
        let live_path = agent_dir.join("live.jsonl");
        std::fs::write(&live_path, "{}\n").unwrap();
        let live = acquire_runtime_session_lease(&live_path, agent_dir).unwrap();
        let dead_directory = {
            let dead_path = agent_dir.join("dead.jsonl");
            std::fs::write(&dead_path, "{}\n").unwrap();
            let directory = lease_directory(agent_dir, &canonical_session_path(&dead_path));
            fs::create_dir_all(&directory).unwrap();
            let owner = LeaseOwner {
                version: 1,
                token: "dead-holder".to_owned(),
                pid: 0,
                process_start_id: get_process_start_id(0),
                active_session_id: None,
                session_path: canonical_session_path(&dead_path)
                    .to_string_lossy()
                    .to_string(),
                created_at: crate::util::now_iso(),
            };
            fs::write(
                directory.join("owner.json"),
                serde_json::to_string_pretty(&owner).unwrap() + "\n",
            )
            .unwrap();
            directory
        };
        let stale_leftover = dead_directory.with_extension("lock.stale-1-abc");
        fs::create_dir_all(&stale_leftover).unwrap();
        let corrupt_directory = {
            let corrupt_path = agent_dir.join("corrupt.jsonl");
            std::fs::write(&corrupt_path, "{}\n").unwrap();
            let directory = lease_directory(agent_dir, &canonical_session_path(&corrupt_path));
            fs::create_dir_all(&directory).unwrap();
            fs::write(directory.join("owner.json"), "not json").unwrap();
            directory
        };

        assert_eq!(
            reclaim_dead_owner_leases(agent_dir),
            2,
            "the dead owner and the stale leftover are the only removals"
        );
        assert!(!dead_directory.exists());
        assert!(!stale_leftover.exists());
        assert!(
            corrupt_directory.exists(),
            "an unreadable owner keeps its lease, like the acquire path"
        );
        live.append(&live_path, b"row\n")
            .expect("the live lease still owns its append");
        live.release();
    }

    /// The state a kill -9 mid-mutation leaves behind: a lease owned by
    /// a dead process plus a brand-new guard its dead holder can never
    /// remove. The open path must wait out the stale window and reclaim
    /// both instead of failing while the reclaim is still seconds away.
    #[test]
    fn create_path_outlasts_a_fresh_guard_of_a_dead_holder() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("session.jsonl");
        std::fs::write(&path, "{}\n").unwrap();
        // `pid: 0` is provably dead through the same liveness ladder the
        // reclaimer applies to real crashed holders.
        let owner = LeaseOwner {
            version: 1,
            token: "dead-holder".to_owned(),
            pid: 0,
            process_start_id: get_process_start_id(0),
            active_session_id: None,
            session_path: canonical_session_path(&path).to_string_lossy().to_string(),
            created_at: crate::util::now_iso(),
        };
        let directory = lease_directory(dir.path(), &canonical_session_path(&path));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join("owner.json"),
            serde_json::to_string_pretty(&owner).unwrap() + "\n",
        )
        .unwrap();
        std::fs::create_dir(format!("{}.guard", directory.display())).unwrap();
        let started = std::time::Instant::now();
        let lease = acquire_runtime_session_lease(&path, dir.path()).unwrap();
        // The guard was brand new: a fresh guard is never stolen early,
        // so success proves the open waited out the stale window. The
        // guard ages from its creation, a hair before `started`, so the
        // bound allows that setup gap.
        let elapsed = started.elapsed();
        assert!(
            elapsed >= STALE_GUARD_AFTER.saturating_sub(Duration::from_millis(250)),
            "the fresh guard was not waited out: {elapsed:?}"
        );
        // Generous ceiling: the reclaim fires right after the window, and
        // only a scheduler stall between iterations can stretch the gap.
        assert!(
            elapsed < STALE_GUARD_AFTER + THROUGH_STALE_SLACK + Duration::from_secs(10),
            "the stale reclaim overran its window: {elapsed:?}"
        );
        lease.release();
    }

    /// A guard past the stale window whose lease owner is alive is never
    /// stolen: the open path waits out its deadline and fails instead of
    /// breaking the live owner's append serialization (the bare guard
    /// carries no identity, so the owner's liveness is all a steal can
    /// consult).
    #[test]
    fn stale_guard_of_a_live_owner_is_never_stolen() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("session.jsonl");
        std::fs::write(&path, "{}\n").unwrap();
        let lease = acquire_runtime_session_lease(&path, dir.path()).unwrap();
        let guard = format!("{}.guard", lease.directory.display());
        std::fs::create_dir(&guard).unwrap();
        let old = std::time::SystemTime::now() - STALE_GUARD_AFTER - Duration::from_secs(1);
        std::fs::File::open(&guard)
            .unwrap()
            .set_modified(old)
            .unwrap();
        let started = std::time::Instant::now();
        let error = acquire_runtime_session_lease(&path, dir.path()).unwrap_err();
        let elapsed = started.elapsed();
        assert!(
            error
                .to_string()
                .contains("Could not coordinate session lease"),
            "unexpected error: {error}"
        );
        assert!(
            elapsed >= STALE_GUARD_AFTER,
            "the wait was cut short: {elapsed:?}"
        );
        assert!(
            elapsed < STALE_GUARD_AFTER + THROUGH_STALE_SLACK + Duration::from_secs(10),
            "the wait overran its deadline: {elapsed:?}"
        );
        assert!(
            std::fs::symlink_metadata(&guard)
                .unwrap()
                .file_type()
                .is_dir(),
            "the live owner's guard was stolen"
        );
        std::fs::remove_dir(&guard).unwrap();
        lease.release();
    }

    /// A stale-guard reclaim whose removal keeps failing must burn the
    /// budget instead of spinning past it on immediate retries.
    #[test]
    fn stale_guard_reclaim_failure_stays_bounded() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("session.jsonl");
        std::fs::write(&path, "{}\n").unwrap();
        // A dead owner (pid 0) whose guard reads stale but can never be
        // reclaimed: `remove_dir_all` on a plain file fails on every
        // retry, root included, so the open must pace itself out.
        let owner = LeaseOwner {
            version: 1,
            token: "dead-holder".to_owned(),
            pid: 0,
            process_start_id: get_process_start_id(0),
            active_session_id: None,
            session_path: canonical_session_path(&path).to_string_lossy().to_string(),
            created_at: crate::util::now_iso(),
        };
        let directory = lease_directory(dir.path(), &canonical_session_path(&path));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join("owner.json"),
            serde_json::to_string_pretty(&owner).unwrap() + "\n",
        )
        .unwrap();
        let guard = format!("{}.guard", directory.display());
        std::fs::write(&guard, b"stale").unwrap();
        let old = std::time::SystemTime::now() - STALE_GUARD_AFTER - Duration::from_secs(1);
        std::fs::File::open(&guard)
            .unwrap()
            .set_modified(old)
            .unwrap();
        let started = std::time::Instant::now();
        let error = acquire_runtime_session_lease(&path, dir.path()).unwrap_err();
        let elapsed = started.elapsed();
        assert!(
            error
                .to_string()
                .contains("Could not coordinate session lease"),
            "unexpected open error: {error}"
        );
        assert!(
            elapsed < STALE_GUARD_AFTER + THROUGH_STALE_SLACK + Duration::from_secs(2),
            "the failed reclaim outlived its deadline: {elapsed:?}"
        );
        std::fs::remove_file(&guard).unwrap();
        let _ = fs::remove_dir_all(&directory);
    }

    #[test]
    fn rename_target_contention_covers_exist_and_not_empty() {
        // TS: EEXIST and ENOTEMPTY are contention.
        for kind in [
            std::io::ErrorKind::AlreadyExists,
            std::io::ErrorKind::DirectoryNotEmpty,
        ] {
            assert!(is_rename_target_contention(&std::io::Error::from(kind)));
        }
    }

    #[test]
    fn rename_target_contention_ignores_unrelated_failures() {
        // TS: EBUSY, permission and other codes are never contention (a
        // shared-open destination must surface, not read as a conflict).
        for error in [
            std::io::Error::from(std::io::ErrorKind::Other),
            std::io::Error::from(std::io::ErrorKind::PermissionDenied),
            std::io::Error::from(std::io::ErrorKind::ResourceBusy),
        ] {
            assert!(!is_rename_target_contention(&error));
        }
    }

    #[test]
    fn release_drains_an_append_still_in_flight() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("session.jsonl");
        std::fs::write(&path, "{}").unwrap();
        let lease = std::sync::Arc::new(acquire_runtime_session_lease(&path, dir.path()).unwrap());
        // An append past its released-check, still inside its write.
        lease
            .append_in_flight
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let directory = lease.directory.clone();
        let releaser = {
            let lease = std::sync::Arc::clone(&lease);
            std::thread::spawn(move || lease.release())
        };
        // The release flips `released` before it drains: once the flag is
        // up, the releaser is parked on the in-flight append.
        while !lease.released.load(std::sync::atomic::Ordering::SeqCst) {
            std::thread::yield_now();
        }
        assert!(
            directory.exists(),
            "release must wait for the append still in flight"
        );
        lease
            .append_in_flight
            .fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
        releaser.join().unwrap();
        assert!(
            !directory.exists(),
            "release reclaims the lease once the append lands"
        );
    }
}
