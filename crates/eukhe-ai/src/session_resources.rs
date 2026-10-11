//! Process-wide session resource cleanup hooks. Port of `session-resources.ts`.
//!
//! API modules that hold per-session resources (for example cached WebSocket
//! connections) register a cleanup here; the app calls
//! [`cleanup_session_resources`] when a session ends.

use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use crate::utils::diagnostics::Thrown;

/// Releases resources of one session, or of every session when given `None`.
pub type SessionResourceCleanup = Arc<dyn Fn(Option<&str>) -> Result<(), Thrown> + Send + Sync>;

/// Registered cleanups in registration order. Like the TS `Set`, registering
/// the same cleanup (same `Arc`) twice keeps one entry.
static SESSION_RESOURCE_CLEANUPS: LazyLock<Mutex<Vec<SessionResourceCleanup>>> =
    LazyLock::new(|| Mutex::new(Vec::new()));

fn cleanups() -> std::sync::MutexGuard<'static, Vec<SessionResourceCleanup>> {
    SESSION_RESOURCE_CLEANUPS
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
}

/// Registers `cleanup` and returns the function that unregisters it.
pub fn register_session_resource_cleanup(
    cleanup: SessionResourceCleanup,
) -> impl Fn() + Send + Sync + 'static {
    {
        let mut registered = cleanups();
        if !registered.iter().any(|entry| Arc::ptr_eq(entry, &cleanup)) {
            registered.push(Arc::clone(&cleanup));
        }
    }
    move || cleanups().retain(|entry| !Arc::ptr_eq(entry, &cleanup))
}

/// Failure of one or more cleanups: the TS `AggregateError`.
#[derive(Debug, Clone, thiserror::Error)]
#[error("Failed to cleanup session resources")]
pub struct SessionResourceCleanupError {
    /// Every cleanup failure, in registration order.
    pub errors: Vec<Thrown>,
}

/// Runs every registered cleanup, continuing past failures.
///
/// # Errors
///
/// Returns [`SessionResourceCleanupError`] with every failure when at least
/// one cleanup failed.
pub fn cleanup_session_resources(
    session_id: Option<&str>,
) -> Result<(), SessionResourceCleanupError> {
    // Snapshot so a cleanup may (un)register cleanups without deadlocking.
    let snapshot: Vec<SessionResourceCleanup> = cleanups().clone();
    let errors: Vec<Thrown> = snapshot
        .iter()
        .filter_map(|cleanup| cleanup(session_id).err())
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(SessionResourceCleanupError { errors })
    }
}
