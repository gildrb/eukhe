//! The worker's end when its durable Harness fails. A failed Harness (a
//! Storage error closes its Session) runs nothing more, so the worker
//! cannot serve the session any longer: it records the typed failure in
//! the recovery journal, closes the session, and exits non-zero. The
//! supervisor's restart path then revives the session from Storage, where
//! its run and its queued inputs survive (ADR 0004: lifecycle derives from
//! durable state, so the reopened Harness resumes what it holds).

use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::session::SessionEnd;

use super::{HostedSession, Worker};
use crate::journal::WorkerFailure;

/// The worker's exit status after its Harness failed (`EX_TEMPFAIL`: the
/// session is retried by its revival).
pub(crate) const HARNESS_FAILED_EXIT_CODE: i32 = 75;

impl Worker {
    /// Watch `hosted`'s Harness end: a failure of the session this worker
    /// still hosts arms [`Worker::retire_failed_harness`]. A session the
    /// worker closed (shutdown, kill) or replaced ended on purpose.
    pub(crate) fn watch_harness_end(&self, hosted: &Arc<HostedSession>) {
        let ended = hosted.harness().closed();
        let slot = self.session.clone();
        let failure = self.harness_failure.clone();
        let watched = Arc::clone(hosted);
        tokio::spawn(async move {
            match ended.await {
                SessionEnd::Closed => {}
                SessionEnd::Failed { error } => {
                    let hosted_still = slot
                        .get()
                        .is_some_and(|current| Arc::ptr_eq(&current, &watched));
                    if hosted_still && watched.session().is_ok() {
                        failure.send_replace(Some(WorkerFailure::HarnessFailed {
                            error: error.to_string(),
                        }));
                    }
                }
            }
        });
    }

    /// Resolves once the hosted session's Harness failed, after the worker
    /// retired it: the typed failure is in the recovery journal (busy, so
    /// a boot adoption revives it too), and the session is closed, its
    /// lease released. The caller exits for the revival.
    pub(crate) async fn retire_failed_harness(&self) -> WorkerFailure {
        let mut failed = self.harness_failure.subscribe();
        let failure = loop {
            if let Some(failure) = failed.borrow_and_update().clone() {
                break failure;
            }
            // The sender lives as long as the worker.
            if failed.changed().await.is_err() {
                std::future::pending::<()>().await;
            }
        };
        let (active_session_id, session_id, session_file) = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            (
                core.active_session_id.clone(),
                core.session_id.clone(),
                core.session_file(),
            )
        };
        if let Some(journal) = self
            .recovery
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .as_mut()
        {
            if let Err(error) = journal.record_failure(
                &active_session_id,
                &session_id,
                session_file.as_deref(),
                failure.clone(),
            ) {
                eprintln!("eukhe-daemon worker: recording the harness failure failed: {error:#}");
            }
        }
        if let Some(hosted) = self.session.take() {
            if let Err(error) = hosted.close(&BACKGROUND_CONTEXT).await {
                eprintln!("eukhe-daemon worker: closing the failed session: {error}");
            }
        }
        failure
    }
}
