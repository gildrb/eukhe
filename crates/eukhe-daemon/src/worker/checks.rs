//! The session's check feed as events: each report of a child's
//! hand-back check (its start, each interval while it runs, its end) goes
//! out as one `check_update` event with its status line, which the TUI's
//! status line and transcript show.

use std::sync::{Arc, Mutex};

use eukhe_types::daemon::agent_tree::CheckProgress;
use eukhe_types::daemon::SessionEvent;
use tokio::sync::broadcast::{error::RecvError, Receiver};

use super::{emit_event_locked, EventPump, SessionCore};

/// Send each report of `checks` as a `check_update` event. Ends with the
/// session's feed, or when another follow took its place (`epoch` is no
/// longer the core's budget epoch, which every follow moves).
#[tracing::instrument(skip_all)]
pub(super) async fn forward_checks(
    mut checks: Receiver<CheckProgress>,
    epoch: u64,
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
) {
    loop {
        match checks.recv().await {
            Ok(check) => {
                let mut core = core
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                if core.budget_epoch != epoch {
                    return;
                }
                let text = check.text();
                emit_event_locked(
                    &mut core,
                    &events,
                    SessionEvent::CheckUpdate { check, text },
                );
            }
            // A report missed while the forwarder lagged is not sent
            // again: the next one (at most an interval later) is.
            Err(RecvError::Lagged(_)) => {}
            Err(RecvError::Closed) => return,
        }
    }
}
