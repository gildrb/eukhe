//! The chat memory's live progress on the wire: while the worker's
//! installed session keeps a chat memory, every compactor update the memory
//! reports goes out as one ephemeral `memory_update` session event (display
//! only, like `chat_turn_wait`: never journaled, never in the transcript).

use std::sync::{Arc, Mutex};

use eukhe_types::daemon::SessionEvent;

use super::summary::emit_worker_event_with;
use super::{EventPump, SessionCore, Worker};

impl Worker {
    /// Follow `memory` (the installed session's chat memory; `None` for a
    /// session without one): the previous forwarder stops, and a new one
    /// forwards `memory`'s updates until the next follow or
    /// [`Worker::stop_memory_updates`].
    pub(crate) fn follow_memory_updates(&self, memory: Option<&eukhe_core::memory::Memory>) {
        let task = memory.map(|memory| {
            tokio::spawn(forward_memory_updates(
                memory.clone(),
                Arc::clone(&self.core),
                Arc::clone(&self.events),
            ))
        });
        let previous = std::mem::replace(
            &mut *self
                .memory_updates
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            task,
        );
        if let Some(previous) = previous {
            previous.abort();
        }
    }

    /// Stop forwarding memory updates (the session closed).
    pub(crate) fn stop_memory_updates(&self) {
        self.follow_memory_updates(None);
    }
}

/// Forward every update `memory` reports as a `memory_update` event. The
/// subscription follows owner changes by itself; an error means the memory
/// is unusable, so the forwarder reports it once and stops.
async fn forward_memory_updates(
    memory: eukhe_core::memory::Memory,
    core: Arc<Mutex<SessionCore>>,
    events: Arc<EventPump>,
) {
    let mut updates = match memory.subscribe().await {
        Ok(updates) => updates,
        Err(error) => {
            eprintln!("eukhe-daemon worker: subscribing to chat memory updates failed: {error:#}");
            return;
        }
    };
    loop {
        match updates.next().await {
            Ok(update) => {
                emit_worker_event_with(&core, &events, SessionEvent::MemoryUpdate { update });
            }
            Err(error) => {
                eprintln!("eukhe-daemon worker: chat memory updates stopped: {error:#}");
                return;
            }
        }
    }
}
