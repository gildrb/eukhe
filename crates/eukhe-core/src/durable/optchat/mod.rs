//! `eukhe.optchat`: the chat memory in a durable session (`OptChat` spec
//! §6-§9). A root conversation logs everything it says and does to the
//! endless chat and starts every call (run) from the settled view; a
//! subagent starts from the view at its first request and logs nothing.
//!
//! - Tools `zoom(id, n)` and `date(id)`.
//! - `pi.generation` `before_request`: the call's request — the pinned
//!   view (`eukhe.optchat.call`) with the call's leading user texts as ONE
//!   user message, then the rest of the call; what came before the call is
//!   in the chat log and dropped ([`request`]).
//! - `pi.tool` `after_tool`: tool results capped at [`crate::memory::CAP`].
//! - The post-commit logger (root sessions): appends finished entries to
//!   the chat log with idempotent keys and a durable cursor
//!   (`eukhe.optchat.logged`), and gives the root-turn lease back when the
//!   session's runs end ([`logger`]).

mod docs;
mod lines;
mod logger;
pub(crate) mod request;
mod tools;
mod turn;

#[cfg(test)]
mod tests;

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_durable::harness::define::{define_extension, hook};
use eukhe_durable::harness::types::{Extension, GenerationHooks};
use eukhe_durable::harness::{GENERATION_TASK, TOOL_TASK};
use eukhe_durable::session::{SessionError, SessionResult};
use futures::FutureExt;

pub use docs::{CallState, LoggedState, CALL_DOC, LOGGED_DOC};

use super::{HarnessCell, HostDeps, TurnWaitSink};
use crate::memory::{Memory, MemoryRole};
use logger::{LoggerLink, LoggerRequest};
use turn::RootTurn;

/// The extension name.
pub const EXTENSION_NAME: &str = "eukhe.optchat";

/// The `eukhe.optchat` extension of a session with chat memory; `None`
/// without. A root session also starts the chat logger when it opens.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Option<Arc<Extension>> {
    let memory = deps.memory.clone()?;
    let chat = OptChat::new(
        memory,
        deps.role.memory_role(),
        deps.session_id.clone(),
        deps.harness.clone(),
        deps.turn_wait.clone(),
    );
    if chat.role == MemoryRole::Root {
        let logged = Arc::clone(&chat);
        deps.add_service(Box::new(move |opened| {
            async move {
                let handle = logged.start_logger(opened.harness).await?;
                let stop: super::ServiceStop = Box::new(move || handle.stop().boxed());
                Ok(Some(stop))
            }
            .boxed()
        }));
    }
    Some(chat.extension())
}

/// One session's chat memory: shared by its hooks, tools, and logger.
pub(crate) struct OptChat {
    memory: Memory,
    role: MemoryRole,
    /// Scopes the logger's append keys (one scope per conversation).
    session_id: String,
    harness: HarnessCell,
    turn_wait: Option<TurnWaitSink>,
    turn: RootTurn,
    /// The running logger (root sessions, while open).
    logger: Mutex<Option<LoggerLink>>,
}

impl OptChat {
    pub(crate) fn new(
        memory: Memory,
        role: MemoryRole,
        session_id: String,
        harness: HarnessCell,
        turn_wait: Option<TurnWaitSink>,
    ) -> Arc<Self> {
        Arc::new(Self {
            memory,
            role,
            session_id,
            harness,
            turn_wait,
            turn: RootTurn::default(),
            logger: Mutex::new(None),
        })
    }

    /// The extension: tools and hooks.
    pub(crate) fn extension(self: &Arc<Self>) -> Arc<Extension> {
        let chat = Arc::clone(self);
        let generation = GenerationHooks {
            before_request: Some(Arc::new(move |request, api, cx| {
                request::transform(Arc::clone(&chat), request.clone(), api.clone(), cx.clone())
                    .boxed()
            })),
            ..GenerationHooks::default()
        };
        define_extension(Extension {
            tools: tools::memory_tools(&self.memory),
            hooks: vec![
                hook(&*GENERATION_TASK, generation),
                hook(&*TOOL_TASK, tools::cap_hooks()),
            ],
            ..Extension::named(EXTENSION_NAME)
        })
    }

    /// Start the post-commit logger over `harness`.
    ///
    /// # Errors
    ///
    /// The cursors of the root conversations cannot be read or created.
    pub(crate) async fn start_logger(
        self: &Arc<Self>,
        harness: eukhe_durable::harness::Harness,
    ) -> SessionResult<logger::LoggerHandle> {
        logger::start(Arc::clone(self), harness).await
    }

    /// Wait until every entry of the root conversations that their runs
    /// do not hold back (everything before a run's start until its call
    /// pins its view) is in the chat log.
    async fn flush(&self) -> SessionResult<()> {
        let Some(link) = self.link() else {
            return Err(SessionError::error("the chat logger is not running"));
        };
        link.request(LoggerRequest::Flush).await
    }

    /// Have the logger look at the committed state again.
    fn wake(&self) {
        if let Some(link) = self.link() {
            link.wake();
        }
    }

    fn link(&self) -> Option<LoggerLink> {
        self.logger
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    fn set_link(&self, link: Option<LoggerLink>) {
        *self.logger.lock().unwrap_or_else(PoisonError::into_inner) = link;
    }
}
