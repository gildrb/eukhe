//! `eukhe.optchat`: the chat memory in a durable session (`OptChat` spec
//! §1, §3.3, §6). Each session is its own thread: a root conversation logs
//! everything it says and does to the session's own chat and sends its own
//! transcript verbatim, after the view of the history that scrolled out of
//! it; a subagent starts from the view at its first request and logs
//! nothing to the chat (its own steps stay in its own session).
//!
//! - Tools `zoom(id, n)`, `zoom("Name")` and `date(id)`, in every session
//!   (the same tool list with or without chat memory, [`tools`]).
//! - `pi.generation` `before_request`: a root call's request is its
//!   transcript with the pinned view (`eukhe.optchat.call`) of the older
//!   history leading its first user message; a subagent's is the view with
//!   its leading user texts as ONE user message, then the rest
//!   ([`request`]).
//! - The post-commit logger (root sessions): appends finished entries to
//!   the chat log with idempotent keys and a durable cursor
//!   (`eukhe.optchat.logged`), and gives the root-turn lease back when the
//!   session's runs end ([`logger`]).

mod docs;
mod lines;
mod logger;
pub(crate) mod request;
mod tools;

#[cfg(test)]
mod tests;

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_durable::harness::define::{define_extension, hook};
use eukhe_durable::harness::types::{Extension, GenerationHooks};
use eukhe_durable::harness::GENERATION_TASK;
use eukhe_durable::session::{SessionError, SessionResult};
use futures::FutureExt;

pub use docs::{CallState, LoggedState, CALL_DOC, LOGGED_DOC};
pub(crate) use tools::agent_chat;

use super::{EukheSettings, HarnessCell, HostDeps};
use crate::memory::{Memory, MemoryRole};
use logger::{LoggerLink, LoggerRequest};

/// The extension name.
pub const EXTENSION_NAME: &str = "eukhe.optchat";

/// The `eukhe.optchat` extension: in a session with chat memory its tools,
/// generation hooks and (root sessions) the chat logger, started when the
/// session opens; without, only the tools, whose memory reads refuse.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let Some(memory) = deps.memory.clone() else {
        return define_extension(Extension {
            tools: tools::memory_tools(None),
            ..Extension::named(EXTENSION_NAME)
        });
    };
    let chat = OptChat::new(
        memory,
        deps.role.memory_role(),
        deps.session_id.clone(),
        Arc::clone(&deps.settings),
        deps.harness.clone(),
    );
    // Weakly: the extension's hooks own the chat memory.
    let _first_extension_wins = deps.optchat.set(Arc::downgrade(&chat));
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
    chat.extension()
}

/// One session's chat memory: shared by its hooks, tools, and logger.
pub(crate) struct OptChat {
    memory: Memory,
    role: MemoryRole,
    /// Scopes the logger's append keys (one scope per conversation).
    session_id: String,
    /// `memory.settleTimeoutMs`: how long a call waits for the view.
    settings: Arc<EukheSettings>,
    harness: HarnessCell,
    /// The running logger (root sessions, while open).
    logger: Mutex<Option<LoggerLink>>,
}

impl OptChat {
    pub(crate) fn new(
        memory: Memory,
        role: MemoryRole,
        session_id: String,
        settings: Arc<EukheSettings>,
        harness: HarnessCell,
    ) -> Arc<Self> {
        Arc::new(Self {
            memory,
            role,
            session_id,
            settings,
            harness,
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
            tools: tools::memory_tools(Some(self.memory.clone())),
            hooks: vec![hook(&*GENERATION_TASK, generation)],
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
