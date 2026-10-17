//! Generated session titles (S9, the `tiny` role): the first user prompt
//! of a top-level, unnamed session starts one background title request
//! (`eukhe_core::tiny::title`). The prompt's admission and its turn never
//! wait for it; the title lands through the session-name path (the
//! durable name, `session_info_changed`, the roster) only while the
//! session is still the hosted one and still unnamed. A failure is logged
//! and leaves the session untitled.

use std::sync::atomic::Ordering;
use std::sync::{Arc, Weak};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::tiny::title::{generate_title, TitleOutcome, TitleRequest};
use eukhe_core::tiny::TinyHome;

use super::{HostedSession, Worker};

impl Worker {
    /// Starts the title of `message` when it is the first user prompt of a
    /// top-level session with no name; at most once per worker. A scripted
    /// session (the faux-script verification seam) takes no title: its
    /// script answers the session's requests from one queue, in order, and
    /// a title request would take a turn's answer.
    pub(crate) fn start_title(&self, hosted: &Arc<HostedSession>, message: &str) {
        let text = message.trim();
        // A slash command is no conversation subject.
        if text.is_empty() || text.starts_with('/') || self.scripted_models.get().is_some() {
            return;
        }
        let Some(worker) = self.this.get().and_then(Weak::upgrade) else {
            return;
        };
        {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let top_level = core.rlm_depth == 0
                && core.parent_session_id.is_none()
                && core.parent_active_session_id.is_none()
                && core.rlm_child_id.is_none();
            let first = core
                .view
                .as_ref()
                .is_none_or(|view| super::summary::first_message(view).is_none());
            if !top_level || core.session_name.is_some() || !first {
                return;
            }
        }
        if self.title_started.swap(true, Ordering::SeqCst) {
            return;
        }
        let weak = Arc::downgrade(&worker);
        drop(worker);
        let hosted = Arc::clone(hosted);
        let text = text.to_owned();
        tokio::spawn(async move { title_session(weak, hosted, text).await });
    }
}

/// Generates the title and stores it.
#[tracing::instrument(skip_all)]
async fn title_session(worker: Weak<Worker>, hosted: Arc<HostedSession>, message: String) {
    let deps = Arc::clone(hosted.deps());
    let settings = deps.settings.manager();
    let session_model = match hosted.main() {
        Ok(main) => match main.agent(&BACKGROUND_CONTEXT).await {
            Ok(agent) => agent
                .model
                .and_then(|model| deps.models.get_model(&model.provider, &model.model_id)),
            Err(_) => None,
        },
        Err(_) => None,
    };
    let worker_exe = match eukhe_core::tiny::worker_exe() {
        Ok(exe) => exe,
        Err(error) => {
            eprintln!(
                "eukhe-daemon worker: no session title: the eukhe executable is unknown: {error}"
            );
            return;
        }
    };
    let home = TinyHome::under(&deps.agent_dir);
    let client = eukhe_core::tiny::client(&deps.agent_dir, settings.cvars(), worker_exe);
    let outcome = generate_title(TitleRequest {
        first_message: &message,
        cvars: settings.cvars(),
        home: &home,
        client: &client,
        models: &deps.models,
        session_model: session_model.as_ref(),
    })
    .await;
    let title = match outcome {
        Ok(TitleOutcome::Titled(title)) => title,
        Ok(TitleOutcome::Disabled | TitleOutcome::Unavailable | TitleOutcome::Empty) => return,
        Err(error) => {
            eprintln!("eukhe-daemon worker: no session title: {error}");
            return;
        }
    };
    let Some(worker) = worker.upgrade() else {
        return;
    };
    // The session-name path, under the rename gate: a name the user set
    // meanwhile wins, and a replaced session is not this one.
    let _rename = worker.rename_gate.lock().await;
    let current = worker
        .session
        .get()
        .is_some_and(|current| Arc::ptr_eq(&current, &hosted));
    let named = worker
        .core
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .session_name
        .is_some();
    if !current || named {
        return;
    }
    if let Err(error) = worker.commit_session_name(&hosted, &title).await {
        eprintln!("eukhe-daemon worker: the session title failed to commit: {error}");
    }
}
