//! The session-navigation surface: the worker arms for `new_session`,
//! `switch_session`, and `import_jsonl` (TS daemon-mode cases over
//! `AgentSessionRuntime.newSession` / `switchSession` / `importFromJsonl`).
//! All three replace the worker's hosted session with another durable
//! session (the TS runtime's replacement path).
//!
//! Replacement order (TS parity): the replacement target is prepared and
//! validated first — a missing switch target, a missing import file, a
//! stored cwd that no longer exists, or a session another process holds
//! fails here and leaves the live session, its kernels, and any in-flight
//! work untouched (the TS `releaseUncommittedLease` fallthrough). The
//! replacement session then opens (taking its storage lease while the live
//! session still holds its own — the lease handoff), the live session is
//! retired (its runs and background tasks aborted, its RLM children
//! closed with the `replaced` reason), and the replacement is installed:
//! the old session closes and releases its lease. Switching to the live
//! session itself closes it before reopening (one owner per storage).
//!
//! Cwd rebind (TS parity): `switchSession` and `importFromJsonl` run the
//! replacement in the TARGET session's cwd (`cwdOverride`, else the stored
//! cwd, else the live cwd); an override also becomes the reopened main
//! conversation's agent cwd, so its tools run there. `newSession` keeps the
//! live cwd.
//!
//! Responses are the TS `{ cancelled: false }` wire object; a missing input
//! file answers the TS import error (`File not found: <path>`), and a
//! stored session cwd that no longer exists answers the TS
//! `MissingSessionCwdError` text.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::{read_session_cwd, SessionLocation};
use eukhe_durable::harness::types::{AgentChange, ConversationAbortOptions, FieldChange};
use serde_json::{json, Value};

use crate::lease::canonical_session_path;
use crate::protocol::{response_failure, response_success, DaemonErrorInfo, DaemonResponse};
use crate::worker::{CreateParams, HostedSession, SessionCore, SessionSlot, Worker};

/// A prepared replacement (TS `SessionManager.open` +
/// `assertSessionCwdExists`): the create parameters the replacement opens
/// with, and the cwd override its main conversation takes.
pub(crate) struct PreparedReplacement {
    params: CreateParams,
    /// The `cwdOverride` that differs from the stored cwd: the reopened
    /// main conversation's agent moves there.
    agent_cwd: Option<String>,
}

/// The navigation surface: the prepare phases of the three commands. The
/// open, retire, and install phases are the worker's
/// (`run_session_replacement`).
pub(crate) struct SessionNavigation {
    session: SessionSlot,
    core: Arc<Mutex<SessionCore>>,
}

/// The live identity a replacement keeps.
struct LiveIdentity {
    cwd: String,
    storage_dir: Option<PathBuf>,
    rlm_depth: u32,
    rlm_child_id: Option<String>,
    parent_active_session_id: Option<String>,
    parent_session_id: Option<String>,
    child_script: Option<String>,
}

impl SessionNavigation {
    pub(crate) fn new(session: SessionSlot, core: Arc<Mutex<SessionCore>>) -> Self {
        SessionNavigation { session, core }
    }

    #[allow(clippy::result_large_err)] // the error is the wire response itself
    fn live(&self, command: &str) -> Result<LiveIdentity, DaemonResponse> {
        let Some(hosted) = self.session.get() else {
            return Err(response_failure(
                None,
                command,
                "Session is still initializing",
                None,
            ));
        };
        let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
        Ok(LiveIdentity {
            cwd: core.cwd.clone(),
            storage_dir: hosted.storage_dir().map(Path::to_path_buf),
            rlm_depth: core.rlm_depth,
            rlm_child_id: core.rlm_child_id.clone(),
            parent_active_session_id: core.parent_active_session_id.clone(),
            parent_session_id: core.parent_session_id.clone(),
            child_script: core.child_script.clone(),
        })
    }

    /// `new_session`'s prepare phase (TS `newSession`): a fresh session in
    /// the live session's sessions directory (in memory for a `noSession`
    /// session), in the live cwd, keeping the live RLM identity. The TS
    /// `parentSession` lineage pointer has no durable home (sessions carry
    /// no header) and is not recorded.
    #[allow(clippy::result_large_err)] // the error is the wire response itself
    pub(crate) fn prepare_new_session(
        &self,
        agent_dir: &Path,
    ) -> Result<PreparedReplacement, DaemonResponse> {
        const COMMAND: &str = "new_session";
        let live = self.live(COMMAND)?;
        let session_dir = sessions_dir_of(live.storage_dir.as_deref(), agent_dir)
            .map_err(|error| response_failure(None, COMMAND, &error, None))?;
        let no_session = live.storage_dir.is_none();
        Ok(PreparedReplacement {
            params: replacement_params(live, None, no_session, session_dir, None),
            agent_cwd: None,
        })
    }

    /// `switch_session`'s prepare phase (TS `SessionManager.open` +
    /// `assertSessionCwdExists`): the target must exist and its cwd (the
    /// override, else the stored one) must be a directory.
    #[allow(clippy::result_large_err)] // the error is the wire response itself
    pub(crate) async fn prepare_switch_session(
        &self,
        payload: &Value,
        agent_dir: &Path,
        cx: &Context,
    ) -> Result<PreparedReplacement, DaemonResponse> {
        const COMMAND: &str = "switch_session";
        let live = self.live(COMMAND)?;
        let session_path = payload
            .get("sessionPath")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let path = crate::paths::expand_tilde(session_path)
            .map_err(|error| response_failure(None, COMMAND, &error.to_string(), None))?;
        if session_path.is_empty() || !crate::worker::durable_host::session_exists(&path) {
            return Err(response_failure(
                None,
                COMMAND,
                &format!("Session file not found: {}", path.display()),
                None,
            ));
        }
        let location = SessionLocation::from_path(path.clone());
        self.prepare_existing(COMMAND, live, &location, payload, agent_dir, cx)
            .await
    }

    /// `import_jsonl`'s prepare phase (TS `importFromJsonl`): copy the input
    /// file into the sessions directory as `<stem>.jsonl` (the legacy file
    /// the open imports into `<stem>/`) and check its stored cwd. A missing
    /// input answers the TS import error; an input whose session storage
    /// already exists from another file is refused rather than shadowed.
    #[allow(clippy::result_large_err)] // the error is the wire response itself
    pub(crate) async fn prepare_import_jsonl(
        &self,
        payload: &Value,
        agent_dir: &Path,
        cx: &Context,
    ) -> Result<PreparedReplacement, DaemonResponse> {
        const COMMAND: &str = "import_jsonl";
        let fail = |error: String| response_failure(None, COMMAND, &error, None);
        let input_path = payload
            .get("inputPath")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let input = Path::new(input_path);
        if !input.is_file() {
            return Err(response_failure(
                None,
                COMMAND,
                &format!("File not found: {}", input.display()),
                Some(DaemonErrorInfo::SessionImportFileNotFound {
                    file_path: input.display().to_string(),
                }),
            ));
        }
        let live = self.live(COMMAND)?;
        let sessions_dir = sessions_dir_of(live.storage_dir.as_deref(), agent_dir).map_err(fail)?;
        let stem = input
            .file_stem()
            .and_then(|stem| stem.to_str())
            .filter(|stem| !stem.is_empty())
            .ok_or_else(|| fail(format!("Invalid session file name: {}", input.display())))?;
        let target = sessions_dir.join(format!("{stem}.jsonl"));
        let in_place = canonical_session_path(&target) == canonical_session_path(input);
        if !in_place {
            let storage_dir = sessions_dir.join(stem);
            if storage_dir.exists() {
                return Err(fail(format!(
                    "Cannot import {}: session {stem} already exists at {}",
                    input.display(),
                    storage_dir.display()
                )));
            }
            std::fs::create_dir_all(&sessions_dir)
                .and_then(|()| std::fs::copy(input, &target).map(drop))
                .map_err(|error| fail(error.to_string()))?;
        }
        let location = SessionLocation::Legacy(target);
        self.prepare_existing(COMMAND, live, &location, payload, agent_dir, cx)
            .await
    }

    /// The shared tail of `switch_session` / `import_jsonl`: resolve the
    /// replacement cwd and check it exists.
    #[allow(clippy::result_large_err)] // the error is the wire response itself
    async fn prepare_existing(
        &self,
        command: &str,
        live: LiveIdentity,
        location: &SessionLocation,
        payload: &Value,
        agent_dir: &Path,
        cx: &Context,
    ) -> Result<PreparedReplacement, DaemonResponse> {
        let cwd_override = payload
            .get("cwdOverride")
            .and_then(Value::as_str)
            .filter(|cwd| !cwd.is_empty())
            .map(str::to_owned);
        let stored = read_session_cwd(location, cx)
            .await
            .filter(|cwd| !cwd.is_empty());
        let cwd = cwd_override.clone().or_else(|| stored.clone());
        if let Some(cwd) = cwd.as_deref() {
            if !Path::new(cwd).is_dir() {
                let path = location.path().display().to_string();
                // The typed error info lets clients render the TS
                // missing-cwd prompt (the issue carries the fallback cwd
                // the confirm answers with).
                return Err(response_failure(
                    None,
                    command,
                    &format!(
                        "Stored session working directory does not exist: {cwd}\nSession file: {path}\nCurrent working directory: {}",
                        live.cwd
                    ),
                    Some(DaemonErrorInfo::MissingSessionCwd {
                        issue: json!({
                            "sessionFile": path,
                            "sessionCwd": cwd,
                            "fallbackCwd": live.cwd,
                        }),
                    }),
                ));
            }
        }
        let session_dir = location
            .storage_dir()
            .parent()
            .map_or_else(
                || sessions_dir_of(None, agent_dir),
                |dir| Ok(dir.to_path_buf()),
            )
            .map_err(|error| response_failure(None, command, &error, None))?;
        let agent_cwd = cwd_override.filter(|cwd| stored.as_ref() != Some(cwd));
        Ok(PreparedReplacement {
            params: replacement_params(
                live,
                Some(location.path().to_path_buf()),
                false,
                session_dir,
                cwd,
            ),
            agent_cwd,
        })
    }
}

/// The sessions directory a replacement lives in: the live storage's
/// parent, else the agent's sessions directory.
fn sessions_dir_of(storage_dir: Option<&Path>, agent_dir: &Path) -> Result<PathBuf, String> {
    match storage_dir.and_then(Path::parent) {
        Some(dir) => Ok(dir.to_path_buf()),
        None => crate::paths::sessions_dir(agent_dir).map_err(|error| error.to_string()),
    }
}

/// The create parameters of a replacement: the target, in `cwd` (else the
/// live cwd), keeping the live RLM identity; no explicit model, thinking
/// level, name, or scoped-model patterns (the session's own state wins).
fn replacement_params(
    live: LiveIdentity,
    session_path: Option<PathBuf>,
    no_session: bool,
    session_dir: PathBuf,
    cwd: Option<String>,
) -> CreateParams {
    CreateParams {
        session_path,
        no_session,
        name: None,
        model: None,
        thinking: None,
        cwd: cwd.unwrap_or(live.cwd),
        session_dir,
        session_id: None,
        rlm_depth: Some(live.rlm_depth),
        rlm_max_depth: None,
        rlm_child_id: live.rlm_child_id,
        parent_active_session_id: live.parent_active_session_id,
        parent_session_id: live.parent_session_id,
        child_script: live.child_script,
        model_patterns: None,
        execution_mode: None,
        spawned_by_request_id: None,
    }
}

/// `response` re-tagged with `command` (the shared open/install helpers
/// answer as `create`).
fn retag(mut response: DaemonResponse, command: &str) -> DaemonResponse {
    command.clone_into(&mut response.command);
    response
}

/// Whether `params` reopens the storage `live` holds.
fn reopens_live(params: &CreateParams, live: &HostedSession) -> bool {
    let (Some(path), Some(dir)) = (params.session_path.as_deref(), live.storage_dir()) else {
        return false;
    };
    let (_, target) = crate::worker::durable_host::storage_for_path(path);
    canonical_session_path(&target) == canonical_session_path(dir)
}

impl Worker {
    /// The shared replacement flow: open the prepared target, retire the
    /// live session, and install the replacement (see the module docs).
    async fn run_session_replacement(
        &self,
        command: &'static str,
        prepared: Result<PreparedReplacement, DaemonResponse>,
    ) -> DaemonResponse {
        let prepared = match prepared {
            Ok(prepared) => prepared,
            // A prepare failure never touched the live session.
            Err(response) => return response,
        };
        let cx = BACKGROUND_CONTEXT.clone();
        // One replacement at a time: open, retire, and install are one
        // serialized critical section.
        let _replacement_gate = self.replacement_gate.lock().await;
        let live = self.session.get();
        let same_storage = live
            .as_deref()
            .is_some_and(|live| reopens_live(&prepared.params, live));
        if same_storage {
            // One owner per storage: the live session closes before it
            // reopens as its own replacement.
            if let Some(live) = &live {
                self.retire_session(live, &cx).await;
            }
            self.close_hosted_session().await;
        }
        let hosted = match self.open_hosted(&prepared.params, &cx).await {
            Ok(hosted) => hosted,
            Err(response) => return retag(*response, command),
        };
        if let Some(cwd) = prepared.agent_cwd {
            let configured = match hosted.main() {
                Ok(main) => {
                    main.configure(
                        AgentChange {
                            cwd: FieldChange::Set(cwd),
                            ..AgentChange::default()
                        },
                        &cx,
                    )
                    .await
                }
                Err(error) => Err(error),
            };
            if let Err(error) = configured {
                if let Err(close) = hosted.close(&cx).await {
                    eprintln!(
                        "eukhe-daemon worker: closing the unused replacement failed: {close}"
                    );
                }
                return response_failure(None, command, &error.to_string(), None);
            }
        }
        if !same_storage {
            if let Some(live) = &live {
                self.retire_session(live, &cx).await;
            }
        }
        // The successor's withdrawn inputs come from its own durable
        // store: `install_hosted` seeds the caches from it.
        if let Err(response) = self.install_hosted(hosted, &prepared.params, &cx).await {
            return retag(*response, command);
        }
        self.reseed_service_tier_for_replacement();
        self.bind_scheduled_jobs().await;
        self.push_roster_delta();
        let (busy, session_ref) = {
            let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
            (core.is_busy(), Worker::herdr_session_ref(&core))
        };
        let _ = self.record_recovery(busy, "replace");
        // The pane reporter re-reports for the successor session (same
        // pane, new session).
        self.herdr
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .session_started(busy, session_ref);
        response_success(None, command, Some(json!({ "cancelled": false })))
    }

    /// Retire the live session before its replacement (TS
    /// `teardownForReplacement`): the branch summary stops, the RLM
    /// children close with the `replaced` reason, and every run and
    /// background task of the main conversation is aborted (its queued
    /// inputs are disposed, like the TS queue). Failures are logged: the
    /// replacement proceeds.
    async fn retire_session(&self, live: &HostedSession, cx: &Context) {
        self.tree_navigation.abort();
        self.close_rlm_children(live, crate::rlm_children::ChildCloseReason::Replaced)
            .await;
        match live.main() {
            Ok(main) => {
                if let Err(error) = main
                    .abort(ConversationAbortOptions { background: true }, cx)
                    .await
                {
                    eprintln!("eukhe-daemon worker: aborting the replaced session failed: {error}");
                }
            }
            Err(error) => {
                eprintln!("eukhe-daemon worker: the replaced session is closed: {error}");
            }
        }
        live.events_delivered().await;
    }

    /// `new_session`.
    pub(crate) async fn handle_new_session(&self, _payload: &Value) -> DaemonResponse {
        if let Err(response) = self.require_created("new_session") {
            return response;
        }
        let prepared = self.navigation.prepare_new_session(&self.config.agent_dir);
        self.run_session_replacement("new_session", prepared).await
    }

    /// `switch_session`.
    pub(crate) async fn handle_switch_session(&self, payload: &Value) -> DaemonResponse {
        if let Err(response) = self.require_created("switch_session") {
            return response;
        }
        let prepared = self
            .navigation
            .prepare_switch_session(payload, &self.config.agent_dir, &BACKGROUND_CONTEXT)
            .await;
        self.run_session_replacement("switch_session", prepared)
            .await
    }

    /// `import_jsonl`.
    pub(crate) async fn handle_import_jsonl(&self, payload: &Value) -> DaemonResponse {
        if let Err(response) = self.require_created("import_jsonl") {
            return response;
        }
        let prepared = self
            .navigation
            .prepare_import_jsonl(payload, &self.config.agent_dir, &BACKGROUND_CONTEXT)
            .await;
        self.run_session_replacement("import_jsonl", prepared).await
    }
}

#[cfg(test)]
#[path = "session_navigation/tests.rs"]
mod tests;
