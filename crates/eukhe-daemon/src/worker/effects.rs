//! The exactly-once effects surface: `get_unknown_effects` reads the main
//! conversation's ledger of steps a restart could not tell the outcome of
//! and treated as not run (the `eukhe.effects` document,
//! `eukhe_durable::harness::effects`), and `resolve_unknown_effect`
//! records a client's optional correction of one in a session commit;
//! `get_ran_effects` reads its ledger of irreversible effects that ran.
//! Nothing waits for one. Attached clients follow the ledger through
//! `unknown_effects_update` and `ran_effects_update` (the event bridge's
//! effects watch) and the attach snapshot's `unknownEffects` and
//! `ranEffects`.
//!
//! A subagent session's irreversible effects go up to its root's ledger:
//! the child hands each to its parent ([`relay_up`], `relay_ran_effect`
//! over the supervisor link, naming itself as the subagent), and a parent
//! records it when it is the root, else hands it on
//! (`Worker::handle_relay_ran_effect`).

use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::ran_effects::record_on;
use eukhe_durable::harness::effects::{read_ran_effects, read_unknown_effects, resolve_unknown};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::daemon::DaemonCommand;
use eukhe_types::effects::{
    EffectResolution, RanEffect, RanEffectDraft, RanEffectsReply, ResolvedEffectReply,
    UnknownEffectsReply,
};
use serde::Deserialize as _;
use serde_json::Value;

use super::{response_failure, response_success, SessionCore, Worker};
use crate::protocol::DaemonResponse;
use crate::supervisor_link::SupervisorLink;

/// The session `core` is a child of, if any (its persisted id, else its
/// live id).
fn parent_of(core: &SessionCore) -> Option<String> {
    core.parent_session_id
        .clone()
        .or_else(|| core.parent_active_session_id.clone())
}

/// Hand `draft`, an irreversible effect this subagent session (or one
/// below it) ran, to the parent session; answers the effect as the root
/// recorded it. A draft that names no subagent yet names this session.
///
/// # Errors
///
/// The session has no parent, or the relay failed or was refused.
pub(crate) async fn relay_up(
    core: &Mutex<SessionCore>,
    link: &SupervisorLink,
    active_session_id: &str,
    draft: RanEffectDraft,
) -> SessionResult<RanEffect> {
    let (parent, agent) = {
        let core = core.lock().unwrap_or_else(PoisonError::into_inner);
        let agent = core
            .session_name
            .clone()
            .or_else(|| core.rlm_child_id.clone())
            .unwrap_or_else(|| active_session_id.to_owned());
        (parent_of(&core), agent)
    };
    let parent =
        parent.ok_or_else(|| SessionError::error("a root session has no parent to relay to"))?;
    let command = DaemonCommand::RelayRanEffect {
        id: None,
        active_session_id: parent,
        effect: RanEffectDraft {
            agent: draft.agent.or(Some(agent)),
            ..draft
        },
        rest: serde_json::Map::default(),
    };
    let command = serde_json::to_value(&command).map_err(SessionError::other)?;
    let data = link
        .request_success(
            command,
            Duration::from_millis(crate::supervisor::WORKER_REQUEST_TIMEOUT_MS),
        )
        .await
        .map_err(|error| {
            SessionError::error(format!(
                "the parent session did not record the effect: {error:#}"
            ))
        })?;
    RanEffect::deserialize(data).map_err(SessionError::other)
}

/// The relay of the child session `core` hosts, for its
/// `SessionConfig::ran_effect_relay`.
pub(crate) fn relay(
    core: Arc<Mutex<SessionCore>>,
    link: Arc<SupervisorLink>,
    active_session_id: String,
) -> eukhe_core::durable::ran_effects::RanEffectRelay {
    Arc::new(move |draft| {
        let (core, link, active) = (
            Arc::clone(&core),
            Arc::clone(&link),
            active_session_id.clone(),
        );
        Box::pin(async move { relay_up(&core, &link, &active, draft).await })
    })
}

impl Worker {
    /// `get_unknown_effects`: the ledger, oldest first, corrected or not.
    #[tracing::instrument(skip(self))]
    pub(crate) async fn handle_get_unknown_effects(&self) -> DaemonResponse {
        const COMMAND: &str = "get_unknown_effects";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let read = async {
            let main = hosted.main()?;
            read_unknown_effects(hosted.harness(), main.id(), &BACKGROUND_CONTEXT).await
        };
        match read.await {
            Ok(effects) => response_success(
                None,
                COMMAND,
                Some(serde_json::to_value(UnknownEffectsReply { effects }).unwrap_or(Value::Null)),
            ),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }

    /// `get_ran_effects`: the session's ledger of irreversible effects
    /// that ran, by id (a root session's: its subagents' too).
    #[tracing::instrument(skip(self))]
    pub(crate) async fn handle_get_ran_effects(&self) -> DaemonResponse {
        const COMMAND: &str = "get_ran_effects";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let read = async {
            let main = hosted.main()?;
            read_ran_effects(hosted.harness(), main.id(), &BACKGROUND_CONTEXT).await
        };
        match read.await {
            Ok(effects) => response_success(
                None,
                COMMAND,
                Some(serde_json::to_value(RanEffectsReply { effects }).unwrap_or(Value::Null)),
            ),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }

    /// `relay_ran_effect`: an irreversible effect a subagent below this
    /// session ran. The root records it in its ledger; any other session
    /// hands it on to its parent. The data is the effect as recorded.
    #[tracing::instrument(skip(self, payload))]
    pub(crate) async fn handle_relay_ran_effect(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "relay_ran_effect";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(draft) = payload
            .get("effect")
            .and_then(|effect| RanEffectDraft::deserialize(effect).ok())
        else {
            return response_failure(None, COMMAND, "Invalid irreversible effect relay", None);
        };
        let child = parent_of(&self.core.lock().unwrap_or_else(PoisonError::into_inner)).is_some();
        let recorded = if child {
            relay_up(
                &self.core,
                &self.supervisor_link,
                &self.config.active_session_id,
                draft,
            )
            .await
        } else {
            match hosted.main() {
                Ok(main) => {
                    record_on(hosted.harness(), main.id(), draft, &BACKGROUND_CONTEXT).await
                }
                Err(error) => Err(error),
            }
        };
        match recorded {
            Ok(effect) => response_success(
                None,
                COMMAND,
                Some(serde_json::to_value(effect).unwrap_or(Value::Null)),
            ),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }

    /// `resolve_unknown_effect`: settle the open effect `effectId` as
    /// `resolution` (`ran` or `notRun`) and answer it as resolved. An id
    /// the ledger holds no open effect of (never noted, or settled
    /// already) changes nothing and fails.
    #[tracing::instrument(skip(self, payload))]
    pub(crate) async fn handle_resolve_unknown_effect(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "resolve_unknown_effect";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(effect_id) = payload
            .get("effectId")
            .and_then(Value::as_str)
            .filter(|id| !id.is_empty())
        else {
            return response_failure(
                None,
                COMMAND,
                "resolve_unknown_effect requires an effectId",
                None,
            );
        };
        let Some(resolution) = payload
            .get("resolution")
            .and_then(|resolution| EffectResolution::deserialize(resolution).ok())
        else {
            return response_failure(
                None,
                COMMAND,
                "resolve_unknown_effect requires resolution \"ran\" or \"notRun\"",
                None,
            );
        };
        let id = effect_id.to_owned();
        let resolved = async {
            let conversation_id = hosted.main()?.id();
            hosted
                .harness()
                .commit(
                    move |tx| async move {
                        resolve_unknown(&tx, conversation_id, &id, resolution).await
                    },
                    &BACKGROUND_CONTEXT,
                )
                .await
        };
        match resolved.await {
            Ok(Some(effect)) => response_success(
                None,
                COMMAND,
                Some(serde_json::to_value(ResolvedEffectReply { effect }).unwrap_or(Value::Null)),
            ),
            Ok(None) => response_failure(
                None,
                COMMAND,
                &format!("No open unknown effect: {effect_id}"),
                None,
            ),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }
}
