//! The worker's client-visible surface: summaries, connection state, the
//! queue projection, the roster push, and the event emission family. Every
//! read comes from the shown conversation's event mirror on the core, so a
//! summary never waits on the Harness.

use super::durable_host::bridge::{QueuedMode, ShownView};
use super::durable_host::wire_messages::entry_wire_message;
use super::lifecycle::active_lifecycle;
use super::{
    create_daemon_event_meta, AgentConnectionState, Arc, DaemonOutbound, DaemonSessionClosedReason,
    EventPump, Map, Mutex, OutboundFrame, Result, SessionActionSnapshot, SessionCore, SessionSlot,
    Value, Worker,
};

use eukhe_durable::entries::{COMPACTION_ENTRY, USER_ENTRY};
use eukhe_durable::harness::usage::UsageState;
use eukhe_types::daemon::{QueuedItem, SessionEvent};
use eukhe_types::pi_ai::Model;
use serde_json::json;

use crate::session_usage::SessionUsageSummary;
use eukhe_types::daemon::SessionSummary;

/// TS `sessionUsageSummaryFrom` over the shown conversation's own spend
/// (`pi.usage`: its entries, summarization attempts, and tool results):
/// `inputTokens` folds cache reads and writes in; absent when the session
/// recorded no billable work.
fn usage_summary(usage: &UsageState) -> Option<SessionUsageSummary> {
    let (mut input_tokens, mut output_tokens, mut cost) = (0u64, 0u64, 0.0);
    for usage in usage.models.values().chain(usage.tools.values()) {
        input_tokens = input_tokens
            .saturating_add(usage.input)
            .saturating_add(usage.cache_read)
            .saturating_add(usage.cache_write);
        output_tokens = output_tokens.saturating_add(usage.output);
        cost += usage.cost.total;
    }
    (input_tokens > 0 || output_tokens > 0 || cost != 0.0).then_some(SessionUsageSummary {
        input_tokens,
        output_tokens,
        cost,
    })
}

/// The shown conversation's model as the wire carries it (`state.model`,
/// summary `model`): the catalog model when the session's Models knows it,
/// else `{id, provider}`.
pub(crate) fn model_metadata(core: &SessionCore, session: &SessionSlot) -> Option<Value> {
    let model_ref = core
        .view
        .as_ref()?
        .translator
        .mirror()
        .agent
        .model
        .clone()?;
    let catalog = catalog_model(session, &model_ref.provider, &model_ref.model_id);
    Some(match catalog {
        Some(model) => serde_json::to_value(&model).unwrap_or(Value::Null),
        None => json!({ "id": model_ref.model_id, "provider": model_ref.provider }),
    })
}

fn catalog_model(session: &SessionSlot, provider: &str, model_id: &str) -> Option<Model> {
    session.get()?.deps().models.get_model(provider, model_id)
}

/// The shown conversation's thinking level as its requests send it
/// (docs/inference.md S10): the stored level clamped to the model's
/// ladder, the clamp every provider applies before it sends a level. An
/// unset level shows as `default`, never as `off`: open settles every
/// main conversation on a level, so `default` shows only before a
/// conversation is shown.
pub(crate) fn thinking_level(core: &SessionCore, session: &SessionSlot) -> String {
    let Some(agent) = core
        .view
        .as_ref()
        .map(|view| &view.translator.mirror().agent)
    else {
        return "default".to_string();
    };
    let Some(level) = agent.thinking_level else {
        return "default".to_string();
    };
    agent
        .model
        .as_ref()
        .and_then(|model_ref| catalog_model(session, &model_ref.provider, &model_ref.model_id))
        .map_or(level, |model| {
            eukhe_ai::models::clamp_thinking_level(&model, level)
        })
        .as_str()
        .to_string()
}

/// The thinking levels the shown model supports (`["off"]` without a
/// reasoning model).
pub(crate) fn available_thinking_levels(core: &SessionCore, session: &SessionSlot) -> Vec<String> {
    let model = core
        .view
        .as_ref()
        .and_then(|view| view.translator.mirror().agent.model.clone())
        .and_then(|model_ref| catalog_model(session, &model_ref.provider, &model_ref.model_id));
    match model {
        Some(model) => eukhe_ai::models::get_supported_thinking_levels(&model)
            .into_iter()
            .map(|level| level.as_str().to_string())
            .collect(),
        None => vec!["off".to_string()],
    }
}

impl Worker {
    pub(crate) fn summary_locked(&self, core: &SessionCore) -> SessionSummary {
        let mut summary = session_summary(
            core,
            &thinking_level(core, &self.session),
            model_metadata(core, &self.session),
            self.user_bash.is_running(),
            quota_parked(&self.session),
        );
        // The worker's roster-delta counter at snapshot time and the
        // process instance that read it: the supervisor's pull gate orders
        // this summary against in-flight deltas.
        summary.roster_delta_sequence = Some(
            self.roster_delta_sequence
                .load(std::sync::atomic::Ordering::SeqCst),
        );
        summary.worker_instance_id = (!self.config.worker_instance_id.is_empty())
            .then(|| self.config.worker_instance_id.clone());
        summary
    }

    /// Publish `summary` as this session's own summary (the kernel
    /// messaging controllers' sender block and family edges).
    pub(crate) fn publish_own_summary(&self, summary: &SessionSummary) {
        *self
            .own_summary
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) =
            serde_json::to_value(summary).ok();
    }

    /// Push one roster delta from a command arm.
    pub(crate) fn push_roster_delta(&self) {
        self.roster_pushes.push();
    }

    pub(crate) fn connection_state_locked(&self, core: &SessionCore) -> AgentConnectionState {
        let mirror = core.view.as_ref().map(|view| view.translator.mirror());
        let settings = self.session_settings(core);
        let model = model_metadata(core, &self.session);
        // TS `createAgentConnectionState` carries `contextUsage:
        // session.getContextUsage()` in every attach snapshot, so the
        // client's first frame reads the tray's context usage off the
        // snapshot instead of blocking on a `get_session_stats`
        // round-trip. The same mirror estimate `get_session_stats` serves:
        // `None` without a model context window.
        let context_usage = mirror
            .zip(crate::state_getters::model_context_window(model.as_ref()))
            .map(|(mirror, window)| {
                crate::state_getters::mirror_context_usage(&mirror.entries, window)
            });
        AgentConnectionState {
            is_streaming: core.is_busy(),
            is_compacting: core.is_compacting(),
            active_session_id: Some(core.active_session_id.clone()),
            cwd: core.cwd.clone(),
            model,
            thinking_level: thinking_level(core, &self.session),
            service_tier: core
                .active_service_tier
                .unwrap_or(eukhe_types::ai::ServiceTier::Auto)
                .as_str()
                .to_string(),
            available_thinking_levels: available_thinking_levels(core, &self.session),
            is_bash_running: self.user_bash.is_running(),
            retry_attempt: mirror
                .and_then(|mirror| mirror.retry_attempt)
                .map_or(0, |attempt| u32::try_from(attempt).unwrap_or(u32::MAX)),
            steering_mode: queue_mode_setting(&settings, QueueKind::Steering),
            follow_up_mode: queue_mode_setting(&settings, QueueKind::FollowUp),
            session_file: core.session_file(),
            session_id: core.session_id.clone(),
            session_name: core.session_name.clone(),
            session_dir: core
                .session_dir
                .as_ref()
                .and_then(|dir| dir.parent())
                .map(|dir| dir.to_string_lossy().into_owned()),
            leaf_id: mirror
                .and_then(|mirror| mirror.entries.last())
                .map(|entry| entry.id.to_string()),
            auto_compaction_enabled: settings.get_compaction_enabled(),
            message_count: message_count(core),
            session_actions: session_snapshot(core),
            compaction_count: mirror.map_or(0, |mirror| {
                let count = mirror
                    .entries
                    .iter()
                    .filter(|entry| entry.kind == COMPACTION_ENTRY.kind())
                    .count();
                u32::try_from(count).unwrap_or(u32::MAX)
            }),
            goal: core
                .view
                .as_ref()
                .map_or(Value::Null, |view| view.goal.clone()),
            scoped_models: core.scoped_models.clone(),
            active_tool_names: Vec::new(),
            context_usage,
        }
    }

    /// The settings the connection state reads: the hosted session's
    /// (reloaded when settings.json changes — the same values the Harness
    /// reads per use), else the session cwd's over this worker's agent dir.
    fn session_settings(&self, core: &SessionCore) -> Arc<eukhe_core::settings::SettingsManager> {
        self.session.get().map_or_else(
            || {
                Arc::new(eukhe_core::settings::SettingsManager::create(
                    &core.cwd,
                    &self.config.agent_dir,
                ))
            },
            |hosted| hosted.deps().settings.manager(),
        )
    }

    /// Record the revival evidence through the worker's journal.
    pub(crate) fn record_recovery(&self, busy: bool, operation: &str) -> Result<()> {
        super::record_recovery_with(&self.recovery, &self.core, busy, operation);
        Ok(())
    }

    /// Sequence and broadcast one `session_event` frame at the worker level.
    pub(crate) fn emit_worker_event(&self, event: SessionEvent) {
        emit_worker_event_with(&self.core, &self.events, event);
    }

    /// Broadcast the queue projection when it changed.
    pub(crate) fn emit_action_update(&self) {
        let mut core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        emit_action_update_locked(&mut core, &self.events);
    }

    pub(crate) fn emit_session_closed(
        &self,
        active_session_id: &str,
        reason: DaemonSessionClosedReason,
    ) -> Result<()> {
        let mut core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let sequence = core.last_event_sequence + 1;
        core.last_event_sequence = sequence;
        let meta = create_daemon_event_meta(
            &core.active_session_id,
            sequence,
            None,
            Some(&core.generation),
        );
        let outbound = DaemonOutbound::SessionClosed {
            active_session_id: active_session_id.to_string(),
            reason,
            meta: Some(meta),
            rest: Map::default(),
        };
        let payload = serde_json::to_vec(&outbound)?;
        self.events.send(OutboundFrame::session_event(payload));
        Ok(())
    }
}

/// Sequence and broadcast one `session_event` under the held core lock (the
/// event bridge's path: the mirror and the sequence advance together).
pub(crate) fn emit_event_locked(core: &mut SessionCore, events: &EventPump, event: SessionEvent) {
    let sequence = core.last_event_sequence + 1;
    core.last_event_sequence = sequence;
    let meta = create_daemon_event_meta(
        &core.active_session_id,
        sequence,
        None,
        Some(&core.generation),
    );
    let outbound = DaemonOutbound::SessionEvent {
        active_session_id: core.active_session_id.clone(),
        event,
        meta: Some(meta),
        rest: Map::default(),
    };
    match serde_json::to_vec(&outbound) {
        Ok(payload) => events.send(OutboundFrame::session_event(payload)),
        Err(error) => eprintln!("eukhe-daemon worker: session event serialization failed: {error}"),
    }
}

/// Emit `session_action_update` when the queue projection changed since
/// the last broadcast.
pub(crate) fn emit_action_update_locked(core: &mut SessionCore, events: &EventPump) {
    let snapshot = session_snapshot(core);
    if core.last_action_snapshot.as_ref() == Some(&snapshot) {
        return;
    }
    core.last_action_snapshot = Some(snapshot.clone());
    emit_event_locked(
        core,
        events,
        SessionEvent::SessionActionUpdate { actions: snapshot },
    );
}

pub(crate) fn emit_worker_event_with(
    core: &Arc<Mutex<SessionCore>>,
    events: &Arc<EventPump>,
    event: SessionEvent,
) {
    let mut core = core
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    emit_event_locked(&mut core, events, event);
}

/// The roster push context: what a `worker_roster_delta` summary reads.
pub(crate) struct RosterPushContext {
    pub(crate) core: Arc<Mutex<SessionCore>>,
    pub(crate) session: SessionSlot,
    pub(crate) user_bash: std::sync::Arc<crate::user_bash::UserBash>,
    pub(crate) roster_link: std::sync::Arc<crate::supervisor_link::SupervisorLink>,
    pub(crate) worker_token: String,
    pub(crate) worker_instance_id: String,
    pub(crate) roster_delta_sequence: std::sync::Arc<std::sync::atomic::AtomicU64>,
}

/// Whether the session's provider runtime is quota-parked (the durable
/// `eukhe.quota_park` state; `false` without a hosted session).
fn quota_parked(session: &SessionSlot) -> bool {
    session.get().is_some_and(|hosted| {
        hosted
            .deps()
            .provider_runtime
            .get()
            .is_some_and(|runtime| runtime.is_quota_parked())
    })
}

/// The worker's roster-delta push: the fresh session summary rides the
/// supervisor link with the worker's monotonic counter (the supervisor's
/// stale-delta gate drops delayed older snapshots). The push queue's one
/// consumer awaits each request, so a wedged supervisor holds at most one
/// roster connection open and pushes never reorder.
pub(crate) async fn push_roster_delta(context: &RosterPushContext) {
    if std::env::var_os("EUKHE_WORKER_DISABLE_ROSTER_PUSH").is_some() {
        return;
    }
    if context.worker_token.is_empty() || context.roster_link.socket_path().as_os_str().is_empty() {
        return;
    }
    // A pull may race this push, but both read the counter with their core
    // snapshot held: an equal-counter pull was captured after this push.
    let command = {
        let core = context
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut summary = session_summary(
            &core,
            &thinking_level(&core, &context.session),
            model_metadata(&core, &context.session),
            context.user_bash.is_running(),
            quota_parked(&context.session),
        );
        // The embedded counter is the pre-stamp value: every sequence
        // stamped before the snapshot is at or below it.
        summary.roster_delta_sequence = Some(
            context
                .roster_delta_sequence
                .load(std::sync::atomic::Ordering::SeqCst),
        );
        let summary = serde_json::to_value(&summary).unwrap_or(Value::Null);
        let sequence_value = context
            .roster_delta_sequence
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            + 1;
        json!({
            "type": "worker_roster_delta",
            "workerToken": context.worker_token,
            "summary": summary,
            "sequence": sequence_value,
            "workerInstanceId": context.worker_instance_id,
        })
    };
    let _ = context
        .roster_link
        .request(command, std::time::Duration::from_secs(10))
        .await;
}

/// Messages the transcript shows (attach `messages` rows).
fn message_count(core: &SessionCore) -> u32 {
    let count = core.view.as_ref().map_or(0, |view| {
        view.translator
            .mirror()
            .entries
            .iter()
            .filter(|entry| entry_wire_message(entry).is_some())
            .count()
    });
    u32::try_from(count).unwrap_or(u32::MAX)
}

/// The first user message's text (summary `firstMessage`).
pub(super) fn first_message(view: &ShownView) -> Option<String> {
    view.translator
        .mirror()
        .entries
        .iter()
        .filter(|entry| entry.kind == USER_ENTRY.kind())
        .find_map(entry_wire_message)
        .map(|message| crate::types::message_text(&message))
}

/// One timed roster-note candidate: its text and when it was written (ms).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TimedNote {
    pub(crate) text: String,
    pub(crate) at_ms: u64,
}

/// The candidates of the roster `note`: the task the session was given,
/// its latest final report, and its latest accepted progress note.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct NoteCandidates {
    /// The first user message, or the first agent message the session
    /// received (a subagent's kickoff), whichever came first.
    pub(crate) task: Option<String>,
    /// The last assistant message that stopped (`stopReason: stop`) with
    /// text.
    pub(crate) report: Option<TimedNote>,
    /// The latest accepted `rlm.progress.note`.
    pub(crate) progress: Option<TimedNote>,
}

/// The task text one wire message carries: a user message's text, or an
/// `agent_message` row's `details.message`.
fn task_text(message: &Value) -> Option<String> {
    let text = match crate::types::message_role(message)? {
        "user" => crate::types::message_text(message),
        "custom" if message.get("customType").and_then(Value::as_str) == Some("agent_message") => {
            message
                .get("details")?
                .get("message")?
                .as_str()?
                .to_string()
        }
        _ => return None,
    };
    (!text.trim().is_empty()).then_some(text)
}

/// The final report one wire message carries: an assistant message that
/// stopped with text, timed by its timestamp.
fn report_note(message: &Value) -> Option<TimedNote> {
    if crate::types::message_role(message) != Some("assistant")
        || message.get("stopReason").and_then(Value::as_str) != Some("stop")
    {
        return None;
    }
    let text = crate::types::message_text(message);
    (!text.trim().is_empty()).then(|| TimedNote {
        text,
        at_ms: crate::types::message_timestamp_ms(message).unwrap_or_default(),
    })
}

/// The task and report candidates of a transcript's wire messages (the
/// progress candidate lives on the core).
pub(crate) fn note_candidates<I>(messages: I) -> NoteCandidates
where
    I: DoubleEndedIterator<Item = Value> + Clone,
{
    NoteCandidates {
        task: messages.clone().find_map(|message| task_text(&message)),
        report: messages.rev().find_map(|message| report_note(&message)),
        progress: None,
    }
}

/// The roster `note`: the first non-empty line of the newer of the report
/// and the progress note, else of the task, whitespace-collapsed and
/// capped at 160 chars.
pub(crate) fn roster_note(candidates: &NoteCandidates) -> Option<String> {
    let latest = match (&candidates.report, &candidates.progress) {
        (Some(report), Some(progress)) if report.at_ms > progress.at_ms => Some(report),
        (_, Some(progress)) => Some(progress),
        (Some(report), None) => Some(report),
        (None, None) => None,
    };
    let text = latest
        .map(|note| note.text.as_str())
        .or(candidates.task.as_deref())?;
    text.lines()
        .find(|line| !line.trim().is_empty())
        .map(compact_action_label)
}

/// The newest message timestamp (ms) of the shown conversation.
fn last_timestamp_ms(view: &ShownView) -> Option<u64> {
    view.translator
        .mirror()
        .entries
        .iter()
        .rev()
        .find_map(|entry| entry_wire_message(entry)?.get("timestamp")?.as_u64())
        .filter(|timestamp| *timestamp > 0)
}

/// The inputs still owed a turn: the shown conversation's inbox, the
/// inputs an abort suspended, and the admissions an input pause holds.
pub(crate) fn queued_inputs(core: &SessionCore) -> usize {
    core.view.as_ref().map_or(0, |view| view.inbox.len()) + core.suspended.len() + core.held.len()
}

pub(crate) fn session_summary(
    core: &SessionCore,
    thinking_level: &str,
    model: Option<Value>,
    bash_running: bool,
    quota_parked: bool,
) -> SessionSummary {
    let streaming = core.is_busy();
    let compacting = core.is_compacting();
    let queued = queued_inputs(core);
    let messages = message_count(core);
    let view = core.view.as_ref();
    let running_tools = view.is_some_and(|view| !view.translator.mirror().tools.is_empty());
    let last_activity_at = view
        .and_then(last_timestamp_ms)
        .map(crate::util::iso_from_unix_ms)
        .or_else(|| core.created_at.clone());
    SessionSummary {
        id: core.active_session_id.clone(),
        lifecycle: active_lifecycle(&core.runtime_kind, messages == 0, streaming).to_string(),
        activity: if streaming || compacting {
            "working"
        } else {
            "idle"
        }
        .to_string(),
        is_session_active: streaming || compacting || queued > 0,
        has_registered_cron_job: Some(false),
        last_activity_at: last_activity_at.clone(),
        rlm_depth: Some(core.rlm_depth),
        active_session_id: Some(core.active_session_id.clone()),
        session_id: core.session_id.clone(),
        session_file: core.session_file(),
        session_name: core.session_name.clone(),
        cwd: core.cwd.clone(),
        thinking_level: Some(thinking_level.to_string()),
        is_streaming: streaming,
        is_compacting: compacting,
        is_quota_parked: Some(quota_parked),
        is_bash_running: Some(bash_running),
        is_running_tools: streaming && running_tools,
        has_running_subagents: false,
        admission: core.model_admission,
        attached_clients: u32::try_from(core.attached_client_ids.len()).unwrap_or(u32::MAX),
        message_count: messages,
        session_actions: session_snapshot(core),
        created: core.created_at.clone(),
        modified: last_activity_at,
        first_message: view.and_then(first_message),
        note: view.and_then(|view| {
            let entries = view.translator.mirror().entries.iter();
            roster_note(&NoteCandidates {
                progress: core.progress_note.clone(),
                ..note_candidates(entries.filter_map(entry_wire_message))
            })
        }),
        parent_session_path: core.parent_session_path.clone(),
        parent_active_session_id: core.parent_active_session_id.clone(),
        parent_session_id: core.parent_session_id.clone(),
        rlm_child_id: core.rlm_child_id.clone(),
        usage: view
            .and_then(|view| usage_summary(&view.translator.mirror().usage))
            .map(|usage| json!(usage)),
        worker_state: Some("ready".to_string()),
        worker_pid: Some(std::process::id()),
        roster_delta_sequence: None,
        worker_instance_id: None,
        model,
        model_fallback_message: None,
        runtime_kind: Some(core.runtime_kind.clone()),
        unfinished_action_count: Some(0),
        anthropic_warning_shown: core.created.then_some(core.anthropic_warning_shown),
    }
}

/// The queue snapshot for one core (TS `sessionActions`): the queued
/// steer and follow-up inputs of the shown conversation's inbox, then the
/// inputs an abort suspended and the admissions an input pause holds, each
/// with its origin; `active` is the run the bridge's active action tracks
/// (the strip's Starting row).
pub(crate) fn session_snapshot(core: &SessionCore) -> SessionActionSnapshot {
    let inbox = core
        .view
        .as_ref()
        .map_or(&[][..], |view| view.inbox.as_slice());
    let queued = || inbox.iter().chain(&core.suspended).chain(&core.held);
    let lane = |mode: QueuedMode| {
        queued()
            .filter(|input| input.mode == mode)
            .map(|input| QueuedItem {
                text: input.text.clone(),
                origin: input.origin.clone(),
            })
            .collect::<Vec<QueuedItem>>()
    };
    SessionActionSnapshot {
        queued_count: u32::try_from(queued().count()).unwrap_or(u32::MAX),
        steering: lane(QueuedMode::Steer),
        follow_ups: lane(QueuedMode::FollowUp),
        active: core.view.as_ref().and_then(|view| view.active.clone()),
    }
}

/// The active action's queue label (TS `compactRlmText(text, 160)`):
/// collapse whitespace and cap at 160 chars with an ellipsis.
pub(crate) fn compact_action_label(text: &str) -> String {
    const MAX_CHARS: usize = 160;
    let compact: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if compact.chars().count() <= MAX_CHARS {
        return compact;
    }
    let kept: String = compact.chars().take(MAX_CHARS - 3).collect();
    format!("{}...", kept.trim_end())
}

#[derive(Clone, Copy)]
enum QueueKind {
    Steering,
    FollowUp,
}

/// The configured queue delivery mode (settings; the Harness reads the same
/// setting per use).
fn queue_mode_setting(settings: &eukhe_core::settings::SettingsManager, kind: QueueKind) -> String {
    let mode = match kind {
        QueueKind::Steering => settings.get_steering_mode(),
        QueueKind::FollowUp => settings.get_follow_up_mode(),
    };
    match mode {
        eukhe_core::settings::QueueModeSetting::All => "all".to_string(),
        eukhe_core::settings::QueueModeSetting::OneAtATime => "one-at-a-time".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use eukhe_durable::harness::SnapshotEvent;
    use eukhe_durable::types::SubmissionId;
    use serde_json::json;

    use super::super::durable_host::bridge::{QueuedInput, QueuedMode};
    use super::super::durable_host::ShownView;
    use super::*;
    use eukhe_types::input_origin::{ChildExit, InputOrigin, Report};

    fn queued(id: u64, mode: QueuedMode, text: &str) -> QueuedInput {
        queued_from(id, mode, text, InputOrigin::User)
    }

    fn queued_from(id: u64, mode: QueuedMode, text: &str, origin: InputOrigin) -> QueuedInput {
        QueuedInput {
            id: SubmissionId::from_number(id),
            mode,
            text: text.to_owned(),
            content: eukhe_types::pi_ai::UserContent::Text(text.to_owned()),
            entry: None,
            origin,
        }
    }

    /// A core with the given inbox.
    fn core_with(
        inbox: Vec<QueuedInput>,
        suspended: Vec<QueuedInput>,
        held: Vec<QueuedInput>,
    ) -> SessionCore {
        let mut core = SessionCore::test_core("/tmp".to_string());
        let snapshot: SnapshotEvent = serde_json::from_value(json!({
            "entries": [], "tools": [], "nestedTools": [], "compactions": [], "inbox": [],
            "agent": {}, "usage": { "models": {}, "tools": {} },
        }))
        .expect("snapshot");
        core.view = Some(ShownView {
            epoch: 1,
            translator: super::super::durable_host::translator::EventTranslator::new(
                &snapshot,
                super::super::durable_host::translator::CoalesceMode::Immediate,
            ),
            inbox,
            active: None,
            goal: Value::Null,
        });
        core.suspended = suspended;
        core.held = held;
        core
    }

    /// Withdrawn and held inputs ride the strip after the inbox ones, each
    /// with the origin its producer set.
    #[test]
    fn the_queue_items_carry_their_origins() {
        let child = InputOrigin::Report {
            report: Report::ChildExited {
                child: "a".to_owned(),
                exit: ChildExit::NoReply,
            },
        };
        let heartbeat = InputOrigin::Report {
            report: Report::Heartbeat {
                schedule: "every 10m".to_owned(),
                run: 0,
            },
        };
        let core = core_with(
            vec![
                queued(1, QueuedMode::Steer, "user text"),
                queued_from(2, QueuedMode::Steer, "child notice", child.clone()),
            ],
            vec![queued(3, QueuedMode::FollowUp, "aborted earlier")],
            vec![queued_from(
                4,
                QueuedMode::Steer,
                "paused admission",
                heartbeat.clone(),
            )],
        );
        let item = |text: &str, origin: InputOrigin| QueuedItem {
            text: text.to_owned(),
            origin,
        };
        let snapshot = session_snapshot(&core);
        assert_eq!(snapshot.queued_count, 4);
        assert_eq!(
            snapshot.steering,
            [
                item("user text", InputOrigin::User),
                item("child notice", child),
                item("paused admission", heartbeat),
            ]
        );
        assert_eq!(
            snapshot.follow_ups,
            [item("aborted earlier", InputOrigin::User)]
        );
    }

    /// The active action rides the projection as the bridge tracked it.
    #[test]
    fn the_active_action_rides_the_snapshot() {
        let mut core = core_with(vec![], vec![], vec![]);
        core.view.as_mut().expect("view").active = Some(eukhe_types::daemon::SessionActionActive {
            kind: "turn".to_string(),
            phase: "preparing".to_string(),
            label: Some("go".to_string()),
        });
        let snapshot = session_snapshot(&core);
        assert_eq!(
            snapshot.active,
            Some(eukhe_types::daemon::SessionActionActive {
                kind: "turn".to_string(),
                phase: "preparing".to_string(),
                label: Some("go".to_string()),
            })
        );
    }

    /// The strip label collapses whitespace and caps at 160 chars.
    #[test]
    fn the_compact_label_matches_the_ts_shape() {
        assert_eq!(compact_action_label("  a   b  "), "a b");
        let long = compact_action_label(&"x".repeat(400));
        assert_eq!(long.chars().count(), 160);
        assert!(long.ends_with("..."));
    }

    /// The roster note's candidates: the kickoff agent message is the task
    /// (before any later user row), the last stopped assistant text is the
    /// report (tool-use turns and empty text never count).
    #[test]
    fn note_candidates_read_the_task_and_the_last_report() {
        let messages = vec![
            json!({ "role": "custom", "customType": "agent_message",
                    "details": { "message": "  map the parser\nthen report" } }),
            json!({ "role": "user", "content": "later user text" }),
            json!({ "role": "assistant", "stopReason": "stop", "timestamp": 10,
                    "content": [{ "type": "text", "text": "first report" }] }),
            json!({ "role": "assistant", "stopReason": "toolUse", "timestamp": 20,
                    "content": [{ "type": "text", "text": "calling a tool" }] }),
            json!({ "role": "assistant", "stopReason": "stop", "timestamp": 30,
                    "content": [{ "type": "text", "text": "  " }] }),
        ];
        assert_eq!(
            note_candidates(messages.into_iter()),
            NoteCandidates {
                task: Some("  map the parser\nthen report".to_string()),
                report: Some(TimedNote {
                    text: "first report".to_string(),
                    at_ms: 10,
                }),
                progress: None,
            }
        );
    }

    /// The note is the newer of report and progress, else the task: its
    /// first non-empty line, whitespace-collapsed and capped at 160 chars.
    #[test]
    fn the_roster_note_prefers_the_newest_report_or_progress() {
        let report = TimedNote {
            text: "\nparser mapped:   three entry points\nsecond line".to_string(),
            at_ms: 30,
        };
        let progress = TimedNote {
            text: "reading lexer.rs".to_string(),
            at_ms: 20,
        };
        let task = Some("map the parser".to_string());
        let notes = [
            roster_note(&NoteCandidates {
                task: task.clone(),
                report: Some(report.clone()),
                progress: Some(progress.clone()),
            }),
            roster_note(&NoteCandidates {
                task: task.clone(),
                report: Some(TimedNote {
                    at_ms: 10,
                    ..report
                }),
                progress: Some(progress),
            }),
            roster_note(&NoteCandidates {
                task,
                report: None,
                progress: None,
            }),
            roster_note(&NoteCandidates {
                task: Some("x".repeat(400)),
                report: None,
                progress: None,
            }),
            roster_note(&NoteCandidates::default()),
        ];
        assert_eq!(
            notes,
            [
                Some("parser mapped: three entry points".to_string()),
                Some("reading lexer.rs".to_string()),
                Some("map the parser".to_string()),
                Some(format!("{}...", "x".repeat(157))),
                None,
            ]
        );
    }
}
