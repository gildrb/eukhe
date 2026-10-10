//! The worker's client-visible surface: summaries, connection state, the
//! queue projection, the roster push, and the event emission family. Every
//! read comes from the shown conversation's event mirror on the core, so a
//! summary never waits on the Harness.

use super::durable_host::bridge::{QueuedMode, ShownView};
use super::durable_host::wire_messages::entry_wire_message;
use super::lifecycle::active_lifecycle;
use super::session_core::InjectionKind;
use super::{
    create_daemon_event_meta, AgentConnectionState, Arc, DaemonOutbound, DaemonSessionClosedReason,
    EventPump, Map, Mutex, OutboundFrame, Result, SessionActionSnapshot, SessionCore, SessionSlot,
    Value, Worker,
};

use eukhe_types::pi_ai::Model;
use serde_json::json;

use crate::types::SessionSummary;

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

/// The shown conversation's thinking level (`off` when unset).
pub(crate) fn thinking_level(core: &SessionCore) -> String {
    core.view
        .as_ref()
        .and_then(|view| view.translator.mirror().agent.thinking_level)
        .map_or("off", |level| level.as_str())
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
        Some(model) => eukhe_pi_ai::models::get_supported_thinking_levels(&model)
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
            &thinking_level(core),
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
            thinking_level: thinking_level(core),
            service_tier: crate::setting_switches::service_tier_wire_name(
                core.active_service_tier
                    .unwrap_or(eukhe_types::ai::ServiceTier::Auto),
            )
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
                    .filter(|entry| entry.kind == "pi.compaction")
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
    pub(crate) fn emit_worker_event(&self, event: Value) {
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
pub(crate) fn emit_event_locked(core: &mut SessionCore, events: &EventPump, event: Value) {
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
        json!({ "type": "session_action_update", "actions": snapshot }),
    );
}

pub(crate) fn emit_worker_event_with(
    core: &Arc<Mutex<SessionCore>>,
    events: &Arc<EventPump>,
    event: Value,
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
            &thinking_level(&core),
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
fn first_message(view: &ShownView) -> Option<String> {
    view.translator
        .mirror()
        .entries
        .iter()
        .filter(|entry| entry.kind == "pi.user")
        .find_map(entry_wire_message)
        .map(|message| crate::types::message_text(&message))
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

pub(crate) fn session_summary(
    core: &SessionCore,
    thinking_level: &str,
    model: Option<Value>,
    bash_running: bool,
    quota_parked: bool,
) -> SessionSummary {
    let streaming = core.is_busy();
    let compacting = core.is_compacting();
    let queued = core.view.as_ref().map_or(0, |view| view.inbox.len())
        + core.suspended.len()
        + core.held.len();
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
        attached_clients: u32::try_from(core.attached_client_ids.len()).unwrap_or(u32::MAX),
        message_count: messages,
        session_actions: session_snapshot(core),
        streaming_message: None,
        created: core.created_at.clone(),
        modified: last_activity_at,
        first_message: view.and_then(first_message),
        parent_session_path: None,
        parent_active_session_id: core.parent_active_session_id.clone(),
        parent_session_id: core.parent_session_id.clone(),
        rlm_child_id: core.rlm_child_id.clone(),
        usage: view.map(|view| json!(view.translator.mirror().usage)),
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
/// inputs an abort suspended and the admissions an input pause holds.
/// The riders mark the daemon-classified parked rows (child status
/// notices, injected prompts) by lane index; `active` is the run the
/// bridge's active action tracks (the strip's Starting row).
pub(crate) fn session_snapshot(core: &SessionCore) -> SessionActionSnapshot {
    let inbox = core
        .view
        .as_ref()
        .map_or(&[][..], |view| view.inbox.as_slice());
    let queued = || inbox.iter().chain(&core.suspended).chain(&core.held);
    let lane = |mode: QueuedMode| {
        queued()
            .filter(|input| input.mode == mode)
            .map(|input| input.text.clone())
            .collect::<Vec<String>>()
    };
    let indices = |mode: QueuedMode, kind: InjectionKind| {
        queued()
            .filter(|input| input.mode == mode)
            .enumerate()
            .filter(|(_, input)| core.injected.get(&input.id) == Some(&kind))
            .map(|(index, _)| index)
            .collect::<Vec<usize>>()
    };
    SessionActionSnapshot {
        queued_count: u32::try_from(queued().count()).unwrap_or(u32::MAX),
        steering: lane(QueuedMode::Steer),
        follow_ups: lane(QueuedMode::FollowUp),
        rlm_child_status: crate::types::QueueLaneIndices {
            steering: indices(QueuedMode::Steer, InjectionKind::ChildStatusNotice),
            follow_up: indices(QueuedMode::FollowUp, InjectionKind::ChildStatusNotice),
        },
        injected_prompts: crate::types::QueueLaneIndices {
            steering: indices(QueuedMode::Steer, InjectionKind::InjectedPrompt),
            follow_up: indices(QueuedMode::FollowUp, InjectionKind::InjectedPrompt),
        },
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
    use super::super::session_core::InjectionKind;
    use super::*;

    fn queued(id: u64, mode: QueuedMode, text: &str) -> QueuedInput {
        QueuedInput {
            id: SubmissionId::from_number(id),
            mode,
            text: text.to_owned(),
            content: eukhe_types::pi_ai::UserContent::Text(text.to_owned()),
        }
    }

    /// A core with the given inbox and rider provenance.
    fn core_with(
        inbox: Vec<QueuedInput>,
        suspended: Vec<QueuedInput>,
        held: Vec<QueuedInput>,
        injected: Vec<(u64, InjectionKind)>,
    ) -> SessionCore {
        let mut core = SessionCore::test_core("/tmp".to_string());
        let snapshot: SnapshotEvent = serde_json::from_value(json!({
            "entries": [], "tools": [], "compactions": [], "inbox": [],
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
        core.injected = injected
            .into_iter()
            .map(|(id, kind)| (SubmissionId::from_number(id), kind))
            .collect();
        core
    }

    /// The riders mark exactly the daemon-classified parked rows, by lane
    /// index (lane-relative, like the old projection); a same-text user
    /// row never flags, and withdrawn inputs ride the strip with the
    /// inbox ones.
    #[test]
    fn the_riders_mark_the_injected_rows_by_lane_index() {
        let core = core_with(
            vec![
                queued(1, QueuedMode::Steer, "user text"),
                queued(2, QueuedMode::Steer, "[child-exited: no-reply child:a]"),
            ],
            vec![queued(3, QueuedMode::FollowUp, "aborted earlier")],
            vec![queued(4, QueuedMode::Steer, "paused admission")],
            vec![
                (2, InjectionKind::ChildStatusNotice),
                (4, InjectionKind::InjectedPrompt),
            ],
        );
        let snapshot = session_snapshot(&core);
        assert_eq!(snapshot.queued_count, 4);
        assert_eq!(
            snapshot.steering,
            [
                "user text",
                "[child-exited: no-reply child:a]",
                "paused admission"
            ]
        );
        assert_eq!(snapshot.follow_ups, ["aborted earlier"]);
        assert_eq!(snapshot.rlm_child_status.steering, vec![1]);
        assert!(snapshot.rlm_child_status.follow_up.is_empty());
        assert_eq!(snapshot.injected_prompts.steering, vec![2]);
        assert!(snapshot.injected_prompts.follow_up.is_empty());

        // The wire omits an empty rider entirely (the TS shape).
        let wire = serde_json::to_value(&snapshot).expect("wire");
        assert_eq!(
            wire["rlmChildStatus"],
            json!({ "steering": [1] }),
            "the rider carries its lane indices, the empty lane omitted"
        );
        assert_eq!(wire["injectedPrompts"], json!({ "steering": [2] }));
    }

    /// A notice-free projection stays the TS wire shape: neither rider
    /// serializes.
    #[test]
    fn a_notice_free_projection_has_no_riders() {
        let core = core_with(
            vec![queued(1, QueuedMode::FollowUp, "plain")],
            vec![],
            vec![],
            vec![],
        );
        let wire = serde_json::to_value(session_snapshot(&core)).expect("wire");
        assert!(wire.get("rlmChildStatus").is_none());
        assert!(wire.get("injectedPrompts").is_none());
    }

    /// The active action rides the projection as the bridge tracked it.
    #[test]
    fn the_active_action_rides_the_snapshot() {
        let mut core = core_with(vec![], vec![], vec![], vec![]);
        core.view.as_mut().expect("view").active = Some(crate::types::SessionActionActive {
            kind: "turn".to_string(),
            phase: "preparing".to_string(),
            label: Some("go".to_string()),
        });
        let snapshot = session_snapshot(&core);
        assert_eq!(
            snapshot.active,
            Some(crate::types::SessionActionActive {
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
}
