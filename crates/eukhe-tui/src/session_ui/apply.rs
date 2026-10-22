//! The apply concern: the streamed-event pump -- client events, turn
//! updates, assistant/tool rows, and compaction aborts.
use eukhe_types::token_estimate::{chars_to_tokens, text_chars, ESTIMATED_IMAGE_CHARS};

use super::bash::BashSettled;
use super::{
    assistant_message_parts, event_to_update, pop_superseded_attempt_row, AgentView, ChatEntry,
    CompactionReason, CompactionState, DaemonClientEvent, DaemonCommand, Duration, Map,
    MessageBlock, Result, RetryState, SessionUi, StatusKind, ToolResultView, TurnUpdate, Value,
    UI_REQUEST_TIMEOUT_MS,
};
use crate::activity::TurnPhase;
use crate::glyphs::WARN;
use crate::snapshot::TurnOutcome;

/// One backgrounded compaction-abort outcome (the abort supervision's UI
/// recovery): a failed abort request surfaces as the transcript note and
/// clears the stuck compaction loader locally -- when even the abort could
/// not reach the daemon, the loader must not hang waiting for a
/// `compaction_end` that will never come. The session id keeps a stale
/// outcome from touching another session after `/switch` or `/new`.
pub(crate) struct CompactionAbortNote {
    pub(crate) active_session_id: String,
    /// The loader generation the abort addressed: an outcome applies only
    /// to the exact `compaction_start` that was on screen when the abort
    /// was sent -- a newer run's loader is never cleared by a stale one.
    pub(crate) compaction_generation: u64,
    pub(crate) outcome: Result<(), String>,
}

impl SessionUi {
    /// Abort the active turn off the UI loop (TS `interruptOrClearInput`
    /// fires `void abortAndSendQueued()` when streaming, schema 29): the
    /// daemon aborts the run and the queue keeps flowing behind the
    /// settled turn -- parked steering delivers as one batched turn, then
    /// the follow-up lane drains one turn per completed turn; a plain
    /// abort when the abort leaves nothing queued. A daemon without the
    /// schema-29 capability gets the plain abort (TS
    /// `supportsServerCapability` + the `isUnknownDaemonCommandError`
    /// catch, both arms of TS `abortAndSendQueued`). The request never
    /// blocks key handling, and a failure surfaces later as a transcript
    /// note.
    fn abort_turn(&self) {
        let client = self.client.clone();
        let active_session_id = self.active_session_id.clone();
        let notes = self.notes.clone();
        tokio::spawn(async move {
            let mut result = if client.supports_server_capability("abort_and_send_queued") {
                client
                    .request_ok(DaemonCommand::AbortAndSendQueued {
                        id: None,
                        active_session_id: active_session_id.clone(),
                        rest: Map::default(),
                    })
                    .await
            } else {
                client
                    .request_ok(DaemonCommand::Abort {
                        id: None,
                        active_session_id: active_session_id.clone(),
                        rest: Map::default(),
                    })
                    .await
            };
            // A daemon that rejects the command itself gets the plain
            // abort too (TS `isUnknownDaemonCommandError`'s arm).
            if matches!(&result, Err(error) if error.to_string().contains("abort_and_send_queued"))
            {
                result = client
                    .request_ok(DaemonCommand::Abort {
                        id: None,
                        active_session_id,
                        rest: Map::default(),
                    })
                    .await;
            }
            if let Err(error) = result {
                let _ = notes.send(format!("the abort failed: {error:#}"));
            }
        });
    }

    /// Cancel the in-flight compaction off the UI loop (TS
    /// `interruptOrClearInput` fires `abortCompaction()` when the
    /// compaction loader is up -- the agent is not streaming during a
    /// compaction, so the interrupt cancels the run, not a turn): the
    /// request never blocks key handling. A failure surfaces later as a
    /// transcript note and clears the stuck loader locally (the abort
    /// supervision's UI recovery): the daemon's own `compaction_end`
    /// normally clears it, but an abort that could not even reach the
    /// daemon must not leave the UI waiting on an end that never comes.
    fn abort_compaction(&self, compaction_generation: u64) {
        let client = self.client.clone();
        let active_session_id = self.active_session_id.clone();
        let abort_notes = self.compaction_abort_notes.clone();
        tokio::spawn(async move {
            // Via the supervisor even when a direct link serves the
            // session: the direct link IS the wedged worker in the case
            // the supervisor's abort arm exists for.
            let result = client
                .request_ok_via_supervisor(DaemonCommand::AbortCompaction {
                    id: None,
                    active_session_id: active_session_id.clone(),
                    rest: Map::default(),
                })
                .await;
            if let Err(error) = result {
                let _ = abort_notes.send(CompactionAbortNote {
                    active_session_id,
                    compaction_generation,
                    outcome: Err(format!("{error:#}")),
                });
            }
        });
    }

    /// Apply one backgrounded compaction-abort outcome: the failed note
    /// surfaces as a transcript row and the compaction loader clears --
    /// the local recovery when the abort never reached the daemon. An
    /// outcome from a session this UI no longer shows (`/switch`, `/new`
    /// mid-request), or addressed to a loader a newer `compaction_start`
    /// has since replaced, touches nothing.
    pub(crate) fn apply_compaction_abort_outcome(
        &mut self,
        note: CompactionAbortNote,
        view: &mut AgentView,
    ) {
        if note.active_session_id != self.active_session_id
            || note.compaction_generation != view.compaction_generation
        {
            return;
        }
        if let Err(error) = note.outcome {
            self.note(&format!("the compaction abort failed: {error:#}"), view);
            view.compaction = None;
            self.settle_compaction_loader(view);
        }
    }

    /// Apply one background note (a failed abort request) to the transcript.
    pub(crate) fn apply_background_note(&mut self, text: &str, view: &mut AgentView) {
        self.note(text, view);
    }

    /// A compaction succeeded and the durable transcript was rebuilt (it
    /// now starts at the compaction summary): re-fetch it and replace the
    /// view's chat (TS `rebuildChatFromMessages`). Best effort -- a failed
    /// fetch keeps the pushed outcome row instead of an empty transcript.
    pub(crate) async fn rebuild_transcript(&mut self, view: &mut AgentView) {
        self.transcript_stale = false;
        // The rebuilt transcript invalidates the tracked status row.
        self.last_status_index = None;
        let Ok(data) = self
            .bounded_request(
                Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                DaemonCommand::GetMessages {
                    id: None,
                    active_session_id: self.active_session_id.clone(),
                    rest: Map::default(),
                },
            )
            .await
        else {
            return;
        };
        let mut messages = match data
            .get("messages")
            .map(<Vec<eukhe_types::session::AgentMessage> as serde::Deserialize>::deserialize)
        {
            Some(Ok(messages)) => messages,
            Some(Err(error)) => {
                self.error_row(
                    &format!("the transcript could not be decoded: {error}"),
                    view,
                );
                return;
            }
            None => return,
        };
        // A restore notice this view showed before stays out of the
        // rebuilt transcript (`crate::restore_notices`).
        messages.retain(|message| self.restore_notices.shows(&self.session_id, message));
        self.restore_notices.record(&self.session_id, &messages);
        let mut entries = crate::snapshot::transcript_to_entries(&messages);
        // The durable summary entry does not record the `/compact` focus;
        // the live `compaction_end` did (the outcome row pushed before the
        // re-fetch), so the rebuilt summary keeps it.
        for entry in &mut entries {
            let ChatEntry::CompactionSummary {
                summary,
                custom_instructions: rebuilt @ None,
                ..
            } = entry
            else {
                continue;
            };
            *rebuilt = view.chat.iter().find_map(|shown| {
                if let ChatEntry::CompactionSummary {
                    summary: shown_summary,
                    custom_instructions: Some(focus),
                    ..
                } = shown
                {
                    (shown_summary == summary).then(|| focus.clone())
                } else {
                    None
                }
            });
        }
        view.clear_chat(crate::view::TranscriptBreak::Rebuild);
        for entry in entries {
            view.push_entry(entry);
        }
        self.dirty = true;
    }

    /// Take a pending `app.suspend` request (TS `handleCtrlZ`): the
    /// interactive loop performs the process-group suspend cycle; only
    /// the loop owns the renderer that hands the terminal over.
    pub(crate) fn take_suspend_request(&mut self) -> bool {
        std::mem::take(&mut self.suspend_requested)
    }

    /// Take a pending `app.editor.external` request (TS
    /// `openExternalEditor`): the interactive loop performs the editor
    /// child's terminal handoff (the reader stop, the renderer suspend);
    /// only the loop owns those.
    pub(crate) fn take_external_editor_request(&mut self) -> Option<String> {
        self.external_editor_request.take()
    }

    pub(crate) fn apply_client_event(&mut self, event: DaemonClientEvent, view: &mut AgentView) {
        match event {
            DaemonClientEvent::SessionEvent {
                active_session_id,
                event,
                meta_sequence,
            } => {
                if active_session_id != self.active_session_id {
                    return;
                }
                // The live event-sequence tracker (`view::handoff`): the
                // run's stash keys the LATEST sequence the worker has
                // reported -- a turn during this run advances it, so the
                // unchanged-sojourn re-entry matches the post-turn value
                // the next attach reports instead of this run's own stale
                // attach sequence. Monotonic max: a replayed event's
                // sequence never lowers it below the attach's value.
                if meta_sequence > self.last_event_sequence {
                    self.last_event_sequence = meta_sequence;
                }
                // A custom row renders from its `message_start`: a restore
                // notice this view showed already does not show again
                // (`crate::restore_notices`).
                if let eukhe_types::daemon::SessionEvent::MessageStart { message, .. } = &*event {
                    if !self.restore_notices.shows(&self.session_id, message) {
                        return;
                    }
                    self.restore_notices.record(&self.session_id, [message]);
                }
                self.apply_update(event_to_update(&event), view);
            }
            DaemonClientEvent::UndecodableSessionEvent {
                active_session_id,
                error,
            } => {
                if active_session_id == self.active_session_id {
                    self.error_row(
                        &format!("A session event could not be decoded: {error}"),
                        view,
                    );
                }
            }
            DaemonClientEvent::SideQuestionEvent {
                active_session_id,
                event,
            } => {
                if active_session_id == self.active_session_id {
                    self.apply_side_question_event(&event, view);
                }
            }
            // The `bash` tool asks whether one step may run: asked at once,
            // or queued behind the open confirm (answered in order).
            DaemonClientEvent::ShellApproval {
                active_session_id,
                request,
                agent,
            } => {
                if active_session_id == self.active_session_id {
                    self.shell_approvals
                        .push_back((active_session_id, request, agent));
                    if view.confirm.is_none() {
                        self.open_next_shell_approval(view);
                    }
                }
            }
            DaemonClientEvent::SessionClosed {
                active_session_id,
                reason,
            } => {
                if active_session_id == self.active_session_id {
                    self.turn_active = false;
                    self.run_open = false;
                    // Nothing runs for this view any more: no loader, no
                    // retry countdown, no compaction row outlives it.
                    Self::stop_loader(view);
                    view.retry = None;
                    view.compaction = None;
                    // A killed, shut-down, or replaced session is an error
                    // the user must still see after the cancelled turn's
                    // later status rows land (TS `showError`), not a
                    // transient note.
                    match reason.as_str() {
                        "shutdown" => self.error_row(
                            "The Eukhe daemon shut down while this window was attached. The session transcript remains saved; restart Eukhe and reopen it from Agents View.",
                            view,
                        ),
                        "replaced" => self.error_row(
                            "The daemon replaced this agent session with another session. Reopen the current session from Agents View.",
                            view,
                        ),
                        "killed" => self.error_row(
                            "The daemon stopped this agent session. Its transcript remains saved and can be reopened from Agents View.",
                            view,
                        ),
                        _ => self.note(&format!("session closed ({reason})"), view),
                    }
                }
            }
            DaemonClientEvent::DirectLinkLost { active_session_id } => {
                // TS `handleTransportClose`: a direct-transport loss is
                // never itself a session loss -- the interactive loop
                // re-attaches through the supervisor. Only the active
                // session arms the loop; a replaced link (session switch)
                // reports its old session and is ignored here.
                if active_session_id == self.active_session_id {
                    self.transport_lost = Some(active_session_id);
                    // The turn's frames stop until the re-attach: the
                    // loader says so instead of a stale phase.
                    Self::set_working_phase(TurnPhase::Reconnecting, view);
                }
            }
            DaemonClientEvent::DaemonClosing { reason } => {
                // TS #2458 `daemonClosingNotice`: the announcement is the
                // discriminator the interactive loop's shutdown recovery
                // arms on (a bare session stop without it stays stopped).
                self.note(&format!("the daemon is shutting down ({reason})"), view);
                self.daemon_closing_notice = Some(reason);
            }
            // The roster push keeps the subagent summary counts live (TS
            // `subscribeAgentRoster` -> `updateSubagentSummaryLine`).
            DaemonClientEvent::RosterUpdate {
                changed,
                removed,
                resync,
            } => {
                self.apply_roster_update(changed, removed, resync);
                self.update_subagent_summary(view);
                self.dirty = true;
            }
            // A heartbeat catalog change anywhere in the daemon (TS
            // `broadcastGlobal`): the scoped catalog refreshes in the
            // background through the update channel (TS
            // `refreshHeartbeatCatalog`) -- an open `/heartbeats` view
            // re-renders from the landed update, and the activity dock's
            // counts follow the catalog even with the view closed
            // (another client's pause/resume reaches the dock at once).
            DaemonClientEvent::HeartbeatsChanged => {
                self.spawn_heartbeat_refresh();
            }
            // A worker replacement superseded the id this client holds:
            // the interactive loop re-attaches to the session's current id
            // (a silent rebind - the transcript rebuilds from the attach
            // snapshot, no banner).
            DaemonClientEvent::SessionBinding {
                previous_active_session_id,
                active_session_id,
            } => {
                if previous_active_session_id == self.active_session_id
                    && !active_session_id.is_empty()
                    && active_session_id != self.active_session_id
                {
                    self.pending_rebind = Some(active_session_id);
                }
            }
            // Saved-session list frames belong to the agents-view UI; the
            // session view only reads its own session. The session view
            // never subscribes to the state tree: a frame changes nothing
            // on screen, so it never marks the view dirty.
            DaemonClientEvent::SessionListItem { .. }
            | DaemonClientEvent::SessionListProgress { .. }
            | DaemonClientEvent::StateTreeUpdate { .. } => {}
        }
    }

    fn apply_update(&mut self, update: TurnUpdate, view: &mut AgentView) {
        match update {
            TurnUpdate::RunStarted => {
                self.run_open = true;
                self.run_rounds = 0;
                self.run_showed_reply = false;
                self.begin_request(view);
            }
            TurnUpdate::TurnStarted => {
                self.run_rounds += 1;
                self.begin_request(view);
            }
            TurnUpdate::UserMessage(text) => {
                self.speed_clock.prompt_added(text_chars(&text));
                // TS `addMessageToChat`'s user case: a skill block parses
                // into the skill-invocation card plus the trailing
                // argument text as its own user block.
                match crate::custom_message::skill_invocation_entries(&text) {
                    Some(entries) => {
                        for entry in entries {
                            view.push_entry(entry);
                        }
                    }
                    None => view.push_entry(ChatEntry::User { text }),
                }
            }
            // `session_info_changed`: the display name moved (the `/name`
            // path also sets it locally; this is the other-client arm).
            TurnUpdate::SessionInfoChanged { name } => {
                self.session_name = name;
                view.chrome.session_name.clone_from(&self.session_name);
                self.dirty = true;
            }
            // `service_tier_changed`: keep the local tier state current (TS
            // patches the connection state; `/fast` reads it).
            TurnUpdate::ServiceTierChanged { tier } => {
                self.service_tier = Some(tier.as_str().to_string());
                // The tray badge follows the applied tier (the `fast`
                // token for priority).
                view.chrome.service_tier.clone_from(&self.service_tier);
                self.dirty = true;
            }
            TurnUpdate::CustomRow(entry) => {
                view.push_entry(entry);
            }
            TurnUpdate::RetryOutcomeRow(entry) => {
                // The episode's ONE line replaces the failed attempts' rows
                // it settles, live exactly like the rebuild
                // (`transcript_to_entries`): the chat never shows a
                // failure twice.
                while pop_superseded_attempt_row(view) {}
                if matches!(
                    entry,
                    ChatEntry::Status {
                        kind: StatusKind::Error,
                        ..
                    }
                ) {
                    self.turn_error_shown = true;
                }
                view.push_entry(entry);
            }
            TurnUpdate::AssistantMessage {
                message,
                streaming,
                stream_event,
            } => {
                self.apply_assistant_message(&message, streaming, stream_event.as_ref(), view);
            }
            TurnUpdate::ToolExecutionStart {
                tool_call_id,
                tool_name,
                args,
            } => {
                // The failed frame's sweep owns the call: the run's late
                // tool frames land on nothing - not the card, not the
                // pending map, not the loader (TS: no component in the
                // cleared pending map).
                if !self.aborted_tools.contains(&tool_call_id) {
                    crate::snapshot::apply_tool_execution_start(
                        view,
                        &tool_call_id,
                        &tool_name,
                        args,
                    );
                    // TS `tool_execution_start` re-registers the call in the
                    // pending map (a card may predate a pending-state reset or
                    // arrive without its own streamed frame).
                    self.pending_tools.insert(tool_call_id.clone());
                    self.run_showed_reply = true;
                    Self::set_working_phase(TurnPhase::RunningTool, view);
                }
            }
            TurnUpdate::ToolExecutionUpdate {
                tool_call_id,
                partial,
            } => {
                // A `starting` partial (python-kernel bootstrap) owns the
                // loader note (TS `setWorkingMessage`); other updates
                // leave any current note alone. The note rides the
                // landed-result gate: the aborted card's late frames must
                // not clobber the delivered turn's loader.
                let loader_message = crate::snapshot::working_message_from_update(&partial);
                if self.apply_tool_result(&tool_call_id, &partial, false, true, view) {
                    if let (Some(message), Some(working)) = (loader_message, view.working.as_mut())
                    {
                        working.message = Some(message);
                    }
                }
            }
            TurnUpdate::ToolExecutionEnd {
                tool_call_id,
                result,
                is_error,
            } => {
                // The result goes into the next request's prompt.
                self.speed_clock.prompt_added(
                    result
                        .content
                        .iter()
                        .map(|block| match block {
                            eukhe_types::ai::UserContentBlock::Text(text) => text_chars(&text.text),
                            eukhe_types::ai::UserContentBlock::Image(_) => ESTIMATED_IMAGE_CHARS,
                            eukhe_types::ai::UserContentBlock::Raw(_) => 0,
                        })
                        .sum(),
                );
                // The landed-result gate keeps the loader safe: after the
                // interrupt delivers the parked queue, a late end frame from
                // the aborted run must not rewrite the new turn's activity
                // label or clear its loader note.
                if self.apply_tool_result(&tool_call_id, &result, is_error, false, view) {
                    Self::set_working_phase(TurnPhase::Requesting, view);
                    // The tool that owned the loader note finished executing
                    // (TS clears `workingMessage` in the tool's `finally`).
                    if let Some(working) = &mut view.working {
                        working.message = None;
                    }
                }
            }
            TurnUpdate::TurnEnded { outcome } => {
                // Only the engine's own turn_end clears the busy state:
                // trailing `agent_end` frames from the previous turn must
                // not cancel a turn admitted in between (prompt queueing).
                self.streaming_index = None;
                self.turn_ends_seen += 1;
                self.turn_active = false;
                view.retry = None;
                // The turn settled: the bash cards held above the
                // indicator stream into the transcript (TS `turn_end`
                // flushes `pendingBashComponents`).
                Self::flush_pending_bash(view);
                // TS `turn_end` clears the pending tool map after the
                // failed frame's settle: stragglers never leak into the
                // next run.
                self.pending_tools.clear();
                self.aborted_tools.clear();
                match outcome {
                    // The answer's tools ran; the run's next request is
                    // on its way (its `turn_start` follows): the loader
                    // stays up and keeps the turn's clock.
                    TurnOutcome::Continues => self.enter_phase(view, TurnPhase::Requesting),
                    TurnOutcome::Answered | TurnOutcome::Aborted | TurnOutcome::Unreported => {
                        Self::stop_loader(view);
                    }
                    // A failure the chat does not show yet (no failed
                    // message carried it, or its row left with a retry)
                    // gets its row now: a turn never ends without a
                    // visible failure.
                    TurnOutcome::Failed(error) => {
                        Self::stop_loader(view);
                        if !self.turn_error_shown {
                            self.push_failure_row(&error, view);
                        }
                    }
                    // A run that put nothing on screen and ended without
                    // a reply says so instead of falling silent.
                    TurnOutcome::Empty => {
                        Self::stop_loader(view);
                        if !self.run_showed_reply {
                            let step =
                                crate::error_summary::failure_next_step("").unwrap_or_default();
                            view.push_entry(ChatEntry::Status {
                                text: format!(
                                    "{WARN} The model ended the turn without a reply{}{step}",
                                    crate::glyphs::SEP
                                ),
                                kind: StatusKind::Warning,
                            });
                        }
                    }
                }
            }
            TurnUpdate::AutoRetryStart {
                attempt,
                max_attempts,
                delay_ms,
                error_message,
                reason,
            } => {
                // The retry countdown loader replaces the working loader
                // until the loop settles (TS auto_retry_start). A backup
                // reason is a provider-failover switch: the loader names
                // the backup provider the turn re-routes to (no countdown;
                // the switch re-issues immediately).
                //
                // SANCTIONED DIVERGENCE (operator ruling 2026-09-23): the
                // just-failed attempt's error row leaves the chat -- the
                // transient loader line (error + attempt + countdown,
                // updated in place) is the ONE error the chat shows while
                // the episode runs, and the episode's durable outcome row
                // replaces it at the settle. (TS keeps one error row per
                // failed attempt; a 429-storm spammed the chat.)
                if pop_superseded_attempt_row(view) {
                    // The failure is off screen until the episode settles:
                    // the next attempt's answer or its own failure row.
                    self.turn_error_shown = false;
                }
                self.enter_phase(view, TurnPhase::Retrying);
                view.retry = Some(RetryState {
                    attempt,
                    max_attempts,
                    ends_at: std::time::Instant::now() + std::time::Duration::from_millis(delay_ms),
                    error_message,
                    reason,
                });
            }
            TurnUpdate::AutoRetryEnd {
                success: _,
                attempt: _,
                final_error,
                restored_model,
            } => {
                view.retry = None;
                if view.working.is_some() {
                    self.enter_phase(view, TurnPhase::Requesting);
                }
                // A give-up whose final failure is not on screen (the
                // retry wait was cancelled, or its last attempt carried no
                // message) shows it now; the episode's durable outcome
                // row, when one follows, replaces it.
                if let (Some(error), false) = (final_error, self.turn_error_shown) {
                    self.push_failure_row(&error, view);
                }
                // A settled switch restores the primary provider (TS
                // `restoredModel` status line).
                if let Some(restored_model) = restored_model {
                    view.push_entry(ChatEntry::Status {
                        text: format!("Primary provider recovered -- back on {restored_model}"),
                        kind: StatusKind::Info,
                    });
                }
            }
            TurnUpdate::CompactionStart {
                reason,
                custom_instructions,
            } => {
                // TS `startCompactionLoader`: the compaction loader
                // replaces the working loader's row for the run's
                // duration; the loader itself stays up underneath (the
                // turn's clock keeps counting, and a compaction outside a
                // turn starts one). The generation bump retires every
                // in-flight abort outcome that addressed an earlier run's
                // loader.
                self.enter_phase(view, TurnPhase::Compacting);
                view.compaction_generation += 1;
                view.compaction = Some(CompactionState {
                    reason,
                    custom_instructions,
                    // A fresh run starts with an empty live summary:
                    // the deltas of THIS run accumulate from here (a
                    // replayed `compaction_start` after a re-attach
                    // drops the previous run's partial text too).
                    summary: String::new(),
                });
            }
            TurnUpdate::CompactionSummaryDelta { delta } => {
                // One streamed chunk of the summary the compaction
                // model is generating: append onto the live loader's
                // state (the expanded view renders the accumulated
                // text under the loader, nested like the expanded
                // summary row that settles it). A delta without a live
                // loader (a late attach mid-run, a stale frame after
                // `compaction_end`) drops -- the settling end still
                // carries the full summary.
                if let Some(compaction) = view.compaction.as_mut() {
                    compaction.summary.push_str(&delta);
                }
            }
            TurnUpdate::CompactionEnd {
                reason,
                result,
                custom_instructions,
                aborted,
                error_message,
                error_severity,
            } => {
                view.compaction = None;
                self.settle_compaction_loader(view);
                if let Some(result) = result {
                    // A succeeded compaction rebuilt the durable transcript
                    // (it now starts at the compaction summary): show the
                    // outcome row immediately, then re-fetch the transcript
                    // so the compacted-away rows drop (TS
                    // `rebuildChatFromMessages`).
                    view.push_entry(ChatEntry::CompactionSummary {
                        summary: result.summary,
                        tokens_before: result.tokens_before,
                        custom_instructions,
                    });
                    self.transcript_stale = true;
                } else if reason == CompactionReason::Manual {
                    // TS `compaction_end` handling: aborts and error
                    // messages surface only for user-issued compactions,
                    // through `showError`/`showWarning` (whose rows carry
                    // the `! Error: ` / `! ` prefixes).
                    if aborted {
                        view.push_entry(ChatEntry::Status {
                            text: format!("{WARN} Error: Compaction cancelled"),
                            kind: StatusKind::Error,
                        });
                    } else if let Some(message) = error_message {
                        if error_severity == Some(eukhe_types::daemon::ErrorSeverity::Warning) {
                            view.push_entry(ChatEntry::Status {
                                text: format!("{WARN} {message}"),
                                kind: StatusKind::Warning,
                            });
                        } else {
                            view.push_entry(ChatEntry::Status {
                                text: format!("{WARN} Error: {message}"),
                                kind: StatusKind::Error,
                            });
                        }
                    }
                }
            }
            TurnUpdate::Idle => {
                // A run that made no model request (stopped while it
                // prepared or waited) never sends the `turn_end` its
                // prompt's admission counts on: its end stands in for it.
                if self.run_open && self.run_rounds == 0 {
                    self.turn_ends_seen += 1;
                }
                self.run_open = false;
                // The run is over unless a later prompt of this client is
                // still owed its turn (admitted in between, or traveling).
                let owed =
                    self.prompt_in_flight > 0 || self.turn_ends_seen < self.last_prompt_turn_end;
                if !owed {
                    self.turn_active = false;
                }
                if !self.turn_active {
                    view.retry = None;
                    // A compaction still running keeps its loader; its
                    // `compaction_end` settles it.
                    if view.compaction.is_none() {
                        Self::stop_loader(view);
                    }
                }
            }
            TurnUpdate::GoalUpdate(goal) => {
                self.apply_goal_update(goal, view);
            }
            TurnUpdate::ChatTurnWait { waiting } => {
                // The turn waits for another window's turn on the shared
                // chat: the loader note says so until the wait ends (a
                // note the wait did not set stays).
                if let Some(working) = &mut view.working {
                    let notice = eukhe_types::daemon::CHAT_TURN_WAIT_NOTICE;
                    if waiting {
                        working.message = Some(notice.to_string());
                    } else if working.message.as_deref() == Some(notice) {
                        working.message = None;
                    }
                }
            }
            TurnUpdate::PromptProgress(progress) => {
                self.speed_clock.prompt_progress(progress);
            }
            TurnUpdate::MemoryUpdate(update) => {
                self.apply_memory_update(&update, view);
            }
            TurnUpdate::AgentRelay(relay) => {
                self.apply_agent_relay(relay, view);
            }
            TurnUpdate::BashStart {
                command,
                exclude_from_context,
                run,
            } => {
                self.apply_bash_start(
                    &command,
                    exclude_from_context,
                    run.transient,
                    run.run_id.as_deref(),
                    view,
                );
            }
            TurnUpdate::BashOutput { chunk } => {
                self.apply_bash_output(&chunk, view);
            }
            TurnUpdate::BashEnd {
                exit_code,
                cancelled,
                output,
                omitted,
                artifact,
                error_message,
                run,
            } => {
                self.apply_bash_end(
                    exit_code,
                    cancelled,
                    BashSettled {
                        output,
                        omitted,
                        artifact,
                    },
                    error_message,
                    run.transient,
                    run.run_id.as_deref(),
                    view,
                );
            }
            TurnUpdate::QueueUpdated(queued) => {
                view.queued = queued;
                // A queue change under an active browse reconciles the
                // selection (TS `refreshQueueSelectionAt`): the cursor
                // survives only when the addressed item is unchanged; a
                // stale selection drops and its stashed draft returns to
                // the editor.
                if let Some(selected) = self.queue_selection.selected() {
                    let (lane, index, text) =
                        (selected.lane, selected.index, selected.text.clone());
                    if let Some(draft) =
                        self.queue_selection
                            .refresh_at(&view.queued, lane, index, &text)
                    {
                        if view.editor.get_text() == text {
                            view.editor.set_text(&draft);
                        }
                    }
                }
                self.sync_queue_selection(view);
            }
            TurnUpdate::StatusUpdate => {}
        }
        self.sync_speed(view);
        self.dirty = true;
    }

    /// TS `interruptOrClearInput`'s abort ladder, shared by the Ctrl+C and
    /// Escape interrupts: a compacting session aborts the compaction run,
    /// a streaming turn aborts through `abort_and_send_queued` (schema 29),
    /// and a running user bash aborts alongside. The side-question abort
    /// stays at the call sites -- the two keys dispose of its pane
    /// differently.
    pub(super) fn interrupt_running_work(&self, view: &AgentView) {
        if view.compaction.is_some() {
            // The compaction loader is up (TS `isAgentCompacting()`):
            // the interrupt cancels the compaction run only -- the agent
            // is not streaming, so no turn abort goes out, exactly like
            // the TS interrupt key.
            self.abort_compaction(view.compaction_generation);
        } else if self.turn_active {
            // TS shows no transient abort hint: the aborted turn's own
            // assistant row carries the interrupt (the red "Operation
            // aborted" error row inside the message component), so
            // nothing is noted here.
            self.abort_turn();
        }
        // A running user-bash command aborts the same way (TS
        // `interruptOrClearInput` fires `void abortBash()`): the settled
        // run reports cancelled through its bash_end.
        if self.user_bash_running {
            self.abort_user_bash();
        }
    }

    /// Apply an assistant message frame: an open streaming message is
    /// updated in place; otherwise the message expands into a chat component
    /// plus a card per tool call.
    fn apply_assistant_message(
        &mut self,
        message: &eukhe_types::ai::AssistantMessage,
        streaming: bool,
        stream_event: Option<&eukhe_types::daemon::StreamUpdate>,
        view: &mut AgentView,
    ) {
        if let Some(event) = stream_event {
            Self::track_stream_activity(event, view);
        }
        let (blocks, tool_calls) = assistant_message_parts(message);
        // A message_start always opens a new streaming message (the engine
        // emits one per provider call); later frames update it in place.
        let starts_message = matches!(stream_event, Some(eukhe_types::daemon::StreamUpdate::Start));
        let usage_output = message.usage.output;
        if streaming {
            if starts_message {
                self.working_tokens.start_message();
            }
            let content_chars: u64 = blocks
                .iter()
                .map(|block| match block {
                    MessageBlock::Text(text) | MessageBlock::Thinking(text) => text_chars(text),
                })
                .sum();
            let current = self
                .working_tokens
                .apply_streaming(usage_output, content_chars);
            if let Some(working) = &mut view.working {
                working.tokens = working.tokens.max(current);
            }
            // This message's own output so far, tool-call arguments
            // included: the provider's count when it streams one, else the
            // content at the one token estimate.
            let tool_chars: u64 = tool_calls
                .iter()
                .map(|(_, name, args)| text_chars(name) + text_chars(&args.to_string()))
                .sum();
            self.speed_clock.streamed(
                std::time::Instant::now(),
                usage_output.max(chars_to_tokens(content_chars + tool_chars)),
            );
        } else {
            self.working_tokens.settle(usage_output);
            self.record_speed_sample(message, view);
            self.speed_clock.settled(message, std::time::Instant::now());
        }
        if let Some(text) = blocks.iter().rev().find_map(|block| match block {
            MessageBlock::Text(text) => Some(text.clone()),
            MessageBlock::Thinking(_) => None,
        }) {
            self.last_assistant_text = Some(text);
        }
        let has_tool_calls = !tool_calls.is_empty();
        if has_tool_calls
            || blocks.iter().any(|block| match block {
                MessageBlock::Text(text) => !text.trim().is_empty(),
                MessageBlock::Thinking(_) => false,
            })
        {
            self.run_showed_reply = true;
        }
        // A message_start always opens a new streaming message (the engine
        // emits one per provider call); later frames update it in place.
        if starts_message {
            self.streaming_index = None;
        }
        match self.streaming_index {
            Some(index) => {
                if let Some(ChatEntry::Assistant(open)) = view.chat.get_mut(index) {
                    open.blocks = blocks;
                    open.has_tool_calls = has_tool_calls;
                    open.streaming = streaming;
                }
                view.mark_entry_stale(index);
            }
            None => {
                if !blocks.is_empty() {
                    view.push_entry(ChatEntry::Assistant(Box::new(
                        crate::chat::AssistantMessage {
                            blocks,
                            has_tool_calls,
                            streaming,
                            error: None,
                            aborted: false,
                        },
                    )));
                    self.streaming_index = Some(view.chat.len() - 1);
                }
            }
        }
        for (id, name, args) in &tool_calls {
            // A streamed tool call first appears queued; the execution start
            // event flips it to running, and later frames refresh its name
            // and args while they stream (TS `updateArgs` + the latest
            // streaming call winning at component creation). The failed
            // run's late frames touch no card either (the settled card
            // keeps its sweep-written result).
            if !self.aborted_tools.contains(id) {
                crate::snapshot::apply_streamed_tool_card(view, id, name, args);
            }
            if starts_message {
                // A new assistant message re-arms a reused id (TS builds a
                // fresh pending component for the new invocation); a late
                // `message_update` from a failed run must not. The re-armed
                // invocation's next streamed frame pushes its own fresh card
                // -- the settled card is skipped by its `aborted` flag, the
                // way TS's cleared pending map forces a new component.
                self.aborted_tools.remove(id);
            }
            // TS `message_update` registers every streamed call in the
            // pending map (`message_start` and the final frame never do:
            // their cards either already settled or get the failed frame's
            // sweep); the failed run's late frames stay out too.
            if streaming && !starts_message && !self.aborted_tools.contains(id) {
                self.pending_tools.insert(id.clone());
            }
        }
        if !streaming {
            let open = self.streaming_index.take();
            self.finalize_assistant_error(message, &tool_calls, open, view);
        }
    }

    /// The final frame of a failed assistant message renders its error row
    /// (TS renders it inside the assistant component): `aborted` always
    /// shows, `error` only when the message carries no tool calls (the
    /// pending cards carry the failure then). The row renders inside the
    /// message's own component -- the open streaming entry when one exists,
    /// otherwise a fresh entry: TS creates one component per assistant
    /// message (`message_start`), so a content-less provider failure stacks
    /// its own error row per failed attempt instead of decorating the
    /// previous reply (TS `AssistantMessageComponent.rebuild`).
    fn finalize_assistant_error(
        &mut self,
        message: &eukhe_types::ai::AssistantMessage,
        tool_calls: &[(String, String, Value)],
        open: Option<usize>,
        view: &mut AgentView,
    ) {
        // TS `message_end`'s failed-frame block: an aborted run's row text
        // is the client's own -- the retry count and the working-elapsed
        // suffix never ride the wire (the rebuild keeps the stored
        // "Operation aborted") -- and every still-pending tool card settles
        // with the failure text; late result frames land on nothing.
        let stop_reason = message.stop_reason;
        let abort_text = if stop_reason == eukhe_types::ai::StopReason::Aborted {
            Some(crate::chat::live_abort_text(
                view.retry.as_ref().map_or(0, |retry| retry.attempt),
                view.working_since.map(|since| since.elapsed().as_secs()),
            ))
        } else {
            None
        };
        if abort_text.is_some() || stop_reason == eukhe_types::ai::StopReason::Error {
            let settle_text = abort_text.clone().unwrap_or_else(|| {
                message
                    .error_message
                    .as_deref()
                    .filter(|text| !text.is_empty())
                    .unwrap_or("Error")
                    .to_string()
            });
            crate::snapshot::settle_pending_tool_cards(
                view,
                &mut self.pending_tools,
                &mut self.aborted_tools,
                &settle_text,
            );
        }
        let Some(error) = crate::snapshot::assistant_error_row(message, tool_calls) else {
            return;
        };
        let error = match abort_text {
            Some(text) => crate::snapshot::AssistantErrorRow {
                text,
                aborted: true,
            },
            None => error,
        };
        self.turn_error_shown = true;
        if let Some(index) = open {
            if let Some(ChatEntry::Assistant(entry)) = view.chat.get_mut(index) {
                entry.error = Some(error.text);
                entry.aborted = error.aborted;
                view.mark_entry_stale(index);
                return;
            }
        }
        // The message rendered no component (empty content): TS still
        // renders the message's own error component, so the failure stacks
        // as a separate row instead of attaching to the last assistant.
        view.push_entry(ChatEntry::Assistant(Box::new(
            crate::chat::AssistantMessage {
                blocks: Vec::new(),
                has_tool_calls: false,
                streaming: false,
                error: Some(error.text),
                aborted: error.aborted,
            },
        )));
    }

    /// Attach a (partial or final) tool result to the matching card.
    /// Returns whether the result landed (a card exists and is not
    /// aborted): the caller's loader work rides the same gate -- the
    /// aborted card's late frames must leave the loader untouched too
    /// (TS `tool_execution_end` does nothing without a pending
    /// component).
    fn apply_tool_result(
        &mut self,
        tool_call_id: &str,
        result: &eukhe_types::daemon::ToolOutput,
        is_error: bool,
        partial: bool,
        view: &mut AgentView,
    ) -> bool {
        let result = ToolResultView::new(result, is_error);
        // The result lands on the newest card carrying the id: a re-armed
        // invocation pushed its own card, and the older settled card keeps
        // its sweep-written result (TS's pending map only ever holds the
        // current component).
        let card_index = view
            .chat
            .iter()
            .rposition(|entry| matches!(entry, ChatEntry::Tool(card) if card.id == tool_call_id));
        if let Some(index) = card_index {
            if let Some(ChatEntry::Tool(card)) = view.chat.get_mut(index) {
                // The failed frame's sweep owns the call: the tool's late
                // result frames land on nothing (TS `tool_execution_end`
                // finds no component in the cleared pending map).
                if self.aborted_tools.contains(tool_call_id) || card.aborted {
                    return false;
                }
                card.result = Some(result);
                card.result_partial = partial;
                if !partial {
                    card.ended_at = Some(std::time::Instant::now());
                    self.pending_tools.remove(tool_call_id);
                }
                view.mark_entry_stale(index);
                return true;
            }
        }
        false
    }

    /// Move an up loader to `phase` (the agent-activity tracker subset): a
    /// tool frame never raises a loader on its own -- a late frame of an
    /// ended run must not leave one behind.
    fn set_working_phase(phase: TurnPhase, view: &mut AgentView) {
        if let Some(working) = &mut view.working {
            working.phase = phase;
            working.download = false;
        }
    }

    /// A model request began (`agent_start` or `turn_start`): the turn is
    /// busy, its loader waits on the model (keeping the clock the Enter, a
    /// queued admission, or an earlier request of the run started), and
    /// the request's failure state starts clean.
    fn begin_request(&mut self, view: &mut AgentView) {
        self.turn_active = true;
        self.turn_error_shown = false;
        self.begin_memory_request(view);
        // TS `agent_start` clears the pending tool map: no card
        // from a previous run settles on this one's failure.
        self.pending_tools.clear();
        self.aborted_tools.clear();
        self.enter_phase(view, TurnPhase::Requesting);
        self.speed_clock.request_started(std::time::Instant::now());
    }

    /// A failure row for a turn whose failure the chat does not show yet:
    /// the failed-attempt row shape (an error-only assistant entry), so it
    /// renders the failure's next step and the episode's outcome row
    /// replaces it like any failed attempt.
    fn push_failure_row(&mut self, error: &str, view: &mut AgentView) {
        view.push_entry(ChatEntry::Assistant(Box::new(
            crate::chat::AssistantMessage {
                blocks: Vec::new(),
                has_tool_calls: false,
                streaming: false,
                error: Some(format!("Error: {error}")),
                aborted: false,
            },
        )));
        self.turn_error_shown = true;
    }

    /// The loader after a compaction settled: the run it ran inside goes
    /// on (its next request follows), a submit still traveling keeps its
    /// send phase, and a compaction outside any turn takes the loader down.
    pub(super) fn settle_compaction_loader(&mut self, view: &mut AgentView) {
        if self.turn_active || self.run_open {
            self.enter_phase(view, TurnPhase::Requesting);
        } else if self.prompt_in_flight > 0 {
            self.enter_phase(view, TurnPhase::Sending);
        } else {
            Self::stop_loader(view);
        }
    }
}
