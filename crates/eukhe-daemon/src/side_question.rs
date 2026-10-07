//! The worker's live side-question runs.
//!
//! Port of the TS daemon-mode side-question surface: the run registry
//! (`sideQuestionRuns`), the `start_side_question`/`abort_side_question`
//! handlers with their exact error strings, and the `side_question_event`
//! frames the worker pushes to the supervisor. The answer is one ephemeral
//! model request over the main conversation's context (its model, thinking
//! level, system prompt, and tool declarations, so the provider-side cache
//! prefix holds); nothing of the run enters the session.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use eukhe_chord::context::{AbortController, AbortSignal, Context, BACKGROUND_CONTEXT};
use eukhe_core::session_engine::side_question::{side_question_prompt, SideQuestionTurn};
use eukhe_pi_ai::models::ModelsSimpleStreamOptions;
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Message, ModelThinkingLevel,
    StopReason, ThinkingLevel, UserContent, UserMessage,
};
use futures::StreamExt;
use serde_json::{json, Map, Value};

use crate::engine::{
    side_question_event_value, SideQuestionOutcome, SideQuestionRequest,
    SIDE_QUESTION_STATUS_RUNNING,
};
use crate::protocol::{response_failure, response_success, DaemonOutbound, DaemonResponse};
use crate::worker::{EventPump, HostedSession, OutboundFrame, SessionSlot};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// A live run (TS `sideQuestionRuns` entries): which client owns it and how
/// to abort it.
struct SideQuestionRun {
    client_id: String,
    abort: AbortController,
}

/// The worker's side-question machinery: registry plus the command handlers.
pub(crate) struct SideQuestionManager {
    session: SessionSlot,
    events: Arc<EventPump>,
    active_session_id: String,
    runs: Arc<Mutex<HashMap<String, SideQuestionRun>>>,
    /// Set (under the registry lock) once a close path (`shutdown`, `kill`)
    /// begins aborting: the close must own the registry's tail — no run may
    /// be admitted after the aborts, or its pane would wedge on a turn no
    /// terminal event will ever settle when the worker exits.
    closing: AtomicBool,
}

impl SideQuestionManager {
    pub(crate) fn new(
        session: SessionSlot,
        events: Arc<EventPump>,
        active_session_id: String,
    ) -> Self {
        SideQuestionManager {
            session,
            events,
            active_session_id,
            runs: Arc::new(Mutex::new(HashMap::new())),
            closing: AtomicBool::new(false),
        }
    }

    /// `start_side_question` (TS handler): one run per client per session;
    /// the response acknowledges before the run answers, results stream as
    /// `side_question_event` frames.
    pub(crate) fn start(&self, payload: &Value) -> DaemonResponse {
        let side_question_id = payload
            .get("sideQuestionId")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        if side_question_id.is_empty() {
            return response_failure(
                None,
                "start_side_question",
                "Side question id is required",
                None,
            );
        }
        let question = payload
            .get("question")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string();
        if question.is_empty() {
            return response_failure(
                None,
                "start_side_question",
                "Question cannot be empty",
                None,
            );
        }
        let Some(hosted) = self.session.get() else {
            return response_failure(
                None,
                "start_side_question",
                "Session is still initializing",
                None,
            );
        };
        let client_id = payload
            .get("clientId")
            .and_then(Value::as_str)
            .unwrap_or("anonymous")
            .to_string();
        let previous_turns: Vec<SideQuestionTurn> = payload
            .get("previousTurns")
            .and_then(Value::as_array)
            .map(|turns| {
                turns
                    .iter()
                    .filter_map(|turn| serde_json::from_value(turn.clone()).ok())
                    .collect()
            })
            .unwrap_or_default();

        let controller = AbortController::new();
        {
            let mut runs = self.runs.lock().unwrap();
            // The admission check rides the registry lock: `abort_all` sets
            // `closing` under the same lock before it aborts, so a start is
            // either admitted before the close's aborts (and aborted with
            // the rest) or rejected once the close owns the registry.
            if self.closing.load(Ordering::SeqCst) {
                return response_failure(
                    None,
                    "start_side_question",
                    &format!("Active session {} is closing", self.active_session_id),
                    None,
                );
            }
            if runs.contains_key(&side_question_id) {
                return response_failure(
                    None,
                    "start_side_question",
                    &format!("Side question already exists: {side_question_id}"),
                    None,
                );
            }
            if runs.values().any(|run| run.client_id == client_id) {
                return response_failure(
                    None,
                    "start_side_question",
                    "A side question is already running for this client and session",
                    None,
                );
            }
            runs.insert(
                side_question_id.clone(),
                SideQuestionRun {
                    client_id,
                    abort: controller.clone(),
                },
            );
        }
        self.spawn_run(
            hosted,
            SideQuestionRequest {
                side_question_id,
                question,
                previous_turns,
            },
            controller.signal(),
        );
        response_success(None, "start_side_question", None)
    }

    /// `abort_side_question` (TS handler): only the owner client can abort.
    pub(crate) fn abort(&self, payload: &Value) -> DaemonResponse {
        let side_question_id = payload
            .get("sideQuestionId")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let client_id = payload
            .get("clientId")
            .and_then(Value::as_str)
            .unwrap_or("anonymous");
        let runs = self.runs.lock().unwrap();
        let aborted = match runs.get(side_question_id) {
            Some(run) if run.client_id == client_id => {
                run.abort.abort(None);
                true
            }
            _ => false,
        };
        response_success(
            None,
            "abort_side_question",
            Some(json!({ "aborted": aborted })),
        )
    }

    /// Abort every run owned by `client_id` (TS `abortSideQuestionsFor`),
    /// the detach path. The entries STAY registered: each run drops its
    /// own entry and queues its terminal cancelled event under one registry
    /// hold, so the registry only drains after the frames queued — a
    /// detach racing a close cannot empty the registry underneath the
    /// close's settle and let the worker exit before the cancelled events
    /// reached the pump.
    pub(crate) fn abort_for_client(&self, client_id: &str) {
        let runs = self.runs.lock().unwrap();
        for run in runs.values() {
            if run.client_id == client_id {
                run.abort.abort(None);
            }
        }
    }

    /// Abort every live run (session close) and close the admission gate.
    /// The run tasks observe the abort and settle through the terminal
    /// path, which frees the registry entry and queues the cancelled event
    /// under one registry hold, so the drained registry means every
    /// cancelled event was queued.
    pub(crate) fn abort_all(&self) {
        let runs = self.runs.lock().unwrap();
        self.closing.store(true, Ordering::SeqCst);
        for run in runs.values() {
            run.abort.abort(None);
        }
    }

    /// Abort every live run and wait (bounded) for their terminal events to
    /// queue on the event pump. The close paths (`shutdown`, `kill`) must
    /// deliver the cancelled events before the process exits (TS
    /// `closeSession` aborts the session's side questions per attached
    /// client before the client sockets end).
    pub(crate) async fn abort_all_and_settle(&self, settle_timeout: Duration) {
        self.abort_all();
        let deadline = tokio::time::Instant::now() + settle_timeout;
        loop {
            let drained = self.runs.lock().unwrap().is_empty();
            if drained || tokio::time::Instant::now() >= deadline {
                return;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    }

    /// Spawn the run task: it emits the event frames and owns the registry
    /// lifetime.
    fn spawn_run(
        &self,
        hosted: Arc<HostedSession>,
        request: SideQuestionRequest,
        signal: AbortSignal,
    ) {
        let runs = Arc::clone(&self.runs);
        let events = Arc::clone(&self.events);
        let active_session_id = self.active_session_id.clone();
        tokio::spawn(async move {
            // The run opens with a running event before the model streams
            // anything (TS emits `running` at the start of the done chain).
            let emit_running = |answer: &str| {
                emit_side_question_frame(
                    &events,
                    &active_session_id,
                    side_question_event_value(&request, answer, SIDE_QUESTION_STATUS_RUNNING, None),
                );
            };
            emit_running("");
            let outcome = run_side_question(&hosted, &request, &signal, &emit_running).await;
            let event = side_question_event_value(
                &request,
                outcome.answer(),
                outcome.status_str(),
                outcome.error_message(),
            );
            // The registry entry drops BEFORE the terminal frame queues, and
            // both run under ONE registry hold: a same-id restart that reacts
            // to the cancelled event can only take the lock after this hold
            // released, so it reads a registry where the id is already free.
            // The shared hold keeps the close paths' settle contract: the
            // drained registry means every terminal event was queued.
            let mut runs = runs.lock().unwrap();
            runs.remove(&request.side_question_id);
            emit_side_question_frame(&events, &active_session_id, event);
        });
    }
}

/// pi-ai `reasoning` of a thinking level; `off` sends none.
fn reasoning(level: ModelThinkingLevel) -> Option<ThinkingLevel> {
    match level {
        ModelThinkingLevel::Off => None,
        ModelThinkingLevel::Minimal => Some(ThinkingLevel::Minimal),
        ModelThinkingLevel::Low => Some(ThinkingLevel::Low),
        ModelThinkingLevel::Medium => Some(ThinkingLevel::Medium),
        ModelThinkingLevel::High => Some(ThinkingLevel::High),
        ModelThinkingLevel::Xhigh => Some(ThinkingLevel::Xhigh),
        ModelThinkingLevel::Max => Some(ThinkingLevel::Max),
    }
}

/// The text blocks of an assistant message, joined.
fn assistant_text(message: &AssistantMessage) -> String {
    message
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect()
}

fn user_message(text: String) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(text),
        timestamp: 0,
    })
}

/// Answer one side question: the main conversation's model context, the
/// earlier side turns, then the question, as one ephemeral request. Each
/// streamed text update reaches `on_update`; `signal` aborts the request.
async fn run_side_question(
    hosted: &HostedSession,
    request: &SideQuestionRequest,
    signal: &AbortSignal,
    on_update: &(dyn Fn(&str) + Send + Sync),
) -> SideQuestionOutcome {
    let failed = |error: String| SideQuestionOutcome::Failed {
        answer: String::new(),
        error,
    };
    let main = match hosted.main() {
        Ok(main) => main,
        Err(error) => return failed(error.to_string()),
    };
    let (agent, view) = match futures::try_join!(main.agent(cx()), main.context(cx())) {
        Ok(read) => read,
        Err(error) => return failed(error.to_string()),
    };
    let Some(model) = agent.model.as_ref().and_then(|model| {
        hosted
            .deps()
            .models
            .get_model(&model.provider, &model.model_id)
    }) else {
        return failed("Select a model before asking a side question".to_string());
    };
    // The main context first (system prompt and tool declarations ride its
    // system messages), then the replayed side turns, then the question.
    let mut messages = view.messages;
    for (index, turn) in request.previous_turns.iter().enumerate() {
        messages.push(user_message(side_question_prompt(
            &turn.question,
            index == 0,
        )));
        let mut answer: AssistantMessage = match serde_json::from_value(json!({
            "role": "assistant",
            "content": [{ "type": "text", "text": turn.answer }],
            "api": model.api,
            "provider": model.provider,
            "model": model.id,
            "usage": {
                "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
            },
            "stopReason": "stop",
            "timestamp": 0,
        })) {
            Ok(answer) => answer,
            Err(error) => return failed(error.to_string()),
        };
        answer.thinking_level = None;
        messages.push(Message::Assistant(answer));
    }
    messages.push(user_message(side_question_prompt(
        &request.question,
        request.previous_turns.is_empty(),
    )));
    let mut options = SimpleStreamOptions {
        reasoning: reasoning(agent.thinking_level),
        ..SimpleStreamOptions::default()
    };
    options.stream.request.signal = Some(signal.clone());
    let context = eukhe_types::pi_ai::Context {
        system_prompt: None,
        messages,
        tools: None,
    };
    let stream = hosted.deps().models.stream_simple(
        &model,
        context,
        ModelsSimpleStreamOptions::from(options),
    );
    let mut events = stream.events();
    let mut answer = String::new();
    while let Some(event) = events.next().await {
        let (AssistantMessageEvent::TextDelta { partial, .. }
        | AssistantMessageEvent::TextEnd { partial, .. }) = &event
        else {
            continue;
        };
        let text = assistant_text(partial);
        if text != answer {
            answer = text;
            on_update(&answer);
        }
    }
    let message = stream.result().await;
    let text = assistant_text(&message);
    let answer = if text.is_empty() { answer } else { text };
    match message.stop_reason {
        _ if signal.aborted() => SideQuestionOutcome::Aborted { answer },
        StopReason::Aborted => SideQuestionOutcome::Aborted { answer },
        StopReason::Error => SideQuestionOutcome::Failed {
            answer,
            error: message
                .error_message
                .unwrap_or_else(|| "Side question failed".to_string()),
        },
        _ if answer.is_empty() => SideQuestionOutcome::Failed {
            answer,
            error: "The side question ended without an answer".to_string(),
        },
        _ => SideQuestionOutcome::Complete { answer },
    }
}

/// Broadcast one `side_question_event` frame for the worker's session.
fn emit_side_question_frame(events: &Arc<EventPump>, active_session_id: &str, event: Value) {
    let outbound = DaemonOutbound::SideQuestionEvent {
        active_session_id: active_session_id.to_string(),
        event,
        rest: Map::default(),
    };
    let payload = serde_json::to_vec(&outbound).unwrap_or_default();
    events.send(OutboundFrame::side_question_event(payload));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable_test_support::{answer, ask, hosted, kinds, Fixture};
    use eukhe_pi_ai::providers::faux::{
        faux_assistant_message, FauxAssistantMessageOptions, FauxResponseStep,
    };
    use tokio::sync::broadcast::Receiver;

    /// A reply that parks until the request's abort lands, then (once
    /// `gate` opens, when given) answers; the faux stream then ends
    /// aborted. The returned notify fires once the request reached the
    /// model, so a test aborts a run that is in flight, never one still
    /// starting. The settle happens by synchronization, never by a timing
    /// budget.
    fn parking_reply(
        gate: Option<Arc<tokio::sync::Notify>>,
    ) -> (FauxResponseStep, Arc<tokio::sync::Notify>) {
        let started = Arc::new(tokio::sync::Notify::new());
        let reached = Arc::clone(&started);
        let step = FauxResponseStep::Factory(Arc::new(move |_context, options, _state, _model| {
            reached.notify_one();
            let signal = options.and_then(|options| options.stream.request.signal.clone());
            let gate = gate.clone();
            Box::pin(async move {
                if let Some(signal) = signal {
                    signal.cancelled().await;
                }
                if let Some(gate) = gate {
                    gate.notified().await;
                }
                Ok(faux_assistant_message(
                    "partial",
                    FauxAssistantMessageOptions::default(),
                ))
            })
        }));
        (step, started)
    }

    /// Start `id` for `client` on a parked reply and wait until it is in
    /// flight.
    async fn start_parked(
        harness: &Harness,
        id: &str,
        client: &str,
        gate: Option<Arc<tokio::sync::Notify>>,
    ) {
        let (reply, started) = parking_reply(gate);
        harness.fixture.faux.append_responses(vec![reply]);
        let response = harness.manager.start(&start_payload(id, client));
        assert!(response.success, "{response:?}");
        started.notified().await;
    }

    struct Harness {
        fixture: Fixture,
        slot: SessionSlot,
        pump: Arc<EventPump>,
        manager: SideQuestionManager,
    }

    impl Harness {
        async fn new() -> Self {
            let fixture = Fixture::new();
            let slot = SessionSlot::default();
            slot.replace(hosted(&fixture).await);
            let pump = Arc::new(EventPump::new());
            let manager =
                SideQuestionManager::new(slot.clone(), Arc::clone(&pump), "sess-1".to_string());
            Harness {
                fixture,
                slot,
                pump,
                manager,
            }
        }

        async fn close(self) {
            if let Some(session) = self.slot.take() {
                session.close(cx()).await.expect("close");
            }
        }
    }

    fn start_payload(id: &str, client: &str) -> Value {
        json!({ "sideQuestionId": id, "clientId": client, "question": "what?" })
    }

    fn drain(receiver: &mut Receiver<Arc<OutboundFrame>>) -> Vec<Value> {
        let mut events = Vec::new();
        while let Ok(frame) = receiver.try_recv() {
            assert_eq!(frame.outbound_type, "side_question_event");
            let payload: Value = serde_json::from_slice(&frame.payload).unwrap();
            events.push(payload["event"].clone());
        }
        events
    }

    fn statuses(events: &[Value]) -> Vec<String> {
        events
            .iter()
            .map(|event| event["status"].as_str().expect("status").to_string())
            .collect()
    }

    /// Wait for the terminal frame of `id` (the registry drained).
    async fn settled(manager: &SideQuestionManager) {
        let deadline = std::time::Instant::now() + Duration::from_secs(5);
        while !manager.runs.lock().unwrap().is_empty() {
            assert!(
                std::time::Instant::now() < deadline,
                "the run never settled out of the registry"
            );
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }

    /// A side question answers from the main conversation's context with
    /// running frames then the complete answer, and leaves the session's
    /// history untouched.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_side_question_answers_without_touching_the_session() {
        let harness = Harness::new().await;
        let main = harness.slot.get().unwrap().main().unwrap();
        ask(&harness.fixture, &main, "hello", "hi").await;
        let before = kinds(&main).await;
        let mut receiver = harness.pump.subscribe();
        harness
            .fixture
            .faux
            .append_responses(vec![answer("forty-two")]);

        let response = harness.manager.start(&start_payload("sq-1", "client-1"));
        assert!(response.success, "{response:?}");
        settled(&harness.manager).await;

        let events = drain(&mut receiver);
        let statuses = statuses(&events);
        assert_eq!(statuses.first().map(String::as_str), Some("running"));
        assert_eq!(statuses.last().map(String::as_str), Some("complete"));
        assert_eq!(
            events.last().unwrap(),
            &json!({ "id": "sq-1", "question": "what?", "answer": "forty-two", "status": "complete" })
        );
        assert_eq!(kinds(&main).await, before, "nothing entered the session");
        harness.close().await;
    }

    /// The handler guards answer the TS error strings.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn start_guards_answer_the_ts_errors() {
        let detached = SideQuestionManager::new(
            SessionSlot::default(),
            Arc::new(EventPump::new()),
            "s".into(),
        );
        let missing = detached.start(&json!({ "question": "q" }));
        assert_eq!(
            missing.error.as_deref(),
            Some("Side question id is required")
        );
        let empty = detached.start(&json!({ "sideQuestionId": "a" }));
        assert_eq!(empty.error.as_deref(), Some("Question cannot be empty"));

        let harness = Harness::new().await;
        start_parked(&harness, "sq-1", "client-1", None).await;
        let duplicate = harness.manager.start(&start_payload("sq-1", "client-2"));
        assert_eq!(
            duplicate.error.as_deref(),
            Some("Side question already exists: sq-1")
        );
        let same_client = harness.manager.start(&start_payload("sq-2", "client-1"));
        assert_eq!(
            same_client.error.as_deref(),
            Some("A side question is already running for this client and session")
        );
        let foreign = harness
            .manager
            .abort(&json!({ "sideQuestionId": "sq-1", "clientId": "client-2" }));
        assert_eq!(foreign.data, Some(json!({ "aborted": false })));
        let owner = harness
            .manager
            .abort(&json!({ "sideQuestionId": "sq-1", "clientId": "client-1" }));
        assert_eq!(owner.data, Some(json!({ "aborted": true })));
        settled(&harness.manager).await;
        harness.close().await;
    }

    /// The close paths (`shutdown`, `kill`) abort every live run and wait
    /// for the cancelled events to queue before the process exits.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn shutdown_settle_queues_the_cancelled_events() {
        let harness = Harness::new().await;
        let mut receiver = harness.pump.subscribe();
        start_parked(&harness, "sq-1", "client-1", None).await;

        harness
            .manager
            .abort_all_and_settle(Duration::from_secs(5))
            .await;

        assert_eq!(
            statuses(&drain(&mut receiver)),
            ["running", "cancelled"],
            "the initial running event and the terminal cancelled event both queued"
        );
        assert!(harness.manager.runs.lock().unwrap().is_empty());
        harness.close().await;
    }

    /// A close owns the registry's tail: once the aborts began, a racing
    /// start is rejected instead of being admitted into a worker about to
    /// exit.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn start_during_the_close_is_rejected() {
        let harness = Harness::new().await;
        start_parked(&harness, "sq-1", "client-1", None).await;
        harness
            .manager
            .abort_all_and_settle(Duration::from_secs(5))
            .await;

        let late = harness.manager.start(&start_payload("sq-2", "client-1"));
        assert_eq!(
            late.error.as_deref(),
            Some("Active session sess-1 is closing")
        );
        harness.close().await;
    }

    /// The detach abort keeps the registry entry until the run's terminal
    /// cancelled event queued.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn detach_abort_settles_the_entry_it_aborts() {
        let harness = Harness::new().await;
        let mut receiver = harness.pump.subscribe();
        start_parked(&harness, "sq-1", "client-1", None).await;

        harness.manager.abort_for_client("client-1");
        settled(&harness.manager).await;

        assert_eq!(statuses(&drain(&mut receiver)), ["running", "cancelled"]);
        harness.close().await;
    }

    /// A same-id restart that reacts to the cancelled event never reads a
    /// stale registry entry: the terminal path frees the id and queues the
    /// cancelled frame under one registry hold. The probe takes the hold,
    /// opens the reply gate under it, and no cancelled frame may queue
    /// while it is taken.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn same_id_restart_after_the_cancelled_event_is_admitted() {
        let harness = Harness::new().await;
        let gate = Arc::new(tokio::sync::Notify::new());
        let mut receiver = harness.pump.subscribe();
        start_parked(&harness, "sq-1", "client-1", Some(Arc::clone(&gate))).await;
        harness.manager.abort_for_client("client-1");

        {
            let runs = harness.manager.runs.lock().unwrap();
            assert!(
                runs.contains_key("sq-1"),
                "the aborted run is still registered"
            );
            gate.notify_one();
            let deadline = std::time::Instant::now() + Duration::from_millis(300);
            while std::time::Instant::now() < deadline {
                assert!(
                    !statuses(&drain(&mut receiver))
                        .iter()
                        .any(|status| status == "cancelled"),
                    "the cancelled frame queued while the registry hold was taken"
                );
                std::thread::sleep(Duration::from_millis(1));
            }
            drop(runs);
        }
        settled(&harness.manager).await;
        assert_eq!(statuses(&drain(&mut receiver)), ["cancelled"]);

        harness.fixture.faux.append_responses(vec![answer("again")]);
        let restart = harness.manager.start(&start_payload("sq-1", "client-1"));
        assert!(restart.success, "same-id restart after cancel: {restart:?}");
        settled(&harness.manager).await;
        harness.close().await;
    }
}
