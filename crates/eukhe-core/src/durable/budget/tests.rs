//! The budget gate over a faux provider and a ledger in a temp dir: what
//! is sent, with which cap, what the ledger holds while it runs and after,
//! what a failed request is charged, when a request is stopped, what the
//! agent is told, and which tool calls run.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use eukhe_ai::api::{FetchDeferredFn, StreamSimpleFn};
use eukhe_ai::models::{create_models, CreateModelsOptions, Models, ModelsSimpleStreamOptions};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_thinking, faux_tool_call,
    FauxAssistantMessageOptions, FauxModelDefinition, FauxProviderHandle, FauxResponseStep,
    RegisterFauxProviderOptions,
};
use eukhe_ai::types::{DeferredFetchOptions, SimpleStreamOptions};
use eukhe_ai::utils::assistant_message_frame::{
    reduce_assistant_message_frames, AssistantMessageFrameEncoder,
};
use eukhe_ai::utils::context_tokens::{context_tokens, model_tokenizer};
use eukhe_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_ai::utils::overflow::is_context_overflow;
use eukhe_ai::utils::retry::{is_retryable_assistant_error, BUDGET_REFUSAL_DIAGNOSTIC};
use eukhe_ai::utils::transcript::normalize_context;
use eukhe_budget::{actual_spend, mask, Ledger, Reserved, Use, REQUEST_MIN_MS};
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_types::budget::{
    BudgetAmounts, BudgetDimension, BudgetLimits, BudgetPhase, BudgetReport,
};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Context as PiContext,
    DeferredHandle, DoneReason, ErrorReason, Message, ModelCost, ModelCostTier, Partial,
    StopReason, Tool, ToolChoice, Usage, UserContent, UserMessage,
};
use futures::StreamExt as _;
use tempfile::TempDir;
use tokio::sync::watch;

use super::gate::{offers, CostFacts, FRAMING_TOKENS};
use super::notices::{self, Notice, NoticeKind};
use super::tools::ToolOutcome;
use super::{wrap_models_with_budget, BudgetGate, FIRST_TURN};
use crate::durable::settings::EukheSettings;

/// The ledger clock of the clocked fixtures: a fixed epoch ms, so a
/// deadline's granted time is exact.
const NOW_MS: u64 = 1_800_000_000_000;

fn fixed_clock() -> u64 {
    NOW_MS
}

/// The ledger clock of the moving fixtures: [`NOW_MS`] until a test moves
/// it. One test uses it.
static MOVING_MS: AtomicU64 = AtomicU64::new(NOW_MS);

fn moving_clock() -> u64 {
    MOVING_MS.load(Ordering::SeqCst)
}

/// What the provider received with one request.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Received {
    max_tokens: Option<u64>,
    tool_choice: Option<ToolChoice>,
    /// The text of the last message, when it is a user's text.
    last: Option<String>,
}

/// A session's gate over a temp agent dir, and a model collection whose
/// one faux provider sits behind it.
struct Fixture {
    dir: TempDir,
    gate: Arc<BudgetGate>,
    models: Models,
    faux: FauxProviderHandle,
    received: Arc<Mutex<Vec<Received>>>,
    notices: Arc<Mutex<Vec<Notice>>>,
}

/// How a fixture's provider answers.
enum Answer {
    /// The faux provider's scripted responses.
    Faux,
    /// This stream function instead of the faux provider's.
    Row(StreamSimpleFn),
    /// This stream function, and this fetch of deferred responses.
    Deferred(StreamSimpleFn, FetchDeferredFn),
}

/// Which clock the fixture's ledger reads.
#[derive(Clone, Copy)]
enum Clock {
    Real,
    Fixed,
    /// [`moving_clock`].
    Moving,
}

impl Fixture {
    fn new() -> Self {
        Self::build(Answer::Faux, Clock::Real)
    }

    fn build(answer: Answer, clock: Clock) -> Self {
        Self::with_provider(answer, clock, RegisterFauxProviderOptions::default())
    }

    /// A fixture whose faux model has these prices, its largest output
    /// 16384 tokens.
    fn priced(cost: ModelCost) -> Self {
        Self::with_provider(
            Answer::Faux,
            Clock::Real,
            RegisterFauxProviderOptions {
                models: Some(vec![FauxModelDefinition {
                    id: "priced".to_owned(),
                    cost: Some(cost),
                    context_window: Some(1_000_000),
                    max_tokens: Some(16_384),
                    ..FauxModelDefinition::default()
                }]),
                ..RegisterFauxProviderOptions::default()
            },
        )
    }

    fn with_provider(answer: Answer, clock: Clock, options: RegisterFauxProviderOptions) -> Self {
        let dir = TempDir::new().unwrap();
        let agent_dir = dir.path().join("agent");
        let cwd = dir.path().join("work");
        std::fs::create_dir_all(&agent_dir).unwrap();
        std::fs::create_dir_all(&cwd).unwrap();
        let settings = Arc::new(EukheSettings::new(cwd, &agent_dir));
        let ledger = Ledger::of(&agent_dir.join("budgets"), "session");
        let gate = match clock {
            Clock::Real => BudgetGate::open(&agent_dir, "session", None, settings),
            Clock::Fixed | Clock::Moving => Arc::new(BudgetGate {
                ledger: ledger.with_clock(match clock {
                    Clock::Fixed | Clock::Real => fixed_clock,
                    Clock::Moving => moving_clock,
                }),
                settings: Some(settings),
                reports: watch::Sender::new(None),
                keep: Mutex::default(),
                told: Mutex::default(),
                notices: OnceLock::new(),
                deferred: Mutex::default(),
                steps: Mutex::default(),
                turn: Mutex::new(FIRST_TURN),
            }),
        };
        let notices = Arc::new(Mutex::new(Vec::new()));
        let told = Arc::clone(&notices);
        gate.deliver_notices(Arc::new(move |notice| told.lock().unwrap().push(notice)));
        let faux = faux_provider(options);
        let models = create_models(CreateModelsOptions::default());
        let mut provider = faux.provider.clone();
        match answer {
            Answer::Faux => {}
            Answer::Row(row) => provider.stream_simple = row,
            Answer::Deferred(row, fetch) => {
                provider.stream_simple = row;
                provider.fetch_deferred = Some(fetch);
            }
        }
        models.set_provider(provider);
        wrap_models_with_budget(&models, &gate);
        Self {
            dir,
            gate,
            models,
            faux,
            received: Arc::default(),
            notices,
        }
    }

    fn agent_dir(&self) -> std::path::PathBuf {
        self.dir.path().join("agent")
    }

    /// Send `context` through the gated collection; the faux provider,
    /// when the request reaches it, records what it received and answers
    /// `done`.
    async fn request(&self, context: PiContext) -> AssistantMessage {
        let received = Arc::clone(&self.received);
        self.faux.set_responses(vec![FauxResponseStep::factory(
            move |context, options, _state, _model| {
                received.lock().unwrap().push(Received {
                    max_tokens: options.and_then(|options| options.stream.max_tokens),
                    tool_choice: options.and_then(|options| options.tool_choice.clone()),
                    last: context.messages().last().and_then(|last| match last {
                        Message::User(UserMessage {
                            content: UserContent::Text(text),
                            ..
                        }) => Some(text.clone()),
                        Message::User(_)
                        | Message::System(_)
                        | Message::Assistant(_)
                        | Message::ToolResult(_) => None,
                    }),
                });
                Ok(faux_assistant_message(
                    "done",
                    FauxAssistantMessageOptions::default(),
                ))
            },
        )]);
        self.send(context).await
    }

    /// Send `context` through the gated collection as it stands.
    async fn send(&self, context: PiContext) -> AssistantMessage {
        self.models
            .complete_simple(
                &self.faux.get_model(),
                context,
                ModelsSimpleStreamOptions::from(SimpleStreamOptions::default()),
            )
            .await
    }

    /// The input tokens a request of `context` reserves, counted here with
    /// the model's real tokenizer: every message is counted locally, so
    /// each carries the framing.
    fn input_tokens(&self, context: &PiContext) -> u64 {
        let normalized = normalize_context(context.clone());
        let tokenizer = model_tokenizer(&self.faux.get_model());
        context_tokens(&tokenizer, normalized.messages()).tokens
            + FRAMING_TOKENS * normalized.messages().len() as u64
    }

    fn received(&self) -> Vec<Received> {
        self.received.lock().unwrap().clone()
    }

    /// The kind and request id of every notice the gate gave.
    fn told(&self) -> Vec<(NoticeKind, String)> {
        self.notices
            .lock()
            .unwrap()
            .iter()
            .map(|notice| (notice.kind, notice.request_id.clone()))
            .collect()
    }
}

fn tokens(tokens: u64) -> BudgetLimits {
    BudgetLimits {
        tokens: Some(tokens),
        ..BudgetLimits::default()
    }
}

/// The report of the fixture session's own account.
fn report(limits: BudgetLimits) -> BudgetReport {
    BudgetReport {
        session_id: "session".to_owned(),
        agent_session_id: "session".to_owned(),
        limits,
        ..BudgetReport::default()
    }
}

/// A side request: no tools.
fn chat(text: &str) -> PiContext {
    PiContext {
        system_prompt: Some("You help.".to_owned()),
        messages: vec![Message::User(UserMessage {
            content: UserContent::Text(text.to_owned()),
            timestamp: 1,
        })],
        tools: None,
    }
}

/// An agent turn: the context declares a tool.
fn agent(text: &str) -> PiContext {
    PiContext {
        tools: Some(vec![Tool {
            name: "probe".to_owned(),
            description: "Probe.".to_owned(),
            parameters: serde_json::json!({ "type": "object", "properties": {} }).into(),
            constrained_sampling: None,
            priority: 0,
        }]),
        ..chat(text)
    }
}

/// A provider message with `usage`.
fn message(text: &str, usage: Usage) -> AssistantMessage {
    AssistantMessage {
        usage,
        ..faux_assistant_message(text, FauxAssistantMessageOptions::default())
    }
}

/// A row that answers each request with `events` (built per request).
fn scripted(
    events: impl Fn() -> Vec<AssistantMessageEvent> + Send + Sync + 'static,
) -> StreamSimpleFn {
    Arc::new(move |_model, _context, _options| {
        let stream = AssistantMessageEventStream::new();
        for event in events() {
            stream.push(event);
        }
        stream.end(None);
        stream
    })
}

/// The events of a stream that started, streamed `text`, and failed with
/// `reported` usage on its error.
fn started_then_failed(text: &str, reported: Usage) -> Vec<AssistantMessageEvent> {
    let partial = Partial::new(message(text, Usage::default()));
    vec![
        AssistantMessageEvent::Start {
            partial: partial.clone(),
        },
        AssistantMessageEvent::TextDelta {
            content_index: 0,
            delta: text.to_owned(),
            partial,
        },
        AssistantMessageEvent::Error {
            reason: ErrorReason::Error,
            error: AssistantMessage {
                stop_reason: StopReason::Error,
                error_message: Some("connection reset".to_owned()),
                ..message(text, reported)
            },
        },
    ]
}

// Token budgets below: a work request under the output cap `c` fits when
// `2 * input + c + 7168` tokens are free (its worst case `input + c`, and
// the final-answer reserve after the smallest cap: `input + 1024 + 4096 +
// 2048`). The inputs of these contexts are below 300 tokens; the faux
// model's largest output is 16384 tokens, so the caps offered are 16384,
// 8192, 4096, 2048, 1024.

/// B1, B6: a side request whose worst case does not fit is not sent,
/// nothing is spent, and it changes nothing else: the agent still works.
#[tokio::test]
async fn a_request_that_does_not_fit_is_not_sent_and_spends_nothing() {
    let fixture = Fixture::new();
    fixture.gate.set(tokens(1_000)).unwrap();
    let reply = fixture.request(chat("summarize")).await;
    assert_eq!(
        (
            reply.error_message,
            fixture.faux.state().call_count,
            fixture.gate.report()
        ),
        (
            Some(
                "Budget exhausted (tokens): the request was not sent. Add budget to continue."
                    .to_owned()
            ),
            0,
            Some(BudgetReport {
                free: BudgetAmounts {
                    tokens: 1_000,
                    ..BudgetAmounts::default()
                },
                ..report(tokens(1_000))
            })
        )
    );
    assert_eq!(fixture.gate.phase(), Some(BudgetPhase::Working));
}

/// B6: a side request (a title, a classifier, a compaction: no tools) is
/// no turn of the agent. It holds and spends no model request, so the
/// agent's work and its final answer keep theirs: under a budget of two
/// requests, a title before the first turn leaves that turn its work
/// request, and the next turn is the final answer.
#[tokio::test]
async fn a_side_request_is_no_turn_of_the_agent() {
    let fixture = Fixture::new();
    let limits = BudgetLimits {
        tokens: Some(100_000),
        requests: Some(2),
        ..BudgetLimits::default()
    };
    fixture.gate.set(limits).unwrap();
    let title = fixture.request(chat("name this session")).await;
    let after_title = fixture.gate.report().map(|report| report.spent.requests);
    let work = fixture.request(agent("build it")).await;
    let last = fixture.request(agent("build more")).await;
    assert_eq!(
        (
            [title.error_message, work.error_message, last.error_message],
            after_title,
            fixture
                .received()
                .into_iter()
                .map(|received| received.tool_choice)
                .collect::<Vec<_>>(),
            fixture.gate.report().map(|report| report.spent.requests),
            fixture.gate.phase(),
            fixture.gate.audit().unwrap().exact()
        ),
        (
            [None, None, None],
            Some(0),
            vec![None, None, Some(ToolChoice::None)],
            Some(2),
            Some(BudgetPhase::WrapUp),
            true
        )
    );
}

/// B2: a request that fits only with a reduced cap is sent with that cap.
#[tokio::test]
async fn a_request_that_fits_with_a_reduced_cap_is_sent_with_that_cap() {
    let fixture = Fixture::new();
    // An agent turn keeps its own final answer free: 16384 needs more than
    // 23552 tokens free, 8192 at most 15960.
    fixture.gate.set(tokens(20_000)).unwrap();
    fixture.request(agent("summarize")).await;
    assert_eq!(
        fixture.received(),
        vec![Received {
            max_tokens: Some(8_192),
            tool_choice: None,
            last: Some("summarize".to_owned()),
        }]
    );
}

/// B1, real tokenizer: while a request is in flight the ledger holds its
/// input counted with the model's real tokenizer, plus the framing of each
/// locally counted message, plus its output cap; nothing more.
#[tokio::test]
async fn a_request_holds_its_real_token_input_its_framing_and_its_cap() {
    let (release, released) = tokio::sync::watch::channel(false);
    let row: StreamSimpleFn = Arc::new(move |_model, _context, _options| {
        let stream = AssistantMessageEventStream::new();
        let sink = stream.clone();
        let mut released = released.clone();
        tokio::spawn(async move {
            let partial = Partial::new(message("", Usage::default()));
            sink.push(AssistantMessageEvent::Start { partial });
            drop(released.wait_for(|released| *released).await);
            sink.push(AssistantMessageEvent::Done {
                reason: DoneReason::Stop,
                message: message("done", Usage::default()),
            });
            sink.end(None);
        });
        stream
    });
    let fixture = Fixture::build(Answer::Row(row), Clock::Real);
    let limits = tokens(1_000_000);
    fixture.gate.set(limits).unwrap();
    let context = chat("summarize the design of this repository in two lines");
    let held = BudgetAmounts {
        tokens: fixture.input_tokens(&context) + 16_384,
        ..BudgetAmounts::default()
    };
    let mut watched = fixture.gate.watch();
    let sent = tokio::spawn({
        let models = fixture.models.clone();
        let model = fixture.faux.get_model();
        async move {
            models
                .complete_simple(
                    &model,
                    context,
                    ModelsSimpleStreamOptions::from(SimpleStreamOptions::default()),
                )
                .await
        }
    });
    let in_flight = watched
        .wait_for(|report| report.as_ref().is_some_and(|report| report.held.tokens > 0))
        .await
        .unwrap()
        .clone();
    release.send(true).unwrap();
    sent.await.unwrap();
    assert_eq!(
        in_flight,
        Some(BudgetReport {
            free: BudgetAmounts {
                tokens: 1_000_000 - held.tokens,
                ..BudgetAmounts::default()
            },
            held,
            ..report(limits)
        })
    );
}

/// B3: after a response the ledger's spend is the response's usage, and
/// nothing stays held.
#[tokio::test]
async fn a_response_settles_at_its_usage_and_frees_the_rest() {
    let fixture = Fixture::new();
    let limits = tokens(100_000);
    fixture.gate.set(limits).unwrap();
    let reply = fixture.request(chat("summarize")).await;
    let spent = mask(actual_spend(&reply.usage), &limits);
    assert_ne!(spent, BudgetAmounts::default());
    let settled = BudgetReport {
        free: BudgetAmounts {
            tokens: 100_000 - spent.tokens,
            ..BudgetAmounts::default()
        },
        spent,
        ..report(limits)
    };
    let watched = fixture.gate.watch().borrow().clone();
    assert_eq!(
        (
            fixture.gate.report(),
            watched,
            fixture.gate.audit().unwrap().exact()
        ),
        (Some(settled.clone()), Some(settled), true)
    );
}

/// Failure charging: a request whose provider never started answering
/// (no `Start`: an error status, a refused connection) is charged nothing
/// but its one request; a side request, which holds none, nothing at all.
#[tokio::test]
async fn a_request_that_never_started_is_charged_only_its_request() {
    let fixture = Fixture::build(
        Answer::Row(scripted(|| {
            vec![AssistantMessageEvent::Error {
                reason: ErrorReason::Error,
                error: AssistantMessage {
                    stop_reason: StopReason::Error,
                    error_message: Some("503 Service Unavailable".to_owned()),
                    ..message(
                        "",
                        Usage {
                            input: 900,
                            ..Usage::default()
                        },
                    )
                },
            }]
        })),
        Clock::Real,
    );
    let limits = BudgetLimits {
        tokens: Some(100_000),
        requests: Some(10),
        ..BudgetLimits::default()
    };
    fixture.gate.set(limits).unwrap();
    fixture.send(chat("summarize")).await;
    fixture.send(agent("summarize")).await;
    assert_eq!(
        fixture.gate.report(),
        Some(BudgetReport {
            free: BudgetAmounts {
                tokens: 100_000,
                requests: 9,
                ..BudgetAmounts::default()
            },
            spent: BudgetAmounts {
                requests: 1,
                ..BudgetAmounts::default()
            },
            ..report(limits)
        })
    );
}

/// Failure charging: a stream that started and then failed is charged
/// what the provider reported on its error.
#[tokio::test]
async fn a_started_request_that_failed_is_charged_what_was_reported() {
    let reported = Usage {
        input: 40,
        output: 500,
        ..Usage::default()
    };
    let fixture = Fixture::build(
        Answer::Row(scripted(move || {
            started_then_failed("half an answer", reported)
        })),
        Clock::Real,
    );
    let limits = tokens(100_000);
    fixture.gate.set(limits).unwrap();
    fixture.send(chat("summarize")).await;
    assert_eq!(
        fixture.gate.report(),
        Some(BudgetReport {
            free: BudgetAmounts {
                tokens: 100_000 - 540,
                ..BudgetAmounts::default()
            },
            spent: BudgetAmounts {
                tokens: 540,
                ..BudgetAmounts::default()
            },
            ..report(limits)
        })
    );
}

/// Failure charging: a stream that started and failed without the
/// provider reporting anything is charged its whole reservation.
#[tokio::test]
async fn a_started_request_that_reported_nothing_is_charged_in_full() {
    let fixture = Fixture::build(
        Answer::Row(scripted(|| {
            started_then_failed("half an answer", Usage::default())
        })),
        Clock::Real,
    );
    let limits = tokens(100_000);
    fixture.gate.set(limits).unwrap();
    let context = chat("summarize");
    let full = fixture.input_tokens(&context) + 16_384;
    fixture.send(context).await;
    assert_eq!(
        fixture.gate.report(),
        Some(BudgetReport {
            free: BudgetAmounts {
                tokens: 100_000 - full,
                ..BudgetAmounts::default()
            },
            spent: BudgetAmounts {
                tokens: full,
                ..BudgetAmounts::default()
            },
            ..report(limits)
        })
    );
}

/// Time: a budget with a deadline stops a request at its granted time (the
/// time left before the deadline): the provider sees the abort exactly
/// then, and the request ends with the budget's typed error.
#[tokio::test(start_paused = true)]
async fn a_request_is_stopped_at_its_granted_time() {
    let aborted_at = Arc::new(Mutex::new(None));
    let seen = Arc::clone(&aborted_at);
    let row: StreamSimpleFn = Arc::new(move |_model, _context, options: SimpleStreamOptions| {
        let stream = AssistantMessageEventStream::new();
        let sink = stream.clone();
        let seen = Arc::clone(&seen);
        let started = tokio::time::Instant::now();
        let signal = options
            .stream
            .request
            .signal
            .expect("the gate's stop signal");
        tokio::spawn(async move {
            let partial = Partial::new(message("", Usage::default()));
            sink.push(AssistantMessageEvent::Start { partial });
            signal.cancelled().await;
            *seen.lock().unwrap() = Some(started.elapsed());
            sink.push(AssistantMessageEvent::Error {
                reason: ErrorReason::Aborted,
                error: AssistantMessage {
                    stop_reason: StopReason::Aborted,
                    ..message("", Usage::default())
                },
            });
            sink.end(None);
        });
        stream
    });
    let fixture = Fixture::build(Answer::Row(row), Clock::Fixed);
    fixture
        .gate
        .set(BudgetLimits {
            time_ms: Some(60_000),
            ..BudgetLimits::default()
        })
        .unwrap();
    let reply = fixture.send(chat("summarize")).await;
    assert_eq!(
        (
            reply.error_message,
            reply
                .diagnostics
                .unwrap_or_default()
                .into_iter()
                .map(|diagnostic| diagnostic.kind)
                .collect::<Vec<_>>(),
            *aborted_at.lock().unwrap(),
        ),
        (
            Some(notices::REQUEST_STOPPED.to_owned()),
            vec![BUDGET_REFUSAL_DIAGNOSTIC.to_owned()],
            Some(std::time::Duration::from_millis(60_000)),
        )
    );
}

/// Time: an agent's work turn leaves its final answer's time free (180 s
/// budget, 45 s kept: B14), so it is stopped at 135 s; stopped before it
/// streamed content, it goes on as the final answer on the same stream,
/// with no tools and the wrap-up notice. Before, it ended with the budget's
/// error and the run had no answer.
#[tokio::test(start_paused = true)]
async fn a_work_turn_stopped_at_its_granted_time_gives_the_final_answer() {
    let calls = Arc::new(AtomicUsize::new(0));
    let aborted_at = Arc::new(Mutex::new(None));
    let received = Arc::new(Mutex::new(Vec::new()));
    let row: StreamSimpleFn = {
        let aborted_at = Arc::clone(&aborted_at);
        let received = Arc::clone(&received);
        Arc::new(move |_model, context, options: SimpleStreamOptions| {
            received.lock().unwrap().push(Received {
                max_tokens: options.stream.max_tokens,
                tool_choice: options.tool_choice.clone(),
                last: context.messages().last().and_then(|last| match last {
                    Message::User(UserMessage {
                        content: UserContent::Text(text),
                        ..
                    }) => Some(text.clone()),
                    Message::User(_)
                    | Message::System(_)
                    | Message::Assistant(_)
                    | Message::ToolResult(_) => None,
                }),
            });
            let stream = AssistantMessageEventStream::new();
            let sink = stream.clone();
            if calls.fetch_add(1, Ordering::SeqCst) == 0 {
                // The work turn: the provider never answers until stopped.
                let aborted_at = Arc::clone(&aborted_at);
                let started = tokio::time::Instant::now();
                let signal = options
                    .stream
                    .request
                    .signal
                    .expect("the gate's stop signal");
                tokio::spawn(async move {
                    let partial = Partial::new(message("", Usage::default()));
                    sink.push(AssistantMessageEvent::Start { partial });
                    signal.cancelled().await;
                    *aborted_at.lock().unwrap() = Some(started.elapsed());
                    sink.push(AssistantMessageEvent::Error {
                        reason: ErrorReason::Aborted,
                        error: AssistantMessage {
                            stop_reason: StopReason::Aborted,
                            ..message("", Usage::default())
                        },
                    });
                    sink.end(None);
                });
            } else {
                let answer = message("wrapped up", Usage::default());
                sink.push(AssistantMessageEvent::Start {
                    partial: Partial::new(answer.clone()),
                });
                sink.push(AssistantMessageEvent::Done {
                    reason: DoneReason::Stop,
                    message: answer,
                });
                sink.end(None);
            }
            stream
        })
    };
    let fixture = Fixture::build(Answer::Row(row), Clock::Fixed);
    fixture
        .gate
        .set(BudgetLimits {
            time_ms: Some(180_000),
            ..BudgetLimits::default()
        })
        .unwrap();
    let reply = fixture.send(agent("build it")).await;
    // The ledger's clock stands still: the notice shows the whole budget.
    let notice = "[budget] The time budget of this task is used up for work: 3m 0s left, too little for another step beside the final answer. Tools are no longer available. Give your final answer now: what is done, what is not, and how to continue. At most 2048 output tokens.";
    let received = received.lock().unwrap().clone();
    assert_eq!(
        (
            reply.error_message,
            reply.content,
            *aborted_at.lock().unwrap(),
            received.len(),
            received.last().cloned(),
        ),
        (
            None,
            message("wrapped up", Usage::default()).content,
            Some(std::time::Duration::from_secs(135)),
            2,
            Some(Received {
                max_tokens: Some(2_048),
                tool_choice: Some(ToolChoice::None),
                last: Some(notice.to_owned()),
            }),
        )
    );
}

/// What a budget of `budget_ms` keeps for the final answer at the agent's
/// first work request, which answers after `first_ms`, and at its next,
/// which never answers, and when that one is stopped: the ledger's clock
/// stands still, so at the budget less what it keeps.
async fn kept_for_the_final_answer(
    budget_ms: u64,
    first_ms: u64,
) -> (u64, u64, Option<std::time::Duration>) {
    let calls = Arc::new(AtomicUsize::new(0));
    let aborted_at = Arc::new(Mutex::new(None));
    let row: StreamSimpleFn = {
        let aborted_at = Arc::clone(&aborted_at);
        Arc::new(move |_model, _context, options: SimpleStreamOptions| {
            let stream = AssistantMessageEventStream::new();
            let sink = stream.clone();
            let answer = message("done", Usage::default());
            let call = calls.fetch_add(1, Ordering::SeqCst);
            let aborted_at = Arc::clone(&aborted_at);
            let signal = options.stream.request.signal;
            tokio::spawn(async move {
                sink.push(AssistantMessageEvent::Start {
                    partial: Partial::new(answer.clone()),
                });
                match call {
                    0 => tokio::time::sleep(std::time::Duration::from_millis(first_ms)).await,
                    1 => {
                        // The second work request answers only when stopped.
                        let started = tokio::time::Instant::now();
                        signal.expect("the gate's stop signal").cancelled().await;
                        *aborted_at.lock().unwrap() = Some(started.elapsed());
                        sink.push(AssistantMessageEvent::Error {
                            reason: ErrorReason::Aborted,
                            error: AssistantMessage {
                                stop_reason: StopReason::Aborted,
                                ..answer
                            },
                        });
                        sink.end(None);
                        return;
                    }
                    // Its final answer.
                    2.. => {}
                }
                sink.push(AssistantMessageEvent::Done {
                    reason: DoneReason::Stop,
                    message: answer,
                });
                sink.end(None);
            });
            stream
        })
    };
    let fixture = Fixture::build(Answer::Row(row), Clock::Fixed);
    fixture
        .gate
        .set(BudgetLimits {
            time_ms: Some(budget_ms),
            ..BudgetLimits::default()
        })
        .unwrap();
    fixture.send(agent("look around")).await;
    let first = fixture.gate.keep().time_ms;
    fixture.send(agent("build it")).await;
    let next = fixture.gate.keep().time_ms;
    let stopped = *aborted_at.lock().unwrap();
    (first, next, stopped)
}

/// B14: the final answer's time reserve is proportionate. A 3-minute
/// budget keeps a quarter of it (45 s) at first and, once a request took
/// 10 s, twice that but at least 20 s, so the next work request is
/// stopped at 160 s; a 10-minute budget keeps 120 s at most, and after a
/// 70 s request still 120 s. (A 10-minute budget's stalled request meets
/// the stream's idle deadline first: only its reserves are compared.)
/// Before, every budget kept 120 s: a 3-minute budget wrapped up after a
/// minute of work.
#[tokio::test(start_paused = true)]
async fn the_final_answers_time_follows_the_budget_and_the_longest_request() {
    let reserves = |(first, next, _): (u64, u64, Option<std::time::Duration>)| (first, next);
    assert_eq!(
        (
            kept_for_the_final_answer(180_000, 10_000).await,
            reserves(kept_for_the_final_answer(600_000, 10_000).await),
            reserves(kept_for_the_final_answer(600_000, 70_000).await),
        ),
        (
            (45_000, 20_000, Some(std::time::Duration::from_secs(160))),
            (120_000, 20_000),
            (120_000, 120_000),
        )
    );
}

/// The answer, the budget's report after it and the final answer's
/// notice when an agent's work turn of a 3-minute budget is stopped at its
/// granted time (135 s: 45 s kept), on a ledger clock the stop moves:
/// `streamed`, after it streamed text; else before any content.
async fn stopped_at_the_deadline(
    streamed: bool,
) -> (
    Vec<AssistantContentBlock>,
    Option<BudgetReport>,
    Option<String>,
) {
    MOVING_MS.store(NOW_MS, Ordering::SeqCst);
    let calls = Arc::new(AtomicUsize::new(0));
    let notice = Arc::new(Mutex::new(None));
    let row: StreamSimpleFn = {
        let notice = Arc::clone(&notice);
        Arc::new(move |_model, context, options: SimpleStreamOptions| {
            let stream = AssistantMessageEventStream::new();
            let sink = stream.clone();
            let mut live = AssistantMessage {
                content: Vec::new(),
                ..message("", Usage::default())
            };
            if calls.fetch_add(1, Ordering::SeqCst) == 0 {
                let signal = options
                    .stream
                    .request
                    .signal
                    .expect("the gate's stop signal");
                tokio::spawn(async move {
                    let started = tokio::time::Instant::now();
                    sink.push_partial(&live, |partial| AssistantMessageEvent::Start { partial });
                    if streamed {
                        live.content.push(faux_text("Running"));
                        sink.push_partial(&live, |partial| AssistantMessageEvent::TextStart {
                            content_index: 0,
                            partial,
                        });
                    }
                    signal.cancelled().await;
                    // The ledger's clock moves with the stop.
                    let elapsed = u64::try_from(started.elapsed().as_millis()).unwrap();
                    MOVING_MS.fetch_add(elapsed, Ordering::SeqCst);
                    sink.push(AssistantMessageEvent::Error {
                        reason: ErrorReason::Aborted,
                        error: AssistantMessage {
                            stop_reason: StopReason::Aborted,
                            ..live
                        },
                    });
                    sink.end(None);
                });
            } else {
                *notice.lock().unwrap() = context.messages().last().and_then(|last| match last {
                    Message::User(UserMessage {
                        content: UserContent::Text(text),
                        ..
                    }) => Some(text.clone()),
                    Message::User(_)
                    | Message::System(_)
                    | Message::Assistant(_)
                    | Message::ToolResult(_) => None,
                });
                let answer = message("wrapped up", Usage::default());
                sink.push(AssistantMessageEvent::Start {
                    partial: Partial::new(answer.clone()),
                });
                sink.push(AssistantMessageEvent::Done {
                    reason: DoneReason::Stop,
                    message: answer,
                });
                sink.end(None);
            }
            stream
        })
    };
    let fixture = Fixture::build(Answer::Row(row), Clock::Moving);
    fixture
        .gate
        .set(BudgetLimits {
            time_ms: Some(180_000),
            ..BudgetLimits::default()
        })
        .unwrap();
    let reply = fixture.send(agent("build it")).await;
    let notice = notice.lock().unwrap().clone();
    (reply.content, fixture.gate.report(), notice)
}

/// B6, B10: a work turn stopped at the granted time the deadline cut has
/// used up the time for work: before its final answer the agent is in
/// `WrapUp`, short of time, as when work is refused for time, whether the
/// turn streamed or not; the final answer is told so. Before, the agent
/// stayed Working and the run did not end budget-limited.
#[tokio::test(start_paused = true)]
async fn a_work_turn_stopped_at_the_deadline_leaves_the_agent_wrapping_up() {
    let limits = BudgetLimits {
        time_ms: Some(180_000),
        ..BudgetLimits::default()
    };
    let wrapping_up = BudgetReport {
        free: BudgetAmounts {
            time_ms: 45_000,
            ..BudgetAmounts::default()
        },
        phase: BudgetPhase::WrapUp,
        short: Some(BudgetDimension::Time),
        deadline_ms: Some(NOW_MS + 180_000),
        ..report(limits)
    };
    let notice = "[budget] The time budget of this task is used up for work: 45s left, too little for another step beside the final answer. Tools are no longer available. Give your final answer now: what is done, what is not, and how to continue. At most 2048 output tokens.";
    assert_eq!(
        (
            stopped_at_the_deadline(false).await,
            stopped_at_the_deadline(true).await,
        ),
        (
            (
                vec![faux_text("wrapped up")],
                Some(wrapping_up.clone()),
                Some(notice.to_owned()),
            ),
            (
                vec![faux_text("Running"), faux_text("wrapped up")],
                Some(wrapping_up),
                Some(notice.to_owned()),
            ),
        )
    );
}

/// The block an event of a stream is about.
fn block_of(event: &AssistantMessageEvent) -> Option<usize> {
    match event {
        AssistantMessageEvent::TextStart { content_index, .. }
        | AssistantMessageEvent::TextDelta { content_index, .. }
        | AssistantMessageEvent::TextEnd { content_index, .. }
        | AssistantMessageEvent::ThinkingStart { content_index, .. }
        | AssistantMessageEvent::ThinkingDelta { content_index, .. }
        | AssistantMessageEvent::ThinkingEnd { content_index, .. }
        | AssistantMessageEvent::ToolCallStart { content_index, .. }
        | AssistantMessageEvent::ToolCallDelta { content_index, .. }
        | AssistantMessageEvent::ToolCallEnd { content_index, .. } => Some(*content_index),
        AssistantMessageEvent::Start { .. }
        | AssistantMessageEvent::PromptProgress { .. }
        | AssistantMessageEvent::Done { .. }
        | AssistantMessageEvent::Error { .. } => None,
    }
}

/// Time: a work turn stopped at its granted time after it streamed content
/// (thinking, a whole tool call, open text) gives the final answer in the
/// same message: what streamed stays and its open text is closed, the
/// final answer's blocks follow it, and the agent's message, which its
/// tools run from, holds no tool call of the cut turn. The final answer is
/// sent with the turn's context, no tools and the wrap-up notice. Before,
/// the turn ended with the budget's error and the run had no answer.
#[tokio::test(start_paused = true)]
async fn a_work_turn_stopped_after_it_streamed_gives_the_final_answer_after_it() {
    let calls = Arc::new(AtomicUsize::new(0));
    let received = Arc::new(Mutex::new(Vec::new()));
    let call = faux_tool_call("probe", serde_json::Map::new(), Some("call-1".to_owned()));
    let row: StreamSimpleFn = {
        let received = Arc::clone(&received);
        let call = call.clone();
        Arc::new(move |_model, context, options: SimpleStreamOptions| {
            received.lock().unwrap().push(Received {
                max_tokens: options.stream.max_tokens,
                tool_choice: options.tool_choice.clone(),
                last: context.messages().last().and_then(|last| match last {
                    Message::User(UserMessage {
                        content: UserContent::Text(text),
                        ..
                    }) => Some(text.clone()),
                    Message::User(_)
                    | Message::System(_)
                    | Message::Assistant(_)
                    | Message::ToolResult(_) => None,
                }),
            });
            let stream = AssistantMessageEventStream::new();
            let sink = stream.clone();
            let mut live = AssistantMessage {
                content: Vec::new(),
                ..message("", Usage::default())
            };
            if calls.fetch_add(1, Ordering::SeqCst) == 0 {
                // The work turn: it streams, then waits until stopped.
                let signal = options
                    .stream
                    .request
                    .signal
                    .expect("the gate's stop signal");
                let AssistantContentBlock::ToolCall(tool_call) = call.clone() else {
                    panic!("a tool call");
                };
                let call = call.clone();
                tokio::spawn(async move {
                    sink.push_partial(&live, |partial| AssistantMessageEvent::Start { partial });
                    live.content.push(faux_thinking(""));
                    sink.push_partial(&live, |partial| AssistantMessageEvent::ThinkingStart {
                        content_index: 0,
                        partial,
                    });
                    live.content[0] = faux_thinking("Plan the build.");
                    sink.push_partial(&live, |partial| AssistantMessageEvent::ThinkingDelta {
                        content_index: 0,
                        delta: "Plan the build.".to_owned(),
                        partial,
                    });
                    sink.push_partial(&live, |partial| AssistantMessageEvent::ThinkingEnd {
                        content_index: 0,
                        content: "Plan the build.".to_owned(),
                        partial,
                    });
                    live.content.push(call);
                    sink.push_partial(&live, |partial| AssistantMessageEvent::ToolCallStart {
                        content_index: 1,
                        partial,
                    });
                    sink.push_partial(&live, |partial| AssistantMessageEvent::ToolCallEnd {
                        content_index: 1,
                        tool_call,
                        partial,
                    });
                    live.content.push(faux_text(""));
                    sink.push_partial(&live, |partial| AssistantMessageEvent::TextStart {
                        content_index: 2,
                        partial,
                    });
                    live.content[2] = faux_text("Running the probe");
                    sink.push_partial(&live, |partial| AssistantMessageEvent::TextDelta {
                        content_index: 2,
                        delta: "Running the probe".to_owned(),
                        partial,
                    });
                    signal.cancelled().await;
                    sink.push(AssistantMessageEvent::Error {
                        reason: ErrorReason::Aborted,
                        error: AssistantMessage {
                            stop_reason: StopReason::Aborted,
                            ..live
                        },
                    });
                    sink.end(None);
                });
            } else {
                sink.push_partial(&live, |partial| AssistantMessageEvent::Start { partial });
                live.content.push(faux_text(""));
                sink.push_partial(&live, |partial| AssistantMessageEvent::TextStart {
                    content_index: 0,
                    partial,
                });
                live.content[0] = faux_text("wrapped up");
                sink.push_partial(&live, |partial| AssistantMessageEvent::TextDelta {
                    content_index: 0,
                    delta: "wrapped up".to_owned(),
                    partial,
                });
                sink.push_partial(&live, |partial| AssistantMessageEvent::TextEnd {
                    content_index: 0,
                    content: "wrapped up".to_owned(),
                    partial,
                });
                sink.push(AssistantMessageEvent::Done {
                    reason: DoneReason::Stop,
                    message: live,
                });
                sink.end(None);
            }
            stream
        })
    };
    let fixture = Fixture::build(Answer::Row(row), Clock::Fixed);
    fixture
        .gate
        .set(BudgetLimits {
            time_ms: Some(180_000),
            ..BudgetLimits::default()
        })
        .unwrap();
    let events: Vec<AssistantMessageEvent> = fixture
        .models
        .stream_simple(
            &fixture.faux.get_model(),
            agent("build it"),
            ModelsSimpleStreamOptions::from(SimpleStreamOptions::default()),
        )
        .events()
        .collect()
        .await;
    // The consumer's frames replay into one message: one start, every
    // block where its events say.
    let mut encoder = AssistantMessageFrameEncoder::new();
    let frames: Vec<_> = events
        .iter()
        .filter_map(|event| encoder.encode(event).unwrap())
        .collect();
    let shown = reduce_assistant_message_frames(&frames)
        .unwrap()
        .map(|message| message.content);
    let answer = match events.last() {
        Some(AssistantMessageEvent::Done { message, .. }) => Some(message.content.clone()),
        Some(_) | None => None,
    };
    let notice = "[budget] The time budget of this task is used up for work: 3m 0s left, too little for another step beside the final answer. Tools are no longer available. Give your final answer now: what is done, what is not, and how to continue. At most 2048 output tokens.";
    let received = received.lock().unwrap().clone();
    assert_eq!(
        (
            events
                .iter()
                .map(|event| (event.type_name(), block_of(event)))
                .collect::<Vec<_>>(),
            shown,
            answer,
            received.len(),
            received.last().cloned(),
        ),
        (
            vec![
                ("start", None),
                ("thinking_start", Some(0)),
                ("thinking_delta", Some(0)),
                ("thinking_end", Some(0)),
                ("toolcall_start", Some(1)),
                ("toolcall_end", Some(1)),
                ("text_start", Some(2)),
                ("text_delta", Some(2)),
                // Closed at the stop.
                ("text_end", Some(2)),
                // The final answer, after what streamed.
                ("text_start", Some(3)),
                ("text_delta", Some(3)),
                ("text_end", Some(3)),
                ("done", None),
            ],
            Some(vec![
                faux_thinking("Plan the build."),
                call,
                faux_text("Running the probe"),
                faux_text("wrapped up"),
            ]),
            // No tool call: none of the cut turn runs.
            Some(vec![
                faux_thinking("Plan the build."),
                faux_text("Running the probe"),
                faux_text("wrapped up"),
            ]),
            2,
            Some(Received {
                max_tokens: Some(2_048),
                tool_choice: Some(ToolChoice::None),
                last: Some(notice.to_owned()),
            }),
        )
    );
}

/// A refused request carries the typed budget refusal: no retry policy
/// treats it as transient and no overflow recovery compacts and resends
/// it, whatever its text.
#[tokio::test]
async fn a_refused_request_is_typed_and_never_retried() {
    let fixture = Fixture::new();
    fixture.gate.set(tokens(10)).unwrap();
    let refused = fixture.request(chat("summarize")).await;
    assert_eq!(
        (
            refused
                .diagnostics
                .clone()
                .unwrap_or_default()
                .into_iter()
                .map(|diagnostic| diagnostic.kind)
                .collect::<Vec<_>>(),
            is_retryable_assistant_error(&refused),
            is_context_overflow(&refused, None),
            fixture.faux.state().call_count,
        ),
        (vec![BUDGET_REFUSAL_DIAGNOSTIC.to_owned()], false, false, 0)
    );
}

/// B4: a child drawing from its parent's account cannot take the reserve
/// its parent keeps for its own final answer: a request that fits what is
/// free, but not what is free past that reserve, is refused.
#[tokio::test]
async fn a_shared_child_cannot_take_its_parents_final_answer_reserve() {
    let fixture = Fixture::new();
    fixture.gate.set(tokens(6_000)).unwrap();
    // The parent's last turn kept 5000 tokens for its final answer.
    let parent = fixture.gate.ledger();
    let parent_keep = BudgetAmounts {
        tokens: 5_000,
        ..BudgetAmounts::default()
    };
    let Reserved::Granted { reservation, .. } = parent
        .reserve(
            "session",
            Use::Work,
            "model:turn",
            parent_keep,
            BudgetAmounts::default(),
            &[BudgetAmounts {
                tokens: 1,
                ..BudgetAmounts::default()
            }],
            REQUEST_MIN_MS,
        )
        .unwrap()
    else {
        panic!("the parent's turn fits");
    };
    parent
        .settle(reservation.id, BudgetAmounts::default())
        .unwrap();
    let agent_dir = fixture.agent_dir();
    let child = BudgetGate::open(
        &agent_dir,
        "child",
        Some("session"),
        Arc::new(EukheSettings::new(
            fixture.dir.path().join("work"),
            &agent_dir,
        )),
    );
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(fixture.faux.provider.clone());
    wrap_models_with_budget(&models, &child);
    let context = chat("summarize");
    // The smallest offer of the child's request: its input and the floor
    // cap.
    let smallest = fixture.input_tokens(&context) + 1_024;
    let reply = models
        .complete_simple(
            &fixture.faux.get_model(),
            context,
            ModelsSimpleStreamOptions::from(SimpleStreamOptions::default()),
        )
        .await;
    assert_eq!(
        (
            reply.error_message,
            smallest <= 6_000,
            fixture.faux.state().call_count,
        ),
        (
            Some(
                "Budget exhausted (tokens): the request was not sent. Add budget to continue."
                    .to_owned()
            ),
            true,
            0,
        )
    );
}

/// A deferred response keeps its reservation open until its fetch: the
/// fetch settles it at the response's usage.
#[tokio::test]
async fn a_deferred_response_settles_when_its_fetch_ends() {
    let handle = DeferredHandle {
        provider: "faux".to_owned(),
        model_id: "faux-1".to_owned(),
        api: "faux".to_owned(),
        id: "job-1".to_owned(),
        expires_at: None,
        poll_after_ms: None,
        data: None,
    };
    let deferred = handle.clone();
    let row = scripted(move || {
        vec![AssistantMessageEvent::Done {
            reason: DoneReason::Deferred,
            message: AssistantMessage {
                stop_reason: StopReason::Deferred,
                deferred: Some(deferred.clone()),
                ..message("", Usage::default())
            },
        }]
    });
    let fetch: FetchDeferredFn = Arc::new(|_model, _handle, _options| {
        let stream = AssistantMessageEventStream::new();
        stream.push(AssistantMessageEvent::Done {
            reason: DoneReason::Stop,
            message: message(
                "done",
                Usage {
                    input: 30,
                    output: 70,
                    ..Usage::default()
                },
            ),
        });
        stream.end(None);
        stream
    });
    let fixture = Fixture::build(Answer::Deferred(row, fetch), Clock::Real);
    let limits = tokens(100_000);
    fixture.gate.set(limits).unwrap();
    let context = chat("summarize");
    let held = fixture.input_tokens(&context) + 16_384;
    fixture.send(context).await;
    let open = fixture.gate.report();
    fixture
        .models
        .fetch_deferred(
            &fixture.faux.get_model(),
            &handle,
            DeferredFetchOptions::default().into(),
        )
        .await;
    assert_eq!(
        (open, fixture.gate.report()),
        (
            Some(BudgetReport {
                free: BudgetAmounts {
                    tokens: 100_000 - held,
                    ..BudgetAmounts::default()
                },
                held: BudgetAmounts {
                    tokens: held,
                    ..BudgetAmounts::default()
                },
                ..report(limits)
            }),
            Some(BudgetReport {
                free: BudgetAmounts {
                    tokens: 100_000 - 100,
                    ..BudgetAmounts::default()
                },
                spent: BudgetAmounts {
                    tokens: 100,
                    ..BudgetAmounts::default()
                },
                ..report(limits)
            }),
        )
    );
}

/// A provider registered on a gated collection after the gate was
/// installed passes the gate too.
#[tokio::test]
async fn a_provider_registered_after_the_wrap_is_gated() {
    let fixture = Fixture::new();
    fixture.gate.set(tokens(1_000)).unwrap();
    let late = faux_provider(RegisterFauxProviderOptions {
        provider: Some("late".to_owned()),
        ..RegisterFauxProviderOptions::default()
    });
    fixture.models.set_provider(late.provider.clone());
    let reply = fixture
        .models
        .complete_simple(
            &late.get_model(),
            chat("summarize"),
            ModelsSimpleStreamOptions::from(SimpleStreamOptions::default()),
        )
        .await;
    assert_eq!(
        (reply.error_message, late.state().call_count),
        (
            Some(
                "Budget exhausted (tokens): the request was not sent. Add budget to continue."
                    .to_owned()
            ),
            0
        )
    );
}

/// B6: an agent turn that work no longer fits is sent as the final answer:
/// no tools, the wrap-up notice as its last message, the phase `WrapUp`.
#[tokio::test]
async fn an_agent_turn_refused_as_work_is_sent_as_the_final_answer() {
    let fixture = Fixture::new();
    // No work cap fits 4000 tokens; a final answer of 2048 does.
    fixture.gate.set(tokens(4_000)).unwrap();
    let reply = fixture.request(agent("build it")).await;
    let notice = "[budget] The tokens budget of this task is used up for work: 4.0k tokens left, too little for another step beside the final answer. Tools are no longer available. Give your final answer now: what is done, what is not, and how to continue. At most 2048 output tokens.";
    assert_eq!(
        (
            reply.error_message,
            fixture.received(),
            fixture.gate.phase(),
            fixture.notices.lock().unwrap().clone()
        ),
        (
            None,
            vec![Received {
                max_tokens: Some(2_048),
                tool_choice: Some(ToolChoice::None),
                last: Some(notice.to_owned()),
            }],
            Some(BudgetPhase::WrapUp),
            vec![Notice {
                kind: NoticeKind::WrapUp,
                request_id: "budget:session:wrap-up:-:4000:-:-:-:-".to_owned(),
                text: notice.to_owned(),
            }]
        )
    );
}

/// B6: when the final answer does not fit either, nothing is sent; added
/// budget admits the same request as work again.
#[tokio::test]
async fn an_exhausted_budget_sends_nothing_until_budget_is_added() {
    let fixture = Fixture::new();
    fixture.gate.set(tokens(100)).unwrap();
    let refused = fixture.request(agent("build it")).await;
    assert_eq!(
        (
            refused.error_message,
            fixture.faux.state().call_count,
            fixture.gate.phase()
        ),
        (
            Some(
                "Budget exhausted (tokens): the request was not sent. Add budget to continue."
                    .to_owned()
            ),
            0,
            Some(BudgetPhase::Exhausted)
        )
    );

    fixture
        .gate
        .add(BudgetAmounts {
            tokens: 100_000,
            ..BudgetAmounts::default()
        })
        .unwrap();
    let sent = fixture.request(agent("build it")).await;
    assert_eq!(
        (sent.error_message, fixture.received(), fixture.gate.phase()),
        (
            None,
            vec![Received {
                max_tokens: Some(16_384),
                tool_choice: None,
                last: Some("build it".to_owned()),
            }],
            Some(BudgetPhase::Working)
        )
    );
}

/// B7: a grant that holds whatever is free (the largest output cap that
/// fits) is no sign that the budget runs low: the agent is told its budget
/// and not that it runs low while two steps of what it actually spent fit
/// many times over.
#[tokio::test]
async fn a_hold_that_fills_what_is_free_does_not_make_the_budget_run_low() {
    let fixture = Fixture::new();
    // The largest cap fits (2 * input + 16384 + 7168 tokens), and another
    // request of its size, started when it ends, would not.
    fixture.gate.set(tokens(30_000)).unwrap();
    fixture.request(agent("build it")).await;
    fixture.request(agent("build it")).await;
    assert_eq!(
        (
            fixture
                .received()
                .iter()
                .map(|received| received.max_tokens)
                .collect::<Vec<_>>(),
            fixture.told()
        ),
        (
            vec![Some(16_384), Some(16_384)],
            vec![(
                NoticeKind::Set,
                "budget:session:set:-:30000:-:-:-:-".to_owned()
            )]
        )
    );
}

/// B7: the agent learns that its budget runs low, once, when two steps of
/// the largest it actually spent (3250 tokens) and its final-answer
/// reserve no longer fit what is left; the notice shows what it can still
/// spend and what its final answer keeps of it.
#[tokio::test]
async fn the_budget_runs_low_once_two_steps_of_the_largest_spend_no_longer_fit() {
    let row = scripted(|| {
        vec![AssistantMessageEvent::Done {
            reason: DoneReason::Stop,
            message: message(
                "done",
                Usage {
                    input: 250,
                    output: 3_000,
                    ..Usage::default()
                },
            ),
        }]
    });
    let fixture = Fixture::build(Answer::Row(row), Clock::Real);
    fixture.gate.set(tokens(20_000)).unwrap();
    let set = (
        NoticeKind::Set,
        "budget:session:set:-:20000:-:-:-:-".to_owned(),
    );
    let low = (
        NoticeKind::Low,
        "budget:session:low:-:20000:-:-:-:-".to_owned(),
    );
    let mut told = Vec::new();
    for _ in 0..4 {
        fixture.send(agent("build it")).await;
        told.push(fixture.told());
    }
    let texts: Vec<String> = fixture
        .notices
        .lock()
        .unwrap()
        .iter()
        .map(|notice| notice.text.clone())
        .collect();
    assert_eq!(
        told,
        vec![
            vec![set.clone()],
            vec![set.clone()],
            vec![set.clone(), low.clone()],
            vec![set, low],
        ]
    );
    // 20000 tokens less two steps of 3250 spent; the request in flight
    // holds the rest of what it may spend
    assert!(
        texts[1].starts_with("[budget] Low: 13.5k tokens left, of which the final answer keeps 7."),
        "{texts:?}"
    );
}

/// B7: the agent is told its budget runs low before its work is refused,
/// also when what it actually spends (300 tokens a step) is far below the
/// smallest hold its work can be granted: a step is the larger of the two.
/// Before, low was judged by the actual steps alone, and the turn that was
/// refused came with no Low notice before it.
#[tokio::test]
async fn the_budget_runs_low_before_work_is_refused_when_a_hold_is_larger_than_a_step() {
    let row = scripted(|| {
        vec![AssistantMessageEvent::Done {
            reason: DoneReason::Stop,
            message: message(
                "done",
                Usage {
                    input: 250,
                    output: 50,
                    ..Usage::default()
                },
            ),
        }]
    });
    let fixture = Fixture::build(Answer::Row(row), Clock::Real);
    fixture.gate.set(tokens(20_000)).unwrap();
    let mut low_before_refusal = None;
    for _ in 0..200 {
        let low = fixture
            .told()
            .iter()
            .any(|(kind, _)| *kind == NoticeKind::Low);
        fixture.send(agent("build it")).await;
        if fixture.gate.phase() != Some(BudgetPhase::Working) {
            low_before_refusal = Some(low);
            break;
        }
    }
    assert_eq!(low_before_refusal, Some(true));
}

/// The prices of a model with a long-context tier above 100k input
/// tokens: $0.1/M input and $0.5/M output below it, five times that
/// above.
fn tiered_cost() -> ModelCost {
    ModelCost {
        input: 0.1,
        output: 0.5,
        cache_read: 0.01,
        cache_write: 0.125,
        tiers: Some(vec![ModelCostTier {
            input: 0.5,
            output: 2.5,
            cache_read: 0.05,
            cache_write: 0.625,
            input_tokens_above: 100_000,
        }]),
    }
}

/// B1, B2: a small cost budget funds work. A turn of about 10k input
/// tokens cannot reach the long-context tier, so its worst case and its
/// final-answer reserve are priced below the tier: $0.02 holds the
/// largest cap and leaves the reserve (about $0.0102 and $0.0041),
/// where pricing the tier made the reserve alone pass the budget and
/// sent the turn as the final answer.
#[tokio::test]
async fn a_small_cost_budget_funds_work_below_the_long_context_tier() {
    let fixture = Fixture::priced(tiered_cost());
    let limits = BudgetLimits {
        cost_micros: Some(20_000),
        ..BudgetLimits::default()
    };
    fixture.gate.set(limits).unwrap();
    let task = "fix the module ".repeat(3_000);
    fixture.request(agent(&task)).await;
    assert_eq!(
        (fixture.received(), fixture.gate.phase()),
        (
            vec![Received {
                max_tokens: Some(16_384),
                tool_choice: None,
                last: Some(task),
            }],
            Some(BudgetPhase::Working)
        )
    );
}

/// A session without a ledger sends its requests and runs its tool calls
/// untouched.
#[tokio::test]
async fn a_session_without_a_budget_passes_requests_and_tool_calls_through() {
    let fixture = Fixture::new();
    fixture.request(agent("build it")).await;
    let ran = fixture
        .gate
        .gated_call("tool:probe".to_owned(), BACKGROUND_CONTEXT.clone(), |_cx| {
            std::future::ready(7)
        })
        .await;
    assert_eq!(
        (
            fixture.received(),
            ran,
            fixture.gate.report(),
            fixture.gate.funds_turn(),
            fixture.told()
        ),
        (
            vec![Received {
                max_tokens: None,
                tool_choice: None,
                last: Some("build it".to_owned()),
            }],
            ToolOutcome::Ran(7),
            None,
            true,
            Vec::new()
        )
    );
}

/// L4, tool calls: a budget whose tool calls are spent funds no further
/// turn, though the agent still works (a model request still fits).
#[tokio::test]
async fn a_budget_with_no_tool_call_left_funds_no_further_turn() {
    let fixture = Fixture::new();
    fixture
        .gate
        .set(BudgetLimits {
            tool_calls: Some(1),
            ..BudgetLimits::default()
        })
        .unwrap();
    let before = fixture.gate.funds_turn();
    fixture.request(agent("build it")).await;
    let ran = fixture
        .gate
        .gated_call("tool:probe".to_owned(), BACKGROUND_CONTEXT.clone(), |_cx| {
            std::future::ready(7)
        })
        .await;
    assert_eq!(
        (before, ran, fixture.gate.phase(), fixture.gate.funds_turn()),
        (true, ToolOutcome::Ran(7), Some(BudgetPhase::Working), false)
    );
}

/// L4, model requests: once the request left is the final answer's, no
/// further turn is funded, though the agent still works.
#[tokio::test]
async fn a_budget_with_only_the_final_answer_request_left_funds_no_further_turn() {
    let fixture = Fixture::new();
    fixture
        .gate
        .set(BudgetLimits {
            requests: Some(2),
            ..BudgetLimits::default()
        })
        .unwrap();
    let before = fixture.gate.funds_turn();
    fixture.request(agent("build it")).await;
    assert_eq!(
        (before, fixture.gate.phase(), fixture.gate.funds_turn()),
        (true, Some(BudgetPhase::Working), false)
    );
}

/// L4, tokens: a turn that fit only at its smallest cap leaves too little
/// for the next turn's smallest offer and its final-answer reserve: no
/// further turn is funded, though the agent still works.
#[tokio::test]
async fn a_budget_without_tokens_for_the_next_turn_funds_no_further_turn() {
    let fixture = Fixture::new();
    let context = agent("build it");
    let input = fixture.input_tokens(&context);
    fixture.gate.set(tokens(2 * input + 1_024 + 7_168)).unwrap();
    let before = fixture.gate.funds_turn();
    fixture.request(context).await;
    assert_eq!(
        (
            before,
            fixture.received(),
            fixture.gate.phase(),
            fixture.gate.funds_turn()
        ),
        (
            true,
            vec![Received {
                max_tokens: Some(1_024),
                tool_choice: None,
                last: Some("build it".to_owned()),
            }],
            Some(BudgetPhase::Working),
            false
        )
    );
}

/// L4, time: 20 s before the deadline is less than the shortest request
/// may run, so no turn is funded; added time funds one again.
#[tokio::test]
async fn a_budget_without_time_for_a_request_funds_no_turn() {
    let fixture = Fixture::build(Answer::Faux, Clock::Fixed);
    fixture
        .gate
        .set(BudgetLimits {
            time_ms: Some(20_000),
            ..BudgetLimits::default()
        })
        .unwrap();
    let short = (fixture.gate.phase(), fixture.gate.funds_turn());
    fixture
        .gate
        .add(BudgetAmounts {
            time_ms: 180_000,
            ..BudgetAmounts::default()
        })
        .unwrap();
    assert_eq!(
        (short, fixture.gate.funds_turn()),
        ((Some(BudgetPhase::Working), false), true)
    );
}

/// Time: a budget with a deadline cancels a tool call at its granted time
/// (the time left before the deadline, here under the 30 s blocking
/// budget): the call's context is cancelled exactly then, and the model
/// reads the budget's tool error.
#[tokio::test(start_paused = true)]
async fn a_tool_call_is_stopped_at_its_granted_time() {
    let fixture = Fixture::build(Answer::Faux, Clock::Fixed);
    fixture
        .gate
        .set(BudgetLimits {
            time_ms: Some(20_000),
            ..BudgetLimits::default()
        })
        .unwrap();
    let stopped_at = Arc::new(Mutex::new(None));
    let seen = Arc::clone(&stopped_at);
    let outcome = fixture
        .gate
        .gated_call(
            "tool:probe".to_owned(),
            BACKGROUND_CONTEXT.clone(),
            move |cx| async move {
                let started = tokio::time::Instant::now();
                cx.abort_signal()
                    .expect("the gate's cancellable context")
                    .cancelled()
                    .await;
                *seen.lock().unwrap() = Some(started.elapsed());
            },
        )
        .await;
    assert_eq!(
        (outcome, *stopped_at.lock().unwrap()),
        (
            ToolOutcome::Refused(notices::TOOL_STOPPED.to_owned()),
            Some(std::time::Duration::from_secs(20))
        )
    );
}

/// B4, B1: a tool call within the tool-call limit runs and settles one
/// call; a call past the limit does not run and answers the budget error.
#[tokio::test]
async fn a_tool_call_past_the_limit_does_not_run() {
    let fixture = Fixture::new();
    let limits = BudgetLimits {
        tool_calls: Some(1),
        ..BudgetLimits::default()
    };
    fixture.gate.set(limits).unwrap();
    let runs = Arc::new(AtomicUsize::new(0));
    let call = || {
        let runs = Arc::clone(&runs);
        fixture.gate.gated_call(
            "tool:probe".to_owned(),
            BACKGROUND_CONTEXT.clone(),
            move |_cx| std::future::ready(runs.fetch_add(1, Ordering::SeqCst)),
        )
    };
    let first = call().await;
    let settled = fixture.gate.report();
    let second = call().await;
    let one_call = BudgetAmounts {
        tool_calls: 1,
        ..BudgetAmounts::default()
    };
    assert_eq!(
        (
            first,
            settled,
            second,
            runs.load(Ordering::SeqCst),
            fixture.gate.report()
        ),
        (
            ToolOutcome::Ran(0),
            Some(BudgetReport {
                spent: one_call,
                ..report(limits)
            }),
            ToolOutcome::Refused(
                "Budget exhausted (tool calls): this tool call was not run. Give your final answer now."
                    .to_owned()
            ),
            1,
            Some(BudgetReport {
                spent: one_call,
                phase: BudgetPhase::WrapUp,
                short: Some(BudgetDimension::ToolCalls),
                ..report(limits)
            })
        )
    );
}

/// The offers of a work request: the caps halve down to the floor, each
/// at the request's deadline (the ledger clips it), each one request and
/// its own worst case; the reserve is the final answer's worst case after
/// the smallest cap.
#[test]
fn every_offer_is_its_requests_worst_case() {
    let cost = ModelCost {
        input: 3.0,
        output: 15.0,
        cache_read: 0.3,
        cache_write: 3.75,
        tiers: Some(vec![ModelCostTier {
            input: 6.0,
            output: 22.5,
            cache_read: 0.6,
            cache_write: 7.5,
            input_tokens_above: 200_000,
        }]),
    };
    let facts = CostFacts {
        cost: &cost,
        price_multiplier: 2.0,
        output_extra: 8_000,
        max_output: 64_000,
        final_ms: 120_000,
    };
    let input = 150_000;
    let ladder = vec![16_384, 8_192, 4_096, 2_048, 1_024];
    assert_eq!(
        offers(&facts, input, 16_384, 600_000),
        (
            facts.final_need(input, 1_024),
            ladder.clone(),
            ladder
                .iter()
                .map(|cap| facts.amount(input, *cap, 600_000))
                .collect::<Vec<_>>()
        )
    );
    assert_eq!(
        (
            facts.amount(input, 1_024, 600_000),
            offers(&facts, input, 1_500, 20_000).1,
            offers(&facts, input, 500, 20_000).1
        ),
        (
            BudgetAmounts {
                cost_micros: facts.amount(input, 1_024, 600_000).cost_micros,
                tokens: input + 1_024 + 8_000,
                time_ms: 600_000,
                tool_calls: 0,
                requests: 1,
            },
            vec![1_500, 1_024],
            vec![500]
        )
    );
}

/// B8: what is left shows in the units a person reads, only for the
/// dimensions the budget limits.
#[test]
fn a_notice_shows_what_is_left_in_each_limited_dimension() {
    let report = BudgetReport {
        session_id: "session".to_owned(),
        agent_session_id: "session".to_owned(),
        limits: BudgetLimits {
            cost_micros: Some(5_000_000),
            tokens: Some(100_000),
            time_ms: Some(600_000),
            tool_calls: Some(10),
            requests: Some(20),
        },
        free: BudgetAmounts {
            cost_micros: 12_345,
            tokens: 12_345,
            time_ms: 80_999,
            tool_calls: 7,
            requests: 3,
        },
        deadline_ms: Some(NOW_MS),
        ..BudgetReport::default()
    };
    let roomy = BudgetReport {
        limits: BudgetLimits {
            time_ms: None,
            ..report.limits
        },
        free: BudgetAmounts {
            cost_micros: 2_509_999,
            tokens: 2_340_000,
            time_ms: 0,
            tool_calls: 1,
            requests: 1,
        },
        held: BudgetAmounts {
            cost_micros: 500_000,
            tokens: 10_000,
            ..BudgetAmounts::default()
        },
        deadline_ms: None,
        ..report.clone()
    };
    let keep = BudgetAmounts {
        cost_micros: 4_200,
        tokens: 7_400,
        time_ms: 120_000,
        tool_calls: 0,
        requests: 1,
    };
    assert_eq!(
        (
            notices::set_text(&report),
            notices::low_text(&roomy, keep),
            notices::remaining(&BudgetReport::default())
        ),
        (
            "[budget] This task has a budget: $0.0123, 12.3k tokens, 1m 20s, 7 tool calls, 3 requests. Nothing can be spent past it: plan your work to fit. In the Python kernel (the python tool) `await budget.status()` returns what is left.".to_owned(),
            "[budget] Low: $3.00, 2.3M tokens, 1 tool call, 1 request left, of which the final answer keeps $0.0042, 7.4k tokens, 0 tool calls, 1 request. Two more steps of the largest size so far would not fit. Finish what matters most; when the work budget is used up you get one final answer without tools.".to_owned(),
            "no limit".to_owned()
        )
    );
}
