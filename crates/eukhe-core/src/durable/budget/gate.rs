//! The chat-request side of a task's budget (spec/README.md B1, B2, B3,
//! B6, B7): a request reserves its worst case in the agent's account before
//! it goes out and settles what it spent when its stream ends.
//!
//! The gate rides INNERMOST, under provider admission and the provider
//! runtime ([`super::rows`]): the reservation is made when the request is
//! about to reach its provider, and every failover re-dispatch and retry
//! passes it again.
//!
//! The input of a request is counted with the model's real tokenizer (the
//! provider's own count up to its last usage, the local count after it),
//! plus the chat template's framing of each locally counted message. A
//! request offers its output caps in order (the wanted one, then halves
//! down to [`MIN_CAP`]); the ledger clips each offer's time to what is left
//! before the deadline, and the first offer that fits is sent, with that
//! cap, and stopped at its granted time when the budget has a deadline.
//! Work leaves the worst case of the agent's final answer free. An agent
//! turn that work no longer fits is sent as the final answer instead: the
//! same context, the wrap-up notice as its last message, no tools. So is
//! an agent turn after the goal reached its token budget in this run
//! ([`BudgetGate::wrap_next`]), with or without a budget. A request that
//! is not an agent turn (a title,
//! a classifier, a compaction, a memory or side question) is a side
//! request: it leaves the reserve of the agent's last turn, holds and is
//! charged no model request (it is no turn of the agent), and when it
//! does not fit it is not sent and changes nothing else. A request that
//! fits in no way is not sent: its stream ends with an error that carries
//! the typed budget refusal, which no retry policy re-issues.

use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::api::simple_options::thinking_budget_for_level;
use eukhe_ai::quirks::service_tier_multiplier;
use eukhe_ai::types::{ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use eukhe_ai::utils::context_tokens::{context_tokens, message_tokens, model_tokenizer};
use eukhe_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_ai::utils::retry::BUDGET_REFUSAL_DIAGNOSTIC;
use eukhe_budget::{
    actual_spend, worst_case_cost_micros, RequestBound, Reserved, Use, REQUEST_MIN_MS,
};
use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_tokens::Tokenizer;
use eukhe_types::budget::{BudgetAmounts, BudgetReport};
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageDiagnostic, AssistantMessageEvent, DeferredHandle,
    DoneReason, ErrorReason, JsonValue, Message, Model, ModelCost, Partial, ServiceTier,
    StopReason, ToolChoice, TranscriptContext, Usage, UserContent, UserMessage,
};
use futures::StreamExt as _;

use super::notices::{self, NoticeKind};
use super::{BudgetGate, Held};
use crate::durable::rlm::now_millis;

/// Chat-template framing charged per locally counted message (as
/// `output_cap_prompt_tokens` charges it): a tokenizer counts a message's
/// content, and every template wraps a message in role markers and
/// separators.
pub(super) const FRAMING_TOKENS: u64 = 16;
/// The smallest output cap a work request is offered with.
const MIN_CAP: u64 = 1024;
/// Tokens kept for the tool results that follow a response, in the context
/// of the final answer after it.
const TOOL_RESERVE: u64 = 4096;
/// The largest output cap of a final answer.
const FINAL_CAP: u64 = 2048;
/// The smallest output cap a final answer is offered with.
const FINAL_MIN_CAP: u64 = 256;
/// How long a final answer may run.
const FINAL_TIME_MS: u64 = 120_000;
/// How long a request without a timeout of its own may run.
pub(super) const DEFAULT_DEADLINE_MS: u64 = 600_000;

/// What bounds the spend of a request to one model: its prices, the
/// multiplier of the service tier it asks for, and how far the provider's
/// output may pass the cap the request names.
#[derive(Debug, Clone, Copy)]
pub(super) struct CostFacts<'a> {
    pub cost: &'a ModelCost,
    /// 1.0: the list price.
    pub price_multiplier: f64,
    /// Output tokens the provider adds on top of the request's cap (the
    /// thinking budget of a budget-mode thinking request).
    pub output_extra: u64,
    /// The model's largest output: no response passes it, whatever the cap.
    pub max_output: u64,
}

impl CostFacts<'_> {
    /// The worst case of one request of `input` tokens under the output
    /// cap `cap` that may run for `time_ms`.
    pub(super) fn amount(&self, input: u64, cap: u64, time_ms: u64) -> BudgetAmounts {
        let output = cap.saturating_add(self.output_extra).min(self.max_output);
        BudgetAmounts {
            cost_micros: worst_case_cost_micros(
                self.cost,
                RequestBound {
                    input_tokens: input,
                    output_cap: output,
                    price_multiplier: self.price_multiplier,
                },
            ),
            tokens: input.saturating_add(output),
            time_ms,
            tool_calls: 0,
            requests: 1,
        }
    }

    /// The worst case of the final answer after a response to `input`
    /// tokens under the output cap `cap`: its context grew by that
    /// response and by [`TOOL_RESERVE`] tokens of tool results.
    pub(super) fn final_need(&self, input: u64, cap: u64) -> BudgetAmounts {
        let response = cap.saturating_add(self.output_extra).min(self.max_output);
        self.amount(
            input.saturating_add(response).saturating_add(TOOL_RESERVE),
            FINAL_CAP,
            FINAL_TIME_MS,
        )
    }
}

/// The input tokens of a request over `messages` as the budget bounds
/// them: the provider's count at the last applicable usage, exact, plus
/// the real-tokenizer count of the messages after it (of every message
/// without one), plus [`FRAMING_TOKENS`] per locally counted message.
pub(super) fn prompt_tokens(tokenizer: &Tokenizer, messages: &[Message]) -> u64 {
    let counted = context_tokens(tokenizer, messages);
    let local = messages.len() - counted.last_usage_index.map_or(0, |index| index + 1);
    counted
        .tokens
        .saturating_add(FRAMING_TOKENS.saturating_mul(local as u64))
}

/// What a work request of `input` tokens offers the ledger: the reserve
/// `keep` it leaves free (the final answer's worst case after the smallest
/// cap), and its offers in order with the output cap of each (`caps[i]` is
/// the cap of `offers[i]`): `want_cap`, then its halves down to
/// [`MIN_CAP`] (`want_cap` alone when it is smaller), each at
/// `deadline_ms` (the ledger clips it to what is left).
pub(super) fn offers(
    facts: &CostFacts<'_>,
    input: u64,
    want_cap: u64,
    deadline_ms: u64,
) -> (BudgetAmounts, Vec<u64>, Vec<BudgetAmounts>) {
    let mut caps = vec![want_cap];
    let mut smallest = want_cap;
    while smallest / 2 >= MIN_CAP {
        smallest /= 2;
        caps.push(smallest);
    }
    if smallest > MIN_CAP {
        smallest = MIN_CAP;
        caps.push(smallest);
    }
    let keep = facts.final_need(input, smallest);
    let amounts = caps
        .iter()
        .map(|cap| facts.amount(input, *cap, deadline_ms))
        .collect();
    (keep, caps, amounts)
}

/// What a request that failed after its provider started answering spent:
/// the usage the provider reported, its output never below the real-token
/// count of what streamed (`streamed`), the part past the reported output
/// at its worst price; `full` (the whole reservation) when the provider
/// reported nothing.
pub(super) fn failed_spend(
    cost: &ModelCost,
    tokenizer: &Tokenizer,
    reported: &Usage,
    streamed: &AssistantMessage,
    full: BudgetAmounts,
) -> BudgetAmounts {
    let nothing = reported.input == 0
        && reported.output == 0
        && reported.cache_read == 0
        && reported.cache_write == 0
        && reported.cost.total <= 0.0;
    if nothing {
        return full;
    }
    let counted = message_tokens(tokenizer, &Message::Assistant(streamed.clone()));
    let missing = counted.saturating_sub(reported.output);
    let spend = actual_spend(reported);
    if missing == 0 {
        return spend;
    }
    BudgetAmounts {
        cost_micros: spend.cost_micros.saturating_add(worst_case_cost_micros(
            cost,
            RequestBound {
                input_tokens: 0,
                output_cap: missing,
                price_multiplier: 1.0,
            },
        )),
        tokens: spend.tokens.saturating_add(missing),
        ..spend
    }
}

/// The key of a deferred response's reservation.
pub(super) fn deferred_key(handle: &DeferredHandle) -> String {
    format!("{}/{}", handle.provider, handle.id)
}

/// Whether the request is an agent turn: its transcript declares tools (a
/// system message with `tools_added`).
fn declares_tools(context: &TranscriptContext) -> bool {
    context.messages().iter().any(|message| {
        message.as_system().is_some_and(|system| {
            system
                .tools_added
                .as_ref()
                .is_some_and(|tools| !tools.is_empty())
        })
    })
}

/// The options of a provider row's request, as the gate reads and changes
/// them. A row takes one of two option types
/// ([`SimpleStreamOptions`], [`ProviderStreamOptions`]); an implementation
/// maps the gate's reads and its two changes (the output cap and the abort
/// signal through `stream_mut`, no tools through `disable_tools`) onto the
/// fields its type carries them in.
pub(super) trait GatedOptions: Send + 'static {
    /// The options every chat request shares.
    fn stream(&self) -> &StreamOptions;
    /// [`Self::stream`], to set the output cap and the abort signal.
    fn stream_mut(&mut self) -> &mut StreamOptions;
    /// The service tier the request asks for, as the price table names it.
    fn service_tier(&self) -> Option<&str>;
    /// Output tokens `model`'s provider adds on top of the request's cap.
    fn output_extra(&self, model: &Model) -> u64;
    /// Make the request call no tool.
    fn disable_tools(&mut self);
}

impl GatedOptions for SimpleStreamOptions {
    fn stream(&self) -> &StreamOptions {
        &self.stream
    }

    fn stream_mut(&mut self) -> &mut StreamOptions {
        &mut self.stream
    }

    fn service_tier(&self) -> Option<&str> {
        self.stream.service_tier.map(ServiceTier::as_str)
    }

    /// A budget-mode thinking request (Anthropic Messages, Claude on
    /// Bedrock) thinks on top of the caller's cap; the level's budget
    /// bounds it for every API.
    fn output_extra(&self, model: &Model) -> u64 {
        match self.reasoning {
            Some(level) if model.reasoning => {
                thinking_budget_for_level(level, self.thinking_budgets.as_ref())
            }
            Some(_) | None => 0,
        }
    }

    fn disable_tools(&mut self) {
        self.tool_choice = Some(ToolChoice::None);
    }
}

impl GatedOptions for ProviderStreamOptions {
    fn stream(&self) -> &StreamOptions {
        &self.stream
    }

    fn stream_mut(&mut self) -> &mut StreamOptions {
        &mut self.stream
    }

    fn service_tier(&self) -> Option<&str> {
        self.extra
            .get("serviceTier")
            .and_then(JsonValue::as_str)
            .or_else(|| self.stream.service_tier.map(ServiceTier::as_str))
    }

    /// The API-specific options name their thinking budget inside the cap.
    fn output_extra(&self, _model: &Model) -> u64 {
        0
    }

    /// Every API reads its tool choice from the `toolChoice` key and takes
    /// `"none"`.
    fn disable_tools(&mut self) {
        self.extra
            .insert("toolChoice".to_owned(), JsonValue::from("none"));
    }
}

/// A provider row's stream function over the options type `O`.
pub(super) type Row<O> =
    Arc<dyn Fn(&Model, &TranscriptContext, O) -> AssistantMessageEventStream + Send + Sync>;

/// How a sent request's stream ended.
enum End {
    Done {
        reason: DoneReason,
        message: AssistantMessage,
    },
    /// An error event, or no terminal event at all.
    Failed(Option<AssistantMessageEvent>),
}

/// One request of an agent that has a budget, on its way through the gate.
pub(super) struct Request<O> {
    pub(super) gate: Arc<BudgetGate>,
    pub(super) model: Model,
    pub(super) inner: Row<O>,
    pub(super) sink: AssistantMessageEventStream,
}

/// A granted request about to go out: its reservation, the report that
/// granted it, and the context it is sent with.
struct Granted {
    id: u64,
    amount: BudgetAmounts,
    report: BudgetReport,
    context: TranscriptContext,
}

/// An agent turn on its way to be sent as its final answer: its input
/// tokens, its `provider/model` label, and the budget's report that
/// refused it as work (`None`: a limit of its run made it the final
/// answer).
struct Finale {
    input: u64,
    target: String,
    report: Option<BudgetReport>,
}

impl<O: GatedOptions> Request<O> {
    /// End the request without sending it (or after the budget stopped
    /// it): `text` is its error, with the typed budget refusal.
    fn refuse(&self, text: String) {
        let model = &self.model;
        self.sink.push(AssistantMessageEvent::Error {
            reason: ErrorReason::Error,
            error: AssistantMessage {
                content: Vec::new(),
                api: model.api.clone(),
                provider: model.provider.clone(),
                model: model.id.clone(),
                response_model: None,
                response_id: None,
                provider_thinking_level: None,
                thinking_level: None,
                diagnostics: Some(vec![AssistantMessageDiagnostic {
                    kind: BUDGET_REFUSAL_DIAGNOSTIC.to_owned(),
                    timestamp: now_millis(),
                    error: None,
                    details: None,
                }]),
                usage: Usage::default(),
                stop_reason: StopReason::Error,
                deferred: None,
                error_message: Some(text),
                raw_stop_reason: None,
                end_turn: None,
                timestamp: now_millis(),
                duration_ms: None,
                timing: None,
            },
        });
        self.sink.end(None);
    }

    /// Send the request as it came: the session has no budget after all
    /// (its ledger file holds no record).
    async fn pass(&self, context: &TranscriptContext, options: O) {
        let mut events = (self.inner)(&self.model, context, options).events();
        while let Some(event) = events.next().await {
            self.sink.push(event);
        }
        self.sink.end(None);
    }

    /// The model's output limit: its catalog's, else its window.
    fn max_output(&self) -> u64 {
        if self.model.max_tokens == 0 {
            // The catalog names no output limit: the window bounds it.
            self.model.context_window.max(MIN_CAP)
        } else {
            self.model.max_tokens
        }
    }

    /// What bounds the spend of this request with `options`.
    fn cost_facts(&self, options: &O) -> CostFacts<'_> {
        let model = &self.model;
        CostFacts {
            cost: &model.cost,
            price_multiplier: options
                .service_tier()
                .and_then(|tier| service_tier_multiplier(model.into(), tier))
                .unwrap_or(1.0),
            output_extra: options.output_extra(model),
            max_output: self.max_output(),
        }
    }

    /// Reserve, send what was granted, forward its events and settle.
    pub(super) async fn run(self, context: TranscriptContext, mut options: O) {
        let model = &self.model;
        let max_output = self.max_output();
        let facts = self.cost_facts(&options);
        let want_cap = options
            .stream()
            .max_tokens
            .unwrap_or(max_output)
            .clamp(1, max_output);
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "a positive duration, held far below 2^53 ms"
        )]
        let deadline_ms = match options.stream().request.timeout_ms {
            Some(timeout) if timeout > 0.0 => timeout.min(1e12).ceil() as u64,
            Some(_) | None => DEFAULT_DEADLINE_MS,
        };
        let tokenizer = model_tokenizer(model);
        let input = prompt_tokens(&tokenizer, context.messages());
        let (own_keep, caps, work) = offers(&facts, input, want_cap, deadline_ms);
        // An agent turn leaves its own final answer free; any other request
        // of the agent is a side request: it leaves the reserve of the
        // agent's last turn and is no turn (it holds no model request).
        let agent_turn = declares_tools(&context);
        let target = format!("{}/{}", model.provider, model.id);
        if agent_turn {
            // A limit of the agent's run was reached: this turn is its
            // final answer.
            if let Some(reason) = self.gate.wrap() {
                let finale = Finale {
                    input,
                    target,
                    report: None,
                };
                return self
                    .final_answer(context, options, &tokenizer, finale, |cap| {
                        notices::run_wrap_up_text(&reason, cap)
                    })
                    .await;
            }
        }
        let (use_, keep, offered) = if agent_turn {
            self.gate.set_keep(own_keep);
            (Use::Work, own_keep, work)
        } else {
            let side = work
                .into_iter()
                .map(|amount| BudgetAmounts {
                    requests: 0,
                    ..amount
                })
                .collect();
            (Use::Side, self.gate.keep(), side)
        };
        let reserved = self
            .gate
            .reserve(
                use_,
                format!("model:{target}"),
                keep,
                offered,
                REQUEST_MIN_MS,
            )
            .await;
        let granted = match reserved {
            Ok(None) => return self.pass(&context, options).await,
            Err(error) => {
                return self.refuse(notices::ledger_failed("the request was not sent", &error))
            }
            Ok(Some(Reserved::Granted {
                reservation,
                report,
            })) => {
                options.stream_mut().max_tokens = Some(caps[reservation.index]);
                if agent_turn {
                    self.gate
                        .tell(NoticeKind::Set, &report, || notices::set_text(&report));
                    if reservation.tight {
                        self.gate
                            .tell(NoticeKind::Low, &report, || notices::low_text(&report));
                    }
                }
                Granted {
                    id: reservation.id,
                    amount: reservation.amount,
                    report,
                    context,
                }
            }
            Ok(Some(Reserved::Refused { refusal, report })) => {
                let short = notices::short_label(refusal, &report);
                if !agent_turn {
                    return self.refuse(notices::request_refused(short));
                }
                // An agent turn: its final answer, from what the reserve kept.
                let finale = Finale {
                    input,
                    target,
                    report: Some(report.clone()),
                };
                return self
                    .final_answer(context, options, &tokenizer, finale, |cap| {
                        notices::wrap_up_text(short, &report, cap)
                    })
                    .await;
            }
        };
        self.send(granted, &tokenizer, options).await;
    }

    /// Send the agent's turn as its final answer: the same context with
    /// `notice` (of the answer's output cap) as its last message, no tools,
    /// at most [`FINAL_CAP`] output tokens, reserved as the final answer
    /// (from what the reserve kept) when the session has a budget. A
    /// budget's refusal (`finale.report`) is told to the user as the
    /// wrap-up notice.
    async fn final_answer(
        self,
        context: TranscriptContext,
        mut options: O,
        tokenizer: &Tokenizer,
        finale: Finale,
        notice: impl Fn(u64) -> String,
    ) {
        let Finale {
            input,
            target,
            report,
        } = finale;
        let max_output = self.max_output();
        let mut final_caps: Vec<u64> = Vec::with_capacity(4);
        for cap in [FINAL_CAP, FINAL_CAP / 2, FINAL_CAP / 4, FINAL_MIN_CAP] {
            let cap = cap.min(max_output);
            if !final_caps.contains(&cap) {
                final_caps.push(cap);
            }
        }
        // The notice with the largest cap is the longest one.
        let longest = Message::User(UserMessage {
            content: UserContent::Text(notice(final_caps[0])),
            timestamp: now_millis(),
        });
        let input = input
            .saturating_add(message_tokens(tokenizer, &longest))
            .saturating_add(FRAMING_TOKENS);
        let facts = self.cost_facts(&options);
        let answers = final_caps
            .iter()
            .map(|cap| facts.amount(input, *cap, FINAL_TIME_MS))
            .collect();
        let answered = self
            .gate
            .reserve(
                Use::Final,
                format!("final:{target}"),
                BudgetAmounts::default(),
                answers,
                REQUEST_MIN_MS,
            )
            .await;
        let wrap_up = |cap: u64, options: &mut O| {
            let mut messages = context.clone().into_messages();
            messages.push(Message::User(UserMessage {
                content: UserContent::Text(notice(cap)),
                timestamp: now_millis(),
            }));
            options.disable_tools();
            options.stream_mut().max_tokens = Some(cap);
            TranscriptContext::from_normalized_messages(messages)
        };
        match answered {
            // No budget: the run's limit alone makes this the final answer.
            Ok(None) => {
                let context = wrap_up(final_caps[0], &mut options);
                self.pass(&context, options).await;
            }
            Err(error) => self.refuse(notices::ledger_failed("the request was not sent", &error)),
            Ok(Some(Reserved::Refused { refusal, report })) => self.refuse(
                notices::request_refused(notices::short_label(refusal, &report)),
            ),
            Ok(Some(Reserved::Granted {
                reservation,
                report: granted,
            })) => {
                let cap = final_caps[reservation.index];
                if report.is_some() {
                    let text = notice(cap);
                    self.gate.tell(NoticeKind::WrapUp, &granted, || text);
                }
                let context = wrap_up(cap, &mut options);
                let granted = Granted {
                    id: reservation.id,
                    amount: reservation.amount,
                    report: granted,
                    context,
                };
                self.send(granted, tokenizer, options).await;
            }
        }
    }

    /// Send a granted request, forward its events, and settle it once:
    /// a response at its usage, a deferred one when its fetch ends, a
    /// request its provider never started at one request, one that failed
    /// after it started at what the provider reported (whole when it
    /// reported nothing).
    async fn send(self, granted: Granted, tokenizer: &Tokenizer, mut options: O) {
        let Granted {
            id,
            amount,
            report,
            context,
        } = granted;
        let model = &self.model;
        // A budget with a deadline stops the request at its granted time.
        let stop_after = report
            .deadline_ms
            .map(|_| Duration::from_millis(amount.time_ms));
        let stopper = AbortController::new();
        if stop_after.is_some() {
            let request = &mut options.stream_mut().request;
            request.signal = Some(match request.signal.take() {
                Some(caller) => AbortSignal::any(&[caller, stopper.signal()]),
                None => stopper.signal(),
            });
        }
        let held = Held::start(&self.gate, id, amount);
        let mut events = (self.inner)(model, &context, options).events();
        let stop = async {
            match stop_after {
                Some(after) => tokio::time::sleep(after).await,
                None => std::future::pending().await,
            }
        };
        tokio::pin!(stop);
        let mut timed_out = false;
        // The live message of the response, from the provider's `Start`:
        // without one the provider never began to answer.
        let mut started: Option<Partial> = None;
        let end = loop {
            let event = tokio::select! {
                biased;
                () = &mut stop, if !timed_out => {
                    timed_out = true;
                    stopper.abort(None);
                    continue;
                }
                event = events.next() => event,
            };
            let Some(event) = event else {
                break End::Failed(None);
            };
            match event {
                AssistantMessageEvent::Done { reason, message } => {
                    break End::Done { reason, message }
                }
                AssistantMessageEvent::Error { .. } => break End::Failed(Some(event)),
                AssistantMessageEvent::Start { partial } => {
                    started = Some(partial.clone());
                    self.sink.push(AssistantMessageEvent::Start { partial });
                }
                AssistantMessageEvent::PromptProgress { .. }
                | AssistantMessageEvent::TextStart { .. }
                | AssistantMessageEvent::TextDelta { .. }
                | AssistantMessageEvent::TextEnd { .. }
                | AssistantMessageEvent::ThinkingStart { .. }
                | AssistantMessageEvent::ThinkingDelta { .. }
                | AssistantMessageEvent::ThinkingEnd { .. }
                | AssistantMessageEvent::ToolCallStart { .. }
                | AssistantMessageEvent::ToolCallDelta { .. }
                | AssistantMessageEvent::ToolCallEnd { .. } => self.sink.push(event),
            }
        };

        // Settle before the consumer sees the end: its next request finds
        // what this one did not spend free again.
        let (spend, last) = match end {
            End::Done { reason, message } => match (reason, message.deferred.as_ref()) {
                // The response comes later, through its handle: the
                // reservation stays open until the fetch settles it.
                (DoneReason::Deferred, Some(handle)) => {
                    self.gate.park_deferred(deferred_key(handle), held);
                    self.sink
                        .push(AssistantMessageEvent::Done { reason, message });
                    self.sink.end(None);
                    return;
                }
                (
                    DoneReason::Stop
                    | DoneReason::Length
                    | DoneReason::ToolUse
                    | DoneReason::Deferred,
                    _,
                ) => (
                    actual_spend(&message.usage),
                    Some(AssistantMessageEvent::Done { reason, message }),
                ),
            },
            End::Failed(last) => {
                let spend = match &started {
                    None => BudgetAmounts {
                        requests: 1,
                        ..BudgetAmounts::default()
                    },
                    Some(partial) => {
                        let streamed = partial.snapshot();
                        // The provider puts what it counted on its error;
                        // without one, the live message carries it.
                        let reported =
                            if let Some(AssistantMessageEvent::Error { error, .. }) = &last {
                                error.usage
                            } else {
                                streamed.usage
                            };
                        failed_spend(&model.cost, tokenizer, &reported, &streamed, held.full)
                    }
                };
                if timed_out {
                    held.settle(spend).await;
                    return self.refuse(notices::REQUEST_STOPPED.to_owned());
                }
                (spend, last)
            }
        };
        held.settle(spend).await;
        if let Some(last) = last {
            self.sink.push(last);
        }
        self.sink.end(None);
    }
}
