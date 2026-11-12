//! The chat-request side of a task's budget (spec/README.md B1, B2, B3,
//! B6, B7, B14): a request reserves its worst case in the agent's account before
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
//! Work leaves the worst case of the agent's final answer free, its time
//! in proportion to the time budget and to the agent's longest model
//! request ([`final_time_ms`]). An agent
//! turn that work no longer fits is sent as the final answer instead: the
//! same context, the wrap-up notice as its last message, no tools; so is
//! an agent turn stopped at its granted time. One stopped after it
//! streamed content keeps what streamed in the agent's message (its open
//! text closed, its tool calls never run) and the final answer's content
//! follows it there. A request that is not an agent turn (a title,
//! a classifier, a compaction, a memory or side question) is a side
//! request: it leaves the reserve of the agent's last turn, holds and is
//! charged no model request (it is no turn of the agent), and when it
//! does not fit it is not sent and changes nothing else. A request that
//! fits in no way is not sent: its stream ends with an error that carries
//! the typed budget refusal, which no retry policy re-issues.

use std::sync::{Arc, PoisonError};
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
use eukhe_types::budget::{BudgetAmounts, BudgetDimension, BudgetReport};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageDiagnostic, AssistantMessageEvent,
    DeferredHandle, DoneReason, ErrorReason, JsonValue, Message, Model, ModelCost, Partial,
    ServiceTier, StopReason, ToolChoice, TranscriptContext, Usage, UserContent, UserMessage,
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
/// The longest a final answer may run (B14).
const FINAL_TIME_MS: u64 = 120_000;
/// The least time kept for a final answer once one of the agent's model
/// requests ended (B14).
const FINAL_MIN_TIME_MS: u64 = 20_000;
/// How long a request without a timeout of its own may run.
pub(super) const DEFAULT_DEADLINE_MS: u64 = 600_000;

/// How long the agent's final answer may run, and so the time its reserve
/// keeps (B14): [`FINAL_TIME_MS`] at most, a quarter of the time budget
/// `budget_ms` at most, and twice the agent's longest model request
/// `longest_ms` at most but never below [`FINAL_MIN_TIME_MS`] once one
/// ended.
fn final_time_ms(budget_ms: Option<u64>, longest_ms: Option<u64>) -> u64 {
    let capped = budget_ms.map_or(FINAL_TIME_MS, |budget| FINAL_TIME_MS.min(budget / 4));
    match longest_ms {
        Some(longest) => capped.min(longest.saturating_mul(2)).max(FINAL_MIN_TIME_MS),
        None => capped,
    }
}

/// What bounds the spend of a request to one model: its prices, the
/// multiplier of the service tier it asks for, how far the provider's
/// output may pass the cap the request names, and how long the agent's
/// final answer may run.
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
    /// How long the agent's final answer may run ([`final_time_ms`]).
    pub final_ms: u64,
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
                    billed_input_tokens: input,
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
            self.final_ms,
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
                // the hold's tokens (input and output cap) bound the
                // request's billed input, which picks its price tier
                billed_input_tokens: full.tokens,
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
pub(super) trait GatedOptions: Clone + Send + 'static {
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

/// A granted request about to go out: its reservation and what it is for,
/// the report that granted it, and the context it is sent with.
struct Granted {
    id: u64,
    amount: BudgetAmounts,
    use_: Use,
    report: BudgetReport,
    context: TranscriptContext,
}

/// An agent turn that work no longer fits, on its way to be sent as its
/// final answer: its input tokens, its `provider/model` label, and the
/// work it asked for when the deadline cut its granted time.
struct Finale {
    input: u64,
    target: String,
    again: Option<Again>,
}

/// The work a turn asked for (its reserve and its offers), asked again
/// when the turn is stopped at a granted time the deadline cut: what is
/// left for work is then below a request's floor, so the ledger refuses
/// it for time and moves the agent to `WrapUp`, as a turn refused for time
/// (B6).
struct Again {
    keep: BudgetAmounts,
    offers: Vec<BudgetAmounts>,
}

/// What a sent request is, for what its stop at its granted time does.
enum Turn {
    /// A side request: it ends with the budget's error.
    Side,
    /// An agent's work turn: stopped, it is sent again as its final answer.
    Work(Finale),
    /// An agent's final answer: it ends with the budget's error.
    Final(Opened),
}

/// What the consumer already holds of the agent's message when its final
/// answer is sent.
enum Opened {
    /// Nothing: the final answer's message is the agent's.
    No,
    /// The start of a stopped work turn's message, without content: the
    /// final answer streams into it without a start of its own.
    Yes,
    /// A stopped work turn's message with the content it streamed: the
    /// final answer's blocks follow it.
    Streamed(Box<Streamed>),
}

/// The blocks of a work turn's stream as the consumer saw them start and
/// end.
#[derive(Default)]
struct Seen {
    /// How many blocks started: the consumer's message holds that many.
    count: usize,
    /// The blocks started and not ended, in the order they started.
    open: Vec<usize>,
}

impl Seen {
    fn see(&mut self, event: &AssistantMessageEvent) {
        match event {
            AssistantMessageEvent::TextStart { content_index, .. }
            | AssistantMessageEvent::ThinkingStart { content_index, .. }
            | AssistantMessageEvent::ToolCallStart { content_index, .. } => {
                self.count = self.count.max(content_index + 1);
                self.open.push(*content_index);
            }
            AssistantMessageEvent::TextEnd { content_index, .. }
            | AssistantMessageEvent::ThinkingEnd { content_index, .. }
            | AssistantMessageEvent::ToolCallEnd { content_index, .. } => {
                self.open.retain(|open| open != content_index);
            }
            AssistantMessageEvent::Start { .. }
            | AssistantMessageEvent::PromptProgress { .. }
            | AssistantMessageEvent::TextDelta { .. }
            | AssistantMessageEvent::ThinkingDelta { .. }
            | AssistantMessageEvent::ToolCallDelta { .. }
            | AssistantMessageEvent::Done { .. }
            | AssistantMessageEvent::Error { .. } => {}
        }
    }
}

/// The message of a work turn stopped after it streamed content, which the
/// consumer holds: the final answer's events are rebased into it, its
/// block `i` at `offset + i`, on the work turn's own live partial.
struct Streamed {
    /// The work turn's live message, shared with the consumer.
    partial: Partial,
    /// What `partial` holds: the streamed blocks, then the final answer's.
    shown: AssistantMessage,
    /// How many blocks streamed.
    offset: usize,
}

impl Streamed {
    /// The stopped work turn's message `partial` of the `seen` blocks: its
    /// open text and thinking end as they streamed (pushed to `sink`); an
    /// open tool call stays unfinished (no event ends a call without
    /// completing it), and no tool call of it is ever run.
    fn cut(partial: Partial, seen: Seen, sink: &AssistantMessageEventStream) -> Self {
        let mut shown = partial.snapshot();
        if shown.content.len() > seen.count {
            // Blocks the provider made and never told: the consumer has
            // none of them.
            shown.content.truncate(seen.count);
            partial.replace(&shown);
        }
        for content_index in seen.open {
            let end = match shown.content.get(content_index) {
                Some(AssistantContentBlock::Text(text)) => AssistantMessageEvent::TextEnd {
                    content_index,
                    content: text.text.clone(),
                    partial: partial.clone(),
                },
                Some(AssistantContentBlock::Thinking(thinking)) => {
                    AssistantMessageEvent::ThinkingEnd {
                        content_index,
                        content: thinking.thinking.clone(),
                        partial: partial.clone(),
                    }
                }
                Some(AssistantContentBlock::ToolCall(_)) | None => continue,
            };
            sink.push(end);
        }
        Streamed {
            partial,
            offset: seen.count,
            shown,
        }
    }

    /// The final answer's `event` as an event of the stopped turn's
    /// message: its block rebased past the streamed ones, on that
    /// message's partial.
    fn follow(&mut self, mut event: AssistantMessageEvent) -> AssistantMessageEvent {
        let offset = self.offset;
        let shown = &mut self.shown;
        let answer = match &mut event {
            AssistantMessageEvent::PromptProgress { partial, .. } => {
                partial.read(|answer| follow_fields(shown, answer));
                partial
            }
            AssistantMessageEvent::TextDelta {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::ThinkingDelta {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::ToolCallDelta {
                content_index,
                partial,
                ..
            } => {
                partial.read(|answer| follow_block(shown, answer, offset, *content_index));
                *content_index += offset;
                partial
            }
            AssistantMessageEvent::TextStart {
                content_index,
                partial,
            }
            | AssistantMessageEvent::TextEnd {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::ThinkingStart {
                content_index,
                partial,
            }
            | AssistantMessageEvent::ThinkingEnd {
                content_index,
                partial,
                ..
            }
            | AssistantMessageEvent::ToolCallStart {
                content_index,
                partial,
            }
            | AssistantMessageEvent::ToolCallEnd {
                content_index,
                partial,
                ..
            } => {
                partial.read(|answer| follow_all(shown, answer, offset));
                *content_index += offset;
                partial
            }
            // No block: nothing to rebase.
            AssistantMessageEvent::Start { .. }
            | AssistantMessageEvent::Done { .. }
            | AssistantMessageEvent::Error { .. } => return event,
        };
        answer.clone_from(&self.partial);
        self.partial.publish(&self.shown, &event);
        event
    }

    /// The final answer's `message` as the agent's whole message: the text
    /// and thinking that streamed before the stop, then its own content.
    /// The stopped turn's tool calls are left out: they never run.
    fn finish(&self, mut message: AssistantMessage) -> AssistantMessage {
        let answer = std::mem::take(&mut message.content);
        message.content = self.shown.content[..self.offset]
            .iter()
            .filter(|block| match block {
                AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => true,
                AssistantContentBlock::ToolCall(_) => false,
            })
            .cloned()
            .chain(answer)
            .collect();
        message
    }
}

/// Make `shown`'s fields but its content those of the final answer's
/// message `answer`.
fn follow_fields(shown: &mut AssistantMessage, answer: &AssistantMessage) {
    let AssistantMessage {
        content: _,
        api,
        provider,
        model,
        response_model,
        response_id,
        provider_thinking_level,
        thinking_level,
        diagnostics,
        usage,
        stop_reason,
        deferred,
        error_message,
        raw_stop_reason,
        end_turn,
        timestamp,
        duration_ms,
        timing,
    } = answer;
    shown.api.clone_from(api);
    shown.provider.clone_from(provider);
    shown.model.clone_from(model);
    shown.response_model.clone_from(response_model);
    shown.response_id.clone_from(response_id);
    shown
        .provider_thinking_level
        .clone_from(provider_thinking_level);
    shown.thinking_level.clone_from(thinking_level);
    shown.diagnostics.clone_from(diagnostics);
    shown.usage.clone_from(usage);
    shown.stop_reason.clone_from(stop_reason);
    shown.deferred.clone_from(deferred);
    shown.error_message.clone_from(error_message);
    shown.raw_stop_reason.clone_from(raw_stop_reason);
    shown.end_turn.clone_from(end_turn);
    shown.timestamp.clone_from(timestamp);
    shown.duration_ms.clone_from(duration_ms);
    shown.timing.clone_from(timing);
}

/// Make `shown` follow `answer` after a change to its block `index` only
/// (a delta): that block grows by what it gained.
fn follow_block(
    shown: &mut AssistantMessage,
    answer: &AssistantMessage,
    offset: usize,
    index: usize,
) {
    let grown = match (
        shown.content.get_mut(offset + index),
        answer.content.get(index),
    ) {
        (Some(AssistantContentBlock::Text(target)), Some(AssistantContentBlock::Text(source))) => {
            grow(&mut target.text, &source.text);
            target.text_signature.clone_from(&source.text_signature);
            true
        }
        (
            Some(AssistantContentBlock::Thinking(target)),
            Some(AssistantContentBlock::Thinking(source)),
        ) => {
            grow(&mut target.thinking, &source.thinking);
            target
                .thinking_signature
                .clone_from(&source.thinking_signature);
            true
        }
        (
            Some(AssistantContentBlock::ToolCall(target)),
            Some(AssistantContentBlock::ToolCall(source)),
        ) => {
            target.clone_from(source);
            true
        }
        (
            Some(
                AssistantContentBlock::Text(_)
                | AssistantContentBlock::Thinking(_)
                | AssistantContentBlock::ToolCall(_),
            )
            | None,
            Some(_) | None,
        ) => false,
    };
    if grown {
        follow_fields(shown, answer);
    } else {
        follow_all(shown, answer, offset);
    }
}

/// Make `shown` the streamed blocks, then `answer` whole.
fn follow_all(shown: &mut AssistantMessage, answer: &AssistantMessage, offset: usize) {
    shown.content.truncate(offset);
    shown.content.extend(answer.content.iter().cloned());
    follow_fields(shown, answer);
}

/// Append the part of `source` past `target`; copy it whole when `target`
/// is not a prefix of it.
fn grow(target: &mut String, source: &str) {
    match source.strip_prefix(target.as_str()) {
        Some(suffix) => target.push_str(suffix),
        None => source.clone_into(target),
    }
}

/// A work turn stopped at its granted time, on its way to be sent again as
/// the agent's final answer: its context and options, what the consumer
/// holds of its message, and the budget as it was left. The final answer
/// is sent with the stopped turn's context, without what streamed: a cut
/// response is no message a provider takes back (its thinking unsigned,
/// its tool call without a result), and the final answer's reserve was
/// counted for that context.
struct Stopped<O> {
    context: TranscriptContext,
    options: O,
    finale: Finale,
    opened: Opened,
    report: BudgetReport,
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

    /// What bounds the spend of this request with `options`; the final
    /// answer's time from the budget as last read and the agent's longest
    /// model request (B14).
    fn cost_facts(&self, options: &O) -> CostFacts<'_> {
        let model = &self.model;
        let budget_ms = self
            .gate
            .reports
            .borrow()
            .as_ref()
            .and_then(|report| report.limits.time_ms);
        CostFacts {
            cost: &model.cost,
            price_multiplier: options
                .service_tier()
                .and_then(|tier| service_tier_multiplier(model.into(), tier))
                .unwrap_or(1.0),
            output_extra: options.output_extra(model),
            max_output: self.max_output(),
            final_ms: final_time_ms(budget_ms, self.gate.longest_request_ms()),
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
        let (use_, keep, offered) = if agent_turn {
            self.gate.set_keep(own_keep);
            self.gate.step_started(now_millis());
            if let Some(smallest) = work.last() {
                *self
                    .gate
                    .turn
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner) = *smallest;
            }
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
        // What an agent turn asks again when it is stopped at a granted
        // time the deadline cut.
        let asked = agent_turn.then(|| offered.clone());
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
        let (granted, again) = match reserved {
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
                    if reservation.low {
                        let keep = self.gate.keep();
                        self.gate.tell(NoticeKind::Low, &report, || {
                            notices::low_text(&report, keep)
                        });
                    }
                }
                let again = asked
                    .filter(|offers| reservation.amount.time_ms < offers[reservation.index].time_ms)
                    .map(|offers| Again { keep, offers });
                let granted = Granted {
                    id: reservation.id,
                    amount: reservation.amount,
                    use_,
                    report,
                    context,
                };
                (granted, again)
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
                    again: None,
                };
                return self
                    .final_answer(context, options, &tokenizer, finale, Opened::No, |cap| {
                        notices::wrap_up_text(short, &report, cap)
                    })
                    .await;
            }
        };
        let turn = if agent_turn {
            Turn::Work(Finale {
                input,
                target,
                again,
            })
        } else {
            Turn::Side
        };
        if let Some(stopped) = self.send(granted, &tokenizer, options, turn).await {
            let Stopped {
                context,
                options,
                mut finale,
                opened,
                report,
            } = stopped;
            let (short, report) = self
                .stopped_short(&finale.target, finale.again.take(), report)
                .await;
            self.final_answer(context, options, &tokenizer, finale, opened, |cap| {
                notices::wrap_up_text(short, &report, cap)
            })
            .await;
        }
    }

    /// What the final answer of a work turn stopped at its granted time is
    /// told: the dimension the agent is short in and the budget. A turn
    /// whose granted time the deadline cut asks for its work `again`,
    /// which the ledger refuses for time: the agent is in `WrapUp`, short of
    /// time, before its final answer.
    async fn stopped_short(
        &self,
        target: &str,
        again: Option<Again>,
        report: BudgetReport,
    ) -> (&'static str, BudgetReport) {
        let time = BudgetDimension::Time.label();
        let Some(Again { keep, offers }) = again else {
            return (time, report);
        };
        let asked = self
            .gate
            .reserve(
                Use::Work,
                format!("model:{target}"),
                keep,
                offers,
                REQUEST_MIN_MS,
            )
            .await;
        match asked {
            Ok(Some(Reserved::Refused { refusal, report })) => {
                (notices::short_label(refusal, &report), report)
            }
            // Budget was added since the turn was granted: work fits again,
            // but the turn is cut. The grant goes back unspent.
            Ok(Some(Reserved::Granted {
                reservation,
                report,
            })) => {
                Held::start(&self.gate, reservation.id, reservation.amount, Use::Work)
                    .settle(BudgetAmounts::default())
                    .await;
                (time, self.gate.reports.borrow().clone().unwrap_or(report))
            }
            Ok(None) => (time, report),
            Err(error) => {
                tracing::warn!(%error, "the stopped turn's work was not asked again");
                (time, report)
            }
        }
    }

    /// Send the agent's turn as its final answer: the same context with
    /// `notice` (of the answer's output cap) as its last message, no tools,
    /// at most [`FINAL_CAP`] output tokens, reserved as the final answer
    /// from what the reserve kept, and told to the user as the wrap-up
    /// notice.
    async fn final_answer(
        self,
        context: TranscriptContext,
        mut options: O,
        tokenizer: &Tokenizer,
        finale: Finale,
        opened: Opened,
        notice: impl Fn(u64) -> String,
    ) {
        // The work it asked for was asked again, if at all, before.
        let Finale {
            input,
            target,
            again: _,
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
            .map(|cap| facts.amount(input, *cap, facts.final_ms))
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
        match answered {
            Ok(None) => self.pass(&context, options).await,
            Err(error) => self.refuse(notices::ledger_failed("the request was not sent", &error)),
            Ok(Some(Reserved::Refused { refusal, report })) => self.refuse(
                notices::request_refused(notices::short_label(refusal, &report)),
            ),
            Ok(Some(Reserved::Granted {
                reservation,
                report: granted,
            })) => {
                let cap = final_caps[reservation.index];
                let notice = notice(cap);
                self.gate
                    .tell(NoticeKind::WrapUp, &granted, || notice.clone());
                let mut messages = context.into_messages();
                messages.push(Message::User(UserMessage {
                    content: UserContent::Text(notice),
                    timestamp: now_millis(),
                }));
                options.disable_tools();
                options.stream_mut().max_tokens = Some(cap);
                let context = TranscriptContext::from_normalized_messages(messages);
                let granted = Granted {
                    id: reservation.id,
                    amount: reservation.amount,
                    use_: Use::Final,
                    report: granted,
                    context,
                };
                // A final answer is no work turn: it is never stopped into
                // another.
                self.send(granted, tokenizer, options, Turn::Final(opened))
                    .await;
            }
        }
    }

    /// Send a granted request, forward its events, and settle it once:
    /// a response at its usage, a deferred one when its fetch ends, a
    /// request its provider never started at one request, one that failed
    /// after it started at what the provider reported (whole when it
    /// reported nothing). A work turn stopped at its granted time ends
    /// nothing: it comes back as [`Stopped`], its streamed text and
    /// thinking closed.
    async fn send(
        &self,
        granted: Granted,
        tokenizer: &Tokenizer,
        mut options: O,
        mut turn: Turn,
    ) -> Option<Stopped<O>> {
        let Granted {
            id,
            amount,
            use_,
            report,
            context,
        } = granted;
        let model = &self.model;
        // A budget with a deadline stops the request at its granted time.
        let stop_after = report
            .deadline_ms
            .map(|_| Duration::from_millis(amount.time_ms));
        // The options a stopped work turn's final answer is sent with:
        // without this request's stop signal.
        let unstopped = match turn {
            Turn::Work(_) => Some(options.clone()),
            Turn::Side | Turn::Final(_) => None,
        };
        let stopper = AbortController::new();
        if stop_after.is_some() {
            let request = &mut options.stream_mut().request;
            request.signal = Some(match request.signal.take() {
                Some(caller) => AbortSignal::any(&[caller, stopper.signal()]),
                None => stopper.signal(),
            });
        }
        let held = Held::start(&self.gate, id, amount, use_);
        let sent = tokio::time::Instant::now();
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
        // Whether a content block reached the consumer, and which.
        let mut content = false;
        let mut seen = Seen::default();
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
                    match turn {
                        Turn::Final(Opened::Yes | Opened::Streamed(_)) => {}
                        Turn::Side | Turn::Work(_) | Turn::Final(Opened::No) => {
                            self.sink.push(AssistantMessageEvent::Start { partial });
                        }
                    }
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
                | AssistantMessageEvent::ToolCallEnd { .. } => {
                    content |= !matches!(event, AssistantMessageEvent::PromptProgress { .. });
                    match &mut turn {
                        Turn::Final(Opened::Streamed(streamed)) => {
                            self.sink.push(streamed.follow(event));
                        }
                        Turn::Side | Turn::Work(_) | Turn::Final(Opened::No | Opened::Yes) => {
                            seen.see(&event);
                            self.sink.push(event);
                        }
                    }
                }
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
                    return None;
                }
                (
                    DoneReason::Stop
                    | DoneReason::Length
                    | DoneReason::ToolUse
                    | DoneReason::Deferred,
                    _,
                ) => {
                    // One of the agent's own requests ended with its
                    // response: its final answer's time follows it (B14).
                    match &turn {
                        Turn::Work(_) | Turn::Final(_) => {
                            let ms = sent.elapsed().as_millis();
                            self.gate
                                .request_ended(u64::try_from(ms).unwrap_or(u64::MAX));
                        }
                        Turn::Side => {}
                    }
                    let message = match &turn {
                        Turn::Final(Opened::Streamed(streamed)) => streamed.finish(message),
                        Turn::Side | Turn::Work(_) | Turn::Final(Opened::No | Opened::Yes) => {
                            message
                        }
                    };
                    (
                        actual_spend(&message.usage),
                        Some(AssistantMessageEvent::Done { reason, message }),
                    )
                }
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
                    return match (turn, unstopped) {
                        // The turn is sent again as the final answer, from
                        // what the reserve kept, into the message the
                        // consumer holds.
                        (Turn::Work(finale), Some(options)) => {
                            let opened = match started {
                                Some(partial) if content => Opened::Streamed(Box::new(
                                    Streamed::cut(partial, seen, &self.sink),
                                )),
                                Some(_) => Opened::Yes,
                                None => Opened::No,
                            };
                            Some(Stopped {
                                context,
                                options,
                                finale,
                                opened,
                                report: self.gate.reports.borrow().clone().unwrap_or(report),
                            })
                        }
                        (Turn::Work(_) | Turn::Side | Turn::Final(_), _) => {
                            self.refuse(notices::REQUEST_STOPPED.to_owned());
                            None
                        }
                    };
                }
                (spend, last)
            }
        };
        held.settle(spend).await;
        if let Some(last) = last {
            self.sink.push(last);
        }
        self.sink.end(None);
        None
    }
}
