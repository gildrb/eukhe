//! Every provider row of a model collection behind a budget gate
//! (spec/README.md B1, B4): its chat streams ([`super::gate`]), the fetch
//! and cancel of its deferred responses, its classifier and its image
//! generation. A row registered on the collection later passes the gate
//! too ([`Models::layer_new_providers`]).

use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::api::{
    CancelDeferredFn, ClassifyFn, FetchDeferredFn, GenerateImagesFn, StreamFn, StreamSimpleFn,
};
use eukhe_ai::models::{Models, Provider};
use eukhe_ai::utils::context_tokens::model_tokenizer;
use eukhe_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_budget::{
    actual_spend, worst_case_cost_micros, RequestBound, Reserved, Use, REQUEST_MIN_MS,
};
use eukhe_types::budget::{BudgetAmounts, BUDGET_AMOUNT_MAX};
use eukhe_types::pi_ai::{
    AssistantImages, AssistantMessageEvent, ClassifierResult, ClassifierStopReason, DoneReason,
    ImagesStopReason, IndexMap, Model, Partial, TranscriptContext, Usage,
};
use futures::{FutureExt as _, StreamExt as _};

use super::gate::{deferred_key, failed_spend, GatedOptions, Request, Row, DEFAULT_DEADLINE_MS};
use super::notices;
use super::BudgetGate;
use crate::durable::rlm::now_millis;

/// The output a classifier answer is bounded by: its answers are labels
/// and scores.
const CLASSIFY_OUTPUT_CAP: u64 = 1024;

/// The stream of one chat request of `gate`'s agent: `inner`'s own stream
/// when the session has no budget (one `stat`) and no limit of the agent's
/// run makes its turn the final answer, else the gated request's. Must be
/// called inside a tokio runtime (the provider contract runs every request
/// on one).
fn gated<O: GatedOptions>(
    gate: &Arc<BudgetGate>,
    inner: &Row<O>,
    model: &Model,
    context: &TranscriptContext,
    options: O,
) -> AssistantMessageEventStream {
    if !gate.ledger.exists() && gate.wrap().is_none() {
        return inner(model, context, options);
    }
    let outer = AssistantMessageEventStream::new();
    let request = Request {
        gate: Arc::clone(gate),
        model: model.clone(),
        inner: Arc::clone(inner),
        sink: outer.clone(),
    };
    tokio::spawn(request.run(context.clone(), options));
    outer
}

/// `provider` with every operation that reaches its service behind `gate`.
fn gate_provider(gate: &Arc<BudgetGate>, mut provider: Provider) -> Provider {
    let stream: StreamFn = {
        let gate = Arc::clone(gate);
        let inner = provider.stream;
        Arc::new(move |model, context, options| gated(&gate, &inner, model, context, options))
    };
    let stream_simple: StreamSimpleFn = {
        let gate = Arc::clone(gate);
        let inner = provider.stream_simple;
        Arc::new(move |model, context, options| gated(&gate, &inner, model, context, options))
    };
    provider.stream = stream;
    provider.stream_simple = stream_simple;
    provider.fetch_deferred = provider
        .fetch_deferred
        .map(|inner| gate_fetch_deferred(Arc::clone(gate), inner));
    provider.cancel_deferred = provider
        .cancel_deferred
        .map(|inner| gate_cancel_deferred(Arc::clone(gate), inner));
    provider.classify = provider
        .classify
        .map(|inner| gate_classify(Arc::clone(gate), inner));
    provider.generate_images = provider
        .generate_images
        .map(|inner| gate_generate_images(Arc::clone(gate), inner));
    provider
}

/// Gate every provider row of `models` (re-wrapped in place), and every
/// provider registered on it later: each request of the collection passes
/// one reservation and one settlement of `gate`'s ledger. Install it
/// before the provider admission gate, and on every other collection the
/// agent sends requests through.
pub fn wrap_models_with_budget(models: &Models, gate: &Arc<BudgetGate>) {
    for provider in models.get_providers() {
        models.set_provider(gate_provider(gate, (*provider).clone()));
    }
    let gate = Arc::clone(gate);
    models.layer_new_providers(Arc::new(move |provider| gate_provider(&gate, provider)));
}

/// A deferred response's fetch settles the reservation its request left
/// open: at its usage when the response is done, kept open while it is
/// still deferred, and on a failure at what the provider reported (whole
/// when it reported nothing). A handle this process holds no reservation
/// for (the session opened again, which settled it at what it held; or no
/// budget) fetches as it came.
fn gate_fetch_deferred(gate: Arc<BudgetGate>, inner: FetchDeferredFn) -> FetchDeferredFn {
    Arc::new(move |model, handle, options| {
        let key = deferred_key(handle);
        let Some(held) = gate.take_deferred(&key) else {
            return inner(model, handle, options);
        };
        let outer = AssistantMessageEventStream::new();
        let sink = outer.clone();
        let mut events = inner(model, handle, options).events();
        let gate = Arc::clone(&gate);
        let model = model.clone();
        tokio::spawn(async move {
            let mut started: Option<Partial> = None;
            let (spend, last) = loop {
                let Some(event) = events.next().await else {
                    break (None, None);
                };
                match event {
                    AssistantMessageEvent::Done { reason, message } => match reason {
                        DoneReason::Deferred => {
                            gate.park_deferred(key, held);
                            sink.push(AssistantMessageEvent::Done { reason, message });
                            sink.end(None);
                            return;
                        }
                        DoneReason::Stop | DoneReason::Length | DoneReason::ToolUse => {
                            break (
                                Some(actual_spend(&message.usage)),
                                Some(AssistantMessageEvent::Done { reason, message }),
                            );
                        }
                    },
                    AssistantMessageEvent::Error { .. } => break (None, Some(event)),
                    AssistantMessageEvent::Start { partial } => {
                        started = Some(partial.clone());
                        sink.push(AssistantMessageEvent::Start { partial });
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
                    | AssistantMessageEvent::ToolCallEnd { .. } => sink.push(event),
                }
            };
            let spend = spend.unwrap_or_else(|| {
                // What streamed: the live message, else the error's own.
                let error = match &last {
                    Some(AssistantMessageEvent::Error { error, .. }) => Some(error),
                    Some(_) | None => None,
                };
                let streamed = started
                    .map(|partial| partial.snapshot())
                    .or_else(|| error.cloned());
                let reported: Usage = error.map_or_else(
                    || {
                        streamed
                            .as_ref()
                            .map_or_else(Usage::default, |streamed| streamed.usage)
                    },
                    |error| error.usage,
                );
                match streamed {
                    Some(streamed) => failed_spend(
                        &model.cost,
                        &model_tokenizer(&model),
                        &reported,
                        &streamed,
                        held.full,
                    ),
                    // The stream ended with no event: nothing is known.
                    None => held.full,
                }
            });
            held.settle(spend).await;
            if let Some(last) = last {
                sink.push(last);
            }
            sink.end(None);
        });
        outer
    })
}

/// A cancelled deferred response settles its open reservation whole: what
/// the provider did with it is not known.
fn gate_cancel_deferred(gate: Arc<BudgetGate>, inner: CancelDeferredFn) -> CancelDeferredFn {
    Arc::new(move |model, handle, options| {
        let held = gate.take_deferred(&deferred_key(handle));
        let cancelled = inner(model, handle, options);
        async move {
            let result = cancelled.await;
            if let Some(held) = held {
                let full = held.full;
                held.settle(full).await;
            }
            result
        }
        .boxed()
    })
}

/// What a request that is no chat request reserves and how long it may
/// run: a side request (spec/README.md B6) of the agent, its worst case
/// `bound` and no model request (a side request is no turn of the agent);
/// `None` without a budget. `Err` is the refusal text.
async fn reserve_other(
    gate: &Arc<BudgetGate>,
    label: String,
    bound: BudgetAmounts,
) -> Result<Option<(super::Held, Option<Duration>)>, String> {
    let reserved = gate
        .reserve(
            Use::Side,
            label,
            gate.keep(),
            vec![BudgetAmounts {
                time_ms: DEFAULT_DEADLINE_MS,
                requests: 0,
                ..bound
            }],
            REQUEST_MIN_MS,
        )
        .await;
    match reserved {
        Ok(None) => Ok(None),
        Err(error) => Err(notices::ledger_failed("the request was not sent", &error)),
        Ok(Some(Reserved::Refused { refusal, report })) => Err(notices::request_refused(
            notices::short_label(refusal, &report),
        )),
        Ok(Some(Reserved::Granted {
            reservation,
            report,
        })) => Ok(Some((
            super::Held::start(gate, reservation.id, reservation.amount),
            report
                .deadline_ms
                .map(|_| Duration::from_millis(reservation.amount.time_ms)),
        ))),
    }
}

/// A classifier request reserves its worst case (its whole context window
/// in, [`CLASSIFY_OUTPUT_CAP`] out) and settles at its usage (whole when it
/// reports none). A refused one answers an error without reaching the
/// service.
fn gate_classify(gate: Arc<BudgetGate>, inner: ClassifyFn) -> ClassifyFn {
    Arc::new(move |model, context, options| {
        if !gate.ledger.exists() {
            return inner(model, context, options);
        }
        let gate = Arc::clone(&gate);
        let inner = Arc::clone(&inner);
        let model = model.clone();
        let context = context.clone();
        async move {
            let bound = BudgetAmounts {
                cost_micros: worst_case_cost_micros(
                    &model.cost,
                    RequestBound {
                        input_tokens: model.context_window,
                        output_cap: CLASSIFY_OUTPUT_CAP,
                        price_multiplier: 1.0,
                    },
                ),
                tokens: model.context_window.saturating_add(CLASSIFY_OUTPUT_CAP),
                ..BudgetAmounts::default()
            };
            let refused = |text: String| ClassifierResult {
                api: model.api.clone(),
                provider: model.provider.clone(),
                model: model.id.clone(),
                answers: IndexMap::new(),
                usage: None,
                stop_reason: ClassifierStopReason::Error,
                error_message: Some(text),
                timestamp: now_millis(),
            };
            let label = format!("classify:{}/{}", model.provider, model.id);
            let (held, stop_after) = match reserve_other(&gate, label, bound).await {
                Ok(None) => return inner(&model, &context, options).await,
                Ok(Some(granted)) => granted,
                Err(text) => return refused(text),
            };
            let call = inner(&model, &context, options);
            let result = match stop_after {
                None => call.await,
                Some(after) => {
                    let Ok(result) = tokio::time::timeout(after, call).await else {
                        let full = held.full;
                        held.settle(full).await;
                        return refused(notices::REQUEST_STOPPED.to_owned());
                    };
                    result
                }
            };
            let spend = result.usage.as_ref().map_or(held.full, actual_spend);
            held.settle(spend).await;
            result
        }
        .boxed()
    })
}

/// An image request has no bound a price table gives: it fits only a
/// budget that limits neither money nor tokens (it reserves their
/// largest), and settles at its usage. A refused one answers an error
/// without reaching the service.
fn gate_generate_images(gate: Arc<BudgetGate>, inner: GenerateImagesFn) -> GenerateImagesFn {
    Arc::new(move |model, context, options| {
        if !gate.ledger.exists() {
            return inner(model, context, options);
        }
        let gate = Arc::clone(&gate);
        let inner = Arc::clone(&inner);
        let model = model.clone();
        let context = context.clone();
        async move {
            let bound = BudgetAmounts {
                cost_micros: BUDGET_AMOUNT_MAX,
                tokens: BUDGET_AMOUNT_MAX,
                ..BudgetAmounts::default()
            };
            let refused = |text: String| AssistantImages {
                api: model.api.clone(),
                provider: model.provider.clone(),
                model: model.id.clone(),
                output: Vec::new(),
                response_id: None,
                usage: None,
                stop_reason: ImagesStopReason::Error,
                error_message: Some(text),
                timestamp: now_millis(),
            };
            let label = format!("images:{}/{}", model.provider, model.id);
            let (held, stop_after) = match reserve_other(&gate, label, bound).await {
                Ok(None) => return inner(&model, &context, options).await,
                Ok(Some(granted)) => granted,
                Err(text) => return refused(text),
            };
            let call = inner(&model, &context, options);
            let result = match stop_after {
                None => call.await,
                Some(after) => {
                    let Ok(result) = tokio::time::timeout(after, call).await else {
                        let full = held.full;
                        held.settle(full).await;
                        return refused(notices::REQUEST_STOPPED.to_owned());
                    };
                    result
                }
            };
            let spend = result.usage.as_ref().map_or(held.full, actual_spend);
            held.settle(spend).await;
            result
        }
        .boxed()
    })
}
