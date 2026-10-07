//! Live cases needing a `ChatGPT` Codex OAuth access token in
//! `OPENAI_CODEX_API_KEY`: `openai-codex-cache-affinity-e2e.test.ts` and
//! the `codex-websocket-cached-probe.ts` script (an ignored test here; its
//! CLI flags become `CODEX_PROBE_*` environment variables).

use std::time::Instant;

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, JsonObject, JsonValue, Message, StopReason, Transport,
};
use serde_json::json;

use super::super::{
    close_openai_codex_websocket_sessions, get_openai_codex_websocket_debug_stats,
    reset_openai_codex_websocket_debug_stats, stream,
};
use super::support::{context, isolate, message, user};
use crate::providers::all::get_builtin_model;
use crate::types::{ProviderStreamOptions, StreamOptions};

fn api_key() -> String {
    std::env::var("OPENAI_CODEX_API_KEY").expect("OPENAI_CODEX_API_KEY")
}

fn text_of(message: &AssistantMessage) -> String {
    message
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_owned()
}

#[tokio::test]
#[ignore = "needs OPENAI_CODEX_API_KEY; run with --ignored"]
async fn handles_sse_requests_with_aligned_cache_affinity_identifiers() {
    let _isolation = isolate().await;
    let model = get_builtin_model("openai-codex", "gpt-5.5").expect("catalog model");
    let mut options = StreamOptions {
        session_id: Some("0195d6e4-4cf9-7f44-a2d8-f8f7f49ee9d3".to_owned()),
        transport: Some(Transport::Sse),
        ..StreamOptions::default()
    };
    options.request.api_key = Some(api_key());

    let response = stream(
        &model,
        &context(
            Some("You are a helpful assistant. Reply exactly as requested."),
            vec![user("Reply with exactly: cache affinity e2e success", 1)],
            None,
        ),
        ProviderStreamOptions {
            stream: options,
            extra: JsonObject::new(),
        },
    )
    .result()
    .await;

    assert_ne!(
        response.stop_reason,
        StopReason::Error,
        "{:?}",
        response.error_message
    );
    assert_eq!(response.error_message, None);
    assert!(text_of(&response).contains("cache affinity e2e success"));
}

fn env_or(name: &str, default: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| default.to_owned())
}

fn build_prompt(turn: u32) -> String {
    let marker = format!("TURN-{turn:02}-MARKER-{}", (turn * 17 + 13) % 97);
    let mut lines = vec![
        "This is an automated OpenAI Codex Responses websocket cache probe.".to_owned(),
        format!(
            "Task for turn {turn}: call deterministic_probe exactly once before your final answer."
        ),
        format!("Use tool arguments: turn={turn}, marker={marker}"),
        format!("After the tool result arrives, reply exactly: TURN {turn} OK {marker}"),
        "The following repeated block is intentional benchmark padding.".to_owned(),
    ];
    for i in 1..=180 {
        lines.push(format!(
            "Turn {turn} synthetic record {i:03}: alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu nu xi omicron pi rho sigma tau upsilon phi chi psi omega."
        ));
    }
    lines.join("\n")
}

/// Port of `codex-websocket-cached-probe.ts`: a tool loop over N turns
/// printing per-request usage and WebSocket debug stats.
#[tokio::test]
#[ignore = "needs OPENAI_CODEX_API_KEY; run with --ignored --nocapture"]
#[allow(clippy::too_many_lines)] // One probe script.
async fn codex_websocket_cached_probe() {
    let _isolation = isolate().await;
    let turns: u32 = env_or("CODEX_PROBE_TURNS", "20")
        .parse()
        .expect("CODEX_PROBE_TURNS");
    let transport = Transport::parse(&env_or("CODEX_PROBE_TRANSPORT", "websocket-cached"))
        .expect("CODEX_PROBE_TRANSPORT: sse | websocket | websocket-cached | auto");
    let max_tokens: u64 = env_or("CODEX_PROBE_MAX_TOKENS", "64")
        .parse()
        .expect("CODEX_PROBE_MAX_TOKENS");
    let reasoning = env_or("CODEX_PROBE_REASONING", "low");
    let session_id = std::env::var("CODEX_PROBE_SESSION_ID")
        .unwrap_or_else(|_| format!("pi-ai-codex-ws-cached-probe-{}", crate::utils::now_ms()));

    let mut model =
        get_builtin_model("openai-codex", "gpt-5.5").expect("Model openai-codex/gpt-5.5 not found");
    model.max_tokens = max_tokens;
    let api_key = api_key();
    let tools = json!([{
        "name": "deterministic_probe",
        "description": "Mandatory benchmark tool. Call exactly once with the turn and marker from the user prompt.",
        "parameters": {
            "type": "object",
            "properties": { "turn": { "type": "number" }, "marker": { "type": "string" } },
            "required": ["turn", "marker"],
        },
    }]);
    let mut messages: Vec<Message> = Vec::new();
    let system_prompt = "You are participating in a benchmark. For each benchmark turn, call deterministic_probe exactly once before the final answer. Keep final answers minimal.";
    let mut elapsed: Vec<f64> = Vec::new();
    reset_openai_codex_websocket_debug_stats(Some(&session_id));

    println!("provider openai-codex, model gpt-5.5");
    println!("sessionId {session_id}");
    println!("turns {turns}, transport {transport}, reasoning {reasoning}, maxTokens {max_tokens}");
    println!();

    for turn in 1..=turns {
        messages.push(user(&build_prompt(turn), crate::utils::now_ms()));
        let before = get_openai_codex_websocket_debug_stats(&session_id).unwrap_or_default();
        let started = Instant::now();
        let mut requests = 0;
        let mut tool_results = 0;
        let (mut input, mut output, mut cache_read, mut cache_write) = (0, 0, 0, 0);
        let final_text = loop {
            requests += 1;
            let mut options = StreamOptions {
                session_id: Some(session_id.clone()),
                transport: Some(transport),
                max_tokens: Some(max_tokens),
                ..StreamOptions::default()
            };
            options.request.api_key = Some(api_key.clone());
            let mut extra = JsonObject::new();
            extra.insert(
                "reasoningEffort".into(),
                JsonValue::String(reasoning.clone()),
            );
            let result = stream(
                &model,
                &context(Some(system_prompt), messages.clone(), Some(tools.clone())),
                ProviderStreamOptions {
                    stream: options,
                    extra,
                },
            )
            .result()
            .await;
            messages.push(Message::Assistant(result.clone()));
            input += result.usage.input;
            output += result.usage.output;
            cache_read += result.usage.cache_read;
            cache_write += result.usage.cache_write;
            let tool_calls: Vec<_> = result
                .content
                .iter()
                .filter_map(|block| match block {
                    AssistantContentBlock::ToolCall(call) => Some(call.clone()),
                    _ => None,
                })
                .collect();
            println!(
                "turn {turn:02}.{requests} | stop {} | in {} | out {} | cache {}/{} | tools {}",
                result.stop_reason,
                result.usage.input,
                result.usage.output,
                result.usage.cache_read,
                result.usage.cache_write,
                tool_calls.len()
            );
            assert!(
                !matches!(result.stop_reason, StopReason::Error | StopReason::Aborted),
                "{}",
                result.error_message.as_deref().map_or_else(
                    || format!("request failed on turn {turn}.{requests}"),
                    str::to_owned
                )
            );
            if tool_calls.is_empty() {
                break text_of(&result);
            }
            for call in tool_calls {
                let arguments = serde_json::to_string(&call.arguments).expect("serializable");
                messages.push(message(json!({
                    "role": "toolResult",
                    "toolCallId": call.id,
                    "toolName": call.name,
                    "content": [{ "type": "text", "text": format!("deterministic_probe_result {arguments} fixed=OK") }],
                    "details": { "fixed": "OK" },
                    "isError": false,
                    "timestamp": crate::utils::now_ms(),
                })));
                tool_results += 1;
            }
            assert!(requests <= 4, "Too many requests for turn {turn}");
        };

        let elapsed_ms = started.elapsed().as_secs_f64() * 1000.0;
        elapsed.push(elapsed_ms);
        let stat_line = get_openai_codex_websocket_debug_stats(&session_id).map_or_else(
            || "ws none".to_owned(),
            |after| {
                format!(
                    "ws requests {} | new/reused {}/{} | cached {} | store {} | full/delta {}/{}",
                    after.requests - before.requests,
                    after.connections_created - before.connections_created,
                    after.connections_reused - before.connections_reused,
                    after.cached_context_requests - before.cached_context_requests,
                    after.store_true_requests - before.store_true_requests,
                    after.full_context_requests - before.full_context_requests,
                    after.delta_requests - before.delta_requests,
                )
            },
        );
        let final_json = serde_json::to_string(&final_text).expect("serializable");
        println!(
            "turn {turn:02} agg | elapsed {:.1}s | assistant {requests} | toolResults {tool_results} | in {input} | out {output} | cache {cache_read}/{cache_write} | {stat_line} | final {}",
            elapsed_ms / 1000.0,
            final_json.chars().take(80).collect::<String>()
        );
    }

    let stats = get_openai_codex_websocket_debug_stats(&session_id);
    let mut sorted = elapsed.clone();
    sorted.sort_by(f64::total_cmp);
    let percentile = |p: f64| {
        if sorted.is_empty() {
            return 0.0;
        }
        // Small positive indexes.
        #[allow(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            clippy::cast_precision_loss
        )]
        let index = ((p / 100.0 * sorted.len() as f64).ceil() as usize).saturating_sub(1);
        sorted[index.min(sorted.len() - 1)]
    };
    let total: f64 = elapsed.iter().sum();
    #[allow(clippy::cast_precision_loss)] // A handful of turns.
    let average = total / elapsed.len().max(1) as f64;
    println!();
    println!(
        "timing | turns {} | total {:.1}s | avg {:.2}s | p50 {:.2}s | p95 {:.2}s | max {:.2}s",
        elapsed.len(),
        total / 1000.0,
        average / 1000.0,
        percentile(50.0) / 1000.0,
        percentile(95.0) / 1000.0,
        sorted.last().copied().unwrap_or_default() / 1000.0
    );
    let stats_text = |f: &dyn Fn(&super::super::OpenAICodexWebSocketDebugStats) -> String,
                      fallback: &str| {
        stats.as_ref().map_or_else(|| fallback.to_owned(), f)
    };
    println!(
        "transport summary | requested {transport} | observed {} | storeTrue {} | full/delta {} | connections created/reused {} | lastPreviousResponseId {}",
        if stats.as_ref().is_some_and(|stats| stats.requests > 0) { "websocket" } else { "sse/no-websocket" },
        stats_text(&|s| format!("{}/{}", s.store_true_requests, s.requests), "0/0"),
        stats_text(&|s| format!("{}/{}", s.full_context_requests, s.delta_requests), "0/0"),
        stats_text(&|s| format!("{}/{}", s.connections_created, s.connections_reused), "0/0"),
        stats
            .as_ref()
            .and_then(|stats| stats.last_previous_response_id.clone())
            .unwrap_or_else(|| "n/a".to_owned()),
    );
    close_openai_codex_websocket_sessions(Some(&session_id));
}
