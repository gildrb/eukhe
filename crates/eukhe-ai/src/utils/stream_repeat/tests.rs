//! The repetition guard: its chunking of deltas into lines (the decision
//! on the chunks is the compiled core's, pinned by `laws/infer_guard.bend`),
//! and `Models` cutting a looping stream with a retryable
//! `stream_repeating` failure.

use eukhe_types::pi_ai::{AssistantContentBlock, Context, StopReason, TextContent};
use serde_json::json;

use super::{RepetitionCut, RepetitionGuard, MAX_CHUNK_BYTES};
use crate::models::{create_models, CreateModelsOptions, ModelsSimpleStreamOptions};
use crate::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_thinking, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use crate::types::SimpleStreamOptions;
use crate::utils::retry::{is_retryable_assistant_error, repeated_lines};
use crate::utils::stream_failure::RepeatedLines;

fn cut(chunks: u64, period: u32, line: &str) -> RepetitionCut {
    RepetitionCut {
        chunks,
        period,
        line: line.to_owned(),
    }
}

#[test]
fn a_line_is_a_chunk_only_once_its_newline_arrives() {
    let mut guard = RepetitionGuard::new(3);
    assert_eq!(guard.push(0, "ab"), None);
    assert_eq!(guard.push(0, "c\nabc\nab"), None);
    assert_eq!(guard.push(0, "c"), None);
    assert_eq!(guard.push(0, "\n"), Some(cut(3, 1, "abc")));
}

#[test]
fn blank_and_whitespace_lines_are_not_chunks() {
    let mut guard = RepetitionGuard::new(2);
    assert_eq!(guard.push(0, "x\n\n   \n\t\n"), None);
    assert_eq!(guard.push(0, "x\n"), Some(cut(2, 1, "x")));
}

#[test]
fn interleaved_blocks_keep_their_own_partial_lines_and_share_one_run() {
    let mut guard = RepetitionGuard::new(2);
    // Text (block 0) and thinking (block 1) interleave mid-line: each keeps
    // its partial line, and their complete lines count in arrival order.
    assert_eq!(guard.push(0, "lo"), None);
    assert_eq!(guard.push(1, "lo\n"), None);
    assert_eq!(guard.push(0, "op\n"), None);
    assert_eq!(guard.push(1, "loop\n"), Some(cut(3, 1, "loop")));
}

/// Regression (audit H3): a failover's sibling attempt opens with its own
/// `start`, and the guard counted the failed attempt's lines with the
/// sibling's, so a preamble both attempts wrote read as a loop.
#[test]
fn a_new_attempt_restarts_the_guard() {
    use crate::types::ProviderRequestOptions;
    use eukhe_types::pi_ai::AssistantMessageEvent;

    let mut request: ProviderRequestOptions = ProviderRequestOptions {
        stream_repeat_limit: Some(3),
        ..ProviderRequestOptions::default()
    };
    let mut repeat = super::StreamRepeat::arm(&mut request);
    let message = faux_assistant_message("", FauxAssistantMessageOptions::default());
    let start = AssistantMessageEvent::Start {
        partial: message.clone().into(),
    };
    let line = AssistantMessageEvent::TextDelta {
        content_index: 0,
        delta: "Reading the files first.\n".to_owned(),
        partial: message.into(),
    };
    let cuts: Vec<bool> = [&start, &line, &line, &start, &line, &line]
        .into_iter()
        .map(|event| repeat.watch(event).is_some())
        .collect();
    assert_eq!(cuts, [false; 6]);
}

/// A loop with no newline (`abab…`) is cut into chunks of
/// `MAX_CHUNK_BYTES`, so the guard still cuts it, and it never buffers
/// more than one chunk.
#[test]
fn a_loop_with_no_newline_is_cut_in_bounded_chunks() {
    let mut guard = RepetitionGuard::new(3);
    let mut buffered = 0;
    let cut_at = (0..10_000).find_map(|delta| {
        let cut = guard.push(0, "ababababab");
        buffered = buffered.max(guard.partial[&0].len());
        cut.map(|cut| (delta, cut))
    });
    assert_eq!(
        (cut_at, buffered <= MAX_CHUNK_BYTES),
        (Some((1228, cut(3, 1, &"ab".repeat(2048)))), true)
    );
}

/// A long line ends its chunks on character boundaries.
#[test]
fn a_long_line_is_chunked_on_character_boundaries() {
    let mut guard = RepetitionGuard::new(2);
    let euros = "€".repeat(MAX_CHUNK_BYTES / 3);
    assert_eq!(
        guard.push(0, &format!("{euros}{euros}€")),
        Some(cut(2, 1, &euros))
    );
}

/// The start of a thinking block that qwen3.8-27b (openai-completions)
/// streamed in a real session, up to its loop.
const OBSERVED_START: &str = "\
The user is asking where they can find deep cybersecurity circles/communities to learn about this field — forums like Twitter where recommendations are shared and the people there actually know what they're talking about.

This is a knowledge question. I can answer from my own knowledge, but I could also verify current resources. Let me think about what I know:

Deep cybersecurity circles:

1. **Twitter/X** — the \"infosec Twitter\" scene is real. Notable accounts:
   - @mally (MalwareLab)
   - @TheTechromancer (Johanna Amann)
   - @GossiTheDog (Gossi The Dog)
   - @hacks4pancakes (Hannah)
   - @mikeborelli
   - @TheTechromancer
   - @0x69
   - @hacks4pancakes
   - @mitchellh (not security)
   - @GossiTheDog
   - @TheTechromancer
   - @hacks4pancakes
   - @mally
   - @0x69
";

/// The block of 7 lines that the observed thinking then repeated.
const OBSERVED_CYCLE: &str = "   - @hacks4pancakes
   - @mitchellh
   - @GossiTheDog
   - @TheTechromancer
   - @hacks4pancakes
   - @mally
   - @0x69
";

/// The whole observed thinking: 23,957 characters, 1,359 non-blank lines,
/// until the stream ended with stop reason `stop` and no text.
fn observed_thinking() -> String {
    format!(
        "{OBSERVED_START}{}   - @hacks4pancakes\n   - @mitchellh\n   - @GossiTheDog\n   - @The",
        OBSERVED_CYCLE.repeat(191)
    )
}

/// The observed loop is a cycle of 7 lines in which no line comes twice in
/// a row, so the former rule (one line `k` times in a row) never cut it:
/// the model looped for 1,359 lines. The default window of 64 lines takes
/// periods up to 16: the 77th line completes 64 lines of period 7.
#[test]
fn the_observed_thinking_loop_is_cut_at_its_77th_line() {
    let thinking = observed_thinking();
    assert_eq!(thinking.chars().count(), 23_957);
    let mut guard = RepetitionGuard::new(super::DEFAULT_STREAM_REPEAT_LIMIT);
    // The deltas of a stream: a few characters each.
    let deltas: Vec<String> = thinking
        .chars()
        .collect::<Vec<_>>()
        .chunks(5)
        .map(|delta| delta.iter().collect())
        .collect();
    let got = deltas.iter().find_map(|delta| guard.push(0, delta));
    assert_eq!(got, Some(cut(77, 7, "   - @GossiTheDog")));
}

fn hello() -> Context {
    serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "hi", "timestamp": 0 }],
    }))
    .expect("context")
}

fn limit(limit: u32) -> ModelsSimpleStreamOptions {
    let mut options = SimpleStreamOptions::default();
    options.stream.request.stream_repeat_limit = Some(limit);
    options.into()
}

#[tokio::test]
async fn a_looping_stream_is_cut_with_a_retryable_repeating_failure() {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    // Thinking and text lines count in one run: two from the thinking and
    // the first of the text make the third.
    faux.set_responses(vec![faux_assistant_message(
        vec![
            faux_thinking("step\nstep\n"),
            faux_text("step\n".repeat(50)),
        ],
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let model = faux.get_model();
    let message = models.complete_simple(&model, hello(), limit(3)).await;
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.error_message.as_deref(),
        Some("Provider stream repeating: the same line 3 times in a row: \"step\"")
    );
    let diagnostics = serde_json::to_value(message.diagnostics.as_ref().expect("diagnostics"))
        .expect("diagnostics JSON");
    assert_eq!(diagnostics[0]["type"], "provider_stream_failure");
    assert_eq!(diagnostics[0]["details"]["kind"], "stream_repeating");
    assert!(is_retryable_assistant_error(&message));
    assert_eq!(
        repeated_lines(&message),
        Some(RepeatedLines {
            period: 1,
            line: "step".to_owned()
        })
    );
}

/// The observed thinking loop, streamed with the default settings, ends
/// with a retryable repeating failure that names the cycle.
#[tokio::test]
async fn the_observed_thinking_loop_fails_as_repeating_by_default() {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    faux.set_responses(vec![faux_assistant_message(
        vec![faux_thinking(observed_thinking())],
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let model = faux.get_model();
    let message = models
        .complete_simple(&model, hello(), SimpleStreamOptions::default().into())
        .await;
    assert_eq!(
        (
            message.stop_reason,
            message.error_message.as_deref(),
            is_retryable_assistant_error(&message),
            repeated_lines(&message)
        ),
        (
            StopReason::Error,
            Some(
                "Provider stream repeating: a cycle of 7 lines repeated over the last 64 \
                 lines, ending with \"   - @GossiTheDog\""
            ),
            true,
            Some(RepeatedLines {
                period: 7,
                line: "   - @GossiTheDog".to_owned()
            })
        )
    );
}

#[tokio::test]
async fn a_stream_that_never_repeats_a_line_k_times_passes_untouched() {
    let faux = faux_provider(RegisterFauxProviderOptions::default());
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let text = "a\nb\na\n\n\nb\nb\nc";
    faux.set_responses(vec![faux_assistant_message(
        text,
        FauxAssistantMessageOptions::default(),
    )
    .into()]);
    let model = faux.get_model();
    let message = models.complete_simple(&model, hello(), limit(3)).await;
    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(
        message.content,
        vec![AssistantContentBlock::Text(TextContent::new(text))]
    );
}

#[test]
fn a_long_repeated_line_is_shown_cut_in_the_failure() {
    let line = "x".repeat(100);
    let failure = super::stream_repeating_failure(64, 1, &line);
    assert_eq!(
        failure.message,
        format!(
            "Provider stream repeating: the same line 64 times in a row: \"{}…\"",
            "x".repeat(80)
        )
    );
}
