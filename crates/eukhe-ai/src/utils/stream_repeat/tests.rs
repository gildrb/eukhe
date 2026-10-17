//! The repetition guard: its chunking of deltas into lines, its agreement
//! with model `guard(xs, k)` (`bend/infer.bend` §4), and `Models` cutting a
//! looping stream with a retryable `stream_repeating` failure.

use eukhe_types::pi_ai::{AssistantContentBlock, Context, StopReason, TextContent};
use serde_json::json;

use super::{RepetitionCut, RepetitionGuard, MAX_CHUNK_BYTES};
use crate::models::{create_models, CreateModelsOptions, ModelsSimpleStreamOptions};
use crate::providers::faux::{
    faux_assistant_message, faux_provider, faux_text, faux_thinking, FauxAssistantMessageOptions,
    RegisterFauxProviderOptions,
};
use crate::types::SimpleStreamOptions;
use crate::utils::retry::is_retryable_assistant_error;

fn cut(chunks: u64, line: &str) -> RepetitionCut {
    RepetitionCut {
        chunks,
        line: line.to_owned(),
    }
}

#[test]
fn a_line_is_a_chunk_only_once_its_newline_arrives() {
    let mut guard = RepetitionGuard::new(3);
    assert_eq!(guard.push(0, "ab"), None);
    assert_eq!(guard.push(0, "c\nabc\nab"), None);
    assert_eq!(guard.push(0, "c"), None);
    assert_eq!(guard.push(0, "\n"), Some(cut(3, "abc")));
}

#[test]
fn blank_and_whitespace_lines_are_not_chunks() {
    let mut guard = RepetitionGuard::new(2);
    assert_eq!(guard.push(0, "x\n\n   \n\t\n"), None);
    assert_eq!(guard.push(0, "x\n"), Some(cut(2, "x")));
}

#[test]
fn a_different_line_restarts_the_run() {
    let mut guard = RepetitionGuard::new(3);
    assert_eq!(guard.push(0, "a\na\nb\na\na\n"), None);
    assert_eq!(guard.push(0, "a\n"), Some(cut(6, "a")));
}

#[test]
fn interleaved_blocks_keep_their_own_partial_lines_and_share_one_run() {
    let mut guard = RepetitionGuard::new(2);
    // Text (block 0) and thinking (block 1) interleave mid-line: each keeps
    // its partial line, and their complete lines count in arrival order.
    assert_eq!(guard.push(0, "lo"), None);
    assert_eq!(guard.push(1, "lo\n"), None);
    assert_eq!(guard.push(0, "op\n"), None);
    assert_eq!(guard.push(1, "loop\n"), Some(cut(3, "loop")));
}

#[test]
fn a_limit_of_at_most_one_cuts_at_the_first_chunk() {
    for limit in [0, 1] {
        let mut guard = RepetitionGuard::new(limit);
        assert_eq!(guard.push(0, "partial"), None);
        assert_eq!(guard.push(0, "\nnext\n"), Some(cut(1, "partial")));
    }
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
        (Some((1228, cut(3, &"ab".repeat(2048)))), true)
    );
}

/// A long line ends its chunks on character boundaries.
#[test]
fn a_long_line_is_chunked_on_character_boundaries() {
    let mut guard = RepetitionGuard::new(2);
    let euros = "€".repeat(MAX_CHUNK_BYTES / 3);
    assert_eq!(
        guard.push(0, &format!("{euros}{euros}€")),
        Some(cut(2, &euros))
    );
}

/// Model `Cut`.
#[derive(Debug, PartialEq)]
enum Cut {
    Whole,
    CutAt(u64),
}

/// Model `guard(xs, k)`, transcribed: `guard.go` with `cut.at` and
/// `run.at`.
fn model_guard(xs: &[u32], k: u32) -> Cut {
    let run_at = |same: bool, run: u32| if same { 1 + run } else { 1 };
    let cut_at = |xs: &[u32], prev: u32, run: u32| match xs.first() {
        None => false,
        Some(x) => k <= run_at(*x == prev, run),
    };
    let (mut prev, mut run, mut n) = (0, 0, 0);
    let mut hit = cut_at(xs, prev, run);
    let mut rest = xs;
    while let Some((x, tail)) = rest.split_first() {
        if hit {
            return Cut::CutAt(1 + n);
        }
        run = run_at(*x == prev, run);
        prev = *x;
        n += 1;
        rest = tail;
        hit = cut_at(rest, prev, run);
    }
    Cut::Whole
}

/// Every chunk sequence over three chunk values up to length 6, against
/// every limit up to 4: the guard fed one line per chunk cuts exactly
/// where the model does.
#[test]
fn the_guard_cuts_where_the_model_does() {
    for length in 0..=6u32 {
        for code in 0..3u32.pow(length) {
            let xs: Vec<u32> = (0..length).map(|at| code / 3u32.pow(at) % 3).collect();
            for k in 0..=4 {
                let mut guard = RepetitionGuard::new(k);
                let got = xs
                    .iter()
                    .find_map(|x| guard.push(0, &format!("{x}\n")))
                    .map_or(Cut::Whole, |cut| Cut::CutAt(cut.chunks));
                assert_eq!(got, model_guard(&xs, k), "xs {xs:?}, k {k}");
            }
        }
    }
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
    let failure = super::stream_repeating_failure(64, &line);
    assert_eq!(
        failure.message,
        format!(
            "Provider stream repeating: the same line 64 times in a row: \"{}…\"",
            "x".repeat(80)
        )
    );
}
